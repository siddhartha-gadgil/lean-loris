from matplotlib import pyplot as plt
import tensorflow_docs.plots
import tensorflow_docs.modeling
import tensorflow_docs as tfdocs
from tensorflow.keras import regularizers
from tensorflow.keras import layers
from tensorflow import keras
import tensorflow as tf
import json
file = open(r"data/matrices.json", "r")
js = file.read()
data = json.loads(js)
file.close()
names = data["names"]
print(len(names))
dim = len(names)
terms = data["terms"]
types = data["types"]
size = len(terms)
print(len(terms))
print(len(types))


# inputs = keras.Input(shape=(dim,), name="types")
# x = layers.Dense(32, activation="relu", name="dense_1")(inputs)
# x = layers.Dense(32, activation="relu", name="dense_2")(x)
# outputs = layers.Dense(dim, activation="softmax", name="predictions")(x)

def floatlist(l):
    return [float(x) for x in l]


def normalize(l):
    total = sum(l)
    if total == 0:
        return floatlist(l)
    return [float(x) / float(total) for x in l]


statements = [floatlist(row) for row in types]
proofs = [normalize(row) for row in terms]

model = keras.Sequential([
    keras.Input(shape=(dim,), name="types"),
    layers.Dense(32, activation="elu", kernel_initializer='glorot_normal',
                 kernel_regularizer=regularizers.l2(0.001),
                 bias_regularizer=regularizers.l2(0.01),
                 name="dense_1"),
    layers.Dropout(0.2),
    layers.Dense(32, activation="elu", kernel_initializer='glorot_normal',
                 kernel_regularizer=regularizers.l2(0.001),
                 bias_regularizer=regularizers.l2(0.01),
                 name="dense_2"),
    layers.Dropout(0.2),
    layers.Dense(dim, activation="softmax", name="predictions")
]
)

statements_tensor = tf.convert_to_tensor(statements[:-1000], dtype=tf.float32)
proofs_tensor = tf.convert_to_tensor(proofs[:-1000], dtype=tf.float32)
test_statements_tensor = tf.convert_to_tensor(
    statements[-1000:], dtype=tf.float32)
test_proofs_tensor = tf.convert_to_tensor(proofs[-1000:], dtype=tf.float32)
print(statements_tensor.shape)
print(proofs_tensor.shape)

keras.callbacks.TensorBoard(
    log_dir="/home/gadgil/code/lean-loris/logs",
    histogram_freq=0,  # How often to log histogram visualizations
    embeddings_freq=0,  # How often to log embedding visualizations
    update_freq="epoch",
)  # How often to write logs (default: once per epoch)

model.compile(
    optimizer=keras.optimizers.Adam(),  # Optimizer
    # Loss function to minimize
    loss=keras.losses.KLDivergence(),
    # List of metrics to monitor
    metrics=[keras.metrics.KLDivergence()],
)

print('Built tensors')

print("Fit model on training data")

log_dir = "/home/gadgil/code/lean-loris/logs"
tensorboard_callback = tf.keras.callbacks.TensorBoard(
    log_dir=log_dir, histogram_freq=1)
history = model.fit(
    statements_tensor,
    proofs_tensor,
    batch_size=64,
    epochs=1024,
    # We pass some validation for
    # monitoring validation loss and metrics
    # at the end of each epoch
    validation_data=(test_statements_tensor, test_proofs_tensor),
    callbacks=[tensorboard_callback]
)

print("Done training")

print(history.history)

print(model.summary())


def namevec(name):
    return tf.convert_to_tensor([[1.0 if x == name else 0 for x in names]], dtype=tf.float32)


def sort_weighted(weights):
    def sort_key(x):
        return weights[x]
    l = list(range(len(names)))
    l.sort(key=sort_key, reverse=True)
    ns = [names[x] for x in l]
    w = list(weights).copy()
    w.sort(reverse=True)
    return [(ns[i], w[i]) for i in range(len(names)) if w[i] > 0]


def name_prediction_weights(name):
    return sort_weighted(model.predict(namevec(name))[0])


def index_prediction(index):
    stat = statements[index]
    stat_tensor = tf.convert_to_tensor([stat], dtype=tf.float32)
    prediction = model.predict(stat_tensor)[0]
    return sort_weighted(stat), sort_weighted(proofs[index]), sort_weighted(prediction)


def name_weight(l, name):
    for (n, w) in l:
        if n == name:
            return w
    return 0.0
