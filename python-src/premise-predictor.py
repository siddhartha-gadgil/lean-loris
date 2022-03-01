file = open(r"data/matrices.json", "r")
js = file.read()
import json
data = json.loads(js)
file.close()
names = data["names"]
print (len(names))
dim = len(names)
terms = data["terms"]
types = data["types"]
size = len(terms)
print (len(terms))
print (len(types))
import tensorflow as tf
from tensorflow import keras
from tensorflow.keras import layers

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

statements = [floatlist(row) for row in types][:-1000]
proofs = [normalize(row) for row in terms][:-1000]

model = keras.Sequential([
    keras.Input(shape=(dim,), name="types"),
    layers.Dense(32, activation="relu", kernel_initializer='glorot_normal', name="dense_1"),
    layers.Dense(32, activation="relu", kernel_initializer='glorot_normal',  name="dense_2"),
    layers.Dense(32, activation="relu", kernel_initializer='glorot_normal', name="dense_3"),
    layers.Dense(32, activation="relu", kernel_initializer='glorot_normal', name="dense_4"),
    layers.Dense(dim, activation="softmax", name="predictions"),
    ]
    )

statements = tf.convert_to_tensor(statements, dtype=tf.float32)
proofs = tf.convert_to_tensor(proofs, dtype=tf.float32)
print(statements.shape)
print(proofs.shape)

model.compile(
    optimizer=keras.optimizers.Adam(),  # Optimizer
    # Loss function to minimize
    loss=keras.losses.KLDivergence(),
    # List of metrics to monitor
    # metrics=[keras.metrics.SparseCategoricalAccuracy()],
)

print('Built tensors')

print("Fit model on training data")
history = model.fit(
    statements,
    proofs,
    batch_size=64,
    epochs=256
    # We pass some validation for
    # monitoring validation loss and metrics
    # at the end of each epoch
)

print("Done training")

print(history.history)

print(model.summary()) 