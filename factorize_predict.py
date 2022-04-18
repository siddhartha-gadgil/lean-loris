import json
import numpy as np
import tensorflow as tf
from tensorflow import keras
from tensorflow.keras import layers
from tensorflow.keras import regularizers

import random

# look up indices (to use for names)


def index_dict(l):
    return {l[j]: j for j in range(len(l))}


# basic reading and json unpickling
file = open(r"data/shallow-frequencies.json", "r")
js = file.read()
data = json.loads(js)
file.close()
names = data["names"]
indices = index_dict(names)
dim = len(names)
triples = data["triples"]

print(f'loaded {len(triples)} triples, which use {len(names)} names')

# separating data into training and validation
data_triples = []
test_triples = []
random.seed(5)
for triple in triples:
   if len(triple["types"]) and len(triple["terms"]) > 0: 
    r = random.random()
    if r < 0.9:
        data_triples.append(triple)
    else:
        test_triples.append(triple)
data_size = len(data_triples)

print(
    f'Separated into data_triples: {len(data_triples)} and test_triples: {len(test_triples)}')

# The model
repr_dim = 10 # dimension of the reprresentations
inputs = keras.Input(shape=(dim,))
# the representation layer
repr = layers.Dense(
    repr_dim,
    activation='elu',  name="repr",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001))(inputs)
# output via representation, normalized by softmax
low_rank_out = layers.Dense(
    dim, activation='elu', name="low_rank_out",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001))(repr)
low_rank_prob = tf.keras.activations.softmax(low_rank_out)

# probability of using weights in statements and its complement
prob_self = layers.Dense(
    1, activation='sigmoid',
    kernel_initializer='glorot_normal',
    bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001),
    name="prob_self")(repr)
prob_others = layers.subtract(
    [tf.constant(1, dtype=np.float32, shape=(1,)), prob_self])

# weighted average of directly predicted weights and type weights with weight learned
from_statement = layers.multiply([inputs, prob_self])
low_rank_scaled = layers.multiply([prob_others, low_rank_prob])
outputs = layers.add([low_rank_scaled, from_statement])

# the built model
model = keras.Model(inputs=inputs, outputs=outputs, name="factorization_model")
print(model.summary())

# lists of lists for terms and types
def terms_and_types(triples):
    terms = [t["terms"] for t in triples]
    types = [t["types"] for t in triples]
    return terms, types

(data_terms, data_types) = terms_and_types(data_triples)
(test_terms, test_types) = terms_and_types(test_triples)

# numpy matrix of probability distributions of terms and types
def prob_matrix(data, dim):
    data_size = len(data)
    matrix = np.zeros((data_size, dim), np.float32)
    for i in range(len(data)):
        row = data[i]
        size = len(row)
        if size > 0:
            for name in row:
                j = indices[name]
                matrix[i][j] = matrix[i][j] + (1 / size)
    return matrix


term_matrix = prob_matrix(data_terms, dim)
type_matrix = prob_matrix(data_types, dim)

test_term_matrix = prob_matrix(test_terms, dim)
test_type_matrix = prob_matrix(test_types, dim)

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
    term_matrix,
    type_matrix,
    batch_size=64,
    epochs=1024,
    # We pass some validation for
    # monitoring validation loss and metrics
    # at the end of each epoch
    validation_data=(test_term_matrix, test_type_matrix),
    callbacks=[tensorboard_callback]
)

print("Done training")

print(history.history)