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


# The first model
repr_dim1 = 10 # dimension of the representations
inputs1 = keras.Input(shape=(dim,))
# the representation layer
repr1 = layers.Dense(
    repr_dim1,
    activation='elu',  name="repr",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001))(inputs1)
# output via representation, normalized by softmax
low_rank_out1 = layers.Dense(
    dim, activation='elu', name="low_rank_out",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001))(repr1)
low_rank_prob1 = tf.keras.activations.softmax(low_rank_out1)

# probability of using weights in statements and its complement
prob_self1 = layers.Dense(
    1, activation='sigmoid',
    kernel_initializer='glorot_normal',
    bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001),
    name="prob_self")(repr1)
prob_others1 = layers.subtract(
    [tf.constant(1, dtype=np.float32, shape=(1,)), prob_self1])

# weighted average of directly predicted weights and type weights with weight learned
from_statement1 = layers.multiply([inputs1, prob_self1])
low_rank_scaled1 = layers.multiply([prob_others1, low_rank_prob1])
outputs1 = layers.add([low_rank_scaled1, from_statement1])

# the built model
model1 = keras.Model(inputs=inputs1, outputs=outputs1, name="factorization_model1")
print(model1.summary())
model1.compile(
    optimizer=keras.optimizers.Adam(),  # Optimizer
    # Loss function to minimize
    loss=keras.losses.KLDivergence(),
    # List of metrics to monitor
    metrics=[keras.metrics.KLDivergence()],
)

print("Compiled model 1")


# The second model
repr_dim2 = 10 # dimension of the representations
step_dim2 = 20
inputs2 = keras.Input(shape=(dim,))
# the representation layer
repr_step2 = layers.Dense(
    step_dim2,
    activation='elu',  name="repr_step",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001))(inputs2)
repr2 = layers.Dense(
    repr_dim2,
    activation='elu',  name="repr",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001))(repr_step2)

# output via representation, normalized by softmax
low_rank_step2 = layers.Dense(
    step_dim2, activation='elu', name="low_rank_step",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001))(repr2)

low_rank_out2 = layers.Dense(
    dim, activation='elu', name="low_rank_out",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001))(low_rank_step2)
low_rank_prob2 = tf.keras.activations.softmax(low_rank_out2)

# probability of using weights in statements and its complement
prob_self2 = layers.Dense(
    1, activation='sigmoid',
    kernel_initializer='glorot_normal',
    bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001),
    name="prob_self")(repr2)
prob_others2 = layers.subtract(
    [tf.constant(1, dtype=np.float32, shape=(1,)), prob_self2])

# weighted average of directly predicted weights and type weights with weight learned
from_statement2 = layers.multiply([inputs2, prob_self2])
low_rank_scaled2 = layers.multiply([prob_others2, low_rank_prob2])
outputs2 = layers.add([low_rank_scaled2, from_statement2])

# the built model
model2 = keras.Model(inputs=inputs2, outputs=outputs2, name="factorization_model2")
print(model2.summary())

model2.compile(
    optimizer=keras.optimizers.Adam(),  # Optimizer
    # Loss function to minimize
    loss=keras.losses.KLDivergence(),
    # List of metrics to monitor
    metrics=[keras.metrics.KLDivergence()],
)

print("Compiled model 2")



log_dir = "/home/gadgil/code/lean-loris/logs"
tensorboard_callback = tf.keras.callbacks.TensorBoard(
    log_dir=log_dir, histogram_freq=1)

def fit(n=1024, m= model1):
    history = m.fit(
        term_matrix,
        type_matrix,
        batch_size=64,
        epochs=n,
        # We pass some validation for
        # monitoring validation loss and metrics
        # at the end of each epoch
        validation_data=(test_term_matrix, test_type_matrix),
        callbacks=[tensorboard_callback]
    )
    print("Done training")
    return history