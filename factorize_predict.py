import numpy as np
import tensorflow as tf
from tensorflow import keras
from tensorflow.keras import layers
from tensorflow.keras import regularizers

import random

# look up indices (to use for names)
def index_dict(l):
    return {l[j] : j for j in range(len(l))}

# basic reading and json unpickling
file = open(r"data/shallow-frequencies.json", "r")
import json
js = file.read()
data = json.loads(js)
file.close()
names = data["names"]
indices = index_dict(names)
dim = len(names)
triples = data["triples"]

print (f'loaded {len(triples)} triples, which use {len(names)} names')

# separating data into training and validation
data_triples = []
test_triples = []
random.seed(5)
for triple in triples:
    r = random.random()
    if r < 0.9:
        data_triples.append(triple)
    else:
        test_triples.append(triple)
data_size = len(data_triples)

print(f'Separated into data_triples: {len(data_triples)} and test_triples: {len(test_triples)}')

# The model
rep_dim=10
inputs = keras.Input(shape=(dim,))
rep = layers.Dense(rep_dim, activation= 'elu',  name="rep", kernel_initializer='glorot_normal', bias_initializer='zeros',
                 kernel_regularizer=regularizers.l2(0.001))(inputs)
low_rank_out = layers.Dense(dim, activation= 'elu', name="low_rank_out")(rep)
low_rank_scaled = layers.Softmax()(low_rank_out)
prob_preserve = layers.Dense(1, activation='sigmoid', kernel_initializer='glorot_normal', bias_initializer='zeros',
     kernel_regularizer=regularizers.l2(0.001), name="prob_preserve")(rep)
from_statement = layers.multiply([inputs, prob_preserve])
outputs_sum = layers.add([low_rank_out, from_statement])
outputs= layers.Softmax()(outputs_sum)
model = keras.Model(inputs=inputs, outputs=outputs, name="factorization_model")
print(model.summary())

# lists of lists for terms and types
def terms_and_types(triples):
    terms =[t["terms"] for t in triples]
    types = [t["types"] for t in triples]
    return terms, types

(data_terms, data_types) = terms_and_types(data_triples)
(test_terms, test_types) = terms_and_types(test_triples)

def prob_matrix(data, dim):
    data_size = len(data)
    matrix = np.zeros((data_size, dim), np.float32)
    for i in range(len(data)):
        row = data[i]
        size = len(row)
        if size > 0:
            for name in row:
                j = indices[name]
                matrix[i][j] = matrix[i][j] + (1/ size)
    return matrix

term_matrix = prob_matrix(data_terms, dim)
type_matrix = prob_matrix(data_types, dim)

test_term_matrix = prob_matrix(test_terms, dim)
test_type_matrix = prob_matrix(test_types, dim)

