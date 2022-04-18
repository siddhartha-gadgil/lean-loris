import numpy as np
import tensorflow as tf
from tensorflow import keras
from tensorflow.keras import layers
import random

def index_dict(l):
    return {l[j] : j for j in range(len(l))}

file = open(r"data/shallow-frequencies.json", "r")
import json
js = file.read()
data = json.loads(js)
file.close()
names = data["names"]
indices = index_dict(names)
dim = len(names)
triples = data["triples"]

print (len(names))
print (len(triples))

data_triples = []
test_triples = []
random.seed(5)
for triple in triples:
    r = random.random()
    if r < 0.9:
        data_triples.append(triple)
    else:
        test_triples.append(triple)
print (len(data_triples))
print (len(test_triples))
data_size = len(data_triples)

# The model
rep_dim=10
inputs = keras.Input(shape=(dim,))
rep = layers.Dense(rep_dim,  name="rep")(inputs)
low_rank_out = layers.Dense(dim, name="low_rank_out")(rep)
prob_preserve = layers.Dense(1, activation='sigmoid',  name="prob_preserve")(rep)
from_statement = layers.multiply([inputs, prob_preserve])
outputs = layers.add([low_rank_out, from_statement])
model = keras.Model(inputs=inputs, outputs=outputs, name="factorization_model")
print(model.summary())

print(test_triples[0]["terms"])
print(test_triples[0]["types"])

def terms_and_types(triples):
    terms =[t["terms"] for t in triples]
    types = [t["types"] for t in triples]
    return terms, types

(data_terms, data_types) = terms_and_types(data_triples)
(test_terms, test_types) = terms_and_types(test_triples)



print(data_terms[0])
print(data_types[0])
print(len(data_terms))