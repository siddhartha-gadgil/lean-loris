from audioop import bias
import json
import numpy as np
import tensorflow as tf
from tensorflow import keras
from tensorflow.keras import layers
from tensorflow.keras import regularizers
# import tensorflow_probability as tfp

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

# numpy vector of count of terms and types


def count_matrix(pairs, dim):
    vec = np.zeros((dim, ), np.float32)
    for d in pairs:
        name = d['name']
        count = d['count']
        vec[indices[name]] = count
    return vec


term_count = count_matrix(data['terms'], dim)
type_count = count_matrix(data['types'], dim)
freq_ratio = tf.constant([(1 + term_count[i]) / (1 + type_count[i])
                          for i in range(dim)], shape=(1, dim), dtype=tf.float32)

# freq_ratio = tf.ones((1, dim), dtype=tf.float32)

# The first model
repr_dim1 = 10  # dimension of the representations
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
prob_others1 = 1 - prob_self1

# weighted average of directly predicted weights and type weights with weight learned
from_statement1 = inputs1 * prob_self1
low_rank_scaled1 = prob_others1 * low_rank_prob1
outputs1 = low_rank_scaled1 + from_statement1

# the built model
model1 = keras.Model(inputs=inputs1, outputs=outputs1,
                     name="factorization_model1")
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
repr_dim2 = 10  # dimension of the representations
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
prob_others2 = 1 - prob_self2

# weighted average of directly predicted weights and type weights with weight learned
from_statement2 = inputs2 * prob_self2
low_rank_scaled2 = prob_others2 * low_rank_prob2
outputs2 = low_rank_scaled2 + from_statement2

# the built model
model2 = keras.Model(inputs=inputs2, outputs=outputs2,
                     name="factorization_model2")
print(model2.summary())

model2.compile(
    optimizer=keras.optimizers.Adam(),  # Optimizer
    # Loss function to minimize
    loss=keras.losses.KLDivergence(),
    # List of metrics to monitor
    metrics=[keras.metrics.KLDivergence()],
)

print("Compiled model 2")

# The third model - like the second but with dropout
repr_dim3 = 10  # dimension of the representations
step_dim3 = 20
inputs3 = keras.Input(shape=(dim,))
# the representation layer
repr_step3 = layers.Dense(
    step_dim3,
    activation='elu',  name="repr_step",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001))(inputs3)
repr_drop3 = layers.Dropout(0.5)(repr_step3)
repr3 = layers.Dense(
    repr_dim3,
    activation='elu',  name="repr",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001))(repr_drop3)
repr3drop = layers.Dropout(0.5)(repr3)

# output via representation, normalized by softmax
low_rank_step3 = layers.Dense(
    step_dim3, activation='elu', name="low_rank_step",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001))(repr3drop)

low_rank_drop3 = layers.Dropout(0.5)(low_rank_step3)
low_rank_out3 = layers.Dense(
    dim, activation='elu', name="low_rank_out",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001))(low_rank_drop3)
low_rank_prob3 = tf.keras.activations.softmax(low_rank_out3)

# probability of using weights in statements and its complement
prob_self3 = layers.Dense(
    1, activation='sigmoid',
    kernel_initializer='glorot_normal',
    bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001),
    name="prob_self")(repr3drop)
prob_others3 = 1 - prob_self3

# weighted average of directly predicted weights and type weights with weight learned
from_statement3 = inputs3 * prob_self3
low_rank_scaled3 = prob_others3 * low_rank_prob3
outputs3 = low_rank_scaled3 + from_statement3

# the built model
model3 = keras.Model(inputs=inputs3, outputs=outputs3,
                     name="factorization_model3")
print(model3.summary())

model3.compile(
    optimizer=keras.optimizers.Adam(),  # Optimizer
    # Loss function to minimize
    loss=keras.losses.KLDivergence(),
    # List of metrics to monitor
    metrics=[keras.metrics.KLDivergence()],
)

print("Compiled model 3")

print('\nCompiling fourth model')
# The fourth model, scaling inputs before mixing in.
repr_dim4 = 10  # dimension of the representations
step_dim4 = 20
inputs4 = keras.Input(shape=(dim,))
# the representation layer
repr_step4 = layers.Dense(
    step_dim4,
    activation='elu',  name="repr_step",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001))(inputs4)
repr_drop4 = layers.Dropout(0.5)(repr_step4)
repr4 = layers.Dense(
    repr_dim4,
    activation='elu',  name="repr",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001))(repr_drop4)
repr4drop = layers.Dropout(0.5)(repr4)

# output via representation, normalized by softmax
low_rank_step4 = layers.Dense(
    step_dim4, activation='elu', name="low_rank_step",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001))(repr4drop)

low_rank_drop4 = layers.Dropout(0.5)(low_rank_step4)
low_rank_out4 = layers.Dense(
    dim, activation='elu', name="low_rank_out",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001))(low_rank_drop4)
low_rank_prob4 = tf.keras.activations.softmax(low_rank_out4)

# probability of using weights in statements and its complement
prob_self4 = layers.Dense(
    1, activation='sigmoid',
    kernel_initializer='glorot_normal',
    bias_initializer='zeros',
    kernel_regularizer='l1_l2',
    name="prob_self")(repr4drop)
prob_others4 = 1 - prob_self4

# weighted average of directly predicted weights and type weights with weight learned
dummy_single4 = layers.Dense(
    1, activation='sigmoid',
    kernel_initializer='zeros',
    bias_initializer=tf.keras.initializers.Constant(1.0),
    kernel_regularizer='l1_l2',
    name="dummy_single")(repr4drop)
freq_scale = layers.Dense(dim, bias_initializer=tf.keras.initializers.Constant(1.0),
                          kernel_initializer='zeros',
                          kernel_regularizer=regularizers.l1(0.01),
                          bias_regularizer=regularizers.l2(0.0001),
                          name='frequency_scale', activation='softmax')(dummy_single4)
# tfp.layers.VariableLayer(shape=(dim, 1), dtype=tf.float32, initializer=tf.keras.initializers.Constant(1.0))
inputs_raw_scaled4 = inputs4 * freq_scale
inputs_scaled_total4 = tf.reduce_sum(inputs_raw_scaled4, axis=1, keepdims=True)
inputs_scaled4 = inputs_raw_scaled4 / inputs_scaled_total4
from_statement4 = inputs_scaled4 * prob_self4
low_rank_scaled4 = prob_others4 * low_rank_prob4
outputs4 = low_rank_scaled4 + from_statement4

# the built model
model4 = keras.Model(inputs=inputs4, outputs=outputs4,
                     name="factorization_model4")
print(model4.summary())

model4.compile(
    optimizer=keras.optimizers.Adam(),  # Optimizer
    # Loss function to minimize
    loss=keras.losses.KLDivergence(),
    # List of metrics to monitor
    metrics=[keras.metrics.KLDivergence()],
)

print("Compiled model 4")

print('\nCompiling fifth model')
# The fifth model, scaling inputs before mixing in.
repr_dim5 = 10  # dimension of the representations
step_dim5 = 20
inputs5 = keras.Input(shape=(dim,))
# the representation layer
repr_step5 = layers.Dense(
    step_dim5,
    activation='elu',  name="repr_step",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001))(inputs5)
repr_drop5 = layers.Dropout(0.5)(repr_step5)
repr5 = layers.Dense(
    repr_dim5,
    activation='elu',  name="repr",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001))(repr_drop5)
repr5drop = layers.Dropout(0.5)(repr5)

dummy_single5 = layers.Dense(
    1, activation='sigmoid',
    kernel_initializer='zeros',
    bias_initializer=tf.keras.initializers.Constant(1.0),
    kernel_regularizer='l1_l2',
    name="dummy_single")(repr5drop)

# output via representation, normalized by softmax
low_rank_step5 = layers.Dense(
    step_dim5, activation='elu', name="low_rank_step",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001))(repr5drop)

low_rank_drop5 = layers.Dropout(0.5)(low_rank_step5)
low_rank_out5 = layers.Dense(
    dim, activation='elu', name="low_rank_out",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.001))(low_rank_drop5)
low_rank_prob5 = tf.keras.activations.softmax(low_rank_out5)

# probability of using weights in statements and its complement
prob_self5 = layers.Dense(
    1, activation='sigmoid',
    kernel_initializer='glorot_normal',
    bias_initializer='zeros',
    kernel_regularizer='l1_l2',
    name="prob_self")(dummy_single5)
prob_others5 = 1 - prob_self5

# weighted average of directly predicted weights and type weights with weight learned
freq_scale = layers.Dense(dim, bias_initializer=tf.keras.initializers.Constant(1.0),
                          kernel_initializer='zeros',
                          kernel_regularizer=regularizers.l1(0.01),
                          bias_regularizer=regularizers.l2(0.0001),
                          name='frequency_scale', activation='softmax')(dummy_single5)
# tfp.layers.VariableLayer(shape=(dim, 1), dtype=tf.float32, initializer=tf.keras.initializers.Constant(1.0))
inputs_raw_scaled5 = inputs5 * freq_scale
inputs_scaled_total5 = tf.reduce_sum(inputs_raw_scaled5, axis=1, keepdims=True)
inputs_scaled5 = inputs_raw_scaled5 / inputs_scaled_total5
from_statement5 = inputs_scaled5 * prob_self5
low_rank_scaled5 = prob_others5 * low_rank_prob5
outputs5 = low_rank_scaled5 + from_statement5

# the built model
model5 = keras.Model(inputs=inputs5, outputs=outputs5,
                     name="factorization_model5")
print(model5.summary())

model5.compile(
    optimizer=keras.optimizers.Adam(),  # Optimizer
    # Loss function to minimize
    loss=keras.losses.KLDivergence(),
    # List of metrics to monitor
    metrics=[keras.metrics.KLDivergence()],
)

print("Compiled model 5")


class Scaling(keras.layers.Layer):
    def __init__(self, input_dim, init_ratios, **kwargs):
        super(Scaling, self).__init__(**kwargs)
        initial_const = tf.constant(np.array([tf.math.log(x) for x in init_ratios]), shape=(1, input_dim), dtype=tf.float32)
        self.w = tf.Variable(
            initial_value=initial_const,
            shape=(1, input_dim),  trainable=True, dtype=tf.float32)
        self.input_dim = input_dim

        self.init_ratios = init_ratios

    def call(self, inputs):
        return inputs * tf.exp(self.w)

    def get_config(self):
        config = super().get_config()
        config.update({
            'input_dim': self.input_dim,
            'init_ratios': self.init_ratios,
        })
        return config

ratios = [(1 + term_count[i]) / (1 + type_count[i]) for i in range(dim)]

print('\nCompiling sixth model')
# The sixth model, scaling inputs before mixing in using a custom layer.
repr_dim6 = 40  # dimension of the representations
step_dim6 = 100
inputs6 = keras.Input(shape=(dim,))
# the representation layer
repr_step6 = layers.Dense(
    step_dim6,
    activation='elu',  name="repr_step",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.0002))(inputs6)
repr_drop6 = layers.Dropout(0.7)(repr_step6)
repr6 = layers.Dense(
    repr_dim6,
    activation='elu',  name="repr",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.0002))(repr_drop6)
repr6drop = layers.Dropout(0.7)(repr6)

# output via representation, normalized by softmax
low_rank_step6 = layers.Dense(
    step_dim6, activation='elu', name="low_rank_step",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.0002))(repr6drop)

low_rank_drop6 = layers.Dropout(0.7)(low_rank_step6)
low_rank_out6 = layers.Dense(
    dim, activation='elu', name="low_rank_out",
    kernel_initializer='glorot_normal', bias_initializer='zeros',
    kernel_regularizer=regularizers.l2(0.002))(low_rank_drop6)
low_rank_prob6 = tf.keras.activations.softmax(low_rank_out6)

# probability of using weights in statements and its complement
prob_self6 = layers.Dense(
    1, activation='sigmoid',
    kernel_initializer='glorot_normal',
    bias_initializer='zeros',
    kernel_regularizer='l1_l2',
    name="prob_self")(repr6drop)
prob_others6 = 1 - prob_self6

# weighted average of directly predicted weights and type weights with weight learned
scaling = Scaling(dim, ratios)
inputs_raw_scaled6 = scaling(inputs6)
inputs_scaled_total6 = tf.reduce_sum(inputs_raw_scaled6, axis=1, keepdims=True)
inputs_scaled6 = inputs_raw_scaled6 / inputs_scaled_total6
from_statement6 = inputs_scaled6 * prob_self6
low_rank_scaled6 = prob_others6 * low_rank_prob6
outputs6 = low_rank_scaled6 + from_statement6

# the built model
model6 = keras.Model(inputs=inputs6, outputs=outputs6,
                     name="factorization_model6")
print(model6.summary())

model6.compile(
    optimizer=keras.optimizers.Adam(),  # Optimizer
    # Loss function to minimize
    loss=keras.losses.KLDivergence(),
    # List of metrics to monitor
    metrics=[keras.metrics.KLDivergence()],
)

print("Compiled model 6")


log_dir = "/home/gadgil/code/lean-loris/logs"
tensorboard_callback = tf.keras.callbacks.TensorBoard(
    log_dir=log_dir, histogram_freq=1)


def fit(n=1024, m=model1, epsilon=0.00001):
    history = m.fit(
        type_matrix,
        term_matrix,
        batch_size=64,
        epochs=n,
        # We pass some validation for
        # monitoring validation loss and metrics
        # at the end of each epoch
        validation_data=(test_type_matrix, test_term_matrix),
        callbacks=[tensorboard_callback,
                   #    keras.callbacks.EarlyStopping(
                   #        # Stop training when `val_loss` is no longer improving
                   #        monitor="val_loss",
                   #        # "no longer improving" being defined as "no better than 1e-2 less"
                   #        min_delta=epsilon,
                   #        # "no longer improving" being further defined as "for at least 2 epochs"
                   #        patience=20,
                   #        verbose=1,)
                   ]
    )
    print("Done training")
    return history
