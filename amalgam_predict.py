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

# lists of lists for terms and types


def terms_and_types(triples):
    terms = [t["terms"] for t in triples]
    types = [t["types"] for t in triples]
    return terms, types

# numpy matrix of probability distributions of terms and types


def prob_matrix(data, dim, indices):
    data_size = len(data)
    matrix = np.zeros((data_size, dim), dtype= np.float32)
    for i in range(len(data)):
        row = data[i]
        size = len(row)
        if size > 0:
            for name in row:
                j = indices[name]
                matrix[i][j] = matrix[i][j] + (1 / size)
    return matrix


def count_matrix(pairs, dim, indices):
    vec = np.zeros((dim, ), np.float32)
    for d in pairs:
        name = d['name']
        count = d['count']
        vec[indices[name]] = count
    return vec


def load_data(filename="data/shallow-frequencies.json"):
    with open(filename, 'r') as f:
        data = json.load(f)
        names = data["names"]
        indices = index_dict(names)
        dim = len(names)
        data['indices'] = indices
        data['dim'] = dim
    return data


def freq_ratios(data):
    dim = data['dim']
    term_count = count_matrix(data['terms'], dim, data['indices'])
    type_count = count_matrix(data['types'], dim, data['indices'])
    return [(1 + term_count[i]) / (1 + type_count[i]) for i in range(dim)]


def training_data(data):
    triples = data['triples']
    dim = data['dim']
    indices = data['indices']
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
    (data_terms, data_types) = terms_and_types(data_triples)
    (test_terms, test_types) = terms_and_types(test_triples)
    term_matrix = prob_matrix(data_terms, dim, indices)
    type_matrix = prob_matrix(data_types, dim, indices)
    test_term_matrix = prob_matrix(test_terms, dim, indices)
    test_type_matrix = prob_matrix(test_types, dim, indices)
    return {'term_matrix': term_matrix, 
            'type_matrix': type_matrix, 
            'test_term_matrix': test_term_matrix, 
            'test_type_matrix': test_type_matrix, 
            'data_size': data_size, 
            'test_size': len(test_triples)}

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

log_dir = "/home/gadgil/code/lean-loris/logs"
tensorboard_callback = tf.keras.callbacks.TensorBoard(
    log_dir=log_dir, histogram_freq=1)


def fit(epochs, model, data):
    td = training_data(data)
    history = model.fit(
        td['type_matrix'],
        td['term_matrix'],
        batch_size=64,
        epochs=epochs,
        # We pass some validation for
        # monitoring validation loss and metrics
        # at the end of each epoch
        validation_data=(td['test_type_matrix'], td['test_term_matrix']),
        callbacks=[tensorboard_callback,
                   #    keras.callbacks.EarlyStopping(
                   #        # Stop training when `val_loss` is no longer improving
                   #        monitor="val_loss",
                   #        # "no longer improving" being defined as "no better than epsilon less"
                   #        min_delta=epsilon,
                   #        # "no longer improving" being further defined as "for at least 20 epochs"
                   #        patience=20,
                   #        verbose=1,)
                   ]
    )
    print("Done training")
    return history


# The sixth model in the original experiments, scaling inputs before mixing in using a custom layer.
def model6(data, repr_dim6 = 40, step_dim6 = 100):
    dim = data['dim']
    ratios=freq_ratios(data)
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
    return model6
