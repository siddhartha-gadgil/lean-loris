# Lean Loris

This is a repository for experiments with some ways of automating reasoning in lean 4, especially *forward reasoning* and *mixed reasoning*, to complement the existing *backward reasoning* used in tactics.

# Illustrations: in compiled code and interactive mode.

Our two main illustrations, one for forward reasoning and one for mixed reasoning, are too resource intensive to run in the interpreter. They are included as two of the three options in the compiled code (the third is generation of data for machine learning). 
## Forward reasoning examples

We illustrate *purely forward* reasoning, i.e., reasoning where no goal or intermediate claims are used in the evolution. These can (and are) specified only to be used for logging.
### Main example: A Czech-Slovak olympiad problem

Our main model problem for forward reasoning is the following from a Czech-Slovak Olympiad:

Let `M` be a set with a product. Given the axioms:
* `∀ a b : M, (a * b) * b = a`,
* `∀ a b : M, a * (a * b) = b`,

for arbitrary elements `m` and `n` in `M`, we have `m * n = n * m`.

We fix `m` and `n` and reason forward starting with `m`, `n`, the axioms, and multiplication. Our forward reasoning is tuned for this problem, and also mildly help by including `m * n` in the initial state. However, the evolution does not use the statement of the problem, any of the lemmas or the proof.

To understand the (automated) reasoning steps (and for use during tuning and debugging), some lemmas and the theorem were defined. While running progress in proving these is logged.

* `def lem1! := (m * n) * n = m` 
* `def lem2! := (m * n) * ((m * n) * n) = n`
* `def lem3! := ((m * n) * m) * m = m * n`
* `def lem4! := (m * n) * ((m * n) * n) = (m * n) * m`
* `def lem5! := (m * n) * m = n`
* `def lem6! := ((m * n) * m) * m = n * m`
* `def thm! := m * n = n * m`

The forward reasoning we use is mainly function application and closure of equality under symmetry and transitivity. In the latter we implicitly use our key "lemma recognition" principle: proofs of simple statements are treated like simple terms while generating.

### A basic example: left and right identities are equal

Another example of forward reasoning, in `ProofExamples.lean`, is one of the first abstract results one sees in algebra: given a multiplication on a set `α` with a left-identity `eₗ` and a right identity `eᵣ`, we have `eₗ = eᵣ`.

Our first proof is by forward reasoning using function application and equality closure under symmetry and transitivity. This is fully automatic forward reasoning in a single step.

We give a second proof of the result: given a multiplication on a set `α` with a left-identity `eₗ` and a right identity `eᵣ`, we have `eₗ = eᵣ` to illustrate implicit "lemma choosing". Notice that the cut-off is just `1` for both steps. However the proof is obtained as during equality generation, we look-ahead and generate proofs of statements that are simple.
## Mixed reasoning examples

We illustrate *mixed reasoning*, where a goal is specified and used in evolution, but generation is not limited to seeking the goal.  
### Main example: Locally constant functions are constant

Our main example of mixed reasoning is the result that if `f: Nat → α` is a function from natural numbers to a type `α` such that `∀ n : Nat, f (n + 1) = f n`, then `∀n : Nat, f n = f 0`, i.e. `f` is a constant function if it is locally constant.

We use two forms of backward reasoning: induction and introduction of variables based on goals (the latter can be replaced by forward reasoning). The forward reasoning we use is mainly function application and closure of equality under symmetry and transitivity. In the latter we implicitly use our key "lemma recognition" principle: proofs of simple statements are treated like simple terms while generating.

### Other examples

We have a few other examples of mixed reasoning, including deriving *Modus Ponens* starting with just its statement, in `ProofExamples.lean`.

# Running the code.

Many examples can be viewed by opening the file `ProofExamples.lean` in a Lean 4 editor, such as `vs-code` with the `lean 4` plugin.

The following instructions are for linux, and should be appropriately modified for any other OS. Assuming a recent installation of lean 4 (including lake), the following will build the code and show what can be run.

```bash
lake build
build/bin/lean-loris
```
You will see the following output:

```bash
Choose one or more of the following:
1. Czech-Slovak Olympiad example
2. Induction: locally constant functions
3. Dependency data generation
```

To run the Czech-Slovak Olympiad example, which uses purely forward reasoning, use the command: 
```bash
build/bin/lean-loris 1
```
Using argument `2` runs the mixed reasoning example. The argument `3` generates data for machine learning.

# Internals and using the code 

Documentation will be posted soon, along with a blog post explaining some of the principles behind the code.
