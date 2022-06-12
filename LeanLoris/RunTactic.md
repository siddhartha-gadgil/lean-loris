# Notes on how tactics are run in lean 4

Main goal is to be able to run tactics with logging, based on input etc.
 
## TacticM module

- `Context` : `main` and an elaborator name
- `State`: `goals` - list of mvar ids

In the `focus` combinator, 
   
- a tactic is run in a `do` loop.
- the type allows this to be a general `TacticM x` (not forcing `Unit`)


## Some functions and types

* `Tactic.run`
    - runs to `Meta` level returning subgoals
* `Term.runTactic` 
    - at `TermElabM` level but returns Unit
    - uses `Tactic.run`
* `Elab.runTactic` 
* `evalTactic` 
    - converts syntax to tactic 
    - question: is it a tacticSeq it runs?
    - the way it runs _at_ some term suggests a single tactic
* `evalTacticSeq` 
