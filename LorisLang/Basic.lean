import Lean
import Std.Data.HashMap.Basic
open Std Lean Elab Meta

namespace LorisLang

universe u v

structure Object where
  type : Type u
  value : type

inductive HList where
 | nil : HList
 | cons {α : Type} (a : α) (tail: HList): HList

structure State  where
  variables: Std.HashMap String Object
  messages: Array <| String × (Option Syntax)

end LorisLang

abbrev LorisLangM  := StateM LorisLang.State

#check LorisLangM
