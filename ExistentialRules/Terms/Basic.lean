/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

/-!
# Terms

We define various kinds of terms that form some of the most basic building blocks of
other structures like atoms and rules.
In this file we start by introducing a `Signature` and the `VarOrConst` as the most basic term type.
-/

public section

/-- First of all, almost all of our definitions consider a fixed but arbitrary `Signature` of predicate symbols `P`, variables `V`, and constants `C`. Also every predicate has a fixed `arity`. Note that `P`, `V`, and `C` can be arbitrary types so there are no requirements in terms of countability or finiteness. However, intuitively you can consider them to be countably infinite sets. This would allow to pick fresh elements for example. In places where we need this property, we express this through the `GetFreshInhabitant` type class. -/
structure Signature where
  P : Type u
  V : Type v
  C : Type w
  arity : P -> Nat

section VarOrConst

/-!
## VarOrConst

We introduce `VarOrConst` as an inductive type representing a term.
The term is either a variable or a constant (thus the name).
`VarOrConst` is used to define `FunctionFreeAtom` later and is thus also the basic building block of (non-Skolemized) `Rule`s.
-/

/-- As the name suggests, a `VarOrConst` is either a variable or a constant. -/
inductive VarOrConst (sig : Signature) [DecidableEq sig.C] [DecidableEq sig.V] where
| var (v : sig.V) : VarOrConst sig
| const (c : sig.C) : VarOrConst sig
deriving DecidableEq

namespace VarOrConst

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

/-- A `VarOrConst` is a variable if it was built using the `VarOrConst.var` constructor. -/
@[expose]
def isVar : VarOrConst sig -> Bool
| .var _ => true
| .const _ => false

/-- Given a list of `VarOrConst`, we can filter out all the variables. Note that we do not use `List.filter` here since we need to change the list type on the way. -/
@[expose]
def filterVars : List (VarOrConst sig) -> List sig.V
| .nil => List.nil
| .cons voc vocs => match voc with
  | .var v => List.cons v (filterVars vocs)
  | .const _ => filterVars vocs

/-- Analogous to `filterVars`, we can also filter for constants. -/
@[expose]
def filterConsts : List (VarOrConst sig) -> List sig.C
| .nil => List.nil
| .cons voc vocs => match voc with
  | .var _ => filterConsts vocs
  | .const c => List.cons c (filterConsts vocs)

/-- Each member of `filterVars` is in the original list (when applying the `VarOrConst.var` constructor again.) -/
@[grind ->]
theorem filterVars_occur_in_original_list (l : List (VarOrConst sig)) (v : sig.V) : v ∈ filterVars l -> VarOrConst.var v ∈ l := by
  fun_induction filterVars <;> grind

/-- If a variable is in a list of `VarOrConst`, then it occurs in `filterVars`. -/
@[grind <-]
theorem mem_filterVars_of_var (l : List (VarOrConst sig)) (v : sig.V) : VarOrConst.var v ∈ l -> v ∈ filterVars l := by
  fun_induction filterVars <;> grind

/-- Each member of `filterConsts` is in the original list (when applying the `VarOrConst.const` constructor again.) -/
@[grind ->]
theorem filterConsts_occur_in_original_list (l : List (VarOrConst sig)) (c : sig.C) : c ∈ filterConsts l -> VarOrConst.const c ∈ l := by
  fun_induction filterConsts <;> grind

/-- If a constant is in a list of `VarOrConst`, then it occurs in `filterConsts`. -/
@[grind <-]
theorem mem_filterConsts_of_const (l : List (VarOrConst sig)) (c : sig.C) : VarOrConst.const c ∈ l -> c ∈ filterConsts l := by
  fun_induction filterConsts <;> grind

end VarOrConst

end VarOrConst

