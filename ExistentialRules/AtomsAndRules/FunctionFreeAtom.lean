/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.AtomsAndRules.Atom

/-!
# FunctionFreeAtom

A `FunctionFreeAtom` is a `GeneralizedAtom` with `VarOrConst`s.
-/

public section

abbrev FunctionFreeAtom (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] := GeneralizedAtom sig (VarOrConst sig)

namespace FunctionFreeAtom

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- Using `VarOrConst.filterVars`, we can obtain all variables from the terms of the `FunctionFreeAtom`. -/
@[expose]
def variables (a : FunctionFreeAtom sig) : List sig.V := VarOrConst.filterVars a.terms

/-- Using `VarOrConst.filterConsts`, we can obtain all constants from the terms of the `FunctionFreeAtom`. -/
@[expose]
def constants (a : FunctionFreeAtom sig) : List sig.C := VarOrConst.filterConsts a.terms

/-- We can `skolemize` a `FunctionFreeAtom` by skolemizing all its `VarOrConst`s. This yields an `Atom`. -/
def skolemize (ruleId : Nat) (disjunctIndex : Nat) (frontier : List sig.V) (a : FunctionFreeAtom sig) : Atom sig := {
  predicate := a.predicate,
  terms := a.terms.map (VarOrConst.skolemize ruleId disjunctIndex frontier),
  arity_ok := by rw [List.length_map, a.arity_ok]
}

/-- A variable occurs in `variables` iff it is a term of the `FunctionFreeAtom. -/
@[simp, grind =]
theorem mem_variables {a : FunctionFreeAtom sig} {v : sig.V} : v ∈ a.variables ↔ (VarOrConst.var v) ∈ a.terms := by
  unfold variables; grind

/-- A constant occurs in `constants` iff it is a term of the `FunctionFreeAtom. -/
@[simp, grind =]
theorem mem_constants {a : FunctionFreeAtom sig} {c : sig.C} : c ∈ a.constants ↔ (VarOrConst.const c) ∈ a.terms := by
  unfold constants; grind

/-- The number of terms remains unchanged when Skolemizing. -/
@[simp, grind =]
theorem length_skolemize {ruleId : Nat} {disjunctIndex : Nat} {frontier : List sig.V} {a : FunctionFreeAtom sig} :
    (a.skolemize ruleId disjunctIndex frontier).terms.length = a.terms.length := by
  unfold skolemize; simp

/-- If a a `VarOrConst` occurs in the terms of the `FunctionFreeAtom`, then the Skolemized `VarOrConst` occurs in the Skolemized `Atom`. -/
@[grind <-]
theorem mem_skolemize_of_mem {ruleId : Nat} {disjunctIndex : Nat} {frontier : List sig.V}
    {a : FunctionFreeAtom sig} {t : VarOrConst sig} :
    t ∈ a.terms -> (t.skolemize ruleId disjunctIndex frontier) ∈ (a.skolemize ruleId disjunctIndex frontier).terms := by
  unfold skolemize
  intro t_mem
  rw [List.mem_map]
  exists t

end FunctionFreeAtom

