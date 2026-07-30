/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.AtomsAndRules.Basic

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

/-- A variable occurs in `variables` iff it is a term of the `FunctionFreeAtom. -/
@[simp, grind =]
theorem mem_variables {a : FunctionFreeAtom sig} {v : sig.V} : v ∈ a.variables ↔ (VarOrConst.var v) ∈ a.terms := by
  unfold variables; grind

/-- A constant occurs in `constants` iff it is a term of the `FunctionFreeAtom. -/
@[simp, grind =]
theorem mem_constants {a : FunctionFreeAtom sig} {c : sig.C} : c ∈ a.constants ↔ (VarOrConst.const c) ∈ a.terms := by
  unfold constants; grind

end FunctionFreeAtom

