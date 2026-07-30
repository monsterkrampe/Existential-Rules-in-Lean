/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.AtomsAndRules.FunctionFreeAtom

/-!
# FunctionFreeConjunction

A conjunction of `FunctionFreeAtom`s $p(x, y) \land q(y)$ can simply be represented as a list of `FunctionFreeAtom`s.
-/

public section

abbrev FunctionFreeConjunction (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] := List (FunctionFreeAtom sig)

namespace FunctionFreeConjunction

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- The `terms` of a `FunctionFreeConjunction` are the terms of all its atoms. -/
@[expose]
def terms (conj : FunctionFreeConjunction sig) : List (VarOrConst sig) := conj.flatMap GeneralizedAtom.terms

/-- The `vars` of a `FunctionFreeConjunction` are the variables of all its atoms. -/
@[expose]
def vars (conj : FunctionFreeConjunction sig) : List sig.V := conj.flatMap FunctionFreeAtom.variables

/-- The `consts` of a `FunctionFreeConjunction` are the constants of all its atoms. -/
@[expose]
def consts (conj : FunctionFreeConjunction sig) : List sig.C := conj.flatMap FunctionFreeAtom.constants

/-- The `predicates` of a `FunctionFreeConjunction` are the predicates of all its atoms. -/
@[expose]
def predicates (conj : FunctionFreeConjunction sig) : List sig.P := conj.map GeneralizedAtom.predicate

/-- Different from the definition, we can also say that a variable is in `variables` iff there is a `FunctionFreeAtom` in the conjunction that features the variable as a term. -/
@[simp, grind =]
theorem mem_vars {conj : FunctionFreeConjunction sig} {v : sig.V} :
    v ∈ conj.vars ↔ ∃ f, f ∈ conj ∧ (VarOrConst.var v) ∈ f.terms := by
  unfold vars; simp

/-- Different from the definition, we can also say that a constant is in `constants` iff there is a `FunctionFreeAtom` in the conjunction that features the constant as a term. -/
@[simp, grind =]
theorem mem_consts {conj : FunctionFreeConjunction sig} {c : sig.C} :
    c ∈ conj.consts ↔ ∃ f, f ∈ conj ∧ (VarOrConst.const c) ∈ f.terms := by
  unfold consts; simp

end FunctionFreeConjunction

