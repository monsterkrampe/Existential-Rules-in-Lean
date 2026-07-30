/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.Terms.SkolemTerm
public import ExistentialRules.AtomsAndRules.FunctionFreeAtom

/-!
# Atom

An `Atom` is simply a `GeneralizedAtom` using `SkolemTerm`s.
-/

public section

abbrev Atom (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] := GeneralizedAtom sig (SkolemTerm sig)

namespace FunctionFreeAtom

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- We can `skolemize` a `FunctionFreeAtom` by skolemizing all its `VarOrConst`s. This yields an `Atom`. -/
def skolemize (rule : Rule sig) (i : Nat) (lt : i < rule.head.length) (a : FunctionFreeAtom sig) : Atom sig := {
  predicate := a.predicate,
  terms := a.terms.map (VarOrConst.skolemize rule i lt),
  arity_ok := by rw [List.length_map, a.arity_ok]
}

/-- The number of terms remains unchanged when Skolemizing. -/
@[simp, grind =]
theorem length_skolemize {rule : Rule sig} {i : Nat} {lt : i < rule.head.length} {a : FunctionFreeAtom sig} :
    (a.skolemize rule i lt).terms.length = a.terms.length := by
  unfold skolemize; simp

/-- If a a `VarOrConst` occurs in the terms of the `FunctionFreeAtom`, then the Skolemized `VarOrConst` occurs in the Skolemized `Atom`. -/
@[grind <-]
theorem mem_skolemize_of_mem {rule : Rule sig} {i : Nat} {lt : i < rule.head.length} {a : FunctionFreeAtom sig} {t : VarOrConst sig} :
    t ∈ a.terms -> (t.skolemize rule i lt) ∈ (a.skolemize rule i lt).terms := by
  unfold skolemize
  intro t_mem
  rw [List.mem_map]
  exists t

end FunctionFreeAtom

