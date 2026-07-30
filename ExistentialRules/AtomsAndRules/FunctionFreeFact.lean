/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.AtomsAndRules.Fact

/-!
# FunctionFreeFacts

A `FunctionFreeFact` is a `GeneralizedAtom` with constants.
-/

public section

abbrev FunctionFreeFact (sig : Signature) [DecidableEq sig.P] := GeneralizedAtom sig sig.C

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace FunctionFreeFact

/-- A `FunctionFreeFact` can always be converted to a `Fact`. -/
@[expose]
def toFact (f : FunctionFreeFact sig) : Fact sig := {
  predicate := f.predicate,
  terms := f.terms.map GroundTerm.const,
  arity_ok := by rw [List.length_map, f.arity_ok]
}

/-- A `Fact` obtained from a `FunctionFreeFact` `isFunctionFree`. -/
@[grind <-]
theorem toFact_isFunctionFree (f : FunctionFreeFact sig) : f.toFact.isFunctionFree := by
  intro _
  unfold toFact
  grind

end FunctionFreeFact

/-- If a `Fact.isFunctionFree`, then we can convert it to a `FunctionFreeFact`. -/
@[expose]
def Fact.toFunctionFreeFact (f : Fact sig) (isFunctionFree : f.isFunctionFree) : FunctionFreeFact sig := {
  predicate := f.predicate
  terms := f.terms.attach.map (fun t => t.val.toConst (isFunctionFree t.val t.property))
  arity_ok := by rw [List.length_map, List.length_attach, f.arity_ok]
}

/-- Converting a `Fact` to a `FunctionFreeFact` and back yields the initial `Fact`. -/
@[simp, grind =]
theorem Fact.toFact_after_toFunctionFreeFact_is_id (f : Fact sig) (isFunctionFree : f.isFunctionFree) : (f.toFunctionFreeFact isFunctionFree).toFact = f := by
  unfold toFunctionFreeFact
  unfold FunctionFreeFact.toFact
  simp only
  rw [GeneralizedAtom.mk.injEq]
  constructor
  . simp
  . rw [List.map_attach_eq_pmap]
    apply List.ext_get
    . simp
    . grind

/-- Converting a `FunctionFreeFact` to a `Fact` and back yields the initial `FunctionFreeFact`. -/
@[simp, grind =]
theorem FunctionFreeFact.toFunctionFreeFact_after_toFact_is_id (f : FunctionFreeFact sig) : f.toFact.toFunctionFreeFact (f.toFact_isFunctionFree) = f := by
  unfold toFact
  unfold Fact.toFunctionFreeFact
  simp only
  rw [GeneralizedAtom.mk.injEq]
  constructor
  . simp
  . rw [List.map_attach_eq_pmap, List.pmap_map]
    simp

