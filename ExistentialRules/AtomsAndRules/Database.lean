/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

import BasicLeanDatastructures.List.EraseDupsKeepRight

public import ExistentialRules.AtomsAndRules.FactSet
public import ExistentialRules.AtomsAndRules.FunctionFreeFact

/-!
# Database

A `Database` is a finite set of `FunctionFreeFact`s.
-/

public section

abbrev Database (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] := { X : Set (FunctionFreeFact sig) // X.finite }

namespace Database

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- Any `Database` can trivially be converted to a finite and function free `FactSet`. -/
@[expose]
def toFactSet (db : Database sig) : { fs : FactSet sig // fs.finite ∧ fs.isFunctionFree } := ⟨
  (fun f => ∃ f', f' ∈ db.val ∧ f'.toFact = f),
  (by
    rcases db.property with ⟨l, _, l_eq⟩
    exists (l.map FunctionFreeFact.toFact).eraseDupsKeepRight
    constructor
    . apply List.nodup_eraseDupsKeepRight
    . intro f
      rw [List.mem_eraseDupsKeepRight]
      rw [List.mem_map]
      simp only [l_eq]
      rfl
  ),
  (by
    intro f f_mem
    rcases f_mem with ⟨_, _, f_eq⟩
    rw [← f_eq]
    apply FunctionFreeFact.toFact_isFunctionFree
  ),
⟩

/-- Each `Database` has a finite set of constants. -/
@[expose]
def constants (db : Database sig) : { C : Set sig.C // C.finite } := ⟨
  fun c => ∃ (f : FunctionFreeFact sig), f ∈ db.val ∧ c ∈ f.terms,
  by
    rcases db.property with ⟨l, _, l_eq⟩
    exists (l.flatMap (fun f => f.terms)).eraseDupsKeepRight
    constructor
    . apply List.nodup_eraseDupsKeepRight
    . intro c
      rw [List.mem_eraseDupsKeepRight, List.mem_flatMap]
      constructor
      . intro h
        rcases h with ⟨f, f_mem, c_mem⟩
        exists f
        constructor
        . rw [l_eq] at f_mem
          exact f_mem
        . exact c_mem
      . intro h
        rcases h with ⟨f, f_mem, c_mem⟩
        exists f
        constructor
        . rw [← l_eq] at f_mem
          exact f_mem
        . exact c_mem
⟩

/-- When converting a `Database` to a `FactSet`, the constants remain the same. -/
@[simp, grind =]
theorem toFactSet_constants_same (db : Database sig) : db.toFactSet.val.constants = db.constants.val := by
  unfold toFactSet
  unfold constants
  unfold FactSet.constants
  simp only
  ext c
  constructor
  . intro h
    rcases h with ⟨f, f_mem, c_mem⟩
    unfold Fact.constants at c_mem
    rcases f_mem with ⟨f', f'_mem, f_eq⟩
    unfold FunctionFreeFact.toFact at f_eq
    exists f'
    grind
  . intro h
    rcases h with ⟨f, f_mem, c_mem⟩
    exists f.toFact
    constructor
    . exists f
    . unfold FunctionFreeFact.toFact
      unfold Fact.constants
      grind

end Database

