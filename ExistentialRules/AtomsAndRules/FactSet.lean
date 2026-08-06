/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

import BasicLeanDatastructures.List.AllListsOfLength
public import BasicLeanDatastructures.List.Basic
import BasicLeanDatastructures.List.EraseDupsKeepRight
public import BasicLeanDatastructures.Set.Basic
public import BasicLeanDatastructures.Set.Finite

public import ExistentialRules.AtomsAndRules.Fact

/-!
# FactSet

A `FactSet` is plainly a `Set` of `Fact`s.
-/

public section

abbrev FactSet (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] := Set (Fact sig)

namespace FactSet

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- The predicate symbols of a `FactSet` are the predicate symbols from all facts. -/
@[expose]
def predicates (fs : FactSet sig) : Set sig.P := fun p => ∃ f, f ∈ fs ∧ f.predicate = p

/-- The terms of a `FactSet` are the terms from all facts. -/
@[expose]
def terms (fs : FactSet sig) : Set (GroundTerm sig) := fun t => ∃ f, f ∈ fs ∧ t ∈ f.terms

/-- The constants of a `FactSet` are the constants from all facts. -/
@[expose]
def constants (fs : FactSet sig) : Set sig.C := fun c => ∃ f, f ∈ fs ∧ c ∈ f.constants

/-- The function symbols of a `FactSet` are the function symbols from all facts. -/
@[expose]
def function_symbols (fs : FactSet sig) : Set (SkolemFS sig) := fun func => ∃ f, f ∈ fs ∧ func ∈ f.function_symbols

/-- A `FactSet` is function free if all of its facts are. -/
@[expose]
def isFunctionFree (fs : FactSet sig) : Prop := ∀ f, f ∈ fs -> f.isFunctionFree

/-- When converting a list to a `FactSet`, the terms remain the same. -/
@[simp, grind =]
theorem mem_terms_toSet {l : List (Fact sig)} : ∀ t, t ∈ FactSet.terms (l.toSet) ↔ t ∈ l.flatMap GeneralizedAtom.terms := by
  intro t; rw [List.mem_flatMap]
  constructor <;> (intro ⟨f, f_mem, t_mem⟩; exists f; grind)

/-- The a `FactSet` is a subset of another, then their terms share this subset relation. -/
@[grind ->]
theorem terms_subset_of_subset {fs1 fs2 : FactSet sig} : fs1 ⊆ fs2 -> fs1.terms ⊆ fs2.terms := by
  intro sub t ⟨f, f_mem, t_mem⟩; exists f; exact ⟨sub _ f_mem, t_mem⟩

/-- The terms of the union of two `FactSet`s are the union of the terms of both sets. -/
@[simp, grind =]
theorem terms_union {fs1 fs2 : FactSet sig} : (fs1 ∪ fs2).terms = fs1.terms ∪ fs2.terms := by
  ext t
  constructor
  . rintro ⟨f, f_mem, t_mem⟩; cases f_mem with | inl f_mem => apply Or.inl; exists f | inr f_mem => apply Or.inr; exists f
  . intro t_mem; cases t_mem with
    | inl t_mem => rcases t_mem with ⟨f, f_mem, t_mem⟩; exists f; grind
    | inr t_mem => rcases t_mem with ⟨f, f_mem, t_mem⟩; exists f; grind

/-- If a `FactSet` is finite, so are its terms. -/
@[grind ->]
theorem terms_finite_of_finite (fs : FactSet sig) (finite : fs.finite) : fs.terms.finite := by
  rcases finite with ⟨l, nodup, finite⟩
  exists (l.map GeneralizedAtom.terms).flatten.eraseDupsKeepRight
  constructor
  . apply List.nodup_eraseDupsKeepRight
  . intro e
    constructor
    . intro in_l
      unfold FactSet.terms
      simp [List.mem_eraseDupsKeepRight, List.mem_flatten] at in_l
      rcases in_l with ⟨terms, ex_f, e_in_terms⟩
      rcases ex_f with ⟨f, f_in_l, terms_eq⟩
      exists f
      grind
    . intro in_fs
      unfold FactSet.terms at in_fs
      simp [List.mem_eraseDupsKeepRight, List.mem_flatten]
      rcases in_fs with ⟨f, f_in_fs, e_in_f⟩
      exists f.terms
      grind

/-- When converting a list to a `FactSet`, the constants remain the same. -/
@[simp, grind =]
theorem mem_constants_toSet {l : List (Fact sig)} : ∀ c, c ∈ FactSet.constants (l.toSet) ↔ c ∈ l.flatMap Fact.constants := by
  intro t; rw [List.mem_flatMap]
  constructor <;> (rintro ⟨f, f_mem, t_mem⟩; exists f; grind)

/-- A constant occurs in the fact set iff it occurs as a constant in one of its terms. -/
theorem mem_constants_iff_mem_terms {fs : FactSet sig} : ∀ {c}, c ∈ fs.constants ↔ ∃ t ∈ fs.terms, c ∈ t.constants := by
  unfold constants terms Fact.constants
  simp only [List.mem_flatMap]
  intro c
  constructor
  . intro ⟨f, f_mem, ⟨t, t_mem, c_mem⟩⟩; exists t; constructor; exists f; exact c_mem
  . intro ⟨t, ⟨f, f_mem, t_mem⟩, c_mem⟩; exists f; constructor; exact f_mem; exists t

/-- The a `FactSet` is a subset of another, then their constants share this subset relation. -/
@[grind ->]
theorem constants_subset_of_subset {fs1 fs2 : FactSet sig} : fs1 ⊆ fs2 -> fs1.constants ⊆ fs2.constants := by
  intro sub c ⟨f, f_mem, c_mem⟩; exists f; exact ⟨sub _ f_mem, c_mem⟩

/-- The constants of the union of two `FactSet`s are the union of the constants of both sets. -/
@[simp, grind =]
theorem constants_union {fs1 fs2 : FactSet sig} : (fs1 ∪ fs2).constants = fs1.constants ∪ fs2.constants := by
  -- NOTE: same proof as terms_union
  ext t
  constructor
  . rintro ⟨f, f_mem, t_mem⟩; cases f_mem with | inl f_mem => apply Or.inl; exists f | inr f_mem => apply Or.inr; exists f
  . intro t_mem; cases t_mem with
    | inl t_mem => rcases t_mem with ⟨f, f_mem, t_mem⟩; exists f; grind
    | inr t_mem => rcases t_mem with ⟨f, f_mem, t_mem⟩; exists f; grind

/-- If a `FactSet` is finite, so are its constants. -/
@[grind ->]
theorem constants_finite_of_finite (fs : FactSet sig) (fin : fs.finite) : fs.constants.finite := by
  rcases fin with ⟨l, _, l_eq⟩
  exists (l.flatMap Fact.constants).eraseDupsKeepRight
  constructor
  . apply List.nodup_eraseDupsKeepRight
  . intro c
    rw [List.mem_eraseDupsKeepRight]
    rw [List.mem_flatMap]
    unfold constants
    constructor
    . intro h
      rcases h with ⟨f, f_mem, c_mem⟩
      rw [l_eq] at f_mem
      exists f
    . intro h
      rcases h with ⟨f, f_mem, c_mem⟩
      rw [← l_eq] at f_mem
      exists f

/-- A `FactSet` is finite if both its predicates and terms are. This holds since the fact set must be a subset of all facts that can possibly be constructed using the prediactes and terms available. This overapproximation is easily shown to be finite. -/
@[grind ->]
theorem finite_of_preds_finite_of_terms_finite (fs : FactSet sig) : fs.predicates.finite -> fs.terms.finite -> fs.finite := by
  intro preds_fin terms_fin
  rcases preds_fin with ⟨preds, _, preds_eq⟩
  rcases terms_fin with ⟨terms, _, terms_eq⟩

  let overapproximation : FactSet sig := fun f => f.predicate ∈ fs.predicates ∧ (∀ t, t ∈ f.terms -> t ∈ fs.terms)
  have overapproximation_fin : overapproximation.finite := by
    exists (preds.flatMap (fun p =>
      (all_lists_of_length terms (sig.arity p)).attach.map (fun ⟨ts, mem⟩ =>
        {
          predicate := p
          terms := ts
          arity_ok := ((mem_all_lists_of_length terms (sig.arity p) ts).mp mem).left
        }
      )
    )).eraseDupsKeepRight

    constructor
    . apply List.nodup_eraseDupsKeepRight
    . intro f
      rw [List.mem_eraseDupsKeepRight]
      simp only [List.mem_flatMap, List.mem_map, List.mem_attach, true_and, Subtype.exists]
      constructor
      . intro _; constructor <;> grind
      . intro h
        rcases h with ⟨pred_mem, ts_mem⟩
        exists f.predicate
        constructor
        . rw [preds_eq]; exact pred_mem
        . exists f.terms
          exists (by
            rw [mem_all_lists_of_length]
            constructor
            . exact f.arity_ok
            . intro t t_mem; rw [terms_eq]; apply ts_mem; exact t_mem
          )

  apply Set.finite_of_subset_finite overapproximation_fin
  intro f f_mem
  constructor
  . exists f
  . intro t t_mem
    exists f

/-- For a list of terms in a given `FactSet`, we can find a list of facts in the fact set such that all the terms from the list occur in the list of facts. -/
theorem list_of_facts_for_list_of_terms {ts : List (GroundTerm sig)} {fs : FactSet sig} (ts_sub : ts.toSet ⊆ fs.terms) :
    ∃ (l : List (Fact sig)), l.toSet ⊆ fs ∧ ts ⊆ l.flatMap GeneralizedAtom.terms := by
  induction ts with
  | nil => exists []; constructor; intro _ mem; simp [List.mem_toSet] at mem; simp
  | cons t ts ih =>
    rcases (ts_sub t (by simp [List.mem_toSet])) with ⟨f, f_mem, t_mem⟩
    rcases ih (by intro _ mem; rw [List.mem_toSet] at mem; apply ts_sub; simp [List.mem_toSet, mem]) with ⟨l, l_sub, ts_sub⟩
    exists (f :: l); constructor
    . intro _ mem; rw [List.mem_toSet, List.mem_cons] at mem
      cases mem with
      | inl mem => rw [mem]; exact f_mem
      | inr mem => apply l_sub; rw [List.mem_toSet]; exact mem
    . grind

end FactSet

