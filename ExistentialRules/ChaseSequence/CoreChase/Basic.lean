/-
Copyright 2026 Henrik Tscherny, Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

import BasicLeanDatastructures.List.Nodup
public import ExistentialRules.AtomsAndFacts.SubstitutionsAndHomomorphisms
public import ExistentialRules.Models.Cores

/-!

# Auxiliary Theorems for the Core Chase

We introduce a few auxiliary theorems on `GroundTermMapping`s and cores here.
Most notably, we prove that every finite set has a weak core.
Eventually, these theorems should move to more appropriate places.

-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace GroundTermMapping

/-- Applying a mapping that is the id on all constants on a function free fact does not change the fact as it only contains constants. -/
theorem applyFact_eq_self_of_isIdOnConstants_of_isFunctionFree
    {h : GroundTermMapping sig} (idOnConst : h.isIdOnConstants) : ∀ {f}, f.isFunctionFree -> h.applyFact f = f := by
  intro f func_free
  apply TermMapping.apply_generalized_atom_eq_self_of_id_on_terms
  intro t t_mem; rcases func_free t t_mem with ⟨c, eq⟩
  rw [eq]; exact idOnConst

/-- For two sets in a subset relation, the id mapping is always a homomorphism from the subset to its superset. -/
theorem isHomomorphism_id_of_subset {A B : FactSet sig} (sub : A ⊆ B) : isHomomorphism id A B := by
  constructor
  . simp [isIdOnConstants]
  . intro f f_mem; rw [mem_applyFactSet] at f_mem; rcases f_mem with ⟨e, e_mem, f_eq⟩
    suffices applyFact id e = e by apply sub; rw [f_eq, this]; exact e_mem
    apply TermMapping.apply_generalized_atom_eq_self_of_id_on_terms; simp

end GroundTermMapping


namespace FactSet

/-- The `homSubset` relation is reflexive. -/
theorem homSubset_refl {fs : FactSet sig} : fs.homSubset fs := by
  constructor
  . exact Set.subset_refl
  . exact ⟨_, GroundTermMapping.isHomomorphism_id_of_subset Set.subset_refl⟩

/-- The `homSubset` relation is transitive. -/
theorem homSubset_trans {A B C : FactSet sig} : A.homSubset B -> B.homSubset C -> A.homSubset C := by
  intro ab bc; constructor; exact Set.subset_trans ab.left bc.left
  rcases ab.right with ⟨g, g_hom⟩; rcases bc.right with ⟨h, h_hom⟩
  exists g ∘ h; apply GroundTermMapping.isHomomorphism_compose; exact h_hom; exact g_hom

/-- The empty fact set is a weak core. -/
theorem isWeakCore_empty : (∅ : FactSet sig).isWeakCore := by
  intro h hom
  constructor
  · intro _ _ _ contra; contradiction
  · intro _ _ _ ⟨_, contra, _⟩; contradiction

/-- If a list has no proper homomorphic sublist, then the list forms a weak core. -/
theorem isWeakCore_list_of_each_homSubset_eq {l : List (Fact sig)} :
    (∀ (sub : List (Fact sig)), homSubset sub.toSet l.toSet -> sub.toSet = l.toSet) -> isWeakCore l.toSet := by
  intro each_homSubset_eq h hom
  suffices h.injectiveSet (terms l.toSet) by exact ⟨hom_strong_of_finite_of_injective _ l.finite_toSet _ hom this, this⟩
  suffices (l.map h.applyFact).toSet = l.toSet by
    have terms_eq : ∀ t, t ∈ terms l.toSet ↔ t ∈ (l.flatMap GeneralizedAtom.terms).eraseDupsKeepRight := by
      intro _; rw [mem_terms_toSet, List.mem_eraseDupsKeepRight]
    rw [Function.injective_set_list_equiv terms_eq]
    rw [Function.injectiveList_iff_length_imageList_eq_of_nodup]
    . apply List.length_eraseDupsKeepRight_eq_of_same_elements
      have mapped_terms_eq : ∀ t, t ∈ (l.flatMap GeneralizedAtom.terms).map h ↔ t ∈ (l.map h.applyFact).flatMap GeneralizedAtom.terms := by
        intro t; simp only [List.map_flatMap, List.flatMap_map, GroundTermMapping.applyFact, TermMapping.apply_generalized_atom]
      have mapped_terms_eq' : ∀ t, t ∈ (l.flatMap GeneralizedAtom.terms).eraseDupsKeepRight.map h ↔ t ∈ (l.flatMap GeneralizedAtom.terms).map h := by
        intro t; simp only [List.mem_map, List.mem_eraseDupsKeepRight]
      rw [Set.ext_iff] at this; simp only [List.mem_toSet] at this
      intro t; rw [mapped_terms_eq', mapped_terms_eq]; simp only [List.mem_flatMap, this]
    . grind
  apply each_homSubset_eq
  have mapping_eq : h.applyFactSet l.toSet = (l.map h.applyFact).toSet := by
    unfold GroundTermMapping.applyFactSet; rw [TermMapping.apply_generalized_atom_set_toSet]; rfl
  constructor
  . rw [← mapping_eq]; exact hom.right
  . exists h; constructor; exact hom.left; rw [mapping_eq]; exact Set.subset_refl

/-- Every list has a weak core. I.e. it is either itself a weak core or has a proper homomorphic sublist that is a weak core. -/
theorem exists_weak_core_for_list (l : List (Fact sig)) :
    ∃ (wc : FactSet sig), wc.isWeakCore ∧ wc.homSubset l.toSet := by
  induction length_eq : l.length using Nat.strongRecOn generalizing l with
  | ind length ih =>
    cases Classical.em (∃ (sub : List (Fact sig)), homSubset sub.toSet l.toSet ∧ sub.toSet ≠ l.toSet) with
    | inr no_sub =>
      exists l.toSet; simp only [homSubset_refl, and_true]
      apply isWeakCore_list_of_each_homSubset_eq
      intro sub homSub
      apply Classical.byContradiction; intro contra
      apply no_sub; exists sub
    | inl ex_sub =>
      rcases ex_sub with ⟨sub, homSub, neq⟩
      have sub_toSet_eq : sub.eraseDupsKeepRight.toSet = sub.toSet := by apply Set.ext; simp
      suffices sub.eraseDupsKeepRight.length < length by
        rcases ih _ this sub.eraseDupsKeepRight rfl with ⟨wc, weakCore, wc_homSub⟩
        rw [sub_toSet_eq] at wc_homSub
        exists wc; simp only [weakCore, true_and]
        exact homSubset_trans wc_homSub homSub
      rw [← length_eq]
      cases Nat.le_iff_lt_or_eq.mp (List.length_le_of_nodup_of_subset sub.eraseDupsKeepRight l sub.nodup_eraseDupsKeepRight (by intro _; rw [List.mem_eraseDupsKeepRight, ← List.mem_toSet, ← List.mem_toSet]; exact homSub.left _)) with
      | inl lt => exact lt
      | inr eq => exfalso; apply neq; rw [← sub_toSet_eq]; apply Set.ext; simp only [List.mem_toSet]; apply List.equiv_of_nodup_of_length_eq_of_subset; exact sub.nodup_eraseDupsKeepRight; exact eq; intro _; rw [List.mem_eraseDupsKeepRight, ← List.mem_toSet, ← List.mem_toSet]; exact homSub.left _

/-- Each finite fact set has a weak core. -/
theorem exists_weak_core_for_set_of_finite {fs : FactSet sig} (fin : fs.finite):
    ∃ (wc : FactSet sig), wc.isWeakCore ∧ wc.homSubset fs := by
  rcases fin with ⟨l, _, eq⟩
  suffices fs = l.toSet by rw [this]; exact exists_weak_core_for_list l
  apply Set.ext; simp [eq]

end FactSet


namespace Database

/-- Each `Database` is a weak core. -/
theorem isWeakCore (db : Database sig) : db.toFactSet.val.isWeakCore := by
  intro gtm gtm_hom
  suffices ∀ t ∈ db.toFactSet.val.terms, gtm t = t by
    constructor
    . intro f ts_in_db f_nmem contra
      apply f_nmem
      simp only [GroundTermMapping.applyFact] at contra
      rw [TermMapping.apply_generalized_atom_eq_self_of_id_on_terms] at contra
      . exact contra
      . intro t t_mem; apply this; apply ts_in_db; exact t_mem
    . intro _ _ s_mem t_mem
      rw [this _ s_mem, this _ t_mem]
      simp
  intro t ⟨f, f_mem, t_mem⟩
  rcases  db.toFactSet.property.right _ f_mem t t_mem with ⟨c, t_eq⟩
  rw [t_eq]
  exact gtm_hom.left

end Database

