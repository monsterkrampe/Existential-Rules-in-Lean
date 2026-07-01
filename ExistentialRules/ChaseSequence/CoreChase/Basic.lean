import ExistentialRules.ChaseSequence.ChaseBranch

import ExistentialRules.Models.Basic
import ExistentialRules.Models.Cores
import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.Basic
import ExistentialRules.Models.Basic
import ExistentialRules.Triggers.Basic
import ExistentialRules.AtomsAndFacts.Basic
import ExistentialRules.AtomsAndFacts.SubstitutionsAndHomomorphisms
import ExistentialRules.ChaseSequence.Termination.Basic
import ExistentialRules.ChaseSequence.Universality

import ExistentialRules.ChaseSequence.Deterministic

import BasicLeanDatastructures.List.EraseDupsKeepRight


variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {kb : KnowledgeBase sig}


namespace GroundTermMapping

  theorem hom_applyFact_isFunctionFree_eq_id (fs1 fs2 : FactSet sig) (f : Fact sig) (f_is_ff : f.isFunctionFree) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism fs1 fs2) : gtm.applyFact f = f := by
      rw [GeneralizedAtom.mk.injEq]
      constructor
      · rfl
      · apply List.map_id_of_id_on_all_mem
        intro gt gt_in
        specialize f_is_ff gt gt_in
        rcases f_is_ff with ⟨c, c_eq⟩
        rw [c_eq]
        exact @gtm_hom.left c

  theorem hom_on_db_id (f : Fact sig) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism kb.db.toFactSet.val kb.db.toFactSet.val) (f_in_db : f ∈ kb.db.toFactSet.val) :
    gtm.applyFact f = f := by
      unfold GroundTermMapping.applyFact
      rw [GeneralizedAtom.mk.injEq]
      constructor
      · rfl
      · apply List.map_id_of_id_on_all_mem
        intro gt gt_in
        unfold GroundTermMapping.isHomomorphism at gtm_hom
        have db_funfree := kb.db.toFactSet.property.right
        unfold FactSet.isFunctionFree at db_funfree
        specialize db_funfree f f_in_db
        unfold Fact.isFunctionFree at db_funfree
        specialize db_funfree gt gt_in
        rcases db_funfree with ⟨c, c_eq⟩
        rcases f_in_db with ⟨ff, ff_in, ff_eq⟩
        unfold FunctionFreeFact.toFact at ff_eq
        rw [GeneralizedAtom.mk.injEq] at ff_eq
        rcases ff_eq with ⟨ff_pred_eq, ff_map_eq⟩
        rcases gtm_hom with ⟨gtm_c, gtm_sub⟩
        rw [c_eq]
        exact @gtm_c c

  @[grind .]
  theorem hom_on_db_term_id (t : GroundTerm sig) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism kb.db.toFactSet.val kb.db.toFactSet.val) (t_in_db_terms : t ∈ kb.db.toFactSet.val.terms) :
    gtm t = t := by
      have db_funfree := kb.db.toFactSet.property.right
      have ex_fact : ∃ f, f ∈ kb.db.toFactSet.val ∧ t ∈ f.terms := t_in_db_terms
      rcases ex_fact with ⟨f, f_in, f_in_ter⟩
      unfold FactSet.isFunctionFree at db_funfree
      specialize db_funfree f f_in t f_in_ter
      rcases db_funfree with ⟨c, c_eq⟩
      rw [c_eq]
      exact @gtm_hom.left c

  @[grind .]
  theorem sub_preserves_hom (A B C : FactSet sig) (sub : C ⊆ A) (h : GroundTermMapping sig) (h_hom : h.isHomomorphism  A B) : h.isHomomorphism C B := by
    rcases h_hom with ⟨idc, af⟩
    constructor
    · exact idc
    · intro f f_in_afc
      apply af
      apply h.apply_generalized_atom_set_subset_of_subset _ _ sub
      exact f_in_afc

  theorem id_is_hom {fs : FactSet sig} : GroundTermMapping.isHomomorphism id fs fs := by
    constructor
    · exact Subtype.ext rfl
    · intro f ⟨e, mem, eq⟩
      rw [TermMapping.apply_generalized_atom_eq_self_of_id_on_terms] at eq
      . grind
      . simp

end GroundTermMapping


namespace FactSet

  @[grind .]
  theorem ex_hom_sub (A B : FactSet sig) (sub : A ⊆ B) : ∃ (h : GroundTermMapping sig), h.isHomomorphism A B := by
    exists id
    constructor
    · intro gt
      simp only [id_eq]
    · intro f f_in
      rw [GroundTermMapping.mem_applyFactSet] at f_in; rcases f_in with ⟨e, e_mem, f_eq⟩
      simp only [GroundTermMapping.applyFact, TermMapping.apply_generalized_atom, List.map_id] at f_eq
      apply sub
      rw [f_eq]
      exact e_mem

  theorem empty_set_is_weak_core : (∅ : FactSet sig).isWeakCore := by
    intro gtm ghom
    constructor
    · intro _ _ contra _
      contradiction
    · intro h1 h2 h3 h4 h5
      unfold FactSet.terms at h3
      rcases h3 with ⟨_, contra, _⟩
      contradiction

  theorem homSubset_refl (fs : FactSet sig) : fs.homSubset fs := by
    constructor
    . apply Set.subset_refl
    . exists id
      exact GroundTermMapping.id_is_hom

  theorem isWeakCore_of_neq_sublist (l : List (Fact sig)):
    ¬ (∃ (sub : List (Fact sig)), sub ⊆ l ∧ sub.toSet ≠ l.toSet ∧ FactSet.homSubset sub.toSet l.toSet) -> (isWeakCore l.toSet) := by
      intro h
      simp only [not_exists] at h
      intro gtm gtm_hom
      simp only [not_and, ne_eq] at h
      have l_set_fin : l.toSet.finite := by exact List.finite_toSet l
      have inj_str := hom_strong_of_finite_of_injective l.toSet l_set_fin gtm gtm_hom

      specialize h (l.map gtm.applyFact)

      have af_sub_l : List.map gtm.applyFact l ⊆ l := by
        rw [List.subset_def]
        intro f f_in_l
        rw [List.mem_map] at f_in_l
        rcases f_in_l with ⟨f', f'_in_l, f'_eq⟩
        rcases gtm_hom with ⟨gtm_c, gtm_af⟩

        specialize gtm_af f
        rw [← List.mem_toSet]
        apply gtm_af
        unfold GroundTermMapping.applyFactSet
        exists f'

      specialize h af_sub_l

      have hom_subset : homSubset (l.map gtm.applyFact).toSet l.toSet := by
        rcases gtm_hom with ⟨gtm_c, gtm_af⟩
        unfold homSubset
        have : gtm.applyFactSet l.toSet = (List.map gtm.applyFact l).toSet := by
          apply Set.ext
          intro e
          rw [List.mem_toSet, List.mem_map]
          unfold GroundTermMapping.applyFactSet
          constructor
          . intro h2
            rcases h2 with ⟨f, f_in, f_eq⟩
            exists f
          . intro h2
            rcases h2 with ⟨f, f_in, f_eq⟩
            exists f

        constructor
        · rw [← this]
          exact gtm_af
        · exists gtm
          constructor
          . exact gtm_c
          . rw [this]; apply Set.subset_refl

      cases Decidable.em (l ⊆ l.map gtm.applyFact) with
      | inl l_sub_mapped =>
        have eq : (l.map gtm.applyFact).toSet = l.toSet := by
          simp_all only [not_true_eq_false, imp_false, Classical.not_not]

        rw [propext (and_iff_right_of_imp inj_str)]
        let terms_list := (l.flatMap GeneralizedAtom.terms).eraseDupsKeepRight
        have nodup_terms_list : terms_list.Nodup := by
          apply List.nodup_eraseDupsKeepRight
        have mem_terms_list : ∀ e, e ∈ (terms l.toSet) ↔ e ∈ terms_list := by
          simp only [terms_list]
          intro e
          rw [List.mem_eraseDupsKeepRight]
          unfold FactSet.terms
          simp only [List.mem_flatMap]
          constructor
          . intro h
            rcases h with ⟨f, f_in_l, e_in_ft⟩
            exists f
          . intro h
            rcases h with ⟨f, f_in_l, e_in_ft⟩
            exists f


        rw [Function.injective_set_list_equiv mem_terms_list]
        rw [Function.injectiveList_iff_length_imageList_eq_of_nodup]

        apply List.length_eraseDupsKeepRight_eq_of_same_elements
        intro gt
        specialize mem_terms_list gt

        unfold terms_list at mem_terms_list
        rw [List.mem_eraseDupsKeepRight] at mem_terms_list
        rw [← mem_terms_list, ← eq]

        have eq2 : gt ∈ List.flatMap GeneralizedAtom.terms (List.map gtm.applyFact l) ↔ gt ∈ terms (List.map gtm.applyFact l).toSet := by grind

        rw [← eq2]
        unfold terms_list

        rw [List.mem_map]; simp only [List.mem_eraseDupsKeepRight]; rw [← List.mem_map]
        rw [List.map_flatMap, List.flatMap_map]

        constructor
        · intro h2
          rw [List.mem_flatMap] at h2
          rcases h2 with ⟨f, f_in, f_eq⟩
          rw [List.mem_flatMap]
          exists f
        · intro h2
          rw [List.mem_flatMap]
          rw [List.mem_flatMap] at h2
          rcases h2 with ⟨f, f_in, f_eq⟩
          exists f

        exact nodup_terms_list

      | inr l_not_sub_mapped =>
        have neq : (l.map gtm.applyFact).toSet ≠ l.toSet := by
          intro contra
          apply l_not_sub_mapped
          intro f f_in_l
          rw [Set.ext_iff] at contra
          specialize contra f
          rw [← List.mem_toSet]
          rw [contra]
          rw [List.mem_toSet]
          exact f_in_l

        specialize h neq

        contradiction

  theorem exists_weak_core_for_list (l : List (Fact sig)) :
    ∃ (wc : FactSet sig), wc.isWeakCore ∧ wc.homSubset l.toSet := by
      induction d : l.length using Nat.strongRecOn generalizing l with
        | ind n ih =>
          by_cases h : (∃ (sub : List (Fact sig)), sub ⊆ l ∧ sub.toSet ≠ l.toSet ∧ FactSet.homSubset sub.toSet l.toSet)
          . rcases h with ⟨sub', h2, h3, h4⟩
            let sub := sub'.eraseDupsKeepRight
            have sub_eq_sub' : sub.toSet = sub'.toSet := by
              apply funext
              intro e
              apply propext
              change e ∈ sub.toSet ↔ e ∈ sub'.toSet
              have := @List.mem_toSet _ sub' e
              rw [this]
              have := @List.mem_toSet _ sub e
              rw [this]
              apply List.mem_eraseDupsKeepRight
            specialize ih sub.length  -- m < n
            by_cases n_zero : (n = 0)
            . exists ∅
              constructor
              . apply empty_set_is_weak_core
              . grind
            . have x : _ := ih (by
                apply Nat.lt_of_le_of_ne
                . rw [← d]; apply List.length_le_of_nodup_of_subset _ _ sub'.nodup_eraseDupsKeepRight; grind
                . intro contra; apply h3; apply Set.ext; simp only [List.mem_toSet, ← sub'.mem_eraseDupsKeepRight]; apply List.equiv_of_nodup_of_length_eq_of_subset <;> grind
              ) sub rfl
              rcases x with ⟨fs, fs_wc, fs_hom_ss_tl⟩
              exists fs
              constructor
              . exact fs_wc
              . rw [sub_eq_sub'] at fs_hom_ss_tl
                rcases fs_hom_ss_tl with ⟨fs_ss_tl, ⟨gtm ,ghom⟩⟩
                rw [homSubset]
                constructor
                have h2' : sub'.toSet ⊆ l.toSet := Set.subset_trans h2 fun e a => a
                . apply Set.subset_trans fs_ss_tl h2'
                . rcases h4 with ⟨h4_sub, h4_hom, h4_hom_hom⟩
                  exists gtm ∘ h4_hom
                  apply GroundTermMapping.isHomomorphism_compose
                  . exact h4_hom_hom
                  . exact ghom
          -- l.toSet is wc
          · have x : FactSet.isWeakCore l.toSet := by
              apply isWeakCore_of_neq_sublist
              exact h
            exists l.toSet
            constructor
            exact x
            rw [homSubset]
            constructor
            apply Set.subset_refl
            exists id
            exact GroundTermMapping.id_is_hom

  theorem exists_weak_core_for_finite_set (fs : FactSet sig) (fs_fin : fs.finite):
    ∃ (wc : FactSet sig), wc.isWeakCore ∧ wc.homSubset fs := by
      rcases fs_fin with ⟨l, nd, eq⟩
      have := exists_weak_core_for_list l
      rcases this with ⟨wc, wc_core, wc_sub⟩
      exists wc
      constructor
      · exact wc_core
      · have eq' : l.toSet = fs := by exact Set.ext l.toSet fs eq
        rw [eq'] at wc_sub
        exact wc_sub


end FactSet

namespace ChaseBranch

  @[grind .]
  theorem geq_none_if_none (scb : RegularChaseBranch obs kb) (n : Nat) (is_some : (scb.branch.get? n).isNone) : ∀ m, m ≥ n → (scb.branch.get? m).isNone := by simp only [Option.isNone_iff_eq_none] at *; grind

  @[grind .]
  theorem terminating_has_last_index (scb : RegularChaseBranch obs kb) : scb.terminates ↔ ∃ n, (scb.branch.infinite_list n) ≠ none ∧ ∀ m, m > n -> scb.branch.infinite_list m = none := by
    unfold ChaseDerivation.terminates
    constructor
    . intro h
      rcases h with ⟨n, h⟩
      induction n with
      | zero =>
        have := scb.database_first
        exists 0
        constructor
        rw [Option.ne_none_iff_isSome]
        exact scb.isSome_head
        intro m gt
        have := geq_none_if_none scb 0 (Option.isNone_iff_eq_none.mpr h) m (Nat.zero_le m)
        exact Option.isNone_iff_eq_none.mp this
      | succ n ih =>
        cases eq : scb.branch.infinite_list n with
        | none => apply ih; exact eq
        | some _ =>
          exists n
          rw [eq]
          simp only [ne_eq, reduceCtorEq, not_false_eq_true, gt_iff_lt, true_and]
          intro m n_lt_m
          have := geq_none_if_none scb (n+1) (Option.isNone_iff_eq_none.mpr h) m (Nat.succ_le_of_lt n_lt_m)
          exact Option.isNone_iff_eq_none.mp this
    . intro h
      rcases h with ⟨n, _, h⟩
      exists n+1
      apply h
      simp only [gt_iff_lt, Nat.lt_add_one]

  @[grind .]
  theorem leq_some_if_some (cb : RegularChaseBranch obs kb) (n : Nat) (is_some : (cb.branch.get? n).isSome) : ∀ m, m ≤ n → (cb.branch.get? m).isSome := by
    intro m leq
    simp only [Option.isSome_iff_ne_none] at *
    grind

  @[grind .]
  theorem ex_prev_node_at_each_leq (cb : RegularChaseBranch obs kb) (n : Nat) (is_some : (cb.branch.get? n).isSome) : ∀ m, m ≤ n → ∃ cn, cn ∈ (cb.branch.get? m) := by
    intro m leq
    have := leq_some_if_some cb n is_some m leq
    exact Option.isSome_iff_exists.mp this

  theorem origin_isSome (cb : RegularChaseBranch obs kb) (n : Nat) {node : RegularChaseNode obs kb.rules} (eq : cb.branch.get? (n + 1) = node) : node.origin.isSome := by
    have ex_before := ex_prev_node_at_each_leq cb n (by rw [Option.isSome_iff_ne_none]; grind) n (Nat.le_refl n)
    rcases ex_before with ⟨before, before_eq⟩
    have trg_ex := cb.triggers_exist n before before_eq node eq
    rcases trg_ex with ⟨isSome, _⟩
    exact isSome

  def getOriginList (scb : RegularChaseBranch obs kb) (n : Nat) (idx_l : List Nat) (idx_l_eq : (idx_l = List.range' 1 n)) (term : (scb.branch.infinite_list n).isSome) :
   (List ((trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length)) :=
      idx_l.pmap (fun m hm => (((scb.branch.infinite_list m).get (by
          have m_in : m ∈ idx_l := hm
          rw [idx_l_eq, List.mem_range'_1] at m_in
          subst idx_l
          have := leq_some_if_some scb n term m (by grind)
          exact Eq.symm (Bool.le_antisymm (fun a => this) (congrFun rfl))
        )).origin.get (by
          have m_in : m ∈ idx_l := hm
          rw [idx_l_eq, List.mem_range'_1] at m_in
          subst idx_l
          have := leq_some_if_some scb n term m (by grind)
          have := @origin_isSome _ _ _ _ _ _ scb (m - 1)
          have ex_cm : ∃ cm, cm ∈ scb.branch.get? m :=
            ex_prev_node_at_each_leq scb n term m (by grind)
          rcases ex_cm with ⟨cm, cm_eq⟩
          have eq : m - 1 + 1 = m := Nat.sub_add_cancel m_in.left
          rw [eq] at this
          specialize this cm_eq
          have : scb.branch.infinite_list m = some cm := Option.mem_def.mp cm_eq
          grind
        ))) (by
          intro m m_in
          exact m_in
        )

end ChaseBranch

