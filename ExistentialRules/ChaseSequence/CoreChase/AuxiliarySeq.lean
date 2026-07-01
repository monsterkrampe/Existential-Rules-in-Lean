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

import ExistentialRules.ChaseSequence.CoreChase.FoldlSaveHist
import ExistentialRules.ChaseSequence.CoreChase.Homomorphisms
import ExistentialRules.ChaseSequence.CoreChase.Triggers
import ExistentialRules.ChaseSequence.CoreChase.Termination


variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {kb : KnowledgeBase sig}


namespace CoreChaseBranch

  noncomputable def generateNextCoreChaseBranchElement (ccn : CoreChaseNode kb.rules) (o : (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length) : CoreChaseNode kb.rules :=

      let trg_result : FactSet sig := (o.fst.val.mapped_head[o.snd]).toSet

      let trg_result_fin : trg_result.finite := List.finite_toSet o.fst.val.mapped_head[o.snd]

      let new_fs := ccn.core ∪ trg_result
      let new_fs_fin : new_fs.finite := by
        apply Set.union_finite_of_both_finite
        exact CoreChaseNode.core_finite ccn
        exact trg_result_fin

    let ex_new_fs_core := new_fs.exists_weak_core_for_finite_set new_fs_fin

    let new_fs_core := Classical.choose ex_new_fs_core
    let new_fs_core_h := Classical.choose_spec ex_new_fs_core

    let ccn_succ : CoreChaseNode kb.rules := {
        fs := new_fs
        fs_fin := new_fs_fin
        core := new_fs_core
        is_core := new_fs_core_h.left
        core_sse := new_fs_core_h.right
        origin := o
        fs_contains_origin_result := by intro _ eq; rw [Option.mem_def, Option.some_inj] at eq; rw [← eq]; apply Set.subset_union_of_subset_right; apply Set.subset_refl
      }

    ccn_succ


  noncomputable def generateNextCoreChaseBranchElement_opt (ccn : CoreChaseNode kb.rules) (o : (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length) : Option (CoreChaseNode kb.rules) :=
    match Classical.propDecidable (o.fst.val.active ccn.core) with
      | isTrue _ =>
        generateNextCoreChaseBranchElement ccn o
      | isFalse _ =>
        none

  noncomputable def buildCoreChaseBranchFromChaseBranch (scb : RegularChaseBranch obs kb) (scb_term : scb.terminates) : CoreChaseBranch kb :=

    have term_n := Classical.choose scb_term


    let origin_list : List ((trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length) := scb.getOriginList term_n (List.range' 1 term_n) rfl sorry

    let init_ccn : CoreChaseNode kb.rules := {
              fs := kb.db.toFactSet
              fs_fin := kb.db.toFactSet.property.left
              core := kb.db.toFactSet
              is_core := db_isWeakCore kb
              core_sse := by
                constructor
                exact fun _ a => a
                exists id
                exact GroundTermMapping.id_is_hom
              origin := none,
              fs_contains_origin_result := by simp
              }

  /-
    origin_list = [o1, o2, o3]

    cn1 = generateNextCoreChaseBranchElement_usingTrigger init_ccn o1
    cn2 = generateNextCoreChaseBranchElement_usingTrigger cn1 o1
    cn3 = generateNextCoreChaseBranchElement_usingTrigger cn2 o1

    node_list = [init_ccn cn1, cn2, cn3]
  -/

  let node_list := foldl_save_hist_opt_nodup origin_list init_ccn generateNextCoreChaseBranchElement_opt

    let new_ccb : CoreChaseBranch kb := {


      branch := PossiblyInfiniteList.from_list node_list
      database_first := by
        rw [PossiblyInfiniteList.get?_from_list, ← List.head?_eq_getElem?]
        exact foldl_save_hist_opt_nodup_head_eq
          origin_list init_ccn generateNextCoreChaseBranchElement_opt

      triggers_active := by
        intro n before before_eq after after_eq
        have after_origin_some : after.origin ≠ none := by sorry -- weil nicht first
        exists (after.origin.get (Option.isSome_iff_ne_none.mpr after_origin_some))
        constructor
        exact Option.get_mem (Option.isSome_iff_ne_none.mpr after_origin_some)


        sorry

      triggers_exist := by
        simp only [PossiblyInfiniteList.get?_from_list]
        intro n before before_eq after after_eq
        have after_origin_some : after.origin ≠ none := by sorry -- weil nicht first


        let trg := (after.origin.get (Option.isSome_iff_ne_none.mpr after_origin_some)).fst
        let disj := (after.origin.get (Option.isSome_iff_ne_none.mpr after_origin_some)).snd
        let trg_result : FactSet sig := (trg.val.mapped_head[disj]).toSet
        let trg_result_fin : trg_result.finite := List.finite_toSet trg.val.mapped_head[disj]

        let new_fs := before.core ∪ trg_result
        let new_fs_fin : new_fs.finite := by
          apply Set.union_finite_of_both_finite
          exact CoreChaseNode.core_finite before
          exact trg_result_fin

        let ex_new_fs_core := new_fs.exists_weak_core_for_finite_set (Set.finite_of_subset_finite new_fs_fin fun e a => a)
        let core := Classical.choose ex_new_fs_core
        let core_wc := (Classical.choose_spec ex_new_fs_core).left
        let core_sub := (Classical.choose_spec ex_new_fs_core).right

        exists trg, disj, core, core_wc, core_sub
        sorry


      fairness := sorry
    }

  new_ccb



  theorem buildCoreChaseBranchFromChaseBranch_terminates (scb : RegularChaseBranch obs kb) (scb_term : scb.terminates) :
    (buildCoreChaseBranchFromChaseBranch scb scb_term).terminates := by sorry


  theorem existsNonTerminatingChaseBranchIfExistsNonTerminatingCoreChaseBranch (ccb : CoreChaseBranch kb) (ccb_term : ¬ ccb.terminates) : ∃ (scb : RegularChaseBranch obs kb), ¬ scb.terminates := by
    sorry



  theorem exTerminatingCoreChaseBranchIfExTerminatingChaseBranch (scb : RegularChaseBranch obs kb) (scb_term : scb.terminates) :
    ∃ (ccb : CoreChaseBranch kb), ccb.terminates := by
      rcases scb.terminating_has_last_index.mp scb_term with ⟨n_ter, some_at, none_beyond⟩
      exists buildCoreChaseBranchFromChaseBranch scb scb_term
      have := buildCoreChaseBranchFromChaseBranch_terminates scb scb_term
      grind


  theorem exTerminatingCoreChaseBranchIfExFiniteUniversalModel (ccb : CoreChaseBranch kb) (kb_det : kb.isDeterministic) : (∃ (fs : FactSet sig), fs.finite ∧ fs.universallyModelsKb kb) → ccb.terminates := by


    /-
    ccb : A_0 → A_1 → A_2 .....
    scb : B_1 → B_2 → B_3 .....
                B_n
    -/

    intro ⟨M, ⟨M_list, _, M_eq⟩, M_umod⟩

    apply Classical.byContradiction
    intro contra

    have ex_inf_scb := existsNonTerminatingChaseBranchIfExistsNonTerminatingCoreChaseBranch ccb contra
    rcases ex_inf_scb with ⟨scb, scb_non_term⟩

    have scb_all_some : ∀ (n : Nat), (scb.branch.infinite_list n).isSome := by
      intro n
      apply Classical.byContradiction
      intro contra
      simp only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at contra
      unfold ChaseDerivation.terminates ChaseDerivationSkeleton.terminates PossiblyInfiniteList.finite at scb_non_term
      simp at scb_non_term
      specialize scb_non_term n
      contradiction

    -- R = B^{res}_ω
    let R := scb.result

    have R_umod : R.universallyModelsKb kb := scb.deterministicChaseBranchResultUniversallyModelsKb kb_det

    have hom_M_R : ∃ (h : GroundTermMapping sig), h.isHomomorphism M R := by
      rcases M_umod with ⟨M_umod_l, M_umod_r⟩
      specialize M_umod_r R RegularChaseBranch.result_models_kb
      exact M_umod_r

    have hom_R_M : ∃ (h : GroundTermMapping sig), h.isHomomorphism R M := by
      rcases R_umod with ⟨R_umod_l, R_umod_r⟩
      specialize R_umod_r M M_umod.left
      exact R_umod_r

    rcases hom_M_R with ⟨h_M_R, hom_M_R⟩
    rcases hom_R_M with ⟨h_R_M, hom_R_M⟩

    rcases RegularChaseDerivationSkeleton.facts_mem_some_node_of_mem_result (M_list.map h_M_R.applyFact) (by
      intro f f_mem; apply hom_M_R.right; rw [GroundTermMapping.mem_applyFactSet]
      rw [List.mem_toSet, List.mem_map] at f_mem; rcases f_mem with ⟨e, e_mem, f_eq⟩
      exists e; rw [← M_eq, f_eq]; exact ⟨e_mem, rfl⟩)
    with ⟨node, node_mem, M_sub_node⟩

    have hom_M_node : h_M_R.isHomomorphism M node.facts := by
      constructor; exact hom_M_R.left
      intro f f_mem
      apply M_sub_node
      rw [List.mem_toSet, List.mem_map]
      rw [GroundTermMapping.mem_applyFactSet] at f_mem; rcases f_mem with ⟨e, e_mem, f_eq⟩
      exists e; rw [M_eq, f_eq]; exact ⟨e_mem, rfl⟩

    have hom_node_M : h_R_M.isHomomorphism node.facts M := by
      constructor; exact hom_R_M.left
      intro f f_mem
      apply hom_R_M.right
      apply h_R_M.apply_generalized_atom_set_subset_of_subset _ _ (RegularChaseDerivationSkeleton.facts_node_subset_result node node_mem)
      exact f_mem

    have node_finite := scb.facts_finite_of_mem ⟨node, node_mem⟩

    rcases node.facts.exists_weak_core_for_finite_set node_finite with ⟨node_core, node_core_isCore⟩

    -- the rest of the prove shall take scb up until node and then compute the core once
    -- we need to prove that a regular core chase branch with the same result exists (this could be a general theorem, i.e. computing the core after any finite number of steps does not make a difference for the result)
    -- then we need to argue that the result of this core chase branch is isomorphic to M (basically since node_core is isomorphic to M) and then we need to argue that the isomorphism preserves modelhood, i.e. that the result of the core chase branch is a model, which justifies that the core chase branch ends at this point. This also yields the desired contradiction.

    sorry

end CoreChaseBranch
