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

import ExistentialRules.ChaseSequence.CoreChase.Homomorphisms
import ExistentialRules.ChaseSequence.CoreChase.PseudoCoreChaseBranch
import ExistentialRules.ChaseSequence.CoreChase.Triggers
import ExistentialRules.ChaseSequence.CoreChase.Termination


variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {kb : KnowledgeBase sig}


namespace CoreChaseBranch


  @[grind .]
  theorem ccb_db_sub_scb_facts (scb : RegularChaseBranch obs kb) (ccb : CoreChaseBranch kb) (n : Nat) (scn : RegularChaseNode obs kb.rules) (init : CoreChaseNode kb.rules) (init_eq : init ∈ ccb.branch.infinite_list 0) (scn_eq : scb.branch.infinite_list n = some scn):
    init.fs ⊆ scn.facts := by
      have db_funfree := kb.db.toFactSet.property.right
      have init_eq' : init.fs = kb.db.toFactSet.val := first_fs_eq ccb init init_eq
      have scb_dbf := scb.database_first
      unfold PossiblyInfiniteList.head InfiniteList.head InfiniteList.get at scb_dbf

      induction n generalizing scn with
        | zero =>
          intro f f_in
          rw [init_eq', ← (scb_dbf _ scn_eq).right.left, scn.outgoingFacts_eq] at f_in
          exact f_in
        | succ n ih =>
          have prev_cn_ex : ∃ prev_cn, scb.branch.infinite_list n = some prev_cn:= by
            exact scb.ex_prev_node_at_each_leq (n + 1) (Option.isSome_of_mem scn_eq) n (Nat.le_add_right n 1)
          intro f f_in
          rcases prev_cn_ex with ⟨prev_cn, prev_cn_eq⟩
          specialize ih prev_cn (by grind) f f_in
          have := scb.f_in_next_if_isFunctionFree n prev_cn prev_cn_eq
          specialize this scn scn_eq f
          have f_in_prev_fs : f ∈ prev_cn.facts := ih
          apply this
          constructor
          exact f_in_prev_fs
          rw [init_eq'] at f_in
          exact db_funfree f f_in


  @[grind .]
  theorem get_origin_list_length_eq_term_n_scb (scb : RegularChaseBranch obs kb) (n : Nat) (term_at_n : (scb.branch.infinite_list n).isSome ∧ (scb.branch.infinite_list (n+1)).isNone)
    (origin_list : List ((trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length))
    (origin_list_eq : origin_list = scb.getOriginList n (List.range' 1 n) rfl term_at_n.left) :
      origin_list.length = n := by
        unfold ChaseBranch.getOriginList at origin_list_eq
        simp_all

  def prev_node_std (cb : RegularChaseBranch obs kb) (n : Nat) (is_some : (cb.branch.get? (n+1)).isSome) : RegularChaseNode obs kb.rules := by
    exact (cb.branch.get? n).get (by grind)


  theorem active_trigger_yields_next_chase_node_std (scb : RegularChaseBranch obs kb) (scn : RegularChaseNode obs kb.rules) (n : Nat) (scn_eq : scb.branch.infinite_list n = some scn) (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) (trg_act : trg.val.active scn.facts) :
    ∃ (scn_succ : RegularChaseNode obs kb.rules), scb.branch.infinite_list (n+1) = some scn_succ := by sorry


  @[grind .]
  theorem no_active_triggers_in_scb_if_empty_get_origin_list_empty (scb : RegularChaseBranch obs kb) (n : Nat) (term_at_n : (scb.branch.infinite_list n).isSome ∧ (scb.branch.infinite_list (n+1)).isNone) :
    scb.getOriginList n (List.range' 1 n) rfl term_at_n.left = [] → ¬ ∃ (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules), trg.val.active ((scb.branch.infinite_list 0).get (by
      by_cases c : n = 0
      subst c
      exact term_at_n.left
      have gt : n > 0 := Nat.zero_lt_of_ne_zero c
      exact scb.leq_some_if_some n term_at_n.left 0 (Nat.zero_le n)
    )).facts := by
      intro h
      apply Classical.byContradiction
      intro contra
      simp only [not_exists, Classical.not_forall, Classical.not_not] at contra
      rcases contra with ⟨trg, trg_loaded, trg_non_obs⟩
      unfold ChaseBranch.getOriginList at h
      let init_scn := (scb.branch.infinite_list 0).get (by
        by_cases c : n = 0
        subst c
        exact term_at_n.left
        have gt : n > 0 := Nat.zero_lt_of_ne_zero c
        exact scb.leq_some_if_some n term_at_n.left 0 (Nat.zero_le n)
      )
      have : ∃ (scn : RegularChaseNode obs kb.rules), (scb.branch.infinite_list 1) = some scn := by
        exact active_trigger_yields_next_chase_node_std scb init_scn 0 (by grind) trg ⟨trg_loaded, trg_non_obs⟩

      rcases this with ⟨scn, scn_eq⟩
      have : scb.getOriginList n (List.range' 1 n) rfl term_at_n.left ≠ [] := by
        unfold ChaseBranch.getOriginList List.pmap
        grind
      contradiction



  @[grind .]
  theorem no_succ_chase_node_if_not_exists_active_trigger (scb : RegularChaseBranch obs kb) (scn : RegularChaseNode obs kb.rules) (n m : Nat) (gt : m > n) (scn_eq : scb.branch.infinite_list n = some scn)
    (no_act_trg : ∀ (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules), ¬ trg.val.active scn.facts) : (scb.branch.infinite_list m).isNone := by
      apply Classical.byContradiction
      intro contra
      simp only [Option.isNone_iff_eq_none, ne_eq, ← Option.isSome_iff_ne_none] at contra
      have ex_cn_succ : ∃ (cn_succ : RegularChaseNode obs kb.rules), scb.branch.infinite_list (n+1) = some cn_succ := by
        exact ChaseBranch.ex_prev_node_at_each_leq scb m contra (n + 1) gt

      rcases ex_cn_succ with ⟨cn_succ, cn_succ_eq⟩
      have trg_act := scb.triggers_active n
      unfold PossiblyInfiniteList.drop InfiniteList.drop PossiblyInfiniteList.tail PossiblyInfiniteList.head InfiniteList.head InfiniteList.get InfiniteList.tail InfiniteList.get at trg_act
      simp only [Nat.succ_eq_add_one, Nat.zero_add] at trg_act
      specialize trg_act scn scn_eq cn_succ cn_succ_eq

      rcases trg_act with ⟨trg', trg'_in, trg'_act⟩
      specialize no_act_trg trg'.fst trg'_act
      contradiction



  theorem ex_list_for_set_if_finite (S : Set α) (S_fin : S.finite) : ∃ (l : List α), ∀ e, e ∈ l ↔ e ∈ S := by
    rcases S_fin with ⟨l, l_nd, l_eq⟩
    exists l

  noncomputable def generateNextCoreChaseBranchElement' (o : (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length) (last_node : CoreChaseNode kb.rules) : CoreChaseNode kb.rules :=


    let trg_result : FactSet sig := (o.fst.val.mapped_head[o.snd]).toSet

    let trg_result_fin : trg_result.finite := List.finite_toSet o.fst.val.mapped_head[o.snd]

    let new_fs := last_node.core ∪ trg_result

    let new_fs_fin : new_fs.finite := by
      apply Set.union_finite_of_both_finite
      exact CoreChaseNode.core_finite last_node
      exact trg_result_fin

    let ex_new_fs_core := new_fs.exists_weak_core_for_finite_set new_fs_fin

    let new_fs_core := Classical.choose ex_new_fs_core
    let new_fs_core_prop := Classical.choose_spec ex_new_fs_core


    let next_ccn : CoreChaseNode kb.rules :=
    {
      fs := new_fs
      fs_fin := new_fs_fin
      core := new_fs_core
      is_core := new_fs_core_prop.left
      core_sse := new_fs_core_prop.right
      origin := o
      fs_contains_origin_result := by intro _ eq; rw [Option.mem_def, Option.some_inj] at eq; rw [← eq]; apply Set.subset_union_of_subset_right; apply Set.subset_refl
    }

    next_ccn


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


  theorem exists_active_trigger_of_step [DecidableEq β] (origin_list : List ((trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length))
    (init_ccn : CoreChaseNode kb.rules) (node_list : (List (CoreChaseNode kb.rules × Option ((trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length))))
    (node_list_eq : node_list = foldl_save_hist_opt_nodup_trace origin_list init_ccn generateNextCoreChaseBranchElement_opt)
    (n : Nat) (h : n + 1 < node_list.length) (before after : CoreChaseNode kb.rules)
    (before_eq : before = (node_list.get ⟨n, (Nat.lt_of_succ_lt h)⟩).fst) (after_eq : after = (node_list.get ⟨n+1, Nat.lt_of_succ_le h⟩).fst) (origin_some : after.origin ≠ none) :
      (after.origin.get (Option.isSome_iff_ne_none.mpr origin_some)).fst.val.active before.core := by
        unfold foldl_save_hist_opt_nodup_trace at *

        have hstep : after ≠ before := by
          have := foldl_save_hist_opt_nodup_trace_adjacent_ne
            origin_list init_ccn generateNextCoreChaseBranchElement_opt n
            (Nat.lt_of_lt_of_eq h (congrArg List.length node_list_eq))
          subst node_list_eq after_eq before_eq
          -- because nodup
          sorry

        have hex :
          ∃ o ∈ origin_list,
            generateNextCoreChaseBranchElement_opt before o = some after := by sorry

        rcases hex with ⟨o, ho_mem, hgen⟩

        unfold generateNextCoreChaseBranchElement_opt at hgen

        cases hdec :
          Classical.propDecidable ((after.origin.get (Option.isSome_iff_ne_none.mpr origin_some)).fst.val.active before.core) with
        | isTrue hactive =>
          exact hactive
        | isFalse hnot =>
          -- then result is none → contradiction
            simp_all
            sorry


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

    intro ⟨M, M_fin, M_umod⟩

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

    have monotonicity : ∀ (n : Nat), ((scb.branch.infinite_list (n)).get (scb_all_some (n))).facts ⊆ ((scb.branch.infinite_list (n+1)).get (scb_all_some (n+1))).facts := by
      intro n f f_in
      exact scb.facts_sub_all_succ_facts n 1 ((scb.branch.get? n).get (scb_all_some n)) ((scb.branch.get? (n+1)).get (scb_all_some (n+1)))
        (Option.get_mem (scb_all_some n)) (Option.get_mem (scb_all_some (n + 1))) f f_in

    have f_first_somewhere : ∀ (f : Fact sig), f ∈ R → ∃ (n_min : Nat), f ∈ ((scb.branch.infinite_list (n_min)).get (scb_all_some (n_min))).facts ∧
      ∀ (m : Nat), m < n_min → ¬ f ∈ ((scb.branch.infinite_list (m)).get (scb_all_some (m))).facts := by

        intro f f_in_R
        simp only [R] at f_in_R

        rcases f_in_R with ⟨cn, cn_in1, cn_in2⟩
        have : ∃ n, cn ∈ scb.branch.get? n := InfiniteList.mem_iff.mp cn_in1
        rcases this with ⟨n, cn_eq⟩
        unfold PossiblyInfiniteList.get? at cn_eq
        -- the set of indices in the scb where f appears in scn.facts
        let Ix := fun (n : Nat) => f ∈ ((scb.branch.infinite_list n).get (scb_all_some n)).facts
        have Ix_non_empty : ∃ (n : Nat), Ix n := by
          simp only [Ix]
          exists n
          have eq : ((scb.branch.infinite_list n).get (scb_all_some n)) = cn := Option.get_of_eq_some (scb_all_some n) cn_eq
          rw [eq]
          exact Set.mem_of_subset_of_mem (fun e a => a) cn_in2

        -- well ordering principle
        have hmin := wop Ix Ix_non_empty
        rcases hmin with ⟨n_min, h1, h2⟩
        have t1 : f ∈ ((scb.branch.infinite_list n_min).get (scb_all_some n_min)).facts := h1
        have t2 : ∀ n, f ∈ ((scb.branch.infinite_list n).get (scb_all_some n)).facts → n_min ≤ n := h2

        have nin_before : ∀ (n : Nat), n < n_min → ¬ f ∈ ((scb.branch.infinite_list (n)).get (scb_all_some (n))).facts := by
          intro n lt contra
          have := h2 n contra
          grind

        exists n_min

    have ex_hom_U_An : ∃ (n : Nat) (gtm : GroundTermMapping sig), gtm.isHomomorphism M ((scb.branch.get? n).get (scb_all_some n)).facts := by
      sorry

    rcases ex_hom_U_An with ⟨n_max, ⟨gtm_U_Bn, gtm_U_Bn_hom⟩⟩

    let Bn := ((scb.branch.infinite_list n_max).get (scb_all_some n_max)).facts

    have ex_hom_Bn_U : ∃ (gtm : GroundTermMapping sig), gtm.isHomomorphism Bn M := by

      have sub : Bn ⊆ R := by
        have := scb.facts_sub_result n_max
        exact this ((scb.branch.infinite_list n_max).get (scb_all_some n_max)) (Option.eq_some_of_isSome (scb_all_some n_max))


      have ex_gtm_Bn_R : ∃ (gtm : GroundTermMapping sig), gtm.isHomomorphism Bn R := FactSet.ex_hom_sub Bn R sub
      rcases ex_gtm_Bn_R with ⟨gtm_Bn_R, gtm_Bn_R_hom⟩

      rcases hom_R_M with ⟨gtm_R_M, gtm_R_M_hom⟩
      exists (gtm_R_M ∘ gtm_Bn_R)
      apply GroundTermMapping.isHomomorphism_compose gtm_Bn_R gtm_R_M Bn R M gtm_Bn_R_hom gtm_R_M_hom


    have Bn_fin : Bn.finite := by sorry

    have ex_Bn_core : ∃ (Bn_core : FactSet sig), Bn_core.isWeakCore ∧ Bn_core.homSubset Bn := Bn.exists_weak_core_for_finite_set Bn_fin

    rcases ex_Bn_core with ⟨Bn_core, Bn_core_c, Bn_core_homsub⟩

    have ex_core_of_scn_step (scb : RegularChaseBranch obs kb) (n : Nat) (scn : RegularChaseNode obs kb.rules) (scn_eq : scb.branch.infinite_list n = some scn) :
      ∃ (c : FactSet sig), c.isWeakCore ∧ c.homSubset scn.facts := by sorry


    rcases (ex_core_of_scn_step scb n_max ((scb.branch.infinite_list n_max).get (scb_all_some n_max)) (Option.eq_some_of_isSome (scb_all_some n_max))) with ⟨Bn_core, Bn_core_wc, Bn_core_homsub⟩


    have : ∃ (n : Nat), ((ccb.branch.infinite_list n).get sorry).core = Bn_core := by sorry

    have ex_U_core : ∃ (c : FactSet sig), c.isWeakCore ∧ c.homSubset M := by

      have ex_wc_sub := FactSet.exists_weak_core_for_finite_set M M_fin
      rcases ex_wc_sub with ⟨c, wc, sub, ⟨gtm, gtm_hom⟩⟩
      exists c
      constructor
      exact wc
      exact ⟨sub, Exists.intro gtm gtm_hom⟩

    rcases ex_U_core with ⟨U_core, U_core_wc, U_core_homsub⟩

    have Bn_umod : Bn_core.universallyModelsKb kb := by sorry
    sorry

    -- contradiction


end CoreChaseBranch
