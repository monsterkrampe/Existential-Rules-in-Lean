import ExistentialRules.ChaseSequence.ChaseBranch

import ExistentialRules.ChaseSequence.CoreChase.CoreChaseBranch
import ExistentialRules.ChaseSequence.CoreChase.Homomorphisms


variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {kb : KnowledgeBase sig}


namespace CoreChaseBranch

  @[grind .]
  theorem ex_func_eq {disj_idx : Nat} {t : GroundTerm sig} {trg : RTrigger obs.toLaxObsolescenceCondition kb.rules} {lt : disj_idx < trg.val.rule.head.length} (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
    ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok := by
      cases cn_eq : t with
      | const _ =>
        rw [cn_eq] at t_mem_trg
        simp [PreTrigger.fresh_terms_for_head_disjunct, PreTrigger.functional_term_for_var, GroundTerm.func, GroundTerm.const] at t_mem_trg
      | func func ts arity_ok => exists func, ts, arity_ok

  @[grind .]
  theorem trg_loaded_in_fs_if_loaded_in_core (cb : CoreChaseBranch kb) (n : Nat) (cn : CoreChaseNode kb.rules) (cn_eq : cn ∈ cb.branch.get? n) (trg : Trigger obs.toLaxObsolescenceCondition) :
    trg.loaded cn.core → trg.loaded cn.fs := by
      intro trg_loaded
      intro f f_in
      specialize trg_loaded f f_in
      exact cn.core_sse.left f trg_loaded

  @[grind .]
    theorem origin_trg_inactive_in_fs (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cn ∈ cb.branch.get? n) (cn_origin_some : cn.origin.isSome) :
      ¬ (cn.origin.get cn_origin_some).fst.val.active cn.fs := by
          have trg_ex := cb.triggers_exist (n - 1)
          by_cases c_lt : n = 0
          subst c_lt
          have dbf := cb.database_first
          grind
          have c_lt := Nat.zero_lt_of_ne_zero c_lt
          have ex_prev_cn := cb.ex_prev_cn_if_origin_some cn n cn_eq cn_origin_some
          rcases ex_prev_cn with ⟨prev_cn, prev_cn_eq⟩
          specialize trg_ex prev_cn prev_cn_eq cn (by grind)
          rcases trg_ex with ⟨trg, i, c, c_wc, c_sub, eq⟩
          intro contra
          rcases contra with ⟨loaded, non_obs⟩
          apply non_obs
          have len_eq : trg.val.mapped_head.length = trg.val.rule.head.length := by exact PreTrigger.length_mapped_head trg.val.toPreTrigger
          have lt : ↑i < (cn.origin.get cn_origin_some).fst.val.rule.head.length := by grind
          exists ⟨i, lt⟩
          rcases (ex_hom_fs_core cb n cn cn_eq) with ⟨gtm, gtm_hom⟩
          have := PreTrigger.satisfied_for_disj_of_mapped_head_contained (cn.origin.get cn_origin_some).fst.val.toPreTrigger cn.fs ⟨↑i, by grind⟩
          apply this
          simp_all
          exact Set.subset_union_of_subset_right trg.val.mapped_head[↑i].toSet prev_cn.core trg.val.mapped_head[↑i].toSet fun e a => a

  -- muss fs loaded in core oder loaded in fs
  @[grind .]
  theorem trg_obs_in_core_if_obs_in_fs_and_loaded_in_core (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cn ∈ cb.branch.get? n) (trg : Trigger obs.toLaxObsolescenceCondition) :
      (obs.cond trg.toPreTrigger cn.fs) ∧ (trg.loaded cn.core) → obs.cond trg.toPreTrigger cn.core := by
        simp only [obs, RestrictedObsolescence]
        intro ⟨trg_sat, trg_loaded⟩
        unfold PreTrigger.satisfied at *
        rcases trg_sat with ⟨i, gs, h1, h2⟩
        rcases (ex_hom_fs_core cb n cn cn_eq) with ⟨gtm, gtm_hom⟩
        have ex_eq_list : ∃ (tl : List (GroundTerm sig)), tl.toSet = cn.core.terms := by
          have := FactSet.terms_finite_of_finite cn.core (cb.core_finite _ _ cn_eq)
          rcases this with ⟨tl, h1, h2⟩
          exists tl
          exact Set.ext tl.toSet cn.core.terms h2

        rcases ex_eq_list with ⟨tl, tl_eq⟩
        have gtm_surj := gtm_fs_core_is_endo cb cn n cn_eq gtm gtm_hom
        have gtm_surj_eq := gtm.surjective_set_list_equiv (domain_set := tl.toSet) (domain_list := tl) (fun e => Eq.to_iff rfl) (image_set := tl.toSet) (image_list := tl) (fun e => Eq.to_iff rfl)
        rw [tl_eq] at gtm_surj_eq
        rw [gtm_surj_eq] at gtm_surj

        have ex_reps := gtm.exists_repetition_that_is_inverse_of_surj tl gtm_surj
        rcases ex_reps with ⟨rep, h⟩

        let rep_hom := gtm.repeat_fun (rep + 1)
        have rep_hom_hom := gtm.repeat_isHomomorphism (gtm_core_set_if_gtm_fs_set cn.core cn gtm gtm_hom) (rep + 1)
        have len_eq : trg.mapped_head.length = trg.rule.head.length := by exact PreTrigger.length_mapped_head trg.toPreTrigger
        have lt : ↑i < trg.mapped_head.length := by simp

        exists i, (rep_hom ∘ gs)

        constructor
        · intro v v_in
          have eq : trg.subs_for_mapped_head ⟨i, lt⟩ v = trg.subs v := by apply trg.apply_to_var_or_const_frontier_var i v v_in
          have one_more_eq : gtm.repeat_fun (rep + 1) (gs v) = gtm.repeat_fun rep (gtm (gs v)) := gtm.repeat_swap_one (gs v)
          simp only [Function.comp_apply]
          specialize h1 v v_in
          rw [← h1]

          simp only [rep_hom]
          rw [one_more_eq]
          specialize h (gs v) (by
            rw [Set.ext_iff] at tl_eq
            specialize tl_eq (gs v)
            rw [← List.mem_toSet, tl_eq]
            rw [h1]
            have terms_sub := FactSet.terms_subset_of_subset cn.core_sse.left
            rcases (cb.core_finite _ _ cn_eq) with ⟨cn_core_l, _, cn_core_l_eq⟩
            have eq : cn_core_l.toSet = cn.core := Set.ext cn_core_l.toSet cn.core cn_core_l_eq
            have t1 := @FactSet.mem_terms_toSet _ _ _ _ cn_core_l (trg.subs v)
            rw [eq] at t1
            rw [t1]
            have t2 := PreTrigger.mem_terms_mapped_body_iff trg.toPreTrigger (trg.subs v)
            have sub : trg.mapped_body ⊆ cn_core_l := by
              intro e e_in
              specialize cn_core_l_eq e
              rw [cn_core_l_eq]
              exact trg_loaded e e_in
            have := @Rule.frontier_subset_vars_body _ _ _ _ trg.rule
            sorry --grind
            )
          exact h

        · intro f f_in
          have rep_hom_hom' : GroundTermMapping.isHomomorphism rep_hom cn.fs cn.core := by
            simp only [rep_hom]
            have g1 := gtm_hom

            have gtm_endo : gtm.isHomomorphism cn.core cn.core := gtm_core_set_if_gtm_fs_set cn.core cn gtm gtm_hom
            have : ∀ k, GroundTermMapping.isHomomorphism (gtm.repeat_fun k) cn.core cn.core := by
              intro k
              induction k with
                | zero => exact GroundTermMapping.repeat_isHomomorphism gtm_endo 0
                | succ k ih =>
                  exact GroundTermMapping.repeat_isHomomorphism gtm_endo (k + 1)
            specialize this rep

            have g1_this_hom : GroundTermMapping.isHomomorphism ((gtm.repeat_fun rep) ∘ gtm) cn.fs cn.core := by
              have y := GroundTermMapping.isHomomorphism_compose gtm (gtm.repeat_fun rep) cn.fs cn.core cn.core g1 this
              exact y
            rw [Function.repeat_add', Function.repeat_once]
            exact g1_this_hom

          apply rep_hom_hom'.right

          unfold GroundSubstitution.apply_function_free_conj TermMapping.apply_generalized_atom_list at f_in
          rw [List.mem_toSet, List.mem_map] at f_in
          rcases f_in with ⟨a, ahl, ahr⟩
          rw [← GroundSubstitution.apply_function_free_atom.eq_def, GroundSubstitution.apply_function_free_atom_compose_of_isIdOnConstants _ _ (rep_hom_hom'.left)] at ahr
          rw [← ahr]
          simp only [Function.comp_apply]
          unfold GroundTermMapping.applyFactSet GroundTermMapping.applyFact
          apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
          apply h2
          rw [List.mem_toSet]
          unfold GroundSubstitution.apply_function_free_conj TermMapping.apply_generalized_atom_list
          rw [List.mem_map]
          exists a


  @[grind .]
  theorem trg_obs_in_fs_if_obs_in_core (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cn ∈ cb.branch.get? n) (trg : Trigger obs.toLaxObsolescenceCondition) :
    obs.cond trg.toPreTrigger cn.core → obs.cond trg.toPreTrigger cn.fs := by
      simp only [obs, RestrictedObsolescence]
      unfold PreTrigger.satisfied
      rcases (ex_hom_fs_core cb n cn cn_eq) with ⟨gtm, gtm_hom⟩
      intro ⟨i, gs, h1, h2⟩
      exists i, gs
      constructor
      intro v v_in
      exact h1 v v_in
      have sub := cn.core_sse.left
      apply Set.subset_trans h2 sub

  @[grind .]
  theorem trg_inactive_in_core_if_inactive_in_fs_and_loaded_in_core (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat)
    (cn_eq : cb.branch.infinite_list n = some cn) (trg : Trigger obs.toLaxObsolescenceCondition) :
    (¬ trg.active cn.fs ∧ trg.loaded cn.core) → ¬ trg.active cn.core := by
      intro ⟨trg_not_active_fs, trg_loaded_core⟩
      unfold Trigger.active at *
      rw [Classical.not_and_iff_not_or_not, Classical.not_not] at *
      have : ¬trg.loaded cn.fs ∨ (trg.loaded cn.fs ∧ obs.cond trg.toPreTrigger cn.fs) := by grind
      rcases this with trg_not_loaded | ⟨trg_loaded, trg_obs⟩
      left
      intro contra
      apply trg_not_loaded
      intro e e_in
      specialize contra e e_in
      exact cn.core_sse.left e contra
      right
      exact trg_obs_in_core_if_obs_in_fs_and_loaded_in_core cb cn n cn_eq trg ⟨trg_obs, trg_loaded_core⟩

  @[grind .]
    theorem origin_trg_obs_and_loaded_in_fs (cb : CoreChaseBranch kb) (n : Nat) (cn : CoreChaseNode kb.rules) (cn_eq : cb.branch.infinite_list n = some cn) (cn_origin_some : cn.origin.isSome) :
      (cn.origin.get cn_origin_some).fst.val.loaded cn.fs ∧ obs.cond (cn.origin.get cn_origin_some).fst.val.toPreTrigger cn.fs := by

        have n_gt : n > 0 := not_first_if_origin_some cb cn cn_origin_some n cn_eq
        have trg_active_origin := origin_trg_active_prev_core cb (n-1) cn (by rw [Nat.sub_add_cancel n_gt]; exact cn_eq)
          (cn.origin.get (Eq.symm (Bool.le_antisymm (fun a => cn_origin_some) (congrFun rfl))))
          (Option.get_mem (Eq.symm (Bool.le_antisymm (fun a => cn_origin_some) (congrFun rfl))))

        rcases trg_active_origin with ⟨trg_loaded, trg_non_obs⟩

        have ex_prev_node := cb.ex_prev_cn_if_origin_some cn n cn_eq cn_origin_some
        rcases ex_prev_node with ⟨prev_cn, prev_cn_eq⟩
        have fs_eq := next_fs_eq' cb (n-1) prev_cn cn prev_cn_eq (by rw [Nat.sub_add_cancel n_gt]; exact cn_eq)
        have trg_loaded_cn_fs : (cn.origin.get cn_origin_some).fst.val.loaded cn.fs := by
          intro f f_in
          specialize trg_loaded f f_in
          grind
        constructor
        exact trg_loaded_cn_fs
        have := origin_trg_inactive_in_fs cb cn n cn_eq cn_origin_some
        unfold Trigger.active at this
        simp only [Classical.not_and_iff_not_or_not, Classical.not_not] at this
        rcases this with not_loaded | is_obs
        contradiction
        exact is_obs


  theorem functional_term_originates_from_some_trigger {cb : CoreChaseBranch kb} (n : Nat) (cn : CoreChaseNode kb.rules) (cn_eq : cn ∈ cb.branch.get? n) (t : GroundTerm sig)
    (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok) (t_mem : t ∈ cn.core.terms) :
      let init_node := ((cb.branch.get? 0).get (cb_fist_isSome cb))
      t ∈ init_node.fs.terms ∨
      ∃ (m : Nat) (prev_cn : CoreChaseNode kb.rules), m ≤ n ∧ prev_cn ∈ cb.branch.get? m ∧
      ∃ o ∈ cn.origin, t ∈ o.fst.val.fresh_terms_for_head_disjunct o.snd.val (by rw [← PreTrigger.length_mapped_head]; exact o.snd.isLt) := by sorry


  theorem result_of_trigger_introducing_functional_term_occurs_in_chase_hom (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules)
    (disj_idx n : Nat) (trg: RTrigger obs.toLaxObsolescenceCondition kb.rules) (cn_eq : cn ∈ cb.branch.get? n)
    (t : GroundTerm sig ) (lt : disj_idx < trg.val.rule.head.length)
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) (t_mem_node : t ∈ cn.core.terms) :
      ∃ (h : GroundTermMapping sig), h.isHomomorphism (trg.val.mapped_head[disj_idx]'(by rw [PreTrigger.length_mapped_head]; exact lt)).toSet cn.core := by
        cases (functional_term_originates_from_some_trigger n cn cn_eq t (ex_func_eq t_mem_trg) t_mem_node) with
          | inl t_mem =>
            apply False.elim
            exact cb.func_term_not_mem_head (PreTrigger.term_functional_of_mem_fresh_terms _ t_mem_trg) t_mem
          | inr t_mem =>
            sorry

  @[grind .]
  theorem func_term_not_mem_head_core {cb : CoreChaseBranch kb} {t : GroundTerm sig} (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok) :
      ¬ t ∈ ((cb.branch.get? 0).get (cb_fist_isSome cb)).fs.terms := by
        intro t_mem
        simp only [cb.database_first] at t_mem
        rcases t_mem with ⟨f, f_mem, t_mem⟩
        rcases kb.db.toFactSet.property.right f f_mem t t_mem with ⟨c, t_eq⟩
        rcases t_is_func with ⟨_, _, _, t_eq'⟩
        rw [t_eq'] at t_eq
        simp [GroundTerm.func_neq_const] at t_eq


    @[grind .]
  theorem ex_next_if_ex_active_trigger (cb : CoreChaseBranch kb) (n : Nat) (cn : CoreChaseNode kb.rules) (cn_eq : cn ∈ cb.branch.get? n)
    (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) (trg_act : trg.val.active cn.core) :
        ∃ (cn' : CoreChaseNode kb.rules), cn' ∈ cb.branch.infinite_list (n+1) := by sorry


  theorem trigger_inactive_after_application (cb : CoreChaseBranch kb) (cn cn_succ : CoreChaseNode kb.rules) (n k : Nat)
  (cn_eq : cb.branch.infinite_list n = some cn) (cn_succ_eq : cb.branch.infinite_list (n + k) = some cn_succ) (cn_origin_some : cn.origin.isSome) :

    ¬ (cn.origin.get cn_origin_some).fst.val.active cn_succ.core := by

      have ex_prev_node := cb.ex_prev_cn_if_origin_some cn n cn_eq cn_origin_some
      rcases ex_prev_node with ⟨prev_cn, prev_cn_eq⟩

      induction k generalizing cn_succ with
        | zero =>
          have eq : cn = cn_succ := by grind
          subst eq
          have trg_inactive_fs := origin_trg_inactive_in_fs cb cn n cn_eq cn_origin_some
          by_cases c : (cn.origin.get cn_origin_some).fst.val.loaded cn.core
          have trg_inactive_core := trg_inactive_in_core_if_inactive_in_fs_and_loaded_in_core cb cn n cn_eq (cn.origin.get cn_origin_some).fst.val ⟨trg_inactive_fs, c⟩
          exact trg_inactive_core
          unfold Trigger.active
          rw [Classical.not_and_iff_not_or_not, Classical.not_not]
          left
          exact c

        | succ k ih =>

          have n_gt : n > 0 := not_first_if_origin_some cb cn cn_origin_some n cn_eq

          have trg_active_prev_cn_core : (cn.origin.get cn_origin_some).fst.val.active prev_cn.core := by
            have := origin_trg_active_prev_core cb (n-1) cn (by rw [Nat.sub_add_cancel n_gt]; exact cn_eq)
            sorry

          have trg_inactive_cn_core : ¬(cn.origin.get cn_origin_some).fst.val.active cn.core := by
              have trg_inactive_fs := origin_trg_inactive_in_fs cb cn n cn_eq cn_origin_some
              by_cases c : (cn.origin.get cn_origin_some).fst.val.loaded cn.core
              have trg_inactive_core := trg_inactive_in_core_if_inactive_in_fs_and_loaded_in_core cb cn n cn_eq (cn.origin.get cn_origin_some).fst.val ⟨trg_inactive_fs, c⟩
              exact trg_inactive_core
              unfold Trigger.active
              rw [Classical.not_and_iff_not_or_not, Classical.not_not]
              left
              exact c


          have ex_cn_k : ∃ (cn_k : CoreChaseNode kb.rules), cn_k ∈ cb.branch.infinite_list (n + k) :=
            cb.ex_prev_node_at_each_leq (n + k + 1) (Option.isSome_of_mem cn_succ_eq) (n + k) (Nat.le_add_right (n + k) 1)

          rcases ex_cn_k with ⟨cn_k, cn_k_eq⟩
          specialize ih cn_k cn_k_eq

          unfold Trigger.active at ih
          have ih' : ¬(cn.origin.get cn_origin_some).fst.val.loaded cn_k.core ∨ (obs.cond (cn.origin.get cn_origin_some).fst.val.toPreTrigger cn_k.core ∧ (cn.origin.get cn_origin_some).fst.val.loaded cn_k.core) := by grind
          cases ih' with
            | inl trg_not_loaded_k =>

              intro ⟨trg_loaded_succ, trg_non_obs_succ⟩

              have trg_prev_cn_loaded := trg_active_prev_cn_core.left
              have trg_prev_cn_non_obs := trg_active_prev_cn_core.right

              have := origin_trg_obs_and_loaded_in_fs cb n cn cn_eq cn_origin_some
              have trg_obs_cn_fs := this.right
              have trg_loaded_cn_fs := this.left

              have l1 := trg_active_prev_cn_core.left
              have l2 := trg_inactive_cn_core
              have l3 := trg_not_loaded_k
              have l4 := trg_loaded_succ

              have trg_obs_cn_core := trg_obs_in_core_if_obs_in_fs_and_loaded_in_core cb cn n cn_eq (cn.origin.get cn_origin_some).fst.val ⟨trg_obs_cn_fs, sorry⟩

              unfold PreTrigger.loaded at l1 l2 l3

              have ex_f_nin : ∃ (f : Fact sig), f ∈ (cn.origin.get cn_origin_some).fst.val.mapped_body.toSet ∧ ¬ f ∈ cn_k.core := by
                unfold Subset instHasSubsetSet at l3
                simp at l3
                exact l3

              rcases ex_f_nin with ⟨f, f_in, f_nin⟩

              have eq : n - 1 + (k + 1) = n + k := by grind
              have ex_cm := cb.ex_intermediate_if_f_mem_not_mem_succ prev_cn cn_k (n-1) (k+1) prev_cn_eq (by rw [eq]; exact cn_k_eq) f (trg_prev_cn_loaded f f_in) f_nin

              rcases ex_cm with ⟨cm, cm_eq⟩

              have t_mem : ∃ (t : GroundTerm sig), t ∈ prev_cn.core.terms ∧ ¬ t ∈ cm.core.terms ∧ t ∈ cn_succ.core.terms := by

                have s1 := FactSet.terms_subset_of_subset cn.core_sse.left
                have s2 := FactSet.terms_subset_of_subset cn_k.core_sse.left
                have s3 := FactSet.terms_subset_of_subset cn_succ.core_sse.left
                sorry

              rcases t_mem with ⟨t, t_in_prev_cn, t_nin_cm, t_in_cn_succ⟩
              have t_in_cn_fs : t ∈ cn.fs.terms := by sorry
              cases eq : t with
                | const c =>

                  have ex_f : ∃ (f : Fact sig), f ∈ cn.fs ∧ t ∈ f.terms := t_in_cn_fs
                  rcases ex_f with ⟨f, f_in_cn_fs, t_in_f⟩

                  have := f_isFunctionFree_in_next_if_some cb (n + k) cn_k cn_k_eq
                  specialize this cn_succ cn_succ_eq


                  have f_is_ff : f.isFunctionFree := by
                    unfold Fact.isFunctionFree
                    intro gt gt_in
                    exists c
                    sorry

                  specialize this f
                  have ff_in_all_succ := f_isFunctionFree_in_geq cb n k cn cn_eq
                  specialize ff_in_all_succ cn_k cn_k_eq
                  have f_in_cn_k_fs : f ∈ cn_k.fs := by
                    apply ff_in_all_succ
                    exact ⟨f_in_cn_fs, f_is_ff⟩
                  have f_nin_cn_k_fs : ¬ f ∈ cn_k.fs := by
                    sorry
                  contradiction

                | func func ts arity_ok =>
                  have ex_snd_trg : ∃ (m : Nat), m < n ∧ t ∈ FactSet.terms (((cb.branch.infinite_list m).get sorry).origin_result sorry).toSet := by sorry
                  rcases ex_snd_trg with ⟨m, lt, t_in⟩
                  sorry

            | inr trg_obs_loaded =>
              rcases trg_obs_loaded with ⟨trg_obs_k_core, trg_loaded_k_core⟩
              intro contra
              apply contra.right
              have trg_loaded_cn_succ_core := contra.left
              have trg_obs_succ_fs : obs.cond (cn.origin.get cn_origin_some).fst.val.toPreTrigger cn_succ.fs := by
                have := before_core_sub_after_fs cb (n + k) cn_k cn_succ cn_k_eq cn_succ_eq
                exact obs.monotone this trg_obs_k_core
              have := trg_obs_in_core_if_obs_in_fs_and_loaded_in_core cb cn_succ (n + (k + 1)) cn_succ_eq ((cn.origin.get cn_origin_some).fst.val) ⟨trg_obs_succ_fs, trg_loaded_cn_succ_core⟩
              exact this


   @[grind .]
  theorem no_succ_chase_node_if_not_exists_active_trigger_core (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cn ∈ cb.branch.get? n)
    (no_act_trg : ∀ (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules), ¬ trg.val.active cn.core) : (cb.branch.get? (n+1)).isNone := by
      apply Classical.byContradiction
      intro contra
      simp only [Option.isNone_iff_eq_none, ne_eq] at contra
      have ex_cn_succ : ∃ (cn_succ : CoreChaseNode kb.rules), cn_succ ∈ cb.branch.get? (n+1) := Option.ne_none_iff_exists'.mp contra
      rcases ex_cn_succ with ⟨cn_succ, cn_succ_eq⟩
      have trg_act := cb.triggers_active n cn cn_eq cn_succ cn_succ_eq
      rcases trg_act with ⟨trg, trg_act, h⟩
      exact Ne.elim (fun a => no_act_trg trg.fst h) cn_eq

end CoreChaseBranch
