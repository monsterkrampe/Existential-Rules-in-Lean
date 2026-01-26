import ExistentialRules.ChaseSequence.Termination.BacktrackingOfFacts
import ExistentialRules.ChaseSequence.Termination.ConstantMappings.InterplayWithObsoletenessCondition

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P]

namespace ChaseBranch

  variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

  theorem backtracking_of_term_in_node [GetFreshInhabitant sig.C] [Inhabited sig.C]
      {cb : ChaseBranch obs kb} {node : ChaseNode obs kb.rules} (node_mem : node ∈ cb.toChaseDerivation) :
      ∀ (rl : RuleList sig), (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) ->
      ∀ (term : GroundTerm sig), (term_mem : term ∈ node.facts.terms) ->
      ∀ (forbidden_constants : List sig.C),
        term.constants ⊆ forbidden_constants ->
        (rl.rules.flatMap Rule.constants) ⊆ forbidden_constants ->
      ∃ (g : ConstantMapping sig),
        g.apply_fact_set (term.backtrackFacts rl (cb.term_ruleIds_valid node_mem rl rl_rs_eq term term_mem) (cb.term_disjIdx_valid node_mem rl rl_rs_eq term term_mem) (cb.term_rule_arity_valid node_mem rl rl_rs_eq term term_mem) forbidden_constants).fst.toSet ⊆ node.facts ∧
        (∀ (d : sig.C), d ∈ forbidden_constants -> g d = .const d) := by
    intro rl rl_rs_eq
    let node : cb.Node := ⟨node, node_mem⟩
    show ∀ (term : GroundTerm sig), (term_mem : term ∈ node.val.facts.terms) ->
      ∀ (forbidden_constants : List sig.C),
        term.constants ⊆ forbidden_constants ->
        (rl.rules.flatMap Rule.constants) ⊆ forbidden_constants ->
      ∃ (g : ConstantMapping sig),
        g.apply_fact_set (term.backtrackFacts rl (cb.term_ruleIds_valid node.property rl rl_rs_eq term term_mem) (cb.term_disjIdx_valid node.property rl rl_rs_eq term term_mem) (cb.term_rule_arity_valid node.property rl rl_rs_eq term term_mem) forbidden_constants).fst.toSet ⊆ node.val.facts ∧
        (∀ (d : sig.C), d ∈ forbidden_constants -> g d = .const d)

    induction node using ChaseDerivation.mem_rec with
    | head =>
      intro term term_mem forbidden_constants forbidden_constants_subsumes_term forbidden_constants_subsumes_rules
      simp only [cb.database_first'] at term_mem
      rcases term_mem with ⟨f, f_mem, term_mem⟩
      rcases kb.db.toFactSet.property.right f f_mem term term_mem with ⟨_, t_eq⟩
      exists GroundTerm.const
      constructor
      . intro f' f'_mem
        rcases f'_mem with ⟨f'', f''_mem, f'_mem⟩
        rw [List.mem_toSet] at f''_mem
        simp only [t_eq, GroundTerm.backtrackFacts, PreGroundTerm.backtrackFacts, GroundTerm.const] at f''_mem
        simp at f''_mem
      . simp
    | step cd suffix ih next next_mem =>
      intro term term_mem forbidden_constants forbidden_constants_subsumes_term forbidden_constants_subsumes_rules
      let backtracking := term.backtrackFacts rl (cb.term_ruleIds_valid (cd.mem_of_mem_suffix suffix _ (cd.next_mem_of_mem _ next_mem)) rl rl_rs_eq term term_mem) (cb.term_disjIdx_valid (cd.mem_of_mem_suffix suffix _ (cd.next_mem_of_mem _ next_mem)) rl rl_rs_eq term term_mem) (cb.term_rule_arity_valid (cd.mem_of_mem_suffix suffix _ (cd.next_mem_of_mem _ next_mem)) rl rl_rs_eq term term_mem) forbidden_constants

      simp only [cd.facts_next next_mem, FactSet.terms_union] at term_mem
      cases term_mem with
      | inl term_mem =>
        rcases ih term term_mem forbidden_constants forbidden_constants_subsumes_term forbidden_constants_subsumes_rules with ⟨g, g_h⟩
        exists g
        constructor
        . simp only [cd.facts_next next_mem]
          apply Set.subset_union_of_subset_left
          exact g_h.left
        . exact g_h.right
      | inr term_mem =>
        simp only [FactSet.mem_terms_toSet, ChaseNode.origin_result, PreTrigger.mem_terms_mapped_head_iff] at term_mem
        cases term_mem with
        | inl term_mem =>
          rcases term_mem with ⟨c, c_mem, term_mem⟩
          exists GroundTerm.const
          constructor
          . intro f' f'_mem
            rcases f'_mem with ⟨f'', f''_mem, f'_mem⟩
            have : backtracking.fst = [] := by
              unfold backtracking
              simp only [← term_mem, GroundTerm.backtrackFacts, PreGroundTerm.backtrackFacts, GroundTerm.const]
            rw [this] at f''_mem
            simp [List.mem_toSet] at f''_mem
          . simp
        | inr term_mem =>
        cases term_mem with
        | inl term_mem =>
          -- TODO: pretty much same as IH application above... can we unify this?
          rcases ih term (by
            apply FactSet.terms_subset_of_subset (cd.active_trigger_origin_next next_mem).left
            rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_body_iff]; apply Or.inr
            rw [List.mem_map] at term_mem; rcases term_mem with ⟨v, v_mem, term_mem⟩
            exists v; simp only [term_mem, and_true]
            apply Rule.frontier_subset_vars_body
            rw [Rule.mem_frontier_iff_mem_frontier_for_head]
            exact ⟨_, v_mem⟩
          ) forbidden_constants forbidden_constants_subsumes_term forbidden_constants_subsumes_rules with ⟨g, g_h⟩
          exists g
          constructor
          . simp only [cd.facts_next next_mem]
            apply Set.subset_union_of_subset_left
            exact g_h.left
          . exact g_h.right
        | inr term_mem =>
          let origin := next.origin.get (cd.isSome_origin_next next_mem)
          have origin_active := cd.active_trigger_origin_next next_mem

          have origin_ruleIds_valid := (cb.trigger_ruleIds_valid_of_loaded (cd.mem_of_mem_suffix suffix _ cd.head_mem) rl rl_rs_eq origin.fst.val origin_active.left)
          have origin_disjIdx_valid := (cb.trigger_disjIdx_valid_of_loaded (cd.mem_of_mem_suffix suffix _ cd.head_mem) rl rl_rs_eq origin.fst.val origin_active.left)
          have origin_rule_arity_valid := (cb.trigger_rule_arity_valid_of_loaded (cd.mem_of_mem_suffix suffix _ cd.head_mem) rl rl_rs_eq origin.fst.val origin_active.left)

          rcases PreTrigger.mem_fresh_terms _ term_mem with ⟨v, v_mem, term_functional⟩
          have func_term_ruleIds_valid := origin.fst.val.skolem_ruleIds_valid_for_fresh_term rl (by rw [rl_rs_eq]; exact origin.fst.property) origin_ruleIds_valid _ _ _ term_mem
          simp only [GroundTerm.skolem_ruleIds_valid, term_functional, GroundTerm.func, PreGroundTerm.skolem_ruleIds_valid] at func_term_ruleIds_valid
          have func_term_disjIdx_valid := origin.fst.val.skolem_disjIdx_valid_for_fresh_term rl (by rw [rl_rs_eq]; exact origin.fst.property) origin_ruleIds_valid origin_disjIdx_valid _ _ _ term_mem
          simp only [GroundTerm.skolem_disjIdx_valid, term_functional, GroundTerm.func, PreGroundTerm.skolem_disjIdx_valid] at func_term_disjIdx_valid
          have func_term_rule_arity_valid := origin.fst.val.skolem_rule_arity_valid_for_fresh_term rl (by rw [rl_rs_eq]; exact origin.fst.property) origin_ruleIds_valid origin_rule_arity_valid _ _ _ term_mem
          simp only [GroundTerm.skolem_rule_arity_valid, term_functional, GroundTerm.func, PreGroundTerm.skolem_rule_arity_valid] at func_term_rule_arity_valid

          let mapped_frontier := origin.fst.val.rule.frontier.map origin.fst.val.subs

          have : ∀ sublist, (sub : sublist ⊆ mapped_frontier) -> ∀ forbidden_constants, (sublist.flatMap GroundTerm.constants ⊆ forbidden_constants) -> (rl.rules.flatMap Rule.constants ⊆ forbidden_constants) -> ∃ (g : ConstantMapping sig),
              (g.apply_fact_set (PreGroundTerm.backtrackFacts_list rl sublist.unattach
                (by simp only [List.mem_unattach]; rintro _ ⟨h, _⟩; exact h)
                (by simp only [List.mem_unattach]
                    rintro _ ⟨h, t_mem⟩
                    apply func_term_ruleIds_valid.right
                    rw [List.mem_unattach]
                    exists h
                    apply sub
                    exact t_mem)
                (by simp only [List.mem_unattach]
                    rintro _ ⟨h, t_mem⟩
                    apply func_term_disjIdx_valid.right
                    rw [List.mem_unattach]
                    exists h
                    apply sub
                    exact t_mem)
                (by simp only [List.mem_unattach]
                    rintro _ ⟨h, t_mem⟩
                    apply func_term_rule_arity_valid.right
                    rw [List.mem_unattach]
                    exists h
                    apply sub
                    exact t_mem)
                forbidden_constants).fst.toSet ⊆ next.facts) ∧
              (∀ (d : sig.C), d ∈ forbidden_constants → g d = .const d) := by
            intro sublist sub forbidden_constants forbidden_constants_subsumes_term forbidden_constants_subsumes_rules
            induction sublist generalizing forbidden_constants with
            | nil =>
              exists fun c => .const c
              constructor
              . intro _ e_mem
                simp only [List.unattach_nil, PreGroundTerm.backtrackFacts_list] at e_mem
                rcases e_mem with ⟨_, f_mem, _⟩
                simp [List.mem_toSet] at f_mem
              . intros; rfl
            | cons hd tl inner_ih =>
              rw [List.flatMap_cons, List.append_subset] at forbidden_constants_subsumes_term

              rcases ih hd (by
                rw [List.cons_subset] at sub
                unfold mapped_frontier at sub
                rw [List.mem_map] at sub
                rcases sub.left with ⟨v, v_mem, hd_eq⟩
                apply FactSet.terms_subset_of_subset origin_active.left
                rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_body_iff]
                apply Or.inr
                exists v; constructor
                . apply Rule.frontier_subset_vars_body; exact v_mem
                . exact hd_eq
              ) forbidden_constants forbidden_constants_subsumes_term.left forbidden_constants_subsumes_rules with ⟨g_hd, g_hd_h⟩
              let t_res := PreGroundTerm.backtrackFacts rl hd.val hd.property
                (by apply func_term_ruleIds_valid.right
                    rw [List.mem_unattach]
                    exists hd.property
                    exact (List.cons_subset.mp sub).left)
                (by apply func_term_disjIdx_valid.right
                    rw [List.mem_unattach]
                    exists hd.property
                    exact (List.cons_subset.mp sub).left)
                (by apply func_term_rule_arity_valid.right
                    rw [List.mem_unattach]
                    exists hd.property
                    exact (List.cons_subset.mp sub).left)
                forbidden_constants
              rcases inner_ih (by apply List.subset_of_cons_subset; exact sub) (forbidden_constants ++ t_res.snd) (by apply List.subset_append_of_subset_left; exact forbidden_constants_subsumes_term.right) (by apply List.subset_append_of_subset_left; exact forbidden_constants_subsumes_rules) with ⟨g_tl, g_tl_h⟩
              let g : ConstantMapping sig := fun c => if c ∈ t_res.snd then g_hd c else g_tl c
              exists g
              constructor
              . intro f f_mem
                rcases f_mem with ⟨f', f'_mem, f_eq⟩
                rw [List.mem_toSet] at f'_mem
                simp only [List.unattach_cons, PreGroundTerm.backtrackFacts_list] at f'_mem
                rw [List.mem_append] at f'_mem
                cases f'_mem with
                | inl f'_mem =>
                  have : g.apply_fact f' = g_hd.apply_fact f' := by
                    apply ConstantMapping.apply_fact_congr_left
                    intro d d_mem
                    unfold g
                    cases Decidable.em (d ∈ t_res.snd) with
                    | inl d_mem' => simp only [d_mem', ↓reduceIte]
                    | inr d_mem' =>
                      have : d ∈ forbidden_constants := by
                        have := PreGroundTerm.backtrackFacts_constants_in_rules_or_term_or_fresh f' f'_mem d d_mem
                        cases this with
                        | inl d_mem'' => apply forbidden_constants_subsumes_rules; exact d_mem''
                        | inr d_mem'' =>
                          cases d_mem'' with
                          | inr d_mem'' => apply False.elim; apply d_mem'; exact d_mem''
                          | inl d_mem'' =>
                            apply forbidden_constants_subsumes_term.left
                            exact d_mem''
                      simp only [d_mem', ↓reduceIte]
                      rw [g_hd_h.right]
                      rw [g_tl_h.right]
                      . rw [List.mem_append]; apply Or.inl; exact this
                      . exact this
                  rw [f_eq, ← ConstantMapping.apply_fact.eq_def, this]
                  rw [cd.facts_next next_mem]
                  apply Or.inl
                  apply g_hd_h.left
                  apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
                  rw [List.mem_toSet]
                  exact f'_mem
                | inr f'_mem =>
                  have : g.apply_fact f' = g_tl.apply_fact f' := by
                    apply ConstantMapping.apply_fact_congr_left
                    intro d d_mem
                    unfold g
                    cases Decidable.em (d ∈ t_res.snd) with
                    | inr d_mem' => simp only [d_mem', ↓reduceIte]
                    | inl d_mem' =>
                      apply False.elim
                      have d_not_forbidden : d ∉ forbidden_constants := PreGroundTerm.backtrackFacts_fresh_constants_not_forbidden d d_mem'
                      have := PreGroundTerm.backtrackFacts_list_constants_in_rules_or_term_or_fresh f' f'_mem d d_mem
                      cases this with
                      | inl d_mem'' => apply d_not_forbidden; apply forbidden_constants_subsumes_rules; exact d_mem''
                      | inr d_mem'' =>
                        cases d_mem'' with
                        | inl d_mem'' =>
                          apply d_not_forbidden
                          apply forbidden_constants_subsumes_term.right
                          rw [List.mem_flatMap] at d_mem''
                          rcases d_mem'' with ⟨t, t_mem, d_mem''⟩
                          rw [List.mem_unattach] at t_mem
                          rcases t_mem with ⟨h, t_mem⟩
                          rw [List.mem_flatMap]
                          exists ⟨t, h⟩
                        | inr d_mem'' =>
                          apply PreGroundTerm.backtrackFacts_list_fresh_constants_not_forbidden d d_mem''
                          rw [List.mem_append]
                          apply Or.inr
                          exact d_mem'

                  rw [f_eq, ← ConstantMapping.apply_fact.eq_def, this]
                  apply g_tl_h.left
                  apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
                  rw [List.mem_toSet]
                  exact f'_mem
              . intro d d_mem
                unfold g
                split
                . apply g_hd_h.right; exact d_mem
                . apply g_tl_h.right; rw [List.mem_append]; apply Or.inl; exact d_mem

          let rule := rl.get_by_id origin.fst.val.rule.id (by exists origin.fst.val.rule; constructor; rw [rl_rs_eq]; exact origin.fst.property; rfl)
          let pure_body_vars := rule.pure_body_vars
          let fresh_consts_for_pure_body_vars := rule.fresh_consts_for_pure_body_vars forbidden_constants
          let backtrack_trigger : PreTrigger sig := origin.fst.val.backtrackTrigger_for_functional_term rl (by rw [rl_rs_eq]; exact origin.fst.property) origin_ruleIds_valid origin_rule_arity_valid forbidden_constants origin.snd.val v

          have triggers_equiv : backtrack_trigger.equiv origin.fst.val := by apply origin.fst.val.backtrackTrigger_for_functional_term_equiv
          rcases this mapped_frontier (by simp) (forbidden_constants ++ fresh_consts_for_pure_body_vars)
            (by apply List.subset_append_of_subset_left
                intro d d_mem
                apply forbidden_constants_subsumes_term
                rw [term_functional, GroundTerm.constants_func]
                exact d_mem)
            (by apply List.subset_append_of_subset_left
                exact forbidden_constants_subsumes_rules)
            with ⟨g_mapped_frontier, g_mapped_frontier_h⟩

          let g : ConstantMapping sig := fun c =>
            if mem : c ∈ fresh_consts_for_pure_body_vars.val
            then
              let idx := fresh_consts_for_pure_body_vars.val.idxOf c
              have : idx < pure_body_vars.length := by
                rw [← fresh_consts_for_pure_body_vars.property.left]
                apply List.idxOf_lt_length_of_mem
                exact mem
              origin.fst.val.subs pure_body_vars[idx]
            else g_mapped_frontier c

          have triggers_strong_equiv : origin.fst.val.strong_equiv { rule := backtrack_trigger.rule, subs := g.apply_ground_term ∘ backtrack_trigger.subs } := by
            unfold PreTrigger.strong_equiv
            constructor
            . rw [triggers_equiv.left]
            . intro v v_mem
              cases Decidable.em (v ∈ backtrack_trigger.rule.frontier) with
              | inl v_mem' =>
                simp only [Function.comp_apply]
                rw [triggers_equiv.right v v_mem']
                apply Eq.symm
                apply ConstantMapping.apply_ground_term_eq_self_of_id_on_constants
                intro d d_mem
                have d_mem' : d ∈ forbidden_constants := by
                  apply forbidden_constants_subsumes_term
                  rw [term_functional, GroundTerm.constants_func]
                  rw [List.mem_flatMap]
                  exists origin.fst.val.subs v
                  constructor
                  . apply List.mem_map_of_mem; rw [← triggers_equiv.left]; exact v_mem'
                  . exact d_mem
                have : d ∉ fresh_consts_for_pure_body_vars.val := by intro contra; apply fresh_consts_for_pure_body_vars.property.right.right; exact contra; exact d_mem'
                simp only [g, this, ↓reduceDIte]
                rw [g_mapped_frontier_h.right]
                rw [List.mem_append]; apply Or.inl; exact d_mem'
              | inr v_mem' =>
                have v_mem'' : v ∈ pure_body_vars := by
                  simp only [pure_body_vars, Rule.pure_body_vars, List.mem_filter]
                  rw [← triggers_equiv.left] at v_mem
                  constructor
                  . exact v_mem
                  . apply decide_eq_true; exact v_mem'
                simp only [backtrack_trigger, PreTrigger.backtrackTrigger_for_functional_term, GroundTerm.backtrackTrigger, PreGroundTerm.backtrackTrigger, PreTrigger.functional_term_for_var, GroundTerm.func]
                simp only [backtrack_trigger, PreTrigger.backtrackTrigger_for_functional_term, GroundTerm.backtrackTrigger, PreGroundTerm.backtrackTrigger, PreTrigger.functional_term_for_var, GroundTerm.func] at v_mem'
                simp only [Function.comp_apply, v_mem', ↓reduceDIte]
                simp only [pure_body_vars, rule] at v_mem''
                simp only [v_mem'', ↓reduceDIte]
                simp only [ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, GroundTerm.const]
                unfold g
                have : fresh_consts_for_pure_body_vars.val[pure_body_vars.idxOf v]'(by unfold pure_body_vars; rw [fresh_consts_for_pure_body_vars.property.left]; apply List.idxOf_lt_length_of_mem; exact v_mem'') ∈ fresh_consts_for_pure_body_vars.val := by apply List.getElem_mem
                conv at this => right; simp only [fresh_consts_for_pure_body_vars, pure_body_vars, rule]
                simp only [this, ↓reduceDIte]
                rw [Subtype.mk.injEq]
                rw [Rule.fresh_consts_pure_body_vars_roundtrip]
                exact v_mem''

          have mapped_body_eq := PreTrigger.mapped_body_eq_of_strong_equiv triggers_strong_equiv
          have mapped_head_eq : origin.fst.val.mapped_head[origin.snd.val] = { rule := backtrack_trigger.rule, subs := g.apply_ground_term ∘ backtrack_trigger.subs : PreTrigger sig }.mapped_head[origin.snd.val]'(by rw [← PreTrigger.result_eq_of_equiv (PreTrigger.equiv_of_strong_equiv triggers_strong_equiv)]; exact origin.snd.isLt) := by simp only [PreTrigger.result_eq_of_equiv (PreTrigger.equiv_of_strong_equiv triggers_strong_equiv)]

          have g_id_on_rule_constants : ∀ c, c ∈ backtrack_trigger.rule.constants -> g c = .const c := by
            intro d d_mem
            have d_mem' : d ∈ forbidden_constants := by
              apply forbidden_constants_subsumes_rules
              rw [List.mem_flatMap]
              exists backtrack_trigger.rule
              constructor
              . rw [triggers_equiv.left, rl_rs_eq]; exact origin.fst.property
              . exact d_mem
            have d_not_mem : d ∉ fresh_consts_for_pure_body_vars.val := by
              intro contra
              apply fresh_consts_for_pure_body_vars.property.right.right
              . exact contra
              . exact d_mem'
            simp only [g, d_not_mem, ↓reduceDIte]
            apply g_mapped_frontier_h.right
            rw [List.mem_append]
            apply Or.inl
            exact d_mem'

          exists g
          constructor
          . intro e e_mem
            rcases e_mem with ⟨f, f_mem, e_eq⟩
            rw [List.mem_toSet] at f_mem
            simp only [term_functional, GroundTerm.func, GroundTerm.backtrackFacts, PreGroundTerm.backtrackFacts] at f_mem

            rw [List.mem_append] at f_mem
            cases f_mem with
            | inl f_mem =>
              simp only [cd.facts_next next_mem]

              rw [List.mem_append] at f_mem
              cases f_mem with
              | inl f_mem =>
                apply Or.inl
                rw [e_eq]
                apply origin_active.left
                rw [List.mem_toSet]

                rw [mapped_body_eq]
                simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]
                simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list] at f_mem
                rw [List.mem_map]
                rw [List.mem_map] at f_mem
                rcases f_mem with ⟨a, a_mem, f_eq⟩
                exists a
                constructor
                . exact a_mem
                . rw [← GroundSubstitution.apply_function_free_atom.eq_def, GroundSubstitution.apply_function_free_atom_compose, ← ConstantMapping.apply_fact_eq_groundTermMapping_applyFact, ← f_eq]
                  . rfl
                  . intro d d_mem
                    rw [ConstantMapping.apply_ground_term_constant]
                    apply g_id_on_rule_constants
                    unfold Rule.constants
                    rw [List.mem_append]
                    apply Or.inl
                    unfold FunctionFreeConjunction.consts
                    rw [List.mem_flatMap]
                    exists a
              | inr f_mem =>
                apply Or.inr
                rw [List.mem_toSet, e_eq]
                simp only [ChaseNode.origin_result]
                rw [mapped_head_eq]
                simp only [PreTrigger.mapped_head]
                simp only [PreTrigger.mapped_head] at f_mem
                rw [List.getElem_map, List.mem_map]
                rw [List.getElem_map, List.mem_map] at f_mem
                rcases f_mem with ⟨a, a_mem, f_eq⟩
                exists a
                constructor
                . exact a_mem
                . rw [← ConstantMapping.apply_fact_swap_apply_to_function_free_atom, ← f_eq]
                  . rfl
                  . intro d d_mem
                    apply g_id_on_rule_constants
                    unfold Rule.constants
                    rw [List.mem_append]
                    apply Or.inr
                    simp only [List.getElem_zipIdx] at a_mem
                    rw [List.mem_flatMap]
                    exists backtrack_trigger.rule.head[origin.snd.val]'(by rw [triggers_equiv.left, ← PreTrigger.length_mapped_head]; exact origin.snd.isLt)
                    constructor
                    . apply List.getElem_mem
                    . unfold FunctionFreeConjunction.consts
                      rw [List.mem_flatMap]
                      exists a
            | inr f_mem =>
              apply g_mapped_frontier_h.left
              rw [e_eq]
              have : g.apply_fact f = g_mapped_frontier.apply_fact f := by
                apply ConstantMapping.apply_fact_congr_left
                intro d d_mem
                cases Decidable.em (d ∈ fresh_consts_for_pure_body_vars.val) with
                | inr d_mem' => simp only [g, d_mem', ↓reduceDIte]
                | inl d_mem' =>
                  apply False.elim
                  have d_not_forbidden : d ∉ forbidden_constants := fresh_consts_for_pure_body_vars.property.right.right d d_mem'
                  have := PreGroundTerm.backtrackFacts_list_constants_in_rules_or_term_or_fresh f f_mem d d_mem
                  cases this with
                  | inl d_mem'' => apply d_not_forbidden; apply forbidden_constants_subsumes_rules; exact d_mem''
                  | inr d_mem'' =>
                    cases d_mem'' with
                    | inl d_mem'' =>
                      apply d_not_forbidden
                      apply forbidden_constants_subsumes_term
                      rw [term_functional, GroundTerm.constants_func]
                      rw [List.mem_flatMap] at d_mem''
                      rcases d_mem'' with ⟨t, t_mem, d_mem''⟩
                      rw [List.mem_unattach] at t_mem
                      rcases t_mem with ⟨h, t_mem⟩
                      rw [List.mem_flatMap]
                      exists ⟨t, h⟩
                    | inr d_mem'' =>
                      apply PreGroundTerm.backtrackFacts_list_fresh_constants_not_forbidden d d_mem''
                      rw [List.mem_append]
                      apply Or.inr
                      exact d_mem'
              rw [← ConstantMapping.apply_fact.eq_def, this]
              apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
              rw [List.mem_toSet]
              exact f_mem
          . intro d d_mem
            have d_nmem : d ∉ fresh_consts_for_pure_body_vars.val := by
              intro contra
              apply fresh_consts_for_pure_body_vars.property.right.right
              . exact contra
              . exact d_mem
            simp only [g, d_nmem, ↓reduceDIte]
            apply g_mapped_frontier_h.right
            rw [List.mem_append]
            apply Or.inl
            exact d_mem

  theorem backtracking_of_term_list_in_node [GetFreshInhabitant sig.C] [Inhabited sig.C]
      {cb : ChaseBranch obs kb} {node : ChaseNode obs kb.rules} (node_mem : node ∈ cb.toChaseDerivation) :
      ∀ (rl : RuleList sig), (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) ->
      ∀ (terms : List (GroundTerm sig)), (terms_mem : terms.toSet ⊆ node.facts.terms) ->
      ∀ (forbidden_constants : List sig.C),
        (terms.flatMap GroundTerm.constants) ⊆ forbidden_constants ->
        (rl.rules.flatMap Rule.constants) ⊆ forbidden_constants ->
      ∃ (g : ConstantMapping sig),
        g.apply_fact_set (GroundTerm.backtrackFacts_list rl terms (by intro t t_mem; apply cb.term_ruleIds_valid node_mem rl rl_rs_eq t; apply terms_mem; rw [List.mem_toSet]; exact t_mem) (by intro t t_mem; apply cb.term_disjIdx_valid node_mem rl rl_rs_eq t; apply terms_mem; rw [List.mem_toSet]; exact t_mem) (by intro t t_mem; apply cb.term_rule_arity_valid node_mem rl rl_rs_eq t; apply terms_mem; rw [List.mem_toSet]; exact t_mem) forbidden_constants).fst.toSet ⊆ node.facts ∧
        (∀ (d : sig.C), d ∈ forbidden_constants -> g d = .const d) := by
    intro rl rl_rs_eq terms terms_mem forbidden_constants forbidden_constants_subsumes_terms forbidden_constants_subsumes_rules
    induction terms generalizing forbidden_constants with
    | nil =>
      exists ConstantMapping.id
      constructor
      . simp only [GroundTerm.backtrackFacts_list]
        intro _ e_mem
        rcases e_mem with ⟨_, f_mem, _⟩
        rw [List.mem_toSet] at f_mem
        simp at f_mem
      . intros; rfl
    | cons hd tl ih =>
      rw [List.flatMap_cons, List.append_subset] at forbidden_constants_subsumes_terms

      have hd_mem : hd ∈ node.facts.terms := by apply terms_mem; simp [List.mem_toSet]

      rcases cb.backtracking_of_term_in_node node_mem rl rl_rs_eq hd hd_mem forbidden_constants forbidden_constants_subsumes_terms.left forbidden_constants_subsumes_rules with ⟨g_hd, g_hd_h⟩

      let result_for_hd := GroundTerm.backtrackFacts rl hd (cb.term_ruleIds_valid node_mem rl rl_rs_eq hd hd_mem) (cb.term_disjIdx_valid node_mem rl rl_rs_eq hd hd_mem) (cb.term_rule_arity_valid node_mem rl rl_rs_eq hd hd_mem) forbidden_constants

      rcases ih (by intro t t_mem; rw [List.mem_toSet] at t_mem; apply terms_mem; simp [List.mem_toSet, t_mem]) (forbidden_constants ++ result_for_hd.snd) (by apply List.subset_append_of_subset_left; exact forbidden_constants_subsumes_terms.right) (by apply List.subset_append_of_subset_left; exact forbidden_constants_subsumes_rules) with ⟨g_tl, g_tl_h⟩

      let g : ConstantMapping sig := fun c => if c ∈ result_for_hd.snd then g_hd c else g_tl c
      exists g
      constructor
      . intro f f_mem
        rcases f_mem with ⟨f', f'_mem, f_eq⟩
        rw [List.mem_toSet] at f'_mem
        simp only [GroundTerm.backtrackFacts_list] at f'_mem
        rw [List.mem_append] at f'_mem
        cases f'_mem with
        | inl f'_mem =>
          have : g.apply_fact f' = g_hd.apply_fact f' := by
            apply ConstantMapping.apply_fact_congr_left
            intro d d_mem
            unfold g
            cases Decidable.em (d ∈ result_for_hd.snd) with
            | inl d_mem' => simp only [d_mem', ↓reduceIte]
            | inr d_mem' =>
              have : d ∈ forbidden_constants := by
                have := PreGroundTerm.backtrackFacts_constants_in_rules_or_term_or_fresh f' f'_mem d d_mem
                cases this with
                | inl d_mem'' => apply forbidden_constants_subsumes_rules; exact d_mem''
                | inr d_mem'' =>
                  cases d_mem'' with
                  | inr d_mem'' => apply False.elim; apply d_mem'; exact d_mem''
                  | inl d_mem'' =>
                    apply forbidden_constants_subsumes_terms.left
                    exact d_mem''
              simp only [d_mem', ↓reduceIte]
              rw [g_hd_h.right]
              rw [g_tl_h.right]
              . rw [List.mem_append]; apply Or.inl; exact this
              . exact this
          rw [f_eq, ← ConstantMapping.apply_fact.eq_def, this]
          apply g_hd_h.left
          apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
          rw [List.mem_toSet]
          exact f'_mem
        | inr f'_mem =>
          have : g.apply_fact f' = g_tl.apply_fact f' := by
            apply ConstantMapping.apply_fact_congr_left
            intro d d_mem
            unfold g
            cases Decidable.em (d ∈ result_for_hd.snd) with
            | inr d_mem' => simp only [d_mem', ↓reduceIte]
            | inl d_mem' =>
              apply False.elim
              have d_not_forbidden : d ∉ forbidden_constants := GroundTerm.backtrackFacts_fresh_constants_not_forbidden d d_mem'
              have := GroundTerm.backtrackFacts_list_constants_in_rules_or_term_or_fresh f' f'_mem d d_mem
              cases this with
              | inl d_mem'' => apply d_not_forbidden; apply forbidden_constants_subsumes_rules; exact d_mem''
              | inr d_mem'' =>
                cases d_mem'' with
                | inl d_mem'' =>
                  apply d_not_forbidden
                  apply forbidden_constants_subsumes_terms.right
                  exact d_mem''
                | inr d_mem'' =>
                  apply GroundTerm.backtrackFacts_list_fresh_constants_not_forbidden d d_mem''
                  rw [List.mem_append]
                  apply Or.inr
                  exact d_mem'

          rw [f_eq, ← ConstantMapping.apply_fact.eq_def, this]
          apply g_tl_h.left
          apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
          rw [List.mem_toSet]
          exact f'_mem
      . intro d d_mem
        unfold g
        split
        . apply g_hd_h.right; exact d_mem
        . apply g_tl_h.right; rw [List.mem_append]; apply Or.inl; exact d_mem

  theorem backtracking_of_loaded_trigger_in_node [GetFreshInhabitant sig.C] [Inhabited sig.C]
      {cb : ChaseBranch obs kb} {node : ChaseNode obs kb.rules} (node_mem : node ∈ cb.toChaseDerivation) :
      ∀ (rl : RuleList sig), (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) ->
      ∀ (trg : PreTrigger sig), (trg_loaded : trg.loaded node.facts) ->
      ∃ (g : ConstantMapping sig),
        g.apply_fact_set (trg.backtrackFacts rl (cb.trigger_ruleIds_valid_of_loaded node_mem rl rl_rs_eq trg trg_loaded) (cb.trigger_disjIdx_valid_of_loaded node_mem rl rl_rs_eq trg trg_loaded) (cb.trigger_rule_arity_valid_of_loaded node_mem rl rl_rs_eq trg trg_loaded)).fst.toSet ⊆ node.facts ∧
        (∀ (d : sig.C), d ∈ ((trg.mapped_body.flatMap Fact.constants).toSet ∪ kb.rules.constants) -> g d = .const d) := by
    intro rl rl_rs_eq trg trg_loaded
    have := cb.backtracking_of_term_list_in_node node_mem rl rl_rs_eq (trg.mapped_body.flatMap GeneralizedAtom.terms)
      (by intro t t_mem
          rw [List.mem_toSet, List.mem_flatMap] at t_mem
          rcases t_mem with ⟨f, f_mem, t_mem⟩
          exists f
          constructor
          . apply trg_loaded; rw [List.mem_toSet]; exact f_mem
          . exact t_mem)
      (trg.mapped_body.flatMap Fact.constants ++ rl.rules.flatMap Rule.constants)
      (by apply List.subset_append_of_subset_left
          unfold Fact.constants
          intro d d_mem
          rw [List.mem_flatMap] at d_mem
          rcases d_mem with ⟨t, t_mem, d_mem⟩
          rw [List.mem_flatMap] at t_mem
          rcases t_mem with ⟨f, f_mem, t_mem⟩
          rw [List.mem_flatMap]
          exists f
          constructor
          . exact f_mem
          . rw [List.mem_flatMap]
            exists t)
      (by apply List.subset_append_of_subset_right
          apply List.Subset.refl)

    rcases this with ⟨g, g_h⟩
    exists g
    constructor
    . intro f f_mem
      rcases f_mem with ⟨f', f'_mem, f_eq⟩
      rw [List.mem_toSet] at f'_mem
      unfold PreTrigger.backtrackFacts at f'_mem
      rw [List.mem_append] at f'_mem
      cases f'_mem with
      | inl f'_mem =>
        have : g.apply_fact f' = f' := by
          apply ConstantMapping.apply_fact_eq_self_of_id_on_constants
          intro d d_mem
          apply g_h.right
          rw [List.mem_append]
          apply Or.inl
          rw [List.mem_flatMap]
          exists f'
        rw [f_eq, ← ConstantMapping.apply_fact.eq_def, this]
        apply trg_loaded
        rw [List.mem_toSet]
        exact f'_mem
      | inr f'_mem =>
        apply g_h.left
        exists f'
    . intro d d_mem
      apply g_h.right
      rw [List.mem_append]
      cases d_mem with
      | inl d_mem => apply Or.inl; rw [List.mem_toSet] at d_mem; exact d_mem
      | inr d_mem =>
        apply Or.inr
        rcases d_mem with ⟨r, r_mem, d_mem⟩
        rw [List.mem_flatMap]
        exists r
        rw [rl_rs_eq]
        constructor
        . exact r_mem
        . exact d_mem

end ChaseBranch

