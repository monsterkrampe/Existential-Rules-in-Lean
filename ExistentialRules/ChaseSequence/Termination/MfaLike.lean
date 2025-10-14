import BasicLeanDatastructures.List.Repeat

import ExistentialRules.ChaseSequence.Termination.Basic
import ExistentialRules.ChaseSequence.Termination.BacktrackingOfFacts
import ExistentialRules.ChaseSequence.Termination.ConstantMappings.Basic
import ExistentialRules.ChaseSequence.Termination.ConstantMappings.InterplayWithBacktracking
import ExistentialRules.ChaseSequence.Termination.RenameConstantsApart
import ExistentialRules.Terms.Cyclic

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

-- TODO: check if can avoid the noncomputable definition; this could work by passing a mapping with the necessary property around and eventually show that such a mapping exists for finite rule sets; not sure if this is better than this though
-- NOTE: this is only used to state some theorems, hence its ok for it to be uncomputable
noncomputable def RuleSet.mfaConstantMapping (rs : RuleSet sig) (special_const : sig.C) : StrictConstantMapping sig :=
  fun c =>
    have : Decidable (c ∈ rs.constants) := Classical.propDecidable (c ∈ rs.constants)
    if (c ∈ rs.constants) then c else special_const

theorem RuleSet.mfaConstantMapping_id_on_rs_constants (rs : RuleSet sig) (special_const : sig.C) : ∀ (c : sig.C), c ∈ rs.constants -> rs.mfaConstantMapping special_const c = c := by
  intro c c_mem
  simp [mfaConstantMapping, c_mem]

theorem RuleSet.mfaConstantMapping_id_on_atom_from_rule (rs : RuleSet sig) (special_const : sig.C) (r : Rule sig) (r_mem : r ∈ rs.rules) : ∀ a, a ∈ r.body ++ r.head.flatten -> (rs.mfaConstantMapping special_const).apply_function_free_atom a = a := by
  intro a a_mem
  unfold StrictConstantMapping.apply_function_free_atom
  rw [GeneralizedAtom.mk.injEq]
  constructor
  . rfl
  . apply List.map_id_of_id_on_all_mem
    intro voc voc_mem
    cases voc with
    | var v => simp [StrictConstantMapping.apply_var_or_const]
    | const s =>
      simp only [StrictConstantMapping.apply_var_or_const]
      rw [VarOrConst.const.injEq]
      apply mfaConstantMapping_id_on_rs_constants
      exists r
      constructor
      . exact r_mem
      . rw [List.mem_append] at a_mem
        unfold Rule.constants
        rw [List.mem_append]
        cases a_mem with
        | inl a_mem =>
          apply Or.inl
          unfold FunctionFreeConjunction.consts
          rw [List.mem_flatMap]
          exists a
          constructor
          . exact a_mem
          . apply VarOrConst.mem_filterConsts_of_const; exact voc_mem
        | inr a_mem =>
          rw [List.mem_flatten] at a_mem
          rcases a_mem with ⟨head, head_mem, a_mem⟩
          apply Or.inr
          rw [List.mem_flatMap]
          exists head
          constructor
          . exact head_mem
          . unfold FunctionFreeConjunction.consts
            rw [List.mem_flatMap]
            exists a
            constructor
            . exact a_mem
            . apply VarOrConst.mem_filterConsts_of_const; exact voc_mem

structure MfaObsoletenessCondition (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] extends LaxObsoletenessCondition sig

instance {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] : Coe (MfaObsoletenessCondition sig) (LaxObsoletenessCondition sig) where
  coe obs := { cond := obs.cond, monotone := obs.monotone }

def MfaObsoletenessCondition.blocks_obs (mfa_obs : MfaObsoletenessCondition sig) (obs : ObsoletenessCondition sig) (rs : RuleSet sig) (special_const : sig.C) : Prop :=
  ∀ {db : Database sig} (cb : ChaseBranch obs ⟨db, rs⟩) (step : Nat) (trg : RTrigger obs rs) (fs : FactSet sig),
  (∃ (i : Fin trg.val.mapped_head.length), ¬ ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact_set trg.val.mapped_head[i.val].toSet) ⊆ fs) ->
  (mfa_obs.cond { rule := trg.val.rule, subs := (rs.mfaConstantMapping special_const).toConstantMapping.apply_ground_term ∘ trg.val.subs } fs) ->
  (cb.branch.infinite_list step).is_none_or (fun node =>
    trg.val.loaded node.facts ->
    obs.cond trg.val node.facts
  )

def DeterministicSkolemObsoleteness (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] : MfaObsoletenessCondition sig := {
  cond := fun (trg : PreTrigger sig) (F : FactSet sig) => trg.mapped_head.length > 0 ∧ ∀ i : Fin trg.mapped_head.length, trg.mapped_head[i.val].toSet ⊆ F
  monotone := by
    intro trg A B A_sub_B
    simp only [and_imp]
    intro length_gt head_sub_A
    constructor
    . exact length_gt
    . intro i
      apply Set.subset_trans
      . apply head_sub_A
      . apply A_sub_B
}

theorem DeterministicSkolemObsoleteness.blocks_each_obs (obs : ObsoletenessCondition sig) (special_const : sig.C) : ∀ rs, (DeterministicSkolemObsoleteness sig).blocks_obs obs rs special_const := by
  intro rs _ _ _ trg fs f_not_in_prev cond
  rcases f_not_in_prev with ⟨disj_index, f_not_in_prev⟩
  apply False.elim
  apply f_not_in_prev

  intro f' f'_mem
  rcases f'_mem with ⟨f, f_mem, f'_mem⟩

  unfold DeterministicSkolemObsoleteness at cond
  apply cond.right ⟨disj_index.val, by
    have isLt := disj_index.isLt
    unfold PreTrigger.mapped_head
    simp only [List.length_map, List.length_zipIdx]
    simp only [PreTrigger.length_mapped_head] at isLt
    exact isLt
  ⟩

  rw [List.mem_toSet]
  unfold PreTrigger.mapped_head
  simp
  unfold PreTrigger.mapped_head at f_mem
  rw [List.mem_toSet, List.getElem_map, List.mem_map] at f_mem
  rcases f_mem with ⟨a, a_mem, f_eq⟩
  rw [List.get_eq_getElem, List.getElem_zipIdx] at a_mem
  rw [List.get_eq_getElem, List.getElem_zipIdx] at f_eq
  exists (rs.mfaConstantMapping special_const).apply_function_free_atom a
  constructor
  . rw [rs.mfaConstantMapping_id_on_atom_from_rule _ trg.val.rule trg.property]
    . exact a_mem
    . rw [List.mem_append]
      apply Or.inr
      apply List.mem_flatten_of_mem _ a_mem
      apply List.getElem_mem
  . rw [f'_mem, ← f_eq]
    simp only [Nat.zero_add]
    rw [← Function.comp_apply (f := { rule := trg.val.rule, subs := (rs.mfaConstantMapping special_const).toConstantMapping.apply_ground_term ∘ trg.val.subs : PreTrigger sig }.apply_to_function_free_atom disj_index.val)]
    rw [← TermMapping.apply_generalized_atom_compose]
    rw [← Function.comp_apply (f := (rs.mfaConstantMapping special_const).toConstantMapping.apply_ground_term.apply_generalized_atom)]
    rw [← TermMapping.apply_generalized_atom_compose]
    apply TermMapping.apply_generalized_atom_congr_left
    intro voc voc_mem
    cases voc with
    | var v =>
      simp only [Function.comp_apply, StrictConstantMapping.apply_var_or_const, PreTrigger.apply_to_var_or_const]
      rw [← ConstantMapping.apply_ground_term_swap_apply_skolem_term]
      . rfl
      . intros
        simp only [PreTrigger.skolemize_var_or_const, VarOrConst.skolemize]
        split <;> simp
    | const c => rfl

def Trigger.blocked_for_backtracking
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    {obs : LaxObsoletenessCondition sig}
    (trg : Trigger obs)
    (rl : RuleList sig) : Prop :=
  (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl)
  -> (trg_disjIdx_valid : trg.skolem_disjIdx_valid rl trg_ruleIds_valid)
  -> (trg_rule_arity_valid : trg.skolem_rule_arity_valid rl trg_ruleIds_valid)
  -> (obs.cond trg (trg.backtrackFacts rl trg_ruleIds_valid trg_disjIdx_valid trg_rule_arity_valid).fst.toSet)

def BlockingObsoleteness [GetFreshInhabitant sig.C] [Inhabited sig.C] (obs : ObsoletenessCondition sig) (rs : RuleSet sig) : MfaObsoletenessCondition sig := {
  cond := fun (trg : PreTrigger sig) _ =>
    ∀ (rl : RuleList sig), (∀ r, r ∈ rl.rules ↔ r ∈ rs.rules) ->
      let trg' := trg.rename_constants_apart (rl.rules.flatMap Rule.constants)
      let trg'' : Trigger obs := { rule := trg'.rule, subs := trg'.subs }
      trg''.blocked_for_backtracking rl
  monotone := by
    -- trivial since the condition does not depend on the passed fact set
    intro trg A B A_sub_B
    intro h
    exact h
}

theorem BlockingObsoleteness.blocks_corresponding_obs [GetFreshInhabitant sig.C] [Inhabited sig.C]
    (obs : ObsoletenessCondition sig) (obs_propagates_under_const_mapping : obs.propagates_under_constant_mapping)
    (rs : RuleSet sig) (rs_finite : rs.rules.finite) (special_const : sig.C) :
    (BlockingObsoleteness obs rs).blocks_obs obs rs special_const := by
  intro db cb step trg _ _ blocked
  rw [Option.is_none_or_iff]
  intro node eq_node loaded
  simp only [BlockingObsoleteness] at blocked

  rcases rs_finite with ⟨rl, rl_nodup, rl_rs_eq⟩
  let rl : RuleList sig := ⟨rl, by intro r1 r2 h; apply rs.id_unique; rw [← rl_rs_eq]; rw [← rl_rs_eq]; exact h⟩

  have blocked : trg.val.blocked_for_backtracking rl := by
    -- should follow from original blocked and should be its own result
    -- it also relates to one theorem/lemma from the DMFA paper if I remember correctly
    -- not sure what to do about the rule adjustment though, maybe it just works?
    intro trg_ruleIds_valid trg_disjIdx_valid trg_rule_arity_valid

    let trg_with_constant_mapping_applied_but_not_renamed_apart : PreTrigger sig := { rule := trg.val.rule, subs := (rs.mfaConstantMapping special_const).toConstantMapping.apply_ground_term ∘ trg.val.subs }

    specialize blocked rl rl_rs_eq
    specialize blocked (by
      apply PreTrigger.rename_constants_apart_preserves_ruleId_validity
      apply PreTrigger.compose_strict_constant_mapping_preserves_ruleId_validity
      exact trg_ruleIds_valid
    )
    specialize blocked (by
      apply PreTrigger.rename_constants_apart_preserves_disjIdx_validity
      apply PreTrigger.compose_strict_constant_mapping_preserves_disjIdx_validity
      exact trg_disjIdx_valid
    )
    specialize blocked (by
      apply PreTrigger.rename_constants_apart_preserves_rule_arity_validity
      apply PreTrigger.compose_strict_constant_mapping_preserves_rule_arity_validity
      exact trg_rule_arity_valid
    )
    simp only at blocked

    have exists_strict_constant_mapping_reversing_renaming :=
      trg_with_constant_mapping_applied_but_not_renamed_apart.exists_strict_constant_mapping_to_reverse_renaming
        trg.val.toPreTrigger
        (by apply PreTrigger.same_skeleton_symm; apply PreTrigger.same_skeleton_under_strict_constant_mapping)
        (rl.rules.flatMap Rule.constants)
    rcases exists_strict_constant_mapping_reversing_renaming with ⟨reverse_renaming_mapping, reverse_renaming_mapping_properties⟩

    rw [← obs.preserved_under_equiv (PreTrigger.equiv_of_strong_equiv _ _ reverse_renaming_mapping_properties.left)]
    rw [← PreTrigger.backtrackFacts_eq_of_strong_equiv _ _ _ _ _ _ reverse_renaming_mapping_properties.left]

    have exists_fresh_constant_remapping_such_that_backtrackings_subsume_each_other := PreTrigger.backtracking_under_constant_mapping_subset_of_composing_with_subs
      rl
      (trg_with_constant_mapping_applied_but_not_renamed_apart.rename_constants_apart (rl.rules.flatMap Rule.constants))
      (by
        apply PreTrigger.rename_constants_apart_preserves_ruleId_validity
        apply PreTrigger.compose_strict_constant_mapping_preserves_ruleId_validity
        exact trg_ruleIds_valid
      )
      (by
        apply PreTrigger.rename_constants_apart_preserves_disjIdx_validity
        apply PreTrigger.compose_strict_constant_mapping_preserves_disjIdx_validity
        exact trg_disjIdx_valid
      )
      (by
        apply PreTrigger.rename_constants_apart_preserves_rule_arity_validity
        apply PreTrigger.compose_strict_constant_mapping_preserves_rule_arity_validity
        exact trg_rule_arity_valid
      )
      (by rw [rl_rs_eq]; exact trg.property)
      reverse_renaming_mapping
      (by
        intro d d_mem
        apply reverse_renaming_mapping_properties.right
        intro contra
        apply trg_with_constant_mapping_applied_but_not_renamed_apart.rename_constants_apart_constants_fresh (rl.rules.flatMap Rule.constants) d contra
        exact d_mem
      )

    rcases exists_fresh_constant_remapping_such_that_backtrackings_subsume_each_other with ⟨fresh_constant_remapping, fresh_constant_remapping_id, fresh_constant_remapping_subsumes⟩

    apply obs.monotone _ _ _ fresh_constant_remapping_subsumes

    have equiv : { rule := trg_with_constant_mapping_applied_but_not_renamed_apart.rule, subs := reverse_renaming_mapping.toConstantMapping.apply_ground_term ∘ (trg_with_constant_mapping_applied_but_not_renamed_apart.rename_constants_apart (rl.rules.flatMap Rule.constants)).subs : PreTrigger sig }.equiv { rule := trg_with_constant_mapping_applied_but_not_renamed_apart.rule, subs := (StrictConstantMapping.toConstantMapping (fun c => if c ∈ (PreTrigger.backtrackFacts rl (trg_with_constant_mapping_applied_but_not_renamed_apart.rename_constants_apart (rl.rules.flatMap Rule.constants)) (by apply PreTrigger.rename_constants_apart_preserves_ruleId_validity; apply PreTrigger.compose_strict_constant_mapping_preserves_ruleId_validity; exact trg_ruleIds_valid) (by apply PreTrigger.rename_constants_apart_preserves_disjIdx_validity; apply PreTrigger.compose_strict_constant_mapping_preserves_disjIdx_validity; exact trg_disjIdx_valid) (by apply PreTrigger.rename_constants_apart_preserves_rule_arity_validity; apply PreTrigger.compose_strict_constant_mapping_preserves_rule_arity_validity; exact trg_rule_arity_valid)).snd then fresh_constant_remapping c else reverse_renaming_mapping c)).apply_ground_term ∘ (trg_with_constant_mapping_applied_but_not_renamed_apart.rename_constants_apart (rl.rules.flatMap Rule.constants)).subs : PreTrigger sig } := by
      simp only [PreTrigger.equiv, true_and]
      intro v v_mem
      simp only [Function.comp_apply]
      apply ConstantMapping.apply_ground_term_congr_left
      intro d d_mem
      simp only [StrictConstantMapping.toConstantMapping, PreTrigger.backtrackFacts]
      split
      case a.isFalse heq => rfl
      case a.isTrue heq =>
        apply False.elim
        apply GroundTerm.backtrackFacts_list_fresh_constants_not_forbidden d heq
        rw [List.mem_append]
        apply Or.inl
        rcases Rule.frontier_occurs_in_body _ _ v_mem with ⟨a, a_mem, v_mem⟩
        rw [List.mem_flatMap]
        exists (trg_with_constant_mapping_applied_but_not_renamed_apart.rename_constants_apart (rl.rules.flatMap Rule.constants)).subs.apply_function_free_atom a
        constructor
        . simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]
          rw [List.mem_map]
          exists a
        . unfold Fact.constants
          rw [List.mem_flatMap]
          exists (trg_with_constant_mapping_applied_but_not_renamed_apart.rename_constants_apart (rl.rules.flatMap Rule.constants)).subs.apply_var_or_const (.var v)
          simp only [GroundSubstitution.apply_function_free_atom, TermMapping.apply_generalized_atom, GroundSubstitution.apply_var_or_const]
          constructor
          . rw [List.mem_map]
            exists .var v
          . exact d_mem

    rw [obs.preserved_under_equiv equiv]

    apply obs_propagates_under_const_mapping (trg := trg_with_constant_mapping_applied_but_not_renamed_apart.rename_constants_apart (rl.rules.flatMap Rule.constants))
    . intro c c_mem
      simp only [StrictConstantMapping.toConstantMapping, GroundTerm.const, Subtype.mk.injEq, FiniteTree.leaf.injEq]
      rw [fresh_constant_remapping_id]
      . split
        case isTrue heq => rfl
        case isFalse heq =>
          apply reverse_renaming_mapping_properties.right
          intro contra
          apply trg_with_constant_mapping_applied_but_not_renamed_apart.rename_constants_apart_constants_fresh (rl.rules.flatMap Rule.constants) c
          . exact contra
          . rw [List.mem_flatMap]
            exists (trg_with_constant_mapping_applied_but_not_renamed_apart.rename_constants_apart (rl.rules.flatMap Rule.constants)).rule
            constructor
            . rw [rl_rs_eq]
              exact trg.property
            . apply Rule.head_constants_subset_constants
              exact c_mem
      . intro contra
        simp only [PreTrigger.backtrackFacts] at contra
        apply GroundTerm.backtrackFacts_list_fresh_constants_not_forbidden c contra
        rw [List.mem_append]
        apply Or.inr
        rw [List.mem_flatMap]
        exists trg.val.rule
        constructor
        . rw [rl_rs_eq]; exact trg.property
        . apply Rule.head_constants_subset_constants
          exact c_mem
    . exact blocked

  simp only [Trigger.blocked_for_backtracking] at blocked

  specialize blocked (by apply cb.trigger_ruleIds_valid_of_loaded step node eq_node rl rl_rs_eq; exact loaded)
  specialize blocked (by apply cb.trigger_disjIdx_valid_of_loaded step node eq_node rl rl_rs_eq; exact loaded)
  specialize blocked (by apply cb.trigger_rule_arity_valid_of_loaded step node eq_node rl rl_rs_eq; exact loaded)


  rcases cb.backtracking_of_loaded_trigger_in_node step node eq_node rl rl_rs_eq trg.val loaded with ⟨g, g_h⟩

  have blocked := obs_propagates_under_const_mapping
    (g := g)
    (by
      intro c c_mem
      apply g_h.right
      apply Or.inr
      apply RuleSet.head_constants_subset_constants
      exists trg.val.rule
      constructor
      . exact trg.property
      . exact c_mem
    )
    blocked

  have equiv : trg.val.equiv {rule := trg.val.rule, subs := g.apply_ground_term ∘ trg.val.subs} := by
    unfold PreTrigger.equiv
    constructor
    . rfl
    . intro v v_mem
      simp only [Function.comp_apply]

      conv => left; rw [← ConstantMapping.apply_ground_term_id (trg.val.subs v)]
      apply ConstantMapping.apply_ground_term_congr_left
      intro d d_mem
      simp only [ConstantMapping.id]
      rw [g_h.right]
      apply Or.inl
      rcases trg.val.rule.frontier_occurs_in_body v v_mem with ⟨a, a_mem, v_mem'⟩
      rw [List.mem_toSet, List.mem_flatMap]
      exists trg.val.subs.apply_function_free_atom a
      constructor
      . simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj]
        apply List.mem_map_of_mem
        exact a_mem
      . unfold Fact.constants
        rw [List.mem_flatMap]
        exists trg.val.subs v
        constructor
        . simp only [GroundSubstitution.apply_function_free_atom, TermMapping.apply_generalized_atom]
          rw [List.mem_map]
          exists .var v
        . exact d_mem

  rw [obs.preserved_under_equiv equiv]

  apply obs.monotone _ _ _ _ blocked
  exact g_h.left


namespace KnowledgeBase

  def parallelSkolemChase (kb : KnowledgeBase sig) (obs : LaxObsoletenessCondition sig) : InfiniteList (FactSet sig)
  | .zero => kb.db.toFactSet
  | .succ n =>
    let prev_step := parallelSkolemChase kb obs n
    fun f =>
      f ∈ prev_step ∨
      (∃ (trg : RTrigger obs kb.rules),
        trg.val.active prev_step ∧
        ∃ (i : Fin trg.val.mapped_head.length), f ∈ trg.val.mapped_head[i.val])

  theorem parallelSkolemChase_subset_all_following (kb : KnowledgeBase sig) (obs : LaxObsoletenessCondition sig) (n m : Nat) : kb.parallelSkolemChase obs n ⊆ kb.parallelSkolemChase obs (n+m) := by
    induction m with
    | zero => apply Set.subset_refl
    | succ m ih =>
      rw [← Nat.add_assoc]
      conv => right; unfold parallelSkolemChase
      intro f f_mem
      apply Or.inl
      apply ih
      exact f_mem

  theorem parallelSkolemChase_predicates (kb : KnowledgeBase sig) (obs : LaxObsoletenessCondition sig) :
      ∀ n, (kb.parallelSkolemChase obs n).predicates ⊆ (kb.rules.predicates ∪ kb.db.toFactSet.val.predicates) := by
    intro n
    induction n with
    | zero =>
      unfold parallelSkolemChase
      apply Set.subset_union_of_subset_right
      apply Set.subset_refl
    | succ n ih =>
      unfold parallelSkolemChase
      intro p p_mem
      rcases p_mem with ⟨f, f_mem, p_mem⟩
      cases f_mem with
      | inl f_mem => apply ih; exists f
      | inr f_mem =>
        rcases f_mem with ⟨trg, trg_act, f_mem⟩
        unfold PreTrigger.mapped_head at f_mem
        rcases f_mem with ⟨i, f_mem⟩
        rw [List.getElem_map, List.mem_map] at f_mem
        rcases f_mem with ⟨a, a_mem, f_mem⟩
        rw [List.get_eq_getElem, List.getElem_zipIdx] at a_mem
        apply Or.inl
        exists trg.val.rule
        constructor
        . exact trg.property
        . unfold Rule.predicates
          rw [List.mem_append]
          apply Or.inr
          rw [List.mem_flatMap]
          exists trg.val.rule.head[i]
          constructor
          . simp
          . unfold FunctionFreeConjunction.predicates
            rw [List.mem_map]
            exists a
            constructor
            . exact a_mem
            . rw [← p_mem, ← f_mem]
              rfl

  theorem parallelSkolemChase_constants (kb : KnowledgeBase sig) (obs : LaxObsoletenessCondition sig) :
      ∀ n, (kb.parallelSkolemChase obs n).constants ⊆ (kb.rules.head_constants ∪ kb.db.constants) := by
    intro n
    induction n with
    | zero =>
      unfold parallelSkolemChase
      apply Set.subset_union_of_subset_right
      rw [Database.toFactSet_constants_same]
      apply Set.subset_refl
    | succ n ih =>
      unfold parallelSkolemChase
      intro c c_mem
      rcases c_mem with ⟨f, f_mem, c_mem⟩
      cases f_mem with
      | inl f_mem => apply ih; exists f
      | inr f_mem =>
        rcases f_mem with ⟨trg, trg_act, f_mem⟩
        unfold PreTrigger.mapped_head at f_mem
        rcases f_mem with ⟨i, f_mem⟩
        rw [List.getElem_map, List.mem_map] at f_mem
        rcases f_mem with ⟨a, a_mem, f_mem⟩
        rw [List.get_eq_getElem, List.getElem_zipIdx] at a_mem

        -- NOTE: heavily inspired by: constantsInChaseBranchAreFromDatabase

        rw [← f_mem] at c_mem
        unfold PreTrigger.apply_to_function_free_atom at c_mem
        unfold Fact.constants at c_mem
        rw [List.mem_flatMap] at c_mem
        rcases c_mem with ⟨tree, tree_mem, c_mem⟩
        simp only [TermMapping.apply_generalized_atom] at tree_mem
        rw [List.mem_map] at tree_mem
        rcases tree_mem with ⟨voc, voc_mem, tree_eq⟩
        unfold PreTrigger.apply_to_var_or_const at tree_eq

        cases voc with
        | const d =>
          simp only [Function.comp_apply, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize] at tree_eq
          apply Or.inl
          unfold RuleSet.head_constants
          exists trg.val.rule
          constructor
          . exact trg.property
          . unfold Rule.head_constants
            rw [List.mem_flatMap]
            exists trg.val.rule.head[i]
            constructor
            . simp
            . unfold FunctionFreeConjunction.consts
              rw [List.mem_flatMap]
              exists a
              constructor
              . exact a_mem
              . unfold FunctionFreeAtom.constants
                apply VarOrConst.mem_filterConsts_of_const
                rw [← tree_eq] at c_mem
                rw [GroundTerm.constants_const, List.mem_singleton] at c_mem
                rw [c_mem]
                exact voc_mem
        | var v =>
          simp only [Function.comp_apply, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize] at tree_eq

          cases Decidable.em (v ∈ trg.val.rule.frontier) with
          | inl v_frontier =>
            simp [v_frontier] at tree_eq

            apply ih
            rcases (trg.val.rule.frontier_occurs_in_body _ v_frontier) with ⟨b, b_mem, v_mem⟩
            exists trg.val.subs.apply_function_free_atom b
            constructor
            . apply trg_act.left
              rw [List.mem_toSet]
              unfold PreTrigger.mapped_body
              simp only [GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]
              rw [List.mem_map]
              exists b
            . unfold Fact.constants
              rw [List.mem_flatMap]
              exists tree
              constructor
              . rw [← tree_eq]
                unfold GroundSubstitution.apply_function_free_atom
                unfold TermMapping.apply_generalized_atom
                rw [List.mem_map]
                exists (VarOrConst.var v)
              . exact c_mem
          | inr v_frontier =>
            simp [v_frontier] at tree_eq
            rw [← tree_eq] at c_mem
            rw [GroundTerm.constants_func, List.mem_flatMap] at c_mem
            rcases c_mem with ⟨tree, tree_mem, c_mem⟩
            rw [List.mem_map] at tree_mem
            rcases tree_mem with ⟨v, v_frontier, tree_eq⟩

            -- from here its the same as in the inl case
            apply ih
            rcases (trg.val.rule.frontier_occurs_in_body _ v_frontier) with ⟨b, b_mem, v_mem⟩
            exists trg.val.subs.apply_function_free_atom b
            constructor
            . apply trg_act.left
              rw [List.mem_toSet]
              unfold PreTrigger.mapped_body
              simp only [GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]
              rw [List.mem_map]
              exists b
            . unfold Fact.constants
              rw [List.mem_flatMap]
              exists tree
              constructor
              . rw [← tree_eq]
                unfold GroundSubstitution.apply_function_free_atom
                unfold TermMapping.apply_generalized_atom
                rw [List.mem_map]
                exists (VarOrConst.var v)
              . exact c_mem

  theorem parallelSkolemChase_functions (kb : KnowledgeBase sig) (obs : LaxObsoletenessCondition sig) :
      ∀ n, (kb.parallelSkolemChase obs n).function_symbols ⊆ (kb.rules.skolem_functions) := by
    intro n
    induction n with
    | zero =>
      unfold parallelSkolemChase
      intro func func_mem
      unfold FactSet.function_symbols at func_mem
      rcases func_mem with ⟨f, f_mem, func_mem⟩
      unfold Fact.function_symbols at func_mem
      rw [List.mem_flatMap] at func_mem
      rcases func_mem with ⟨t, t_mem, func_mem⟩
      cases eq : t with
      | const c => simp [eq, GroundTerm.functions_const] at func_mem
      | func _ _ =>
        have func_free := kb.db.toFactSet.property.right
        specialize func_free f f_mem t t_mem
        rcases func_free with ⟨c, t_eq⟩
        rw [t_eq] at eq
        simp [GroundTerm.const, GroundTerm.func] at eq
    | succ n ih =>
      unfold parallelSkolemChase
      intro func func_mem
      rcases func_mem with ⟨f, f_mem, func_mem⟩
      cases f_mem with
      | inl f_mem => apply ih; exists f
      | inr f_mem =>
        rcases f_mem with ⟨trg, trg_act, f_mem⟩
        unfold PreTrigger.mapped_head at f_mem
        rcases f_mem with ⟨i, f_mem⟩
        rw [List.getElem_map, List.mem_map] at f_mem
        rcases f_mem with ⟨a, a_mem, f_mem⟩
        rw [List.get_eq_getElem, List.getElem_zipIdx] at a_mem

        unfold Fact.function_symbols at func_mem
        rw [List.mem_flatMap] at func_mem
        rcases func_mem with ⟨t, t_mem, func_mem⟩
        rw [← f_mem] at t_mem
        simp only [PreTrigger.apply_to_function_free_atom, TermMapping.apply_generalized_atom] at t_mem
        rw [List.mem_map] at t_mem
        rcases t_mem with ⟨voc, voc_mem, t_mem⟩
        simp only [PreTrigger.apply_to_var_or_const, Function.comp_apply, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize] at t_mem
        cases voc with
        | const c =>
          simp only at t_mem
          rw [← t_mem] at func_mem
          simp [GroundTerm.functions_const] at func_mem
        | var v =>
          simp only at t_mem
          cases Decidable.em (v ∈ trg.val.rule.frontier) with
          | inl v_frontier =>
            simp [v_frontier] at t_mem
            -- apply ih here with some massaging
            apply ih
            rcases trg.val.rule.frontier_occurs_in_body _ v_frontier with ⟨body_atom, body_atom_mem, v_mem⟩
            unfold FactSet.function_symbols
            exists (trg.val.subs.apply_function_free_atom body_atom)
            constructor
            . apply trg_act.left
              rw [List.mem_toSet]
              simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]
              rw [List.mem_map]
              exists body_atom
            . unfold Fact.function_symbols
              rw [List.mem_flatMap]
              exists t
              constructor
              . unfold GroundSubstitution.apply_function_free_atom
                unfold TermMapping.apply_generalized_atom
                rw [List.mem_map]
                exists VarOrConst.var v
              . exact func_mem
          | inr v_frontier =>
            simp only [v_frontier, ↓reduceIte] at t_mem
            rw [← t_mem] at func_mem
            simp only [GroundTerm.functions_func] at func_mem
            rw [List.mem_cons] at func_mem
            cases func_mem with
            | inl func_mem =>
              exists trg.val.rule
              constructor
              . exact trg.property
              . unfold Rule.skolem_functions
                rw [List.mem_flatMap]
                exists (trg.val.rule.head[i], i)
                constructor
                . rw [List.mem_zipIdx_iff_getElem?]
                  simp
                . rw [func_mem]
                  simp
                  constructor
                  . unfold FunctionFreeConjunction.vars
                    rw [List.mem_flatMap]
                    exists a
                    constructor
                    . exact a_mem
                    . unfold FunctionFreeAtom.variables
                      apply VarOrConst.mem_filterVars_of_var
                      exact voc_mem
                  . exact v_frontier
            | inr func_mem =>
              rw [List.mem_flatMap] at func_mem
              rcases func_mem with ⟨tree, tree_mem, func_mem⟩
              rw [List.mem_map] at tree_mem
              rcases tree_mem with ⟨frontier_var, frontier_var_mem, tree_mem⟩

              -- apply ih here with some massaging (should be similar to inl case for v_frontier
              apply ih
              rcases trg.val.rule.frontier_occurs_in_body _ frontier_var_mem with ⟨body_atom, body_atom_mem, frontier_var_mem⟩
              unfold FactSet.function_symbols
              exists (trg.val.subs.apply_function_free_atom body_atom)
              constructor
              . apply trg_act.left
                rw [List.mem_toSet]
                simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]
                rw [List.mem_map]
                exists body_atom
              . unfold Fact.function_symbols
                rw [List.mem_flatMap]
                exists (trg.val.subs frontier_var)
                constructor
                . unfold GroundSubstitution.apply_function_free_atom
                  unfold TermMapping.apply_generalized_atom
                  rw [List.mem_map]
                  exists VarOrConst.var frontier_var
                . rw [← tree_mem] at func_mem
                  exact func_mem

  def deterministicSkolemChaseResult (kb : KnowledgeBase sig) (obs : LaxObsoletenessCondition sig) : FactSet sig := fun f => ∃ n, f ∈ parallelSkolemChase kb obs n

  theorem deterministicSkolemChaseResult_eq_every_chase_branch_result (kb : KnowledgeBase sig) (det : kb.rules.isDeterministic) : ∀ (cb : ChaseBranch (SkolemObsoleteness sig) kb), cb.result = kb.deterministicSkolemChaseResult (DeterministicSkolemObsoleteness sig) := by
    intro cb
    apply Set.ext
    intro f
    unfold ChaseBranch.result
    unfold deterministicSkolemChaseResult
    constructor
    . intro h
      rcases h with ⟨n, h⟩
      induction n generalizing f with
      | zero =>
        rw [cb.database_first, Option.is_some_and] at h
        exists 0
      | succ n ih =>
        -- should be easy enough: get n from induction hypothesis and then use n+1
        rw [Option.is_some_and_iff] at h
        rcases h with ⟨node, eq_node, h⟩
        rw [cb.origin_trg_result_yields_next_node_facts n node eq_node] at h
        cases h with
        | inl h =>
          specialize ih f
          rw [cb.prev_node_eq n (by simp [eq_node]), Option.is_some_and] at ih
          specialize ih h
          exact ih
        | inr h =>
          let prev_node := cb.prev_node n (by simp [eq_node])

          have : ∃ n, prev_node.facts.val ⊆ kb.parallelSkolemChase (DeterministicSkolemObsoleteness sig) n := by
            have prev_finite := prev_node.facts.property
            rcases prev_finite with ⟨prev_l, _, prev_l_eq⟩

            have : ∀ (l : List (Fact sig)), (∀ e, e ∈ l -> e ∈  prev_node.facts.val) -> ∃ n, (∀ e, e ∈ l -> e ∈ kb.parallelSkolemChase (DeterministicSkolemObsoleteness sig) n) := by
              intro l l_sub
              induction l with
              | nil => exists 0; intro e; simp
              | cons hd tl ih_inner =>
                have from_ih := ih_inner (by intro e e_mem; apply l_sub; simp [e_mem])
                rcases from_ih with ⟨n_from_ih, from_ih⟩

                have from_hd := ih hd
                rw [cb.prev_node_eq n (by simp [eq_node]), Option.is_some_and] at from_hd
                specialize from_hd (by apply l_sub; simp)
                rcases from_hd with ⟨n_from_hd, from_hd⟩

                cases Decidable.em (n_from_ih ≤ n_from_hd) with
                | inl le =>
                  exists n_from_hd
                  intro f f_mem
                  simp at f_mem
                  cases f_mem with
                  | inl f_mem => rw [f_mem]; exact from_hd
                  | inr f_mem =>
                    rcases Nat.exists_eq_add_of_le le with ⟨diff, le⟩
                    rw [le]
                    apply kb.parallelSkolemChase_subset_all_following (DeterministicSkolemObsoleteness sig) n_from_ih diff
                    apply from_ih; exact f_mem
                | inr lt =>
                  simp at lt
                  have le := Nat.le_of_lt lt
                  exists n_from_ih
                  intro f f_mem
                  simp at f_mem
                  cases f_mem with
                  | inr f_mem => apply from_ih; exact f_mem
                  | inl f_mem =>
                    rcases Nat.exists_eq_add_of_le le with ⟨diff, le⟩
                    rw [le]
                    apply kb.parallelSkolemChase_subset_all_following (DeterministicSkolemObsoleteness sig) n_from_hd diff
                    rw [f_mem]; exact from_hd

            specialize this prev_l (by intro f; exact (prev_l_eq f).mp)
            rcases this with ⟨n, this⟩
            exists n
            intro f
            rw [← prev_l_eq]
            exact this f
          rcases this with ⟨n, prev_subs⟩

          exists n+1
          unfold parallelSkolemChase

          -- TODO: would be Decidable if we define sets in the parallelSkolemChase to be finite
          cases Classical.em (f ∈ kb.parallelSkolemChase (DeterministicSkolemObsoleteness sig) n) with
          | inl mem => apply Or.inl; exact mem
          | inr not_mem =>
            apply Or.inr
            let origin := node.origin.get (cb.origin_isSome _ eq_node)
            exists ⟨{ rule := origin.fst.val.rule, subs := origin.fst.val.subs }, origin.fst.property⟩
            constructor
            . unfold Trigger.active
              constructor
              . unfold PreTrigger.loaded
                apply Set.subset_trans (b := prev_node.facts.val)
                . exact (cb.origin_trg_is_active _ _ eq_node).left
                . exact prev_subs
              . intro contra
                apply not_mem
                apply contra.right origin.snd
                exact h
            . rw [List.mem_toSet] at h
              exists origin.snd
    . intro h
      rcases h with ⟨n, h⟩
      induction n generalizing f with
      | zero =>
        exists 0
        rw [cb.database_first, Option.is_some_and]
        exact h
      | succ n ih =>
        -- we need to invoke fairness somehow
        unfold parallelSkolemChase at h
        cases h with
        | inl h => exact ih _ h
        | inr h =>
          rcases h with ⟨trg, trg_active, f_mem⟩

          have trg_loaded_somewhere : ∃ n, (cb.branch.infinite_list n).is_some_and (fun node => trg.val.loaded node.facts.val) := by
            have : ∀ (l : List (Fact sig)), (∀ e, e ∈ l -> e ∈ trg.val.mapped_body) -> ∃ n, (cb.branch.infinite_list n).is_some_and (fun node => (∀ e, e ∈ l -> e ∈ node.facts.val)) := by
              intro l l_sub
              induction l with
              | nil => exists 0; rw [cb.database_first, Option.is_some_and]; simp
              | cons hd tl ih_inner =>
                have from_ih := ih_inner (by intro f f_mem; apply l_sub; simp [f_mem])
                rcases from_ih with ⟨n_from_ih, from_ih⟩

                cases eq_from_ih : cb.branch.infinite_list n_from_ih with
                | none => rw [eq_from_ih, Option.is_some_and] at from_ih; simp at from_ih
                | some node_from_ih =>
                rw [eq_from_ih, Option.is_some_and] at from_ih

                have from_hd := ih hd (by apply trg_active.left; rw [List.mem_toSet]; apply l_sub; simp)
                rcases from_hd with ⟨n_from_hd, from_hd⟩

                cases eq_from_hd : cb.branch.infinite_list n_from_hd with
                | none => rw [eq_from_hd, Option.is_some_and] at from_hd; simp at from_hd
                | some node_from_hd =>
                rw [eq_from_hd, Option.is_some_and] at from_hd

                cases Decidable.em (n_from_ih ≤ n_from_hd) with
                | inl le =>
                  exists n_from_hd
                  rw [eq_from_hd, Option.is_some_and]
                  intro f f_mem
                  simp at f_mem
                  cases f_mem with
                  | inl f_mem => rw [f_mem]; exact from_hd
                  | inr f_mem =>
                    rcases Nat.exists_eq_add_of_le le with ⟨diff, le⟩
                    have subsetAllFollowing := ChaseBranch.stepIsSubsetOfAllFollowing cb n_from_ih _ eq_from_ih diff
                    rw [← le, eq_from_hd, Option.is_none_or] at subsetAllFollowing
                    apply subsetAllFollowing
                    apply from_ih; exact f_mem
                | inr lt =>
                  simp at lt
                  have le := Nat.le_of_lt lt
                  exists n_from_ih
                  rw [eq_from_ih, Option.is_some_and]
                  intro f f_mem
                  simp at f_mem
                  cases f_mem with
                  | inr f_mem => apply from_ih; exact f_mem
                  | inl f_mem =>
                    rcases Nat.exists_eq_add_of_le le with ⟨diff, le⟩
                    have subsetAllFollowing := ChaseBranch.stepIsSubsetOfAllFollowing cb n_from_hd _ eq_from_hd diff
                    rw [← le, eq_from_ih, Option.is_none_or] at subsetAllFollowing
                    apply subsetAllFollowing
                    rw [f_mem]; exact from_hd

            specialize this trg.val.mapped_body (by simp)
            rcases this with ⟨n, this⟩
            exists n
          rcases trg_loaded_somewhere with ⟨loaded_n, trg_loaded_somewhere⟩
          cases eq_node_loaded : cb.branch.infinite_list loaded_n with
          | none => rw [eq_node_loaded, Option.is_some_and] at trg_loaded_somewhere; simp at trg_loaded_somewhere
          | some node_loaded =>
          rw [eq_node_loaded, Option.is_some_and] at trg_loaded_somewhere

          have fair := cb.fairness ⟨{ rule := trg.val.rule, subs:= trg.val.subs }, trg.property⟩
          rcases fair with ⟨fairness_n, fair⟩
          cases eq_node_fairness : cb.branch.infinite_list fairness_n with
          | none => rw [eq_node_fairness, Option.is_some_and] at fair; simp at fair
          | some node_fairness =>
          rw [eq_node_fairness, Option.is_some_and] at fair

          cases Decidable.em (loaded_n ≤ fairness_n) with
          | inl le =>
            exists fairness_n
            rw [eq_node_fairness, Option.is_some_and]
            have trg_not_active := fair.left
            unfold Trigger.active at trg_not_active
            simp only [not_and, Classical.not_not] at trg_not_active

            have trg_loaded : trg.val.loaded node_fairness.facts.val := by
              intro f f_mem
              rcases Nat.exists_eq_add_of_le le with ⟨diff, le⟩
              have subsetAllFollowing := ChaseBranch.stepIsSubsetOfAllFollowing cb loaded_n _ eq_node_loaded diff
              rw [← le, eq_node_fairness, Option.is_none_or] at subsetAllFollowing
              apply subsetAllFollowing
              apply trg_loaded_somewhere
              exact f_mem

            specialize trg_not_active trg_loaded
            rcases trg_not_active with ⟨disj_index, trg_not_active⟩
            apply trg_not_active
            have disj_index_zero : disj_index.val = 0 := by
              have isLt := disj_index.isLt
              simp only [PreTrigger.length_mapped_head] at isLt
              specialize det _ trg.property
              unfold Rule.isDeterministic at det
              rw [decide_eq_true_iff] at det
              rw [det, Nat.lt_one_iff] at isLt
              exact isLt
            rcases f_mem with ⟨i, f_mem⟩
            have i_zero : i.val = 0 := by
              have isLt := i.isLt
              simp only [PreTrigger.length_mapped_head] at isLt
              specialize det _ trg.property
              unfold Rule.isDeterministic at det
              rw [decide_eq_true_iff] at det
              rw [det, Nat.lt_one_iff] at isLt
              exact isLt
            rw [List.mem_toSet]
            simp only [disj_index_zero]
            simp only [i_zero] at f_mem
            exact f_mem
          | inr lt =>
            simp at lt

            exists loaded_n
            rw [eq_node_loaded, Option.is_some_and]
            have trg_not_active := fair.right loaded_n lt
            rw [eq_node_loaded, Option.is_none_or] at trg_not_active
            unfold Trigger.active at trg_not_active
            simp only [not_and, Classical.not_not] at trg_not_active

            specialize trg_not_active trg_loaded_somewhere
            rcases trg_not_active with ⟨disj_index, trg_not_active⟩
            apply trg_not_active
            have disj_index_zero : disj_index.val = 0 := by
              have isLt := disj_index.isLt
              simp only [PreTrigger.length_mapped_head] at isLt
              specialize det _ trg.property
              unfold Rule.isDeterministic at det
              rw [decide_eq_true_iff] at det
              rw [det, Nat.lt_one_iff] at isLt
              exact isLt
            rcases f_mem with ⟨i, f_mem⟩
            have i_zero : i.val = 0 := by
              have isLt := i.isLt
              simp only [PreTrigger.length_mapped_head] at isLt
              specialize det _ trg.property
              unfold Rule.isDeterministic at det
              rw [decide_eq_true_iff] at det
              rw [det, Nat.lt_one_iff] at isLt
              exact isLt
            rw [List.mem_toSet]
            simp only [disj_index_zero]
            simp only [i_zero] at f_mem
            exact f_mem

  theorem deterministicSkolemChaseResult_predicates (kb : KnowledgeBase sig) (obs : LaxObsoletenessCondition sig) :
      (kb.deterministicSkolemChaseResult obs).predicates ⊆ (kb.rules.predicates ∪ kb.db.toFactSet.val.predicates) := by
    intro p p_mem
    rcases p_mem with ⟨f, f_mem, p_mem⟩
    rcases f_mem with ⟨n, f_mem⟩
    apply kb.parallelSkolemChase_predicates obs n
    exists f

  theorem deterministicSkolemChaseResult_constants (kb : KnowledgeBase sig) (obs : LaxObsoletenessCondition sig) :
      (kb.deterministicSkolemChaseResult obs).constants ⊆ (kb.rules.head_constants ∪ kb.db.constants) := by
    intro c c_mem
    rcases c_mem with ⟨f, f_mem, c_mem⟩
    rcases f_mem with ⟨n, f_mem⟩
    apply kb.parallelSkolemChase_constants obs n
    exists f

  theorem deterministicSkolemChaseResult_functions (kb : KnowledgeBase sig) (obs : LaxObsoletenessCondition sig) :
      (kb.deterministicSkolemChaseResult obs).function_symbols ⊆ (kb.rules.skolem_functions) := by
    intro func func_mem
    rcases func_mem with ⟨f, f_mem, func_mem⟩
    rcases f_mem with ⟨n, f_mem⟩
    apply kb.parallelSkolemChase_functions obs n
    exists f

end KnowledgeBase

namespace RuleSet

  def criticalInstance (rs : RuleSet sig) (finite : rs.rules.finite) (special_const : sig.C) : Database sig :=
    ⟨fun f => f.predicate ∈ rs.predicates ∧ ∀ t, t ∈ f.terms -> (t = special_const ∨ t ∈ rs.constants), by
      -- TODO: this is very close to part of the proof of FactSet.finite_of_preds_finite_of_terms_finite
      -- but we cannot use it since our set is not Set (Fact sig) but Set (FunctionFreeFact sig)...
      -- maybe we can generalize this someday

      have preds_finite := rs.predicates_finite_of_finite finite
      rcases preds_finite with ⟨l_preds, _, preds_eq⟩
      have consts_finite := rs.constants_finite_of_finite finite
      rcases consts_finite with ⟨l_consts, _, consts_eq⟩

      exists (l_preds.flatMap (fun p =>
        (all_lists_of_length (special_const :: l_consts) (sig.arity p)).attach.map (fun ⟨ts, mem⟩ =>
          {
            predicate := p
            terms := ts
            arity_ok := ((mem_all_lists_of_length (special_const :: l_consts) (sig.arity p) ts).mp mem).left
          }
        )
      )).eraseDupsKeepRight

      constructor
      . apply List.nodup_eraseDupsKeepRight
      . intro f
        rw [List.mem_eraseDupsKeepRight]
        simp only [List.mem_flatMap, List.mem_map, List.mem_attach, true_and, Subtype.exists]
        constructor
        . intro h
          rcases h with ⟨pred, pred_mem, ts, ts_mem, f_eq⟩
          rw [← f_eq]
          constructor
          . rw [preds_eq] at pred_mem
            exact pred_mem
          . rw [mem_all_lists_of_length] at ts_mem
            intro t t_mem
            rw [← consts_eq]
            rw [← List.mem_cons]
            apply ts_mem.right
            exact t_mem
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
              . intro t t_mem; rw [List.mem_cons]; rw [consts_eq]; apply ts_mem; exact t_mem
            )
    ⟩

  def mfaKb (rs : RuleSet sig) (finite : rs.rules.finite) (special_const : sig.C) : KnowledgeBase sig := {
    rules := rs
    db := criticalInstance rs finite special_const
  }

  theorem mfaKb_db_constants (rs : RuleSet sig) (finite : rs.rules.finite) (special_const : sig.C) :
      ∀ c, c ∈ (rs.mfaKb finite special_const).db.constants.val -> (c = special_const ∨ c ∈ rs.constants) := by
    intro c c_mem
    unfold mfaKb at c_mem
    unfold criticalInstance at c_mem
    unfold Database.constants at c_mem
    simp only at c_mem
    rcases c_mem with ⟨f, f_mem, c_mem⟩
    apply f_mem.right
    exact c_mem

  def mfaSet (rs : RuleSet sig) (finite : rs.rules.finite) (special_const : sig.C) (obs : MfaObsoletenessCondition sig) : FactSet sig :=
    (rs.mfaKb finite special_const).deterministicSkolemChaseResult obs

  theorem mfaSet_contains_every_chase_step_for_every_kb_except_for_facts_with_predicates_not_from_rs (rs : RuleSet sig) (finite : rs.rules.finite) (special_const : sig.C) (mfa_obs : MfaObsoletenessCondition sig) : ∀ {db : Database sig} {obs : ObsoletenessCondition sig}, (mfa_obs.blocks_obs obs rs special_const) -> ∀ (cb : ChaseBranch obs { rules := rs, db := db }) (n : Nat), (cb.branch.infinite_list n).is_none_or (fun node => ∀ f, f.predicate ∈ rs.predicates -> f ∈ node.facts.val -> ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact f) ∈ (rs.mfaSet finite special_const mfa_obs)) := by
    intro db obs blocks cb n
    induction n with
    | zero =>
      rw [cb.database_first, Option.is_none_or]
      simp only
      intro f f_predicate f_mem
      exists 0
      unfold KnowledgeBase.parallelSkolemChase
      unfold Database.toFactSet
      unfold RuleSet.mfaKb
      unfold criticalInstance
      simp only

      have every_t_const : ∀ t, t ∈ ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact f).terms -> ∃ c, t = GroundTerm.const c ∧ (c = special_const ∨ c ∈ rs.constants) := by
        intro t t_mem
        unfold ConstantMapping.apply_fact at t_mem
        unfold TermMapping.apply_generalized_atom at t_mem
        simp only [List.mem_map] at t_mem
        rcases t_mem with ⟨s, s_mem, t_eq⟩

        have isFunctionFree := db.toFactSet.property.right
        specialize isFunctionFree _ f_mem
        specialize isFunctionFree _ s_mem
        rcases isFunctionFree with ⟨c, s_eq⟩
        exists (rs.mfaConstantMapping special_const) c
        constructor
        . rw [← t_eq, s_eq]
          simp [StrictConstantMapping.toConstantMapping, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, GroundTerm.const]
        . cases Classical.em (c ∈ rs.constants) with
          | inl c_mem => apply Or.inr; simp [mfaConstantMapping, c_mem]
          | inr c_mem => apply Or.inl; simp [mfaConstantMapping, c_mem]
      have f_func_free : ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact f).isFunctionFree := by
        intro t t_mem
        rcases every_t_const t t_mem with ⟨c, t_eq, _⟩
        exists c

      exists ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact f).toFunctionFreeFact f_func_free
      constructor
      . unfold Fact.toFunctionFreeFact
        constructor
        . exact f_predicate
        . simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists, forall_exists_index]
          intro c t t_arity_ok t_mem c_eq
          specialize every_t_const ⟨t, t_arity_ok⟩ t_mem
          rcases every_t_const with ⟨d, d_eq, goal⟩
          rw [← c_eq]
          simp only [d_eq]
          simp [GroundTerm.const, GroundTerm.toConst, goal]
      . rw [Fact.toFact_after_toFunctionFreeFact_is_id]
    | succ n ih =>
      rw [Option.is_none_or_iff]
      intro node eq_node
      rw [cb.prev_node_eq n (by simp [eq_node]), Option.is_none_or] at ih
      intro f f_predicate f_mem
      rw [cb.origin_trg_result_yields_next_node_facts _ _ eq_node] at f_mem
      cases f_mem with
      | inl f_mem =>
        apply ih
        . exact f_predicate
        . exact f_mem
      | inr f_mem =>
        let prev_node := cb.prev_node n (by simp [eq_node])
        unfold RuleSet.mfaSet
        unfold KnowledgeBase.deterministicSkolemChaseResult

        have : ∃ n, ∀ f, f.predicate ∈ rs.predicates -> f ∈ prev_node.facts.val -> ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact f) ∈ (rs.mfaKb finite special_const).parallelSkolemChase mfa_obs n := by
          let kb := rs.mfaKb finite special_const
          let prev_filtered : FactSet sig := fun f => f.predicate ∈ rs.predicates ∧ f ∈ prev_node.facts.val
          have prev_finite : prev_filtered.finite := by
            rcases prev_node.facts.property with ⟨prev_l, _, prev_l_eq⟩
            rcases (RuleSet.predicates_finite_of_finite _ finite) with ⟨preds_l, _, preds_l_eq⟩
            exists (prev_l.filter (fun f => f.predicate ∈ preds_l)).eraseDupsKeepRight
            constructor
            . apply List.nodup_eraseDupsKeepRight
            . intro f
              rw [List.mem_eraseDupsKeepRight, List.mem_filter]
              rw [prev_l_eq]
              unfold prev_filtered
              simp only [preds_l_eq, decide_eq_true_eq, And.comm]
              rfl
          rcases prev_finite with ⟨prev_l, _, prev_l_eq⟩

          have : ∀ (l : List (Fact sig)), (∀ e, e ∈ l -> e.predicate ∈ rs.predicates ∧ e ∈ prev_node.facts.val) -> ∃ n, (∀ e, e ∈ l -> ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact e) ∈ (kb.parallelSkolemChase mfa_obs n)) := by
            intro l l_sub
            induction l with
            | nil => exists 0; intro e; simp
            | cons hd tl ih_inner =>
              have from_ih := ih_inner (by intro e e_mem; apply l_sub; simp [e_mem])
              rcases from_ih with ⟨n_from_ih, from_ih⟩

              have from_hd := ih hd (l_sub hd (by simp)).left (l_sub hd (by simp)).right
              rcases from_hd with ⟨n_from_hd, from_hd⟩

              cases Decidable.em (n_from_ih ≤ n_from_hd) with
              | inl le =>
                exists n_from_hd
                intro f f_mem
                simp at f_mem
                cases f_mem with
                | inl f_mem => rw [f_mem]; exact from_hd
                | inr f_mem =>
                  rcases Nat.exists_eq_add_of_le le with ⟨diff, le⟩
                  rw [le]
                  apply kb.parallelSkolemChase_subset_all_following mfa_obs n_from_ih diff
                  apply from_ih; exact f_mem
              | inr lt =>
                simp at lt
                have le := Nat.le_of_lt lt
                exists n_from_ih
                intro f f_mem
                simp at f_mem
                cases f_mem with
                | inr f_mem => apply from_ih; exact f_mem
                | inl f_mem =>
                  rcases Nat.exists_eq_add_of_le le with ⟨diff, le⟩
                  rw [le]
                  apply kb.parallelSkolemChase_subset_all_following mfa_obs n_from_hd diff
                  rw [f_mem]; exact from_hd

          specialize this prev_l (by
            intro f f_mem
            rw [prev_l_eq] at f_mem
            unfold prev_filtered at f_mem
            exact f_mem
          )

          rcases this with ⟨m, this⟩
          exists m
          intro f f_pred f_mem
          specialize this f (by
            rw [prev_l_eq]
            unfold prev_filtered
            constructor
            . exact f_pred
            . exact f_mem
          )
          exact this

        rcases this with ⟨m, prev_node_subs_parallel_chase⟩
        exists (m+1)
        unfold KnowledgeBase.parallelSkolemChase
        simp only [instMembershipSet]

        rw [Classical.or_iff_not_imp_left]
        intro f_not_in_prev

        let origin := node.origin.get (cb.origin_isSome _ eq_node)
        let trg := origin.fst
        let disj_index := origin.snd

        let adjusted_trg : RTrigger mfa_obs (rs.mfaKb finite special_const).rules := ⟨⟨trg.val.rule, (rs.mfaConstantMapping special_const).toConstantMapping.apply_ground_term ∘ trg.val.subs⟩, trg.property⟩

        exists adjusted_trg
        constructor
        . constructor
          . apply Set.subset_trans (b := fun f => f.predicate ∈ rs.predicates ∧ f ∈ ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact_set prev_node.facts.val))
            . intro f f_mem
              rw [List.mem_toSet] at f_mem
              simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list, List.mem_map] at f_mem
              rcases f_mem with ⟨a, a_mem, f_eq⟩
              unfold adjusted_trg at a_mem
              constructor
              . rw [← f_eq]
                exists trg.val.rule
                constructor
                . exact trg.property
                . unfold Rule.predicates
                  rw [List.mem_append]
                  apply Or.inl
                  unfold FunctionFreeConjunction.predicates
                  rw [List.mem_map]
                  exists a
              . exists trg.val.subs.apply_function_free_atom a
                constructor
                . apply (cb.origin_trg_is_active _ _ eq_node).left
                  rw [List.mem_toSet]
                  simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list, List.mem_map]
                  exists a
                . rw [← f_eq]
                  rw [← Function.comp_apply (f := (rs.mfaConstantMapping special_const).toConstantMapping.apply_ground_term.apply_generalized_atom)]
                  rw [← TermMapping.apply_generalized_atom_compose]
                  apply TermMapping.apply_generalized_atom_congr_left
                  intro voc voc_mem
                  cases voc with
                  | var v => rfl
                  | const c =>
                    simp only [Function.comp_apply, GroundSubstitution.apply_var_or_const, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, StrictConstantMapping.toConstantMapping, GroundTerm.const]
                    apply Subtype.eq
                    simp only [FiniteTree.leaf.injEq]
                    rw [rs.mfaConstantMapping_id_on_rs_constants]
                    exists trg.val.rule
                    constructor
                    . exact trg.property
                    unfold Rule.constants
                    rw [List.mem_append]
                    apply Or.inl
                    unfold FunctionFreeConjunction.consts
                    rw [List.mem_flatMap]
                    exists a
                    constructor
                    . exact a_mem
                    . apply VarOrConst.mem_filterConsts_of_const; exact voc_mem
            . intro f f_mem
              rcases f_mem with ⟨f_pred, f', f'_mem, f_eq⟩
              rw [f_eq]
              apply prev_node_subs_parallel_chase
              . rw [f_eq] at f_pred
                exact f_pred
              . exact f'_mem
          . intro contra
            have contra := blocks cb n trg _ (by
              exists disj_index
              intro contra
              apply f_not_in_prev
              apply contra
              apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
              exact f_mem
            ) contra
            rw [ChaseBranch.prev_node_eq _ _ (by simp [eq_node])] at contra
            simp only [Option.is_none_or] at contra
            specialize contra (cb.origin_trg_is_active _ _ eq_node).left

            apply (cb.origin_trg_is_active _ _ eq_node).right
            exact contra
        . rw [List.mem_toSet] at f_mem
          unfold ChaseNode.origin_result at f_mem
          unfold PreTrigger.mapped_head at f_mem
          simp at f_mem
          rcases f_mem with ⟨a, a_mem, f_eq⟩

          let adjusted_disj_index : Fin adjusted_trg.val.mapped_head.length := ⟨disj_index.val, by
            have isLt := disj_index.isLt
            simp only [PreTrigger.length_mapped_head]
            unfold adjusted_trg
            simp only [PreTrigger.length_mapped_head] at isLt
            exact isLt
          ⟩
          exists adjusted_disj_index
          unfold PreTrigger.mapped_head
          simp

          exists (rs.mfaConstantMapping special_const).apply_function_free_atom a
          constructor
          . rw [rs.mfaConstantMapping_id_on_atom_from_rule _ adjusted_trg.val.rule adjusted_trg.property]
            . exact a_mem
            . rw [List.mem_append]
              apply Or.inr
              apply List.mem_flatten_of_mem _ a_mem
              apply List.getElem_mem
          . rw [← f_eq]
            rw [rs.mfaConstantMapping_id_on_atom_from_rule _ adjusted_trg.val.rule adjusted_trg.property]
            . rw [ConstantMapping.apply_fact_swap_apply_to_function_free_atom]
              intro d d_mem
              simp only [StrictConstantMapping.toConstantMapping]
              rw [mfaConstantMapping_id_on_rs_constants]
              apply RuleSet.head_constants_subset_constants
              exists trg.val.rule
              unfold Rule.head_constants
              rw [List.mem_flatMap]
              constructor
              . exact trg.property
              . exists trg.val.rule.head[disj_index.val]'(by rw [← PreTrigger.length_mapped_head]; exact disj_index.isLt)
                constructor
                . apply List.getElem_mem
                . unfold FunctionFreeConjunction.consts
                  rw [List.mem_flatMap]
                  exists a
            . rw [List.mem_append]
              apply Or.inr
              apply List.mem_flatten_of_mem _ a_mem
              apply List.getElem_mem

  theorem filtered_cb_result_subset_mfaSet (rs : RuleSet sig) (finite : rs.rules.finite) (special_const : sig.C) (mfa_obs : MfaObsoletenessCondition sig) : ∀ {db : Database sig} {obs : ObsoletenessCondition sig}, (mfa_obs.blocks_obs obs rs special_const) -> ∀ (cb : ChaseBranch obs { rules := rs, db := db }), ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact_set (fun f => f.predicate ∈ rs.predicates ∧ f ∈ cb.result)) ⊆ (rs.mfaSet finite special_const mfa_obs) := by
    intro db obs blocks cb f f_mem

    rcases f_mem with ⟨f', f'_mem, f_eq⟩
    rcases f'_mem with ⟨f'_pred, f'_mem⟩
    rcases f'_mem with ⟨n, f'_mem⟩
    rw [f_eq]

    cases eq : cb.branch.infinite_list n with
    | none => simp [eq, Option.is_some_and] at f'_mem
    | some node =>
      have := rs.mfaSet_contains_every_chase_step_for_every_kb_except_for_facts_with_predicates_not_from_rs finite special_const mfa_obs blocks cb n
      rw [eq, Option.is_none_or] at this
      apply this
      . exact f'_pred
      . rw [eq, Option.is_some_and] at f'_mem
        exact f'_mem

  theorem terminates_of_mfaSet_finite [Inhabited sig.C] (rs : RuleSet sig) (rs_finite : rs.rules.finite) (mfa_obs : MfaObsoletenessCondition sig) :
      ∀ {obs : ObsoletenessCondition sig}, (mfa_obs.blocks_obs obs rs Inhabited.default) -> (rs.mfaSet rs_finite Inhabited.default mfa_obs).finite -> rs.terminates obs := by
    intro obs blocks mfa_finite
    unfold RuleSet.terminates
    intro db
    unfold KnowledgeBase.terminates
    intro ct
    unfold ChaseTree.terminates
    intro cb cb_mem
    rw [ChaseBranch.terminates_iff_result_finite]

    let res_filtered : FactSet sig := fun f => f.predicate ∈ rs.predicates ∧ f ∈ cb.result
    have res_filtered_finite : res_filtered.finite := by
      have : ((rs.mfaConstantMapping Inhabited.default).toConstantMapping.apply_fact_set (fun f => f.predicate ∈ rs.predicates ∧ f ∈ cb.result)).finite :=
        Set.finite_of_subset_finite mfa_finite (rs.filtered_cb_result_subset_mfaSet rs_finite Inhabited.default mfa_obs blocks cb)

      rcases this with ⟨l, _, l_eq⟩

      let db_constants := db.constants
      rcases db_constants.property with ⟨l_db_c, _, l_db_c_eq⟩

      let rs_constants := rs.head_constants
      have rs_constants_finite : rs_constants.finite := RuleSet.head_constants_finite_of_finite _ rs_finite
      rcases rs_constants_finite with ⟨l_rs_c, _, l_rs_c_eq⟩

      let arguments : FactSet sig := fun f => (∀ c, c ∈ f.constants -> (c ∈ l_db_c ++ l_rs_c)) ∧ ((rs.mfaConstantMapping default).toConstantMapping.apply_fact f) ∈ ((rs.mfaConstantMapping default).toConstantMapping.apply_fact_set res_filtered)
      have arguments_fin : arguments.finite := by
        exists (l.flatMap (fun f => (rs.mfaConstantMapping default).arguments_for_fact (l_db_c ++ l_rs_c) f)).eraseDupsKeepRight
        constructor
        . apply List.nodup_eraseDupsKeepRight
        . intro f
          rw [List.mem_eraseDupsKeepRight, List.mem_flatMap]
          constructor
          . intro h
            rcases h with ⟨f', f'_mem, f_mem⟩
            rw [l_eq] at f'_mem
            have : f' = (rs.mfaConstantMapping default).toConstantMapping.apply_fact f := by
              have := (rs.mfaConstantMapping default).apply_to_arguments_yields_original_fact (l_db_c ++ l_rs_c) f'
              rw [((this _).mp _).right]
              exact f_mem
            rw [this] at f'_mem
            constructor
            . have := (rs.mfaConstantMapping default).apply_to_arguments_yields_original_fact (l_db_c ++ l_rs_c) f' f
              apply (this.mp _).left
              exact f_mem
            . exact f'_mem
          . intro h
            exists (rs.mfaConstantMapping default).toConstantMapping.apply_fact f
            constructor
            . rw [l_eq]
              exact h.right
            . rw [(rs.mfaConstantMapping default).apply_to_arguments_yields_original_fact (l_db_c ++ l_rs_c)]
              simp only [and_true]
              exact h.left

      apply Set.finite_of_subset_finite arguments_fin
      intro f f_mem
      constructor
      . rcases f_mem.right with ⟨step, f_mem⟩
        intro c c_mem
        rw [Option.is_some_and_iff] at f_mem
        rcases f_mem with ⟨node, eq_step, f_mem⟩
        have := ChaseBranch.constantsInStepAreFromDatabaseOrRuleSet cb step node eq_step c (by exists f)
        rw [List.mem_append]
        cases this with
        | inl this => apply Or.inl; rw [l_db_c_eq]; exact this
        | inr this => apply Or.inr; rw [l_rs_c_eq]; exact this
      . apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
        exact f_mem

    have res_sub_db_and_filtered : cb.result ⊆ db.toFactSet.val ∪ res_filtered := by
      have each_step_sub_db_and_filtered : ∀ n, (cb.branch.infinite_list n).is_none_or (fun node => node.facts.val ⊆ db.toFactSet.val ∪ res_filtered) := by
        intro n
        induction n with
        | zero => rw [cb.database_first, Option.is_none_or]; intro f f_mem; apply Or.inl; exact f_mem
        | succ n ih =>
          rw [Option.is_none_or_iff]
          intro node eq_node
          rw [cb.origin_trg_result_yields_next_node_facts n node eq_node]
          intro f f_mem
          cases f_mem with
          | inl f_mem =>
            rw [cb.prev_node_eq n (by simp [eq_node]), Option.is_none_or] at ih
            apply ih
            exact f_mem
          | inr f_mem =>
            apply Or.inr
            constructor
            . -- since f occur in the trigger result, its predicate occurs in the rule and must therefore occur in the ruleset
              let origin := node.origin.get (cb.origin_isSome n eq_node)
              rw [List.mem_toSet] at f_mem
              simp only [ChaseNode.origin_result, PreTrigger.mapped_head] at f_mem
              simp at f_mem
              rcases f_mem with ⟨a, a_mem, f_eq⟩
              rw [← f_eq]
              simp only [PreTrigger.apply_to_function_free_atom]
              exists origin.fst.val.rule
              constructor
              . exact origin.fst.property
              . unfold Rule.predicates
                rw [List.mem_append]
                apply Or.inr
                rw [List.mem_flatMap]
                exists origin.fst.val.rule.head[origin.snd.val]'(by rw [← PreTrigger.length_mapped_head]; exact origin.snd.isLt)
                simp only [List.getElem_mem, true_and]
                unfold FunctionFreeConjunction.predicates
                rw [List.mem_map]
                exists a
            . exists (n+1)
              rw [eq_node, Option.is_some_and]
              rw [cb.origin_trg_result_yields_next_node_facts n node eq_node]
              apply Or.inr
              exact f_mem

      intro f f_mem
      rcases f_mem with ⟨n, f_mem⟩
      cases eq_node : cb.branch.infinite_list n with
      | none => simp [eq_node, Option.is_some_and] at f_mem
      | some node =>
        rw [eq_node, Option.is_some_and] at f_mem
        specialize each_step_sub_db_and_filtered n
        rw [eq_node, Option.is_none_or] at each_step_sub_db_and_filtered
        apply each_step_sub_db_and_filtered
        exact f_mem

    apply Set.finite_of_subset_finite _ res_sub_db_and_filtered
    apply Set.union_finite_of_both_finite
    . exact db.toFactSet.property.left
    . exact res_filtered_finite

  def isMfa [Inhabited sig.C] (rs : RuleSet sig) (finite : rs.rules.finite) (mfa_obs : MfaObsoletenessCondition sig) : Prop :=
    ∀ t, t ∈ (rs.mfaSet finite default mfa_obs).terms -> ¬ PreGroundTerm.cyclic t.val

  theorem terminates_of_isMfa [Inhabited sig.C] (rs : RuleSet sig) (rs_finite : rs.rules.finite) (mfa_obs : MfaObsoletenessCondition sig) :
      ∀ {obs : ObsoletenessCondition sig}, (mfa_obs.blocks_obs obs rs Inhabited.default) -> rs.isMfa rs_finite mfa_obs -> rs.terminates obs := by
    intro obs blocks isMfa
    apply rs.terminates_of_mfaSet_finite rs_finite mfa_obs blocks
    apply FactSet.finite_of_preds_finite_of_terms_finite
    . apply Set.finite_of_subset_finite _ (KnowledgeBase.deterministicSkolemChaseResult_predicates (rs.mfaKb rs_finite default) mfa_obs)
      apply Set.union_finite_of_both_finite
      . apply RuleSet.predicates_finite_of_finite
        exact rs_finite
      . have prop := (rs.mfaKb rs_finite default).db.toFactSet.property.left
        rcases prop with ⟨l, _, l_eq⟩
        exists (l.map (fun f => f.predicate)).eraseDupsKeepRight
        constructor
        . apply List.nodup_eraseDupsKeepRight
        . intro p
          rw [List.mem_eraseDupsKeepRight]
          rw [List.mem_map]
          unfold FactSet.predicates
          constructor
          . intro h
            rcases h with ⟨f, f_mem, p_eq⟩
            exists f
            constructor
            . rw [← l_eq]
              exact f_mem
            . exact p_eq
          . intro h
            rcases h with ⟨f, f_mem, p_eq⟩
            exists f
            constructor
            . rw [l_eq]
              exact f_mem
            . exact p_eq
    . unfold RuleSet.isMfa at isMfa
      let consts := rs.constants
      have consts_finite := rs.constants_finite_of_finite rs_finite
      rcases consts_finite with ⟨l_consts, l_consts_nodup, consts_eq⟩
      let funcs : Set (SkolemFS sig) := rs.skolem_functions
      have funcs_finite : funcs.finite := rs.skolem_functions_finite_of_finite rs_finite
      rcases funcs_finite with ⟨l_funcs, l_funcs_nodup, funcs_eq⟩
      let overapproximation : Set (GroundTerm sig) := fun t => (t.val.depth ≤ l_funcs.length + 1 ∧ (∀ c, c ∈ t.val.leaves -> c = default ∨ c ∈ l_consts) ∧ (∀ func, func ∈ t.val.innerLabels -> func ∈ l_funcs))
      have overapproximation_finite : overapproximation.finite := by
        exists (all_terms_limited_by_depth (default :: l_consts) l_funcs (l_funcs.length + 1)).eraseDupsKeepRight
        constructor
        . apply List.nodup_eraseDupsKeepRight
        . intro t
          rw [List.mem_eraseDupsKeepRight]
          rw [mem_all_terms_limited_by_depth]
          simp only [overapproximation, List.mem_cons]
          rfl
      apply Set.finite_of_subset_finite overapproximation_finite
      intro t t_mem

      have : ∀ func, func ∈ t.val.innerLabels -> func ∈ l_funcs := by
        intro func func_mem
        rw [funcs_eq]
        unfold funcs

        apply (KnowledgeBase.deterministicSkolemChaseResult_functions (rs.mfaKb rs_finite default))
        rcases t_mem with ⟨f, f_mem, t_mem⟩
        exists f
        constructor
        . exact f_mem
        . unfold Fact.function_symbols
          rw [List.mem_flatMap]
          exists t

      unfold overapproximation
      constructor
      . apply Decidable.byContradiction
        intro contra
        apply isMfa t t_mem
        apply PreGroundTerm.cyclic_of_depth_too_big t l_funcs
        . exact l_funcs_nodup
        . exact this
        . simp at contra
          apply Nat.succ_le_of_lt
          exact contra
      constructor
      . intro c c_mem

        have := (KnowledgeBase.deterministicSkolemChaseResult_constants (rs.mfaKb rs_finite default) mfa_obs)
        specialize this c (by
          unfold FactSet.constants
          rcases t_mem with ⟨f, f_mem, t_mem⟩
          exists f
          constructor
          . exact f_mem
          . unfold Fact.constants
            rw [List.mem_flatMap]
            exists t
        )
        rw [consts_eq]
        cases this with
        | inl this =>
          apply Or.inr
          apply RuleSet.head_constants_subset_constants
          exact this
        | inr this =>
          apply rs.mfaKb_db_constants rs_finite default
          exact this
      . exact this

  theorem terminates_of_isMfa_with_DeterministicSkolemObsoleteness [Inhabited sig.C] (rs : RuleSet sig) (rs_finite : rs.rules.finite) :
      rs.isMfa rs_finite (DeterministicSkolemObsoleteness sig) -> rs.terminates obs :=
    rs.terminates_of_isMfa rs_finite (DeterministicSkolemObsoleteness sig) (DeterministicSkolemObsoleteness.blocks_each_obs obs default rs)

  theorem terminates_of_isMfa_with_BlockingObsoleteness [GetFreshInhabitant sig.C] [Inhabited sig.C] (rs : RuleSet sig) (rs_finite : rs.rules.finite) (obs : ObsoletenessCondition sig) (obs_propagates_under_const_mapping : obs.propagates_under_constant_mapping) :
      rs.isMfa rs_finite (BlockingObsoleteness obs rs) -> rs.terminates obs :=
    rs.terminates_of_isMfa rs_finite (BlockingObsoleteness obs rs) (BlockingObsoleteness.blocks_corresponding_obs obs obs_propagates_under_const_mapping rs rs_finite default)

end RuleSet

