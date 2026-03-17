import ExistentialRules.ChaseSequence.Termination.Basic
import ExistentialRules.ChaseSequence.Termination.BacktrackingOfFacts
import ExistentialRules.ChaseSequence.Termination.ConstantMappings.Basic
import ExistentialRules.ChaseSequence.Termination.ConstantMappings.InterplayWithBacktracking
import ExistentialRules.ChaseSequence.Termination.ParallelDeterminizedChase
import ExistentialRules.ChaseSequence.Termination.RenameConstantsApart
import ExistentialRules.Terms.Cyclic

/-!
# Model-Faithful Acyclicity and its Relatives

There is plenty of research around sufficient conditions for chase termination.
These are usually conditions on `RuleSet`s. If they are fulfilled, we know that the `RuleSet.terminates`. If they are not fulfilled, we gain nothing.
Here, we consider variants of Model-Faithful Acyclicity (MFA), Disjunctive MFA (DMFA) and Restricted MFA (RMFA) essentially all at once.
We should note though that technically DMFA and RMFA assume a so-called Datalog-first chase, which always prefers triggers with Datalog rules before all others. So far, we are not modelling this possibility in our chase definitions.
Consequently, we also implement slightly different versions of DMFA and RMFA that simply drop the part that optimizes for Datalog-first sequences.
The modified versions are of course still correct (as we prove) but lifting the restriction of Datalog-first chase comes at the cost of potentially marking fewer rule sets as terminating. Indeed there are rule sets that would terminate for all Datalog-first chases but not for all more liberal application strategies.
In the future, we also aim to formalize the original Datalog-first version.

## How does MFA work?

The idea is almost shockingly simple.
First of all, for MFA, we turn all disjunctions in rules into conjunctions.
Then, we compute the chase on the new rule set and a special database and stop as soon as we see a cyclic function term.
If we see such a term, we do not learn anything about termination.
If we do not see such a term, then the chase computed for MFA will terminate on its own, since there are only finitely many non-cyclic terms.
But then, we can argue that any chase on any database also terminates since MFA basically generalizes all of them.
MFA shows termination of a rule set for the so-called Skolem chase, i.e. if we consider `SkolemObsoleteness` for the `ObsoletenessCondition`.
But SkolemObsoleteness is actually the "most non-terminating" of our `ObsoletenessCondition`s so we really are able to show that `MFA` guarantees termination no matter which `ObsoletenessCondition` we choose.
See `terminates_of_isMfa_with_DeterministicSkolemObsoleteness`. Note what we call `isMfa` in our framework is already a generalized version of MFA that is also able to captures the (modified versions of) DMFA and RMFA by accepting something called `MfaObsoletenessCondition`. So what we call MFA here is really `isMfa` with the `DeterministicSkolemObsoleteness`.

## How do DMFA and RMFA work?

For MFA everything is comparibly simple since there are no disjunctions and we really only care about the Skolem chase.
It is not obvious but in this setting no trigger is every really obsolete unless its exact result is already part of the chase.
But then applying the trigger would not make a difference anyway.
This is different if disjunctions are present or if we consider a stricter `ObsoletenessCondition` (or both). Less triggers might be active and therefore the chase may terminate in more cases.
MFA would still work but maybe we can do better now. This is exactly the motivation behind DMFA and RMFA, where DMFA is optimized for Skolem chase on disjunctive rules and RMFA is designed for the restricted chase, potentially also with disjunctive rules.

The basic idea remains the same. We just simulate the chase on a special database. However, we now want to forbid certain trigger applications; ones that we call "blocked".
Formally, we can say that a trigger is blocked if we know that whenever it is loaded in a chase, then it is necessarily already obsolete.
To see why this may happen, remember that a trigger might require various facts to be introduced during the chase to become loaded. It can happen that the necessary facts at the same time also make the trigger obsolete, in which case we say that it is blocked.
In our framework, we realize this by using `BlockingObsoleteness` for the `MfaObsoletenessCondition` in `isMfa`.
Blocking is very similar for DMFA and RMFA and essentially only differs in the `ObsoletenessCondition` that for DMFA would be `SkolemObsoleteness` and for RMFA would be `RestrictedObsoleteness`. So what we do is simple: `BlockingObsoleteness` is simply defined taking a `ObsoletenessCondition` condition as a parameter. Thereby we obtain an MFA-like condition for any `ObsoletenessCondition` that one can imagine. So we can express DMFA, RMFA, and everything in-between.
We show in `terminates_of_isMfa_with_BlockingObsoleteness` that `isMfa` with any such `BlockingObsoleteness` guarantees termination.

## Our Framework

Despite the differences between MFA and DMFA/RMFA, you may realize that `terminates_of_isMfa_with_DeterministicSkolemObsoleteness` and `terminates_of_isMfa_with_BlockingObsoleteness` essentially use the same proof, namely they just call `terminates_of_isMfa`.
This result is generic over all possible `MfaObsoletenessCondition`s and just demands that the given `MfaObsoletenessCondition` has the `blocks_obs` property with respect to the target `ObsoletenessCondition`.
For example, the `DeterministicSkolemObsoleteness` used for (the original) MFA has the `blocks_obs` property with respect to all `ObsoletenessCondition`s
and the `BlockingObsoleteness` for a given `ObsoletenessCondition` $o$ has the `blocks_obs` property with respect to $o$.
Of course, this is something we need to prove and we do this in `DeterministicSkolemObsoleteness.blocks_each_obs` and `BlockingObsoleteness.blocks_corresponding_obs`, respectively.

## How to actually check if a trigger is blocked?

The definition of `BlockingObsoleteness` and also the proof of `BlockingObsoleteness.blocks_corresponding_obs` is awefully technical.
To check if a trigger is blocked, we backtrack where the functional terms involved in its mapped body come from.
We can do this, since each function symbol has a rule and disjunct id. Based on this information, we know which trigger must have been applied to make our target trigger loaded. At least *almost*.
The functional terms contain the mapped frontier, which we can use for reconstruction, but we do not know the mapping for the remaining body variables.
This could be anything. To not cause any interference there, we map them to fresh constants. While this is simply stated on paper, it is quite an effort to do formally. And there is yet another place where we require fresh constants. For reasons beyond what I want to discuss here, to check if a trigger is blocked, we first need to rename all of its constant occurrences apart, which again uses fresh constants.

If you actually aim to understand all the details, then good luck! There are a few doc comments on what happens in the individual files so you can dig into those a bit more. You can also have a look at the papers introducing the notions but this is likely still mind-boggling. Feel free to reach out to me at any point. I will try my best to explain and answer your questions!
-/

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- At some point we need to map constants from arbitrary chases to the ones in the special database. For this, we map all rule set constants to themselves and all others to the single `special_const`. -/
noncomputable def RuleSet.mfaConstantMapping (rs : RuleSet sig) (special_const : sig.C) : StrictConstantMapping sig :=
  fun c =>
    have : Decidable (c ∈ rs.constants) := Classical.propDecidable (c ∈ rs.constants)
    if (c ∈ rs.constants) then c else special_const

/-- Indeed the `mfaConstantMapping` is the id on all rule set constants. -/
theorem RuleSet.mfaConstantMapping_id_on_rs_constants (rs : RuleSet sig) (special_const : sig.C) : ∀ (c : sig.C), c ∈ rs.constants -> rs.mfaConstantMapping special_const c = c := by
  intro c c_mem
  simp [mfaConstantMapping, c_mem]

/-- The `mfaConstantMapping` is even the id on all rule atoms. (Constant mappings leave variables untouched.) -/
theorem RuleSet.mfaConstantMapping_id_on_atom_from_rule (rs : RuleSet sig) (special_const : sig.C) (r : Rule sig) (r_mem : r ∈ rs.rules) : ∀ a, a ∈ r.body ++ r.head.flatten -> (rs.mfaConstantMapping special_const).apply_function_free_atom a = a := by
  intro a a_mem
  apply TermMapping.apply_generalized_atom_eq_self_of_id_on_terms
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

/--
A `MfaObsoletenessCondition` is simply a `LaxObsoletenessCondition`, i.e. besides the actual condition it only has subset monotonicity as its only condition.
-/
structure MfaObsoletenessCondition (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] extends LaxObsoletenessCondition sig

instance {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] : Coe (MfaObsoletenessCondition sig) (LaxObsoletenessCondition sig) where
  coe obs := { cond := obs.cond, monotone := obs.monotone }

/--
Here we define what it means for a `MfaObsoletenessCondition` to block a `ObsoletenessCondition`.
Essentially, we say that if the mfa obsoleteness is fulfilled and the trigger is loaded, then also the real obsoleteness condition is fulfilled.
Before that, we filter trggers where already every head result occurs in in the mfa set of facts anyway.
This is safe to do since applying these again would not make a difference.
The necessesity for doing this comes from `DeterministicSkolemObsoleteness.blocks_obs`. `BlockingObsoleteness.blocks_obs` works without.
-/
def MfaObsoletenessCondition.blocks_obs (mfa_obs : MfaObsoletenessCondition sig) (obs : ObsoletenessCondition sig) (rs : RuleSet sig) (special_const : sig.C) : Prop :=
  ∀ {db : Database sig} (cb : ChaseBranch obs ⟨db, rs⟩) (node : cb.Node) (trg : RTrigger obs rs) (fs : FactSet sig),
  (∃ (i : Fin trg.val.mapped_head.length), ¬ ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact_set trg.val.mapped_head[i.val].toSet) ⊆ fs) ->
  (mfa_obs.cond { rule := trg.val.rule, subs := (rs.mfaConstantMapping special_const).toConstantMapping.apply_ground_term ∘ trg.val.subs } fs) ->
  trg.val.loaded node.val.facts -> obs.cond trg.val node.val.facts

/-- A trigger fulfills `DeterministicSkolemObsoleteness` if each of its derived heads is already in the fact set in question. Note that this captures the idea of replacing disjunctions with conjunctions, which is part of MFA. We do this nowhere explicitely, so disjunctions always remain in rules, but we implicitly treat them like conjunctions when necessary (like here). -/
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

/-- `DeterministicSkolemObsoleteness` has the `blocks_obs` property for each `ObsoletenessCondition`. -/
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
    rw [← TermMapping.apply_generalized_atom_compose']
    conv => left; unfold PreTrigger.apply_to_function_free_atom
    rw [← TermMapping.apply_generalized_atom_compose']
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
    | const c => simp [StrictConstantMapping.apply_var_or_const, PreTrigger.apply_to_var_or_const_for_const, ConstantMapping.apply_ground_term_constant, StrictConstantMapping.toConstantMapping]

/-- A trigger is blocked for its own backtracking if it is obsolete for its own backtracking. Note that the backtracking always requires us to prove that Skolem function terms are well-formed, which is what the additional conditions are for. -/
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

/-- A trigger fulfills `BlockingObsoleteness` if the trigger with renamed-apart constants is blocked for its own backtracking. Note that `BlockingObsoleteness` only depends on the trigger. The passed fact set is ignored. -/
def BlockingObsoleteness [GetFreshInhabitant sig.C] [Inhabited sig.C] (obs : ObsoletenessCondition sig) (rs : RuleSet sig) : MfaObsoletenessCondition sig := {
  cond := fun (trg : PreTrigger sig) _ =>
    ∀ (rl : RuleList sig), (∀ r, r ∈ rl.rules ↔ r ∈ rs.rules) ->
      let trg' := trg.rename_constants_apart (rl.rules.flatMap Rule.constants)
      let trg'' : Trigger obs := { rule := trg'.rule, subs := trg'.subs }
      trg''.blocked_for_backtracking rl
  monotone := by intro _ _ _ _ h; exact h -- trivial since the condition does not depend on the passed fact set
}

/-- `BlockingObsoleteness` has the `blocks_obs` condition for the `ObsoletenessCondition` it was defined for. -/
theorem BlockingObsoleteness.blocks_corresponding_obs [GetFreshInhabitant sig.C] [Inhabited sig.C]
    (obs : ObsoletenessCondition sig) (obs_propagates_under_const_mapping : obs.propagates_under_constant_mapping)
    (rs : RuleSet sig) (rs_finite : rs.rules.finite) (special_const : sig.C) :
    (BlockingObsoleteness obs rs).blocks_obs obs rs special_const := by
  intro db cb node trg _ _ blocked loaded
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

    rw [← obs.preserved_under_equiv (PreTrigger.equiv_of_strong_equiv reverse_renaming_mapping_properties.left)]
    rw [PreTrigger.backtrackFacts_eq_of_strong_equiv _ _ _ _ _ _ (PreTrigger.strong_equiv_symm reverse_renaming_mapping_properties.left)]

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

    rcases exists_fresh_constant_remapping_such_that_backtrackings_subsume_each_other with ⟨fresh_constant_remapping, fresh_constant_remapping_id, fresh_constant_remapping_subsumes, _⟩

    apply obs.monotone fresh_constant_remapping_subsumes

    have equiv : { rule := trg_with_constant_mapping_applied_but_not_renamed_apart.rule, subs := reverse_renaming_mapping.toConstantMapping.apply_ground_term ∘ (trg_with_constant_mapping_applied_but_not_renamed_apart.rename_constants_apart (rl.rules.flatMap Rule.constants)).subs : PreTrigger sig }.equiv { rule := trg_with_constant_mapping_applied_but_not_renamed_apart.rule, subs := (StrictConstantMapping.toConstantMapping (fun c => if c ∈ (PreTrigger.backtrackFacts rl (trg_with_constant_mapping_applied_but_not_renamed_apart.rename_constants_apart (rl.rules.flatMap Rule.constants)) (by apply PreTrigger.rename_constants_apart_preserves_ruleId_validity; apply PreTrigger.compose_strict_constant_mapping_preserves_ruleId_validity; exact trg_ruleIds_valid) (by apply PreTrigger.rename_constants_apart_preserves_disjIdx_validity; apply PreTrigger.compose_strict_constant_mapping_preserves_disjIdx_validity; exact trg_disjIdx_valid) (by apply PreTrigger.rename_constants_apart_preserves_rule_arity_validity; apply PreTrigger.compose_strict_constant_mapping_preserves_rule_arity_validity; exact trg_rule_arity_valid)).snd then fresh_constant_remapping c else reverse_renaming_mapping c)).apply_ground_term ∘ (trg_with_constant_mapping_applied_but_not_renamed_apart.rename_constants_apart (rl.rules.flatMap Rule.constants)).subs : PreTrigger sig } := by
      simp only [PreTrigger.equiv, true_and]
      intro v v_mem
      simp only [Function.comp_apply]
      apply ConstantMapping.apply_ground_term_congr_left
      intro d d_mem
      simp only [StrictConstantMapping.toConstantMapping, Function.comp_apply, PreTrigger.backtrackFacts]
      split
      case a.isFalse heq => rfl
      case a.isTrue heq =>
        apply False.elim
        apply GroundTerm.backtrackFacts_list_fresh_constants_not_forbidden d heq
        rw [List.mem_append]
        apply Or.inl
        rcases FunctionFreeConjunction.mem_vars.mp (Rule.frontier_subset_vars_body v_mem) with ⟨a, a_mem, v_mem⟩
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
      simp only [StrictConstantMapping.toConstantMapping, Function.comp_apply, GroundTerm.const, Subtype.mk.injEq, FiniteTree.leaf.injEq]
      rw [fresh_constant_remapping_id]
      . split
        case a.isTrue heq => rfl
        case a.isFalse heq =>
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

  specialize blocked (by apply cb.trigger_ruleIds_valid_of_loaded node.property rl rl_rs_eq; exact loaded)
  specialize blocked (by apply cb.trigger_disjIdx_valid_of_loaded node.property rl rl_rs_eq; exact loaded)
  specialize blocked (by apply cb.trigger_rule_arity_valid_of_loaded node.property rl rl_rs_eq; exact loaded)

  rcases cb.backtracking_of_loaded_trigger_in_node node.property rl rl_rs_eq trg.val loaded with ⟨g, g_h⟩

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
      apply Eq.symm
      apply ConstantMapping.apply_ground_term_eq_self_of_id_on_constants
      intro d d_mem
      rw [g_h.right]
      apply Or.inl
      rcases FunctionFreeConjunction.mem_vars.mp (Rule.frontier_subset_vars_body v_mem) with ⟨a, a_mem, v_mem'⟩
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

  apply obs.monotone _ blocked
  exact g_h.left

namespace KnowledgeBase

/-- This result is not necessary for MFA-like conditions but still interesting, also as a sanity check: The result of every deterministic Skolem `ChaseBranch` is the same as the `parallelDeterminizedChase_result`. -/
theorem parallelDeterminizedChase_result_eq_every_chase_branch_result
    (kb : KnowledgeBase sig) (det : kb.rules.isDeterministic) :
    ∀ (cb : ChaseBranch (SkolemObsoleteness sig) kb), cb.result =
      parallelDeterminizedChase_result kb (DeterministicSkolemObsoleteness sig) := by
  intro cb
  apply Set.ext
  intro f
  constructor
  . rintro ⟨node, node_mem, f_mem⟩
    revert f f_mem
    let node : cb.Node := ⟨node, node_mem⟩
    show ∀ f ∈ node.val.facts, f ∈ parallelDeterminizedChase_result kb (DeterministicSkolemObsoleteness sig)
    induction node using cb.toChaseDerivation.mem_rec with
    | head =>
      intro f f_mem
      simp only [cb.database_first'] at f_mem
      exists (parallelDeterminizedChase kb (DeterministicSkolemObsoleteness sig)).head
      simp only [parallelDeterminizedChase, InfiniteList.head_mem]
      simp [parallelDeterminizedDerivation_head, f_mem]
    | step cd suffix ih next next_mem =>
      intro f f_mem
      simp only [cd.facts_next next_mem] at f_mem
      cases f_mem with
      | inl f_mem => apply ih; exact f_mem
      | inr f_mem =>
        have : ∃ fs ∈ parallelDeterminizedChase kb (DeterministicSkolemObsoleteness sig), cd.head.facts ⊆ fs := by
          have prev_finite := cb.facts_finite_of_mem ⟨cd.head, (cd.mem_of_mem_suffix suffix _ cd.head_mem)⟩
          rcases prev_finite with ⟨prev_l, _, prev_l_eq⟩
          have : ∀ (l : List (Fact sig)), (∀ e, e ∈ l -> e ∈ cd.head.facts) -> ∃ fs ∈ (parallelDeterminizedChase kb (DeterministicSkolemObsoleteness sig)), (∀ e, e ∈ l -> e ∈ fs) := by
            intro l l_sub
            induction l with
            | nil =>
              exists (parallelDeterminizedChase kb (DeterministicSkolemObsoleteness sig)).head
              constructor
              . exact InfiniteList.head_mem
              . intro _; simp
            | cons hd tl ih_inner =>
              have from_ih := ih_inner (by intro e e_mem; apply l_sub; simp [e_mem])
              rcases from_ih with ⟨fs_from_ih, from_ih⟩

              have from_hd := ih hd
              specialize from_hd (by apply l_sub; simp)
              rcases from_hd with ⟨fs_from_hd, from_hd⟩

              cases (parallelDeterminizedDerivation_subset_total _ _ from_ih.left from_hd.left) with
              | inl sub =>
                exists fs_from_hd; constructor; exact from_hd.left
                intro f f_mem; rw [List.mem_cons] at f_mem; cases f_mem with
                | inl f_mem => rw [f_mem]; exact from_hd.right
                | inr f_mem => apply sub; apply from_ih.right; exact f_mem
              | inr sub =>
                exists fs_from_ih; constructor; exact from_ih.left
                intro f f_mem; rw [List.mem_cons] at f_mem; cases f_mem with
                | inl f_mem => rw [f_mem]; apply sub; exact from_hd.right
                | inr f_mem => apply from_ih.right; exact f_mem
          specialize this prev_l (by intro f; exact (prev_l_eq f).mp)
          rcases this with ⟨fs, this⟩
          exists fs; constructor
          . exact this.left
          . intro f
            rw [← prev_l_eq]
            exact this.right f

        rcases this with ⟨fs, fs_mem, head_sub_fs⟩
        exists parallelDeterminizedDerivation_step kb.rules (DeterministicSkolemObsoleteness sig) fs
        constructor
        . apply parallelDeterminizedDerivation_step_mem_of_mem; exact fs_mem
        -- TODO: would be Decidable if we define sets in the parallelDeterminizedChase to be finite
        cases Classical.em (f ∈ fs) with
        | inl mem => apply Or.inl; exact mem
        | inr not_mem =>
          apply Or.inr
          let origin := next.origin.get (cd.isSome_origin_next next_mem)
          exists ⟨{ rule := origin.fst.val.rule, subs := origin.fst.val.subs }, origin.fst.property⟩
          constructor
          . unfold Trigger.active
            constructor
            . unfold PreTrigger.loaded
              apply Set.subset_trans _ head_sub_fs
              exact (cd.active_trigger_origin_next next_mem).left
            . intro contra
              apply not_mem
              apply contra.right origin.snd
              exact f_mem
          . exists origin.snd
  . have goal : ∀ elem : (parallelDeterminizedChase kb (DeterministicSkolemObsoleteness sig)).Element, elem.val ⊆ cb.result := by
      intro elem
      induction elem using parallelDeterminizedDerivation_mem_rec with
      | head =>
        simp only [parallelDeterminizedDerivation_head]
        apply Set.subset_trans _ (ChaseDerivationSkeleton.facts_node_subset_result _ cb.head_mem)
        rw [cb.database_first']
        apply Set.subset_refl
      | step _ ih =>
        intro f f_mem; cases f_mem with
        | inl f_mem => exact ih _ f_mem
        | inr f_mem =>
          rcases f_mem with ⟨trg, trg_active, f_mem⟩

          have trg_loaded_somewhere : ∃ node ∈ cb.toChaseDerivation, trg.val.loaded node.facts := by
            have : ∀ (l : List (Fact sig)), l ⊆ trg.val.mapped_body -> ∃ node ∈ cb.toChaseDerivation, (∀ e, e ∈ l -> e ∈ node.facts) := by
              intro l l_sub
              induction l with
              | nil => exists cb.head; constructor; exact cb.head_mem; simp
              | cons hd tl ih_inner =>
                have from_ih := ih_inner (by intro f f_mem; apply l_sub; simp [f_mem])
                rcases from_ih with ⟨n_from_ih, n_from_ih_mem, from_ih⟩

                have from_hd := ih hd (by apply trg_active.left; rw [List.mem_toSet]; apply l_sub; simp)
                rcases from_hd with ⟨n_from_hd, n_from_hd_mem, from_hd⟩

                cases cb.predecessor_total ⟨n_from_ih, n_from_ih_mem⟩ ⟨n_from_hd, n_from_hd_mem⟩ with
                | inl prec =>
                  exists n_from_hd; constructor; exact n_from_hd_mem
                  intro f f_mem; rw [List.mem_cons] at f_mem; cases f_mem with
                  | inl f_mem => rw [f_mem]; exact from_hd
                  | inr f_mem =>
                    apply cb.facts_node_subset_of_prec prec
                    apply from_ih; exact f_mem
                | inr prec =>
                  exists n_from_ih; simp only [n_from_ih_mem, true_and]
                  intro f f_mem; rw [List.mem_cons] at f_mem; cases f_mem with
                  | inr f_mem => apply from_ih; exact f_mem
                  | inl f_mem =>
                    apply cb.facts_node_subset_of_prec prec
                    rw [f_mem]; exact from_hd

            specialize this trg.val.mapped_body (by simp)
            rcases this with ⟨n, this⟩
            exists n
          rcases trg_loaded_somewhere with ⟨node, node_mem, trg_loaded⟩

          have fair := cb.fairness_prec ⟨{ rule := trg.val.rule, subs:= trg.val.subs }, trg.property⟩
          rcases fair with ⟨fairness_node, fair⟩

          rcases f_mem with ⟨i, f_mem⟩
          have i_zero : i.val = 0 := by
            have isLt := i.isLt
            simp only [PreTrigger.length_mapped_head] at isLt
            specialize det _ trg.property
            unfold Rule.isDeterministic at det
            rw [decide_eq_true_iff] at det
            rw [det, Nat.lt_one_iff] at isLt
            exact isLt
          simp only [i_zero] at f_mem

          cases cb.predecessor_total ⟨node, node_mem⟩ fairness_node with
          | inl prec =>
            exists fairness_node.val; constructor; exact fairness_node.property
            specialize fair fairness_node cb.predecessor_refl
            unfold Trigger.active at fair
            simp only [not_and, Classical.not_not] at fair
            have trg_loaded : trg.val.loaded fairness_node.val.facts := by
              intro f f_mem
              apply cb.facts_node_subset_of_prec prec
              apply trg_loaded
              exact f_mem
            specialize fair trg_loaded
            rcases fair with ⟨disj_index, fair⟩
            apply fair
            have disj_index_zero : disj_index.val = 0 := by
              have isLt := disj_index.isLt
              simp only [PreTrigger.length_mapped_head] at isLt
              specialize det _ trg.property
              unfold Rule.isDeterministic at det
              rw [decide_eq_true_iff] at det
              rw [det, Nat.lt_one_iff] at isLt
              exact isLt
            simp only [List.mem_toSet, disj_index_zero]
            exact f_mem
          | inr prec =>
            exists node; constructor; exact node_mem
            specialize fair ⟨node, node_mem⟩ prec
            unfold Trigger.active at fair
            simp only [not_and, Classical.not_not] at fair
            specialize fair trg_loaded
            rcases fair with ⟨disj_index, fair⟩
            apply fair
            have disj_index_zero : disj_index.val = 0 := by
              have isLt := disj_index.isLt
              simp only [PreTrigger.length_mapped_head] at isLt
              specialize det _ trg.property
              unfold Rule.isDeterministic at det
              rw [decide_eq_true_iff] at det
              rw [det, Nat.lt_one_iff] at isLt
              exact isLt
            simp only [List.mem_toSet, disj_index_zero]
            exact f_mem
    rintro ⟨fs, fs_mem, h⟩
    apply goal ⟨fs, fs_mem⟩
    exact h

end KnowledgeBase

namespace RuleSet

/-- The MFA-like conditions all start on a special database, called the "critical instance". We define this here. It consists of all facts that can be build from predicates in the rule set and constants from the ruleset plus a "special constant". Intuitively, this generalizes all possible databases. -/
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

/-- The `KnowledgeBase` for the MFA-like checks consists of the rule set in question and the `criticalInstance`. -/
def mfaKb (rs : RuleSet sig) (finite : rs.rules.finite) (special_const : sig.C) : KnowledgeBase sig := {
  rules := rs
  db := criticalInstance rs finite special_const
}

/-- Constants in the `mfaKb` are either the special constants or they come from the rule set. -/
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

/-- The fact set computed in the MFA-like checks is the parallel determinized chase result (defined in a separete file) for the `mfaKb`. -/
def mfaSet (rs : RuleSet sig) (finite : rs.rules.finite) (special_const : sig.C) (obs : MfaObsoletenessCondition sig) : FactSet sig :=
  parallelDeterminizedChase_result (rs.mfaKb finite special_const) obs

/-- We can map every possible `ChaseBranch` into the `mfaSet` by replacing all (non-ruleset) constants by the special constant. At least this is the intuition for this behemoth of a theorem statement. -/
theorem mfaSet_contains_every_chase_step_for_every_kb_except_for_facts_with_predicates_not_from_rs
    (rs : RuleSet sig) (finite : rs.rules.finite)
    (special_const : sig.C) (mfa_obs : MfaObsoletenessCondition sig) :
    ∀ {db : Database sig} {obs : ObsoletenessCondition sig}, (mfa_obs.blocks_obs obs rs special_const) ->
    ∀ (cb : ChaseBranch obs { rules := rs, db := db }) (node : cb.Node),
    ∀ f, f.predicate ∈ rs.predicates -> f ∈ node.val.facts ->
      ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact f) ∈ (rs.mfaSet finite special_const mfa_obs) := by
  intro db obs blocks cb node
  induction node using cb.mem_rec with
  | head =>
    intro f f_predicate f_mem
    simp only [cb.database_first'] at f_mem
    exists (parallelDeterminizedChase (rs.mfaKb finite special_const) mfa_obs).head
    simp only [parallelDeterminizedChase, InfiniteList.head_mem, true_and]
    rw [parallelDeterminizedDerivation_head]

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
  | step cd suffix ih next next_mem =>
    intro f f_predicate f_mem
    simp only [cd.facts_next next_mem] at f_mem
    cases f_mem with
    | inl f_mem =>
      apply ih
      . exact f_predicate
      . exact f_mem
    | inr f_mem =>
      have : ∃ fs ∈ (parallelDeterminizedChase (rs.mfaKb finite special_const) mfa_obs), ∀ f, f.predicate ∈ rs.predicates -> f ∈ cd.head.facts -> ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact f) ∈ fs := by
        let kb := rs.mfaKb finite special_const
        let prev_filtered : FactSet sig := fun f => f.predicate ∈ rs.predicates ∧ f ∈ cd.head.facts
        have prev_finite : prev_filtered.finite := by
          rcases cb.facts_finite_of_mem ⟨cd.head, (cd.mem_of_mem_suffix suffix _ cd.head_mem)⟩ with ⟨prev_l, _, prev_l_eq⟩
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

        have : ∀ (l : List (Fact sig)), (∀ e, e ∈ l -> e.predicate ∈ rs.predicates ∧ e ∈ cd.head.facts) -> ∃ fs ∈ (parallelDeterminizedChase kb mfa_obs), (∀ e, e ∈ l -> ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact e) ∈ fs) := by
          intro l l_sub
          induction l with
          | nil =>
            exists (parallelDeterminizedChase kb mfa_obs).head
            constructor
            . exact InfiniteList.head_mem
            . intro _; simp
          | cons hd tl ih_inner =>
            have from_ih := ih_inner (by intro e e_mem; apply l_sub; simp [e_mem])
            rcases from_ih with ⟨fs_from_ih, from_ih⟩

            have from_hd := ih hd (l_sub hd (by simp)).left (l_sub hd (by simp)).right
            rcases from_hd with ⟨fs_from_hd, from_hd⟩

            cases (parallelDeterminizedDerivation_subset_total _ _ from_ih.left from_hd.left) with
            | inl sub =>
              exists fs_from_hd; constructor; exact from_hd.left
              intro f f_mem; rw [List.mem_cons] at f_mem; cases f_mem with
              | inl f_mem => rw [f_mem]; exact from_hd.right
              | inr f_mem => apply sub; apply from_ih.right; exact f_mem
            | inr sub =>
              exists fs_from_ih; constructor; exact from_ih.left
              intro f f_mem; rw [List.mem_cons] at f_mem; cases f_mem with
              | inl f_mem => rw [f_mem]; apply sub; exact from_hd.right
              | inr f_mem => apply from_ih.right; exact f_mem

        specialize this prev_l (by
          intro f f_mem
          rw [prev_l_eq] at f_mem
          unfold prev_filtered at f_mem
          exact f_mem
        )

        rcases this with ⟨fs, fs_mem, this⟩
        exists fs; constructor; exact fs_mem
        intro f f_pred f_mem
        specialize this f (by
          rw [prev_l_eq]
          unfold prev_filtered
          constructor
          . exact f_pred
          . exact f_mem
        )
        exact this

      rcases this with ⟨fs, fs_mem, prev_node_subs_parallel_chase⟩
      exists parallelDeterminizedDerivation_step rs mfa_obs fs
      constructor
      . apply parallelDeterminizedDerivation_step_mem_of_mem; exact fs_mem
      simp only [parallelDeterminizedDerivation_step, instUnionSet, instMembershipSet]
      rw [Classical.or_iff_not_imp_left]
      intro f_not_in_prev

      let origin := next.origin.get (cd.isSome_origin_next next_mem)
      let trg := origin.fst
      let disj_index := origin.snd

      let adjusted_trg : RTrigger mfa_obs (rs.mfaKb finite special_const).rules := ⟨⟨trg.val.rule, (rs.mfaConstantMapping special_const).toConstantMapping.apply_ground_term ∘ trg.val.subs⟩, trg.property⟩

      exists adjusted_trg
      constructor
      . constructor
        . apply Set.subset_trans (b := fun f => f.predicate ∈ rs.predicates ∧ f ∈ ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact_set cd.head.facts))
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
              . apply (cd.active_trigger_origin_next next_mem).left
                rw [List.mem_toSet]
                simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list, List.mem_map]
                exists a
              . rw [← f_eq]
                rw [← TermMapping.apply_generalized_atom_compose']
                apply TermMapping.apply_generalized_atom_congr_left
                intro voc voc_mem
                cases voc with
                | var v => rfl
                | const c =>
                  simp only [Function.comp_apply, GroundSubstitution.apply_var_or_const, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, StrictConstantMapping.toConstantMapping, GroundTerm.const]
                  apply Subtype.ext
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
          have contra := blocks cb ⟨cd.head, cd.mem_of_mem_suffix suffix _ cd.head_mem⟩ trg _ (by
            exists disj_index
            intro contra
            apply f_not_in_prev
            apply contra
            apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
            exact f_mem
          ) contra
          specialize contra (cd.active_trigger_origin_next next_mem).left
          apply (cd.active_trigger_origin_next next_mem).right
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
            simp only [StrictConstantMapping.toConstantMapping, Function.comp_apply]
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

/-- We can extend the result above to the whole result of the `ChaseBranch`. -/
theorem filtered_cb_result_subset_mfaSet (rs : RuleSet sig) (finite : rs.rules.finite) (special_const : sig.C) (mfa_obs : MfaObsoletenessCondition sig) :
    ∀ {db : Database sig} {obs : ObsoletenessCondition sig}, (mfa_obs.blocks_obs obs rs special_const) ->
    ∀ (cb : ChaseBranch obs { rules := rs, db := db }), ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact_set (fun f => f.predicate ∈ rs.predicates ∧ f ∈ cb.result)) ⊆ (rs.mfaSet finite special_const mfa_obs) := by
  intro db obs blocks cb f f_mem

  rcases f_mem with ⟨f', f'_mem, f_eq⟩
  rcases f'_mem with ⟨f'_pred, f'_mem⟩
  rcases f'_mem with ⟨node, node_mem, f'_mem⟩
  rw [f_eq]

  have := rs.mfaSet_contains_every_chase_step_for_every_kb_except_for_facts_with_predicates_not_from_rs finite special_const mfa_obs blocks cb ⟨node, node_mem⟩
  apply this
  . exact f'_pred
  . exact f'_mem

/-- If the `mfaSet` is finite, then the rule set terminates. The argument is that if the `mfaSet` is finite and every `ChaseBranch` can be embedded into this set, then each of these `ChaseBranch`es also needs to be finite. This is still a bit involved since we need to show that only finitely many terms can collapse to the same on in the `mfaSet`. -/
theorem terminates_of_mfaSet_finite [Inhabited sig.C] (rs : RuleSet sig) (rs_finite : rs.rules.finite) (mfa_obs : MfaObsoletenessCondition sig) :
    ∀ {obs : ObsoletenessCondition sig}, (mfa_obs.blocks_obs obs rs Inhabited.default) -> (rs.mfaSet rs_finite Inhabited.default mfa_obs).finite -> rs.terminates obs := by
  intro obs blocks mfa_finite
  unfold RuleSet.terminates
  intro db
  unfold KnowledgeBase.terminates
  intro ct
  rw [ChaseTree.terminates_iff_result_finite]
  rintro result ⟨cb, cb_mem, result_eq⟩
  let cb := ct.chaseBranch_for_branch cb_mem

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
    . rcases f_mem.right with ⟨node, node_mem, f_mem⟩
      intro c c_mem
      rw [List.mem_append]
      cases ChaseBranch.constants_node_subset_constants_db_union_constants_rules (node := ⟨node, node_mem⟩) c (by exists f) with
      | inl this => apply Or.inl; rw [l_db_c_eq]; exact this
      | inr this => apply Or.inr; rw [l_rs_c_eq]; exact this
    . apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
      exact f_mem

  have res_sub_db_and_filtered : cb.result ⊆ db.toFactSet.val ∪ res_filtered := by
    have each_step_sub_db_and_filtered : ∀ node : cb.Node, node.val.facts ⊆ db.toFactSet.val ∪ res_filtered := by
      intro node
      induction node using cb.mem_rec with
      | head => simp only [cb.database_first']; intro f f_mem; apply Or.inl; exact f_mem
      | step cd suffix ih next next_mem =>
        simp only [cd.facts_next next_mem]
        intro f f_mem
        cases f_mem with
        | inl f_mem => apply ih; exact f_mem
        | inr f_mem =>
          apply Or.inr
          constructor
          . -- since f occur in the trigger result, its predicate occurs in the rule and must therefore occur in the ruleset
            let origin := next.origin.get (cd.isSome_origin_next next_mem)
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
          . exists next; constructor
            . exact cd.mem_of_mem_suffix suffix _ (cd.next_mem_of_mem _ next_mem)
            . rw [cd.facts_next next_mem]; apply Or.inr; exact f_mem

    intro f f_mem
    rcases f_mem with ⟨node, node_mem, f_mem⟩
    specialize each_step_sub_db_and_filtered ⟨node, node_mem⟩
    apply each_step_sub_db_and_filtered
    exact f_mem

  rw [result_eq]
  apply Set.finite_of_subset_finite _ res_sub_db_and_filtered
  apply Set.union_finite_of_both_finite
  . exact db.toFactSet.property.left
  . exact res_filtered_finite

/-- A rule set `isMfa` if its `mfsSet` does not contain a cyclic term. -/
def isMfa [Inhabited sig.C] (rs : RuleSet sig) (finite : rs.rules.finite) (mfa_obs : MfaObsoletenessCondition sig) : Prop :=
  ∀ t, t ∈ (rs.mfaSet finite default mfa_obs).terms -> ¬ PreGroundTerm.cyclic t.val

/-- A rule set terminates if it `isMfa`. What mainly remains to be shown here is that only finitely many terms are non-cyclic. -/
theorem terminates_of_isMfa [Inhabited sig.C] (rs : RuleSet sig) (rs_finite : rs.rules.finite) (mfa_obs : MfaObsoletenessCondition sig) :
    ∀ {obs : ObsoletenessCondition sig}, (mfa_obs.blocks_obs obs rs Inhabited.default) -> rs.isMfa rs_finite mfa_obs -> rs.terminates obs := by
  intro obs blocks isMfa
  apply rs.terminates_of_mfaSet_finite rs_finite mfa_obs blocks
  apply FactSet.finite_of_preds_finite_of_terms_finite
  . apply Set.finite_of_subset_finite _ parallelDeterminizedDerivation_result_predicates
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

      apply parallelDeterminizedChase_result_functions (kb := rs.mfaKb rs_finite default)
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

      have := parallelDeterminizedChase_result_constants (kb := rs.mfaKb rs_finite default) (obs := mfa_obs)
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

/-- MFA correctness - If a rule set is MFA (`isMfa` with `DeterministicSkolemObsoleteness`), then it terminates. -/
theorem terminates_of_isMfa_with_DeterministicSkolemObsoleteness [Inhabited sig.C] (rs : RuleSet sig) (rs_finite : rs.rules.finite) :
    rs.isMfa rs_finite (DeterministicSkolemObsoleteness sig) -> ∀ obs, rs.terminates obs := by
  intro isMfa obs
  apply rs.terminates_of_isMfa rs_finite (DeterministicSkolemObsoleteness sig) (DeterministicSkolemObsoleteness.blocks_each_obs obs default rs)
  exact isMfa

/-- DMFA/RMFA correctness - If a rule set is DMFA/RMFA or anything in between (`isMfa` with `BlockingObsoleteness`), then it terminates for the respective `ObsoletenessCondition`. -/
theorem terminates_of_isMfa_with_BlockingObsoleteness [GetFreshInhabitant sig.C] [Inhabited sig.C] (rs : RuleSet sig) (rs_finite : rs.rules.finite) (obs : ObsoletenessCondition sig) (obs_propagates_under_const_mapping : obs.propagates_under_constant_mapping) :
    rs.isMfa rs_finite (BlockingObsoleteness obs rs) -> rs.terminates obs :=
  rs.terminates_of_isMfa rs_finite (BlockingObsoleteness obs rs) (BlockingObsoleteness.blocks_corresponding_obs obs obs_propagates_under_const_mapping rs rs_finite default)

end RuleSet

