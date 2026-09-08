/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.Nontermination.HeadChoice

/-!
# Unblockability

Here we define what it means for a trigger to be unblockable and we also introduce overapproximations that can be used to witness unblockability.

THIS IS VERY MUCH WORK IN PROGRESS!
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-!
## Another Condition for Obsolescence

For RPC-like conditions we require another property of `ObsolescenceCondition` conditions that does not hold for the general definition.
The condition shall be stable across certain `GroundTermMapping`s that at least map the head constants to themselves. But this only needs to be true of no fresh term of the trigger already occurs, which, in the context of a chase, means that the trigger itself has not been applied before.
The reason for excluding this case is a bit technical. Bottom line, we do this as otherwise the property would simply not hold for `SkolemObsolescence`.
But if a trigger is only obsolete according to `SkolemObsolescence` because it was already applied, then we do not really care. The interesting case is that
a trigger is obsolete because a disjunct without existentials is already present.

Anyway, at the end you probably don't need to care much about the condition. It is enough to show the desired theorems and as a sanity check,
we also prove that it holds for both `SkolemObsolescence` and `RestrictedObsolescence` as intended.
-/

@[expose]
def ObsolescenceCondition.propagates_under_term_mapping_of_no_fresh_term_occurs (obs : ObsolescenceCondition sig) : Prop := ∀ {trg : PreTrigger sig} {fs : FactSet sig} {h : GroundTermMapping sig}, (∀ i lt t, t ∈ trg.fresh_terms_for_head_disjunct i lt -> t ∉ fs.terms) -> (∀ c ∈ trg.rule.head_constants, h (.const c) = .const c) -> obs.cond trg fs -> obs.cond (trg.extend_with_groundTermMapping h) (h.applyFactSet fs)

theorem SkolemObsolescence.propagates_under_term_mapping_of_no_fresh_term_occurs :
    (SkolemObsolescence sig).propagates_under_term_mapping_of_no_fresh_term_occurs := by
  intro trg fs h no_fresh_term_occurs id_const cond
  simp only [SkolemObsolescence] at cond
  simp only [SkolemObsolescence]
  rcases cond with ⟨i, lt, cond⟩
  exists i, lt
  intro f f_mem
  suffices f ∈ h.applyFactSet (trg.mapped_head[i]'(by grind)).toSet by
    apply TermMapping.apply_generalized_atom_set_subset_of_subset
    . exact cond
    . exact this
  rw [List.mem_toSet] at f_mem
  unfold PreTrigger.mapped_head at f_mem
  simp only [List.getElem_map, List.getElem_attach, List.getElem_zipIdx, List.mem_map, Nat.zero_add] at f_mem
  rcases f_mem with ⟨a, a_mem, f_eq⟩
  rw [TermMapping.mem_apply_generalized_atom_set]
  exists trg.apply_to_function_free_atom i lt a; constructor
  . rw [List.mem_toSet]; simp only [PreTrigger.mapped_head, List.getElem_map, List.getElem_attach, List.getElem_zipIdx, Nat.zero_add, List.mem_map]; exists a
  . rw [← f_eq, GeneralizedAtom.mk.injEq]
    simp only [PreTrigger.apply_to_function_free_atom, TermMapping.apply_generalized_atom, true_and]
    rw [List.map_map, List.map_inj_left]
    intro voc voc_mem; rw [Function.comp_apply]
    cases voc with
    | const c =>
      rw [PreTrigger.apply_to_var_or_const_for_const]
      rw [PreTrigger.apply_to_var_or_const_for_const]
      apply Eq.symm; apply id_const
      simp only [Rule.head_constants, List.mem_flatMap]; exists trg.rule.head[i]; constructor; exact List.getElem_mem _
      rw [FunctionFreeConjunction.mem_consts]; exists a
    | var v =>
      suffices v ∉ trg.rule.existential_vars_for_head_disjunct i lt by
        rw [PreTrigger.apply_to_var_or_const_of_not_mem_existential_vars trg _ _ _ this]
        rw [PreTrigger.apply_to_var_or_const_of_not_mem_existential_vars (trg.extend_with_groundTermMapping h) _ _ _ this]
        simp [PreTrigger.extend_with_groundTermMapping]
      intro contra; apply no_fresh_term_occurs i lt (trg.functional_term_for_var i lt v contra)
      . apply trg.mem_fresh_terms_of_functional_for_exis_var
      . exists trg.apply_to_function_free_atom i lt a; constructor
        . apply cond; rw [List.mem_toSet]; simp only [PreTrigger.mapped_head, List.getElem_map, List.getElem_attach, List.getElem_zipIdx, Nat.zero_add, List.mem_map]; exists a
        . simp only [PreTrigger.apply_to_function_free_atom, TermMapping.apply_generalized_atom]
          rw [List.mem_map]; exists .var v; constructor; exact voc_mem
          rw [trg.apply_to_var_or_const_of_mem_existential_vars _ _ _ contra]

theorem RestrictedObsolescence.propagates_under_term_mapping_of_no_fresh_term_occurs :
    (RestrictedObsolescence sig).propagates_under_term_mapping_of_no_fresh_term_occurs := by
  intro trg fs h _ id_const cond -- no_fresh_term_occurs is only needed for SkolemObsolescence
  simp only [RestrictedObsolescence, PreTrigger.satisfied, PreTrigger.satisfied_for_disj] at cond
  simp only [RestrictedObsolescence, PreTrigger.satisfied, PreTrigger.satisfied_for_disj]
  rcases cond with ⟨i, lt, cond⟩
  exists i, lt
  rcases cond with ⟨s, id_front, cond⟩
  exists h ∘ s;
  constructor
  . intro v v_mem; simp only [Function.comp_apply]; rw [id_front v v_mem]; rfl
  . rw [GroundSubstitution.apply_function_free_conj_compose]
    . rw [← TermMapping.apply_generalized_atom_set_toSet]
      apply TermMapping.apply_generalized_atom_set_subset_of_subset
      exact cond
    . intro d d_mem; apply id_const
      simp only [Rule.head_constants, List.mem_flatMap]; exists trg.rule.head[i]; constructor; exact List.getElem_mem _; exact d_mem


/-!
## Unblockability and Overapproximations

We now start to define what it means for a trigger to be unblockable. Also we define the notion of Overapproximation that gives us a way
of detecting unblockability. Specific such overapproximations will follow later.
-/

variable {obs : ObsolescenceCondition sig}

/-- A trigger is unblockable for a given `HeadChoice` if, for every derivation, when the trigger is loaded in a node of the branch indicated by the `HeacChoice`, then the `HeadChoice` result of the trigger also occurs in that branch. In the introducing paper this is called g-unblockable. -/
@[expose]
def Trigger.unblockable
    (rules : RuleSet sig)
    (hc : HeadChoice sig)
    (trg : Trigger obs.toLaxObsolescenceCondition) : Prop :=
  ∀ kb : KnowledgeBase sig, kb.rules = rules ->
  ∀ ct : RegularChaseTree obs kb, ∀ node : (ct.subderivation_for_headChoice hc).Node, trg.loaded node.val.facts ->
  ∃ node2 : (ct.subderivation_for_headChoice hc).Node, node ≼ node2 ∧
  (trg.output_for_headChoice hc).toSet ⊆ node2.val.facts

/-- Every deterministic Datalog trigger is unblockable. -/
theorem Trigger.unblockable_of_isDatalog_of_isDeterministic {rules : RuleSet sig} {hc : HeadChoice sig} {trg : RTrigger obs rules}
    (isDatalog : trg.val.rule.isDatalog)
    (isDet : trg.val.rule.isDeterministic) :
    trg.val.unblockable rules hc := by
  intro kb rules_eq ct node loaded
  let trg_kb : RTrigger obs kb.rules := ⟨trg.val, by rw [rules_eq]; exact trg.property⟩
  suffices ∃ node2, node ≼ node2 ∧ ¬ trg.val.active node2.val.facts by
    rcases this with ⟨node2, prec, not_active⟩
    exists node2, prec
    unfold Trigger.active at not_active; rw [not_and, Classical.not_not] at not_active
    specialize not_active (Set.subset_trans loaded (RegularChaseDerivationSkeleton.facts_node_subset_of_prec prec))
    rcases obs.cond_implies_contained_of_isDatalog isDatalog not_active with ⟨i, lt, contained⟩
    suffices (hc trg.val).val = i by unfold PreTrigger.output_for_headChoice; simp only [this]; exact contained
    have isLt := (hc trg.val).isLt
    simp only [Rule.isDeterministic, decide_eq_true_iff] at isDet
    simp only [isDet, Nat.lt_one_iff] at isLt
    simp only [isDet, Nat.lt_one_iff] at lt
    rw [isLt, lt]
  rcases RegularChaseDerivation.fairness_prec (cd := (ct.subderivation_for_headChoice hc).toChaseDerivation) trg_kb with ⟨fairness_node, fair⟩
  cases ChaseDerivationSkeleton.predecessor_total node fairness_node with
  | inl prec => exists fairness_node; constructor; exact prec; apply fair; grind
  | inr prec => exists node; constructor; grind; apply fair; exact prec

/-- This is Definition 7 from the [RPC] paper. -/
def FactSet.is_rpc_overapproximation
    (rules : RuleSet sig)
    (hc : HeadChoice sig)
    (trg : Trigger obs.toLaxObsolescenceCondition)
    (fs : FactSet sig) : Prop :=
  ∃ h : GroundTermMapping sig, (∀ c ∈ trg.rule.head_constants, h (.const c) = .const c) ∧ (∀ t ∈ trg.mapped_frontier, h t = t) ∧
    ∀ kb : KnowledgeBase sig, kb.rules = rules ->
    ∀ ct : RegularChaseTree obs kb, ∀ node ∈ (ct.subderivation_for_headChoice hc).toChaseDerivation,
      (¬ (trg.output_for_headChoice hc).toSet ⊆ node.facts) -> h.applyFactSet node.facts ⊆ fs

/-- This is Lemma 1 from the [RPC] paper. -/
theorem RTrigger.unblockable_of_not_obsolete_for_overapproximation
    (obs_propagates : obs.propagates_under_term_mapping_of_no_fresh_term_occurs)
    {rules : RuleSet sig} {hc : HeadChoice sig}
    (hc_consistent : hc.consistent_for_equivalent_triggers)
    {trg : RTrigger obs rules} {fs : FactSet sig} :
    fs.is_rpc_overapproximation rules hc trg.val -> ¬ obs.cond trg.val fs -> trg.val.unblockable rules hc := by
  intro ⟨h, id_head_consts, id_frontier, overapprox⟩ not_obs
  intro kb rules_eq ct node loaded
  let trg_kb : RTrigger obs kb.rules := ⟨trg.val, by rw [rules_eq]; exact trg.property⟩
  suffices ∃ node2, node ≼ node2 ∧ ¬ trg.val.active node2.val.facts by
    rcases this with ⟨node2, prec, not_active⟩
    exists node2; constructor; exact prec
    apply Classical.byContradiction
    intro contra
    apply not_active; constructor; exact Set.subset_trans loaded (RegularChaseDerivationSkeleton.facts_node_subset_of_prec prec)
    intro is_obs; apply not_obs
    suffices obs.cond trg.val (h.applyFactSet node2.val.facts) by
      apply LaxObsolescenceCondition.monotone _ _ this
      apply overapprox _ rules_eq _ _ node2.property
      exact contra
    apply (obs.preserved_under_equiv _).mp (obs_propagates _ _ is_obs)
    . apply PreTrigger.equiv_of_rule_eq_of_mapped_frontier_equiv; rfl
      rw [← PreTrigger.apply_mapping_after_mapped_frontier]
      apply List.map_id_of_id_on_all_mem; exact id_frontier
    . intro i lt t t_fresh t_mem_node2; apply contra
      rcases RegularChaseBranch.trigger_introducing_functional_term_occurs_in_chase node2 t_mem_node2 (trg := trg_kb) t_fresh with ⟨node3, node3_prec, orig, orig_mem, equiv, headIdx_eq⟩
      apply Set.subset_trans _ (RegularChaseDerivationSkeleton.facts_node_subset_of_prec node3_prec)
      rw [← PreTrigger.output_for_headChoice_eq_of_equiv hc_consistent equiv]; simp only [PreTrigger.output_for_headChoice]
      suffices RegularChaseNode.regularChaseNodeInstance.adheres_to_headChoice node3.val hc by
        simp only [← this orig orig_mem]
        exact node3.val.facts_contain_origin_result orig orig_mem
      apply ct.subderivation_for_headChoice_adheres_to_headChoice
      exact node3.property
    . exact id_head_consts
  rcases RegularChaseDerivation.fairness_prec (cd := (ct.subderivation_for_headChoice hc).toChaseDerivation) trg_kb with ⟨fairness_node, fair⟩
  cases ChaseDerivationSkeleton.predecessor_total node fairness_node with
  | inl prec => exists fairness_node; constructor; exact prec; apply fair; grind
  | inr prec => exists node; constructor; grind; apply fair; exact prec

