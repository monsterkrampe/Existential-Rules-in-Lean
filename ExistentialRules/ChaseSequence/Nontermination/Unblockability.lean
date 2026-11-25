/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

import ExistentialRules.ChaseSequence.CriticalInstance
public import ExistentialRules.ChaseSequence.HeadChoice

open CustomBasicDatastructures

/-!
# Unblockability

Here we define what it means for a trigger to be unblockable and we also introduce overapproximations that can be used to witness unblockability.

THIS IS VERY MUCH WORK IN PROGRESS!
-/

public section


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
def ObsolescenceCondition.propagates_under_term_mapping_of_no_fresh_term_occurs (obs : ObsolescenceCondition) : Prop := ∀ {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P] {trg : PreTrigger sig} {fs : FactSet sig} {h : GroundTermMapping sig}, (∀ i lt t, t ∈ trg.fresh_terms_for_head_disjunct i lt -> t ∉ fs.terms) -> (∀ c ∈ trg.rule.head_constants, h (.const c) = .const c) -> obs.cond trg fs -> obs.cond (trg.extend_with_groundTermMapping h) (h.applyFactSet fs)

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

theorem SkolemObsolescence.propagates_under_term_mapping_of_no_fresh_term_occurs :
    SkolemObsolescence.propagates_under_term_mapping_of_no_fresh_term_occurs := by
  intro sig _ _ _ trg fs h no_fresh_term_occurs id_const cond
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
    RestrictedObsolescence.propagates_under_term_mapping_of_no_fresh_term_occurs := by
  intro sig _ _ _ trg fs h _ id_const cond -- no_fresh_term_occurs is only needed for SkolemObsolescence
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

variable {obs : ObsolescenceCondition}

/-- A trigger is `kbUnblockable` for a given `KnowledgeBase` and `HeadChoice` if, for every derivation, when the trigger is loaded in a node of the branch indicated by the `HeadChoice`, then the `HeadChoice` result of the trigger also occurs in that branch. In the introducing paper this is called g-unblockable. -/
@[expose]
def Trigger.kbUnblockable
    (kb : KnowledgeBase sig)
    (hc : HeadChoice sig)
    (trg : Trigger sig obs.toLaxObsolescenceCondition) : Prop :=
  ∀ ct : RegularChaseTree obs kb, ∀ node : (ct.subderivation_for_headChoice hc).Node, trg.loaded node.val.facts ->
  ∃ node2 : (ct.subderivation_for_headChoice hc).Node, node ≼ node2 ∧
  (trg.output_for_headChoice hc).toSet ⊆ node2.val.facts

/-- A trigger is `rsUnblockable` for a given `RuleSet` if it is `kbUnblockable` for every `KnowledgeBase` with the rule set in question. -/
@[expose]
def Trigger.rsUnblockable
    (rules : RuleSet sig)
    (hc : HeadChoice sig)
    (trg : Trigger sig obs.toLaxObsolescenceCondition) : Prop :=
  ∀ kb : KnowledgeBase sig, kb.rules = rules -> trg.kbUnblockable kb hc

/-- Every deterministic Datalog trigger is `rsUnblockable`. -/
theorem Trigger.rsUnblockable_of_isDatalog_of_isDeterministic {rules : RuleSet sig} {hc : HeadChoice sig} {trg : RTrigger obs rules}
    (isDatalog : trg.val.rule.isDatalog)
    (isDet : trg.val.rule.isDeterministic) :
    trg.val.rsUnblockable rules hc := by
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
    (trg : Trigger sig obs.toLaxObsolescenceCondition)
    (fs : FactSet sig) : Prop :=
  ∃ h : GroundTermMapping sig, (∀ c ∈ trg.rule.head_constants, h (.const c) = .const c) ∧ (∀ t ∈ trg.mapped_frontier, h t = t) ∧
    ∀ kb : KnowledgeBase sig, kb.rules = rules ->
    ∀ ct : RegularChaseTree obs kb, ∀ node ∈ (ct.subderivation_for_headChoice hc).toChaseDerivation,
      (¬ (trg.output_for_headChoice hc).toSet ⊆ node.facts) -> h.applyFactSet node.facts ⊆ fs

/-- The overapproximation definition is independant of the trigger up to equivalence. -/
theorem FactSet.is_rpc_overapproximation_of_equiv
    {rules : RuleSet sig}
    {hc : HeadChoice sig}
    (hc_consistent : hc.consistent_for_equivalent_triggers)
    {trg1 trg2 : Trigger sig obs.toLaxObsolescenceCondition}
    {fs : FactSet sig}
    (overapprox : fs.is_rpc_overapproximation rules hc trg1) :
    trg1.equiv trg2 -> fs.is_rpc_overapproximation rules hc trg2 := by
  intro equiv; rcases overapprox with ⟨h, id_const, id_frontier, overapprox⟩
  exists h; constructor; rw [← equiv.left]; exact id_const
  constructor; rw [← PreTrigger.mapped_frontier_eq_of_equiv equiv]; exact id_frontier
  intro kb rules_eq ct node node_mem output_sub_node
  apply overapprox kb rules_eq ct node node_mem
  rw [PreTrigger.output_for_headChoice_eq_of_equiv hc_consistent equiv]
  exact output_sub_node

/-- This is Lemma 1 from the [RPC] paper. -/
theorem RTrigger.rsUnblockable_of_not_obsolete_for_overapproximation
    (obs_propagates : obs.propagates_under_term_mapping_of_no_fresh_term_occurs)
    {rules : RuleSet sig} {hc : HeadChoice sig}
    (hc_consistent : hc.consistent_for_equivalent_triggers)
    {trg : RTrigger obs rules} {fs : FactSet sig} :
    fs.is_rpc_overapproximation rules hc trg.val -> ¬ obs.cond trg.val fs -> trg.val.rsUnblockable rules hc := by
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
        have := this orig orig_mem; unfold ChaseNodeOrigin.adheres_to_headChoice at this
        simp only [← this]
        exact node3.val.facts_contain_origin_result orig orig_mem
      apply ct.subderivation_for_headChoice_adheres_to_headChoice
      exact node3.property
    . exact id_head_consts
  rcases RegularChaseDerivation.fairness_prec (cd := (ct.subderivation_for_headChoice hc).toChaseDerivation) trg_kb with ⟨fairness_node, fair⟩
  cases ChaseDerivationSkeleton.predecessor_total node fairness_node with
  | inl prec => exists fairness_node; constructor; exact prec; apply fair; grind
  | inr prec => exists node; constructor; grind; apply fair; exact prec

/-- A slight generalization of the above theorem showing that all equivalent triggers are also rsUnblockable. -/
theorem RTrigger.rsUnblockable_of_equiv_trigger_not_obsolete_for_overapproximation
    (obs_propagates : obs.propagates_under_term_mapping_of_no_fresh_term_occurs)
    {rules : RuleSet sig} {hc : HeadChoice sig}
    (hc_consistent : hc.consistent_for_equivalent_triggers)
    {trg : RTrigger obs rules} {fs : FactSet sig} :
    fs.is_rpc_overapproximation rules hc trg.val -> ¬ obs.cond trg.val fs -> ∀ trg', trg.equiv trg' -> trg'.val.rsUnblockable rules hc := by
  intro overapprox not_obs trg' trg_equiv
  apply trg'.rsUnblockable_of_not_obsolete_for_overapproximation obs_propagates hc_consistent
  . exact fs.is_rpc_overapproximation_of_equiv hc_consistent overapprox trg_equiv
  . rw [← obs.preserved_under_equiv trg_equiv]; exact not_obs

section RestrictedObsolescenceOnly

/--
If a trigger has a rule with at least one existentially quantified variable but only constants in the mapped frontier,
then at least an equivalent trigger cannot be `rsUnblockable`. (It can still be `kbUnblockable` though.)
To show this, we simply pick the knowledge base featuring the database with all the constants from the trigger interconnected.
This is already a model so the only chase tree features exactly the root node. But then the result of the trigger does not occur.
-/
-- TODO: A similar result should hold for arbitrary ObsolescenceConditions but only for rules with at least one head disjunct without existential variables. We already have a corresponding critical instance result for this but to show the theorem, we would still need to be able to construct a chase tree (because it would not stop immediately after the database). Once we have such a general construction, it is easy to argue that triggers remain obsolete because they are already obsolete for the database.
theorem Trigger.not_rsUnblockable_of_hc_exis_of_frontier_only_constants
    [Inhabited sig.C] {rules : RuleSet sig} {hc : HeadChoice sig} {trg : RTrigger RestrictedObsolescence rules}
    (rules_finite : rules.finite)
    (hc_consistent : hc.consistent_for_equivalent_triggers)
    (hc_exis : trg.val.rule.existential_vars_for_head_disjunct (hc trg.val).val (hc trg.val).isLt ≠ [])
    (frontier_only_constants : ∀ t ∈ trg.val.mapped_frontier, ∃ c, t = .const c) :
    ∃ trg', trg.equiv trg' ∧ ¬ trg'.val.rsUnblockable rules hc := by
  have rules_non_empty_heads : ∀ r ∈ rules, r.head ≠ [] := by
    -- TODO: rules with empty heads basically function as denial constraints (they are can never be satisfied once their body matches); maybe we should forbid this in general? although it's maybe also nice to have this as an option. Maybe we should introduce this as a property that rules and rule sets can have (being free of denial constraints that is). Also, observe that by our current definitions, a kb with denial constraints does not admit a chase derivation if a denial constraint becomes loaded at some point, because then, fairness is violated.
    -- Note that here, the existence of a head choice implies that no rule can have an empty head. If any rule had an empty head, we could not pick an apropriate index with the head choice. Truth be told, this is not necessarily an intentional consequence but I take it.
    intro r _ contra
    let trg : PreTrigger sig := ⟨r, fun _ => .const default⟩
    let i := hc trg
    apply Nat.not_lt_zero i.val
    suffices trg.rule.head.length = 0 by rw [← this]; exact i.isLt
    simp [trg, contra]
  suffices ∃ db : Database sig, (∃ trg', trg.equiv trg' ∧ trg'.val.loaded db.toFactSet.val) ∧ ∀ trg : RTrigger RestrictedObsolescence rules, ¬ trg.val.active db.toFactSet.val by
    rcases this with ⟨db, ⟨trg', trg_equiv, trg'_loaded⟩, all_obs⟩
    have hc_exis' : trg'.val.rule.existential_vars_for_head_disjunct (hc trg'.val).val (hc trg'.val).isLt ≠ [] := by
      simp only [← trg_equiv.left, ← hc_consistent trg_equiv]; exact hc_exis
    exists trg'; constructor; exact trg_equiv
    let kb : KnowledgeBase sig := ⟨db, rules⟩
    intro contra; specialize contra kb rfl
    let startNode : RegularChaseNode RestrictedObsolescence rules := { facts := db.toFactSet.val, origin := none, facts_contain_origin_result := by simp }
    let ct : RegularChaseTree RestrictedObsolescence kb := {
      tree := FiniteDegreeTree.node startNode []
      isSome_root := by simp
      database_first := by simp [TreeDerivation.root, RegularChaseNode.ingoingFacts_eq, RegularChaseNode.outgoingFacts_eq, RegularChaseNode.origin_eq, kb, startNode]
      triggers_exist := by
        intro t2 suffix; rw [FiniteDegreeTree.IsSuffix_iff] at suffix; rcases suffix with ⟨ns, suffix⟩
        cases ns with
        | nil => simp [← suffix, FiniteDegreeTree.childNodes_eq, ChaseNode.succ_list]
        | cons n ns => simp [← suffix, FiniteDegreeTree.get?_node_cons]
      fairness_leaves := by
        intro leaf leaf_mem
        suffices leaf = startNode by
          intro trg; rw [this, RegularChaseNode.outgoingFacts_eq]; simp only [startNode]
          intro active
          apply all_obs
          exact active
        rw [FiniteDegreeTree.mem_leaves] at leaf_mem; rcases leaf_mem with ⟨ns, leaf_mem⟩
        cases ns with
        | nil => grind
        | cons n ns => simp [FiniteDegreeTree.get?_node_cons] at leaf_mem
      fairness_infinite_branches := by intro trg; exists 1; intro ns len_ge; cases ns; simp at len_ge; simp [FiniteDegreeTree.get?_node_cons]
    }
    have startNode_only_node : ∀ node ∈ ct, node = startNode := by
      intro node; rw [ChaseTree.mem_iff]; intro ⟨ns, node_mem⟩
      cases ns with
      | nil => simp only [ct, FiniteDegreeTree.get?_node_nil, Option.some_inj] at node_mem; exact Eq.symm node_mem
      | cons n ns => simp [ct, FiniteDegreeTree.get?_node_cons] at node_mem
    have childNodes_empty : ct.childNodes = [] := by simp only [ct]; rw [TreeDerivation.childNodes_eq, List.map_eq_nil_iff]; simp [TreeDerivation.childTrees]
    specialize contra ct ⟨startNode, by
      suffices startNode = (ct.subderivation_for_headChoice hc).head by
        rw [this]; exact ChaseDerivationSkeleton.head_mem
      simp only [ChaseTree.subderivation_for_headChoice]
      rw [ct.toTreeDerivation.head_subderivation_for_headChoice]
      simp [ct, startNode, TreeDerivation.root]⟩
    specialize contra trg'_loaded
    rcases contra with ⟨node2, node2_succ, contra⟩
    have node2_eq : node2.val = startNode := by
      apply startNode_only_node
      have node2_mem := node2.property
      rw [ChaseDerivation.mem_iff_eq_head_or_mem_tail] at node2_mem
      cases node2_mem with
      | inl node2_mem => rw [node2_mem]; simp only [ChaseTree.subderivation_for_headChoice, ct.head_subderivation_for_headChoice]; exact ct.root_mem
      | inr node2_mem =>
        rcases node2_mem with ⟨h, _⟩
        simp only [ChaseTree.subderivation_for_headChoice] at h
        rw [Option.isSome_iff_exists] at h; rcases h with ⟨next, h⟩
        have h := ct.next_subderivation_for_headChoice_mem_childNodes next h
        simp [childNodes_empty] at h
    rw [node2_eq] at contra
    rcases List.exists_mem_of_ne_nil _ hc_exis' with ⟨v, v_mem⟩
    suffices trg'.val.functional_term_for_var (hc trg'.val).val (hc trg'.val).isLt v v_mem ∈ startNode.facts.terms by
      rcases this with ⟨f, f_mem, t_mem⟩
      rcases db.toFactSet.property.right f f_mem _ t_mem with ⟨c, t_eq⟩
      exact GroundTerm.func_neq_const t_eq
    apply FactSet.terms_subset_of_subset contra
    simp only [FactSet.mem_terms_toSet, PreTrigger.output_for_headChoice, trg'.val.mem_terms_mapped_head_iff (hc trg'.val).val (hc trg'.val).isLt]
    apply Or.inr; apply Or.inr; apply PreTrigger.mem_fresh_terms_of_functional_for_exis_var

  let consts : List sig.C := trg.val.mapped_frontier.flatMap GroundTerm.constants
  exists rules.generalizedCriticalInstance rules_finite (Inhabited.default :: consts)
  constructor
  . let subs : GroundSubstitution sig := fun v => if v ∈ trg.val.rule.frontier then trg.val.subs v else .const Inhabited.default
    let trg' : RTrigger RestrictedObsolescence rules := ⟨⟨trg.val.rule, subs⟩, trg.property⟩
    exists trg'; constructor
    . apply PreTrigger.equiv_of_rule_eq_of_mapped_frontier_equiv
      . rfl
      . simp only [PreTrigger.mapped_frontier, trg', subs]
        apply List.map_congr_left
        intro v v_mem; simp [v_mem]
    . apply rules.generalizedCriticalInstance_trigger_loaded
      intro t t_mem
      rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_body_iff] at t_mem
      rw [Set.mem_map]
      cases t_mem with
      | inl t_mem =>
        rcases t_mem with ⟨c, c_mem, t_mem⟩
        exists c; constructor
        . apply Set.mem_union_of_mem_right; exists trg'.val.rule; constructor; exact trg'.property; apply Rule.body_constants_subset_constants; exact c_mem
        . exact t_mem
      | inr t_mem =>
        rcases t_mem with ⟨v, v_mem, t_mem⟩
        cases Decidable.em (v ∈ trg.val.rule.frontier) with
        | inl v_frontier =>
          rcases frontier_only_constants (trg.val.subs v) (List.mem_map_of_mem v_frontier) with ⟨c, c_mem⟩
          exists c; constructor
          . apply Set.mem_union_of_mem_left; rw [List.mem_toSet, List.mem_cons]; apply Or.inr; simp only [consts]; rw [List.mem_flatMap]; exists trg.val.subs v; constructor; exact List.mem_map_of_mem v_frontier; rw [c_mem]; simp
          . rw [← t_mem, ← c_mem]; simp [trg', subs, v_frontier]
        | inr v_frontier =>
          exists Inhabited.default; constructor
          . apply Set.mem_union_of_mem_left; simp
          . rw [← t_mem]; simp [trg', subs, v_frontier]
  . intro trg
    apply rules.generalizedCriticalInstance_no_trigger_active_for_restrictedObsolescence
    . exists default; grind
    . apply rules_non_empty_heads; exact trg.property

end RestrictedObsolescenceOnly

