/-
Copyright 2026 Henrik Tscherny, Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

import ExistentialRules.ChaseSequence.CoreChase.Basic
public import ExistentialRules.ChaseSequence.CoreChase.CoreChaseBranch

/-!
# Universality of the Core Chase Result

Just as for determistic `RegularChaseBranch`es, the result of a determistic `CoreChaseBranch` is a universal model of the underlying `KnowledgeBase`.
-/

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace CoreChaseBranch

variable {kb : KnowledgeBase sig}

-- TODO: This duplicates a lot of the universality proof of the regular chase derivations. A lot is already generalized over there but it all works on trees, which is why we cannot simply reuse it here... Unify this in the future!

theorem extend_hom_to_next
    {cb : CoreChaseBranch kb} {cd : CoreChaseDerivation kb.rules} {m : FactSet sig} {h : GroundTermMapping sig} :
    cd <:+ cb.toChaseDerivation -> kb.isDeterministic -> m.modelsRules kb.rules -> h.isHomomorphism cd.head.core m ->
    ∀ next ∈ cd.next, ∃ (h' : GroundTermMapping sig), h'.isHomomorphism next.core m := by
  intro suf det m_is_model h_hom next next_mem

  let orig := next.origin.get (cd.isSome_origin_next next_mem)
  let trg := orig.fst
  have trg_act : trg.val.active cd.head.core := cd.active_trigger_origin_next next_mem
  have trg_rule_det : trg.val.rule.head.length = 1 := by
    have := det _ trg.property; unfold Rule.isDeterministic at this; rw [decide_eq_true_iff] at this; exact this
  have orig_snd_zero : orig.snd.val = 0 := by
    have isLt := orig.snd.isLt; unfold trg at trg_rule_det; simp only [PreTrigger.length_mapped_head, trg_rule_det] at isLt; grind

  let trg_variant_for_m : RTrigger (RestrictedObsolescence sig) kb.rules := {
    val := {
      rule := trg.val.rule
      subs := fun t => h (trg.val.subs t)
    }
    property := trg.property
  }
  have trg_variant_loaded_for_m : trg_variant_for_m.val.loaded m := by
    suffices trg_variant_for_m.val.loaded (h.applyFactSet cd.head.core) by
      exact Set.subset_trans this h_hom.right
    apply PreTrigger.term_mapping_preserves_loadedness
    . exact h_hom.left
    . exact trg_act.left
  have trg_variant_satisfied_on_m : trg_variant_for_m.val.satisfied_for_disj m ⟨0, by rw [trg_rule_det]; simp⟩ := by
    suffices trg_variant_for_m.val.satisfied m by
      rcases this with ⟨idx, goal⟩
      have : idx = ⟨0, by rw [trg_rule_det]; simp⟩ := by have isLt := idx.isLt; simp only [trg_variant_for_m, trg_rule_det] at isLt; grind
      simp only [this] at goal
      exact goal
    have m_models_rule : m.modelsRule trg_variant_for_m.val.rule := by exact m_is_model trg.val.rule trg.property
    unfold FactSet.modelsRule at m_models_rule
    apply m_models_rule
    apply trg_variant_loaded_for_m

  rcases trg_variant_satisfied_on_m with ⟨obs_for_m_subs, obs_for_m_subs_spec⟩

  let next_hom : GroundTermMapping sig := fun t =>
    let t_in_node := t ∈ cd.head.core.terms
    have t_in_node_dec := Classical.propDecidable t_in_node
    if t_in_node then h t else
      let t_fresh := t ∈ trg.val.fresh_terms_for_head_disjunct 0 (by rw [trg_rule_det]; simp)
      have t_fresh_dec := Classical.propDecidable t_fresh
      if t_fresh_true : t_fresh then
        obs_for_m_subs (trg.val.existential_var_for_fresh_term _ _ t t_fresh_true)
      else t

  have next_hom_id_const : next_hom.isIdOnConstants := by
    intro c
    simp only [next_hom]
    split
    . exact h_hom.left
    . split
      case isFalse _ => rfl
      case isTrue h => rcases trg.val.term_functional_of_mem_fresh_terms _ h with ⟨_, _, _, contra⟩; have contra := Eq.symm contra; simp [GroundTerm.func_neq_const] at contra

  exists next_hom; constructor; exact next_hom_id_const
  intro mapped_f
  rw [GroundTermMapping.mem_applyFactSet]
  intro ⟨f, f_mem, mapped_f_eq⟩
  have f_mem := next.homSubset.left _ f_mem
  rw [← CoreChaseNode.ingoingFacts_eq, cd.facts_next next_mem] at f_mem
  rw [mapped_f_eq]
  cases f_mem with
  | inl f_mem =>
    apply h_hom.right
    rw [GroundTermMapping.mem_applyFactSet]
    exists f; rw [CoreChaseNode.outgoingFacts_eq] at f_mem; simp only [f_mem, true_and]
    apply TermMapping.apply_generalized_atom_congr_left
    intro t t_mem
    have t_mem : t ∈ cd.head.core.terms := by exists f
    simp [next_hom, t_mem]
  | inr f_mem =>
    have f_mem : f ∈ trg.val.mapped_head[0] := by
      rw [List.mem_toSet, ChaseNode.origin_result_eq _ (trg := trg.val.toPreTrigger) (i := 0)] at f_mem; exact f_mem
      . rfl
      . exact Eq.symm orig_snd_zero
    apply obs_for_m_subs_spec.right
    rw [List.mem_toSet]
    rw [GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]
    rw [List.mem_map]
    exists (trg.val.atom_for_result_fact ⟨0, by rw [PreTrigger.length_mapped_head, trg_rule_det]; simp⟩ f_mem); constructor
    . apply PreTrigger.atom_for_result_fact_mem_head
    conv => right; rw [← trg.val.apply_on_atom_for_result_fact_is_fact ⟨0, by rw [PreTrigger.length_mapped_head, trg_rule_det]; simp⟩ f_mem]
    rw [← PreTrigger.apply_subs_for_atom_eq]
    unfold GroundTermMapping.applyFact
    rw [← Function.comp_apply (f := TermMapping.apply_generalized_atom next_hom)]
    rw [← GroundTermMapping.applyFact.eq_def, ← GroundSubstitution.apply_function_free_atom_compose_of_isIdOnConstants _ _ next_hom_id_const]
    apply TermMapping.apply_generalized_atom_congr_left
    intro voc voc_mem
    cases voc with
    | const c => simp [GroundSubstitution.apply_var_or_const]
    | var v =>
      rw [GroundSubstitution.apply_var_or_const_compose_of_isIdOnConstants _ _ next_hom_id_const]
      rw [Function.comp_apply, PreTrigger.apply_subs_for_var_or_const_eq]
      simp only [GroundSubstitution.apply_var_or_const]
      cases Decidable.em (v ∈ trg.val.rule.frontier) with
      | inl v_front =>
        rw [obs_for_m_subs_spec.left v v_front]
        rw [PreTrigger.apply_to_var_or_const_frontier_var _ _ _ v_front]
        simp only [trg_variant_for_m, next_hom]
        suffices trg.val.subs v ∈ cd.head.core.terms by simp [this]
        apply FactSet.terms_subset_of_subset trg_act.left
        rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_body_iff]
        apply Or.inr
        exists v; constructor
        . apply Rule.frontier_subset_vars_body; exact v_front
        . rfl
      | inr v_front =>
        have v_exis : v ∈ trg.val.rule.existential_vars_for_head_disjunct 0 (by rw [trg_rule_det]; simp) := by
          simp only [Rule.existential_vars_for_head_disjunct, List.mem_filter, decide_eq_true_eq]; constructor
          . rw [FunctionFreeConjunction.mem_vars];
            exists (trg.val.atom_for_result_fact ⟨0, by rw [PreTrigger.length_mapped_head, trg_rule_det]; simp⟩ f_mem); constructor
            . apply PreTrigger.atom_for_result_fact_mem_head
            . exact voc_mem
          . exact v_front
        have func_term_fresh : trg.val.functional_term_for_var 0 v ∈ trg.val.fresh_terms_for_head_disjunct 0 (by rw [trg_rule_det]; simp) := by apply List.mem_map_of_mem; exact v_exis
        rw [PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v_front]
        simp only [next_hom]
        suffices ¬ trg.val.functional_term_for_var 0 v ∈ cd.head.core.terms by
          simp only [this, ↓reduceIte]
          simp only [func_term_fresh, ↓reduceDIte]
          rw [PreTrigger.existential_var_for_fresh_term_after_functional_term_for_var]
          exact v_exis
        intro contra
        -- from here this is a bit different than for the regular chase derivation
        rcases cb.trigger_introducing_functional_term_occurs_in_chase ⟨cd.head, cd.mem_of_mem_suffix suf _ cd.head_mem⟩ (FactSet.terms_subset_of_subset cd.head.homSubset.left _ contra) func_term_fresh with ⟨node2, prec, orig2, orig2_mem, equiv, orig2_snd_zero⟩
        apply cb.origin_trg_remains_inactive prec _ orig2_mem _ equiv
        exact trg_act

theorem extend_hom_to_each
    {cb : CoreChaseBranch kb} {cd : CoreChaseDerivation kb.rules} {m : FactSet sig} {h : GroundTermMapping sig} :
    cd <:+ cb.toChaseDerivation -> kb.isDeterministic -> m.modelsRules kb.rules -> h.isHomomorphism cd.head.core m ->
    ∀ node ∈ cd, ∃ (h' : GroundTermMapping sig), h'.isHomomorphism node.core m := by
  intro suf det m_is_model h_hom node node_mem
  let node : cd.Node := ⟨node, node_mem⟩
  show ∃ (h' : GroundTermMapping sig), h'.isHomomorphism node.val.core m
  induction node using cd.mem_rec with
  | head => exists h
  | step cd2 suf2 ih next next_mem =>
    rcases ih with ⟨ig_h, ih_h_hom⟩
    exact cb.extend_hom_to_next (PossiblyInfiniteList.IsSuffix_trans suf2 suf) det m_is_model ih_h_hom next next_mem

theorem extend_hom_prec
    {cb : CoreChaseBranch kb} {m : FactSet sig} {h : GroundTermMapping sig} :
    kb.isDeterministic -> m.modelsRules kb.rules ->
    ∀ (n1 n2 : cb.Node), n1 ≼ n2 -> h.isHomomorphism n1.val.core m -> ∃ (h' : GroundTermMapping sig), h'.isHomomorphism n2.val.core m := by
  intro det m_is_model n1 n2 prec h_hom
  rw [cb.predecessor_iff] at prec; rcases prec with ⟨cd, suf, head_eq, n2_mem⟩
  exact extend_hom_to_each suf det m_is_model (by rw [head_eq]; exact h_hom) _ n2_mem

public theorem result_universallyModels_kb {cb : CoreChaseBranch kb} (det : kb.isDeterministic) (term : cb.terminates) :
    (CoreChaseDerivation.result cb.toChaseDerivation term).universallyModelsKb kb := by
  constructor; exact cb.result_models_kb term
  intro m m_is_model
  suffices GroundTermMapping.isHomomorphism id cb.head.core m by
    exact cb.extend_hom_prec det m_is_model.right ⟨cb.head, cb.head_mem⟩ ⟨cb.last term, cb.last_mem term⟩ (cb.each_prec_last term _) this
  apply GroundTermMapping.isHomomorphism_id_of_subset
  intro f f_mem
  apply m_is_model.left
  rw [← cb.database_first'.right.left, CoreChaseNode.outgoingFacts_eq]
  exact f_mem

end CoreChaseBranch

