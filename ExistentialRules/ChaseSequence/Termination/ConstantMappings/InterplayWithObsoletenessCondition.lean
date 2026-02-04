import ExistentialRules.ChaseSequence.Termination.ConstantMappings.InterplayWithRenamingConstantsApart

/-!
# Interactions of ConstantMappings with Obsoleteness

For MFA-like conditions, we want to make an additional assumption on `ObsoletenessCondition` that we did not demand before.
Namely, we want that the condition `propagates_under_constant_mapping`, meaning that of a trigger is obsolete for a fact set, then
the version of the trigger where a `ConstantMapping` is composed with the original substitution is also obsolete for the version of the fact set where the `ConstantMapping` was applied. At least this shall be the case if the `ConstantMapping` does not touch the head constants of the rule in the trigger.

We briefly demonstrate that this property holds for both `SkolemObsoleteness` and `RestrictedObsoleteness`.
-/

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P]

def ObsoletenessCondition.propagates_under_constant_mapping (obs : ObsoletenessCondition sig) : Prop := ∀ {trg : PreTrigger sig} {fs : FactSet sig} {g : ConstantMapping sig}, (∀ c ∈ trg.rule.head_constants, g c = GroundTerm.const c) -> obs.cond trg fs -> obs.cond { rule := trg.rule, subs := g.apply_ground_term ∘ trg.subs } (g.apply_fact_set fs)

theorem SkolemObsoleteness.propagates_under_constant_mapping : (SkolemObsoleteness sig).propagates_under_constant_mapping := by
  intro trg fs g g_id cond
  simp only [SkolemObsoleteness] at cond
  simp only [SkolemObsoleteness]
  let trg' : PreTrigger sig := { rule := trg.rule, subs := g.apply_ground_term ∘ trg.subs }
  rcases cond with ⟨i, cond⟩
  let i' : Fin trg'.mapped_head.length := ⟨i.val, by have isLt := i.isLt; simp only [PreTrigger.length_mapped_head] at *; exact isLt⟩
  exists i'
  intro f f_mem
  rw [List.mem_toSet] at f_mem
  unfold PreTrigger.mapped_head at f_mem
  simp only [List.getElem_map, List.getElem_zipIdx, List.mem_map, Nat.zero_add] at f_mem
  rcases f_mem with ⟨a, a_mem, f_eq⟩
  rw [← ConstantMapping.apply_fact_swap_apply_to_function_free_atom] at f_eq
  . rw [← f_eq]
    apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
    apply cond
    rw [List.mem_toSet]
    simp only [PreTrigger.mapped_head, List.getElem_map, List.getElem_zipIdx, List.mem_map, Nat.zero_add]
    exists a
  . intro d d_mem
    apply g_id
    unfold Rule.head_constants
    rw [List.mem_flatMap]
    exists trg.rule.head[i.val]'(by rw [← PreTrigger.length_mapped_head]; exact i.isLt)
    constructor
    . apply List.getElem_mem
    . unfold FunctionFreeConjunction.consts
      rw [List.mem_flatMap]
      exists a

theorem RestrictedObsoleteness.propagates_under_constant_mapping : (RestrictedObsoleteness sig).propagates_under_constant_mapping := by
  intro trg fs g g_id cond
  simp only [RestrictedObsoleteness, PreTrigger.satisfied, PreTrigger.satisfied_for_disj] at cond
  simp only [RestrictedObsoleteness, PreTrigger.satisfied, PreTrigger.satisfied_for_disj]
  let trg' : PreTrigger sig := { rule := trg.rule, subs := g.apply_ground_term ∘ trg.subs }
  rcases cond with ⟨i, cond⟩
  exists i
  rcases cond with ⟨s, id_front, cond⟩
  exists g.apply_ground_term ∘ s
  constructor
  . intro v v_mem; simp only [Function.comp_apply]; rw [id_front v v_mem]
  . unfold GroundSubstitution.apply_function_free_conj
    unfold TermMapping.apply_generalized_atom_list
    intro f f_mem
    rw [List.mem_toSet, List.mem_map] at f_mem
    rcases f_mem with ⟨a, a_mem, f_eq⟩
    rw [← GroundSubstitution.apply_function_free_atom.eq_def, GroundSubstitution.apply_function_free_atom_compose] at f_eq
    . rw [← f_eq]
      rw [← ConstantMapping.apply_fact_eq_groundTermMapping_applyFact]
      apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
      apply cond
      rw [List.mem_toSet]
      apply List.mem_map_of_mem
      exact a_mem
    . intro d d_mem
      conv => left; simp only [ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, GroundTerm.const, FiniteTree.mapLeaves]
      apply g_id
      unfold Rule.head_constants
      rw [List.mem_flatMap]
      exists trg.rule.head[i.val]
      constructor
      . apply List.getElem_mem
      . unfold FunctionFreeConjunction.consts
        rw [List.mem_flatMap]
        exists a

