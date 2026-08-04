/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.Termination.ConstantMappings.InterplayWithBacktracking.BacktrackingUnderConstantMappingSubsetOfComposingWithSubs.PreGroundTerm

/-!
# Interaction of Backtrackings and Strict Constant Mappings on GroundTerm

We merely lift `PreGroundTerm.backtrackFacts_under_constant_mapping_subset_of_composing_with_subs` to `GroundTerm` here.
-/

public section

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P]

theorem GroundTerm.backtrackFacts_under_constant_mapping_subset_of_composing_with_subs
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    (term : GroundTerm sig)
    (forbidden_constants : List sig.C)
    (forbidden_constants_subsumes_term : term.constants ⊆ forbidden_constants)
    (forbidden_constants_subsumes_rules : (term.rules.flatMap Rule.constants) ⊆ forbidden_constants) :
    let backtracking := (backtrackFacts term forbidden_constants)
    ∀ (g : StrictConstantMapping sig), (∀ d, (d ∈ term.rules.flatMap Rule.constants) -> g d = d) ->
      ∃ (fresh_constant_remapping : StrictConstantMapping sig),
      (∀ d ∉ backtracking.snd, fresh_constant_remapping d = d) ∧ -- Is this first condition even required?!
      ((StrictConstantMapping.toConstantMapping (fun c => if c ∈ backtracking.snd then fresh_constant_remapping c else g c)).apply_fact_set backtracking.fst.toSet ⊆
      (backtrackFacts (g.toConstantMapping.apply_ground_term term) (forbidden_constants.map g)).fst.toSet) ∧
      (backtracking.snd.map fresh_constant_remapping = (backtrackFacts (g.toConstantMapping.apply_ground_term term) (forbidden_constants.map g)).snd) := by
  intro backtracking g g_id
  exact PreGroundTerm.backtrackFacts_under_constant_mapping_subset_of_composing_with_subs term.val term.property forbidden_constants forbidden_constants_subsumes_term (by unfold GroundTerm.rules at forbidden_constants_subsumes_rules; rw [List.flatMap_map] at forbidden_constants_subsumes_rules; exact forbidden_constants_subsumes_rules) g (by unfold GroundTerm.rules at g_id; rw [List.flatMap_map] at g_id; exact g_id)

theorem GroundTerm.backtrackFacts_list_under_constant_mapping_subset_of_composing_with_subs
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    (terms : List (GroundTerm sig))
    (forbidden_constants : List sig.C)
    (forbidden_constants_subsumes_terms : terms.flatMap GroundTerm.constants ⊆ forbidden_constants)
    (forbidden_constants_subsumes_rules : ((terms.flatMap GroundTerm.rules).flatMap Rule.constants) ⊆ forbidden_constants) :
    let backtracking := (backtrackFacts_list terms forbidden_constants)
    ∀ (g : StrictConstantMapping sig), (∀ d, (d ∈ (terms.flatMap GroundTerm.rules).flatMap Rule.constants) -> g d = d) ->
      ∃ (fresh_constant_remapping : StrictConstantMapping sig),
      (∀ d ∉ backtracking.snd, fresh_constant_remapping d = d) ∧
      ((StrictConstantMapping.toConstantMapping (fun c => if c ∈ backtracking.snd then fresh_constant_remapping c else g c)).apply_fact_set backtracking.fst.toSet ⊆
      (backtrackFacts_list (terms.map g.toConstantMapping.apply_ground_term) (forbidden_constants.map g)).fst.toSet) ∧
      (backtracking.snd.map fresh_constant_remapping = (backtrackFacts_list (terms.map g.toConstantMapping.apply_ground_term) (forbidden_constants.map g)).snd) := by
  intro backtracking g g_id
  have : (terms.map g.toConstantMapping.apply_ground_term).unattach = terms.unattach.map g.toConstantMapping.apply_pre_ground_term := by
    conv => left; unfold List.unattach
    rw [List.map_map]
    rw [List.map_unattach]
    apply List.map_congr_left
    intro t t_mem
    simp only [Function.comp_apply, ConstantMapping.apply_ground_term]
    rfl
  simp only [backtracking, backtrackFacts_list_eq, this]
  exact PreGroundTerm.backtrackFacts_list_under_constant_mapping_subset_of_composing_with_subs terms.unattach
    (by simp only [List.mem_unattach]; rintro _ ⟨h, _⟩; exact h)
    forbidden_constants
    (by rw [List.flatMap_unattach]; exact forbidden_constants_subsumes_terms)
    (by rw [List.flatMap_unattach]; unfold GroundTerm.rules at forbidden_constants_subsumes_rules; rw [← List.map_flatMap, List.flatMap_map] at forbidden_constants_subsumes_rules; exact forbidden_constants_subsumes_rules)
    g
    (by rw [List.flatMap_unattach]; unfold GroundTerm.rules at g_id; rw [← List.map_flatMap, List.flatMap_map] at g_id; exact g_id)

