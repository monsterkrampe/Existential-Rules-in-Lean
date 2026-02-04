import ExistentialRules.ChaseSequence.Termination.ConstantMappings.InterplayWithBacktracking.BacktrackingUnderConstantMappingSubsetOfComposingWithSubs.PreGroundTerm

/-!
# Interaction of Backtrackings and Strict Constant Mappings on GroundTerm

We merely lift `PreGroundTerm.backtrackFacts_under_constant_mapping_subset_of_composing_with_subs` to `GroundTerm` here.
-/

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P]

theorem GroundTerm.backtrackFacts_under_constant_mapping_subset_of_composing_with_subs
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    (rl : RuleList sig)
    (term : GroundTerm sig)
    (term_ruleIds_valid : term.skolem_ruleIds_valid rl)
    (term_disjIdx_valid : term.skolem_disjIdx_valid rl term_ruleIds_valid)
    (term_rule_arity_valid : term.skolem_rule_arity_valid rl term_ruleIds_valid)
    (forbidden_constants : List sig.C)
    (forbidden_constants_subsumes_term : term.constants ⊆ forbidden_constants)
    (forbidden_constants_subsumes_rules : (rl.rules.flatMap Rule.constants) ⊆ forbidden_constants) :
    let backtracking := (backtrackFacts rl term term_ruleIds_valid term_disjIdx_valid term_rule_arity_valid forbidden_constants)
    ∀ (g : StrictConstantMapping sig), (∀ d, (d ∈ rl.rules.flatMap Rule.constants) -> g d = d) ->
      ∃ (fresh_constant_remapping : StrictConstantMapping sig),
      (∀ d ∉ backtracking.snd, fresh_constant_remapping d = d) ∧ -- Is this first condition even required?!
      ((StrictConstantMapping.toConstantMapping (fun c => if c ∈ backtracking.snd then fresh_constant_remapping c else g c)).apply_fact_set backtracking.fst.toSet ⊆
      (backtrackFacts rl (g.toConstantMapping.apply_ground_term term)
        (by apply StrictConstantMapping.apply_ground_term_preserves_ruleId_validity; exact term_ruleIds_valid)
        (by apply StrictConstantMapping.apply_ground_term_preserves_disjIdx_validity; exact term_disjIdx_valid)
        (by apply StrictConstantMapping.apply_ground_term_preserves_rule_arity_validity; exact term_rule_arity_valid)
        (forbidden_constants.map g)
      ).fst.toSet) ∧
      (backtracking.snd.map fresh_constant_remapping = (backtrackFacts rl (g.toConstantMapping.apply_ground_term term)
        (by apply StrictConstantMapping.apply_ground_term_preserves_ruleId_validity; exact term_ruleIds_valid)
        (by apply StrictConstantMapping.apply_ground_term_preserves_disjIdx_validity; exact term_disjIdx_valid)
        (by apply StrictConstantMapping.apply_ground_term_preserves_rule_arity_validity; exact term_rule_arity_valid)
        (forbidden_constants.map g)
      ).snd) := by
  intro backtracking g g_id
  exact PreGroundTerm.backtrackFacts_under_constant_mapping_subset_of_composing_with_subs rl term.val term.property term_ruleIds_valid term_disjIdx_valid term_rule_arity_valid forbidden_constants forbidden_constants_subsumes_term forbidden_constants_subsumes_rules g g_id

theorem GroundTerm.backtrackFacts_list_under_constant_mapping_subset_of_composing_with_subs
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    (rl : RuleList sig)
    (terms : List (GroundTerm sig))
    (terms_ruleIds_valid : ∀ t ∈ terms, t.skolem_ruleIds_valid rl)
    (terms_disjIdx_valid : ∀ t, (mem : t ∈ terms) -> t.skolem_disjIdx_valid rl (terms_ruleIds_valid t mem))
    (terms_rule_arity_valid : ∀ t, (mem : t ∈ terms) -> t.skolem_rule_arity_valid rl (terms_ruleIds_valid t mem))
    (forbidden_constants : List sig.C)
    (forbidden_constants_subsumes_terms : terms.flatMap GroundTerm.constants ⊆ forbidden_constants)
    (forbidden_constants_subsumes_rules : (rl.rules.flatMap Rule.constants) ⊆ forbidden_constants) :
    let backtracking := (backtrackFacts_list rl terms terms_ruleIds_valid terms_disjIdx_valid terms_rule_arity_valid forbidden_constants)
    ∀ (g : StrictConstantMapping sig), (∀ d, (d ∈ rl.rules.flatMap Rule.constants) -> g d = d) ->
      ∃ (fresh_constant_remapping : StrictConstantMapping sig),
      (∀ d ∉ backtracking.snd, fresh_constant_remapping d = d) ∧
      ((StrictConstantMapping.toConstantMapping (fun c => if c ∈ backtracking.snd then fresh_constant_remapping c else g c)).apply_fact_set backtracking.fst.toSet ⊆
      (backtrackFacts_list rl (terms.map g.toConstantMapping.apply_ground_term)
        (by intro t t_mem; rw [List.mem_map] at t_mem; rcases t_mem with ⟨t', t'_mem, t_eq⟩; rw [← t_eq]; apply StrictConstantMapping.apply_ground_term_preserves_ruleId_validity; apply terms_ruleIds_valid; exact t'_mem)
        (by intro t t_mem; rw [List.mem_map] at t_mem; rcases t_mem with ⟨t', t'_mem, t_eq⟩; simp only [← t_eq]; apply StrictConstantMapping.apply_ground_term_preserves_disjIdx_validity; apply terms_disjIdx_valid; exact t'_mem)
        (by intro t t_mem; rw [List.mem_map] at t_mem; rcases t_mem with ⟨t', t'_mem, t_eq⟩; simp only [← t_eq]; apply StrictConstantMapping.apply_ground_term_preserves_rule_arity_validity; apply terms_rule_arity_valid; exact t'_mem)
        (forbidden_constants.map g)
      ).fst.toSet) ∧
      (backtracking.snd.map fresh_constant_remapping = (backtrackFacts_list rl (terms.map g.toConstantMapping.apply_ground_term)
        (by intro t t_mem; rw [List.mem_map] at t_mem; rcases t_mem with ⟨t', t'_mem, t_eq⟩; rw [← t_eq]; apply StrictConstantMapping.apply_ground_term_preserves_ruleId_validity; apply terms_ruleIds_valid; exact t'_mem)
        (by intro t t_mem; rw [List.mem_map] at t_mem; rcases t_mem with ⟨t', t'_mem, t_eq⟩; simp only [← t_eq]; apply StrictConstantMapping.apply_ground_term_preserves_disjIdx_validity; apply terms_disjIdx_valid; exact t'_mem)
        (by intro t t_mem; rw [List.mem_map] at t_mem; rcases t_mem with ⟨t', t'_mem, t_eq⟩; simp only [← t_eq]; apply StrictConstantMapping.apply_ground_term_preserves_rule_arity_validity; apply terms_rule_arity_valid; exact t'_mem)
        (forbidden_constants.map g)
      ).snd) := by
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
  exact PreGroundTerm.backtrackFacts_list_under_constant_mapping_subset_of_composing_with_subs rl terms.unattach
    (by simp only [List.mem_unattach]; rintro _ ⟨h, _⟩; exact h)
    (by simp only [List.mem_unattach]; rintro _ ⟨_, t_mem⟩; exact terms_ruleIds_valid _ t_mem)
    (by simp only [List.mem_unattach]; rintro _ ⟨_, t_mem⟩; exact terms_disjIdx_valid _ t_mem)
    (by simp only [List.mem_unattach]; rintro _ ⟨_, t_mem⟩; exact terms_rule_arity_valid _ t_mem)
    forbidden_constants (by rw [List.flatMap_unattach]; exact forbidden_constants_subsumes_terms) forbidden_constants_subsumes_rules g g_id

