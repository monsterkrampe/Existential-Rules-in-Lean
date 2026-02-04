import ExistentialRules.ChaseSequence.Termination.ConstantMappings.ArgumentsForImages

/-!
# StrictConstantMappings preserve Function Term Validity

Applying `StrictConstantMapping`s does not alter validity of functional terms in any way
since they only rename constants inside terms but do not change their structure.
Recall that term validity is required for backtrackings.
-/

namespace StrictConstantMapping

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P]

theorem apply_pre_ground_term_preserves_ruleId_validity (g : StrictConstantMapping sig) (term : FiniteTree (SkolemFS sig) sig.C) :
    ∀ rl, PreGroundTerm.skolem_ruleIds_valid rl term -> PreGroundTerm.skolem_ruleIds_valid rl (g.toConstantMapping.apply_pre_ground_term term) := by
  intro rl valid
  induction term with
  | leaf _ => simp [PreGroundTerm.skolem_ruleIds_valid, StrictConstantMapping.toConstantMapping, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, GroundTerm.const]
  | inner func ts ih =>
    simp only [PreGroundTerm.skolem_ruleIds_valid, StrictConstantMapping.toConstantMapping, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves]
    simp only [PreGroundTerm.skolem_ruleIds_valid] at valid
    constructor
    . exact valid.left
    . simp only [List.mem_map]
      rintro t' ⟨t, t_mem, t'_eq⟩
      rw [← t'_eq]
      apply ih _ t_mem
      exact valid.right _ t_mem

theorem apply_pre_ground_term_preserves_disjIdx_validity (g : StrictConstantMapping sig) (term : FiniteTree (SkolemFS sig) sig.C) :
    ∀ rl, (h : PreGroundTerm.skolem_ruleIds_valid rl term) -> PreGroundTerm.skolem_disjIdx_valid rl term h -> PreGroundTerm.skolem_disjIdx_valid rl (g.toConstantMapping.apply_pre_ground_term term) (g.apply_pre_ground_term_preserves_ruleId_validity term rl h) := by
  intro rl _ valid
  induction term with
  | leaf _ => simp [PreGroundTerm.skolem_disjIdx_valid, StrictConstantMapping.toConstantMapping, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, GroundTerm.const]
  | inner func ts ih =>
    simp only [PreGroundTerm.skolem_disjIdx_valid, StrictConstantMapping.toConstantMapping, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves]
    simp only [PreGroundTerm.skolem_disjIdx_valid] at valid
    constructor
    . exact valid.left
    . simp only [List.mem_map]
      rintro t' ⟨t, t_mem, t'_eq⟩
      simp only [← t'_eq]
      apply ih _ t_mem
      exact valid.right _ t_mem

theorem apply_pre_ground_term_preserves_rule_arity_validity (g : StrictConstantMapping sig) (term : FiniteTree (SkolemFS sig) sig.C) :
    ∀ rl, (h : PreGroundTerm.skolem_ruleIds_valid rl term) -> PreGroundTerm.skolem_rule_arity_valid rl term h -> PreGroundTerm.skolem_rule_arity_valid rl (g.toConstantMapping.apply_pre_ground_term term) (g.apply_pre_ground_term_preserves_ruleId_validity term rl h) := by
  intro rl _ valid
  induction term with
  | leaf _ => simp [PreGroundTerm.skolem_rule_arity_valid, StrictConstantMapping.toConstantMapping, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, GroundTerm.const]
  | inner func ts ih =>
    simp only [PreGroundTerm.skolem_rule_arity_valid, StrictConstantMapping.toConstantMapping, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves]
    simp only [PreGroundTerm.skolem_rule_arity_valid] at valid
    constructor
    . exact valid.left
    . simp only [List.mem_map]
      rintro t' ⟨t, t_mem, t'_eq⟩
      simp only [← t'_eq]
      apply ih _ t_mem
      exact valid.right _ t_mem

theorem apply_ground_term_preserves_ruleId_validity (g : StrictConstantMapping sig) (term : GroundTerm sig) :
    ∀ rl, GroundTerm.skolem_ruleIds_valid rl term -> GroundTerm.skolem_ruleIds_valid rl (g.toConstantMapping.apply_ground_term term) := by
  intro rl valid
  apply apply_pre_ground_term_preserves_ruleId_validity
  exact valid

theorem apply_ground_term_preserves_disjIdx_validity (g : StrictConstantMapping sig) (term : GroundTerm sig) :
    ∀ rl, (h : GroundTerm.skolem_ruleIds_valid rl term) -> GroundTerm.skolem_disjIdx_valid rl term h -> GroundTerm.skolem_disjIdx_valid rl (g.toConstantMapping.apply_ground_term term) (g.apply_ground_term_preserves_ruleId_validity term rl h) := by
  intro rl _ valid
  apply apply_pre_ground_term_preserves_disjIdx_validity
  exact valid

theorem apply_ground_term_preserves_rule_arity_validity (g : StrictConstantMapping sig) (term : GroundTerm sig) :
    ∀ rl, (h : GroundTerm.skolem_ruleIds_valid rl term) -> GroundTerm.skolem_rule_arity_valid rl term h -> GroundTerm.skolem_rule_arity_valid rl (g.toConstantMapping.apply_ground_term term) (g.apply_ground_term_preserves_ruleId_validity term rl h) := by
  intro rl _ valid
  apply apply_pre_ground_term_preserves_rule_arity_validity
  exact valid

end StrictConstantMapping

namespace PreTrigger

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P]

theorem compose_strict_constant_mapping_preserves_ruleId_validity (trg : PreTrigger sig) (g : StrictConstantMapping sig) :
    ∀ rl, trg.skolem_ruleIds_valid rl -> {rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ trg.subs : PreTrigger sig}.skolem_ruleIds_valid rl := by
  intro rl valid
  intro t t_mem
  rw [PreTrigger.mem_terms_mapped_body_iff] at t_mem
  cases t_mem with
  | inl t_mem =>
    rcases t_mem with ⟨c, c_mem, t_eq⟩
    simp only [← t_eq]
    apply GroundTerm.skolem_ruleIds_valid_const
  | inr t_mem =>
    rcases t_mem with ⟨v, v_mem, t_eq⟩
    simp only [← t_eq]
    apply StrictConstantMapping.apply_ground_term_preserves_ruleId_validity
    apply valid
    rw [PreTrigger.mem_terms_mapped_body_iff]
    apply Or.inr
    exists v

theorem compose_strict_constant_mapping_preserves_disjIdx_validity (trg : PreTrigger sig) (g : StrictConstantMapping sig) :
    ∀ rl, (h : trg.skolem_ruleIds_valid rl) -> trg.skolem_disjIdx_valid rl h -> {rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ trg.subs : PreTrigger sig}.skolem_disjIdx_valid rl (trg.compose_strict_constant_mapping_preserves_ruleId_validity g rl h) := by
  intro rl _ valid
  intro t t_mem
  rw [PreTrigger.mem_terms_mapped_body_iff] at t_mem
  cases t_mem with
  | inl t_mem =>
    rcases t_mem with ⟨c, c_mem, t_eq⟩
    simp only [← t_eq]
    apply GroundTerm.skolem_disjIdx_valid_const
  | inr t_mem =>
    rcases t_mem with ⟨v, v_mem, t_eq⟩
    simp only [← t_eq]
    apply StrictConstantMapping.apply_ground_term_preserves_disjIdx_validity
    apply valid
    rw [PreTrigger.mem_terms_mapped_body_iff]
    apply Or.inr
    exists v

theorem compose_strict_constant_mapping_preserves_rule_arity_validity (trg : PreTrigger sig) (g : StrictConstantMapping sig) :
    ∀ rl, (h : trg.skolem_ruleIds_valid rl) -> trg.skolem_rule_arity_valid rl h -> {rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ trg.subs : PreTrigger sig}.skolem_rule_arity_valid rl (trg.compose_strict_constant_mapping_preserves_ruleId_validity g rl h) := by
  intro rl _ valid
  intro t t_mem
  rw [PreTrigger.mem_terms_mapped_body_iff] at t_mem
  cases t_mem with
  | inl t_mem =>
    rcases t_mem with ⟨c, c_mem, t_eq⟩
    simp only [← t_eq]
    apply GroundTerm.skolem_rule_arity_valid_const
  | inr t_mem =>
    rcases t_mem with ⟨v, v_mem, t_eq⟩
    simp only [← t_eq]
    apply StrictConstantMapping.apply_ground_term_preserves_rule_arity_validity
    apply valid
    rw [PreTrigger.mem_terms_mapped_body_iff]
    apply Or.inr
    exists v

end PreTrigger
