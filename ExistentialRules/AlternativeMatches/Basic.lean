import ExistentialRules.ChaseSequence.ChaseTree
import ExistentialRules.ChaseSequence.Deterministic

/-!
# Alternative Matches

Put simply, alternative matches are homomorphisms that witness that a trigger can be satisfied in a way where one of its freshly introduced terms would be redundant. The goal of this notion is to show that a chase without any alternative matches yields a result that is a core, which is, intuitively speaking, the smallest possibly model up to isomorphism.
-/

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace GroundTermMapping

/-- A `GroundTermMapping` is an alternative match for a head disjunct of a trigger and a given fact set $F$ if (1) the mapping is a homomorphism from the head disjunct into $F$, (2) the mapping is the id on all frontier terms, and (3) there is a term that is freshly introduced by the trigger that does not occur in the mapped version of all fresh terms. -/
def isAlternativeMatch (h_alt : GroundTermMapping sig) (trg : PreTrigger sig) (disj_index : Fin trg.mapped_head.length) (fs : FactSet sig) : Prop :=
  have isLt : disj_index.val < trg.rule.head.length := by rw [← PreTrigger.length_mapped_head]; exact disj_index.isLt
  (h_alt.isHomomorphism trg.mapped_head[disj_index.val].toSet fs) ∧
  (∀ t, t ∈ trg.rule.frontier.map trg.subs -> h_alt t = t) ∧
  (∃ t, (t ∈ trg.fresh_terms_for_head_disjunct disj_index.val isLt) ∧
        (¬ t ∈ (trg.fresh_terms_for_head_disjunct disj_index.val isLt).map h_alt))

end GroundTermMapping

namespace PreTrigger

/-- If there exists an alternative match for a trigger, then the trigger is satisfied. -/
theorem satisfied_of_alternativeMatch {trg : PreTrigger sig} {fs : FactSet sig} {h_alt : GroundTermMapping sig} {disj_index : Fin trg.mapped_head.length} :
    h_alt.isAlternativeMatch trg disj_index fs -> trg.satisfied fs := by
  intro is_alt_match
  exists ⟨disj_index.val, by rw [← PreTrigger.length_mapped_head]; exact disj_index.isLt⟩
  exists (h_alt ∘ trg.apply_to_var_or_const disj_index ∘ VarOrConst.var)
  constructor
  . intro v v_in_frontier
    simp only [Function.comp_apply]
    rw [PreTrigger.apply_to_var_or_const_frontier_var _ _ _ v_in_frontier]
    apply is_alt_match.right.left
    apply List.mem_map_of_mem
    exact v_in_frontier
  . intro f f_mem
    apply is_alt_match.left.right
    simp only [← PreTrigger.apply_subs_for_mapped_head_eq, TermMapping.apply_generalized_atom_set_toSet]
    rw [GroundSubstitution.apply_function_free_conj_compose_of_isIdOnConstants _ _ is_alt_match.left.left] at f_mem
    exact f_mem

/-- If a trigger is satisfied for a fact set $F$ and there is a term that is freshly introduced by the trigger but does not occur in $F$, then the trigger has an alternative match. -/
theorem alternativeMatch_of_satisfied
    {trg : PreTrigger sig} {fs : FactSet sig} {disj_index : Fin trg.mapped_head.length} {gt : GroundTerm sig}
    (gt_in_res_but_not_fs : gt ∈ (trg.fresh_terms_for_head_disjunct disj_index.val (by rw [← PreTrigger.length_mapped_head]; exact disj_index.isLt)) ∧ ¬ gt ∈ fs.terms) :
    trg.satisfied_for_disj fs ⟨disj_index, by rw [← PreTrigger.length_mapped_head]; exact disj_index.isLt⟩ ->
      ∃ (h_alt : GroundTermMapping sig), h_alt.isAlternativeMatch trg disj_index fs := by
  intro satisfied
  rcases satisfied with ⟨s, s_frontier, s_subs⟩

  let h_alt : GroundTermMapping sig := fun t =>
    if t ∈ trg.fresh_terms_for_head_disjunct disj_index.val (by rw [← PreTrigger.length_mapped_head]; exact disj_index.isLt) then
      match t.val with
      | .leaf c => t -- this can actually never happen as the fresh terms are all functional
      | .inner skolem_fs _ => s skolem_fs.var
    else t

  have id_on_const : h_alt.isIdOnConstants := by
    intro c
    have : ¬ .const c ∈ trg.fresh_terms_for_head_disjunct disj_index.val (by rw [← PreTrigger.length_mapped_head]; exact disj_index.isLt) := by
      apply PreTrigger.constant_not_mem_fresh_terms_for_head_disjunct
    simp [h_alt, this]

  have : h_alt.applyFactSet trg.mapped_head[disj_index.val].toSet ⊆ fs := by
    intro f f_mem
    apply s_subs
    simp only [TermMapping.apply_generalized_atom_set_toSet, List.mem_toSet, ← PreTrigger.apply_subs_for_mapped_head_eq] at f_mem
    rw [← GroundSubstitution.apply_function_free_conj_compose _ _ _ (by intros; exact id_on_const)] at f_mem
    simp only [GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list, List.mem_map] at f_mem
    simp only [List.mem_toSet, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list, List.mem_map]
    rcases f_mem with ⟨a, a_mem, f_mem⟩
    exists a; simp only [a_mem, true_and]
    rw [← f_mem]
    apply TermMapping.apply_generalized_atom_congr_left
    intro voc voc_mem
    cases voc with
    | const c => simp [GroundSubstitution.apply_var_or_const]
    | var v =>
      simp only [GroundSubstitution.apply_var_or_const, Function.comp_apply]
      cases Decidable.em (v ∈ trg.rule.frontier) with
      | inl v_in_frontier =>
        simp only [PreTrigger.subs_for_mapped_head, PreTrigger.apply_to_var_or_const_frontier_var _ _ _ v_in_frontier]
        rw [s_frontier _ v_in_frontier]
        simp only [h_alt]
        have : ¬ trg.subs v ∈ trg.fresh_terms_for_head_disjunct disj_index.val (by rw [← PreTrigger.length_mapped_head]; exact disj_index.isLt) := by
          apply PreTrigger.frontier_term_not_mem_fresh_terms_for_head_disjunct
          apply List.mem_map_of_mem
          exact v_in_frontier
        simp [this]
      | inr v_in_frontier =>
        simp only [PreTrigger.subs_for_mapped_head, PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v_in_frontier]
        simp only [h_alt]
        have : trg.functional_term_for_var disj_index.val v ∈ trg.fresh_terms_for_head_disjunct disj_index.val (by rw [← PreTrigger.length_mapped_head]; exact disj_index.isLt) := by
          apply List.mem_map_of_mem
          simp only [Rule.existential_vars_for_head_disjunct, List.mem_filter, decide_eq_true_eq]; constructor
          . rw [FunctionFreeConjunction.mem_vars]; exists a
          . exact v_in_frontier
        rcases trg.term_functional_of_mem_fresh_terms _ this with ⟨func, ts, arity_ok, eq⟩
        simp only [this, ↓reduceIte]; simp only [eq, GroundTerm.func]
        simp only [PreTrigger.functional_term_for_var, GroundTerm.func] at eq; rw [Subtype.mk.injEq, FiniteTree.inner.injEq] at eq
        rw [← eq.left]

  exists h_alt
  constructor
  . constructor
    . exact id_on_const
    . exact this
  constructor
  . intro t ht; simp only [h_alt]
    have : ¬ t ∈ trg.fresh_terms_for_head_disjunct disj_index.val (by rw [← PreTrigger.length_mapped_head]; exact disj_index.isLt) := by
      apply PreTrigger.frontier_term_not_mem_fresh_terms_for_head_disjunct; exact ht
    simp [this]
  . exists gt
    constructor
    . exact gt_in_res_but_not_fs.left
    . intro contra; rw [List.mem_map] at contra
      apply gt_in_res_but_not_fs.right
      rcases contra with ⟨t, t_mem, gt_mem⟩
      apply FactSet.terms_subset_of_subset this
      rw [← gt_mem, GroundTermMapping.terms_applyFactSet]
      exists t; simp only [and_true]
      rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_head_iff]
      apply Or.inr; apply Or.inr; exact t_mem

end PreTrigger

