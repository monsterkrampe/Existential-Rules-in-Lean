import ExistentialRules.ChaseSequence.Basic
import ExistentialRules.ChaseSequence.Deterministic

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace GroundTermMapping

  def isAlternativeMatch (h_alt : GroundTermMapping sig) (trg : PreTrigger sig) (disj_index : Fin trg.mapped_head.length) (fs : FactSet sig) : Prop :=
    (h_alt.isHomomorphism trg.mapped_head[disj_index.val].toSet fs) ∧
    (∀ t, t ∈ trg.rule.frontier.map trg.subs -> h_alt t = t) ∧
    (∃ n, (n ∈ FactSet.terms trg.mapped_head[disj_index.val].toSet) ∧ (¬ n ∈ (h_alt.applyFactSet trg.mapped_head[disj_index.val].toSet).terms))

end GroundTermMapping

namespace PreTrigger

  -- TODO: cleanup the proof; seems like we need lemmas on PreTrigger and Substitution Interaction (likely also useful elsewhere)
  theorem satisfied_of_alternativeMatch (trg : PreTrigger sig) (fs : FactSet sig) : ∀ (h_alt : GroundTermMapping sig) (disj_index : Fin trg.mapped_head.length), h_alt.isAlternativeMatch trg disj_index fs -> trg.satisfied fs := by
    intro h_alt disj_index is_alt_match
    exists ⟨disj_index.val, by rw [← PreTrigger.length_mapped_head]; exact disj_index.isLt⟩
    exists (h_alt ∘ trg.apply_to_var_or_const disj_index ∘ VarOrConst.var)
    constructor
    . intro v v_in_frontier
      simp only [Function.comp_apply]
      simp [PreTrigger.apply_to_var_or_const, PreTrigger.skolemize_var_or_const, VarOrConst.skolemize, v_in_frontier]
      apply is_alt_match.right.left
      simp
      exists v
    . intro f f_mem
      apply is_alt_match.left.right
      rw [List.mem_toSet] at f_mem
      unfold GroundSubstitution.apply_function_free_conj at f_mem
      simp only [TermMapping.apply_generalized_atom_list, List.mem_map] at f_mem
      simp [PreTrigger.mapped_head]
      unfold GroundTermMapping.applyFactSet
      rcases f_mem with ⟨a, a_mem, a_eq⟩
      rw [← a_eq]
      rw [GroundSubstitution.apply_var_or_const_compose_of_isIdOnConstants _ _ is_alt_match.left.left]
      rw [TermMapping.apply_generalized_atom_compose]
      apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
      unfold PreTrigger.apply_to_function_free_atom
      rw [List.mem_toSet, List.mem_map]
      exists a
      constructor
      . exact a_mem
      . apply TermMapping.apply_generalized_atom_congr_left
        intro t t_mem
        cases t with
        | const c => rw [PreTrigger.apply_to_var_or_const_for_const]; simp [GroundSubstitution.apply_var_or_const]
        | var v => simp [GroundSubstitution.apply_var_or_const]

  theorem alternativeMatch_of_satisfied (trg : PreTrigger sig) (fs : FactSet sig) (disj_index : Fin trg.mapped_head.length) (gt : GroundTerm sig) (gt_in_res_but_not_fs : gt ∈ (FactSet.terms trg.mapped_head[disj_index.val].toSet) ∧ ¬ gt ∈ fs.terms) : trg.satisfied_for_disj fs ⟨disj_index, by rw [← PreTrigger.length_mapped_head]; exact disj_index.isLt⟩ -> ∃ (h_alt : GroundTermMapping sig), h_alt.isAlternativeMatch trg disj_index fs := by
    intro satisfied
    rcases satisfied with ⟨s, s_frontier, s_subs⟩

    let h_alt : GroundTermMapping sig := fun t =>
      if t ∈ trg.rule.frontier.map trg.subs then t else match t.val with
        | .leaf c => t
        | .inner skolem_fs _ => s skolem_fs.var

    have : h_alt.applyFactSet trg.mapped_head[disj_index.val].toSet ⊆ fs := by
      intro f f_mem
      apply s_subs
      unfold GroundTermMapping.applyFactSet at f_mem
      rcases f_mem with ⟨f', f'_mem, f'_eq⟩
      simp only [PreTrigger.mapped_head] at f'_mem
      rw [List.mem_toSet] at f'_mem
      simp only [List.getElem_map, List.mem_map, List.getElem_zipIdx] at f'_mem
      rcases f'_mem with ⟨a, a_mem, a_eq⟩

      rw [List.mem_toSet]
      simp only [GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list, List.mem_map]
      exists a
      constructor
      . exact a_mem
      . rw [f'_eq, ← a_eq]
        rw [← Function.comp_apply (f := TermMapping.apply_generalized_atom h_alt), ← TermMapping.apply_generalized_atom_compose]
        apply TermMapping.apply_generalized_atom_congr_left
        intro voc voc_mem
        cases voc with
        | const c =>
          simp [GroundSubstitution.apply_var_or_const, PreTrigger.apply_to_var_or_const, PreTrigger.skolemize_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term]
          simp [h_alt, GroundTerm.const]
        | var v =>
          simp [GroundSubstitution.apply_var_or_const]
          cases Decidable.em (v ∈ trg.rule.frontier) with
          | inl v_in_frontier =>
            simp [PreTrigger.apply_to_var_or_const, PreTrigger.skolemize_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term]
            simp [v_in_frontier, h_alt]
            have : ∃ a, a ∈ trg.rule.frontier ∧ trg.subs a = trg.subs v := by exists v
            simp [this]
            apply s_frontier
            exact v_in_frontier
          | inr v_not_in_frontier =>
            simp only [h_alt]
            have : ¬ trg.apply_to_var_or_const disj_index.val (VarOrConst.var v) ∈ trg.rule.frontier.map trg.subs := by
              apply trg.result_term_not_in_frontier_image_of_var_not_in_frontier ⟨disj_index.val, by rw [← PreTrigger.length_mapped_head]; exact disj_index.isLt⟩
              exact v_not_in_frontier
            simp [this]
            simp [PreTrigger.apply_to_var_or_const, PreTrigger.skolemize_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term, GroundTerm.func]
            simp [v_not_in_frontier]

    exists h_alt
    constructor
    . constructor
      . intro t; cases eq : t with
        | const c => simp [GroundTerm.const, h_alt]
        | func _ _ => simp [GroundTerm.func]
      . exact this
    constructor
    . intro t ht; simp only [h_alt, ht]; simp
    . exists gt
      constructor
      . exact gt_in_res_but_not_fs.left
      . intro contra
        apply gt_in_res_but_not_fs.right
        rcases contra with ⟨f, f_mem, gt_mem⟩
        exists f
        constructor
        . apply this; exact f_mem
        . exact gt_mem

end PreTrigger

