import ExistentialRules.ChaseSequence.ChaseDerivation

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

structure ChaseBranch (obs : ObsoletenessCondition sig) (kb : KnowledgeBase sig) extends ChaseDerivation obs kb.rules where
  database_first : branch.head = some {
    facts := kb.db.toFactSet,
    origin := none,
    facts_contain_origin_result := by simp [Option.is_none_or]
  }

namespace ChaseBranch

  variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

  theorem database_first' {cb : ChaseBranch obs kb} : cb.head = {
    facts := kb.db.toFactSet,
    origin := none,
    facts_contain_origin_result := by simp [Option.is_none_or]
  } := by simp only [ChaseDerivation.head, cb.database_first, Option.get_some]

  theorem facts_finite_of_mem {cb : ChaseBranch obs kb} (node : cb.Node) : node.val.facts.finite := by
    induction node using ChaseDerivation.mem_rec with
    | head => simp only [database_first']; exact kb.db.toFactSet.property.left
    | step cd2 suffix ih next next_mem =>
      rw [cd2.facts_next next_mem]
      apply Set.union_finite_of_both_finite ih
      apply List.finite_toSet

  theorem func_term_not_mem_head {cb : ChaseBranch obs kb} {t : GroundTerm sig} (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok) : ¬ t ∈ cb.head.facts.terms := by
    intro t_mem
    simp only [database_first'] at t_mem
    rcases t_mem with ⟨f, f_mem, t_mem⟩
    rcases kb.db.toFactSet.property.right f f_mem t t_mem with ⟨c, t_eq⟩
    rcases t_is_func with ⟨_, _, _, t_eq'⟩
    rw [t_eq'] at t_eq
    simp [GroundTerm.const, GroundTerm.func] at t_eq

  theorem constants_node_subset_constants_db_union_constants_rules {cb : ChaseBranch obs kb} {node : cb.Node} :
      node.val.facts.constants ⊆ (kb.db.constants.val ∪ kb.rules.head_constants) := by
    have := cb.constants_node_subset_constants_fs_union_constants_rules node.property
    simp only [cb.database_first', Database.toFactSet_constants_same] at this
    exact this

  theorem result_models_kb {cb : ChaseBranch obs kb} : cb.result.modelsKb kb := by
    constructor
    . intro f h
      apply cb.facts_node_subset_result cb.head
      . apply cb.head_mem
      . rw [database_first']; exact h
    . exact cb.result_models_rules

  theorem functional_term_originates_from_some_trigger
      {cb : ChaseBranch obs kb}
      (node : cb.Node)
      {t : GroundTerm sig}
      (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok)
      (t_mem : t ∈ node.val.facts.terms) :
      ∃ node2, node2 ≼ node ∧ node2.val.origin.is_some_and (fun origin => t ∈ origin.fst.val.fresh_terms_for_head_disjunct origin.snd.val (by rw [← PreTrigger.length_mapped_head]; exact origin.snd.isLt)) := by
    cases ChaseDerivation.functional_term_originates_from_some_trigger node t_is_func t_mem with
    | inl t_mem => apply False.elim; exact cb.func_term_not_mem_head t_is_func t_mem
    | inr t_mem => exact t_mem

  theorem trigger_introducing_functional_term_occurs_in_chase
      {cb : ChaseBranch obs kb}
      (node : cb.Node)
      {t : GroundTerm sig}
      (t_mem_node : t ∈ node.val.facts.terms)
      {trg : RTrigger obs kb.rules}
      {disj_idx : Nat}
      {lt : disj_idx < trg.val.rule.head.length}
      (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
      ∃ node2, node2 ≼ node ∧ node2.val.origin.is_some_and (fun origin => origin.fst.equiv trg ∧ origin.snd.val = disj_idx) := by
    cases ChaseDerivation.trigger_introducing_functional_term_occurs_in_chase node t_mem_node t_mem_trg with
    | inl t_mem => apply False.elim; exact cb.func_term_not_mem_head (PreTrigger.term_functional_of_mem_fresh_terms _ t_mem_trg) t_mem
    | inr t_mem => exact t_mem

  theorem result_of_trigger_introducing_functional_term_occurs_in_chase
      {cb : ChaseBranch obs kb}
      (node : cb.Node)
      {t : GroundTerm sig}
      (t_mem_node : t ∈ node.val.facts.terms)
      {trg : RTrigger obs kb.rules}
      {disj_idx : Nat}
      {lt : disj_idx < trg.val.rule.head.length}
      (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
      (trg.val.mapped_head[disj_idx]'(by rw [PreTrigger.length_mapped_head]; exact lt)).toSet ⊆ node.val.facts := by
    cases ChaseDerivation.result_of_trigger_introducing_functional_term_occurs_in_chase node t_mem_node t_mem_trg with
    | inl t_mem => apply False.elim; exact cb.func_term_not_mem_head (PreTrigger.term_functional_of_mem_fresh_terms _ t_mem_trg) t_mem
    | inr t_mem => exact t_mem

end ChaseBranch

