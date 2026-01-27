import ExistentialRules.ChaseSequence.ChaseBranch
import ExistentialRules.ChaseSequence.TreeDerivation

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

structure ChaseTree (obs : ObsoletenessCondition sig) (kb : KnowledgeBase sig) extends TreeDerivation obs kb.rules where
  database_first : tree.root = some {
    facts := kb.db.toFactSet
    origin := none
    facts_contain_origin_result := by simp
  }

namespace ChaseTree

  variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

  instance : Membership (ChaseNode obs kb.rules) (ChaseTree obs kb) where
    mem td node := node ∈ td.tree

  def chaseBranch_for_branch {ct : ChaseTree obs kb} {branch : ChaseDerivation obs kb.rules} (branch_mem : branch ∈ ct.branches) : ChaseBranch obs kb := {
    branch := branch.branch
    isSome_head := branch.isSome_head
    triggers_exist := branch.triggers_exist
    fairness := branch.fairness
    database_first := by rw [← ct.database_first]; unfold TreeDerivation.branches at branch_mem; rw [FiniteDegreeTree.branches_eq] at branch_mem; rw [branch_mem.left]
  }

  theorem database_first' {ct : ChaseTree obs kb} : ct.root = {
    facts := kb.db.toFactSet,
    origin := none,
    facts_contain_origin_result := by simp
  } := by simp only [TreeDerivation.root, ct.database_first, Option.get_some]

  theorem facts_finite_of_mem {ct : ChaseTree obs kb} {node : ChaseNode obs kb.rules} (node_mem : node ∈ ct) : node.facts.finite := by
    rcases node_mem with ⟨addr, node_mem⟩
    let node' : ct.NodeWithAddress := {node := node, address := addr, eq := node_mem}
    show node'.node.facts.finite
    induction node' using TreeDerivation.mem_rec_address with
    | root => simp only [TreeDerivation.root_NodeWithAddress, database_first']; exact kb.db.toFactSet.property.left
    | step new_root ih c c_mem =>
      simp only [TreeDerivation.NodeWithAddress.cast_for_new_root_node]
      rw [TreeDerivation.facts_childNodes (TreeDerivation.mem_childNodes_of_mem_childNodes_as_NodesWithAddress c_mem)]
      rw [TreeDerivation.root_subderivation_for_NodeWithAddress]
      apply Set.union_finite_of_both_finite ih
      apply List.finite_toSet

  theorem func_term_not_mem_head {ct : ChaseTree obs kb} {t : GroundTerm sig} (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok) : ¬ t ∈ ct.root.facts.terms := by
    intro t_mem
    simp only [database_first'] at t_mem
    rcases t_mem with ⟨f, f_mem, t_mem⟩
    rcases kb.db.toFactSet.property.right f f_mem t t_mem with ⟨c, t_eq⟩
    rcases t_is_func with ⟨_, _, _, t_eq'⟩
    rw [t_eq'] at t_eq
    simp [GroundTerm.const, GroundTerm.func] at t_eq

  theorem constants_node_subset_constants_db_union_constants_rules {ct : ChaseTree obs kb} {node : ChaseNode obs kb.rules} (node_mem : node ∈ ct) :
      node.facts.constants ⊆ (kb.db.constants.val ∪ kb.rules.head_constants) := by
    have := ct.constants_node_subset_constants_fs_union_constants_rules node_mem
    simp only [ct.database_first', Database.toFactSet_constants_same] at this
    exact this

  theorem result_models_kb {ct : ChaseTree obs kb} : ∀ fs ∈ ct.result, fs.modelsKb kb := by
    rintro fs ⟨branch, branch_mem, fs_mem⟩
    let cb := ct.chaseBranch_for_branch branch_mem
    have : branch.result = cb.result := by rfl
    rw [← fs_mem, this]
    exact cb.result_models_kb

  theorem functional_term_originates_from_some_trigger
      {ct : ChaseTree obs kb}
      (node : ct.NodeWithAddress)
      {t : GroundTerm sig}
      (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok)
      (t_mem : t ∈ node.node.facts.terms) :
      ∃ node2, node2 ≼ node ∧ ∃ orig ∈ node2.node.origin, t ∈ orig.fst.val.fresh_terms_for_head_disjunct orig.snd.val (by rw [← PreTrigger.length_mapped_head]; exact orig.snd.isLt) := by
    cases TreeDerivation.functional_term_originates_from_some_trigger node t_is_func t_mem with
    | inl t_mem => apply False.elim; exact ct.func_term_not_mem_head t_is_func t_mem
    | inr t_mem => exact t_mem

  theorem trigger_introducing_functional_term_occurs_in_chase
      {ct : ChaseTree obs kb}
      (node : ct.NodeWithAddress)
      {t : GroundTerm sig}
      (t_mem_node : t ∈ node.node.facts.terms)
      {trg : RTrigger obs kb.rules}
      {disj_idx : Nat}
      {lt : disj_idx < trg.val.rule.head.length}
      (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
      ∃ node2, node2 ≼ node ∧ ∃ orig ∈ node2.node.origin, orig.fst.equiv trg ∧ orig.snd.val = disj_idx := by
    cases TreeDerivation.trigger_introducing_functional_term_occurs_in_chase node t_mem_node t_mem_trg with
    | inl t_mem => apply False.elim; exact ct.func_term_not_mem_head (PreTrigger.term_functional_of_mem_fresh_terms _ t_mem_trg) t_mem
    | inr t_mem => exact t_mem

  theorem result_of_trigger_introducing_functional_term_occurs_in_chase
      {ct : ChaseTree obs kb}
      (node : ct.NodeWithAddress)
      {t : GroundTerm sig}
      (t_mem_node : t ∈ node.node.facts.terms)
      {trg : RTrigger obs kb.rules}
      {disj_idx : Nat}
      {lt : disj_idx < trg.val.rule.head.length}
      (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
      (trg.val.mapped_head[disj_idx]'(by rw [PreTrigger.length_mapped_head]; exact lt)).toSet ⊆ node.node.facts := by
    cases TreeDerivation.result_of_trigger_introducing_functional_term_occurs_in_chase node t_mem_node t_mem_trg with
    | inl t_mem => apply False.elim; exact ct.func_term_not_mem_head (PreTrigger.term_functional_of_mem_fresh_terms _ t_mem_trg) t_mem
    | inr t_mem => exact t_mem

end ChaseTree
