/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.ChaseBranch
public import ExistentialRules.ChaseSequence.TreeDerivation

/-!
# Chase Tree

A `ChaseTree` is a special kind of `TreeDerivation` which is defined for a `KnowledgeBase`
and enforces the root of the `TreeDerivation` to be the database from the `KnowledgeBase`.

Compared to the `TreeDerivation` some new theorems can be shown or some existing ones strengthened. For example, we know now that functional terms can never occur in a database so every functional term must originate as a fresh term from some trigger that is used in the chase.

The `ChaseTree` is to the `TreeDerivation` what the `ChaseBranch` is to the `ChaseDerivation`.
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- The `ChaseTree` merely extends the `TreeDerivation` with the condition that the root is the database from the knowledge base. -/
structure ChaseTree (N : Type u) (obs : ObsolescenceCondition sig) (kb : KnowledgeBase sig) [CN : ChaseNode N obs kb.rules] extends TreeDerivation N obs kb.rules where
  -- We do not need to demand existence here since the TreeDerivation already ensures that the root exists.
  -- The ∀ quantifier makes this condition more convenient to use.
  database_first : ∀ root ∈ tree.root,
    CN.ingoingFacts root = kb.db.toFactSet ∧
    CN.outgoingFacts root = kb.db.toFactSet ∧
    CN.origin root = none

namespace ChaseTree

variable {obs : ObsolescenceCondition sig} {kb : KnowledgeBase sig}
variable {N : Type u} [CN : ChaseNode N obs kb.rules]

instance : Membership N (ChaseTree N obs kb) where
  mem td node := node ∈ td.tree

/-- An element is a member of the tree iff it occurs at some address. -/
theorem mem_iff {ct : ChaseTree N obs kb} :
  ∀ {e}, e ∈ ct ↔ ∃ ns, ct.tree.get? ns = some e := TreeDerivation.mem_iff

/-- We can convert `ChaseDerivation`s that are branches in the `ChaseTree` to `ChaseBranch`es. -/
@[expose]
def chaseBranch_for_branch {ct : ChaseTree N obs kb} {branch : ChaseDerivation N obs kb.rules} (branch_mem : branch ∈ ct.branches) : ChaseBranch N obs kb := {
  branch := branch.branch
  isSome_head := branch.isSome_head
  triggers_exist := branch.triggers_exist
  triggers_active := branch.triggers_active
  fairness := branch.fairness
  database_first := by
    rw [TreeDerivation.branches_eq] at branch_mem
    have head_eq := branch_mem.left
    unfold TreeDerivation.root ChaseDerivationSkeleton.head at head_eq; rw [Option.get_inj] at head_eq
    intro head; rw [head_eq]
    exact ct.database_first head
}

/-- We restate the `database_first` condition in terms of the `TreeDerivation` vocabulary. -/
theorem database_first' {ct : ChaseTree N obs kb} :
    CN.ingoingFacts ct.root = kb.db.toFactSet ∧
    CN.outgoingFacts ct.root = kb.db.toFactSet ∧
    CN.origin ct.root = none := by
  apply ct.database_first; simp [TreeDerivation.root]

/-- The root of the `ChaseTree` does not contain any function terms. -/
theorem func_term_not_mem_root {ct : ChaseTree N obs kb}
    {t : GroundTerm sig} (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok) :
    ¬ t ∈ (CN.outgoingFacts ct.root).terms := by
  intro t_mem
  simp only [database_first'] at t_mem
  rcases t_mem with ⟨f, f_mem, t_mem⟩
  rcases kb.db.toFactSet.property.right f f_mem t t_mem with ⟨c, t_eq⟩
  rcases t_is_func with ⟨_, _, _, t_eq'⟩
  rw [t_eq'] at t_eq
  simp [GroundTerm.func_neq_const] at t_eq

end ChaseTree


abbrev RegularChaseTree (obs : ObsolescenceCondition sig) (kb : KnowledgeBase sig) := ChaseTree (RegularChaseNode obs kb.rules) obs kb

namespace RegularChaseTree

variable {obs : ObsolescenceCondition sig} {kb : KnowledgeBase sig}

/-- Opposed to a `TreeDerivation`, we know that each node in a `ChaseBranch` has a finite set of facts. This is because the database is finite and each trigger only adds finitely many new facts. -/
theorem facts_finite_of_mem {ct : RegularChaseTree obs kb} {node : RegularChaseNode obs kb.rules} (node_mem : node ∈ ct) :
    node.facts.finite := by
  rw [RegularTreeDerivation.facts_node_eq_union_initial_and_generated node_mem]
  apply Set.union_finite_of_both_finite
  . rw [← ct.root.outgoingFacts_eq, ct.database_first'.right.left]; exact kb.db.toFactSet.property.left
  . exact RegularTreeDerivation.generatedFacts_finite_of_mem node_mem

/-- We define a shortcut for `RegularTreeDerivation.result`. -/
abbrev result (ct : RegularChaseTree obs kb) := RegularTreeDerivation.result ct.toTreeDerivation

/-- Each element of the result of a `ChaseTree` not only models the rule set but the whole `KnowledgeBase`. -/
theorem result_models_kb {ct : RegularChaseTree obs kb} : ∀ fs ∈ ct.result, fs.modelsKb kb := by
  unfold result RegularTreeDerivation.result; simp only [Set.mem_map]
  intro fs ⟨branch, branch_mem, fs_mem⟩
  let cb := ct.chaseBranch_for_branch branch_mem
  have : RegularChaseDerivationSkeleton.result branch.toChaseDerivationSkeleton = RegularChaseDerivationSkeleton.result cb.toChaseDerivationSkeleton := by rfl
  simp only [← fs_mem, this]
  exact RegularChaseBranch.result_models_kb

/-- Constants in the chase must be in the database or in some rule. -/
theorem constants_node_subset_constants_db_union_constants_rules {ct : RegularChaseTree obs kb}
    {node : RegularChaseNode obs kb.rules} (node_mem : node ∈ ct) :
    node.facts.constants ⊆ (kb.db.constants.val ∪ kb.rules.head_constants) := by
  have := RegularTreeDerivation.constants_node_subset_constants_fs_union_constants_rules node_mem
  rw [← ct.root.outgoingFacts_eq, ct.database_first'.right.left, Database.toFactSet_constants_same] at this
  exact this

/-- Each functional term in the chase originates as a fresh term from a trigger. -/
theorem functional_term_originates_from_some_trigger
    {ct : RegularChaseTree obs kb}
    (node : ct.NodeWithAddress)
    {t : GroundTerm sig}
    (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok)
    (t_mem : t ∈ node.node.facts.terms) :
    ∃ node2, node2 ≼ node ∧ ∃ orig ∈ node2.node.origin, t ∈ orig.fst.val.fresh_terms_for_head_disjunct orig.snd.val (by grind) := by
  cases RegularTreeDerivation.functional_term_originates_from_some_trigger node t_is_func t_mem with
  | inl t_mem => apply False.elim; exact ct.func_term_not_mem_root t_is_func t_mem
  | inr t_mem => exact t_mem

/-- If a functional term occurs in the chase, then the trigger that introduces this term must have been used in the chase. -/
theorem trigger_introducing_functional_term_occurs_in_chase
    {ct : RegularChaseTree obs kb}
    (node : ct.NodeWithAddress)
    {t : GroundTerm sig}
    (t_mem_node : t ∈ node.node.facts.terms)
    {trg : RTrigger obs kb.rules}
    {disj_idx : Nat}
    {lt : disj_idx < trg.val.rule.head.length}
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
    ∃ node2, node2 ≼ node ∧ ∃ orig ∈ node2.node.origin, orig.fst.equiv trg ∧ orig.snd.val = disj_idx := by
  cases RegularTreeDerivation.trigger_introducing_functional_term_occurs_in_chase node t_mem_node t_mem_trg with
  | inl t_mem => apply False.elim; exact ct.func_term_not_mem_root (PreTrigger.term_functional_of_mem_fresh_terms _ t_mem_trg) t_mem
  | inr t_mem => exact t_mem

/-- If a functional term occurs in the chase, then the result of the trigger that introduces this term is contained in the current node. -/
theorem result_of_trigger_introducing_functional_term_occurs_in_chase
    {ct : RegularChaseTree obs kb}
    (node : ct.NodeWithAddress)
    {t : GroundTerm sig}
    (t_mem_node : t ∈ node.node.facts.terms)
    {trg : RTrigger obs kb.rules}
    {disj_idx : Nat}
    {lt : disj_idx < trg.val.rule.head.length}
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) : (trg.val.mapped_head[disj_idx]'(by simpa)).toSet ⊆ node.node.facts := by
  cases RegularTreeDerivation.result_of_trigger_introducing_functional_term_occurs_in_chase node t_mem_node t_mem_trg with
  | inl t_mem => apply False.elim; exact ct.func_term_not_mem_root (PreTrigger.term_functional_of_mem_fresh_terms _ t_mem_trg) t_mem
  | inr t_mem => exact t_mem

end RegularChaseTree

