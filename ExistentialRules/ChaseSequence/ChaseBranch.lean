/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.ChaseDerivation

/-!
# Chase Branch

A `ChaseBranch` is a special kind of `ChaseDerivation` which is defined for a `KnowledgeBase`
and enforces the head of the `ChaseDerivation` to be the database from the `KnowledgeBase`.
This is arguably the most common way for defining chase sequences/derivations in the literature.
We call this branch here, since we consider rules with disjunctions that would actually create a chase tree (see `TreeDerivation` and `ChaseTree`)
and intuitively the `ChaseBranch` is a branch in such a tree. However, it can be defined outside the tree, which is what we do here (and mostly did for the `ChaseDerivation` already).

Compared to the `ChaseDerivation` some new theorems can be shown or some existing ones strengthened. For example, we know now that functional terms can never occur in a database so every functional term must originate as a fresh term from some trigger that is used in the chase.
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- The `ChaseBranch` merely extends the `ChaseDerivation` with the condition that the head is the database from the knowledge base. -/
structure ChaseBranch (N : Type u) (obs : ObsolescenceCondition sig) (kb : KnowledgeBase sig) [CN : ChaseNode N obs kb.rules] extends ChaseDerivation N obs kb.rules where
  -- We do not need to demand existence here since the ChaseDerivation(Skeleton) already ensures that the head exists.
  -- The ∀ quantifier makes this condition more convenient to use.
  database_first : ∀ head ∈ branch.head,
    CN.ingoingFacts head = kb.db.toFactSet ∧
    CN.outgoingFacts head = kb.db.toFactSet ∧
    CN.origin head = none

namespace ChaseBranch

variable {obs : ObsolescenceCondition sig} {kb : KnowledgeBase sig}
variable {N : Type u} [CN : ChaseNode N obs kb.rules]

/-- We restate the `database_first` condition in terms of the `ChaseDerivation` vocabulary. -/
theorem database_first' {cb : ChaseBranch N obs kb} :
    CN.ingoingFacts cb.head = kb.db.toFactSet ∧
    CN.outgoingFacts cb.head = kb.db.toFactSet ∧
    CN.origin cb.head = none := by
  apply cb.database_first; simp [ChaseDerivationSkeleton.head]

/-- The head of the `ChaseBranch` does not contain any function terms. -/
theorem func_term_not_mem_head {cb : ChaseBranch N obs kb} {t : GroundTerm sig} (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok) :
    -- This is also true for the ingoingFacts but I think that we will only need this for the outgoingFacts.
    ¬ t ∈ (CN.outgoingFacts cb.head).terms := by
  intro t_mem
  simp only [database_first'] at t_mem
  rcases t_mem with ⟨f, f_mem, t_mem⟩
  rcases kb.db.toFactSet.property.right f f_mem t t_mem with ⟨c, t_eq⟩
  rcases t_is_func with ⟨_, _, _, t_eq'⟩
  rw [t_eq'] at t_eq
  simp [GroundTerm.func_neq_const] at t_eq

end ChaseBranch


abbrev RegularChaseBranch (obs : ObsolescenceCondition sig) (kb : KnowledgeBase sig) := ChaseBranch (RegularChaseNode obs kb.rules) obs kb

namespace RegularChaseBranch

variable {obs : ObsolescenceCondition sig} {kb : KnowledgeBase sig}

/-- Opposed to a `ChaseDerivation`, we know that each node in a `ChaseBranch` has a finite set of facts. This is because the database is finite and each trigger only adds finitely many new facts. -/
@[grind <-]
theorem facts_finite_of_mem {cb : RegularChaseBranch obs kb} (node : cb.Node) : node.val.facts.finite := by
  rw [RegularChaseDerivationSkeleton.facts_node_eq_union_initial_and_generated node.property]
  apply Set.union_finite_of_both_finite
  . rw [← cb.head.outgoingFacts_eq, cb.database_first'.right.left]; exact kb.db.toFactSet.property.left
  . exact RegularChaseDerivationSkeleton.generatedFacts_finite_of_mem node.property

/-- We define a shortcut for `RegularChaseDerivationSkeleton.result`. -/
abbrev result (cd : RegularChaseBranch obs kb) := RegularChaseDerivationSkeleton.result cd.toChaseDerivationSkeleton

/-- The result of a `ChaseBranch` not only models the rule set but the whole `KnowledgeBase`. -/
@[grind <-]
theorem result_models_kb {cb : RegularChaseBranch obs kb} : cb.result.modelsKb kb := by
  constructor
  . intro f h
    apply RegularChaseDerivationSkeleton.facts_node_subset_result cb.head
    . apply cb.head_mem
    . rw [← cb.head.outgoingFacts_eq, cb.database_first'.right.left]; exact h
  . exact RegularChaseDerivation.result_models_rules

/-- Constants in the chase must be in the database or in some rule. -/
theorem constants_node_subset_constants_db_union_constants_rules {cb : RegularChaseBranch obs kb} {node : cb.Node} :
    node.val.facts.constants ⊆ (kb.db.constants.val ∪ kb.rules.head_constants) := by
  have := RegularChaseDerivation.constants_node_subset_constants_fs_union_constants_rules node.property
  rw [← cb.head.outgoingFacts_eq, cb.database_first'.right.left, Database.toFactSet_constants_same] at this
  exact this

/-- Each functional term in the chase originates as a fresh term from a trigger. -/
theorem functional_term_originates_from_some_trigger
    {cb : RegularChaseBranch obs kb}
    (node : cb.Node)
    {t : GroundTerm sig}
    (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok)
    (t_mem : t ∈ node.val.facts.terms) :
    ∃ node2, node2 ≼ node ∧ ∃ orig ∈ node2.val.origin,
      t ∈ orig.fst.val.fresh_terms_for_head_disjunct orig.snd.val (by rw [← PreTrigger.length_mapped_head]; exact orig.snd.isLt) := by
  cases RegularChaseDerivation.functional_term_originates_from_some_trigger node t_is_func t_mem with
  | inl t_mem => apply False.elim; exact cb.func_term_not_mem_head t_is_func t_mem
  | inr t_mem => exact t_mem

/-- If a functional term occurs in the chase, then the trigger that introduces this term must have been used in the chase. -/
theorem trigger_introducing_functional_term_occurs_in_chase
    {cb : RegularChaseBranch obs kb}
    (node : cb.Node)
    {t : GroundTerm sig}
    (t_mem_node : t ∈ node.val.facts.terms)
    {trg : RTrigger obs kb.rules}
    {disj_idx : Nat}
    {lt : disj_idx < trg.val.rule.head.length}
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
    ∃ node2, node2 ≼ node ∧ ∃ orig ∈ node2.val.origin, orig.fst.equiv trg ∧ orig.snd.val = disj_idx := by
  cases RegularChaseDerivation.trigger_introducing_functional_term_occurs_in_chase node t_mem_node t_mem_trg with
  | inl t_mem => apply False.elim; exact cb.func_term_not_mem_head (PreTrigger.term_functional_of_mem_fresh_terms _ t_mem_trg) t_mem
  | inr t_mem => exact t_mem

/-- If a functional term occurs in the chase, then the result of the trigger that introduces this term is contained in the current node. -/
theorem result_of_trigger_introducing_functional_term_occurs_in_chase
    {cb : RegularChaseBranch obs kb}
    (node : cb.Node)
    {t : GroundTerm sig}
    (t_mem_node : t ∈ node.val.facts.terms)
    {trg : RTrigger obs kb.rules}
    {disj_idx : Nat}
    {lt : disj_idx < trg.val.rule.head.length}
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
    (trg.val.mapped_head[disj_idx]'(by rw [PreTrigger.length_mapped_head]; exact lt)).toSet ⊆ node.val.facts := by
  cases RegularChaseDerivation.result_of_trigger_introducing_functional_term_occurs_in_chase node t_mem_node t_mem_trg with
  | inl t_mem => apply False.elim; exact cb.func_term_not_mem_head (PreTrigger.term_functional_of_mem_fresh_terms _ t_mem_trg) t_mem
  | inr t_mem => exact t_mem

end RegularChaseBranch

