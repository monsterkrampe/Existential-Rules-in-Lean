/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.KoenigsLemma

public import ExistentialRules.ChaseSequence.ChaseTree

/-!
# Chase Termination

We introduce basic definitions and theorems around chase termination.
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

section Definitions

/-- A `ChaseDerivationSkeleton` terminates if the underlying `PossiblyInfiniteList` is finite. -/
@[expose]
def ChaseDerivationSkeleton.terminates {obs : ObsolescenceCondition sig} {rules : RuleSet sig} {N : Type u} [CN : ChaseNode N obs rules]
  (cds : ChaseDerivationSkeleton N obs rules) : Prop := cds.branch.finite

/-- A `ChaseDerivationSkeleton` terminates if and only if its suffixes terminate. -/
theorem ChaseDerivationSkeleton.terminates_iff_terminates_suffix
    {obs : ObsolescenceCondition sig} {rules : RuleSet sig} {N : Type u} [CN : ChaseNode N obs rules]
    {cd cd2 : ChaseDerivationSkeleton N obs rules} (suf : cd2 <:+ cd) : cd.terminates ↔ cd2.terminates := by
  rw [IsSuffix_iff] at suf; rcases suf with ⟨m, suf⟩
  constructor
  . intro ⟨n, eq_none⟩
    exists n - m
    rw [← suf, PossiblyInfiniteList.get?_drop];
    apply PossiblyInfiniteList.get?_eq_none_of_le_of_eq_none eq_none
    grind
  . intro ⟨n, eq_none⟩
    exists m + n
    rw [← PossiblyInfiniteList.get?_drop, suf]; exact eq_none

/-- A `ChaseDerivation` terminates if the underlying `ChaseDerivationSkeleton` is finite. -/
@[expose]
def ChaseDerivation.terminates {obs : ObsolescenceCondition sig} {rules : RuleSet sig} {N : Type u} [CN : ChaseNode N obs rules]
  (cd : ChaseDerivation N obs rules) : Prop := cd.toChaseDerivationSkeleton.terminates

/-- A `TreeDerivation` terminates if all of its branches terminate. -/
@[expose]
def TreeDerivation.terminates {obs : ObsolescenceCondition sig} {rules : RuleSet sig} {N : Type u} [CN : ChaseNode N obs rules]
  (td : TreeDerivation N obs rules) : Prop := ∀ branch, branch ∈ td.branches -> branch.terminates

/-- A `KnowledgeBase` terminates if all of its `ChaseTree`s terminate. -/
@[expose]
def KnowledgeBase.terminates (kb : KnowledgeBase sig) (obs : ObsolescenceCondition sig) (N : Type u) [CN : ChaseNode N obs kb.rules] : Prop :=
  ∀ (ct : ChaseTree N obs kb), ct.terminates

/-- A `RuleSet` terminates if all knowledge bases featuring this rule set terminate. -/
@[expose]
def RuleSet.terminates (rs : RuleSet sig) (obs : ObsolescenceCondition sig) (N : Type u) [CN : ChaseNode N obs rs] : Prop :=
  ∀ (db : Database sig), { rules := rs, db := db : KnowledgeBase sig }.terminates obs N

end Definitions


section LastChaseElement

/-!
## Last Chase Element

For terminating derivations, we define machinery to get the last chase node from the derivation.
-/

namespace ChaseDerivationSkeleton

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig}
variable {N : Type u} [CN : ChaseNode N obs rules]

/-- For terminating derivations, we define the last chase node via turning the derivation into a finite list and then retreiving the last element. -/
def last (cd : ChaseDerivationSkeleton N obs rules) (term : cd.terminates) : N := (cd.branch.toList_of_finite term).getLast (by
  intro contra
  rw [PossiblyInfiniteList.toList_of_finite_empty_iff, PossiblyInfiniteList.empty_iff_head_none] at contra
  have head_some := cd.isSome_head
  simp [contra] at head_some)

/-- The `last` node is a member of the derivation. -/
theorem last_mem {cd : ChaseDerivationSkeleton N obs rules} (term : cd.terminates) : cd.last term ∈ cd := by
  suffices cd.last term ∈ cd.branch.toList_of_finite term by rw [PossiblyInfiniteList.mem_toList_of_finite] at this; exact this
  simp [last]

/-- All suffixes have the same last node. -/
theorem last_eq_of_suffix {cd cd2 : ChaseDerivationSkeleton N obs rules} (suf : cd2 <:+ cd) (term : cd.terminates) :
    cd.last term = cd2.last ((terminates_iff_terminates_suffix suf).mp term) := by
  apply Eq.symm; apply List.IsSuffix.getLast
  have cd2_fin := ((terminates_iff_terminates_suffix suf).mp term)
  rw [IsSuffix_iff] at suf; rcases suf with ⟨m, suf⟩
  suffices cd2.branch.toList_of_finite cd2_fin = (cd.branch.toList_of_finite term).drop m by
    rw [this]; apply List.drop_suffix
  simp only [← suf]
  apply List.ext_getElem?; intro i; simp

/-- Every node is a predecessor of the last one. -/
theorem each_prec_last {cd : ChaseDerivationSkeleton N obs rules} (term : cd.terminates) : ∀ (node : cd.Node), node ≼ ⟨cd.last term, cd.last_mem term⟩ := by
  intro node; rcases cd.subderivation_of_node_mem node.property with ⟨cd2, head_eq, suf⟩
  exists cd2; constructor; exact suf; constructor; exact head_eq
  simp only; rw [last_eq_of_suffix suf]; exact cd2.last_mem _

end ChaseDerivationSkeleton

namespace RegularChaseDerivationSkeleton

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig}

/-- For terminating derivations, the result is equal to the facts of the last node. -/
theorem result_eq_facts_last {cd : RegularChaseDerivationSkeleton obs rules} (term : cd.terminates) : cd.result = (cd.last term).facts := by
  apply Set.ext; intro f; constructor
  . intro ⟨node, node_mem, f_mem⟩
    let node : cd.Node := ⟨node, node_mem⟩
    apply cd.facts_node_subset_of_prec (cd.each_prec_last term node)
    exact f_mem
  . apply cd.facts_node_subset_result _ (cd.last_mem term)

end RegularChaseDerivationSkeleton

namespace ChaseDerivation

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig}
variable {N : Type u} [CN : ChaseNode N obs rules]

/-- No trigger is active on the last node. -/
theorem trg_inactive_for_last {cd : ChaseDerivation N obs rules} (term : cd.terminates) :
    ∀ (trg : RTrigger obs rules), ¬ trg.val.active (CN.outgoingFacts (cd.last term)) := by
  intro trg
  rcases cd.fairness' trg with ⟨cd2, suf, fair⟩
  apply fair
  rw [cd.last_eq_of_suffix suf]; exact cd2.last_mem _

end ChaseDerivation

end LastChaseElement


section GeneralResults

/-!
We now show some general results mainly relating termination and finiteness of the chase result.
-/

namespace RegularChaseDerivation

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig}

/-- A `ChaseDerivation` terminates if and only if there is a maximal node according to the `≼` relation. -/
theorem terminating_has_last_node (cd : RegularChaseDerivation obs rules) : cd.terminates ↔ ∃ (node : cd.Node), ∀ (node2 : cd.Node), node2 ≼ node := by
  constructor
  . intro term
    exists ⟨cd.last term, cd.last_mem term⟩
    apply cd.each_prec_last
  . rintro ⟨node, all_pred⟩
    rcases node.property with ⟨n, node_eq⟩
    exists n+1
    apply Decidable.byContradiction
    intro ne_none
    rw [← ne_eq, Option.ne_none_iff_exists'] at ne_none
    rcases ne_none with ⟨next, next_eq⟩
    let next_node : cd.Node := ⟨next, by exists n+1⟩
    specialize all_pred next_node
    let d1 := cd.derivation_for_branch_suffix (cd.branch.drop n) (cd.branch.IsSuffix_drop n) (by simp [PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?, node_eq])
    have head_eq1 : d1.head = node.val := by simp [d1, ChaseDerivationSkeleton.derivation_for_branch_suffix, ChaseDerivationSkeleton.head, PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?, node_eq]
    have suf1 : d1 <:+ cd.toChaseDerivationSkeleton := (cd.branch.IsSuffix_drop n)
    have next_d1 : d1.next = some next := by rw [← next_eq]; simp [d1, ChaseDerivationSkeleton.derivation_for_branch_suffix, ChaseDerivationSkeleton.next, PossiblyInfiniteList.tail_drop, PossiblyInfiniteList.head_drop]
    have node_pred_next : node ≼ next_node := by exists d1; simp only [head_eq1, suf1, true_and]; apply d1.next_mem_of_mem; exact next_d1
    have node_eq_next : node = next_node := cd.predecessor_antisymm node_pred_next all_pred
    apply RegularChaseDerivation.head_not_mem_tail (cd := cd.derivation_for_skeleton d1 suf1)
    . simp only [ChaseDerivation.derivation_for_skeleton, ChaseDerivation.tail]
      rw [ChaseDerivation.mem_def, d1.mem_tail_iff]
      exists d1; constructor; exact d1.branch.IsSuffix_refl; rw [next_d1, head_eq1, node_eq_next]
    . simp [ChaseDerivation.derivation_for_skeleton, next_d1]

end RegularChaseDerivation

namespace RegularChaseBranch

variable {obs : ObsolescenceCondition sig} {kb : KnowledgeBase sig}

/-- A `ChaseBranch` terminates if and only if its result is `Set.finite`. -/
theorem terminates_iff_result_finite (cb : RegularChaseBranch obs kb) : cb.terminates ↔ cb.result.finite := by
  constructor
  . intro terminates
    unfold result
    rw [RegularChaseDerivationSkeleton.result_eq_facts_last terminates]
    let node : cb.Node := ⟨cb.last terminates, cb.last_mem terminates⟩
    apply cb.facts_finite_of_mem node
  . rintro ⟨l, _, l_eq⟩
    rw [RegularChaseDerivation.terminating_has_last_node]
    rcases RegularChaseDerivationSkeleton.facts_mem_some_node_of_mem_result l (by intro _ mem; rw [List.mem_toSet, l_eq] at mem; exact mem) with ⟨node, node_mem, l_sub⟩
    exists ⟨node, node_mem⟩
    intro node2
    cases cb.predecessor_total ⟨node, node_mem⟩ node2 with
    | inr prec => exact prec
    | inl prec =>
      cases cb.eq_or_strict_of_predecessor prec with
      | inl eq => rw [eq]; apply cb.predecessor_refl
      | inr prec =>
        apply False.elim; apply RegularChaseDerivation.facts_not_subset_of_strict_predecessor prec
        apply Set.subset_trans _ l_sub
        intro e e_mem; rw [List.mem_toSet, l_eq]
        apply (RegularChaseDerivationSkeleton.facts_node_subset_result _ node2.property)
        exact e_mem

end RegularChaseBranch

namespace TreeDerivation

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig}

/-- A terminating `TreeDerivation` only has finitely many branches. We show this using König's Lemma. -/
@[grind ->]
theorem branches_finite_of_terminates {N : Type u} [CN : ChaseNode N obs rules] (td : TreeDerivation N obs rules) : td.terminates -> td.branches.finite := by
  intro each_b_term

  have : ∀ b, b ∈ td.tree.branches -> b.finite := by
    intro b b_mem
    exact each_b_term (td.derivation_for_branch b b_mem) b_mem

  -- Koenig's Lemma
  rcases (td.tree.branches_finite_of_each_branch_finite this) with ⟨l, _, l_eq⟩

  have decEq := Classical.typeDecidableEq (ChaseDerivation N obs rules)
  apply Set.finite_of_list_with_same_elements (l.attach.map (fun ⟨b, b_mem⟩ => td.derivation_for_branch b (by rw [← l_eq]; exact b_mem)))

  intro branch
  unfold branches
  simp only [List.mem_map, List.mem_attach, true_and]
  constructor
  . rintro ⟨⟨b, b_mem⟩, branch_eq⟩; simp only [← branch_eq, ← l_eq]; exact b_mem
  . intro branch_mem; exists ⟨branch.branch, by rw [l_eq]; exact branch_mem⟩

end TreeDerivation

namespace RegularTreeDerivation

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig}

/-- A `TreeDerivation` with finitely many branches only has finitely many fact sets in its result. -/
@[grind ->]
theorem result_finite_of_branches_finite (td : RegularTreeDerivation obs rules) : td.branches.finite -> td.result.finite := by
  rintro ⟨l, _, iff⟩
  have : DecidableEq (FactSet sig) := Classical.typeDecidableEq (FactSet sig)
  apply Set.finite_of_list_with_same_elements (l.map RegularChaseDerivation.result)
  intro fs
  rw [List.mem_map]
  constructor
  . intro ⟨b, mem, eq⟩
    unfold result; rw [Set.mem_map]
    exists b; grind
  . unfold result; rw [Set.mem_map]
    intro ⟨b, mem, eq⟩
    exists b; grind

end RegularTreeDerivation

namespace RegularChaseTree

variable {obs : ObsolescenceCondition sig} {kb : KnowledgeBase sig}

/-- A `ChaseTree` terminates if and only if each fact set in its result is finite. -/
theorem terminates_iff_result_finite (ct : RegularChaseTree obs kb) :
    ct.terminates ↔ ∀ fs, fs ∈ ct.result -> fs.finite := by
  constructor
  . intro each_b_term res
    unfold RegularChaseTree.result RegularTreeDerivation.result; rw [Set.mem_map]
    intro ⟨b, mem, eq⟩
    let b' := ChaseTree.chaseBranch_for_branch mem
    have : RegularChaseBranch.result b' = RegularChaseDerivation.result b := rfl
    simp only [← eq, ← this]
    rw [← RegularChaseBranch.terminates_iff_result_finite]
    apply each_b_term
    exact mem
  . intro each_b_term b mem
    let b' := ChaseTree.chaseBranch_for_branch mem
    have : b'.terminates ↔ b.terminates := by rfl
    rw [← this]
    rw [RegularChaseBranch.terminates_iff_result_finite]
    apply each_b_term
    unfold RegularChaseTree.result RegularTreeDerivation.result; rw [Set.mem_map]
    exists b

end RegularChaseTree

end GeneralResults

