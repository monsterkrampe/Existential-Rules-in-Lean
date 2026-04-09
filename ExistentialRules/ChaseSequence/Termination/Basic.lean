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
def ChaseDerivationSkeleton.terminates {obs : ObsoletenessCondition sig} {rules : RuleSet sig} (cds : ChaseDerivationSkeleton obs rules) : Prop := cds.branch.finite

/-- A `ChaseDerivation` terminates if the underlying `ChaseDerivationSkeleton` is finite. -/
@[expose]
def ChaseDerivation.terminates {obs : ObsoletenessCondition sig} {rules : RuleSet sig} (cd : ChaseDerivation obs rules) : Prop := cd.toChaseDerivationSkeleton.terminates

/-- A `TreeDerivation` terminates if all of its branches terminate. -/
@[expose]
def TreeDerivation.terminates {obs : ObsoletenessCondition sig} {rules : RuleSet sig} (td : TreeDerivation obs rules) : Prop := ∀ branch, branch ∈ td.branches -> branch.terminates

/-- A `KnowledgeBase` terminates if all of its `ChaseTree`s terminate. -/
@[expose]
def KnowledgeBase.terminates (kb : KnowledgeBase sig) (obs : ObsoletenessCondition sig) : Prop := ∀ (ct : ChaseTree obs kb), ct.terminates

/-- A `RuleSet` terminates if all knowledge bases featuring this rule set terminate. -/
@[expose]
def RuleSet.terminates (rs : RuleSet sig) (obs : ObsoletenessCondition sig) : Prop := ∀ (db : Database sig), { rules := rs, db := db : KnowledgeBase sig }.terminates obs

end Definitions

section GeneralResults

namespace ChaseDerivationSkeleton

variable {obs : ObsoletenessCondition sig} {rules : RuleSet sig}

/-- If a `ChaseDerivationSkeleton` terminates, then there is a maximal node according to the `≼` relation. -/
theorem has_last_node_of_terminates (cds : ChaseDerivationSkeleton obs rules) :
    cds.terminates -> ∃ (node : cds.Node), ∀ (node2 : cds.Node), node2 ≼ node := by
  rintro ⟨n, h⟩
  induction n with
  | zero => have contra := cds.isSome_head; rw [PossiblyInfiniteList.head_eq, h] at contra; simp at contra
  | succ n ih =>
    cases eq : cds.branch.get? n with
    | none => apply ih; exact eq
    | some node =>
      let node : cds.Node := ⟨node, by exists n⟩
      exists node
      intro node2
      -- TODO: Maybe it helps that ≼ is total here but this is tricky since right now we depend on the specific d1..
      let d1 := cds.derivation_for_branch_suffix (cds.branch.drop n) (cds.branch.IsSuffix_drop n) (by rw [PossiblyInfiniteList.head_drop]; simp [eq])
      have head_eq1 : d1.head = node.val := by simp [d1, derivation_for_branch_suffix, head, PossiblyInfiniteList.head_drop, eq, node]
      have suf1 : d1 <:+ cds := (cds.branch.IsSuffix_drop n)
      rcases subderivation_of_node_mem node2.property with ⟨d2, head_eq2, suf2⟩
      cases PossiblyInfiniteList.suffix_or_suffix_of_suffix suf1 suf2 with
      | inl suf3 => exists d2; constructor; exact suf2; simp only [head_eq2, true_and]; apply d1.mem_of_mem_suffix suf3; rw [← head_eq1]; exact d1.head_mem
      | inr suf3 =>
        cases suffix_iff_eq_or_suffix_tail.mp suf3 with
        | inl suf3 =>
          have : node = node2 := by rw [Subtype.mk.injEq, ← head_eq2, suf3, head_eq1]
          rw [this]
          exact predecessor_refl
        | inr suf3 =>
          rcases suf3 with ⟨contra, suf3⟩
          apply False.elim
          unfold next at contra
          rw [Option.isSome_iff_ne_none] at contra
          apply contra
          simp only [d1, derivation_for_branch_suffix, PossiblyInfiniteList.tail_drop, PossiblyInfiniteList.head_drop]
          exact h

end ChaseDerivationSkeleton

namespace ChaseDerivation

variable {obs : ObsoletenessCondition sig} {rules : RuleSet sig}

/-- A `ChaseDerivation` terminates if and only if there is a maximal node according to the `≼` relation. -/
theorem terminating_has_last_node (cd : ChaseDerivation obs rules) : cd.terminates ↔ ∃ (node : cd.Node), ∀ (node2 : cd.Node), node2 ≼ node := by
  constructor
  . exact cd.toChaseDerivationSkeleton.has_last_node_of_terminates
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
    apply (cd.derivation_for_skeleton d1 suf1).head_not_mem_tail
    . simp only [derivation_for_skeleton, tail]
      rw [mem_def, d1.mem_tail_iff]
      exists d1; constructor; exact d1.branch.IsSuffix_refl; rw [next_d1, head_eq1, node_eq_next]
    . simp [derivation_for_skeleton, next_d1]

end ChaseDerivation

namespace ChaseBranch

variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

/-- A `ChaseBranch` terminates if and only if its result is `Set.finite`. -/
theorem terminates_iff_result_finite (cb : ChaseBranch obs kb) : cb.terminates ↔ cb.result.finite := by
  constructor
  . intro terminates
    rcases cb.terminating_has_last_node.mp terminates with ⟨node, all_pred⟩
    have : cb.result ⊆ node.val.facts := by
      rintro f ⟨node2, node2_mem, f_mem⟩
      apply cb.facts_node_subset_of_prec (all_pred ⟨node2, node2_mem⟩)
      exact f_mem
    apply Set.finite_of_subset_finite _ this
    apply cb.facts_finite_of_mem
  . rintro ⟨l, _, l_eq⟩
    rw [cb.terminating_has_last_node]
    rcases cb.facts_mem_some_node_of_mem_result l (by intro _ mem; rw [List.mem_toSet, l_eq] at mem; exact mem) with ⟨node, node_mem, l_sub⟩
    exists ⟨node, node_mem⟩
    intro node2
    cases cb.predecessor_total ⟨node, node_mem⟩ node2 with
    | inr prec => exact prec
    | inl prec =>
      cases cb.eq_or_strict_of_predecessor prec with
      | inl eq => rw [eq]; apply cb.predecessor_refl
      | inr prec =>
        apply False.elim; apply cb.facts_not_subset_of_strict_predecessor prec
        apply Set.subset_trans _ l_sub
        intro e e_mem; rw [List.mem_toSet, l_eq]
        apply (cb.facts_node_subset_result _ node2.property)
        exact e_mem

end ChaseBranch

namespace TreeDerivation

variable {obs : ObsoletenessCondition sig} {rules : RuleSet sig}

/-- A terminating `TreeDerivation` only has finitely many branches. We show this using König's Lemma. -/
@[grind ->]
theorem branches_finite_of_terminates (td : TreeDerivation obs rules) : td.terminates -> td.branches.finite := by
  intro each_b_term

  have : ∀ b, b ∈ td.tree.branches -> b.finite := by
    intro b b_mem
    exact each_b_term (td.derivation_for_branch b b_mem) b_mem

  -- Koenig's Lemma
  rcases (td.tree.branches_finite_of_each_branch_finite this) with ⟨l, _, l_eq⟩

  have decEq := Classical.typeDecidableEq (ChaseDerivation obs rules)
  apply Set.finite_of_list_with_same_elements (l.attach.map (fun ⟨b, b_mem⟩ => td.derivation_for_branch b (by rw [← l_eq]; exact b_mem)))

  intro branch
  unfold branches
  simp only [List.mem_map, List.mem_attach, true_and]
  constructor
  . rintro ⟨⟨b, b_mem⟩, branch_eq⟩; simp only [← branch_eq, ← l_eq]; exact b_mem
  . intro branch_mem; exists ⟨branch.branch, by rw [l_eq]; exact branch_mem⟩

/-- A `TreeDerivation` with finitely many branches only has finitely many fact sets in its result. -/
@[grind ->]
theorem result_finite_of_branches_finite (td : TreeDerivation obs rules) : td.branches.finite -> td.result.finite := by
  rintro ⟨l, _, iff⟩
  have : DecidableEq (FactSet sig) := Classical.typeDecidableEq (FactSet sig)
  apply Set.finite_of_list_with_same_elements (l.map (fun deriv => deriv.result))
  intro fs
  rw [List.mem_map]
  constructor
  . intro ⟨b, mem, eq⟩
    unfold result; rw [Set.mem_map]
    exists b; grind
  . unfold result; rw [Set.mem_map]
    intro ⟨b, mem, eq⟩
    exists b; grind

end TreeDerivation

namespace ChaseTree

variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

/-- A `ChaseTree` terminates if and only if each fact set in its result is finite. -/
theorem terminates_iff_result_finite (ct : ChaseTree obs kb) : ct.terminates ↔ ∀ fs, fs ∈ ct.result -> fs.finite := by
  constructor
  . intro each_b_term res
    unfold TreeDerivation.result; rw [Set.mem_map]
    intro ⟨b, mem, eq⟩
    let b' := ChaseTree.chaseBranch_for_branch mem
    have : b'.result = b.result := rfl
    simp only [← eq, ← this]
    rw [← ChaseBranch.terminates_iff_result_finite]
    apply each_b_term
    exact mem
  . intro each_b_term b mem
    let b' := ChaseTree.chaseBranch_for_branch mem
    have : b'.terminates ↔ b.terminates := by rfl
    rw [← this]
    rw [ChaseBranch.terminates_iff_result_finite]
    apply each_b_term
    unfold TreeDerivation.result; rw [Set.mem_map]
    exists b

end ChaseTree

end GeneralResults

