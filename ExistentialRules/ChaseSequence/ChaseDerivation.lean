/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

import BasicLeanDatastructures.Nat

public import ExistentialRules.Models.Basic
public import ExistentialRules.ChaseSequence.ChaseDerivationSkeleton

/-!
# Chase Derivation

Now we go from a `ChaseDerivationSkeleton` to a `ChaseDerivation`.

The chase starts on an initial fact set and then applies triggers until all triggers are obsolete, which might only be the case after infinitely many steps.
This whole process needs to be "fair", i.e. a trigger that is `Trigger.active` needs to be not active after finitely many steps. This can happen by applying the trigger itself or another trigger that will make the former obsolete.

We should note that chase derivations usually start on a `Database`, i.e. a finite fact set where all terms are constants.
This is what we demand for a `ChaseBranch` later but for now it is more convenient for us to relax this condition since it is not relevant for
most basic definitions and results.
What we gain by relaxing the condition is that we can drop an abitrary number of `ChaseNode`s from the beginning of a derivation and still be left with a derivation. This gives the `ChaseDerivation` a more coinductive behavior that conveniently alignes with the `PossiblyInfiniteList` that is used to provide the basic structure of the derivation skeleton.

The goal of the chase is to eventually build a most general (i.e. universal) model of a given `KnowledgeBase` by iteratively satisfying all triggers and thereby all rules.
For the more generic `ChaseDerivation`, we cannot quite expect this as a result but we can already show that the `ChaseDerivationSkeleton.result` models all of the rules in `ChaseDerivation.result_models_rules`.
-/

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-!
## The ChaseDerivation Structure

The backbone of the `ChaseDerivation` is a `ChaseDerivationSkeleton` with additional conditions.

1. Each trigger used in the derivation must be active for the previous fact set.
2. The derivation needs to be fair. That is, for each trigger, there exists a step in the derivation from which on the trigger is not active.

Expressing the conditions in terms of the machinery available form the `PossiblyInfiniteList` is admittedly quite convoluted.
As part of the framework built around the `ChaseDerivation`, we will also restate these conditions in a more accessible way. See e.g. `ChaseDerivation.fairness'`.
-/

public structure ChaseDerivation (N : Type u) (obs : ObsolescenceCondition sig) (rules : RuleSet sig) [CN : ChaseNode N obs rules] extends ChaseDerivationSkeleton N obs rules where
  triggers_active : ∀ n : Nat, ∀ before ∈ (branch.drop n).head,
    ∀ after ∈ (branch.drop n).tail.head, ∃ orig ∈ CN.origin after, orig.fst.val.active (CN.outgoingFacts before)
  fairness : ∀ trg : (RTrigger obs rules), ∃ i : Nat, (∃ node ∈ (branch.drop i).head, ¬ trg.val.active (CN.outgoingFacts node))
    ∧ (∀ j : Nat, ∀ node2 ∈ (branch.drop i).tail.get? j, ¬ trg.val.active (CN.outgoingFacts node2))

namespace ChaseDerivation

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig}

public section Basics

variable {N : Type u} [CN : ChaseNode N obs rules]

/-!
## Basic Definitions

Here we introduce some auxiliary definitions and theorems and we lift some of the machinery of the underlying `PossiblyInfiniteList` to `ChaseDerivation`. Some have already been lifted to `ChaseDerivationSkeleton`.
-/

/-- Membership of `ChaseNode`s in the `ChaseDerivation` directly corresponds to membership in the `ChaseDerivationSkeleton`. -/
instance : Membership N (ChaseDerivation N obs rules) where
  mem cd node := node ∈ cd.toChaseDerivationSkeleton

/-- Unfolds the Membership definition. -/
theorem mem_def {cd : ChaseDerivation N obs rules} : ∀ {e}, e ∈ cd ↔ e ∈ cd.toChaseDerivationSkeleton := by rfl

/-- An element is a member of the derivation iff it occurs at some index in the underlying branch. -/
theorem mem_iff {cd : ChaseDerivation N obs rules} : ∀ {e}, e ∈ cd ↔ ∃ n, cd.branch.get? n = some e := ChaseDerivationSkeleton.mem_iff

/-- Each suffix of the underlying `ChaseDerivationSkeleton` is itself a `ChaseDerivation`. -/
@[expose]
def derivation_for_skeleton
    (cd : ChaseDerivation N obs rules)
    (l2 : ChaseDerivationSkeleton N obs rules)
    (suffix : l2 <:+ cd.toChaseDerivationSkeleton) :
    ChaseDerivation N obs rules where
  branch := l2.branch
  isSome_head := l2.isSome_head
  triggers_exist := l2.triggers_exist
  triggers_active := by
    rw [ChaseDerivationSkeleton.IsSuffix_iff] at suffix
    rcases suffix with ⟨m, suffix⟩
    rw [← suffix]
    intro n
    have := cd.triggers_active (m + n)
    simp only [PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?_drop, PossiblyInfiniteList.tail_drop] at *
    exact this
  fairness := by
    have l2_head_some := l2.isSome_head
    rw [Option.isSome_iff_exists] at l2_head_some; rcases l2_head_some with ⟨l2_head, l2_head_eq⟩
    rw [ChaseDerivationSkeleton.IsSuffix_iff] at suffix
    rcases suffix with ⟨m, suffix⟩
    rw [← suffix]
    intro trg
    rcases cd.fairness trg with ⟨i, fairness⟩
    cases Decidable.em (i < m) with
    | inl lt =>
      rcases Nat.exists_eq_add_of_lt lt with ⟨diff, lt⟩
      exists 0
      constructor
      . exists l2_head
        constructor
        . grind
        . apply (fairness.right diff)
          grind
      . intro j
        have fairness := fairness.right (diff.succ + j)
        simp only [PossiblyInfiniteList.drop_zero, PossiblyInfiniteList.get?_tail, PossiblyInfiniteList.get?_drop] at *
        have : (i + diff + 1 + j.succ) = (i + (diff.succ + j).succ) := by omega
        rw [lt, this]
        exact fairness
    | inr le =>
      have le := Nat.le_of_not_lt le
      simp only [PossiblyInfiniteList.tail_drop, PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?_drop, Nat.succ_add] at *
      exists (i - m)
      simp only [← Nat.add_succ, ← Nat.add_assoc, Nat.add_sub_of_le le] at *
      exact fairness

section Next

/-!
### The "next" ChaseNode

Compared to the `ChaseDerivationSkeleton` we can show some additional results for `next`.
-/

/-- The trigger used to derive `ChaseDerivationSkeleton.next` is active for `ChaseDerivationSkeleton.head`. -/
@[grind ->]
theorem active_trigger_origin_next {cd : ChaseDerivation N obs rules} {next : N} (eq : cd.next = some next) :
    ((CN.origin next).get (cd.isSome_origin_next eq)).fst.val.active (CN.outgoingFacts cd.head) := by
  have trg_act := cd.triggers_active 0 cd.head (by simp [ChaseDerivationSkeleton.head]) next (by simp [← eq, ChaseDerivationSkeleton.next])
  rcases trg_act with ⟨orig, orig_mem, trg_act⟩
  rw [Option.mem_def] at orig_mem
  simp only [orig_mem, Option.get_some]
  exact trg_act

/-- The `ChaseDerivationSkeleton.next` node is not none if and only if some trigger is active on `ChaseDerivationSkeleton.head`. -/
theorem isSome_next_iff_trg_ex {cd : ChaseDerivation N obs rules} : cd.next.isSome ↔ ∃ (trg : RTrigger obs rules), trg.val.active (CN.outgoingFacts cd.head) := by
  constructor
  . rw [Option.isSome_iff_exists]
    rintro ⟨next, eq⟩
    exists ((CN.origin next).get (cd.isSome_origin_next eq)).fst
    exact active_trigger_origin_next eq
  . rintro ⟨trg, active⟩
    apply Decidable.byContradiction
    rw [Option.not_isSome_iff_eq_none]
    intro eq_none
    have fair := cd.fairness trg
    rcases cd.fairness trg with ⟨i, ⟨node, node_mem, not_active⟩, fair⟩
    cases i with
    | zero =>
      apply not_active
      have eq : cd.head = node := by unfold ChaseDerivationSkeleton.head; rw [Option.mem_def] at node_mem; grind
      rw [← eq]
      exact active
    | succ i =>
      simp only [ChaseDerivationSkeleton.next, ← PossiblyInfiniteList.empty_iff_head_none] at eq_none
      rw [PossiblyInfiniteList.head_drop, ← PossiblyInfiniteList.get?_tail, eq_none] at node_mem
      simp at node_mem

end Next

section Suffixes

/-!
### ChaseDerivation Suffixes

Suffixes on `ChaseDerivation`s allow us to state the fairness condition more nicely.
-/

@[expose]
def IsSuffix (cd1 cd2 : ChaseDerivation N obs rules) : Prop := ChaseDerivationSkeleton.IsSuffix cd1.toChaseDerivationSkeleton cd2.toChaseDerivationSkeleton
infixl:50 " <:+ " => IsSuffix

/-- Members of our suffix are also our members. -/
@[grind ->]
theorem mem_of_mem_suffix {cd1 cd2 : ChaseDerivation N obs rules} (suffix : cd1 <:+ cd2) : ∀ node ∈ cd1, node ∈ cd2 :=
  ChaseDerivationSkeleton.mem_of_mem_suffix suffix

/-- Each `ChaseNode` in the `ChaseDerivation` induces a subderivation. -/
theorem subderivation_of_node_mem {cd : ChaseDerivation N obs rules} {node : N} (node_mem : node ∈ cd) :
    ∃ (cd2 : ChaseDerivation N obs rules), cd2.head = node ∧ cd2 <:+ cd := by
  rcases cd.toChaseDerivationSkeleton.subderivation_of_node_mem node_mem with ⟨cds2, head_eq, suffix⟩
  exists cd.derivation_for_skeleton cds2 suffix

/-- Fairness can be stated as: For each trigger, there exists a subderivation such that the trigger is not active for all nodes in the subderivation. -/
theorem fairness' {cd : ChaseDerivation N obs rules} :
    ∀ (trg : RTrigger obs rules), ∃ (cd2 : ChaseDerivation N obs rules), cd2 <:+ cd ∧ ∀ node ∈ cd2, ¬ trg.val.active (CN.outgoingFacts node) := by
  intro trg
  rcases cd.fairness trg with ⟨n, ⟨node, node_mem, fairness_head⟩, fairness_tail⟩
  let cds2 := cd.derivation_for_branch_suffix (cd.branch.drop n) (cd.branch.IsSuffix_drop n) (by rw [node_mem]; simp)
  let cd2 := cd.derivation_for_skeleton cds2 (cd.branch.IsSuffix_drop n)
  exists cd2
  constructor
  . exact cd.branch.IsSuffix_drop n
  . intro node2 node2_mem
    rw [mem_iff] at node2_mem
    rcases node2_mem with ⟨m, node2_mem⟩
    simp only [cd2, derivation_for_skeleton, cds2, ChaseDerivationSkeleton.derivation_for_branch_suffix] at node2_mem
    cases m with
    | zero => grind
    | succ m => apply fairness_tail m; grind

end Suffixes

section Tail

/-!
### Tail
-/

@[expose]
def tail (cd : ChaseDerivation N obs rules) (next_some : cd.next.isSome) : ChaseDerivation N obs rules :=
  cd.derivation_for_skeleton (ChaseDerivationSkeleton.tail cd.toChaseDerivationSkeleton next_some) (cd.branch.IsSuffix_tail)

/-- The `ChaseDerivationSkeleton.head` of the `tail` is `ChaseDerivationSkeleton.next`. -/
theorem head_tail {cd : ChaseDerivation N obs rules} {next_some : cd.next.isSome} : some (cd.tail next_some).head = cd.next :=
  ChaseDerivationSkeleton.head_tail

/-- The `ChaseDerivationSkeleton.head` of the `tail` is `ChaseDerivationSkeleton.next`. -/
@[simp, grind =]
theorem head_tail' {cd : ChaseDerivation N obs rules} {next_some : cd.next.isSome} : (cd.tail next_some).head = cd.next.get next_some :=
  ChaseDerivationSkeleton.head_tail'

/-- `ChaseDerivationSkeleton.next` is a member of the `tail`. -/
@[grind ->]
theorem next_mem_tail {cd : ChaseDerivation N obs rules} {next_some : cd.next.isSome} : ∀ next ∈ cd.next, next ∈ cd.tail next_some :=
  ChaseDerivationSkeleton.next_mem_tail

/-- A node is a member if and only if it is either the head or it is a member of the tail. -/
theorem mem_iff_eq_head_or_mem_tail {cd : ChaseDerivation N obs rules} {node : N} : node ∈ cd ↔ node = cd.head ∨ ∃ h, node ∈ cd.tail h :=
  ChaseDerivationSkeleton.mem_iff_eq_head_or_mem_tail

/-- A derivation is a suffix of another if and only if both are the same or the first is a suffix of the second's tail. -/
theorem suffix_iff_eq_or_suffix_tail {cd1 cd2 : ChaseDerivation N obs rules} : cd1 <:+ cd2 ↔ cd1 = cd2 ∨ ∃ h, cd1 <:+ cd2.tail h := by
  simp only [IsSuffix]
  rw [ChaseDerivationSkeleton.suffix_iff_eq_or_suffix_tail]
  rw [ChaseDerivation.mk.injEq]
  rfl

end Tail

section InductionPrinciple

/-!
### Induction Principle for Members

We lift `ChaseDerivationSkeleton.mem_rec` to `ChaseDerivation`.
-/

abbrev Node (cd : ChaseDerivation N obs rules) := { node : N // node ∈ cd}

/-- A `Node` of our suffix can be cast into our `Node` type. -/
@[expose]
def Node.cast_suffix {cd cd2 : ChaseDerivation N obs rules} (suffix : cd <:+ cd2) (node : Node cd) : Node cd2 := ⟨node.val, mem_of_mem_suffix suffix _ node.property⟩

/-- If we want to show a motive for all nodes in a derivation, it is enough to show the motive for the head and for the next node in each abitrary subderivation where the motive already holds for the head. This can be used with the induction tactic. -/
theorem mem_rec
    {cd : ChaseDerivation N obs rules}
    {motive : Node cd -> Prop}
    (head : motive ⟨cd.head, cd.head_mem⟩)
    (step : ∀ (cd2 : ChaseDerivation N obs rules), (suffix : cd2 <:+ cd) -> motive ⟨cd2.head, mem_of_mem_suffix suffix _ cd2.head_mem⟩ -> ∀ next, (next_mem : next ∈ cd2.next) -> motive ⟨next, mem_of_mem_suffix suffix _ (cd2.next_mem_of_mem _ next_mem)⟩)
    (node : Node cd) :
    motive node := by
  induction node using ChaseDerivationSkeleton.mem_rec with
  | head => exact head
  | step cds2 suffix ih next next_mem =>
    let cd2 := cd.derivation_for_skeleton cds2 suffix
    exact step cd2 suffix ih _ next_mem

/-- A node is a member of the `tail` if and only if there is a subderivation where the node is in the `ChaseDerivationSkeleton.next` position. -/
theorem mem_tail_iff {cd : ChaseDerivation N obs rules} {next_some : cd.next.isSome} {node : N} :
    node ∈ cd.tail next_some ↔ ∃ cd2, cd2 <:+ cd ∧ cd2.next = some node := by
  have : node ∈ cd.tail next_some ↔ node ∈ cd.toChaseDerivationSkeleton.tail next_some := by rfl
  rw [this, ChaseDerivationSkeleton.mem_tail_iff]
  constructor
  . rintro ⟨cds2, suf, next_mem⟩; exists cd.derivation_for_skeleton cds2 suf
  . rintro ⟨cd2, suf, next_mem⟩; exists cd2.toChaseDerivationSkeleton

end InductionPrinciple

end Basics

public section Predecessors

/-!
## Predecessor Relation

We lift the predecessor relation from `ChaseDerivationSkeleton`s to `ChaseDerivation`s.
-/

variable {N : Type u} [CN : ChaseNode N obs rules]

/-- We could also define the predecessor relation directly on `ChaseDerivation`s. This theorem shows how this would look. -/
theorem predecessor_iff {cd : ChaseDerivation N obs rules} (n1 n2 : Node cd) :
    n1 ≼ n2 ↔ ∃ cd2, cd2 <:+ cd ∧ cd2.head = n1.val ∧ n2.val ∈ cd2 := by
  constructor
  . rintro ⟨cds2, suf, head, mem⟩; exists cd.derivation_for_skeleton cds2 suf
  . rintro ⟨cd2, suf, head, mem⟩; exists cd2.toChaseDerivationSkeleton

end Predecessors

public section TermsInChase

/-!
## Terms in the Chase

We make some general observations about certain terms that might occur in the chase.

1. Constants can only originate directly from rules or from the initial fact set. No other constants can be introduced.
2. Functional terms can either also originate from the initial fact set or they are introduced as fresh terms by a trigger.

The second observation entails that the precense of a functional term that does not occur in the initial fact set implies
that the trigger that introduces this term must have been applied in some `ChaseNode`.
-/

variable {N : Type u} [CN : ChaseNode N obs rules]

/-- Constants in the chase can only come from the initial fact set or from a constant in a rule. -/
theorem constants_node_subset_constants_fs_union_constants_rules
    (out_sub_in : CN.out_sub_in)
    {cd : ChaseDerivation N obs rules}
    (start_eq : CN.ingoingFacts cd.head = CN.outgoingFacts cd.head)
    {node : N} (node_mem : node ∈ cd) :
    (CN.ingoingFacts node).constants ⊆ ((CN.outgoingFacts cd.head).constants ∪ rules.head_constants) := by
  let node' : cd.Node := ⟨node, node_mem⟩
  show (CN.ingoingFacts node'.val).constants ⊆ ((CN.outgoingFacts cd.head).constants ∪ rules.head_constants)
  induction node' using mem_rec with
  | head =>
    apply Set.subset_union_of_subset_left
    rw [start_eq]
    apply Set.subset_refl
  | step cd2 suffix ih next next_eq =>
    rw [ChaseDerivationSkeleton.facts_next next_eq]
    intro c c_mem
    rw [FactSet.constants_union] at c_mem
    cases c_mem with
    | inl c_mem => apply ih; apply FactSet.constants_subset_of_subset out_sub_in; exact c_mem
    | inr c_mem =>
      let origin := (CN.origin next).get (cd2.isSome_origin_next next_eq)
      apply Set.subset_trans (origin.fst.val.mapped_head_constants_subset origin.snd)
      . intro c c_mem
        rw [List.mem_toSet, List.mem_append] at c_mem
        cases c_mem with
        | inl c_mem =>
          apply ih
          rw [List.mem_flatMap] at c_mem
          rcases c_mem with ⟨t, t_mem, c_mem⟩
          rw [List.mem_map] at t_mem
          rcases t_mem with ⟨v, v_mem, t_mem⟩
          rcases FunctionFreeConjunction.mem_vars.mp (origin.fst.val.rule.frontier_subset_vars_body v_mem) with ⟨a, a_mem, v_mem'⟩
          exists origin.fst.val.subs.apply_function_free_atom a
          constructor
          . apply out_sub_in
            apply (cd2.active_trigger_origin_next next_eq).left
            rw [List.mem_toSet]
            apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_list
            exact a_mem
          . unfold Fact.constants
            rw [List.mem_flatMap]
            exists t
            constructor
            . unfold GroundSubstitution.apply_function_free_atom
              unfold TermMapping.apply_generalized_atom
              rw [List.mem_map]
              exists VarOrConst.var v
              constructor
              . exact v_mem'
              . unfold PreTrigger.subs_for_mapped_head at t_mem
                rw [PreTrigger.apply_to_var_or_const_frontier_var _ _ _ v_mem] at t_mem
                exact t_mem
            . exact c_mem
        | inr c_mem =>
          apply Or.inr
          exists origin.fst.val.rule
          constructor
          . exact origin.fst.property
          . unfold Rule.head_constants
            grind
      . exact c_mem

/-- Each functional term in the chase originates as a fresh term from a trigger if it was not already part of the initial fact set. -/
theorem functional_term_originates_from_some_trigger
    (out_sub_in : CN.out_sub_in)
    {cd : ChaseDerivation N obs rules}
    (start_eq : CN.ingoingFacts cd.head = CN.outgoingFacts cd.head)
    (predecessor_trans : ∀ {n1 n2 n3 : cd.Node}, n1 ≼ n2 -> n2 ≼ n3 -> n1 ≼ n3)
    (node : Node cd)
    {t : GroundTerm sig}
    (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok)
    (t_mem : t ∈ (CN.ingoingFacts node.val).terms) :
    t ∈ (CN.outgoingFacts cd.head).terms ∨ ∃ node2, node2 ≼ node ∧ ∃ orig ∈ (CN.origin node2.val), t ∈ orig.fst.val.fresh_terms_for_head_disjunct orig.snd.val (by rw [← PreTrigger.length_mapped_head]; exact orig.snd.isLt) := by
  induction node using mem_rec with
  | head => apply Or.inl; rw [← start_eq]; exact t_mem
  | step cd2 suffix ih next next_mem =>
    rw [cd2.facts_next next_mem, FactSet.terms_union] at t_mem

    have aux : t ∈ (CN.ingoingFacts cd2.head).terms -> t ∈ (CN.outgoingFacts cd.head).terms ∨ ∃ (node2 : cd.Node), node2 ≼ ⟨next, cd2.mem_of_mem_suffix suffix _ (cd2.next_mem_of_mem _ next_mem)⟩ ∧ ∃ orig ∈ (CN.origin node2.val), t ∈ orig.fst.val.fresh_terms_for_head_disjunct orig.snd.val (by rw [← PreTrigger.length_mapped_head]; exact orig.snd.isLt) := by
      intro t_mem
      cases ih t_mem with
      | inl ih => apply Or.inl; exact ih
      | inr ih =>
        rcases ih with ⟨node2, prec, t_mem⟩
        apply Or.inr; exists node2; constructor;
        . apply predecessor_trans prec
          exact ChaseDerivationSkeleton.predecessor_of_suffix suffix (ChaseDerivationSkeleton.head_prec_next next_mem)
        . exact t_mem

    cases t_mem with
    | inl t_mem => exact aux (FactSet.terms_subset_of_subset out_sub_in _ t_mem)
    | inr t_mem =>
      unfold ChaseNode.origin_result at t_mem
      rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_head_iff] at t_mem
      cases t_mem with
      | inl t_mem => rcases t_is_func with ⟨func, ts, arity, t_is_func⟩; rcases t_mem with ⟨c, _, t_mem⟩; rw [← t_mem] at t_is_func; apply False.elim; exact GroundTerm.func_neq_const (Eq.symm t_is_func)
      | inr t_mem =>
      cases t_mem with
      | inr t_mem =>
        apply Or.inr; exists ⟨next, cd2.mem_of_mem_suffix suffix _ (cd2.next_mem_of_mem _ next_mem)⟩; constructor
        . exact ChaseDerivationSkeleton.predecessor_refl
        . exists (CN.origin next).get (cd2.isSome_origin_next next_mem)
          simp only [Option.get_mem, true_and]
          exact t_mem
      | inl t_mem =>
        apply aux
        apply FactSet.terms_subset_of_subset out_sub_in
        apply FactSet.terms_subset_of_subset (cd2.active_trigger_origin_next next_mem).left
        rw [List.mem_map] at t_mem
        rcases t_mem with ⟨v, v_mem, t_mem⟩
        rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_body_iff]
        apply Or.inr
        exists v; simp only [t_mem, and_true]
        apply Rule.frontier_subset_vars_body; rw [Rule.mem_frontier_iff_mem_frontier_for_head]; exact ⟨_, ⟨_, v_mem⟩⟩

/-- If a functional term occurs in the chase, then the trigger that introduces this term must have been used in the chase, unless the term already occurs in the initial fact set. -/
theorem trigger_introducing_functional_term_occurs_in_chase
    (out_sub_in : CN.out_sub_in)
    {cd : ChaseDerivation N obs rules}
    (start_eq : CN.ingoingFacts cd.head = CN.outgoingFacts cd.head)
    (predecessor_trans : ∀ {n1 n2 n3 : cd.Node}, n1 ≼ n2 -> n2 ≼ n3 -> n1 ≼ n3)
    (node : Node cd)
    {t : GroundTerm sig}
    (t_mem_node : t ∈ (CN.ingoingFacts node.val).terms)
    {trg : RTrigger obs rules}
    {disj_idx : Nat}
    {lt : disj_idx < trg.val.rule.head.length}
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
    t ∈ (CN.outgoingFacts cd.head).terms ∨ ∃ node2, node2 ≼ node ∧ ∃ orig ∈ (CN.origin node2.val), orig.fst.equiv trg ∧ orig.snd.val = disj_idx := by
  cases functional_term_originates_from_some_trigger out_sub_in start_eq predecessor_trans node (by
    cases eq : t with
    | const _ =>
      rw [eq] at t_mem_trg
      simp [PreTrigger.fresh_terms_for_head_disjunct, PreTrigger.functional_term_for_var, GroundTerm.func_neq_const] at t_mem_trg
    | func func ts arity_ok => exists func, ts, arity_ok
  ) t_mem_node with
  | inl t_mem => apply Or.inl; exact t_mem
  | inr t_mem =>
    apply Or.inr
    rcases t_mem with ⟨node2, prec, origin, origin_eq, t_mem⟩
    exists node2; simp only [prec, true_and]
    exists origin; simp only [origin_eq, true_and]
    exact RTrigger.equiv_of_term_mem_fresh_terms_for_head_disjunct t_mem t_mem_trg

end TermsInChase

end ChaseDerivation


public abbrev RegularChaseDerivation (obs : ObsolescenceCondition sig) (rules : RuleSet sig) := ChaseDerivation (RegularChaseNode obs rules) obs rules

namespace RegularChaseDerivation

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig}

public section FactMonotonicity

/-!
## Subset Monotonicity of Facts in ChaseNodes

Compared to `ChaseDerivationSkeleton`, we get a couple of nice implications out of the subset monotonicity of fact sets. For example, we can never see the same `ChaseNode` twice as otherwise the trigger in second occurrence would already be obsolete.
-/

/-- Each member's facts contain the head facts. Note that this extends to arbitrary pairs of members since each member always induces a subderivation where it acts as the head. -/
@[grind <-]
theorem facts_node_subset_every_mem {cd : RegularChaseDerivation obs rules} : ∀ node ∈ cd, cd.head.facts ⊆ node.facts :=
  RegularChaseDerivationSkeleton.facts_node_subset_every_mem

/-- A first implication of `facts_node_subset_every_mem` is that, considering one of our subderivations, each of our members either has all of its facts contained in the head of the subderivation or it is itself a member of the subderivation. -/
theorem mem_suffix_of_mem {cd1 cd2 : RegularChaseDerivation obs rules} (suffix : cd1 <:+ cd2) : ∀ node ∈ cd2, node.facts ⊆ cd1.head.facts ∨ node ∈ cd1 :=
  RegularChaseDerivationSkeleton.mem_suffix_of_mem suffix

/-- The `head` cannot occur in the `tail`. Otherwise, it would be introduced using a trigger but then this trigger is already obsolete since all the facts from `head` already occur in the very beginning. We use `ObsolescenceCondition.contains_trg_result_implies_cond` here. -/
theorem head_not_mem_tail {cd : RegularChaseDerivation obs rules} : ∀ h, ¬ cd.head ∈ cd.tail h := by
  intro h contra
  rw [cd.mem_tail_iff] at contra
  rcases contra with ⟨cd2, suffix, contra⟩
  apply (cd2.active_trigger_origin_next contra).right
  apply obs.contains_trg_result_implies_cond
  apply Set.subset_trans (cd.head.facts_contain_origin_result (cd.head.origin.get (cd2.isSome_origin_next contra)) (by simp))
  apply cd.facts_node_subset_every_mem
  apply cd2.mem_of_mem_suffix suffix
  exact cd2.head_mem

/-- By `head_not_mem_tail`, if we have a suffix but our head occurs in the suffix, then our suffix is equal to us. -/
@[grind ->]
theorem eq_of_suffix_of_head_mem {cd1 cd2 : RegularChaseDerivation obs rules} (suffix : cd1 <:+ cd2) (head_mem : cd2.head ∈ cd1) : cd1 = cd2 := by
  rw [ChaseDerivation.suffix_iff_eq_or_suffix_tail] at suffix
  cases suffix with
  | inl suffix => exact suffix
  | inr suffix => rcases suffix with ⟨h, suffix⟩; apply False.elim; apply head_not_mem_tail h; apply cd1.mem_of_mem_suffix suffix; exact head_mem

/-- And now by `eq_of_suffix_of_head_mem`, if we have two suffixes $C$ and $D$, and the head of $D$ occurs in $C$, then $D$ is a suffix of $C$. This may seem obvious even without the above results but it is really not even though it aligns well with one's intuition. Imagine that a `ChaseNode` could occur multiple times in a `ChaseDerivation`. Then we may have a case where $C$ is a subderivation of $D$, $D$ is not a subderivation of $C$ but $D$ occurs in $C$. -/
@[grind ->]
theorem suffix_of_suffix_of_suffix_of_head_mem {cd cd1 cd2 : RegularChaseDerivation obs rules} :
    cd1 <:+ cd -> cd2 <:+ cd -> cd2.head ∈ cd1 -> cd2 <:+ cd1 := by
  intro suffix1 suffix2 head_mem
  cases PossiblyInfiniteList.suffix_or_suffix_of_suffix suffix1 suffix2 with
  | inr suffix => exact suffix
  | inl suffix => rw [eq_of_suffix_of_head_mem suffix]; exact PossiblyInfiniteList.IsSuffix_refl; exact head_mem

end FactMonotonicity

public section Predecessors

/-!
## Predecessor Relation

Since we learned that `ChaseNode`s cannot occur multiple times in the same `ChaseDerivation`,
the predecessor relation defined on `ChaseDerivationSkeleton` is now a total order on `ChaseDerivation.Node`.
This is particularly nice, since we can do this while completely ignoring indices of the nodes in the underlying `PossiblyInfiniteList`.
-/

/-- The predecessor relation is antisymmetric. -/
@[grind ->]
theorem predecessor_antisymm {cd : RegularChaseDerivation obs rules} {n1 n2 : cd.Node} : n1 ≼ n2 -> n2 ≼ n1 -> n1 = n2 := by
  simp only [cd.predecessor_iff]; grind

/-- The predecessor relation is transitive. -/
@[grind ->]
theorem predecessor_trans {cd : RegularChaseDerivation obs rules} {n1 n2 n3 : cd.Node} : n1 ≼ n2 -> n2 ≼ n3 -> n1 ≼ n3 := by
  simp only [cd.predecessor_iff]; grind

/-- We can express fairness in terms of the predecessor relation: For each trigger, there is a node such that the trigger is not active for each of the node's successors. -/
theorem fairness_prec {cd : RegularChaseDerivation obs rules} :
    ∀ (trg : RTrigger obs rules), ∃ (node : cd.Node), ∀ node2, node ≼ node2 -> ¬ trg.val.active node2.val.facts := by
  intro trg
  rcases cd.fairness' trg with ⟨cd2, suffix, fair⟩
  exists ⟨cd2.head, cd2.mem_of_mem_suffix suffix _ cd2.head_mem⟩
  intro node2 prec
  apply fair
  rw [cd.predecessor_iff] at prec
  rcases prec with ⟨cd3, suf3, head3, node2_mem_cd3⟩
  simp only at head3
  have : cd3 = cd2 := by
    have : cd2.head ∈ cd2 := cd2.head_mem
    apply eq_of_suffix_of_head_mem _ (by rw [← head3]; exact cd3.head_mem)
    apply suffix_of_suffix_of_suffix_of_head_mem suffix suf3
    rw [head3]; exact cd2.head_mem
  rw [← this]
  exact node2_mem_cd3

section StrictPredecessor

/-!
The strict version of the predecessor is a strict total order on `ChaseDerivation.Node` for the `ChaseDerivation`.
-/

/-- The strict predecessor relation is asymmetric. -/
@[grind ->]
theorem strict_predecessor_asymmetric {cd : RegularChaseDerivation obs rules} {n1 n2 : cd.Node} : n1 ≺ n2 -> ¬ n2 ≺ n1 := by
  intro prec contra; apply prec.right; apply predecessor_antisymm prec.left contra.left

/-- The strict predecessor relation is transitive. -/
@[grind ->]
theorem strict_predecessor_trans {cd : RegularChaseDerivation obs rules} {n1 n2 n3 : cd.Node} : n1 ≺ n2 -> n2 ≺ n3 -> n1 ≺ n3 := by
  intro prec1 prec2
  constructor
  . exact predecessor_trans prec1.left prec2.left
  . grind

/-- The `ChaseDerivationSkeleton.head` is a strict predecessor of `ChaseDerivationSkeleton.next`. -/
theorem head_strict_prec_next {cd : RegularChaseDerivation obs rules} :
    ∀ {next}, (mem : next ∈ cd.next) -> ⟨cd.head, cd.head_mem⟩ ≺ ⟨next, cd.next_mem_of_mem _ mem⟩ := by
  intro next next_mem
  constructor
  . exact cd.head_prec_next next_mem
  . intro contra
    apply cd.head_not_mem_tail (by rw [next_mem]; simp)
    grind

/-- The facts of a strict successor cannot be a subset of our facts. This is because strict successor nodes can only be introduced by active triggers. But if a trigger only produces facts that already exist, then it cannot be active. -/
@[grind ->]
theorem facts_not_subset_of_strict_predecessor {cd : RegularChaseDerivation obs rules} {n1 n2 : cd.Node} :
    n1 ≺ n2 -> ¬ n2.val.facts ⊆ n1.val.facts := by
  intro prec contra
  rcases (cd.predecessor_iff _ _).mp prec.left with ⟨d, suf, head, mem⟩
  rcases cd.subderivation_of_node_mem n2.property with ⟨d2, head2, suf2⟩
  have suf3 : d2 <:+ d := suffix_of_suffix_of_suffix_of_head_mem suf suf2 (by rw [head2]; exact mem)
  cases ChaseDerivation.suffix_iff_eq_or_suffix_tail.mp suf3 with
  | inl suf3 => grind
  | inr suf3 =>
    rcases suf3 with ⟨next_some, suf3⟩
    rw [Option.isSome_iff_exists] at next_some
    rcases next_some with ⟨next, next_some⟩
    apply (d.active_trigger_origin_next next_some).right
    apply ObsolescenceCondition.contains_trg_result_implies_cond
    have : next.facts ⊆ d.head.facts := by
      have : ⟨next, d.next_mem_of_mem _ next_some⟩ ≼ ⟨n2.val, by apply ChaseDerivation.mem_of_mem_suffix (d2.branch.IsSuffix_trans suf3 d.branch.IsSuffix_tail); rw [← head2]; exact d2.head_mem⟩ := by
        rw [d.predecessor_iff]
        exists d.tail (by simp [next_some])
        constructor
        . exact PossiblyInfiniteList.IsSuffix_tail
        constructor
        . simp [d.head_tail', next_some]
        . apply ChaseDerivation.mem_of_mem_suffix suf3; rw [← head2]; exact d2.head_mem
      grind
    exact Set.subset_trans (by rw [← next.ingoingFacts_eq, d.facts_next next_some]; apply Set.subset_union_of_subset_right; apply Set.subset_refl) this

end StrictPredecessor

end Predecessors

public section ChaseResult

/-!
## Chase Result

Opposed to the `ChaseDerivationSkeleton`, the result is now a model for all rules.
-/

/-- We define a shortcut for `RegularChaseDerivationSkeleton.result`. -/
abbrev result (cd : RegularChaseDerivation obs rules) := RegularChaseDerivationSkeleton.result cd.toChaseDerivationSkeleton

/-- The result is a model of all rules. This is true because otherwise, there would be an active trigger on the result. But then, this trigger needs to be active for some node and the hence it needs to become inactive at some point due to fairness. Hence it cannot be active on the result. Contradiction! -/
@[grind <-]
theorem result_models_rules {cd : RegularChaseDerivation obs rules} : cd.result.modelsRules rules := by
  intro r r_mem subs subs_loaded
  let trg : Trigger obs := ⟨r, subs⟩
  have trg_loaded : trg.loaded cd.result := subs_loaded
  apply obs.cond_implies_trg_is_satisfied (trg := trg)
  rcases RegularChaseDerivationSkeleton.trg_loaded_for_some_node_of_trg_loaded_for_result trg trg_loaded with ⟨node_loaded, node_loaded_mem, trg_loaded⟩
  rcases cd.subderivation_of_node_mem node_loaded_mem with ⟨cd_loaded, cd_loaded_head, cd_loaded_suffix⟩
  rcases cd_loaded.fairness' ⟨trg, r_mem⟩ with ⟨cd_obs, cd_obs_suffix, fairness⟩
  specialize fairness cd_obs.head cd_obs.head_mem
  apply Classical.byContradiction
  intro contra_not_obs
  apply fairness
  constructor
  . apply Set.subset_trans trg_loaded
    rw [← cd_loaded_head]
    apply RegularChaseDerivationSkeleton.facts_node_subset_every_mem
    apply cd_obs.mem_of_mem_suffix cd_obs_suffix
    apply cd_obs.head_mem
  . intro contra
    apply contra_not_obs
    unfold result
    rw [← RegularChaseDerivationSkeleton.result_suffix (PossiblyInfiniteList.IsSuffix_trans cd_obs_suffix cd_loaded_suffix)]
    apply obs.monotone
    . apply RegularChaseDerivationSkeleton.facts_node_subset_result; apply cd_obs.head_mem
    . exact contra

end ChaseResult

public section TermsInChase

/-!
## Terms in the Chase

We make some general observations about certain terms that might occur in the chase.

1. Constants can only originate directly from rules or from the initial fact set. No other constants can be introduced.
2. Functional terms can either also originate from the initial fact set or they are introduced as fresh terms by a trigger.

The second observation entails that the precense of a functional term that does not occur in the initial fact set implies
that the trigger that introduces this term must have been applied in some `ChaseNode`.
-/


/-- Constants in the chase can only come from the initial fact set or from a constant in a rule. -/
theorem constants_node_subset_constants_fs_union_constants_rules
    {cd : RegularChaseDerivation obs rules}
    {node : RegularChaseNode obs rules} (node_mem : node ∈ cd) :
    node.facts.constants ⊆ cd.head.facts.constants ∪ rules.head_constants := by
  apply ChaseDerivation.constants_node_subset_constants_fs_union_constants_rules RegularChaseNode.out_sub_in _ node_mem
  rw [RegularChaseNode.ingoingFacts_eq, RegularChaseNode.outgoingFacts_eq]

/-- Each functional term in the chase originates as a fresh term from a trigger if it was not already part of the initial fact set. -/
theorem functional_term_originates_from_some_trigger
    {cd : RegularChaseDerivation obs rules}
    (node : cd.Node)
    {t : GroundTerm sig}
    (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok)
    (t_mem : t ∈ node.val.facts.terms) :
    t ∈ cd.head.facts.terms ∨ ∃ node2, node2 ≼ node ∧ ∃ orig ∈ node2.val.origin, t ∈ orig.fst.val.fresh_terms_for_head_disjunct orig.snd.val (by rw [← PreTrigger.length_mapped_head]; exact orig.snd.isLt) := by
  apply ChaseDerivation.functional_term_originates_from_some_trigger RegularChaseNode.out_sub_in _ predecessor_trans node t_is_func t_mem
  rw [RegularChaseNode.ingoingFacts_eq, RegularChaseNode.outgoingFacts_eq]

/-- If a functional term occurs in the chase, then the trigger that introduces this term must have been used in the chase, unless the term already occurs in the initial fact set. -/
theorem trigger_introducing_functional_term_occurs_in_chase
    {cd : RegularChaseDerivation obs rules}
    (node : cd.Node)
    {t : GroundTerm sig}
    (t_mem_node : t ∈ node.val.facts.terms)
    {trg : RTrigger obs rules}
    {disj_idx : Nat}
    {lt : disj_idx < trg.val.rule.head.length}
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
    t ∈ cd.head.facts.terms ∨ ∃ node2, node2 ≼ node ∧ ∃ orig ∈ node2.val.origin, orig.fst.equiv trg ∧ orig.snd.val = disj_idx := by
  apply ChaseDerivation.trigger_introducing_functional_term_occurs_in_chase RegularChaseNode.out_sub_in _ predecessor_trans node t_mem_node t_mem_trg
  rw [RegularChaseNode.ingoingFacts_eq, RegularChaseNode.outgoingFacts_eq]

/-- If a functional term occurs in the chase, then the result of the trigger that introduces this term is contained in the current node, unless the functional term already occurs in the initial fact set. -/
theorem result_of_trigger_introducing_functional_term_occurs_in_chase
    {cd : RegularChaseDerivation obs rules}
    (node : cd.Node)
    {t : GroundTerm sig}
    (t_mem_node : t ∈ node.val.facts.terms)
    {trg : RTrigger obs rules}
    {disj_idx : Nat}
    {lt : disj_idx < trg.val.rule.head.length}
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
    t ∈ cd.head.facts.terms ∨ (trg.val.mapped_head[disj_idx]'(by rw [PreTrigger.length_mapped_head]; exact lt)).toSet ⊆ node.val.facts := by
  cases trigger_introducing_functional_term_occurs_in_chase node t_mem_node t_mem_trg with
  | inl t_mem => apply Or.inl; exact t_mem
  | inr t_mem =>
    apply Or.inr
    rcases t_mem with ⟨node2, prec, origin, origin_eq, equiv, index_eq⟩
    apply Set.subset_trans _ (RegularChaseDerivationSkeleton.facts_node_subset_of_prec prec)
    simp only [← PreTrigger.result_eq_of_equiv equiv, ← index_eq]
    exact node2.val.facts_contain_origin_result _ origin_eq

end TermsInChase

section MinimalNodeWithProp

/-!
## Minimal Nodes with given Properties

If a property hold for a given node in the chase, then there must be a "first" node for which this property holds. That means that this node is minimal with respect to the `≺` relation.
The result itself is `prop_for_node_has_minimal_such_node` and is shown via `prop_for_nat_has_minimal_such_nat`.
This forces us to take into account specific node indices and therefore requires auxiliary theorems, mainly `get?_branch_injective`, which is shown using `node_has_unique_position`.
-/

theorem node_has_unique_position (cd : RegularChaseDerivation obs rules) :
    ∀ node, ∀ i j, i < j -> cd.branch.get? i = some node -> cd.branch.get? j ≠ some node := by
  intro node i j lt eq_i eq_j
  have le := Nat.le_pred_of_lt lt
  let cds2 := cd.derivation_for_branch_suffix (cd.branch.drop j.pred) (PossiblyInfiniteList.IsSuffix_drop j.pred) (by
    rw [Option.isSome_iff_ne_none, PossiblyInfiniteList.head_drop]; intro contra
    have := cd.branch.no_holes' j.pred contra
    rw [Nat.succ_pred (Nat.ne_zero_of_lt lt)] at this
    rw [eq_j] at this
    simp at this
  )
  let cd2 := cd.derivation_for_skeleton cds2 (PossiblyInfiniteList.IsSuffix_drop j.pred)
  have next_eq : cd2.next = some node := by
    simp only [ChaseDerivationSkeleton.next, cd2, ChaseDerivation.derivation_for_skeleton, cds2, ChaseDerivationSkeleton.derivation_for_branch_suffix, PossiblyInfiniteList.tail_drop, PossiblyInfiniteList.head_drop]
    rw [Nat.succ_pred (Nat.ne_zero_of_lt lt)]
    exact eq_j
  apply (cd2.active_trigger_origin_next next_eq).right
  apply obs.contains_trg_result_implies_cond
  have sub : node.facts ⊆ cd2.head.facts := by
    let node : cd.Node := ⟨node, by exists i⟩
    let node2 : cd.Node := ⟨cd2.head, by exists j.pred; simp only [cd2, ChaseDerivation.derivation_for_skeleton, cds2, ChaseDerivationSkeleton.derivation_for_branch_suffix, ChaseDerivationSkeleton.head, Option.some_get, PossiblyInfiniteList.head_drop]; rfl⟩
    have prec : node ≼ node2 := by
      exists cd.derivation_for_branch_suffix (cd.branch.drop i) (PossiblyInfiniteList.IsSuffix_drop i) (by simp [PossiblyInfiniteList.head_drop, eq_i])
      simp only [ChaseDerivationSkeleton.derivation_for_branch_suffix, ChaseDerivationSkeleton.head, PossiblyInfiniteList.head_drop]
      constructor; exact PossiblyInfiniteList.IsSuffix_drop i
      constructor; simp [eq_i, node]
      apply ChaseDerivationSkeleton.mem_of_mem_suffix (cd1 := cds2) _ _ cd2.head_mem
      rw [ChaseDerivationSkeleton.IsSuffix_iff]
      exists j.pred - i
      simp only [cds2, ChaseDerivationSkeleton.derivation_for_branch_suffix]
      grind
    exact RegularChaseDerivationSkeleton.facts_node_subset_of_prec prec
  exact Set.subset_trans (node.facts_contain_origin_result (node.origin.get (cd2.isSome_origin_next next_eq)) (by simp)) sub

theorem get?_branch_injective (cd : RegularChaseDerivation obs rules) : ∀ node, ∀ i j, cd.branch.get? i = some node -> cd.branch.get? j = some node -> i = j := by
  intro node i j eq_i eq_j
  apply Decidable.byContradiction
  intro ne
  cases Nat.lt_or_lt_of_ne ne with
  | inl lt => exact cd.node_has_unique_position node i j lt eq_i eq_j
  | inr lt => exact cd.node_has_unique_position node j i lt eq_j eq_i

public theorem prop_for_node_has_minimal_such_node {cd : RegularChaseDerivation obs rules} (prop : cd.Node -> Prop) :
    ∀ n, prop n -> ∃ n2, prop n2 ∧ ∀ n3, n3 ≺ n2 -> ¬ prop n3 := by
  let prop' : Nat -> Prop := fun i => ∃ (e : RegularChaseNode obs rules) (mem : e ∈ cd.branch.get? i), prop ⟨e, by exists i⟩
  intro n prop_n
  rcases n.property with ⟨i, n_mem⟩
  rcases prop_for_nat_has_minimal_such_nat prop' i (by exists n.val, n_mem) with ⟨k, prop_k, not_lt_k⟩
  rcases prop_k with ⟨n2, n2_mem, prop_n2⟩
  exists ⟨n2, by exists k⟩, prop_n2
  intro n3 prec contra
  rcases n3.property with ⟨j, n3_mem⟩
  apply not_lt_k ⟨j, by
    apply Decidable.byContradiction
    intro le; simp only [Nat.not_lt] at le
    apply strict_predecessor_asymmetric prec
    constructor
    . rw [cd.predecessor_iff]
      have n2_mem' : n2 ∈ cd := by exists k
      rcases cd.subderivation_of_node_mem n2_mem' with ⟨cd2, head2, suf2⟩
      exists cd2; simp only [suf2, head2, true_and]
      rw [cd2.mem_iff]
      exists j - k
      unfold ChaseDerivation.IsSuffix at suf2; rw [ChaseDerivationSkeleton.IsSuffix_iff] at suf2; rcases suf2 with ⟨k', suf2⟩
      have : k' = k := by
        apply cd.get?_branch_injective n2
        . rw [← head2]
          simp only [ChaseDerivationSkeleton.head, Option.some_get]
          rw [← suf2]
          simp
        . exact n2_mem
      rw [← suf2, this, PossiblyInfiniteList.get?_drop, Nat.add_sub_of_le le]
      exact n3_mem
    . exact Ne.symm prec.right⟩
  exists n3.val, n3_mem

end MinimalNodeWithProp

end RegularChaseDerivation

