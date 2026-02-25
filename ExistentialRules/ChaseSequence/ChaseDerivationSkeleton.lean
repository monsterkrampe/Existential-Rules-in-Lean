import PossiblyInfiniteTrees.PossiblyInfiniteList.PossiblyInfiniteList

import ExistentialRules.ChaseSequence.ChaseNode

/-!
# Chase Derivation Skeleton

It is time to define the chase.
We are going to introduce slightly different representations and the `ChaseDerivationSkeleton` is arguably the most basic but also most versatile one.

We only demand a `PossiblyInfiniteList` of `ChaseNode`s that is non-empty such that the next `ChaseNode` always results from a trigger application. However, we do not care so far if the trigger is active or even loaded.
We also do not care here whether the derivation is "fair".
-/

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

section ChaseStep

/-!
## Chase Step

To define how one chase step follows from the previous, we introduce an auxiliary definitions that capture that the next `ChaseNode` in a `ChaseDerivationSkeleton` always follows from the previous from a trigger application, given that a next node still exists.
-/

def exists_trigger_opt_fs (obs : ObsoletenessCondition sig) (rules : RuleSet sig) (before : ChaseNode obs rules) (after : Option (ChaseNode obs rules)) : Prop :=
  ∀ node ∈ after,
  ∃ trg : (RTrigger (obs : LaxObsoletenessCondition sig) rules),
  ∃ i,
  node = {
    facts := before.facts ∪ (trg.val.mapped_head[i.val]'(i.isLt)).toSet,
    origin := some ⟨trg, i⟩
    facts_contain_origin_result := by intro _ eq; rw [Option.mem_def, Option.some_inj] at eq; rw [← eq]; apply Set.subset_union_of_subset_right; apply Set.subset_refl
  }

end ChaseStep

/-!
## The ChaseDerivation Structure

The backbone of the `ChaseDerivationSkeleton` is a `PossiblyInfiniteList` of `ChaseNode`s with two conditions.

1. We enforce that there is at least an initial `ChaseNode`.
2. At each step in the derivation, either there exists a trigger that yields the next node or there is no next node.
-/

structure ChaseDerivationSkeleton (obs : ObsoletenessCondition sig) (rules : RuleSet sig) where
  branch : PossiblyInfiniteList (ChaseNode obs rules)
  isSome_head : branch.head.isSome
  triggers_exist : ∀ n : Nat, ∀ before ∈ (branch.drop n).head,
    let after := (branch.drop n).tail.head
    (exists_trigger_opt_fs obs rules before after)

namespace ChaseDerivationSkeleton

variable {obs : ObsoletenessCondition sig} {rules : RuleSet sig}

section Basics

/-!
## Basic Definitions

Here we introduce some auxiliary definitions and theorems and we lift some of the machinery of the underlying `PossiblyInfiniteList` to `ChaseDerivationSkeleton`.
-/

/-- Membership of `ChaseNode`s in the `ChaseDerivationSkeleton` directly corresponds to membership in the `PossiblyInfiniteList`. -/
instance : Membership (ChaseNode obs rules) (ChaseDerivationSkeleton obs rules) where
  mem cd node := node ∈ cd.branch

/-- Each suffix of the underlying `PossiblyInfiniteList` is itself a `ChaseDerivationSkeleton` as long as its head is not none. -/
def derivation_for_branch_suffix
    (cd : ChaseDerivationSkeleton obs rules)
    (l2 : PossiblyInfiniteList (ChaseNode obs rules))
    (suffix : l2 <:+ cd.branch)
    (l2_head_some : l2.head.isSome) :
    ChaseDerivationSkeleton obs rules where
  branch := l2
  isSome_head := l2_head_some
  triggers_exist := by
    rw [PossiblyInfiniteList.IsSuffix_iff] at suffix
    rcases suffix with ⟨m, suffix⟩
    rw [← suffix]
    intro n
    have := cd.triggers_exist (m + n)
    simp only [PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?_drop] at *
    exact this

/-- The head of the `ChaseDerivationSkeleton` is the initial `ChaseNode`. We know that this is never none. -/
def head (cd : ChaseDerivationSkeleton obs rules) : ChaseNode obs rules := cd.branch.head.get (cd.isSome_head)

/-- The `head` is a member. -/
theorem head_mem {cd : ChaseDerivationSkeleton obs rules} : cd.head ∈ cd := by exists 0; simp [head, PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?]

section Next

/-!
### The "next" ChaseNode

For a `ChaseDerivationSkeleton` derivation, its `next` node is the `ChaseNode` immediately following the `head`.
We mainly introduce a couple of theorems here that abstract away the `triggers_exist` condition from the `ChaseDerivationSkeleton` definition.
-/

def next (cd : ChaseDerivationSkeleton obs rules) : Option (ChaseNode obs rules) := cd.branch.tail.head

/-- The `next` node is a member. -/
theorem next_mem_of_mem {cd : ChaseDerivationSkeleton obs rules} : ∀ next ∈ cd.next, next ∈ cd := by intro next next_mem; apply cd.branch.tail.mem_of_mem_suffix cd.branch.IsSuffix_tail; apply cd.branch.tail.head_mem; exact next_mem

/-- The origin of the `next` `ChaseNode` needs to be set. -/
theorem isSome_origin_next {cd : ChaseDerivationSkeleton obs rules} {next : ChaseNode obs rules} (eq : cd.next = some next) : next.origin.isSome := by
  have trg_ex := cd.triggers_exist 0 cd.head (by simp [PossiblyInfiniteList.drop_zero, head])
  rw [PossiblyInfiniteList.drop_zero] at trg_ex
  specialize trg_ex _ eq
  rcases trg_ex with ⟨_, _, trg_ex⟩; rw [trg_ex]; simp

/-- The fact set of the `next` `ChaseNode` consists exactly of the facts from `head` and the result of the trigger that introduces `next`. -/
theorem facts_next {cd : ChaseDerivationSkeleton obs rules} {next : ChaseNode obs rules} (eq : cd.next = some next) :
    next.facts = cd.head.facts ∪ (next.origin_result (cd.isSome_origin_next eq)).toSet := by
  have trg_ex := cd.triggers_exist 0 cd.head (by simp [PossiblyInfiniteList.drop_zero, head])
  rw [PossiblyInfiniteList.drop_zero] at trg_ex
  specialize trg_ex _ eq
  rcases trg_ex with ⟨trg', _, trg_ex⟩; simp only [trg_ex]; rfl

end Next

section Suffixes

/-!
### ChaseDerivationSkeleton Suffixes

We define a suffix relation on `ChaseDerivationSkeleton` simply as the suffix relation of the underlying `PossiblyInfiniteList`.
-/

def IsSuffix (cd1 cd2 : ChaseDerivationSkeleton obs rules) : Prop := cd1.branch <:+ cd2.branch
infixl:50 " <:+ " => IsSuffix

/-- Members of our suffix are also our members. -/
theorem mem_of_mem_suffix {cd1 cd2 : ChaseDerivationSkeleton obs rules} (suffix : cd1 <:+ cd2) : ∀ node ∈ cd1, node ∈ cd2 := by
  rintro node ⟨n, node_eq⟩
  rcases suffix with ⟨m, suffix⟩
  exists m + n
  rw [← suffix, InfiniteList.get_drop] at node_eq
  exact node_eq

/-- Each `ChaseNode` in the `ChaseDerivationSkeleton` induces a subderivation. -/
theorem subderivation_of_node_mem {cd : ChaseDerivationSkeleton obs rules} {node : ChaseNode obs rules} (node_mem : node ∈ cd) :
    ∃ (cd2 : ChaseDerivationSkeleton obs rules), cd2.head = node ∧ cd2 <:+ cd := by
  rcases node_mem with ⟨n, node_mem⟩
  exists cd.derivation_for_branch_suffix (cd.branch.drop n) (cd.branch.IsSuffix_drop n) (by simp only [PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?, node_mem]; simp)
  constructor
  . simp only [derivation_for_branch_suffix, head, PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?, node_mem, Option.get_some]
  . exact cd.branch.IsSuffix_drop n

end Suffixes

section Tail

/-!
### Tail

If `next` exists, we can drop the first element from the `ChaseDerivationSkeleton` and obtain a new `ChaseDerivationSkeleton`, which, inspired by the `PossiblyInfiniteList`, we call the `tail`.
-/

def tail (cd : ChaseDerivationSkeleton obs rules) (next_some : cd.next.isSome) : ChaseDerivationSkeleton obs rules :=
  cd.derivation_for_branch_suffix cd.branch.tail (cd.branch.IsSuffix_tail) next_some

/-- The `head` of the `tail` is `next`. -/
theorem head_tail {cd : ChaseDerivationSkeleton obs rules} {next_some : cd.next.isSome} : some (cd.tail next_some).head = cd.next := by
  unfold tail head ChaseDerivationSkeleton.next derivation_for_branch_suffix
  simp only [Option.some_get]

/-- The `head` of the `tail` is `next`. -/
theorem head_tail' {cd : ChaseDerivationSkeleton obs rules} {next_some : cd.next.isSome} : (cd.tail next_some).head = cd.next.get next_some := by rfl

/-- `next` is a member of the `tail`. -/
theorem next_mem_tail {cd : ChaseDerivationSkeleton obs rules} {next_some : cd.next.isSome} : ∀ next ∈ cd.next, next ∈ cd.tail next_some := by
  intro next next_mem
  have : next = cd.next.get next_some := by
    conv => right; left; rw [next_mem]
    simp
  rw [this, ← head_tail']
  exact head_mem

/-- A node is a member if and only if it is either the head or it is a member of the tail. -/
theorem mem_iff_eq_head_or_mem_tail {cd : ChaseDerivationSkeleton obs rules} {node : ChaseNode obs rules} : node ∈ cd ↔ node = cd.head ∨ ∃ h, node ∈ cd.tail h := by
  constructor
  . rintro ⟨n, mem⟩
    cases n with
    | zero => apply Or.inl; simp [head, PossiblyInfiniteList.head, InfiniteList.head, mem]
    | succ n =>
      apply Or.inr;
      exists (by
        rw [Option.isSome_iff_ne_none]; intro contra; simp only [next, PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?_tail] at contra
        have := cd.branch.get?_eq_none_of_le_of_eq_none contra n.succ (by simp)
        simp only [PossiblyInfiniteList.get?] at this; rw [this] at mem
        simp at mem)
      exists n
  . intro or; cases or with
    | inl eq_head => rw [eq_head]; exact cd.head_mem
    | inr mem_tail => rcases mem_tail with ⟨_, mem_tail⟩; apply mem_of_mem_suffix _ _ mem_tail; exact cd.branch.IsSuffix_tail

/-- A derivation is a suffix of another if and only if both are the same or the first is a suffix of the second's tail. -/
theorem suffix_iff_eq_or_suffix_tail {cd1 cd2 : ChaseDerivationSkeleton obs rules} : cd1 <:+ cd2 ↔ cd1 = cd2 ∨ ∃ h, cd1 <:+ cd2.tail h := by
  -- TODO: maybe we should extract a result like this to InfiniteList directly
  constructor
  . rintro ⟨n, suffix⟩
    cases n with
    | zero => apply Or.inl; rw [InfiniteList.drop_zero] at suffix; apply Eq.symm; rw [ChaseDerivationSkeleton.mk.injEq, PossiblyInfiniteList.mk.injEq]; exact suffix
    | succ n =>
      apply Or.inr
      exists (by
        rw [Option.isSome_iff_ne_none]
        intro contra
        have := cd2.branch.get?_eq_none_of_le_of_eq_none contra (n+1) (by simp)
        simp only [PossiblyInfiniteList.get?] at this
        rw [InfiniteList.ext_iff] at suffix
        specialize suffix 0
        rw [InfiniteList.get_drop, Nat.add_zero, this] at suffix
        have contra := cd1.isSome_head
        rw [Option.isSome_iff_ne_none] at contra
        apply contra
        simp only [PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?]
        rw [← suffix])
      exists n
      simp only [tail, derivation_for_branch_suffix, PossiblyInfiniteList.tail]
      apply InfiniteList.ext
      intro m
      simp only [InfiniteList.get_tail, InfiniteList.get_drop]
      rw [InfiniteList.ext_iff] at suffix
      simp only [InfiniteList.get_drop] at suffix
      have : (n+m).succ = (n + 1 + m) := by omega
      rw [this]
      apply suffix m
  . intro h; cases h with
    | inl eq => rw [eq]; exact PossiblyInfiniteList.IsSuffix_refl
    | inr suffix => rcases suffix with ⟨h, suffix⟩; apply PossiblyInfiniteList.IsSuffix_trans suffix; exact PossiblyInfiniteList.IsSuffix_tail

end Tail

section InductionPrinciple

/-!
### Induction Principle for Members

Similar to `PossiblyInfiniteList.mem_rec`, we define an induction principle to show
properties of `ChaseNode`s in a `ChaseDerivationSkeleton`.
For this, we introduce `ChaseDerivationSkeleton.Node` as the subtype of `ChaseNode` that features a membership proof.
-/

abbrev Node (cd : ChaseDerivationSkeleton obs rules) := { node : ChaseNode obs rules // node ∈ cd}

/-- A `Node` of our suffix can be cast into our `Node` type. -/
def Node.cast_suffix {cd cd2 : ChaseDerivationSkeleton obs rules} (suffix : cd <:+ cd2) (node : Node cd) : Node cd2 := ⟨node.val, mem_of_mem_suffix suffix _ node.property⟩

/-- If we want to show a motive for all nodes in a derivation, it is enough to show the motive for the head and for the next node in each abitrary subderivation where the motive already holds for the head. This can be used with the induction tactic. -/
theorem mem_rec
    {cd : ChaseDerivationSkeleton obs rules}
    {motive : Node cd -> Prop}
    (head : motive ⟨cd.head, cd.head_mem⟩)
    (step : ∀ (cd2 : ChaseDerivationSkeleton obs rules), (suffix : cd2 <:+ cd) -> motive ⟨cd2.head, mem_of_mem_suffix suffix _ cd2.head_mem⟩ -> ∀ next, (next_mem : next ∈ cd2.next) -> motive ⟨next, mem_of_mem_suffix suffix _ (cd2.next_mem_of_mem _ next_mem)⟩)
    (node : Node cd) :
    motive node := by
  induction node using PossiblyInfiniteList.mem_rec with
  | head head' mem => unfold ChaseDerivationSkeleton.head at head; rw [Option.mem_def] at mem; simp only [mem, Option.get_some] at head; exact head
  | step l2 suffix ih next next_mem =>
    rcases ih with ⟨head, head_mem, ih⟩
    let cd2 : ChaseDerivationSkeleton obs rules := cd.derivation_for_branch_suffix l2 suffix (by rw [head_mem]; simp)
    apply step cd2 suffix
    . simp only [cd2, derivation_for_branch_suffix, ChaseDerivationSkeleton.head];
      conv => right; left; left; rw [head_mem]
      simp only [Option.get_some]
      exact ih
    . exact next_mem

/-- A node is a member of the `tail` if and only if there is a subderivation where the node is in the `next` position. Part of this proof uses the induction principle defined above. -/
theorem mem_tail_iff {cd : ChaseDerivationSkeleton obs rules} {next_some : cd.next.isSome} {node : ChaseNode obs rules} :
    node ∈ cd.tail next_some ↔ ∃ cd2, cd2 <:+ cd ∧ cd2.next = some node := by
  constructor
  . intro node_mem
    let node' : (cd.tail next_some).Node := ⟨node, node_mem⟩
    show ∃ cd2, cd2 <:+ cd ∧ cd2.next = some node'.val
    induction node' using mem_rec with
    | head => exists cd; constructor; exact cd.branch.IsSuffix_refl; rw [head_tail]
    | step cd3 suffix ih next next_mem =>
      exists cd3; constructor
      . apply cd3.branch.IsSuffix_trans suffix; exact cd.branch.IsSuffix_tail
      . exact next_mem
  . rintro ⟨cd2, suffix, next_eq⟩
    have : cd2.tail (by simp [next_eq]) <:+ cd.tail next_some := by
      -- TODO: maybe we should extract a result like this to InfiniteList directly
      rcases suffix with ⟨n, suffix⟩
      exists n
      simp only [tail, derivation_for_branch_suffix, PossiblyInfiniteList.tail]
      apply InfiniteList.ext
      intro m
      simp only [InfiniteList.get_tail, InfiniteList.get_drop]
      rw [InfiniteList.ext_iff] at suffix
      simp only [InfiniteList.get_drop] at suffix
      apply suffix m.succ
    apply mem_of_mem_suffix this
    rw [← head_tail (next_some := by simp [next_eq]), Option.some_inj] at next_eq
    simp only [← next_eq]
    apply head_mem

end InductionPrinciple

end Basics

section FactMonotonicity

/-!
## Subset Monotonicity of Facts in ChaseNodes

Since `ChaseNodes` always extend the previous facts, the fact sets can only be growing along the `ChaseDerivationSkeleton`.
-/

/-- Each member's facts contain the head facts. Note that this extends to arbitrary pairs of members since each member always induces a subderivation where it acts as the head. -/
theorem facts_node_subset_every_mem {cd : ChaseDerivationSkeleton obs rules} : ∀ node ∈ cd, cd.head.facts ⊆ node.facts := by
  intro node node_mem
  let node' : cd.Node := ⟨node, node_mem⟩
  show cd.head.facts ⊆ node'.val.facts
  induction node' using mem_rec with
  | head => apply Set.subset_refl
  | step cd2 suffix subset next next_eq =>
    apply Set.subset_trans subset
    rw [cd2.facts_next next_eq]
    apply Set.subset_union_of_subset_left
    apply Set.subset_refl

/-- A first implication of `facts_node_subset_every_mem` is that, considering one of our subderivations, each of our members either has all of its facts contained in the head of the subderivation or it is itself a member of the subderivation. -/
theorem mem_suffix_of_mem {cd1 cd2 : ChaseDerivationSkeleton obs rules} (suffix : cd1 <:+ cd2) : ∀ node ∈ cd2, node.facts ⊆ cd1.head.facts ∨ node ∈ cd1 := by
  intro node node_mem
  rcases subderivation_of_node_mem node_mem with ⟨cd3, cd3_head, suffix'⟩
  cases PossiblyInfiniteList.suffix_or_suffix_of_suffix suffix suffix' with
  | inl suffix => apply Or.inl; rw [← cd3_head]; apply cd3.facts_node_subset_every_mem; apply mem_of_mem_suffix suffix; apply cd1.head_mem
  | inr suffix => apply Or.inr; rw [← cd3_head]; apply mem_of_mem_suffix suffix; apply cd3.head_mem

end FactMonotonicity

section Predecessors

/-!
## Predecessor Relation

We can define a predecessor relation (`≼`) on `ChaseDerivation.Node`.
At this point, it does not have many properties. On Proper `ChaseDerivation`s it will be a total order.
-/

/-- A node $n$ is a predecessor of a node $m$ if there is a subderivation there $n$ is the head and $m$ is an arbitrary member. -/
def predecessor {cd : ChaseDerivationSkeleton obs rules} (n1 n2 : Node cd) : Prop := ∃ cd2, cd2 <:+ cd ∧ cd2.head = n1.val ∧ n2.val ∈ cd2
infixl:50 " ≼ " => predecessor

/-- The predecessor relation is stable across suffixes. That is, predecessor in our suffix are also predecessor for us. We only need to cast the nodes. -/
theorem predecessor_of_suffix {cd cd2 : ChaseDerivationSkeleton obs rules} {n1 n2 : Node cd} (suffix : cd <:+ cd2) : n1 ≼ n2 -> (n1.cast_suffix suffix) ≼ (n2.cast_suffix suffix) := by
  rintro ⟨cd3, suffix', head_eq, mem⟩
  exists cd3; constructor
  . exact cd3.branch.IsSuffix_trans suffix' suffix
  constructor
  . rw [head_eq]; rfl
  . exact mem

/-- The predecessor relation is reflexive. -/
theorem predecessor_refl {cd : ChaseDerivationSkeleton obs rules} {node : Node cd} : node ≼ node := by rcases cd.subderivation_of_node_mem node.property with ⟨cd2, head_eq, suffix⟩; exists cd2; simp only [suffix, head_eq, true_and]; rw [← head_eq]; exact cd2.head_mem

/-- The predecessor relation is total. -/
theorem predecessor_total {cd : ChaseDerivationSkeleton obs rules} (n1 n2 : Node cd) : n1 ≼ n2 ∨ n2 ≼ n1 := by
  rcases cd.subderivation_of_node_mem n1.property with ⟨cd1, head1, suf1⟩
  rcases cd.subderivation_of_node_mem n2.property with ⟨cd2, head2, suf2⟩
  cases PossiblyInfiniteList.suffix_or_suffix_of_suffix suf1 suf2 with
  | inl suffix => apply Or.inr; exists cd2; simp only [suf2, head2, true_and]; apply cd1.mem_of_mem_suffix; exact suffix; rw [← head1]; exact cd1.head_mem
  | inr suffix => apply Or.inl; exists cd1; simp only [suf1, head1, true_and]; apply cd2.mem_of_mem_suffix; exact suffix; rw [← head2]; exact cd2.head_mem

/-- The `head` is a predecessor of `next`. -/
theorem head_prec_next {cd : ChaseDerivationSkeleton obs rules} : ∀ {next}, (mem : next ∈ cd.next) -> ⟨cd.head, cd.head_mem⟩ ≼ ⟨next, cd.next_mem_of_mem _ mem⟩ := by
  intro next next_mem; exact ⟨cd, cd.branch.IsSuffix_refl, rfl, cd.next_mem_of_mem _ next_mem⟩

/-- The facts of our predecessor are a subset of our facts. -/
theorem facts_node_subset_of_prec {cd : ChaseDerivationSkeleton obs rules} {node1 node2 : cd.Node} : node1 ≼ node2 -> node1.val.facts ⊆ node2.val.facts := by
  rintro ⟨cd2, suffix, head_eq, mem⟩
  rw [← head_eq]
  apply facts_node_subset_every_mem
  exact mem


section StrictPredecessor

/-!
We also define a strict version of the predecessor relation (`≺`) in the obvious way.
-/

/-- A node is a strict predecessor of another if it is a predecessor but not equal. -/
def strict_predecessor {cd : ChaseDerivationSkeleton obs rules} (n1 n2 : Node cd) : Prop := n1 ≼ n2 ∧ n1 ≠ n2
infixl:50 " ≺ " => strict_predecessor

/-- As for the predecessor relation, we can show that the relation is stable across suffixes given that we cast the nodes. -/
theorem strict_predecessor_of_suffix {cd cd2 : ChaseDerivationSkeleton obs rules} {n1 n2 : Node cd} (suffix : cd <:+ cd2) : n1 ≺ n2 -> (n1.cast_suffix suffix) ≺ (n2.cast_suffix suffix) := by
  intro prec
  constructor
  . apply predecessor_of_suffix suffix; exact prec.left
  . simp only [Node.cast_suffix]; intro contra; rw [Subtype.mk.injEq] at contra; apply prec.right; rw [Subtype.mk.injEq]; exact contra

/-- The strict predecessor relation is irreflexive. -/
theorem strict_predecessor_irreflexive {cd : ChaseDerivationSkeleton obs rules} {n : Node cd} : ¬ n ≺ n := by intro contra; apply contra.right; rfl

/-- The strict predecessor relation is total. -/
theorem strict_predecessor_total {cd : ChaseDerivationSkeleton obs rules} {n1 n2 : Node cd} : n1 ≠ n2 -> n1 ≺ n2 ∨ n2 ≺ n1 := by
  intro ne
  cases predecessor_total n1 n2 with
  | inl prec => apply Or.inl; constructor; exact prec; exact ne
  | inr prec => apply Or.inr; constructor; exact prec; exact Ne.symm ne

/-- A predecessor is either equal or a strict predecessor. -/
theorem eq_or_strict_of_predecessor {cd : ChaseDerivationSkeleton obs rules} {n1 n2 : Node cd} : n1 ≼ n2 -> n1 = n2 ∨ n1 ≺ n2 := by
  intro prec
  cases Classical.em (n1 = n2) with
  | inl eq => apply Or.inl; exact eq
  | inr ne => apply Or.inr; exact ⟨prec, ne⟩

end StrictPredecessor

end Predecessors

section ChaseResult

/-!
## Chase Result

Here, we define the result of a `ChaseDerivationSkeleton`, which is simply the `FactSet` that is the union of all facts of all `ChaseNode`s.
-/

def result (cd : ChaseDerivationSkeleton obs rules) : FactSet sig :=
  fun f => ∃ node ∈ cd, f ∈ node.facts

/-- Every node's facts occur in the result. -/
theorem facts_node_subset_result {cd : ChaseDerivationSkeleton obs rules} : ∀ node ∈ cd, node.facts ⊆ cd.result := by intro node _ _ _; exists node

/-- The result of our suffix is the same our result. -/
theorem result_suffix {cd1 cd2 : ChaseDerivationSkeleton obs rules} (suffix : cd1 <:+ cd2) : cd1.result = cd2.result := by
  apply Set.ext
  intro f
  constructor
  . rintro ⟨node, node_mem, f_mem⟩; apply cd2.facts_node_subset_result; exact mem_of_mem_suffix suffix _ node_mem; exact f_mem
  . rintro ⟨node, node_mem, f_mem⟩
    cases mem_suffix_of_mem suffix _ node_mem with
    | inl mem_suffix => apply cd1.facts_node_subset_result; exact cd1.head_mem; apply mem_suffix; exact f_mem
    | inr mem_suffix => apply cd1.facts_node_subset_result; exact mem_suffix; exact f_mem

/-- For each (finite) list of facts in the result, there is a node that that contains all of them. -/
theorem facts_mem_some_node_of_mem_result {cd : ChaseDerivationSkeleton obs rules} : ∀ (l : List (Fact sig)), l.toSet ⊆ cd.result -> ∃ node ∈ cd, l.toSet ⊆ node.facts := by
  intro l
  induction l with
  | nil => intros; exists cd.head; constructor; exact cd.head_mem; intro _ contra; simp [List.mem_toSet] at contra
  | cons f l ih =>
    intro subset
    rcases subset f (by simp [List.mem_toSet]) with ⟨node_f, node_f_mem, f_mem⟩
    rcases ih (by intro f f_mem; apply subset; rw [List.mem_toSet] at f_mem; simp [List.mem_toSet, f_mem]) with ⟨node_ih, node_ih_mem, l_subset⟩
    rcases cd.subderivation_of_node_mem node_f_mem with ⟨cd_f, cd_f_head, cd_f_suffix⟩
    cases mem_suffix_of_mem cd_f_suffix _ node_ih_mem with
    | inl mem_suffix =>
      exists node_f
      constructor
      . exact node_f_mem
      . intro e e_mem
        rw [List.mem_toSet, List.mem_cons] at e_mem
        cases e_mem with
        | inl e_mem => rw [e_mem]; exact f_mem
        | inr e_mem => rw [← cd_f_head]; apply mem_suffix; apply l_subset; rw [List.mem_toSet]; exact e_mem
    | inr mem_suffix =>
      exists node_ih
      constructor
      . exact node_ih_mem
      . intro e e_mem
        rw [List.mem_toSet, List.mem_cons] at e_mem
        cases e_mem with
        | inr e_mem => apply l_subset; rw [List.mem_toSet]; exact e_mem
        | inl e_mem =>
          rw [e_mem]
          apply cd_f.facts_node_subset_every_mem _ mem_suffix
          rw [cd_f_head]; exact f_mem

/-- If a trigger is loaded for the result, then it is loaded for some node in the derivation. -/
theorem trg_loaded_for_some_node_of_trg_loaded_for_result {cd : ChaseDerivationSkeleton obs rules} : ∀ trg : Trigger obs, trg.loaded cd.result -> ∃ node ∈ cd, trg.loaded node.facts := by
  intro trg trg_loaded
  apply cd.facts_mem_some_node_of_mem_result
  exact trg_loaded

end ChaseResult

end ChaseDerivationSkeleton

