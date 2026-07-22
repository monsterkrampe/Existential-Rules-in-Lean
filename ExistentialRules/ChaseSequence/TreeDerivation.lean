/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.Basic

public import ExistentialRules.ChaseSequence.ChaseDerivation

/-!
# Tree Derivation

The `TreeDerivation` is the tree version of the `ChaseDerivation`.
Since we allow rules to feature disjunctions,
there are multiple possible results for a given trigger. The `ChaseDerivation` picks one possible choice.
For the `TreeDerivation`, we consider all possiblities at once. That is, the tree branches out for the disjunctions.

We try to mimic much of the machinery introduced for `ChaseDerivation` but we will see that some of this requires a different approach.
Most prominently, we now need to consider addresses of nodes in the tree to be able to define a proper predecessor relation.
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-!
## The TreeDerivation Structure

The backbone of the `TreeDerivation` is a `FiniteDegreeTree` of `ChaseNode`s with a couple of conditions.

1. We enforce that there is at least an initial `ChaseNode`.
2. At each step in the derivation, either there exists a trigger that yields the child nodes or there is no trigger and consequently the derivation stops at this point. This is expressed by the two auxiliary definitions above.
3. No triggers are active on leaf nodes.
4. For each trigger, there exists a depth in the tree from which on the trigger is never active anymore.

Conditions 3 and 4 together are "fairness", i.e. each trigger must eventually be non-active. Fairness ensures that the chase result (or in this case each fact set in the chase result) is indeed a model.
-/

structure TreeDerivation (N : Type u) (obs : ObsolescenceCondition sig) (rules : RuleSet sig) [CN : ChaseNode N obs rules] where
  tree : FiniteDegreeTree N
  isSome_root : tree.root.isSome
  triggers_exist : ∀ ns : List Nat, ∀ before ∈ (tree.drop ns).root,
    CN.succ_list before (tree.drop ns).childNodes
  fairness_leaves : ∀ leaf, leaf ∈ tree.leaves -> ∀ trg : (RTrigger obs rules), ¬ trg.val.active (CN.outgoingFacts leaf)
  fairness_infinite_branches : ∀ trg : (RTrigger obs rules), ∃ i : Nat, ∀ ns : List Nat, ns.length ≥ i ->
    ∀ node ∈ tree.get? ns, ¬ trg.val.active (CN.outgoingFacts node)

namespace TreeDerivation

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig}

section Basics

variable {N : Type u} [CN : ChaseNode N obs rules]

/-!
## Basic Definitions

Here we introduce some auxiliary definitions and theorems and we lift some of the machinery of the underlying `FiniteDegreeTree` to `TreeDerivation`.
-/

/-- We can convert a `TreeDerivation` directly to a `FiniteDegreeTree.FiniteDegreeTreeWithRoot`. -/
@[expose]
def toFiniteDegreeTreeWithRoot (td : TreeDerivation N obs rules) : FiniteDegreeTree.FiniteDegreeTreeWithRoot N :=
  ⟨td.tree, by rw [← Option.isSome_iff_ne_none]; exact td.isSome_root⟩

/-- Membership of `ChaseNode`s in the `TreeDerivation` directly corresponds to membership in the `FiniteDegreeTree`. -/
instance : Membership N (TreeDerivation N obs rules) where
  mem td node := node ∈ td.tree

/-- An element is a member of the tree iff it occurs at some address. -/
theorem mem_iff {td : TreeDerivation N obs rules} : ∀ {e}, e ∈ td ↔ ∃ ns, td.tree.get? ns = some e := FiniteDegreeTree.mem_iff

/-- Each subtree of the underlying `FiniteDegreeTree` is itself a `TreeDerivation` as long as its root is not none. -/
@[expose]
def derivation_for_suffix
    (td : TreeDerivation N obs rules)
    (t2 : FiniteDegreeTree N)
    (suffix : t2 <:+ td.tree)
    (t2_root_some : t2.root.isSome) :
    TreeDerivation N obs rules where
  tree := t2
  isSome_root := t2_root_some
  triggers_exist := by
    rw [FiniteDegreeTree.IsSuffix_iff] at suffix
    rcases suffix with ⟨ms, suffix⟩
    rw [← suffix]
    intro ns
    have := td.triggers_exist (ms ++ ns)
    simp only [FiniteDegreeTree.root_drop, FiniteDegreeTree.drop_drop] at *
    exact this
  fairness_leaves := by
    rw [FiniteDegreeTree.IsSuffix_iff] at suffix
    rcases suffix with ⟨ms, suffix⟩
    intro leaf leaf_mem
    rw [FiniteDegreeTree.mem_leaves] at leaf_mem
    rcases leaf_mem with ⟨ns, leaf_mem⟩
    rw [← suffix] at leaf_mem
    apply td.fairness_leaves
    rw [FiniteDegreeTree.mem_leaves]
    exists (ms ++ ns)
    grind
  fairness_infinite_branches := by
    rw [Option.isSome_iff_exists] at t2_root_some; rcases t2_root_some with ⟨t2_root, t2_root_eq⟩
    rw [FiniteDegreeTree.IsSuffix_iff] at suffix
    rcases suffix with ⟨ms, suffix⟩
    rw [← suffix]
    intro trg
    rcases td.fairness_infinite_branches trg with ⟨i, fairness⟩
    exists i
    grind

/-- The root of the `TreeDerivation` is the initial `ChaseNode`. We know that this is never none. -/
@[expose]
def root (td : TreeDerivation N obs rules) : N := td.tree.root.get (td.isSome_root)

/-- The `root` is a member. -/
@[grind <-]
theorem root_mem {td : TreeDerivation N obs rules} : td.root ∈ td := by rw [mem_iff]; exists []; simp [root, FiniteDegreeTree.root_eq]

section ChildNodes

/-!
### The (immediate) ChildNodes

For a `TreeDerivation` derivation, its `childNodes` are the `ChaseNode`s immediately following the `root`.
We mainly introduce a couple of theorems here that abstract away the `triggers_exist` condition from the `TreeDerivation` definition.
-/

@[expose]
def childNodes (td : TreeDerivation N obs rules) : List N := td.tree.childNodes

/-- Each child node is a member. -/
@[grind ->]
theorem mem_of_mem_childNodes {td : TreeDerivation N obs rules} : ∀ n ∈ td.childNodes, n ∈ td := FiniteDegreeTree.mem_of_mem_childNodes

/-- The origin of the `childNodes` needs to be set. -/
@[grind ->]
theorem isSome_origin_of_mem_childNodes {td : TreeDerivation N obs rules} : ∀ n ∈ td.childNodes, (CN.origin n).isSome := by
  intro n n_mem
  have trg_ex := td.triggers_exist []
  rw [FiniteDegreeTree.drop_nil] at trg_ex
  specialize trg_ex td.root (by simp [root])
  rcases CN.succ_of_mem_succ_list trg_ex _ n_mem with ⟨goal, _⟩
  exact goal

/-- The trigger used to derive the `childNodes` is active for `head`. -/
@[grind ->]
theorem active_trigger_origin_of_mem_childNodes {td : TreeDerivation N obs rules} :
    ∀ {n}, (mem : n ∈ td.childNodes) -> ((CN.origin n).get (td.isSome_origin_of_mem_childNodes _ mem)).fst.val.active (CN.outgoingFacts td.root) := by
  intro n n_mem
  have trg_ex := td.triggers_exist []
  rw [FiniteDegreeTree.drop_nil] at trg_ex
  specialize trg_ex td.root (by simp [root]) (by intro contra; unfold childNodes at n_mem; rw [contra] at n_mem; simp at n_mem)
  rcases trg_ex with ⟨trg, act, _, orig_eq, _⟩
  specialize orig_eq n n_mem
  rw [Option.map_eq_some_iff] at orig_eq; rcases orig_eq with ⟨_, orig_eq, trg_eq⟩
  simp only [orig_eq, Option.get_some, trg_eq]; exact act

/-- The `childNodes` are not nil if and only if some trigger is active on `root`. -/
theorem childNodes_ne_nil_iff_trg_ex {td : TreeDerivation N obs rules} :
    td.childNodes ≠ [] ↔ ∃ (trg : RTrigger obs rules), trg.val.active (CN.outgoingFacts td.root) := by
  constructor
  . rw [List.ne_nil_iff_exists_cons]
    rintro ⟨hd, tl, eq⟩
    exists ((CN.origin hd).get (td.isSome_origin_of_mem_childNodes _ (by simp [eq]))).fst
    apply active_trigger_origin_of_mem_childNodes
    simp [eq]
  . rintro ⟨trg, active⟩
    intro eq_nil
    apply td.fairness_leaves td.root _ trg active
    rw [FiniteDegreeTree.mem_leaves]
    exists []
    unfold childNodes at eq_nil
    simp [root, FiniteDegreeTree.root_eq, eq_nil]

/-- The fact set of each of the `childNodes` consists exactly of the facts from `root` and the result of the trigger that introduces the child node. -/
theorem facts_childNodes {td : TreeDerivation N obs rules} : ∀ {n}, (mem : n ∈ td.childNodes) ->
    CN.ingoingFacts n = CN.outgoingFacts td.root ∪ (CN.origin_result n (td.isSome_origin_of_mem_childNodes _ mem)).toSet := by
  intro n n_mem
  have trg_ex := td.triggers_exist []
  rw [FiniteDegreeTree.drop_nil] at trg_ex
  specialize trg_ex td.root (by simp [root])
  rcases CN.succ_of_mem_succ_list trg_ex _ n_mem with ⟨_, goal⟩
  exact goal

end ChildNodes

section Suffixes

/-!
### TreeDerivation Subtrees

We define a suffix/subtree relation on `TreeDerivation` simply as the subtree relation of the underlying `FiniteDegreeTree`.
-/

def IsSuffix (td1 td2 : TreeDerivation N obs rules) : Prop := td1.tree <:+ td2.tree
infixl:50 " <:+ " => IsSuffix

theorem IsSuffix_iff {td1 td2 : TreeDerivation N obs rules} : td1 <:+ td2 ↔ td1.tree <:+ td2.tree := by rfl

/-- Members of our subtrees are also our members. -/
@[grind ->]
theorem mem_of_mem_suffix {cd1 cd2 : TreeDerivation N obs rules} (suffix : cd1 <:+ cd2) :
    ∀ node ∈ cd1, node ∈ cd2 :=
  FiniteDegreeTree.mem_of_mem_suffix suffix

end Suffixes

section ChildTrees

/-!
### Child Trees

We can drop the root of a `TreeDerivation` and obtain a (possibly empty) list of `childTrees`, which are again `TreeDerivation`s.
-/

/-- We obtain the child trees of the `FiniteDegreeTree` and convert each of them into a `TreeDerivation` using `derivation_for_suffix`. We know that all of those trees have non-none roots. -/
@[expose]
def childTrees (td : TreeDerivation N obs rules) : List (TreeDerivation N obs rules) :=
  td.tree.childTrees.attach.map (fun t =>
    td.derivation_for_suffix t.val (by apply FiniteDegreeTree.IsSuffix_of_mem_childTrees; exact t.property) (by rw [Option.isSome_iff_ne_none]; exact t.val.property)
  )

/-- Membership in `childTrees` can be boiled down to membership in `FiniteDegreeTree.childTrees`. -/
theorem mem_childTrees_iff {td : TreeDerivation N obs rules} : ∀ c, c ∈ td.childTrees ↔ c.toFiniteDegreeTreeWithRoot ∈ td.tree.childTrees := by
  intro c
  unfold childTrees toFiniteDegreeTreeWithRoot derivation_for_suffix
  simp only [List.mem_map, List.mem_attach, true_and]
  constructor
  . intro ⟨d, eq⟩; rw [← eq]; exact d.property
  . intro mem; exists ⟨c.toFiniteDegreeTreeWithRoot, mem⟩

/-- `childNodes` can be expressed by mapping each `childTrees` to its root. -/
theorem childNodes_eq {td : TreeDerivation N obs rules} : td.childNodes = td.childTrees.map root := by
  unfold childNodes childTrees
  rw [FiniteDegreeTree.childNodes_eq]
  apply List.ext_getElem
  . simp
  . simp [derivation_for_suffix, root]

/-- Each `childTrees` is a suffix. -/
@[grind ->]
theorem IsSuffix_of_mem_childTrees {td : TreeDerivation N obs rules} : ∀ td2 ∈ td.childTrees, td2 <:+ td := by
  intro td2 mem; apply FiniteDegreeTree.IsSuffix_of_mem_childTrees td2.toFiniteDegreeTreeWithRoot; rw [← mem_childTrees_iff]; exact mem

/-- A derivation is a subtree of another if and only if both are the same or the first is a suffix of one of the second's child trees. -/
theorem suffix_iff_eq_or_suffix_childTree {td1 td2 : TreeDerivation N obs rules} : td1 <:+ td2 ↔ td1 = td2 ∨ ∃ td3 ∈ td2.childTrees, td1 <:+ td3 := by
  constructor
  . rw [IsSuffix_iff, FiniteDegreeTree.IsSuffix_iff]; rintro ⟨ns, suffix⟩
    cases ns with
    | nil => apply Or.inl; rw [TreeDerivation.mk.injEq]; rw [FiniteDegreeTree.drop_nil] at suffix; apply Eq.symm; exact suffix
    | cons hd tl =>
      apply Or.inr
      cases eq : td2.childTrees[hd]? with
      | none =>
        have contra := td1.isSome_root
        rw [Option.isSome_iff_ne_none] at contra
        apply False.elim; apply contra
        have suf : td1.tree <:+ td2.tree.drop [hd] := by
          rw [FiniteDegreeTree.IsSuffix_iff]
          exists tl
          simpa using suffix
        rw [← FiniteDegreeTree.empty_iff_root_none]
        simp only [childTrees, List.getElem?_map, List.getElem?_attach, Option.map_eq_none_iff, Option.pmap_eq_none_iff] at eq
        rw [FiniteDegreeTree.get?_childTrees, FiniteDegreeTree.FiniteDegreeTreeWithRoot.tree_to_opt_none_iff] at eq
        rw [← FiniteDegreeTree.empty_iff_root_none] at eq
        rw [eq] at suf
        apply FiniteDegreeTree.empty_suffix_of_empty suf
      | some c =>
        rw [List.getElem?_eq_some_iff] at eq
        rcases eq with ⟨_, eq⟩
        exists c
        constructor
        . simp [← eq]
        . rw [IsSuffix_iff, FiniteDegreeTree.IsSuffix_iff]; exists tl; rw [← eq]; simp only [childTrees, derivation_for_suffix]; grind
  . intro h; cases h with
    | inl eq => rw [eq]; exact FiniteDegreeTree.IsSuffix_refl
    | inr suffix => rcases suffix with ⟨td3, td3_mem, suffix⟩; apply FiniteDegreeTree.IsSuffix_trans suffix; exact IsSuffix_of_mem_childTrees _ td3_mem

end ChildTrees

section InductionPrinciple

/-!
### Induction Principle for Members

Similar to `FiniteDegreeTree.mem_rec`, we define an induction principle to show
properties of `ChaseNode`s in a `TreeDerivation`.

Looking ahead a bit, we will also want to define a predecessor relation on nodes in the tree as we did for nodes in a `ChaseDerivation`.
This is not so elegant here though as the same node might indeed occur multiple times in the tree.
Therefore, we are going to associate each node with its address in the tree to tell them apart.
Since we are doing this anyway, it makes sense to define the induction principle already with respect to this kind of node.
-/

/-!
#### NodeWithAddress

The `NodeWithAddress` is a structure of a `ChaseNode`, an address (i.e. a `List Nat`), and a proof that the chase node is indeed at the given address.
We also introduce a couple of covenience functions and theorems for the `NodeWithAddress`.
-/

structure NodeWithAddress (td : TreeDerivation N obs rules) where
  node : N
  address : List Nat
  eq : td.tree.get? address = some node

namespace NodeWithAddress

/-- Each `NodeWithAddress` induces a `subderivation` in the `TreeDerivation`. -/
@[expose]
def subderivation {td : TreeDerivation N obs rules} (node : NodeWithAddress td) : TreeDerivation N obs rules :=
  td.derivation_for_suffix (td.tree.drop node.address) (td.tree.IsSuffix_drop node.address) (by rw [FiniteDegreeTree.root_drop, node.eq]; simp)

/-- We can cast a node for one of our subderivations into our own node. -/
@[expose]
def cast_for_new_root_node
    {td : TreeDerivation N obs rules}
    (new_root : NodeWithAddress td)
    (node : new_root.subderivation.NodeWithAddress) :
    NodeWithAddress td where
  node := node.node
  address := new_root.address ++ node.address
  eq := by
    rw [← node.eq]
    simp only [subderivation, derivation_for_suffix, FiniteDegreeTree.get?_drop]

/-- The `NodeWithAddress` version of `TreeDerivation.root`. -/
@[expose]
def root (td : TreeDerivation N obs rules) : NodeWithAddress td where
  node := td.root
  address := []
  eq := by simp [TreeDerivation.root, FiniteDegreeTree.root_eq]

/-- The child nodes of a given `NodeWithAddress`. -/
@[expose]
def childNodes {td : TreeDerivation N obs rules} (node : NodeWithAddress td) : List (NodeWithAddress td) := node.subderivation.childNodes.zipIdx_with_lt.attach.map (fun ⟨⟨c, idx⟩, prop⟩ => {
  node := c
  address := node.address ++ [idx.val]
  eq := by
    unfold TreeDerivation.childNodes at prop
    rw [List.mem_zipIdx_with_lt_iff_mem_zipIdx, List.mem_zipIdx_iff_getElem?, FiniteDegreeTree.get?_childNodes] at prop
    unfold subderivation derivation_for_suffix at prop
    grind
})

/-- The `NodeWithAddress` is a member. -/
@[grind <-]
theorem mem {td : TreeDerivation N obs rules} (node : td.NodeWithAddress) : node.node ∈ td := by
  rw [mem_iff]; exists node.address; exact node.eq

/-- Two `NodeWithAddress` are equal if their addresses are. -/
@[grind ->]
theorem eq_of_address_eq {td : TreeDerivation N obs rules} {n1 n2 : td.NodeWithAddress} :
    n1.address = n2.address -> n1 = n2 := by
  intro eq
  rw [NodeWithAddress.mk.injEq]
  simp only [eq, and_true]
  have eq1 := n1.eq
  have eq2 := n2.eq
  rw [eq] at eq1
  rw [eq1, Option.some_inj] at eq2
  exact eq2

/-- `NodeWithAddress` has `DecidableEq` based on its address. -/
def decEq {td : TreeDerivation N obs rules} (n1 n2 : NodeWithAddress td) : Decidable (n1 = n2) :=
  if eq : n1.address = n2.address
  then .isTrue (eq_of_address_eq eq)
  else .isFalse (by intro contra; apply eq; rw [contra])

instance {td : TreeDerivation N obs rules} : DecidableEq (NodeWithAddress td) := decEq

/-- `subderivation` is indeed a subtree. -/
@[grind <-]
theorem IsSuffix_subderivation {td : TreeDerivation N obs rules} {node : NodeWithAddress td} :
    node.subderivation <:+ td :=
  td.tree.IsSuffix_drop node.address

/-- The root of the `subderivation` is the node itself with empty address. -/
theorem root_subderivation {td : TreeDerivation N obs rules} {node : NodeWithAddress td} : (root node.subderivation) = { node := node.node, address := [], eq := by simp only [subderivation, derivation_for_suffix, FiniteDegreeTree.get?_drop, List.append_nil]; exact node.eq } := by
  simp [subderivation, derivation_for_suffix, root, TreeDerivation.root, node.eq]

/-- The root of the `subderivation` is the node itself. -/
@[simp, grind =]
theorem root_subderivation' {td : TreeDerivation N obs rules} {node : NodeWithAddress td} : node.subderivation.root = node.node := by
  simp [subderivation, derivation_for_suffix, TreeDerivation.root, node.eq]

/-- The `subderivation` of the root is the original `TreeDerivation`. -/
@[simp, grind =]
theorem subderivation_root {td : TreeDerivation N obs rules} : (root td).subderivation = td := by
  simp [subderivation, derivation_for_suffix, root]

/-- Unfolds the childNodes and subderivation definitions to an expression on the underlying tree. -/
theorem childNodes_subderivation {td : TreeDerivation N obs rules} {node : NodeWithAddress td} :
  node.subderivation.childNodes = (td.tree.drop node.address).childNodes := by rfl

/-- `NodeWithAddress.childNodes` has the same length as `TreeDerivation.childNodes`. -/
@[simp, grind =]
theorem length_childNodes {td : TreeDerivation N obs rules} {node : NodeWithAddress td} : node.childNodes.length = node.subderivation.childNodes.length := by
  simp [childNodes]

/-- `NodeWithAddress.childNodes` and `TreeDerivation.childNodes` are (almost) equal. -/
theorem childNodes_eq_childNodes {td : TreeDerivation N obs rules} {node : NodeWithAddress td} :
    node.subderivation.childNodes = node.childNodes.map NodeWithAddress.node := by
  apply List.ext_getElem
  . rw [List.length_map, length_childNodes]
  . intro i lt _; simp [childNodes, lt]

/-- Membership for `NodeWithAddress.childNodes` and `TreeDerivation.childNodes` is (almost) the same. -/
@[grind ->]
theorem mem_childNodes_of_mem_childNodes {td : TreeDerivation N obs rules} {node : NodeWithAddress td} :
    ∀ {n}, n ∈ node.childNodes -> n.node ∈ node.subderivation.childNodes := by
  intro n n_mem; rw [childNodes_eq_childNodes]; apply List.mem_map_of_mem; exact n_mem

/-- Getting specific elements from child nodes can be translated between `NodeWithAddress.childNodes` and `TreeDerivation.childNodes`. -/
@[simp, grind =]
theorem node_getElem_childNodes {td : TreeDerivation N obs rules} {node : NodeWithAddress td} :
    ∀ i (lt : i < node.childNodes.length), node.childNodes[i].node = node.subderivation.childNodes[i]'(by rw [← length_childNodes]; exact lt) := by
  simp only [childNodes_eq_childNodes]; simp

/-- Getting specific element addresses from child nodes can be translated between `NodeWithAddress.childNodes` and `TreeDerivation.childNodes`. -/
@[simp, grind =]
theorem address_getElem_childNodes {td : TreeDerivation N obs rules} {node : NodeWithAddress td} :
    ∀ i (lt : i < node.childNodes.length), node.childNodes[i].address = node.address ++ [i] := by
  intro i lt; simp only [childNodes]; grind

/-- The subderivation for a child node is a child tree. -/
@[grind ->]
theorem subderivation_mem_childTrees_of_mem_childNodes
    {td : TreeDerivation N obs rules} {node node2 : NodeWithAddress td} :
    node2 ∈ node.childNodes -> node2.subderivation ∈ node.subderivation.childTrees := by
  intro node2_mem
  simp only [childNodes, List.mem_map, List.mem_attach, true_and] at node2_mem
  rcases node2_mem with ⟨⟨node2_with_idx, node2_mem⟩, node2_eq⟩
  rw [List.mem_zipIdx_with_lt_iff_mem_zipIdx] at node2_mem
  have node2_mem := List.mem_zipIdx' node2_mem
  have : node2.subderivation = node.subderivation.childTrees[node2_with_idx.snd.val]'(by have lt := node2_with_idx.snd.isLt; simp only [childNodes_eq, List.length_map] at lt; exact lt) := by
    simp only [childTrees, subderivation, derivation_for_suffix]
    suffices node2.address = node.address ++ [node2_with_idx.snd.val] by simp [this]
    grind
  rw [this]
  apply List.getElem_mem

/-- The triggers_exist property expressed in terms of the `NodeWithAddress`. -/
theorem triggers_exist {td : TreeDerivation N obs rules} (node : td.NodeWithAddress) :
    CN.succ_list node.node node.subderivation.childNodes := by
  have trg_ex := node.subderivation.triggers_exist [] node.node
  rw [FiniteDegreeTree.drop_nil] at trg_ex
  apply trg_ex
  suffices node.node = node.subderivation.root by rw [this]; unfold TreeDerivation.root; simp
  simp

end NodeWithAddress

/-!
Now we are ready for the actual induction principle on `NodeWithAddress`s in a `TreeDerivation`.
-/

/-- If we want to show a motive for all nodes in a derivation, it is enough to show the motive for the root and for each arbitrary child node in each abitrary subderivation where the motive in turn already holds for the root. This can be used with the induction tactic. -/
theorem mem_rec_address
    {td : TreeDerivation N obs rules}
    {motive : NodeWithAddress td -> Prop}
    (root : motive (NodeWithAddress.root td))
    (step : ∀ (new_root : NodeWithAddress td), motive new_root -> ∀ c ∈ new_root.childNodes, motive c)
    (node : NodeWithAddress td) :
    motive node := by
  let motive' (rev_addr : List Nat) := ∀ n, (mem : n ∈ td.tree.get? rev_addr.reverse) -> motive {
    node := n
    address := rev_addr.reverse
    eq := mem
  }
  let rev_addr_node := node.address.reverse
  have : motive' rev_addr_node := by
    induction rev_addr_node with
    | nil =>
      intro n n_mem
      have eq : NodeWithAddress.root td = {node := n, address := [].reverse, eq := n_mem} := by
        apply NodeWithAddress.eq_of_address_eq; simp [NodeWithAddress.root]
      rw [← eq]
      exact root
    | cons hd tl ih =>
      intro n n_mem
      have n_mem : n ∈ (td.tree.drop tl.reverse).childNodes[hd]? := by rw [FiniteDegreeTree.get?_childNodes]; grind
      cases eq : td.tree.get? tl.reverse with
      | none =>
        have contra := td.tree.no_orphans (td.tree.drop tl.reverse) (FiniteDegreeTree.IsSuffix_drop tl.reverse) (by rw [FiniteDegreeTree.root_drop]; exact eq)
        simp [contra] at n_mem
      | some m =>
        let new_root : td.NodeWithAddress := { node := m, address := tl.reverse, eq := eq }
        specialize step new_root (ih m eq) _ (by
          simp only [NodeWithAddress.childNodes, List.mem_map]
          exists ⟨⟨n, ⟨hd, by simp only [NodeWithAddress.subderivation, derivation_for_suffix, childNodes, new_root]; grind⟩⟩, by
            rw [List.mem_zipIdx_with_lt_iff_mem_zipIdx]; simp only [NodeWithAddress.subderivation, derivation_for_suffix, childNodes]; grind⟩
          constructor; simp; rfl)
        simp only [new_root] at step
        simp only [List.reverse_cons]
        exact step
  specialize this node.node (by simp only [rev_addr_node, List.reverse_reverse]; exact node.eq)
  simp only [rev_addr_node, List.reverse_reverse] at this
  exact this

/-- A node is a member of some element of `childTrees` if and only if there is a subderivation where the node occurs in the `childNodes`. Part of this proof uses the induction principle defined above. -/
theorem mem_some_childTree_iff {td : TreeDerivation N obs rules} {node : N} :
    (∃ t ∈ td.childTrees, node ∈ t) ↔ ∃ td2, td2 <:+ td ∧ node ∈ td2.childNodes := by
  constructor
  . rintro ⟨t, t_mem, node_mem⟩
    rw [mem_iff] at node_mem
    rcases node_mem with ⟨addr, node_mem⟩
    let node' : t.NodeWithAddress := { node := node, address := addr, eq := node_mem }
    show ∃ td2, td2 <:+ td ∧ node'.node ∈ td2.childNodes
    induction node' using mem_rec_address with
    | root => exists td; constructor; exact td.tree.IsSuffix_refl; simp only [childNodes_eq, NodeWithAddress.root]; apply List.mem_map_of_mem; exact t_mem
    | step new_root ih c c_mem =>
      exists new_root.subderivation; constructor
      . apply FiniteDegreeTree.IsSuffix_trans NodeWithAddress.IsSuffix_subderivation; exact IsSuffix_of_mem_childTrees _ t_mem
      . rw [NodeWithAddress.childNodes_eq_childNodes]; apply List.mem_map_of_mem; exact c_mem
  . rintro ⟨td2, suffix, node_mem⟩
    rw [IsSuffix_iff, FiniteDegreeTree.IsSuffix_iff] at suffix; rcases suffix with ⟨ns, suffix⟩
    cases ns with
    | nil =>
      have : td = td2 := by rw [TreeDerivation.mk.injEq]; rw [FiniteDegreeTree.drop_nil] at suffix; exact suffix
      rw [childNodes_eq, List.mem_map] at node_mem; rcases node_mem with ⟨t, t_mem, node_mem⟩; exists t; constructor; rw [this]; exact t_mem; rw [← node_mem]; exact root_mem
    | cons hd tl =>
      cases eq : td.childTrees[hd]? with
      | none =>
        have contra := td2.isSome_root
        rw [Option.isSome_iff_ne_none] at contra
        apply False.elim; apply contra
        have suf : td2.tree <:+ td.tree.drop [hd] := by
          rw [FiniteDegreeTree.IsSuffix_iff]
          exists tl
          simpa using suffix
        rw [← FiniteDegreeTree.empty_iff_root_none]
        simp only [childTrees, List.getElem?_map, List.getElem?_attach, Option.map_eq_none_iff, Option.pmap_eq_none_iff] at eq
        rw [FiniteDegreeTree.get?_childTrees, FiniteDegreeTree.FiniteDegreeTreeWithRoot.tree_to_opt_none_iff] at eq
        rw [← FiniteDegreeTree.empty_iff_root_none] at eq
        rw [eq] at suf
        apply FiniteDegreeTree.empty_suffix_of_empty suf
      | some t =>
        rw [List.getElem?_eq_some_iff] at eq; rcases eq with ⟨_, eq⟩
        exists t; constructor; simp [← eq]
        have : td2 <:+ t := by rw [IsSuffix_iff, FiniteDegreeTree.IsSuffix_iff]; exists tl; rw [← eq]; simpa [childTrees, derivation_for_suffix] using suffix
        apply mem_of_mem_suffix this
        apply mem_of_mem_childNodes
        exact node_mem

end InductionPrinciple

end Basics

section GeneratedFacts

/-!
## Only Finitely many Generated Facts

The generated facts of node in a `TreeDerivation` are all facts that are not part of the initial fact set.
For each node, the set of generated facts is finite since each trigger only introduces finitely many new facts.
-/

variable {N : Type u} [CN : ChaseNode N obs rules]

/-- The generated facts of a chase node are the facts that orruc in the node but not in the initial chase node. -/
@[expose]
def generatedFacts (td : TreeDerivation N obs rules) (node : N) : FactSet sig :=
  fun f => f ∈ CN.ingoingFacts node ∧ f ∉ CN.outgoingFacts td.root

/-- The `generatedFacts` are always finite. -/
theorem generatedFacts_finite_of_mem
    (out_sub_in : CN.out_sub_in)
    {td : TreeDerivation N obs rules} (start_eq : CN.ingoingFacts td.root = CN.outgoingFacts td.root)
    {node : N} (mem : node ∈ td) :
    (td.generatedFacts node).finite := by
  rw [mem_iff] at mem
  rcases mem with ⟨addr, mem⟩
  let node' : td.NodeWithAddress := {node := node, address := addr, eq := mem}
  show (td.generatedFacts node'.node).finite
  induction node' using mem_rec_address with
  | root => exists []; simp only [List.nodup_nil, true_and]; intro _; rw [List.mem_nil_iff]; simp only [NodeWithAddress.root]; simp [generatedFacts, Membership.mem, start_eq]
  | step new_root ih c c_mem =>
    suffices td.generatedFacts c.node ⊆ td.generatedFacts new_root.node ∪ (ChaseNode.origin_result c.node (isSome_origin_of_mem_childNodes _ (NodeWithAddress.mem_childNodes_of_mem_childNodes c_mem))).toSet by
      apply Set.finite_of_subset_finite _ this
      apply Set.union_finite_of_both_finite ih
      apply List.finite_toSet
    unfold generatedFacts
    rw [facts_childNodes (NodeWithAddress.mem_childNodes_of_mem_childNodes c_mem), NodeWithAddress.root_subderivation']
    intro f ⟨f_mem, f_nmem⟩
    rw [Set.mem_union_iff] at f_mem
    cases f_mem with
    | inl f_mem => apply Set.mem_union_of_mem_left; exact ⟨out_sub_in _ f_mem, f_nmem⟩
    | inr f_mem => exact Set.mem_union_of_mem_right f_mem

end GeneratedFacts

section Predecessors

/-!
## Predecessor Relation

Opposed to the `ChaseDerivation`, we define the predecessor relation direclty using addresses here.
This is because `ChaseNode`s may indeed occur multiple times in a `TreeDerivation` (just not in the same branch)
and therefore the approach used in `ChaseDerivation` would not quite work.
In particular, note that the `TreeDerivation` has no equivalent for `ChaseDerivation.suffix_of_suffix_of_suffix_of_head_mem`.

Also, even with the address approach, the relation is not total here (which is expected for a tree).
-/

variable {N : Type u} [CN : ChaseNode N obs rules]

/-- Node $n$ is a predecessor of node $m$ if the address of $n$ is a prefix of the address of $m$. Predecessor can therefore also be understood as ancestor in the tree. -/
@[expose]
def predecessor {td : TreeDerivation N obs rules} (n1 n2 : NodeWithAddress td) : Prop := n1.address <+: n2.address
infixl:50 " ≼ " => predecessor

/-- The predecessor relation is stable across suffixes. That is, predecessor in our suffix are also predecessor for us. We only need to cast the nodes. -/
@[grind <-]
theorem predecessor_of_suffix {td : TreeDerivation N obs rules} {new_root : NodeWithAddress td} {n1 n2 : NodeWithAddress new_root.subderivation} :
    n1 ≼ n2 -> (new_root.cast_for_new_root_node n1) ≼ (new_root.cast_for_new_root_node n2) := by
  rintro ⟨addr, eq⟩
  exists addr
  simp only [NodeWithAddress.cast_for_new_root_node]
  simp [← eq]

/-- The predecessor relation is reflexive. -/
@[grind <-]
theorem predecessor_refl {td : TreeDerivation N obs rules} {node : NodeWithAddress td} : node ≼ node := List.prefix_rfl

/-- The predecessor relation is antisymmetric. -/
@[grind ->]
theorem predecessor_antisymm {td : TreeDerivation N obs rules} {n1 n2 : NodeWithAddress td} : n1 ≼ n2 -> n2 ≼ n1 -> n1 = n2 := by
  rintro prefix1 ⟨addr2, prefix2⟩
  apply NodeWithAddress.eq_of_address_eq
  apply List.IsPrefix.eq_of_length_le prefix1
  simp [← prefix2]

/-- The predecessor relation is transitive. -/
@[grind ->]
theorem predecessor_trans {td : TreeDerivation N obs rules} {n1 n2 n3 : NodeWithAddress td} : n1 ≼ n2 -> n2 ≼ n3 -> n1 ≼ n3 := List.IsPrefix.trans

/-- Each node is the predecessor of its `childNodes`. -/
@[grind ->]
theorem node_prec_childNodes {td : TreeDerivation N obs rules} {node : NodeWithAddress td} : ∀ n ∈ node.childNodes, node ≼ n := by
  intro n
  rw [List.mem_iff_getElem]
  intro ⟨i, _, n_mem⟩
  unfold predecessor
  rw [← n_mem, NodeWithAddress.address_getElem_childNodes]
  exact List.prefix_append _ _


section StrictPredecessor

/-!
We also define a strict version of the predecessor relation (`≺`) in the obvious way.
-/

/-- A node is a strict predecessor of another if it is a predecessor but not equal. -/
@[expose]
def strict_predecessor {td : TreeDerivation N obs rules} (n1 n2 : NodeWithAddress td) : Prop := n1 ≼ n2 ∧ n1 ≠ n2
infixl:50 " ≺ " => strict_predecessor

/-- As for the predecessor relation, we can show that the relation is stable across suffixes given that we cast the nodes. -/
@[grind <-]
theorem strict_predecessor_of_suffix {td : TreeDerivation N obs rules} {new_root : NodeWithAddress td} {n1 n2 : NodeWithAddress new_root.subderivation} :
    n1 ≺ n2 -> (new_root.cast_for_new_root_node n1) ≺ (new_root.cast_for_new_root_node n2) := by
  intro prec
  constructor
  . exact predecessor_of_suffix prec.left
  . simp only [NodeWithAddress.cast_for_new_root_node]; intro contra; rw [NodeWithAddress.mk.injEq] at contra; apply prec.right; apply NodeWithAddress.eq_of_address_eq; rw [List.append_right_inj] at contra; exact contra.right

/-- The strict predecessor relation is irreflexive. -/
@[grind <-]
theorem strict_predecessor_irreflexive {td : TreeDerivation N obs rules} {n : NodeWithAddress td} : ¬ n ≺ n := by intro contra; apply contra.right; rfl

/-- A predecessor is either equal or a strict predecessor. -/
theorem eq_or_strict_of_predecessor {td : TreeDerivation N obs rules} {n1 n2 : NodeWithAddress td} : n1 ≼ n2 -> n1 = n2 ∨ n1 ≺ n2 := by
  intro prec
  cases Classical.em (n1 = n2) with
  | inl eq => apply Or.inl; exact eq
  | inr ne => apply Or.inr; exact ⟨prec, ne⟩

/-- The strict predecessor relation is asymmetric. -/
@[grind ->]
theorem strict_predecessor_asymmetric {td : TreeDerivation N obs rules} {n1 n2 : NodeWithAddress td} : n1 ≺ n2 -> ¬ n2 ≺ n1 := by
  intro prec contra; apply prec.right; apply predecessor_antisymm prec.left contra.left

/-- The strict predecessor relation is transitive. -/
@[grind ->]
theorem strict_predecessor_trans {td : TreeDerivation N obs rules} {n1 n2 n3 : NodeWithAddress td} : n1 ≺ n2 -> n2 ≺ n3 -> n1 ≺ n3 := by
  intro prec1 prec2
  constructor
  . exact predecessor_trans prec1.left prec2.left
  . grind

/-- If a node is a strict predecessor, the length of its address is strictly smaller. -/
@[grind <-]
theorem length_address_lt_of_strict_predecessor {td : TreeDerivation N obs rules} {n1 n2 : NodeWithAddress td} :
    n1 ≺ n2 -> n1.address.length < n2.address.length := by
  intro succ
  apply Nat.lt_of_le_of_ne; exact List.IsPrefix.length_le succ.left
  intro contra; apply succ.right; apply NodeWithAddress.eq_of_address_eq; exact List.IsPrefix.eq_of_length succ.left contra

/-- If n2 is a strict successor of n1, we can find the child of n1 that is on the path to n2. -/
@[expose]
def next_on_path_to_succ {td : TreeDerivation N obs rules} {n1 n2 : NodeWithAddress td} (succ : n1 ≺ n2) : NodeWithAddress td :=
  let childIndex := (n2.address.drop n1.address.length).head (by
    intro contra; rw [List.drop_eq_nil_iff] at contra
    apply succ.right
    apply NodeWithAddress.eq_of_address_eq
    exact List.IsPrefix.eq_of_length_le succ.left contra)

  have n2_addr : n2.address = n1.address ++ (childIndex :: (n2.address.drop n1.address.length).tail) := by
    apply Eq.symm
    rw [List.cons_head_tail, ← List.prefix_iff_eq_append]
    exact succ.left

  n1.childNodes[childIndex]'(by
      rw [NodeWithAddress.length_childNodes, NodeWithAddress.childNodes_subderivation]
      have address_eq := n2.eq
      rw [n2_addr, ← FiniteDegreeTree.get?_drop] at address_eq
      suffices (td.tree.drop n1.address).childNodes[childIndex]? = (td.tree.drop n1.address).get? [childIndex] by
        rw [← FiniteDegreeTree.root_drop, FiniteDegreeTree.drop_drop] at this
        cases next_eq : (td.tree.drop (n1.address ++ [childIndex])).root with
        | none =>
          rw [← FiniteDegreeTree.empty_iff_root_none] at next_eq
          suffices (td.tree.drop (n1.address ++ [childIndex])).get? (n2.address.drop n1.address.length).tail = none by
            rw [FiniteDegreeTree.get?_drop, List.append_assoc, List.singleton_append] at this
            rw [FiniteDegreeTree.get?_drop] at address_eq
            rw [this] at address_eq; simp at address_eq
          rw [next_eq]
          simp
        | some next =>
          rw [next_eq] at this
          rw [List.getElem?_eq_some_iff] at this; rcases this with ⟨goal, _⟩
          exact goal
      rw [FiniteDegreeTree.get?_childNodes]
      simp)

/-- The node that is next on the path from n1 to n2 has an address with the length of n1's address plus one. -/
@[simp, grind =]
theorem length_address_next_on_path_to_succ {td : TreeDerivation N obs rules} {n1 n2 : NodeWithAddress td} (succ : n1 ≺ n2) :
  (next_on_path_to_succ succ).address.length = n1.address.length + 1 := by simp [next_on_path_to_succ]

/-- The node that is next on the path from n1 to n2 is a child of n1. -/
@[grind ->]
theorem next_on_path_to_succ_mem_childNodes {td : TreeDerivation N obs rules} {n1 n2 : NodeWithAddress td} (succ : n1 ≺ n2) :
  next_on_path_to_succ succ ∈ n1.childNodes := by simp [next_on_path_to_succ]

/-- The node that is next on the path from n1 to n2 is a predecessor of n2 (not necessarily a strict one). -/
@[grind ->]
theorem next_on_path_to_succ_is_prec {td : TreeDerivation N obs rules} {n1 n2 : NodeWithAddress td} (succ : n1 ≺ n2) :
    next_on_path_to_succ succ ≼ n2 := by
  suffices n2.address = (next_on_path_to_succ succ).address ++ (n2.address.drop n1.address.length).tail by
    unfold predecessor; rw [this]; simp
  apply Eq.symm
  simp only [next_on_path_to_succ, NodeWithAddress.address_getElem_childNodes]
  rw [List.append_assoc, List.singleton_append]
  rw [List.cons_head_tail, ← List.prefix_iff_eq_append]
  exact succ.left

end StrictPredecessor

end Predecessors


section Branches

/-!
## Branches and Chase Result

Here, we define the branches of the `TreeDerivation`. It should be no surprise that these are `ChaseDerivation`s.
-/

variable {N : Type u} [CN : ChaseNode N obs rules]

/-- Each branch of the underlying tree can be transformed into a proper `ChaseDerivation`. -/
@[expose]
def derivation_for_branch (td : TreeDerivation N obs rules) (branch : PossiblyInfiniteList N) (branch_mem : branch ∈ td.tree.branches) : ChaseDerivation N obs rules := {
  branch := branch,
  isSome_head := by
    rw [FiniteDegreeTree.branches_eq] at branch_mem
    rcases branch_mem with ⟨head_eq, _⟩
    rw [head_eq]
    exact td.isSome_root
  triggers_exist := by
    rw [FiniteDegreeTree.mem_branches] at branch_mem
    rcases branch_mem with ⟨ns, branch_eq, ns_max⟩
    have branch_eq2 : ∀ n, (branch.drop n).head = (td.tree.drop (ns.take n)).root := by
      intro n; rw [branch_eq]; simp
    intro n node node_mem after_node after_mem
    apply ChaseNode.succ_of_mem_succ_list (td.triggers_exist (ns.take n) node (by rw [← branch_eq2]; exact node_mem))
    rw [List.mem_iff_getElem?]; exists ns.get n
    rw [FiniteDegreeTree.get?_childNodes, FiniteDegreeTree.get?_childTrees, FiniteDegreeTree.FiniteDegreeTreeWithRoot.opt_to_tree_after_tree_to_opt]
    rw [FiniteDegreeTree.drop_drop, ← InfiniteList.take_succ', ← branch_eq2, ← PossiblyInfiniteList.tail_drop, after_mem]
  triggers_active:= by
    rw [FiniteDegreeTree.mem_branches] at branch_mem
    rcases branch_mem with ⟨ns, branch_eq, ns_max⟩
    have branch_eq2 : ∀ n, (branch.drop n).head = (td.tree.drop (ns.take n)).root := by intro n; rw [branch_eq]; simp
    intro n node node_mem after_node after_mem
    have after_node_mem_childNodes : after_node ∈ (td.tree.drop (ns.take n)).childNodes := by
      rw [List.mem_iff_getElem?]; exists ns.get n
      rw [FiniteDegreeTree.get?_childNodes, FiniteDegreeTree.get?_childTrees, FiniteDegreeTree.FiniteDegreeTreeWithRoot.opt_to_tree_after_tree_to_opt]
      rw [FiniteDegreeTree.drop_drop, ← InfiniteList.take_succ', ← branch_eq2, ← PossiblyInfiniteList.tail_drop, after_mem]
    rcases td.triggers_exist (ns.take n) node (by rw [← branch_eq2]; exact node_mem) (List.ne_nil_of_mem after_node_mem_childNodes)
      with ⟨trg, act, facts_eq, orig_eq, idx_eq⟩
    specialize orig_eq after_node after_node_mem_childNodes
    rw [Option.map_eq_some_iff] at orig_eq; rcases orig_eq with ⟨orig, orig_mem, orig_eq⟩
    exists orig; constructor; exact orig_mem
    rw [orig_eq]; exact act
  fairness := by
    rw [FiniteDegreeTree.mem_branches] at branch_mem
    rcases branch_mem with ⟨ns, branch_eq, ns_max⟩
    have branch_eq2 : ∀ n, (branch.drop n).head = (td.tree.drop (ns.take n)).root := by intro n; rw [branch_eq]; simp

    intro trg
    -- Case Distinction: Is branch finite?
    cases Classical.em (∃ n : Nat, td.tree.get? (ns.take n) ≠ none ∧ ∀ m : Nat, m > n -> td.tree.get? (ns.take m) = none) with
    | inl h =>
      rcases h with ⟨n, h⟩
      exists n
      constructor
      . rcases Option.ne_none_iff_exists'.mp h.left with ⟨node, node_eq⟩
        exists node
        constructor
        . rw [branch_eq2, FiniteDegreeTree.root_drop]; exact node_eq
        . apply td.fairness_leaves
          rw [FiniteDegreeTree.mem_leaves]
          exists ns.take n
          constructor
          . exact node_eq
          . rw [FiniteDegreeTree.branchAddressIsMaximal_iff] at ns_max
            apply ns_max
            rw [FiniteDegreeTree.get?_branchForAddress]
            apply h.right
            simp
      . intro m
        rw [PossiblyInfiniteList.tail_drop, PossiblyInfiniteList.get?_drop, ← PossiblyInfiniteList.head_drop]
        rw [branch_eq2]
        rw [FiniteDegreeTree.root_drop]
        rw [h.right _ (by omega)]
        simp
    | inr h =>
      have h : ∀ n, td.tree.get? (ns.take n) ≠ none := by
        intro n contra
        induction n with
        | zero => rw [InfiniteList.take_zero] at contra; rw [← FiniteDegreeTree.root_eq] at contra; have contra' := td.isSome_root; simp [contra] at contra'
        | succ n ih =>
          apply h
          exists n
          constructor
          . exact ih
          . grind
      rcases td.fairness_infinite_branches trg with ⟨i, fairness⟩
      exists i
      constructor
      . rcases Option.ne_none_iff_exists'.mp (h i) with ⟨node, node_eq⟩
        rw [branch_eq2]
        exists node
        grind
      . grind
}

/-- The branches of the `TreeDerivation` are defined as all the `ChaseDerivation` that occur as branches in the tree. -/
@[expose]
def branches (td : TreeDerivation N obs rules) : Set (ChaseDerivation N obs rules) := fun branch =>
  branch.branch ∈ td.tree.branches

/-- We lift `FiniteDegreeTree.branches_eq` to a similar version for `TreeDerivation`s. -/
theorem branches_eq {td : TreeDerivation N obs rules} : td.branches = fun b =>
    b.head = td.root ∧ ((td.childTrees = [] ∧ b.next = none) ∨ (∃ td2 ∈ td.childTrees,
      ∃ next, ∃ (next_eq : next ∈ b.next), b.tail (by rw [next_eq]; simp) ∈ td2.branches)) := by
  unfold branches; rw [FiniteDegreeTree.branches_eq]
  ext b
  constructor
  . intro ⟨head, tail⟩
    constructor
    . unfold root ChaseDerivationSkeleton.head; simp [head]
    . cases tail with
      | inl tail => apply Or.inl; unfold childTrees ChaseDerivationSkeleton.next; simp [tail]
      | inr tail =>
        apply Or.inr
        rcases tail with ⟨td2, mem, tail⟩
        exists td.derivation_for_suffix td2 (td.tree.IsSuffix_of_mem_childTrees _ mem) (by rw [Option.isSome_iff_ne_none]; exact td2.property)
        constructor
        . rw [mem_childTrees_iff]; exact mem
        . exists td2.val.root.get (by rw [Option.isSome_iff_ne_none]; exact td2.property), (by
          unfold ChaseDerivationSkeleton.next
          rw [FiniteDegreeTree.branches_eq] at tail
          rw [tail.left]
          simp
        )
  . intro ⟨head, tail⟩
    constructor
    . unfold root ChaseDerivationSkeleton.head at head; rw [Option.get_inj] at head; exact head
    . cases tail with
      | inl tail =>
        apply Or.inl
        unfold childTrees ChaseDerivationSkeleton.next at tail
        rw [List.map_eq_nil_iff, List.attach_eq_nil_iff] at tail
        rw [← PossiblyInfiniteList.empty_iff_head_none] at tail
        exact tail
      | inr tail =>
        apply Or.inr
        rcases tail with ⟨td2, mem, next, next_mem, tail⟩
        rw [mem_childTrees_iff] at mem
        exists td2.toFiniteDegreeTreeWithRoot

/-- Each `ChaseDerivation` constructed using `derivation_for_branch` occurs in `branches`. -/
@[grind <-]
theorem derivation_for_branch_mem_branches
  {td : TreeDerivation N obs rules} {branch : PossiblyInfiniteList N} {branch_mem : branch ∈ td.tree.branches} :
  td.derivation_for_branch branch branch_mem ∈ td.branches := branch_mem

end Branches


section TermsInChase

/-!
## Terms in the Chase

We make some general observations about certain terms that might occur in the chase.

1. Constants can only originate directly from rules or from the initial fact set. No other constants can be introduced.
2. Functional terms can either also originate from the initial fact set or they are introduced as fresh terms by a trigger.

The second observation entails that the precense of a functional term that does not occur in the initial fact set implies
that the trigger that introduces this term must have been applied in some node.
-/

variable {N : Type u} [CN : ChaseNode N obs rules]

/-- Constants in the chase can only come from the initial fact set or from a constant in a rule. -/
theorem constants_node_subset_constants_fs_union_constants_rules
    (out_sub_in : CN.out_sub_in)
    {td : TreeDerivation N obs rules}
    (start_eq : CN.ingoingFacts td.root = CN.outgoingFacts td.root)
    {node : N} (node_mem : node ∈ td) :
    (CN.ingoingFacts node).constants ⊆ ((CN.outgoingFacts td.root).constants ∪ rules.head_constants) := by
  rw [mem_iff] at node_mem
  rcases node_mem with ⟨addr, node_mem⟩
  let node' : td.NodeWithAddress := {node := node, address := addr, eq := node_mem}
  show (CN.ingoingFacts node'.node).constants ⊆ ((CN.outgoingFacts td.root).constants ∪ rules.head_constants)
  induction node' using mem_rec_address with
  | root =>
    apply Set.subset_union_of_subset_left
    simp only [NodeWithAddress.root]
    rw [start_eq]
    apply Set.subset_refl
  | step new_root ih c c_mem =>
    rw [facts_childNodes (NodeWithAddress.mem_childNodes_of_mem_childNodes c_mem), NodeWithAddress.root_subderivation']
    intro d d_mem
    rw [FactSet.constants_union] at d_mem
    cases d_mem with
    | inl d_mem => apply ih; apply FactSet.constants_subset_of_subset out_sub_in; exact d_mem
    | inr d_mem =>
      let origin := (CN.origin c.node).get (isSome_origin_of_mem_childNodes _ (NodeWithAddress.mem_childNodes_of_mem_childNodes c_mem))
      apply Set.subset_trans (origin.fst.val.mapped_head_constants_subset origin.snd)
      . intro d d_mem
        rw [List.mem_toSet, List.mem_append] at d_mem
        cases d_mem with
        | inl d_mem =>
          apply ih
          rw [List.mem_flatMap] at d_mem
          rcases d_mem with ⟨t, t_mem, d_mem⟩
          rw [List.mem_map] at t_mem
          rcases t_mem with ⟨v, v_mem, t_mem⟩
          rcases FunctionFreeConjunction.mem_vars.mp (origin.fst.val.rule.frontier_subset_vars_body v_mem) with ⟨a, a_mem, v_mem'⟩
          exists origin.fst.val.subs.apply_function_free_atom a
          constructor
          . apply out_sub_in
            have := active_trigger_origin_of_mem_childNodes (NodeWithAddress.mem_childNodes_of_mem_childNodes c_mem)
            rw [NodeWithAddress.root_subderivation'] at this
            apply this.left
            unfold PreTrigger.mapped_body
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
            . exact d_mem
        | inr d_mem =>
          apply Or.inr
          exists origin.fst.val.rule
          constructor
          . exact origin.fst.property
          . unfold Rule.head_constants
            grind
      . exact d_mem

/-- Each functional term in the chase originates as a fresh term from a trigger if it was not already part of the initial fact set. -/
theorem functional_term_originates_from_some_trigger
    (out_sub_in : CN.out_sub_in)
    {td : TreeDerivation N obs rules}
    (start_eq : CN.ingoingFacts td.root = CN.outgoingFacts td.root)
    (node : NodeWithAddress td)
    {t : GroundTerm sig}
    (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok)
    (t_mem : t ∈ (CN.ingoingFacts node.node).terms) :
    t ∈ (CN.outgoingFacts td.root).terms ∨ ∃ node2, node2 ≼ node ∧ ∃ orig ∈ (CN.origin node2.node), t ∈ orig.fst.val.fresh_terms_for_head_disjunct orig.snd.val (by rw [← PreTrigger.length_mapped_head]; exact orig.snd.isLt) := by
  induction node using mem_rec_address with
  | root => apply Or.inl; rw [← start_eq]; exact t_mem
  | step new_root ih c c_mem =>
    rw [facts_childNodes (NodeWithAddress.mem_childNodes_of_mem_childNodes c_mem), NodeWithAddress.root_subderivation', FactSet.terms_union] at t_mem

    have aux : t ∈ (CN.ingoingFacts new_root.node).terms -> t ∈ (CN.outgoingFacts td.root).terms ∨ ∃ (node2 : td.NodeWithAddress), node2 ≼ c ∧ ∃ orig ∈ (CN.origin node2.node), t ∈ orig.fst.val.fresh_terms_for_head_disjunct orig.snd.val (by rw [← PreTrigger.length_mapped_head]; exact orig.snd.isLt) := by
      intro t_mem
      cases ih t_mem with
      | inl ih => apply Or.inl; exact ih
      | inr ih =>
        rcases ih with ⟨node2, prec, t_mem⟩
        apply Or.inr; exists node2; constructor;
        . apply predecessor_trans prec; grind
        . exact t_mem

    cases t_mem with
    | inl t_mem => exact aux (FactSet.terms_subset_of_subset out_sub_in _ t_mem)
    | inr t_mem =>
      unfold ChaseNode.origin_result at t_mem
      rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_head_iff] at t_mem
      cases t_mem with
      | inl t_mem => rcases t_is_func with ⟨func, ts, arity, t_is_func⟩; rcases t_mem with ⟨c, _, t_mem⟩; rw [← t_mem] at t_is_func; have contra := Eq.symm t_is_func; simp [GroundTerm.func_neq_const] at contra
      | inr t_mem =>
      cases t_mem with
      | inr t_mem =>
        apply Or.inr; exists c; constructor
        . exact predecessor_refl
        . exists (CN.origin c.node).get (isSome_origin_of_mem_childNodes _ (NodeWithAddress.mem_childNodes_of_mem_childNodes c_mem))
          simp only [Option.get_mem, true_and]
          exact t_mem
      | inl t_mem =>
        apply aux
        apply FactSet.terms_subset_of_subset out_sub_in
        have := active_trigger_origin_of_mem_childNodes (NodeWithAddress.mem_childNodes_of_mem_childNodes c_mem)
        rw [NodeWithAddress.root_subderivation'] at this
        apply FactSet.terms_subset_of_subset this.left
        rw [List.mem_map] at t_mem
        rcases t_mem with ⟨v, v_mem, t_mem⟩
        rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_body_iff]
        apply Or.inr
        exists v; simp only [t_mem, and_true]
        apply Rule.frontier_subset_vars_body; rw [Rule.mem_frontier_iff_mem_frontier_for_head]; exact ⟨_, ⟨_, v_mem⟩⟩

/-- If a functional term occurs in the chase, then the trigger that introduces this term must have been used in the chase, unless the term already occurs in the initial fact set. -/
theorem trigger_introducing_functional_term_occurs_in_chase
    (out_sub_in : CN.out_sub_in)
    {td : TreeDerivation N obs rules}
    (start_eq : CN.ingoingFacts td.root = CN.outgoingFacts td.root)
    (node : NodeWithAddress td)
    {t : GroundTerm sig}
    (t_mem_node : t ∈ (CN.ingoingFacts node.node).terms)
    {trg : RTrigger obs rules}
    {disj_idx : Nat}
    {lt : disj_idx < trg.val.rule.head.length}
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
    t ∈ (CN.outgoingFacts td.root).terms ∨ ∃ node2, node2 ≼ node ∧ ∃ orig ∈ (CN.origin node2.node), orig.fst.equiv trg ∧ orig.snd.val = disj_idx := by
  cases functional_term_originates_from_some_trigger out_sub_in start_eq node (by
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

section Generate

/-!
## Derivation Generation

We lift `FiniteDegreeTree.generate_branch` to `TreeDerivation` using a generator over `NodeWithAddress` and combine it with `FiniteDegreeTree.generate_branch_mem_branches` to obtain a `ChaseDerivation` directly.
-/

variable {N : Type u} [CN : ChaseNode N obs rules]

/-- We lift `FiniteDegreeTree.generate_branch` to `TreeDerivation`. -/
@[expose]
def generate_branch (td : TreeDerivation N obs rules)
    (start : β) (generator : β -> Option β) (mapper : β -> td.NodeWithAddress) :
    PossiblyInfiniteList N :=
  FiniteDegreeTree.generate_branch (some start) generator (fun b => (mapper b).subderivation.toFiniteDegreeTreeWithRoot)

/-- We lift `FiniteDegreeTree.generate_branch_mem_branches` to `TreeDerivation`. -/
theorem generate_branch_mem_tree_branches {td : TreeDerivation N obs rules}
    {start : β} {generator : β -> Option β} {mapper : β -> td.NodeWithAddress}
    (next_is_child : ∀ b, ∀ b' ∈ generator b, mapper b' ∈ (mapper b).childNodes)
    (maximal : ∀ b, generator b = none -> (mapper b).subderivation.childTrees = []) :
    td.generate_branch start generator mapper ∈ (mapper start).subderivation.tree.branches := by
  apply FiniteDegreeTree.generate_branch_mem_branches (start := some start) (generator := generator) (mapper := (fun b => (mapper b).subderivation.toFiniteDegreeTreeWithRoot))
  . intro b b' mem
    specialize next_is_child _ _ mem
    conv => left; simp only [toFiniteDegreeTreeWithRoot]
    rw [← mem_childTrees_iff]
    exact NodeWithAddress.subderivation_mem_childTrees_of_mem_childNodes next_is_child
  . intro b eq_none
    specialize maximal _ eq_none
    simp only [childTrees, List.map_eq_nil_iff, List.attach_eq_nil_iff] at maximal
    simp only [toFiniteDegreeTreeWithRoot]
    exact maximal
  . simp

/-- We can genearte a `ChaseDerivation` within a `TreeDerivation` using a generator function that ensures that the cnsecutive elements are children of each other and that the genearted derivation is maximal. -/
@[expose]
def generate_subderivation (td : TreeDerivation N obs rules)
    (start : β) (generator : β -> Option β) (mapper : β -> td.NodeWithAddress)
    (next_is_child : ∀ b, ∀ b' ∈ generator b, mapper b' ∈ (mapper b).childNodes)
    (maximal : ∀ b, generator b = none -> (mapper b).subderivation.childTrees = []) :
    ChaseDerivation N obs rules :=
  (mapper start).subderivation.derivation_for_branch (td.generate_branch start generator mapper) (td.generate_branch_mem_tree_branches next_is_child maximal)

/-- The result of `generate_subderivation` occurs in `TreeDerivation.branches` if it starts on the root of the tree. -/
theorem generate_subderivation_mem_branches {td : TreeDerivation N obs rules}
    {start : β} {generator : β -> Option β} {mapper : β -> td.NodeWithAddress}
    {next_is_child : ∀ b, ∀ b' ∈ generator b, mapper b' ∈ (mapper b).childNodes}
    {maximal : ∀ b, generator b = none -> (mapper b).subderivation.childTrees = []}
    (start_eq : mapper start = NodeWithAddress.root td) :
    td.generate_subderivation start generator mapper next_is_child maximal ∈ td.branches := by
  suffices td = (mapper start).subderivation by
    conv => left; rw [this]
    exact td.generate_branch_mem_tree_branches next_is_child maximal
  rw [start_eq, NodeWithAddress.subderivation_root]

/-- The head for the derivation produced by `generate_subderivation` is exactly the mapped start value. -/
@[simp, grind =]
theorem head_generate_subderivation {td : TreeDerivation N obs rules}
    {start : β} {generator : β -> Option β} {mapper : β -> td.NodeWithAddress}
    {next_is_child : ∀ b, ∀ b' ∈ generator b, mapper b' ∈ (mapper b).childNodes}
    {maximal : ∀ b, generator b = none -> (mapper b).subderivation.childTrees = []} :
    (td.generate_subderivation start generator mapper next_is_child maximal).head = (mapper start).node := by
  simp only [generate_subderivation, generate_branch, derivation_for_branch, ChaseDerivationSkeleton.head]
  simp only [FiniteDegreeTree.head_generate_branch, toFiniteDegreeTreeWithRoot, Option.map_some, Option.get_some]
  rw [← root.eq_def, NodeWithAddress.root_subderivation']

/-- The next node for the derivation produced by `generate_subderivation` is exactly the mapped value after the first generator application. -/
@[simp, grind =]
theorem next_generate_subderivation {td : TreeDerivation N obs rules}
    {start : β} {generator : β -> Option β} {mapper : β -> td.NodeWithAddress}
    {next_is_child : ∀ b, ∀ b' ∈ generator b, mapper b' ∈ (mapper b).childNodes}
    {maximal : ∀ b, generator b = none -> (mapper b).subderivation.childTrees = []} :
    (td.generate_subderivation start generator mapper next_is_child maximal).next = ((generator start).map mapper).map NodeWithAddress.node := by
  simp only [generate_subderivation, generate_branch, ChaseDerivationSkeleton.next, derivation_for_branch, FiniteDegreeTree.tail_generate_branch, FiniteDegreeTree.head_generate_branch]
  simp only [Option.bind_some, Option.map_map, toFiniteDegreeTreeWithRoot]
  rw [Option.map_congr]; intros; rw [← root.eq_def, NodeWithAddress.root_subderivation']; rfl

/-- The tail for the derivation produced by `generate_subderivation` is exactly the generated derivation when applying the generator once initially. -/
theorem tail_generate_subderivation {td : TreeDerivation N obs rules}
    {start : β} {generator : β -> Option β} {mapper : β -> td.NodeWithAddress}
    {next_is_child : ∀ b, ∀ b' ∈ generator b, mapper b' ∈ (mapper b).childNodes}
    {maximal : ∀ b, generator b = none -> (mapper b).subderivation.childTrees = []}
    (next : β) (next_mem : next ∈ (generator start)) :
    (td.generate_subderivation start generator mapper next_is_child maximal).tail (by rw [next_generate_subderivation, next_mem]; simp) =
      (td.generate_subderivation next generator mapper next_is_child maximal) := by
  rw [ChaseDerivation.mk.injEq, ChaseDerivationSkeleton.mk.injEq]
  simp only [generate_subderivation, generate_branch, ChaseDerivation.tail, ChaseDerivationSkeleton.tail, derivation_for_branch, ChaseDerivation.derivation_for_skeleton, ChaseDerivationSkeleton.derivation_for_branch_suffix]
  rw [FiniteDegreeTree.tail_generate_branch, Option.bind_some, next_mem]

/-- A node occurs in `generate_subderivation` iff there is an appropriate number of repetitions for the generator function. -/
theorem mem_generate_subderivation {td : TreeDerivation N obs rules}
    {start : β} {generator : β -> Option β} {mapper : β -> td.NodeWithAddress}
    {next_is_child : ∀ b, ∀ b' ∈ generator b, mapper b' ∈ (mapper b).childNodes}
    {maximal : ∀ b, generator b = none -> (mapper b).subderivation.childTrees = []}
    {node : N} :
    node ∈ (td.generate_subderivation start generator mapper next_is_child maximal) ↔
    ∃ n, node ∈ (((·.bind generator).repeat_fun n (some start)).map mapper).map NodeWithAddress.node := by
  rw [ChaseDerivation.mem_iff]
  simp only [generate_subderivation, generate_branch, derivation_for_branch]
  constructor
  . intro ⟨n, h⟩; exists n
    rw [FiniteDegreeTree.get?_generate_branch, Option.map_map, Option.map_eq_some_iff] at h
    rw [Option.mem_def, Option.map_map, Option.map_eq_some_iff]
    rcases h with ⟨b, h, b_eq⟩
    exists b; constructor; exact h
    suffices node = (mapper b).subderivation.root by rw [this, NodeWithAddress.root_subderivation']; simp
    rw [← b_eq]; rfl
  . intro ⟨n, h⟩; exists n
    rw [FiniteDegreeTree.get?_generate_branch, Option.map_map, Option.map_eq_some_iff]
    rw [Option.mem_def, Option.map_map, Option.map_eq_some_iff] at h
    rcases h with ⟨b, h, b_eq⟩
    exists b; constructor; exact h
    suffices node = (mapper b).subderivation.root by rw [this]; rfl
    rw [← b_eq, NodeWithAddress.root_subderivation']; simp

end Generate

end TreeDerivation

/-!
# RegularTreeDerivation

As for the `RegularChaseDerivation`, we consider the special case of `TreeDerivation` where the node type is fixed to be `RegularChaseNode` to talk about Skolem and restricted chase (but not core chase).
We abbreviate fixing this node type by introducing the `RegularTreeDerivation`.
-/

abbrev RegularTreeDerivation (obs : ObsolescenceCondition sig) (rules : RuleSet sig) := TreeDerivation (RegularChaseNode obs rules) obs rules

namespace RegularTreeDerivation

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig}

section FactMonotonicity

/-!
## Subset Monotonicity of Facts in ChaseNodes

Since `ChaseNode`s always extend the previous facts, the fact sets can only be growing along the branches of the `TreeDerivation`.
This has a couple of convenient implications. For example, the root of a `TreeDerivation` can never occur in its `childTrees`.
-/

/-- Each member's facts contain the root facts. -/
@[grind <-]
theorem facts_node_subset_every_mem {td : RegularTreeDerivation obs rules} :
    ∀ node ∈ td, td.root.facts ⊆ node.facts := by
  simp only [td.mem_iff]
  intro node ⟨addr, node_mem⟩
  let node' : td.NodeWithAddress := { node := node, address := addr, eq := node_mem }
  show td.root.facts ⊆ node'.node.facts
  induction node' using td.mem_rec_address with
  | root => apply Set.subset_refl
  | step new_root ih c c_mem =>
    apply Set.subset_trans ih
    rw [← c.node.ingoingFacts_eq, new_root.subderivation.facts_childNodes (TreeDerivation.NodeWithAddress.mem_childNodes_of_mem_childNodes c_mem)]
    apply Set.subset_union_of_subset_left
    rw [TreeDerivation.NodeWithAddress.root_subderivation']
    apply Set.subset_refl

/-- The `root` cannot occur in the `childTrees`. Otherwise, it would be introduced using a trigger but then this trigger is already obsolete since all the facts from `root` already occur in the very beginning. We use `ObsolescenceCondition.contains_trg_result_implies_cond` here. -/
theorem root_not_mem_childTrees {td : RegularTreeDerivation obs rules} :
    ¬ ∃ t ∈ td.childTrees, td.root ∈ t := by
  intro contra
  rw [td.mem_some_childTree_iff] at contra
  rcases contra with ⟨td2, suffix, contra⟩
  apply (td2.active_trigger_origin_of_mem_childNodes contra).right
  apply obs.contains_trg_result_implies_cond
  apply Set.subset_trans (td.root.facts_contain_origin_result (td.root.origin.get (td2.isSome_origin_of_mem_childNodes _ contra)) (by simp))
  apply td.facts_node_subset_every_mem
  apply td2.mem_of_mem_suffix suffix
  exact td2.root_mem

/-- By `root_not_mem_childTrees`, if we have a subtree but our root occurs in the subtree, then our subtree is equal to us. -/
@[grind ->]
theorem eq_of_suffix_of_root_mem {td1 td2 : RegularTreeDerivation obs rules}
    (suffix : td1 <:+ td2) (root_mem : td2.root ∈ td1) : td1 = td2 := by
  rw [td1.suffix_iff_eq_or_suffix_childTree] at suffix
  cases suffix with
  | inl suffix => exact suffix
  | inr suffix => rcases suffix with ⟨td3, td3_mem, suffix⟩; apply False.elim; apply td2.root_not_mem_childTrees; exists td3; grind

end FactMonotonicity

section GeneratedFacts

/-!
## Only Finitely many Generated Facts

Here we cover the special case for `RegularTreeDerivation`s.
-/

/-- Each node's facts are formed by the initial facts and its `generatedFacts`. -/
theorem facts_node_eq_union_initial_and_generated
    {td : RegularTreeDerivation obs rules}
    {node : RegularChaseNode obs rules} (mem : node ∈ td) :
    node.facts = td.root.facts ∪ td.generatedFacts node := by
  unfold TreeDerivation.generatedFacts
  apply Set.ext; intro f; constructor
  . intro f_mem; cases Classical.em (f ∈ td.root.facts) with
    | inl f_mem' => exact Set.mem_union_of_mem_left f_mem'
    | inr f_mem' => apply Set.mem_union_of_mem_right; exact ⟨f_mem, f_mem'⟩
  . intro f_mem; rw [Set.mem_union_iff] at f_mem; cases f_mem with
    | inl f_mem => exact facts_node_subset_every_mem _ mem _ f_mem
    | inr f_mem => exact f_mem.left

/-- The `generatedFacts` are always finite. -/
theorem generatedFacts_finite_of_mem
    {td : RegularTreeDerivation obs rules}
    {node : (RegularChaseNode obs rules)} (mem : node ∈ td) :
    (td.generatedFacts node).finite := by
  apply TreeDerivation.generatedFacts_finite_of_mem RegularChaseNode.out_sub_in _ mem
  rw [RegularChaseNode.ingoingFacts_eq, RegularChaseNode.outgoingFacts_eq]

end GeneratedFacts

section Predecessors

/-!
## Predecessor Relation

Here we cover the special case for `RegularChaseDerivationSkeleton`s.
-/

/-- The facts of our predecessor are a subset of our facts. -/
@[grind ->]
theorem facts_node_subset_of_prec {td : RegularTreeDerivation obs rules} {node1 node2 : td.NodeWithAddress} :
    node1 ≼ node2 -> node1.node.facts ⊆ node2.node.facts := by
  intro ⟨diff, addr_eq⟩
  have := facts_node_subset_every_mem (td := node1.subderivation) node2.node
  rw [TreeDerivation.NodeWithAddress.root_subderivation'] at this
  apply this
  rw [TreeDerivation.mem_iff]
  exists diff
  rw [← node2.eq, ← addr_eq]
  simp [TreeDerivation.NodeWithAddress.subderivation, TreeDerivation.derivation_for_suffix]

/-- Each node is a strict predecessor of its `childNodes`. -/
@[grind ->]
theorem node_strict_prec_childNodes {td : RegularTreeDerivation obs rules} {node : td.NodeWithAddress} :
    ∀ n ∈ node.childNodes, node ≺ n := by
  intro n n_mem
  constructor
  . exact td.node_prec_childNodes n n_mem
  . intro contra
    rw [← contra] at n_mem
    apply RegularTreeDerivation.root_not_mem_childTrees (td := node.subderivation)
    exists node.subderivation; constructor
    . exact node.subderivation_mem_childTrees_of_mem_childNodes n_mem
    . exact node.subderivation.root_mem

/-- The facts of a strict successor cannot be a subset of our facts. This is because strict successor nodes can only be introduced by active triggers. But if a trigger only produces facts that already exist, then it cannot be active. -/
@[grind ->]
theorem facts_not_subset_of_strict_predecessor {td : RegularTreeDerivation obs rules} {n1 n2 : td.NodeWithAddress} :
    n1 ≺ n2 -> ¬ n2.node.facts ⊆ n1.node.facts := by
  intro prec contra
  suffices ∃ c ∈ n1.childNodes, c ≼ n2 by
    rcases this with ⟨c, c_mem, c_prec⟩
    apply (n1.subderivation.active_trigger_origin_of_mem_childNodes (n1.mem_childNodes_of_mem_childNodes c_mem)).right
    apply ObsolescenceCondition.contains_trg_result_implies_cond
    apply Set.subset_trans (c.node.facts_contain_origin_result _ (by simp; rfl))
    apply Set.subset_trans (td.facts_node_subset_of_prec c_prec)
    rw [TreeDerivation.NodeWithAddress.root_subderivation']
    exact contra
  exists td.next_on_path_to_succ prec; constructor
  . exact td.next_on_path_to_succ_mem_childNodes prec
  . exact td.next_on_path_to_succ_is_prec prec

end Predecessors

section ChaseResult

/-!
## Chase Result

The chase result is the set of the results of all the `ChaseDerivation`s in the tree branches.
We already know from the `ChaseDerivation` that each element of `TreeDerivation.result` is therefore a model of the rules.
-/

/-- The result is the set of `FactSet`s that correspond to the results of the `branches`. -/
@[expose]
def result (td : RegularTreeDerivation obs rules) : Set (FactSet sig) :=
  td.branches.map (fun deriv => RegularChaseDerivationSkeleton.result deriv.toChaseDerivationSkeleton)

/-- Each element of the `result` models the rules. -/
theorem result_models_rules {td : RegularTreeDerivation obs rules} : ∀ fs ∈ td.result, fs.modelsRules rules := by
  unfold result; simp only [Set.mem_map]
  intro fs ⟨branch, _, fs_mem⟩; rw [← fs_mem]; exact RegularChaseDerivation.result_models_rules

end ChaseResult

section TermsInChase

/-!
## Terms in the Chase

We make some general observations about certain terms that might occur in the chase.

1. Constants can only originate directly from rules or from the initial fact set. No other constants can be introduced.
2. Functional terms can either also originate from the initial fact set or they are introduced as fresh terms by a trigger.

The second observation entails that the precense of a functional term that does not occur in the initial fact set implies
that the trigger that introduces this term must have been applied in some node.
-/

/-- Constants in the chase can only come from the initial fact set or from a constant in a rule. -/
theorem constants_node_subset_constants_fs_union_constants_rules
    {td : RegularTreeDerivation obs rules}
    {node : RegularChaseNode obs rules} (node_mem : node ∈ td) :
    node.facts.constants ⊆ (td.root.facts.constants ∪ rules.head_constants) := by
  apply TreeDerivation.constants_node_subset_constants_fs_union_constants_rules RegularChaseNode.out_sub_in _ node_mem
  rw [RegularChaseNode.ingoingFacts_eq, RegularChaseNode.outgoingFacts_eq]

/-- Each functional term in the chase originates as a fresh term from a trigger if it was not already part of the initial fact set. -/
theorem functional_term_originates_from_some_trigger
    {td : RegularTreeDerivation obs rules}
    (node : td.NodeWithAddress)
    {t : GroundTerm sig}
    (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok)
    (t_mem : t ∈ node.node.facts.terms) :
    t ∈ td.root.facts.terms ∨ ∃ node2, node2 ≼ node ∧ ∃ orig ∈ node2.node.origin, t ∈ orig.fst.val.fresh_terms_for_head_disjunct orig.snd.val (by rw [← PreTrigger.length_mapped_head]; exact orig.snd.isLt) := by
  apply TreeDerivation.functional_term_originates_from_some_trigger RegularChaseNode.out_sub_in _ node t_is_func t_mem
  rw [RegularChaseNode.ingoingFacts_eq, RegularChaseNode.outgoingFacts_eq]

/-- If a functional term occurs in the chase, then the trigger that introduces this term must have been used in the chase, unless the term already occurs in the initial fact set. -/
theorem trigger_introducing_functional_term_occurs_in_chase
    {td : RegularTreeDerivation obs rules}
    (node : td.NodeWithAddress)
    {t : GroundTerm sig}
    (t_mem_node : t ∈ node.node.facts.terms)
    {trg : RTrigger obs rules}
    {disj_idx : Nat}
    {lt : disj_idx < trg.val.rule.head.length}
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
    t ∈ td.root.facts.terms ∨ ∃ node2, node2 ≼ node ∧ ∃ orig ∈ node2.node.origin, orig.fst.equiv trg ∧ orig.snd.val = disj_idx := by
  apply TreeDerivation.trigger_introducing_functional_term_occurs_in_chase RegularChaseNode.out_sub_in _ node t_mem_node t_mem_trg
  rw [RegularChaseNode.ingoingFacts_eq, RegularChaseNode.outgoingFacts_eq]

/-- If a functional term occurs in the chase, then the result of the trigger that introduces this term is contained in the current node, unless the functional term already occurs in the initial fact set. -/
theorem result_of_trigger_introducing_functional_term_occurs_in_chase
    {td : RegularTreeDerivation obs rules}
    (node : td.NodeWithAddress)
    {t : GroundTerm sig}
    (t_mem_node : t ∈ node.node.facts.terms)
    {trg : RTrigger obs rules}
    {disj_idx : Nat}
    {lt : disj_idx < trg.val.rule.head.length}
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
    t ∈ td.root.facts.terms ∨ (trg.val.mapped_head[disj_idx]'(by rw [PreTrigger.length_mapped_head]; exact lt)).toSet ⊆ node.node.facts := by
  cases trigger_introducing_functional_term_occurs_in_chase node t_mem_node t_mem_trg with
  | inl t_mem => apply Or.inl; exact t_mem
  | inr t_mem =>
    apply Or.inr
    rcases t_mem with ⟨node2, prec, origin, origin_eq, equiv, index_eq⟩
    apply Set.subset_trans _ (td.facts_node_subset_of_prec prec)
    simp only [← PreTrigger.result_eq_of_equiv equiv, ← index_eq]
    exact node2.node.facts_contain_origin_result _ origin_eq

end TermsInChase

end RegularTreeDerivation

