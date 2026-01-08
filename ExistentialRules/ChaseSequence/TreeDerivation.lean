import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.Basic

import ExistentialRules.Models.Basic
import ExistentialRules.ChaseSequence.ChaseDerivation
import ExistentialRules.ChaseSequence.ChaseNode

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

def exists_trigger_list_condition (obs : ObsoletenessCondition sig) (rules : RuleSet sig) (before : ChaseNode obs rules) (after : List (ChaseNode obs rules)) (trg : RTrigger obs rules) : Prop :=
  trg.val.active before.facts ∧ after = trg.val.mapped_head.zipIdx_with_lt.attach.map (fun ⟨⟨head, i⟩, h⟩ => {
    facts := before.facts ∪ head.toSet
    origin := some ⟨trg, i⟩
    facts_contain_origin_result := by
      have : head = trg.val.mapped_head[i.val] := by rw [List.mk_mem_zipIdx_with_lt_iff_getElem] at h; rw [h]
      simp only [Option.is_none_or]
      apply Set.subset_union_of_subset_right
      rw [this]
      apply Set.subset_refl
  })

def exists_trigger_list (obs : ObsoletenessCondition sig) (rules : RuleSet sig) (before : ChaseNode obs rules) (after : List (ChaseNode obs rules)) : Prop :=
  ∃ trg : (RTrigger obs rules), exists_trigger_list_condition obs rules before after trg

def not_exists_trigger_list (obs : ObsoletenessCondition sig) (rules : RuleSet sig) (before : ChaseNode obs rules) (after : List (ChaseNode obs rules)) : Prop :=
  ¬(∃ trg : (RTrigger obs rules), trg.val.active before.facts) ∧ after = []

structure TreeDerivation (obs : ObsoletenessCondition sig) (rules : RuleSet sig) where
  tree : FiniteDegreeTree (ChaseNode obs rules)
  isSome_root : tree.root.isSome
  triggers_exist : ∀ ns : List Nat, (tree.drop ns).root.is_none_or (fun before =>
    let after := (tree.drop ns).childNodes
    (exists_trigger_list obs rules before after) ∨
    (not_exists_trigger_list obs rules before after))

  fairness_leaves : ∀ leaf, leaf ∈ tree.leaves -> ∀ trg : (RTrigger obs rules), ¬ trg.val.active leaf.facts
  fairness_infinite_branches : ∀ trg : (RTrigger obs rules), ∃ i : Nat, ∀ ns : List Nat, ns.length ≥ i ->
    (tree.get? ns).is_none_or (fun fs => ¬ trg.val.active fs.facts)

namespace TreeDerivation

  variable {obs : ObsoletenessCondition sig} {rules : RuleSet sig}

  def toFiniteDegreeTreeWithRoot (td : TreeDerivation obs rules) : FiniteDegreeTree.FiniteDegreeTreeWithRoot (ChaseNode obs rules) :=
    ⟨td.tree, by rw [← Option.isSome_iff_ne_none]; exact td.isSome_root⟩

  instance : Membership (ChaseNode obs rules) (TreeDerivation obs rules) where
    mem td node := node ∈ td.tree

  def derivation_for_branch (td : TreeDerivation obs rules) (branch : PossiblyInfiniteList (ChaseNode obs rules)) (branch_mem : branch ∈ td.tree.branches) : ChaseDerivation obs rules := {
    branch := branch,
    isSome_head := by
      rw [FiniteDegreeTree.branches_eq] at branch_mem
      rcases branch_mem with ⟨head_eq, _⟩
      rw [head_eq]
      exact td.isSome_root
    triggers_exist := by
      rcases branch_mem with ⟨ns, branch_eq, ns_max⟩
      have branch_eq2 : ∀ n, (branch.drop n).head = (td.tree.drop (ns.take n)).root := by intro n; rw [branch_eq, FiniteDegreeTree.root_drop]; rfl

      intro n
      rw [Option.is_none_or_iff]
      intro node node_eq
      have trg_ex := td.triggers_exist (ns.take n)
      rw [Option.is_none_or_iff] at trg_ex
      specialize trg_ex node (by rw [← branch_eq2, node_eq])
      cases trg_ex with
      | inl trg_ex =>
        apply Or.inl
        rcases trg_ex with ⟨trg, trg_ex⟩
        exists trg
        constructor
        . exact trg_ex.left
        . cases Decidable.em (ns.get n < trg.val.rule.head.length) with
          | inl n_lt_head_length =>
            have length_aux_1 : ns.get n < trg.val.mapped_head.length := by
              rw [trg.val.length_mapped_head]
              exact n_lt_head_length
            exists ⟨ns.get n, length_aux_1⟩
            specialize branch_eq2 n.succ
            rw [PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?_drop] at branch_eq2
            rw [PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?_tail, PossiblyInfiniteList.get?_drop, branch_eq2]
            rw [InfiniteList.take_succ', ← FiniteDegreeTree.drop_drop]
            rw [← FiniteDegreeTree.FiniteDegreeTreeWithRoot.opt_to_tree_after_tree_to_opt (t := ((td.tree.drop (ns.take n)).drop [ns.get n]))]
            rw [← FiniteDegreeTree.get?_childTrees]
            rw [← FiniteDegreeTree.get?_childNodes]
            rw [trg_ex.right]
            simp only
            rw [List.getElem?_eq_getElem (by rw [List.length_map, List.length_attach, List.length_zipIdx_with_lt]; exact length_aux_1)]
            rw [Option.some_inj]
            rw [List.getElem_map, List.getElem_attach, ChaseNode.mk.injEq]
            rw [List.zipIdx_with_lt_getElem_fst_eq_getElem]
            rw [List.zipIdx_with_lt_getElem_snd_eq_index]
            constructor
            . rfl
            . rfl
          | inr n_lt_head_length =>
            have : (td.tree.drop (ns.take n)).childNodes[ns.get n]? = none := by
              rw [trg_ex.right]
              apply List.getElem?_eq_none
              apply Nat.le_of_not_lt
              rw [List.length_map, List.length_attach, List.length_zipIdx_with_lt, trg.val.length_mapped_head]
              exact n_lt_head_length
            have : node ∈ td.tree.leaves := by
              unfold FiniteDegreeTree.leaves
              unfold PossiblyInfiniteTree.leaves
              exists (ns.take n)
              constructor
              . rw [branch_eq2, FiniteDegreeTree.root_drop] at node_eq
                exact node_eq
              . apply ns_max
                rw [PossiblyInfiniteTree.get?_branchForAddress, InfiniteList.take_succ']
                rw [FiniteDegreeTree.get?_childNodes, ← FiniteDegreeTree.FiniteDegreeTreeWithRoot.opt_to_tree_none_iff] at this
                rw [FiniteDegreeTree.get?_childTrees, FiniteDegreeTree.FiniteDegreeTreeWithRoot.tree_to_opt_none_iff] at this
                rw [FiniteDegreeTree.drop_drop, FiniteDegreeTree.root_drop] at this
                exact this
            have not_active : ¬ trg.val.active node.facts := by apply td.fairness_leaves; exact this
            have active : trg.val.active node.facts := trg_ex.left
            contradiction
      | inr trg_ex =>
        apply Or.inr
        constructor
        . exact trg_ex.left
        . specialize branch_eq2 n.succ
          rw [PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?_drop] at branch_eq2
          rw [PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?_tail, PossiblyInfiniteList.get?_drop, branch_eq2]
          rw [InfiniteList.take_succ', ← FiniteDegreeTree.drop_drop]
          rw [← FiniteDegreeTree.FiniteDegreeTreeWithRoot.opt_to_tree_after_tree_to_opt (t := ((td.tree.drop (ns.take n)).drop [ns.get n]))]
          rw [← FiniteDegreeTree.get?_childTrees]
          rw [← FiniteDegreeTree.get?_childNodes]
          rw [trg_ex.right]
          simp
    fairness := by
      rcases branch_mem with ⟨ns, branch_eq, ns_max⟩
      have branch_eq2 : ∀ n, (branch.drop n).head = (td.tree.drop (ns.take n)).root := by intro n; rw [branch_eq, FiniteDegreeTree.root_drop]; rfl

      intro trg
      -- Case Distinction: Is branch finite?
      cases Classical.em (∃ n : Nat, td.tree.get? (ns.take n) ≠ none ∧ ∀ m : Nat, m > n -> td.tree.get? (ns.take m) = none) with
      | inl h =>
        rcases h with ⟨n, h⟩
        exists n
        constructor
        . rw [Option.is_some_and_iff]
          rcases Option.ne_none_iff_exists'.mp h.left with ⟨node, node_eq⟩
          exists node
          constructor
          . rw [branch_eq2, FiniteDegreeTree.root_drop]; exact node_eq
          . apply td.fairness_leaves
            exists ns.take n
            constructor
            . exact node_eq
            . apply ns_max
              apply h.right
              simp
        . intro m
          rw [PossiblyInfiniteList.tail_drop, PossiblyInfiniteList.get?_drop, ← PossiblyInfiniteList.head_drop]
          rw [branch_eq2]
          rw [FiniteDegreeTree.root_drop]
          rw [h.right _ (by omega)]
          simp [Option.is_none_or]
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
            . intro m m_gt
              rw [← FiniteDegreeTree.root_drop] at contra
              simp only [FiniteDegreeTree.root] at contra
              rw [← PossiblyInfiniteTree.empty_iff_root_none] at contra
              rw [gt_iff_lt, ← Nat.succ_le_iff] at m_gt
              rcases Nat.exists_eq_add_of_le m_gt with ⟨K, m_gt⟩
              rw [m_gt, InfiniteList.take_add, ← FiniteDegreeTree.get?_drop]
              simp only [FiniteDegreeTree.get?]
              rw [contra, PossiblyInfiniteTree.get?_empty]
        rcases td.fairness_infinite_branches trg with ⟨i, fairness⟩
        exists i
        constructor
        . rcases Option.ne_none_iff_exists'.mp (h i) with ⟨node, node_eq⟩
          rw [branch_eq2, Option.is_some_and_iff]
          exists node
          constructor
          . rw [FiniteDegreeTree.root_drop]
            exact node_eq
          . specialize fairness (ns.take i) (by rw [InfiniteList.length_take]; simp)
            rw [Option.is_none_or_iff] at fairness
            apply fairness
            exact node_eq
        . intro m
          rw [PossiblyInfiniteList.tail_drop, PossiblyInfiniteList.get?_drop, ← PossiblyInfiniteList.head_drop]
          rw [branch_eq2]
          rw [FiniteDegreeTree.root_drop]
          apply fairness
          rw [InfiniteList.length_take]
          omega
  }

  def branches (td : TreeDerivation obs rules) : Set (ChaseDerivation obs rules) := fun branch =>
    branch.branch ∈ td.tree.branches

  def result (td : TreeDerivation obs rules) : Set (FactSet sig) := fun fs => ∃ branch, branch ∈ td.branches ∧ branch.result = fs

  -- inspired by List.IsSuffix; see https://github.com/leanprover/lean4/blob/9d4ad1273f6cea397c3066c2c83062a4410d16bf/src/Init/Data/List/Basic.lean#L1205
  def IsSuffix (td1 td2 : TreeDerivation obs rules) : Prop := td1.tree <:+ td2.tree
  infixl:50 " <:+ " => IsSuffix

  theorem mem_of_mem_suffix {cd1 cd2 : TreeDerivation obs rules} (suffix : cd1 <:+ cd2) : ∀ node ∈ cd1, node ∈ cd2 := FiniteDegreeTree.mem_of_mem_suffix suffix

  def derivation_for_suffix
      (td : TreeDerivation obs rules)
      (t2 : FiniteDegreeTree (ChaseNode obs rules))
      (suffix : t2 <:+ td.tree)
      (t2_root_some : t2.root.isSome) :
      TreeDerivation obs rules where
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
      rcases leaf_mem with ⟨ns, leaf_mem⟩
      simp only [← suffix, FiniteDegreeTree.drop, PossiblyInfiniteTree.drop_drop] at leaf_mem
      apply td.fairness_leaves
      exists (ms ++ ns)
    fairness_infinite_branches := by
      rw [Option.isSome_iff_exists] at t2_root_some; rcases t2_root_some with ⟨t2_root, t2_root_eq⟩
      rw [FiniteDegreeTree.IsSuffix_iff] at suffix
      rcases suffix with ⟨ms, suffix⟩
      rw [← suffix]
      intro trg
      rcases td.fairness_infinite_branches trg with ⟨i, fairness⟩
      exists i
      intro ns ns_length
      rw [FiniteDegreeTree.get?_drop]
      apply fairness (ms ++ ns)
      rw [List.length_append, ge_iff_le]
      apply Nat.le_add_left_of_le
      exact ns_length

  def root (td : TreeDerivation obs rules) : ChaseNode obs rules := td.tree.root.get (td.isSome_root)
  theorem root_mem {td : TreeDerivation obs rules} : td.root ∈ td := by exists []; simp [root, FiniteDegreeTree.root_eq, FiniteDegreeTree.get?, PossiblyInfiniteTree.get?]

  structure NodeWithAddress (td : TreeDerivation obs rules) where
    node : ChaseNode obs rules
    address : List Nat
    eq : td.tree.get? address = some node

  def subderivation_for_NodeWithAddress {td : TreeDerivation obs rules} (node : NodeWithAddress td) : TreeDerivation obs rules :=
    td.derivation_for_suffix (td.tree.drop node.address) (td.tree.IsSuffix_drop node.address) (by simp [FiniteDegreeTree.root_drop, node.eq])

  theorem IsSuffix_subderivation_for_NodeWithAddress {td : TreeDerivation obs rules} {node : NodeWithAddress td} : td.subderivation_for_NodeWithAddress node <:+ td := td.tree.IsSuffix_drop node.address

  def NodeWithAddress.cast_for_new_root_node
      {td : TreeDerivation obs rules}
      (new_root : NodeWithAddress td)
      (node : (td.subderivation_for_NodeWithAddress new_root).NodeWithAddress) :
      NodeWithAddress td where
    node := node.node
    address := new_root.address ++ node.address
    eq := by
      rw [← node.eq]
      simp only [subderivation_for_NodeWithAddress, derivation_for_suffix, FiniteDegreeTree.get?_drop]

  theorem NodeWithAddress.mem {td : TreeDerivation obs rules} (node : td.NodeWithAddress) : node.node ∈ td := by exists node.address; exact node.eq
  theorem NodeWithAddress.eq_of_address_eq {td : TreeDerivation obs rules} {n1 n2 : td.NodeWithAddress} : n1.address = n2.address -> n1 = n2 := by
    intro eq
    rw [NodeWithAddress.mk.injEq]
    simp only [eq, and_true]
    have eq1 := n1.eq
    have eq2 := n2.eq
    rw [eq] at eq1
    rw [eq1, Option.some_inj] at eq2
    exact eq2

  def root_NodeWithAddress (td : TreeDerivation obs rules) : NodeWithAddress td where
    node := td.root
    address := []
    eq := by simp [root, FiniteDegreeTree.root_eq]

  theorem root_NodeWithAddress_subderivation_for_NodeWithAddress {td : TreeDerivation obs rules} {node : NodeWithAddress td} : (td.subderivation_for_NodeWithAddress node).root_NodeWithAddress = { node := node.node, address := [], eq := by simp only [subderivation_for_NodeWithAddress, derivation_for_suffix, FiniteDegreeTree.get?_drop, List.append_nil]; exact node.eq } := by
    simp [subderivation_for_NodeWithAddress, derivation_for_suffix, root_NodeWithAddress, root, FiniteDegreeTree.root_drop, node.eq]

  theorem root_subderivation_for_NodeWithAddress {td : TreeDerivation obs rules} {node : NodeWithAddress td}: (td.subderivation_for_NodeWithAddress node).root = node.node := by
    simp [subderivation_for_NodeWithAddress, derivation_for_suffix, root, FiniteDegreeTree.root_drop, node.eq]

  def predecessor {td : TreeDerivation obs rules} (n1 n2 : NodeWithAddress td) : Prop := n1.address <+: n2.address
  infixl:50 " ≼ " => predecessor

  theorem predecessor_refl {td : TreeDerivation obs rules} {node : NodeWithAddress td} : node ≼ node := List.prefix_rfl
  theorem predecessor_trans {td : TreeDerivation obs rules} {n1 n2 n3 : NodeWithAddress td} : n1 ≼ n2 -> n2 ≼ n3 -> n1 ≼ n3 := List.IsPrefix.trans
  theorem predecessor_antisymm {td : TreeDerivation obs rules} {n1 n2 : NodeWithAddress td} : n1 ≼ n2 -> n2 ≼ n1 -> n1 = n2 := by
    rintro prefix1 ⟨addr2, prefix2⟩
    apply NodeWithAddress.eq_of_address_eq
    apply List.IsPrefix.eq_of_length_le prefix1
    simp [← prefix2]
  theorem predecessor_of_suffix {td : TreeDerivation obs rules} {new_root : NodeWithAddress td} {n1 n2 : NodeWithAddress (subderivation_for_NodeWithAddress new_root)} : n1 ≼ n2 -> (new_root.cast_for_new_root_node n1) ≼ (new_root.cast_for_new_root_node n2) := by
    rintro ⟨addr, eq⟩
    exists addr
    simp only [NodeWithAddress.cast_for_new_root_node]
    simp [← eq]

  def childTrees (td : TreeDerivation obs rules) : List (TreeDerivation obs rules) :=
    td.tree.childTrees.attach.map (fun t =>
      td.derivation_for_suffix t.val (by apply FiniteDegreeTree.IsSuffix_of_mem_childTrees; exact t.property) (by rw [Option.isSome_iff_ne_none]; exact t.val.property)
    )

  theorem mem_childTrees_iff {td : TreeDerivation obs rules} : ∀ c, c ∈ td.childTrees ↔ c.toFiniteDegreeTreeWithRoot ∈ td.tree.childTrees := by
    intro c
    unfold childTrees toFiniteDegreeTreeWithRoot derivation_for_suffix
    simp only [List.mem_map, List.mem_attach, true_and]
    constructor
    . rintro ⟨d, eq⟩; rw [← eq]; exact d.property
    . intro mem; exists ⟨c.toFiniteDegreeTreeWithRoot, mem⟩

  theorem IsSuffix_of_mem_childTrees {td : TreeDerivation obs rules} : ∀ td2 ∈ td.childTrees, td2 <:+ td := by intro td2 mem; apply FiniteDegreeTree.IsSuffix_of_mem_childTrees td2.toFiniteDegreeTreeWithRoot; rw [← mem_childTrees_iff]; exact mem

  theorem suffix_iff_eq_or_suffix_childTree {td1 td2 : TreeDerivation obs rules} : td1 <:+ td2 ↔ td1 = td2 ∨ ∃ td3 ∈ td2.childTrees, td1 <:+ td3 := by
    constructor
    . rintro ⟨ns, suffix⟩
      cases ns with
      | nil => apply Or.inl; rw [TreeDerivation.mk.injEq, FiniteDegreeTree.mk.injEq, PossiblyInfiniteTree.mk.injEq]; rw [InfiniteTreeSkeleton.drop_nil] at suffix; apply Eq.symm; exact suffix
      | cons hd tl =>
        apply Or.inr
        cases eq : td2.childTrees[hd]? with
        | none =>
          have contra := td1.isSome_root
          rw [Option.isSome_iff_ne_none] at contra
          apply False.elim; apply contra
          simp only [FiniteDegreeTree.root_eq, FiniteDegreeTree.get?, PossiblyInfiniteTree.get?]
          rw [← suffix, InfiniteTreeSkeleton.get_drop, List.append_nil]
          have no_orphans := td2.tree.no_orphans_closure [hd]
          simp only [childTrees, List.getElem?_map, List.getElem?_attach, Option.map_eq_none_iff, Option.pmap_eq_none_iff] at eq
          rw [FiniteDegreeTree.get?_childTrees, FiniteDegreeTree.FiniteDegreeTreeWithRoot.tree_to_opt_none_iff, FiniteDegreeTree.root_drop] at eq
          specialize no_orphans eq tl
          rw [FiniteDegreeTree.get?_drop] at no_orphans
          simp only [FiniteDegreeTree.get?, PossiblyInfiniteTree.get?, List.singleton_append] at no_orphans
          exact no_orphans
        | some c =>
          rw [List.getElem?_eq_some_iff] at eq
          rcases eq with ⟨_, eq⟩
          exists c
          constructor
          . simp [← eq]
          . exists tl; rw [← eq]; simp only [childTrees, derivation_for_suffix, List.getElem_map, List.getElem_attach, FiniteDegreeTree.get_childTrees]; exact suffix
    . intro h; cases h with
      | inl eq => rw [eq]; exact FiniteDegreeTree.IsSuffix_refl
      | inr suffix => rcases suffix with ⟨td3, td3_mem, suffix⟩; apply FiniteDegreeTree.IsSuffix_trans suffix; exact IsSuffix_of_mem_childTrees _ td3_mem

  def childNodes (td : TreeDerivation obs rules) : List (ChaseNode obs rules) := td.tree.childNodes

  def childNodes_as_NodesWithAddress (td : TreeDerivation obs rules) : List (NodeWithAddress td) := td.childNodes.zipIdx_with_lt.attach.map (fun ⟨⟨c, idx⟩, prop⟩ => {
    node := c
    address := [idx.val]
    eq := by
      rw [List.mem_zipIdx_with_lt_iff_mem_zipIdx, List.mem_zipIdx_iff_getElem?] at prop
      simp only [childNodes, FiniteDegreeTree.get?_childNodes, FiniteDegreeTree.get?_childTrees, FiniteDegreeTree.FiniteDegreeTreeWithRoot.opt_to_tree_after_tree_to_opt] at prop
      exact prop
  })

  theorem length_childNodes_as_Nodes {td : TreeDerivation obs rules} : td.childNodes_as_NodesWithAddress.length = td.childNodes.length := by
    simp [childNodes_as_NodesWithAddress, List.length_zipIdx_with_lt]

  theorem childNodes_as_NodesWithAddress_eq_childNodes {td : TreeDerivation obs rules} : td.childNodes = td.childNodes_as_NodesWithAddress.map NodeWithAddress.node := by
    apply List.ext_getElem
    . rw [List.length_map, td.length_childNodes_as_Nodes]
    intro i _ _
    simp only [childNodes_as_NodesWithAddress, List.getElem_map, List.getElem_attach]
    rw [List.zipIdx_with_lt_getElem_fst_eq_getElem]

  theorem node_getElem_childNodes_as_nodesWithAddress {td : TreeDerivation obs rules} : ∀ i (lt : i < td.childNodes_as_NodesWithAddress.length), td.childNodes_as_NodesWithAddress[i].node = td.childNodes[i]'(by rw [← length_childNodes_as_Nodes]; exact lt) := by simp [childNodes_as_NodesWithAddress_eq_childNodes]

  theorem mem_childNodes_of_mem_childNodes_as_NodesWithAddress {td : TreeDerivation obs rules} : ∀ {n}, n ∈ td.childNodes_as_NodesWithAddress -> n.node ∈ td.childNodes := by
    intro n n_mem; rw [childNodes_as_NodesWithAddress_eq_childNodes]; apply List.mem_map_of_mem; exact n_mem

  theorem childNodes_eq {td : TreeDerivation obs rules} : td.childNodes = td.childTrees.map root := by
    unfold childNodes childTrees
    rw [FiniteDegreeTree.childNodes_eq]
    apply List.ext_getElem
    . simp
    . intro i _ _; simp [derivation_for_suffix, root]

  theorem subderivation_mem_childTrees_of_mem_childNodes_as_NodesWithAddress {td : TreeDerivation obs rules} {node : NodeWithAddress td} :
      node ∈ td.childNodes_as_NodesWithAddress -> (td.subderivation_for_NodeWithAddress node) ∈ td.childTrees := by
    intro node_mem
    simp only [childNodes_as_NodesWithAddress, List.mem_map, List.mem_attach, true_and] at node_mem
    rcases node_mem with ⟨⟨node_with_idx, node_mem⟩, node_eq⟩
    rw [List.mem_zipIdx_with_lt_iff_mem_zipIdx] at node_mem
    have node_mem := List.mem_zipIdx' node_mem
    have : subderivation_for_NodeWithAddress node = td.childTrees[node_with_idx.snd.val]'(by have lt := node_with_idx.snd.isLt; simp only [childNodes_eq, List.length_map] at lt; exact lt) := by
      simp only [childTrees, List.getElem_map, List.getElem_attach, FiniteDegreeTree.get_childTrees]
      simp only [subderivation_for_NodeWithAddress]
      rw [← node_eq]
    rw [this]
    apply List.getElem_mem

  theorem mem_of_mem_childNodes {td : TreeDerivation obs rules} : ∀ n ∈ td.childNodes, n ∈ td := FiniteDegreeTree.mem_of_mem_childNodes

  theorem isSome_origin_of_mem_childNodes {td : TreeDerivation obs rules} : ∀ n ∈ td.childNodes, n.origin.isSome := by
    intro n n_mem
    have trg_ex := td.triggers_exist []
    rw [FiniteDegreeTree.drop_nil, Option.is_none_or_iff] at trg_ex
    specialize trg_ex td.root (by simp [root])
    cases trg_ex with
    | inl trg_ex => rcases trg_ex with ⟨_, _, trg_ex⟩; unfold childNodes at n_mem; rw [trg_ex] at n_mem; simp only [List.mem_map] at n_mem; rcases n_mem with ⟨a, _, eq⟩; rw [← eq]; simp
    | inr trg_ex => have contra := trg_ex.right; unfold childNodes at n_mem; rw [contra] at n_mem; simp at n_mem

  theorem active_trigger_origin_of_mem_childNodes {td : TreeDerivation obs rules} :
      ∀ {n}, (mem : n ∈ td.childNodes) -> (n.origin.get (td.isSome_origin_of_mem_childNodes _ mem)).fst.val.active td.root.facts := by
    intro n n_mem
    have trg_ex := td.triggers_exist []
    rw [FiniteDegreeTree.drop_nil, Option.is_none_or_iff] at trg_ex
    specialize trg_ex td.root (by simp [root])
    cases trg_ex with
    | inl trg_ex => rcases trg_ex with ⟨_, trg_act, trg_ex⟩; unfold childNodes at n_mem; rw [trg_ex] at n_mem; simp only [List.mem_map] at n_mem; rcases n_mem with ⟨a, _, eq⟩; simp only [← eq]; exact trg_act
    | inr trg_ex => have contra := trg_ex.right; unfold childNodes at n_mem; rw [contra] at n_mem; simp at n_mem

  theorem childNodes_ne_nil_iff_trg_ex {td : TreeDerivation obs rules} : td.childNodes ≠ [] ↔ ∃ (trg : RTrigger obs rules), trg.val.active td.root.facts := by
    constructor
    . rw [List.ne_nil_iff_exists_cons]
      rintro ⟨hd, tl, eq⟩
      exists (hd.origin.get (td.isSome_origin_of_mem_childNodes _ (by simp [eq]))).fst
      apply active_trigger_origin_of_mem_childNodes
      simp [eq]
    . rintro ⟨trg, active⟩
      intro eq_nil
      apply td.fairness_leaves td.root _ trg active
      exists []
      simp only [root, Option.some_get, FiniteDegreeTree.root, PossiblyInfiniteTree.root_eq, true_and]
      simp only [childNodes, FiniteDegreeTree.childNodes, PossiblyInfiniteList.toList_of_finite_empty_iff] at eq_nil
      simp only [PossiblyInfiniteTree.drop_nil]
      rw [← PossiblyInfiniteList.empty_iff_head_none]
      exact eq_nil

  theorem facts_childNodes {td : TreeDerivation obs rules} :
      ∀ {n}, (mem : n ∈ td.childNodes) -> n.facts = td.root.facts ∪ (n.origin_result (td.isSome_origin_of_mem_childNodes _ mem)).toSet := by
    intro n n_mem
    have trg_ex := td.triggers_exist []
    rw [FiniteDegreeTree.drop_nil, Option.is_none_or_iff] at trg_ex
    specialize trg_ex td.root (by simp [root])
    cases trg_ex with
    | inl trg_ex =>
      rcases trg_ex with ⟨trg, trg_act, trg_ex⟩; unfold childNodes at n_mem; rw [trg_ex] at n_mem; simp only [List.mem_map] at n_mem
      rcases n_mem with ⟨head, _, eq⟩; simp only [← eq]
      have head_mem := head.property
      rw [List.mem_zipIdx_with_lt_iff_mem_zipIdx, List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff] at head_mem
      rcases head_mem with ⟨_, head_mem⟩
      simp only at head_mem
      simp only [← head_mem]
      rfl
    | inr trg_ex => have contra := trg_ex.right; unfold childNodes at n_mem; rw [contra] at n_mem; simp at n_mem

  theorem root_prec_childNodes {td : TreeDerivation obs rules} : ∀ n ∈ td.childNodes_as_NodesWithAddress, td.root_NodeWithAddress ≼ n := by
    intros; exact List.nil_prefix

  theorem mem_rec_address
      {td : TreeDerivation obs rules}
      {motive : NodeWithAddress td -> Prop}
      (root : motive td.root_NodeWithAddress)
      (step : ∀ (new_root : NodeWithAddress td), motive new_root -> ∀ c, (mem : c ∈ (td.subderivation_for_NodeWithAddress new_root).childNodes_as_NodesWithAddress) -> motive (NodeWithAddress.cast_for_new_root_node new_root c))
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
        have eq : td.root_NodeWithAddress = {node := n, address := [].reverse, eq := n_mem} := by apply NodeWithAddress.eq_of_address_eq; simp [root_NodeWithAddress]
        rw [← eq]
        exact root
      | cons hd tl ih =>
        intro n n_mem
        cases eq : td.tree.get? tl.reverse with
        | none =>
          have contra := td.tree.no_orphans_closure tl.reverse eq [hd]
          rw [FiniteDegreeTree.get?_drop] at contra
          rw [List.reverse_cons, contra] at n_mem
          simp at n_mem
        | some m =>
          have n_mem : n ∈ (td.tree.drop tl.reverse).childNodes[hd]? := by rw [FiniteDegreeTree.get?_childNodes, FiniteDegreeTree.get?_childTrees, FiniteDegreeTree.FiniteDegreeTreeWithRoot.opt_to_tree_after_tree_to_opt, FiniteDegreeTree.root_drop, FiniteDegreeTree.get?_drop]; rw [List.reverse_cons] at n_mem; exact n_mem
          let new_root : td.NodeWithAddress := { node := m, address := tl.reverse, eq := eq }
          specialize step new_root (ih m eq) _ (by
            simp only [childNodes_as_NodesWithAddress, List.mem_map]
            exists ⟨⟨n, ⟨hd, by
                simp only [subderivation_for_NodeWithAddress, derivation_for_suffix, childNodes, new_root]
                rw [Option.mem_def, List.getElem?_eq_some_iff] at n_mem
                rcases n_mem with ⟨lt, _⟩
                exact lt⟩⟩, by
              rw [List.mem_zipIdx_with_lt_iff_mem_zipIdx, List.mem_zipIdx_iff_getElem?]
              simp only [subderivation_for_NodeWithAddress, derivation_for_suffix, childNodes, new_root]
              exact n_mem⟩
            constructor; simp; rfl)
          simp only [NodeWithAddress.cast_for_new_root_node, new_root] at step
          simp only [List.reverse_cons]
          exact step
    specialize this node.node (by simp only [rev_addr_node, List.reverse_reverse]; exact node.eq)
    simp only [rev_addr_node, List.reverse_reverse] at this
    exact this

  theorem mem_some_childTree_iff {td : TreeDerivation obs rules} {node : ChaseNode obs rules} :
      (∃ t ∈ td.childTrees, node ∈ t) ↔ ∃ td2, td2 <:+ td ∧ node ∈ td2.childNodes := by
    constructor
    . rintro ⟨t, t_mem, node_mem⟩
      rcases node_mem with ⟨addr, node_mem⟩
      let node' : t.NodeWithAddress := { node := node, address := addr, eq := node_mem }
      show ∃ td2, td2 <:+ td ∧ node'.node ∈ td2.childNodes
      induction node' using mem_rec_address with
      | root => exists td; constructor; exact td.tree.IsSuffix_refl; simp only [childNodes_eq, root_NodeWithAddress]; apply List.mem_map_of_mem; exact t_mem
      | step new_root ih c c_mem =>
        exists subderivation_for_NodeWithAddress new_root; constructor
        . apply FiniteDegreeTree.IsSuffix_trans IsSuffix_subderivation_for_NodeWithAddress; exact IsSuffix_of_mem_childTrees _ t_mem
        . rw [childNodes_as_NodesWithAddress_eq_childNodes]; apply List.mem_map_of_mem; exact c_mem
    . rintro ⟨td2, suffix, node_mem⟩
      rcases suffix with ⟨ns, suffix⟩
      cases ns with
      | nil =>
        have : td = td2 := by rw [TreeDerivation.mk.injEq, FiniteDegreeTree.mk.injEq, PossiblyInfiniteTree.mk.injEq]; rw [InfiniteTreeSkeleton.drop_nil] at suffix; exact suffix
        rw [childNodes_eq, List.mem_map] at node_mem; rcases node_mem with ⟨t, t_mem, node_mem⟩; exists t; constructor; rw [this]; exact t_mem; rw [← node_mem]; exact root_mem
      | cons hd tl =>
        cases eq : td.childTrees[hd]? with
        | none =>
          have contra := td2.isSome_root
          rw [Option.isSome_iff_ne_none] at contra
          apply False.elim; apply contra
          simp only [FiniteDegreeTree.root_eq, FiniteDegreeTree.get?, PossiblyInfiniteTree.get?]
          rw [← suffix, InfiniteTreeSkeleton.get_drop, List.append_nil]
          have no_orphans := td.tree.no_orphans_closure [hd]
          simp only [childTrees, List.getElem?_map, List.getElem?_attach, Option.map_eq_none_iff, Option.pmap_eq_none_iff] at eq
          rw [FiniteDegreeTree.get?_childTrees, FiniteDegreeTree.FiniteDegreeTreeWithRoot.tree_to_opt_none_iff, FiniteDegreeTree.root_drop] at eq
          specialize no_orphans eq tl
          rw [FiniteDegreeTree.get?_drop] at no_orphans
          simp only [FiniteDegreeTree.get?, PossiblyInfiniteTree.get?, List.singleton_append] at no_orphans
          exact no_orphans
        | some t =>
          rw [List.getElem?_eq_some_iff] at eq; rcases eq with ⟨_, eq⟩
          exists t; constructor; simp [← eq]
          have : td2 <:+ t := by exists tl; rw [← eq]; simp only [childTrees, derivation_for_suffix, List.getElem_map, List.getElem_attach, FiniteDegreeTree.get_childTrees, FiniteDegreeTree.drop, PossiblyInfiniteTree.drop]; rw [InfiniteTreeSkeleton.drop_drop, List.singleton_append]; exact suffix
          apply mem_of_mem_suffix this
          apply mem_of_mem_childNodes
          exact node_mem

  theorem facts_node_subset_every_mem {td : TreeDerivation obs rules} : ∀ node ∈ td, td.root.facts ⊆ node.facts := by
    rintro node ⟨addr, node_mem⟩
    let node' : td.NodeWithAddress := { node := node, address := addr, eq := node_mem }
    show td.root.facts ⊆ node'.node.facts
    induction node' using mem_rec_address with
    | root => apply Set.subset_refl
    | step new_root ih c c_mem =>
      apply Set.subset_trans ih
      simp only [NodeWithAddress.cast_for_new_root_node]
      rw [facts_childNodes (mem_childNodes_of_mem_childNodes_as_NodesWithAddress c_mem)]
      apply Set.subset_union_of_subset_left
      rw [root_subderivation_for_NodeWithAddress]
      apply Set.subset_refl

  theorem facts_node_subset_of_prec {td : TreeDerivation obs rules} {node1 node2 : td.NodeWithAddress} : node1 ≼ node2 -> node1.node.facts ⊆ node2.node.facts := by
    rintro ⟨diff, addr_eq⟩
    have := (subderivation_for_NodeWithAddress node1).facts_node_subset_every_mem node2.node
    rw [root_subderivation_for_NodeWithAddress] at this
    apply this
    exists diff
    rw [← node2.eq, ← addr_eq]
    rfl

  theorem root_not_mem_childTrees {td : TreeDerivation obs rules} : ¬ ∃ t ∈ td.childTrees, td.root ∈ t := by
    intro contra
    rw [mem_some_childTree_iff] at contra
    rcases contra with ⟨td2, suffix, contra⟩
    apply (td2.active_trigger_origin_of_mem_childNodes contra).right
    apply obs.contains_trg_result_implies_cond
    have := td.root.facts_contain_origin_result
    rw [Option.is_none_or_iff] at this
    specialize this (td.root.origin.get (td2.isSome_origin_of_mem_childNodes _ contra)) (by simp)
    apply Set.subset_trans this
    apply td.facts_node_subset_every_mem
    apply mem_of_mem_suffix suffix
    exact td2.root_mem

  theorem eq_of_suffix_of_root_mem {td1 td2 : TreeDerivation obs rules} (suffix : td1 <:+ td2) (root_mem : td2.root ∈ td1) : td1 = td2 := by
    rw [suffix_iff_eq_or_suffix_childTree] at suffix
    cases suffix with
    | inl suffix => exact suffix
    | inr suffix => rcases suffix with ⟨td3, td3_mem, suffix⟩; apply False.elim; apply td2.root_not_mem_childTrees; exists td3; constructor; exact td3_mem; apply mem_of_mem_suffix suffix; exact root_mem

  theorem constants_node_subset_constants_fs_union_constants_rules {td : TreeDerivation obs rules} {node : ChaseNode obs rules} (node_mem : node ∈ td) :
      node.facts.constants ⊆ (td.root.facts.constants ∪ rules.head_constants) := by
    rcases node_mem with ⟨addr, node_mem⟩
    let node' : td.NodeWithAddress := {node := node, address := addr, eq := node_mem}
    show node'.node.facts.constants ⊆ (td.root.facts.constants ∪ rules.head_constants)
    induction node' using mem_rec_address with
    | root =>
      apply Set.subset_union_of_subset_left
      apply Set.subset_refl
    | step new_root ih c c_mem =>
      simp only [NodeWithAddress.cast_for_new_root_node]
      rw [facts_childNodes (mem_childNodes_of_mem_childNodes_as_NodesWithAddress c_mem), root_subderivation_for_NodeWithAddress]
      intro d d_mem
      rw [FactSet.constants_union] at d_mem
      cases d_mem with
      | inl d_mem => apply ih; exact d_mem
      | inr d_mem =>
        let origin := c.node.origin.get (isSome_origin_of_mem_childNodes _ (mem_childNodes_of_mem_childNodes_as_NodesWithAddress c_mem))
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
            . have := active_trigger_origin_of_mem_childNodes (mem_childNodes_of_mem_childNodes_as_NodesWithAddress c_mem)
              rw [root_subderivation_for_NodeWithAddress] at this
              apply this.left
              rw [List.mem_toSet]
              unfold PreTrigger.mapped_body
              unfold GroundSubstitution.apply_function_free_conj
              apply List.mem_map_of_mem
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
                  rw [PreTrigger.apply_to_var_or_const_frontier_var] at t_mem
                  . exact t_mem
                  . exact v_mem
              . exact d_mem
          | inr d_mem =>
            apply Or.inr
            exists origin.fst.val.rule
            constructor
            . exact origin.fst.property
            . unfold Rule.head_constants
              rw [List.mem_flatMap]
              exists origin.fst.val.rule.head[origin.snd.val]'(by rw [← PreTrigger.length_mapped_head]; exact origin.snd.isLt)
              constructor
              . apply List.get_mem
              . exact d_mem
        . exact d_mem

  theorem result_models_rules {td : TreeDerivation obs rules} : ∀ fs ∈ td.result, fs.modelsRules rules := by
    rintro fs ⟨branch, _, fs_mem⟩; rw [← fs_mem]; apply branch.result_models_rules

  theorem functional_term_originates_from_some_trigger
      {td : TreeDerivation obs rules}
      (node : NodeWithAddress td)
      {t : GroundTerm sig}
      (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok)
      (t_mem : t ∈ node.node.facts.terms) :
      t ∈ td.root.facts.terms ∨ ∃ node2, node2 ≼ node ∧ node2.node.origin.is_some_and (fun origin => t ∈ origin.fst.val.fresh_terms_for_head_disjunct origin.snd.val (by rw [← PreTrigger.length_mapped_head]; exact origin.snd.isLt)) := by
    induction node using mem_rec_address with
    | root => apply Or.inl; exact t_mem
    | step new_root ih c c_mem =>
      simp only [NodeWithAddress.cast_for_new_root_node] at t_mem
      rw [facts_childNodes (mem_childNodes_of_mem_childNodes_as_NodesWithAddress c_mem), root_subderivation_for_NodeWithAddress, FactSet.terms_union] at t_mem

      have aux : t ∈ new_root.node.facts.terms -> t ∈ td.root.facts.terms ∨ ∃ (node2 : td.NodeWithAddress), node2 ≼ (NodeWithAddress.cast_for_new_root_node new_root c) ∧ node2.node.origin.is_some_and (fun origin => t ∈ origin.fst.val.fresh_terms_for_head_disjunct origin.snd.val (by rw [← PreTrigger.length_mapped_head]; exact origin.snd.isLt)) := by
        intro t_mem
        cases ih t_mem with
        | inl ih => apply Or.inl; exact ih
        | inr ih =>
          rcases ih with ⟨node2, prec, t_mem⟩
          apply Or.inr; exists node2; constructor;
          . apply predecessor_trans prec
            have : new_root = new_root.cast_for_new_root_node (subderivation_for_NodeWithAddress new_root).root_NodeWithAddress := by
              apply NodeWithAddress.eq_of_address_eq
              rw [root_NodeWithAddress_subderivation_for_NodeWithAddress]
              simp [NodeWithAddress.cast_for_new_root_node]
            conv => left; rw [this]
            apply predecessor_of_suffix
            apply root_prec_childNodes
            exact c_mem
          . exact t_mem

      cases t_mem with
      | inl t_mem => exact aux t_mem
      | inr t_mem =>
        unfold ChaseNode.origin_result at t_mem
        rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_head_iff] at t_mem
        cases t_mem with
        | inl t_mem => rcases t_is_func with ⟨func, ts, arity, t_is_func⟩; rcases t_mem with ⟨c, _, t_mem⟩; rw [← t_mem] at t_is_func; simp [GroundTerm.const, GroundTerm.func] at t_is_func
        | inr t_mem =>
        cases t_mem with
        | inr t_mem =>
          apply Or.inr; exists new_root.cast_for_new_root_node c; constructor
          . exact predecessor_refl
          . rw [Option.is_some_and_iff]
            exists c.node.origin.get (isSome_origin_of_mem_childNodes _ (mem_childNodes_of_mem_childNodes_as_NodesWithAddress c_mem))
            simp only [NodeWithAddress.cast_for_new_root_node, Option.some_get, true_and]
            exact t_mem
        | inl t_mem =>
          apply aux
          have := active_trigger_origin_of_mem_childNodes (mem_childNodes_of_mem_childNodes_as_NodesWithAddress c_mem)
          rw [root_subderivation_for_NodeWithAddress] at this
          apply FactSet.terms_subset_of_subset this.left
          rw [List.mem_map] at t_mem
          rcases t_mem with ⟨v, v_mem, t_mem⟩
          rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_body_iff]
          apply Or.inr
          exists v; simp only [t_mem, and_true]
          apply Rule.frontier_subset_vars_body; rw [Rule.mem_frontier_iff_mem_frontier_for_head]; exact ⟨_, v_mem⟩

  theorem trigger_introducing_functional_term_occurs_in_chase
      {td : TreeDerivation obs rules}
      (node : NodeWithAddress td)
      {t : GroundTerm sig}
      (t_mem_node : t ∈ node.node.facts.terms)
      {trg : RTrigger obs rules}
      {disj_idx : Nat}
      {lt : disj_idx < trg.val.rule.head.length}
      (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
      t ∈ td.root.facts.terms ∨ ∃ node2, node2 ≼ node ∧ node2.node.origin.is_some_and (fun origin => origin.fst.equiv trg ∧ origin.snd.val = disj_idx) := by
    cases functional_term_originates_from_some_trigger node (by
      cases eq : t with
      | const _ =>
        rw [eq] at t_mem_trg
        simp [PreTrigger.fresh_terms_for_head_disjunct, PreTrigger.functional_term_for_var, GroundTerm.func, GroundTerm.const] at t_mem_trg
      | func func ts arity_ok => exists func, ts, arity_ok
    ) t_mem_node with
    | inl t_mem => apply Or.inl; exact t_mem
    | inr t_mem =>
      apply Or.inr
      simp only [Option.is_some_and_iff] at t_mem
      rcases t_mem with ⟨node2, prec, origin, origin_eq, t_mem⟩
      simp only [Option.is_some_and_iff]
      exists node2; simp only [prec, true_and]
      exists origin; simp only [origin_eq, true_and]
      exact RTrigger.equiv_of_term_mem_fresh_terms_for_head_disjunct t_mem t_mem_trg

  theorem result_of_trigger_introducing_functional_term_occurs_in_chase
      {td : TreeDerivation obs rules}
      (node : NodeWithAddress td)
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
      simp only [Option.is_some_and_iff] at t_mem
      rcases t_mem with ⟨node2, prec, origin, origin_eq, equiv, index_eq⟩
      apply Set.subset_trans _ (td.facts_node_subset_of_prec prec)
      have := node2.node.facts_contain_origin_result
      simp only [origin_eq, Option.is_none_or] at this
      simp only [← PreTrigger.result_eq_of_equiv equiv, ← index_eq]
      exact this

end TreeDerivation

