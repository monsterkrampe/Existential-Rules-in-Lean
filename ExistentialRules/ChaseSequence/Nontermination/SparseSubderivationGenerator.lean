/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.TreeDerivation

/-!

# Generate Branch in Tree Derivation from Sparse Sequence

The `TreeDerivation` already offers functionality for generating `ChaseDerivation` that correspond to branches in the tree.
However, the generating function is forces to always yield an immediate child node, which is too restrictive for what we
aim to do in the non-termination conditions like RPC.
Instead, we get a generator that will always yield a node that occurs somewhere in the subtree of the previous node.
We can then "fill in the gaps" to get the full branch. We do this by adjusting the generator function to fill in the blanks for us.
This is a bit technical but hopefully abstracted away enough so that the internals are irrelevant outside of this file.

-/

namespace TreeDerivation

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig}
variable {N : Type u} [CN : ChaseNode N obs rules]

namespace NodeWithAddress

/-- Given a node and an list of natural numbers, representing an address starting at the node, returns the list of nodes along the address (not including the starting node).  -/
def nodes_along_address {td : TreeDerivation N obs rules} (node : NodeWithAddress td) : List Nat -> List (NodeWithAddress td)
| [] => []
| hd :: tl =>
  (node.childNodes[hd]?.map (fun child =>
    child :: child.nodes_along_address tl
  )).getD []

/-- The first node in `nodes_along_address` is a child of the starting node. -/
theorem head_of_nodes_along_address_mem_childNodes {td : TreeDerivation N obs rules} {node : NodeWithAddress td} (addr : List Nat) :
    ∀ hd ∈ (node.nodes_along_address addr).head?, hd ∈ node.childNodes := by
  fun_cases nodes_along_address; simp; grind

/-- If the address starts with number $i$, then the head of `nodes_along_address` is the $i$-th child of the starting node.-/
theorem head_nodes_along_address_of_cons
    {td : TreeDerivation N obs rules} {node : NodeWithAddress td} (addr_hd : Nat) (addr_tl : List Nat) :
    (node.nodes_along_address (addr_hd :: addr_tl)).head? = node.childNodes[addr_hd]? := by
  simp only [nodes_along_address]; grind

/-- Given two nodes, returns the list of nodes that form the path from one to the other (omitting start and end). This uses `nodes_along_address` internally. -/
def nodes_to {td : TreeDerivation N obs rules} (node1 node2 : NodeWithAddress td) : List (NodeWithAddress td) :=
  node1.nodes_along_address (node2.address.drop node1.address.length).dropLast

/-- The `nodes_to` list from a node to itself is empty. -/
theorem nodes_to_self
    {td : TreeDerivation N obs rules} {node : NodeWithAddress td} :
    node.nodes_to node = [] := by
  simp [nodes_to, nodes_along_address]

/-- The `nodes_to` list from a node to one of its children is empty. -/
theorem nodes_to_child
    {td : TreeDerivation N obs rules} {node1 node2 : NodeWithAddress td} (child : node2 ∈ node1.childNodes) :
    node1.nodes_to node2 = [] := by
  rw [List.mem_iff_getElem] at child; rcases child with ⟨i, lt, child⟩
  unfold nodes_to
  suffices node2.address.drop node1.address.length = [i] by rw [this]; simp [nodes_along_address]
  rw [← child]; simp

/-- The `nodes_to` list from a node to one of its successors that is not an immediate child starts with the node defined by `next_on_path_to_succ`. -/
theorem nodes_to_succ_of_no_child_node
    {td : TreeDerivation N obs rules} {node1 node2 : NodeWithAddress td} (succ : node1 ≺ node2) (no_child : node2 ∉ node1.childNodes) :
    node1.nodes_to node2 = next_on_path_to_succ succ :: (next_on_path_to_succ succ).nodes_to node2 := by
  unfold nodes_to
  cases eq : node2.address.drop node1.address.length with
  | nil =>
    exfalso
    apply succ.right
    apply eq_of_address_eq
    apply List.IsPrefix.eq_of_length_le
    . exact succ.left
    . exact List.drop_eq_nil_iff.mp eq
  | cons hd tl =>
    rw [length_address_next_on_path_to_succ]
    cases tl with
    | nil =>
      exfalso
      apply no_child
      suffices node2 = next_on_path_to_succ succ by rw [this]; exact next_on_path_to_succ_mem_childNodes succ
      apply eq_of_address_eq
      rw [← List.prefix_iff_eq_append.mp succ.left]
      simp only [next_on_path_to_succ, eq]
      simp
    | cons hd2 tl2 =>
      rw [List.drop_eq_getElem_cons (length_address_lt_of_strict_predecessor succ), List.cons_eq_cons] at eq
      rw [eq.right]
      rw [List.dropLast_cons_cons]
      simp only [nodes_along_address]
      suffices node1.childNodes[hd]? = some (next_on_path_to_succ succ) by rw [this]; simp
      rw [← eq.left]
      simp [next_on_path_to_succ]

/-- For two distinct nodes in succession, the head of `nodes_to` is a child of the first node. -/
theorem nodes_to.head_child {td : TreeDerivation N obs rules} {node1 node2 : NodeWithAddress td} (succ : node1 ≺ node2) :
    (node1.nodes_to node2).headD node2 ∈ node1.childNodes := by
  cases Decidable.em (node2 ∈ node1.childNodes) with
  | inl child => rw [nodes_to_child child]; simpa using child
  | inr no_child => rw [nodes_to_succ_of_no_child_node succ no_child, List.headD_cons]; exact next_on_path_to_succ_mem_childNodes succ

/-- For two distinct nodes in succession, the second node is a child of the last element of the `nodes_to` list. -/
theorem nodes_to.last_child {td : TreeDerivation N obs rules} {node1 node2 : NodeWithAddress td} (succ : node1 ≺ node2) :
    node2 ∈ ((node1.nodes_to node2).getLastD node1).childNodes := by
  cases Decidable.em (node2 ∈ node1.childNodes) with
  | inl child => rw [nodes_to_child child]; simpa using child
  | inr no_child =>
    rw [nodes_to_succ_of_no_child_node succ no_child]
    cases eq_or_strict_of_predecessor (next_on_path_to_succ_is_prec succ) with
    | inr strict =>
      have _term : node2.address.length - (node1.address.length + 1) < node2.address.length - node1.address.length := by
        apply Nat.sub_succ_lt_self; exact length_address_lt_of_strict_predecessor succ
      rw [List.getLastD_cons]; apply nodes_to.last_child; exact strict
    | inl eq =>
      exfalso
      apply no_child
      rw [← eq]
      exact next_on_path_to_succ_mem_childNodes succ
termination_by node2.address.length - node1.address.length

/-- This definition expresses the condition that, in a list of nodes, each node is a child of the previous one. This is trivially true for empty or singleton lists. -/
def list_children_of_each_other {td : TreeDerivation N obs rules} : List (NodeWithAddress td) -> Prop
| [] => True
| [_] => True
| hd :: hd2 :: tl => hd2 ∈ hd.childNodes ∧ list_children_of_each_other (hd2 :: tl)

/-- The nodes returned by `nodes_along_address` are children of each other. -/
theorem nodes_along_address.children_of_each_other {td : TreeDerivation N obs rules} {node : NodeWithAddress td} {addr : List Nat} :
    list_children_of_each_other (node.nodes_along_address addr) := by
  fun_induction nodes_along_address with
  | case1 _ => simp [list_children_of_each_other]
  | case2 node hd tl ih =>
    cases node.childNodes[hd]? with
    | none => simp [list_children_of_each_other]
    | some child =>
      specialize ih child
      rw [Option.map_some, Option.getD_some]
      fun_cases nodes_along_address with
      | case1 => simp [list_children_of_each_other]
      | case2 hd2 tl2 =>
        simp only [nodes_along_address] at ih
        cases eq : child.childNodes[hd2]? with
        | none => simp [list_children_of_each_other]
        | some child2 =>
          rw [Option.map_some, Option.getD_some]
          rw [eq, Option.map_some, Option.getD_some] at ih
          constructor
          . rw [List.getElem?_eq_some_iff] at eq; rcases eq with ⟨_, eq⟩
            rw [← eq]
            apply List.getElem_mem
          . exact ih

/-- The nodes returned by `nodes_to` are children of each other. -/
theorem nodes_to.children_of_each_other {td : TreeDerivation N obs rules} {node1 node2 : NodeWithAddress td} :
  list_children_of_each_other (node1.nodes_to node2) := nodes_along_address.children_of_each_other

end NodeWithAddress

/-- For the a type `β` used in a sparse generator function, the densified type associates each `β` element with a list of nodes that intuitively fill the gap from one generated value to the next (not including the generated values). -/
abbrev DensifiedResult (β : Type u) (td : TreeDerivation N obs rules) := β × List (NodeWithAddress td)

/-- A `DensifiedResult` is `wellFormed` if the node corresponding to the `β` element is a child of the last node in the filler list and if the nodes in the filler list are children of each other. If the filler list is empty, then this is trivially true. -/
def DensifiedResult.wellFormed {β : Type u} {td : TreeDerivation N obs rules} (mapper : β -> NodeWithAddress td) (dr : DensifiedResult β td) : Prop :=
  match dr.snd with
  | [] => True
  | hd :: tl =>
    (mapper dr.fst) ∈ ((hd :: tl).getLast (by simp)).childNodes ∧ NodeWithAddress.list_children_of_each_other (hd :: tl)

/-- For a given generator function over a type `β`, this function constructs a densified generator function operating on a `DensifiedResult`. If the previous `DensifiedResult` already contains a filler list, then the function simply drops the first element. Otherwise the function uses the original generator to obtain the next `β` value and constructs a filler list using the `nodes_to` function. -/
def densify_generator {β : Type u} (td : TreeDerivation N obs rules) (generator : β -> Option β) (mapper : β -> NodeWithAddress td) :
    DensifiedResult β td -> Option (DensifiedResult β td)
| (b, []) =>
  (generator b).map (fun b' =>
    (b', (mapper b).nodes_to (mapper b'))
  )
| (b, _::tl) => some (b, tl)

/-- For a `wellFormed` input, the `densify_generator` again returns a `wellFormed` result. -/
theorem densify_generator.wellFormed {β : Type u} {td : TreeDerivation N obs rules} {generator : β -> Option β} {mapper : β -> NodeWithAddress td}
    (next_is_succ : ∀ b, ∀ b' ∈ generator b, mapper b ≺ mapper b') :
    ∀ dr : DensifiedResult β td, dr.wellFormed mapper -> ∀ next ∈ td.densify_generator generator mapper dr, next.wellFormed mapper := by
  intro dr wellFormed next
  fun_cases densify_generator with
  | case1 b =>
    rw [Option.mem_def, Option.map_eq_some_iff]
    intro ⟨b', b'_eq, next_eq⟩
    rw [← next_eq]
    fun_cases DensifiedResult.wellFormed mapper (b', _) with
    | case1 => simp
    | case2 hd tl eq =>
      simp only at eq
      rw [List.getLast_eq_getLastD]
      have : tl.getLastD hd = ((mapper b).nodes_to (mapper b')).getLastD (mapper b) := by rw [eq, List.getLastD_cons]
      rw [this, ← eq]
      constructor
      . apply NodeWithAddress.nodes_to.last_child
        exact next_is_succ _ _ b'_eq
      . exact NodeWithAddress.nodes_to.children_of_each_other
  | case2 b hd tl =>
    rw [Option.mem_some]; intro eq; rw [← eq]
    simp only [DensifiedResult.wellFormed] at wellFormed
    fun_cases DensifiedResult.wellFormed with
    | case1 => simp
    | case2 hd2 tl2 eq2 =>
      simp only at eq2
      rw [eq2, List.getLast_cons (by simp)] at wellFormed
      constructor
      . exact wellFormed.left
      . exact wellFormed.right.right

/-- When we densify a generator function, we also need to adjust the mapper function (mapping `β` elements to a nodes) accordingly to map `DensifiedResult`s to nodes. This will simply use the first element from the filler list if available and otherwise fall back to using the original mapping function on the `β` value. -/
def densify_mapper (td : TreeDerivation N obs rules) (mapper : β -> NodeWithAddress td) (dr : DensifiedResult β td) : NodeWithAddress td :=
  dr.snd.headD (mapper dr.fst)

/-- After densifying generator and mapper, the next generated value is a child of the previous value. -/
theorem densify_generator.next_child {β : Type u} {td : TreeDerivation N obs rules} {generator : β -> Option β} {mapper : β -> NodeWithAddress td}
    (next_is_succ : ∀ b, ∀ b' ∈ generator b, mapper b ≺ mapper b') :
    ∀ dr : DensifiedResult β td, dr.wellFormed mapper ->
    ∀ next ∈ td.densify_generator generator mapper dr, densify_mapper td mapper next ∈ (densify_mapper td mapper dr).childNodes := by
  intro dr wellFormed next
  fun_cases densify_generator with
  | case1 b =>
    rw [Option.mem_def, Option.map_eq_some_iff]
    intro ⟨b', b'_eq, next_eq⟩
    rw [← next_eq]
    simp only [densify_mapper, List.headD_nil]
    apply NodeWithAddress.nodes_to.head_child
    exact next_is_succ _ _ b'_eq
  | case2 b hd tl =>
    rw [Option.mem_some]; intro eq; rw [← eq]
    simp only [DensifiedResult.wellFormed, List.getLast_eq_getLastD] at wellFormed
    simp only [densify_mapper, List.headD_cons]
    cases tl with
    | nil => exact wellFormed.left
    | cons hd2 tl2 => rw [List.headD_cons]; exact wellFormed.right.left

/-- After densifying generator and mapper, if there is no new value generated, then the current nodes has no children. -/
theorem densify_generator.childTrees_empty_of_next_none {β : Type u}
    {td : TreeDerivation N obs rules} {generator : β -> Option β} {mapper : β -> NodeWithAddress td}
    (maximal : ∀ b, generator b = none -> (mapper b).subderivation.childTrees = []) :
    ∀ dr : DensifiedResult β td, td.densify_generator generator mapper dr = none -> (densify_mapper td mapper dr).subderivation.childTrees = [] := by
  intro dr
  fun_cases densify_generator
  . rw [Option.map_eq_none_iff]
    simp only [densify_mapper]
    exact maximal _
  . simp

/-- Given any `DensifiedResult`, if we iterate the `densify_generator` n times, where n is the length of the list in the second component, then we obtain a densified result where the first component is unchanged but the second component is the empty list. Intuitively, we have then iterated over exactly the list elements in the second component. -/
theorem densify_generator.original_generator_value_after_exhausting_list {β : Type u}
    {td : TreeDerivation N obs rules} {generator : β -> Option β} {mapper : β -> NodeWithAddress td} :
    ∀ dr : DensifiedResult β td, (·.bind (td.densify_generator generator mapper)).repeat_fun dr.snd.length (some dr) = some ⟨dr.fst, []⟩ := by
  intro dr
  induction eq : dr.snd generalizing dr with
  | nil => rw [List.length_nil, Function.repeat_zero]; grind
  | cons hd tl ih =>
    rw [List.length_cons, Function.repeat_add, Function.repeat_once, Option.bind_some]
    have dr_eq : dr = ⟨dr.fst, hd::tl⟩ := by grind
    rw [dr_eq]
    simp only [densify_generator]
    apply ih
    rfl

/-- Every value that can be reached by iterating the original generator can also be reached by iterating the densified version (but the number of iterations can and will most of the time be different). -/
theorem mem_densify_generator_of_mem_generator {β : Type u}
    (td : TreeDerivation N obs rules) (generator : β -> Option β) (mapper : β -> NodeWithAddress td)
    (start : β) : ∀ n, ∃ m, (·.bind (td.densify_generator generator mapper)).repeat_fun m (some ⟨start, []⟩) = ((·.bind generator).repeat_fun n (some start)).map (fun b' => ⟨b', []⟩) := by
  intro n; induction n with
  | zero => exists 0
  | succ n ih =>
    rcases ih with ⟨m, ih⟩
    cases eq_next : (·.bind generator).repeat_fun n.succ (some start) with
    | none =>
      exists m + 1; rw [Option.map_none]
      rw [Function.repeat_add, Function.repeat_once, ← Function.repeat_swap_one, ih]
      rw [Option.bind_eq_none_iff]
      intro val val_eq; rw [Option.map_eq_some_iff] at val_eq; rcases val_eq with ⟨b, b_eq, val_eq⟩
      simp only [densify_generator, ← val_eq]
      rw [Function.repeat_succ, b_eq, Option.bind_some] at eq_next
      rw [eq_next]
      simp
    | some next =>
      cases eq_current : (·.bind generator).repeat_fun n (some start) with
      | none => rw [Function.repeat_succ, eq_current] at eq_next; simp at eq_next
      | some current =>
        exists m + ((mapper current).nodes_to (mapper next)).length.succ
        rw [Option.map_some]
        rw [Function.repeat_add, Function.repeat_swap, Function.repeat_succ, (Option.bind · (td.densify_generator generator mapper)).repeat_swap_one]
        rw [ih, eq_current]
        simp only [Option.map_some, Option.bind_some, densify_generator]
        suffices generator current = next by
          rw [this]; exact densify_generator.original_generator_value_after_exhausting_list ⟨next, (mapper current).nodes_to (mapper next)⟩
        rw [← eq_next, Function.repeat_succ, eq_current]; simp

/-- A version of `densify_generator` that works only on `wellFormed` `DensifiedResult`s. -/
def densify_generator' {β : Type u} (td : TreeDerivation N obs rules) (generator : β -> Option β) (mapper : β -> NodeWithAddress td)
    (next_is_succ : ∀ b, ∀ b' ∈ generator b, mapper b ≺ mapper b')
    (dr : {dr : DensifiedResult β td // dr.wellFormed mapper}) : Option {dr : DensifiedResult β td // dr.wellFormed mapper} :=
  (densify_generator td generator mapper dr.val).attach.map (fun ⟨next, next_mem⟩ =>
    ⟨next, densify_generator.wellFormed next_is_succ dr.val dr.property next next_mem⟩
  )

/-- A version of `densify_mapper` that works only on `wellFormed` `DensifiedResult`s. -/
def densify_mapper' (td : TreeDerivation N obs rules) (mapper : β -> NodeWithAddress td)
    (dr : {dr : DensifiedResult β td // dr.wellFormed mapper}) : NodeWithAddress td :=
  densify_mapper td mapper dr.val

/-- Rpeating `densify_generator'` is not different than repeating `densify_generator` except that we need to isolate the value of the subtype. -/
theorem densify_generator'_eq_densify_generator {β : Type u}
    {td : TreeDerivation N obs rules} {generator : β -> Option β} {mapper : β -> NodeWithAddress td}
    {next_is_succ : ∀ b, ∀ b' ∈ generator b, mapper b ≺ mapper b'}
    {dr : {dr : DensifiedResult β td // dr.wellFormed mapper}} :
    ∀ n, ((·.bind (td.densify_generator' generator mapper next_is_succ)).repeat_fun n (some dr)).map Subtype.val =
      ((·.bind (td.densify_generator generator mapper)).repeat_fun n (some dr.val)) := by
  intro n; induction n with
  | zero => simp [Function.repeat_zero]
  | succ n ih =>
    rw [Function.repeat_succ]
    conv => right; rw [Function.repeat_succ]
    rw [← ih]
    cases (·.bind (td.densify_generator' generator mapper next_is_succ)).repeat_fun n (some dr) <;> simp [densify_generator']

/-- Applying `densify_mapper'` after any number of repetitions of `densify_generator'` is the same as applyign `densify_mapper` after repeating `densify_generator` for the same number of iterations. -/
theorem densify'_eq_densify {β : Type u}
    {td : TreeDerivation N obs rules} {generator : β -> Option β} {mapper : β -> NodeWithAddress td}
    {next_is_succ : ∀ b, ∀ b' ∈ generator b, mapper b ≺ mapper b'}
    {dr : {dr : DensifiedResult β td // dr.wellFormed mapper}} :
    ∀ n, ((·.bind (td.densify_generator' generator mapper next_is_succ)).repeat_fun n (some dr)).map (td.densify_mapper' mapper) =
      ((·.bind (td.densify_generator generator mapper)).repeat_fun n (some dr.val)).map (td.densify_mapper mapper) := by
  intro n
  rw [← densify_generator'_eq_densify_generator (next_is_succ := next_is_succ)]
  cases (·.bind (td.densify_generator' generator mapper next_is_succ)).repeat_fun n (some dr) <;> simp [densify_mapper']

/-- Given a sparse generator function, uses the original `TreeDerivation.generate_subderivation` function together with `densify_generator` and `densify_mapper` to generate a `ChaseDerivation` that corresponds to a branch in the tree. -/
def generate_subderivation_from_sparse {β : Type u} (td : TreeDerivation N obs rules)
    (start : β) (generator : β -> Option β) (mapper : β -> NodeWithAddress td)
    (next_is_succ : ∀ b, ∀ b' ∈ generator b, mapper b ≺ mapper b')
    (maximal : ∀ b, generator b = none -> (mapper b).subderivation.childTrees = []) :
    ChaseDerivation N obs rules :=
  td.generate_subderivation ⟨(start, []), by simp [DensifiedResult.wellFormed]⟩
    (td.densify_generator' generator mapper next_is_succ)
    (td.densify_mapper' mapper)
    (by intro b b'
        simp only [densify_mapper', densify_generator']
        simp only [Option.mem_def, Option.map_eq_some_iff, Option.attach_eq_some_iff]
        intro ⟨inner_b', is_next, b'_eq⟩
        simp only [← b'_eq]
        apply densify_generator.next_child next_is_succ
        . exact b.property
        . rw [Option.mem_def, ← is_next])
    (by intro b
        simp only [densify_mapper', densify_generator']
        rw [Option.map_eq_none_iff, Option.attach_eq_none_iff]
        exact densify_generator.childTrees_empty_of_next_none maximal b.val)

/-- Given a sparse but total generator function, uses the original `TreeDerivation.generate_subderivation` function together with `densify_generator` and `densify_mapper` to generate a `ChaseDerivation` that corresponds to a branch in the tree. Since the generator function is total, the generated derivation is necessarily infinite. -/
public def generate_subderivation_from_sparse_of_total_generator {β : Type u} (td : TreeDerivation N obs rules)
    (start : β) (generator : β -> β) (mapper : β -> NodeWithAddress td)
    (next_is_succ : ∀ b, mapper b ≺ mapper (generator b)) :
    ChaseDerivation N obs rules :=
  td.generate_subderivation_from_sparse start (Option.some ∘ generator) mapper
    (by intro b _ eq; rw [Function.comp_apply, Option.mem_def, Option.some_inj] at eq; rw [← eq]; exact next_is_succ b)
    (by simp)

/-- `generate_subderivation_from_sparse_of_total_generator` produces a tree branch because underneath it uses `TreeDerivation.generate_subderivation`, which already has this property. -/
public theorem generate_subderivation_from_sparse_of_total_generator_mem_branches
    {β : Type u} {td : TreeDerivation N obs rules}
    {start : β} {generator : β -> β} {mapper : β -> NodeWithAddress td}
    {next_is_succ : ∀ b, mapper b ≺ mapper (generator b)}
    (start_eq : mapper start = NodeWithAddress.root td) :
    (td.generate_subderivation_from_sparse_of_total_generator start generator mapper next_is_succ)
      ∈ td.branches := by
  unfold generate_subderivation_from_sparse_of_total_generator generate_subderivation_from_sparse
  apply generate_subderivation_mem_branches
  simp only [densify_mapper', densify_mapper, List.headD_nil]
  exact start_eq

/-- Every node that is part of the original generator also occurs in the derivation produces by the densified version. -/
public theorem mem_generate_subderivation_from_sparse_of_total_generator_of_mem_original_generator
    {β : Type u} {td : TreeDerivation N obs rules}
    {start : β} {generator : β -> β} {mapper : β -> NodeWithAddress td}
    {next_is_succ : ∀ b, mapper b ≺ mapper (generator b)} :
    ∀ b ∈ InfiniteList.iterate start generator, (mapper b).node ∈
      (td.generate_subderivation_from_sparse_of_total_generator start generator mapper next_is_succ) := by
  intro b b_mem
  simp only [InfiniteList.mem_iff, InfiniteList.get_iterate] at b_mem
  rcases b_mem with ⟨n, b_mem⟩
  simp only [generate_subderivation_from_sparse_of_total_generator, generate_subderivation_from_sparse]
  rw [TreeDerivation.mem_generate_subderivation]
  rcases mem_densify_generator_of_mem_generator td (Option.some ∘ generator) mapper start n with ⟨m, b_mem'⟩
  exists m
  rw [densify'_eq_densify, b_mem']
  suffices (·.bind (Option.some ∘ generator)).repeat_fun n (some start) = some b by rw [this]; simp [densify_mapper]
  suffices ∀ n, (·.bind (Option.some ∘ generator)).repeat_fun n (some start) = some (generator.repeat_fun n start) by rw [this, b_mem]
  intro n
  induction n with
  | zero => simp [Function.repeat_zero]
  | succ n ih => rw [Function.repeat_succ, ih, Function.repeat_succ]; simp

end TreeDerivation

