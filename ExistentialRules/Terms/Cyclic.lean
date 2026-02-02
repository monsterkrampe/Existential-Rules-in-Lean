import ExistentialRules.Terms.Basic

/-!
# Cyclic Terms

In this file, we define when a `PreGroundTerm` is `cyclic`.
This is exactly the case, when a function symbol contains twice in a nested fashion.
For example $h(d, f(g(f(c))))$ is cyclic but $h(f(d), f(c))$ is not.
Cyclic terms are mainly used to define MFA later.

The main result in this file then is `cyclic_of_depth_too_big`. That is, if a term exceeds a certain depth, then it is necessarily cyclic.
This of course requires that only finitely many different function symbols are usable.
-/

namespace PreGroundTerm

variable {sig : Signature} [DecidableEq sig.V]

/-- The `function_paths` of a `PreGroundTerm` are essentially all the (maximal) branches in the underlying finite tree without the terminal constant symbol. These can be used to detect cyclic terms by simply looking for repetitions along a branch. -/
def function_paths : FiniteTree (SkolemFS sig) sig.C -> List (List (SkolemFS sig))
| .leaf _ => [[]]
| .inner f ts =>
  if ts = [] then [[f]] else
  (ts.flatMap function_paths).map (fun path => f :: path)

/-- A `PreGroundTerm` contains a function symbol if this symbols occurs as one of the inner labels. -/
def contains_func (func : SkolemFS sig) : FiniteTree (SkolemFS sig) sig.C -> Bool
| .leaf _ => false
| .inner func' ts => func == func' || ts.attach.any (fun ⟨t, _⟩ => contains_func func t)

/-- A `PreGroundTerm` is `cyclic` if one of its children `contains_func` the function symbol of the term or if one of its children is already `cyclic`. Constants are never cyclic. -/
def cyclic : FiniteTree (SkolemFS sig) sig.C -> Bool
| .leaf _ => false
| .inner func ts => ts.any (contains_func func) || ts.attach.any (fun ⟨t, _⟩ => PreGroundTerm.cyclic t)

/-- All elements of the `function_paths` paths are inner labels of the finite tree. -/
theorem function_path_elements_are_inner_labels (t : FiniteTree (SkolemFS sig) sig.C) : ∀ (path : List (SkolemFS sig)), path ∈ PreGroundTerm.function_paths t -> ∀f, f ∈ path -> f ∈ t.innerLabels := by
  intro path path_mem f f_mem
  induction t generalizing path with
  | leaf c =>
    simp only [function_paths, List.mem_singleton] at path_mem
    rw [path_mem] at f_mem
    simp at f_mem
  | inner func ts ih =>
    unfold function_paths at path_mem
    cases ts with
    | nil =>
      simp only [↓reduceIte] at path_mem
      rw [List.mem_singleton] at path_mem
      rw [path_mem] at f_mem
      rw [List.mem_singleton] at f_mem
      unfold FiniteTree.innerLabels
      rw [List.mem_cons]
      apply Or.inl
      exact f_mem
    | cons hd tl =>
      simp only [List.cons_ne_nil, ↓reduceIte] at path_mem
      rw [List.map_flatMap, List.mem_flatMap] at path_mem
      rcases path_mem with ⟨t, t_mem, path_mem⟩
      rw [List.mem_map] at path_mem
      rcases path_mem with ⟨path', mem, eq⟩
      rw [← eq] at f_mem
      rw [List.mem_cons] at f_mem
      unfold FiniteTree.innerLabels
      rw [List.mem_cons]
      cases f_mem with
      | inl f_mem => apply Or.inl; exact f_mem
      | inr f_mem =>
        apply Or.inr
        rw [List.mem_flatMap]
        exists t
        constructor
        . exact t_mem
        . exact ih t t_mem path' mem f_mem

/-- There is a path in `function_paths` that matches the depth of the term (-1). That means that this path is one of maximal possible length. -/
theorem function_path_of_depth_exists (t : FiniteTree (SkolemFS sig) sig.C) : ∃ (path : List (SkolemFS sig)), path ∈ PreGroundTerm.function_paths t ∧ path.length = t.depth - 1 := by
  induction t with
  | leaf c => exists []; simp [FiniteTree.depth, function_paths]
  | inner f ts ih =>
    cases ts with
    | nil =>
      exists [f]
      constructor
      . unfold function_paths
        simp
      . unfold FiniteTree.depth
        simp
    | cons hd tl =>
      have : ∃ t, t ∈ (hd::tl) ∧ t.depth = (FiniteTree.inner f (hd :: tl)).depth - 1 := by
        simp only [FiniteTree.depth]
        rw [Nat.add_comm, Nat.add_one_sub_one]
        rw [← List.mem_map]
        apply List.max?_mem
        simp
      rcases this with ⟨t, t_mem, t_depth⟩
      rcases ih t t_mem with ⟨path, mem, len⟩
      exists (f :: path)
      constructor
      . unfold function_paths
        simp only [List.cons_ne_nil, ↓reduceIte]
        rw [List.mem_map]
        exists path
        constructor
        . rw [List.mem_flatMap]
          exists t
        . rfl
      . rw [← t_depth, List.length_cons]
        rw [len]
        rw [Nat.sub_one_add_one]
        intro contra
        cases t with
        | leaf _ => simp [FiniteTree.depth] at contra
        | inner _ _ => simp [FiniteTree.depth] at contra

/-- For each element in a path from `function_paths`, `contains_func` is true. -/
theorem function_path_elements_are_in_contains_func (t : FiniteTree (SkolemFS sig) sig.C) : ∀ (path : List (SkolemFS sig)), path ∈ PreGroundTerm.function_paths t -> ∀ f, f ∈ path -> PreGroundTerm.contains_func f t := by
  intro path path_mem f f_mem
  induction t generalizing path with
  | leaf c =>
    simp only [function_paths, List.mem_singleton] at path_mem
    rw [path_mem] at f_mem
    simp at f_mem
  | inner func ts ih =>
    unfold contains_func
    rw [Bool.or_eq_true]
    unfold function_paths at path_mem
    cases ts with
    | nil =>
      simp only [↓reduceIte] at path_mem
      rw [List.mem_singleton] at path_mem
      rw [path_mem] at f_mem
      rw [List.mem_singleton] at f_mem
      apply Or.inl
      rw [f_mem]
      simp
    | cons hd tl =>
      simp only [List.cons_ne_nil, ↓reduceIte] at path_mem
      rw [List.map_flatMap, List.mem_flatMap] at path_mem
      rcases path_mem with ⟨t, t_mem, path_mem⟩
      rw [List.mem_map] at path_mem
      rcases path_mem with ⟨path', mem, eq⟩
      rw [← eq] at f_mem
      rw [List.mem_cons] at f_mem
      cases f_mem with
      | inl f_mem => apply Or.inl; rw [f_mem]; simp
      | inr f_mem =>
        apply Or.inr
        rw [List.any_eq_true]
        exists ⟨t, t_mem⟩
        constructor
        . apply List.mem_attach
        . exact ih t t_mem path' mem f_mem

/-- A term is `cyclic` if a path in `function_paths` has a duplicate. -/
theorem cyclic_of_path_with_dup (t : FiniteTree (SkolemFS sig) sig.C) (path : List (SkolemFS sig)) (path_mem : path ∈ PreGroundTerm.function_paths t) (dup : ¬ path.Nodup) : PreGroundTerm.cyclic t := by
  induction t generalizing path with
  | leaf c =>
    unfold PreGroundTerm.function_paths at path_mem
    rw [List.mem_singleton] at path_mem
    rw [path_mem] at dup
    simp at dup
  | inner f ts ih =>
    unfold PreGroundTerm.function_paths at path_mem
    cases ts with
    | nil =>
      simp only [↓reduceIte] at path_mem
      rw [List.mem_singleton] at path_mem
      rw [path_mem] at dup
      simp at dup
    | cons hd tl =>
      simp only [List.cons_ne_nil, ↓reduceIte] at path_mem
      rw [List.map_flatMap, List.mem_flatMap] at path_mem
      rcases path_mem with ⟨t, t_mem, path_mem⟩
      rw [List.mem_map] at path_mem
      rcases path_mem with ⟨path', mem, eq⟩
      unfold PreGroundTerm.cyclic
      rw [Bool.or_eq_true]
      cases Decidable.em (f ∈ path') with
      | inl f_mem =>
        apply Or.inl
        rw [List.any_eq_true]
        exists t
        constructor
        . exact t_mem
        . exact function_path_elements_are_in_contains_func t path' mem f f_mem
      | inr f_mem =>
        apply Or.inr
        rw [← eq] at dup
        rw [List.nodup_cons] at dup
        simp only [not_and] at dup
        rw [List.any_eq_true]
        exists ⟨t, t_mem⟩
        constructor
        . apply List.mem_attach
        . exact ih t t_mem path' mem (dup f_mem)


variable [DecidableEq sig.C]

/-- Consider a (deduplicated) list of possible function symbols and a term. If the depth of the term is at least the number of function symbols + 2, then the term must be cyclic.  -/
theorem cyclic_of_depth_too_big (t : PreGroundTerm sig) (funcs : List (SkolemFS sig)) (nodup : funcs.Nodup) (funcs_in_t_from_funcs : ∀ func, func ∈ t.innerLabels -> func ∈ funcs) : funcs.length + 2 ≤ t.depth -> PreGroundTerm.cyclic t := by
  intro le_depth
  have := PreGroundTerm.function_path_of_depth_exists t
  rcases this with ⟨path, path_mem, path_len⟩

  have path_length_gt : funcs.length < path.length := by
    rw [path_len]
    apply Nat.lt_of_succ_le
    apply Nat.le_of_succ_le_succ
    rw [Nat.succ_eq_add_one]
    rw [Nat.succ_eq_add_one]
    rw [Nat.sub_one_add_one]
    . exact le_depth
    . unfold FiniteTree.depth
      cases t <;> simp

  have dup_in_path : ¬ path.Nodup := by
    apply List.contains_dup_of_exceeding_nodup_list_with_same_elements funcs path nodup path_length_gt
    intro f f_mem
    apply funcs_in_t_from_funcs
    exact PreGroundTerm.function_path_elements_are_inner_labels t path path_mem f f_mem

  exact PreGroundTerm.cyclic_of_path_with_dup t path path_mem dup_in_path

end PreGroundTerm

