/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import BasicLeanDatastructures.FiniteTree

public import ExistentialRules.Terms.SkolemTerm

/-!
# Ground Terms

A `GroundTerm` is a constant or a functional term with arbitrary nesting of function symbols (`SkolemFS`).
Aiming to define `GroundTerm`, we need to define a more basic structure first, where we do not demand yet that function symbol arities are respected.
`PreGroundTerm`s need to be able to model Skolem terms, i.e. function terms. We can represent those conveniently using inductively defined `FiniteTree`s.

With `PreGroundTerm`s in place, we merely define `GroundTerm`s to be the `PreGroundTerm`s where `arity_ok` holds.
We then define appropriate constructors and recursion principles on the `GroundTerm` to make it behave almost like an inductive type with a `GroundTerm.const` and `GroundTerm.func` constructor.
-/

public section

/-- The `PreGroundTerm` is simply a `FiniteTree (SkolemFS sig) sig.C`. That is a tree that features Skolem function symbols in its inner nodes and constants in its leaf nodes. -/
abbrev PreGroundTerm (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] := FiniteTree (SkolemFS sig) sig.C

namespace PreGroundTerm

/-- The arity of a functional term is ok if the defined arity of its function symbol matches its number of children and `arity_ok` also holds for each child. For constants, i.e. the leaf nodes, the arity is trivially ok. -/
@[expose]
def arity_ok {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] : FiniteTree (SkolemFS sig) sig.C -> Bool
| .leaf _ => true
| .inner func ts =>
  ts.length == func.arity && ts.attach.all (fun ⟨t, _⟩ => arity_ok t)

end PreGroundTerm

/-- As mentioned above, a `GroundTerm` is simply a `PreGroundTerm` subtype where `arity_ok` holds. -/
abbrev GroundTerm (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] := { t : PreGroundTerm sig // PreGroundTerm.arity_ok t }


namespace GroundTerm

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- A `GroundTerm` can be direclty constructed from a constant. -/
@[expose]
def const (c : sig.C) : GroundTerm sig := ⟨FiniteTree.leaf c, by simp [PreGroundTerm.arity_ok]⟩

/-- The `GroundTerm.const` constructor is injective. -/
@[grind inj]
theorem const.inj : Function.Injective (GroundTerm.const (sig := sig)) := by intro c d; unfold const; simp
@[simp]
theorem const.injEq {c d : sig.C} : GroundTerm.const c = GroundTerm.const d ↔ c = d := by grind

/-- Also, a `GroundTerm` can be constructed from a `SkolemFS` and a list of `GroundTerm`s as long as the length of the list matches the function symbol's arity. -/
@[expose]
def func (func : SkolemFS sig) (ts : List (GroundTerm sig)) (arity_ok : ts.length = func.arity) : GroundTerm sig := ⟨FiniteTree.inner func ts.unattach, by
  unfold PreGroundTerm.arity_ok
  rw [Bool.and_eq_true, beq_iff_eq]
  constructor
  . rw [List.length_unattach]; exact arity_ok
  . rw [List.all_eq_true]
    intro t t_mem
    unfold List.unattach at t_mem
    rw [List.attach_map, List.mem_map] at t_mem
    rcases t_mem with ⟨t, t_mem, t_eq⟩
    rw [← t_eq]
    exact t.val.property
⟩

/-- The `GroundTerm.func` constructor is injective. -/
@[grind ->]
theorem func.inj
  {func1 func2 : SkolemFS sig} {ts1 ts2 : List (GroundTerm sig)} {arity_ok1 : ts1.length = func1.arity} {arity_ok2 : ts2.length = func2.arity} :
  GroundTerm.func func1 ts1 arity_ok1 = GroundTerm.func func2 ts2 arity_ok2 -> func1 = func2 ∧ ts1 = ts2 := by unfold func; simp
@[simp]
theorem func.injEq
  {func1 func2 : SkolemFS sig} {ts1 ts2 : List (GroundTerm sig)} {arity_ok1 : ts1.length = func1.arity} {arity_ok2 : ts2.length = func2.arity} :
  GroundTerm.func func1 ts1 arity_ok1 = GroundTerm.func func2 ts2 arity_ok2 ↔ func1 = func2 ∧ ts1 = ts2 := by grind

/-- `GroundTerm.func` can never be equal to `GroundTerm.const`. -/
theorem func_neq_const {func : SkolemFS sig} {ts : List (GroundTerm sig)} {arity_ok : ts.length = func.arity} {c : sig.C} :
  GroundTerm.func func ts arity_ok ≠ GroundTerm.const c := by simp [GroundTerm.func, const]

/-- A term cannot occur in its own child. -/
theorem eq_while_contained_is_impossible {func : SkolemFS sig} {ts : List (GroundTerm sig)} {arity_ok : ts.length = func.arity} :
    GroundTerm.func func ts arity_ok ∉ ts := by
  intro mem
  apply FiniteTree.tree_eq_while_contained_is_impossible (GroundTerm.func func ts arity_ok).val ts.unattach func
  . rfl
  . rw [List.mem_unattach]; exact ⟨_, mem⟩

/-- We define a cases eliminator for the `GroundTerm` having a case for each constructor. This allows to use the `cases` tactic direcly on `GroundTerm`s. -/
@[elab_as_elim, cases_eliminator]
def cases
    {motive : GroundTerm sig -> Sort u}
    (t : GroundTerm sig)
    (const : (c : sig.C) -> motive (GroundTerm.const c))
    (func : (func : SkolemFS sig) -> (ts : List (GroundTerm sig)) -> (arity_ok : ts.length = func.arity) -> motive (GroundTerm.func func ts arity_ok)) :
    motive t :=
  match eq : t.val with
  | .leaf c =>
    have eq : t = GroundTerm.const c := Subtype.ext eq
    eq ▸ const c
  | .inner f ts =>
    let ts : List (GroundTerm sig) := ts.attach.map (fun t' => ⟨t'.val, by
      have prop := t.property
      unfold PreGroundTerm.arity_ok at prop
      simp only [eq, Bool.and_eq_true, beq_iff_eq] at prop
      have prop := prop.right
      rw [List.all_eq_true] at prop
      apply prop ⟨t', t'.property⟩
      apply List.mem_attach
    ⟩)
    have arity_ok : ts.length = f.arity := by
      have prop := t.property
      unfold PreGroundTerm.arity_ok at prop
      simp only [eq, Bool.and_eq_true, beq_iff_eq] at prop
      unfold ts
      rw [List.length_map, List.length_attach]
      exact prop.left
    have eq : t = GroundTerm.func f ts arity_ok := by
      apply Subtype.ext
      unfold GroundTerm.func
      simp only [eq, ts]
      unfold List.unattach
      rw [List.map_map, List.map_attach_eq_pmap]
      simp
    eq ▸ (func f ts arity_ok)

/-- We define an induction eliminator for the `GroundTerm` having a case for each constructor. This allows to use the `induction` tactic direcly on `GroundTerm`s. -/
@[elab_as_elim, induction_eliminator]
def rec
    {motive : GroundTerm sig -> Sort u}
    (const : (c : sig.C) -> motive (GroundTerm.const c))
    (func : (func : SkolemFS sig) -> (ts : List (GroundTerm sig)) -> (arity_ok : ts.length = func.arity) -> (∀ t, t ∈ ts -> motive t) -> motive (GroundTerm.func func ts arity_ok))
    (t : GroundTerm sig) :
    motive t :=
  match eq_val : t.val with
  | .leaf c =>
    have eq : t = GroundTerm.const c := Subtype.ext eq_val
    eq ▸ const c
  | .inner f ts =>
    let ts : List (GroundTerm sig) := ts.attach.map (fun t' => ⟨t'.val, by
      have prop := t.property
      unfold PreGroundTerm.arity_ok at prop
      simp only [eq_val, Bool.and_eq_true, beq_iff_eq] at prop
      have prop := prop.right
      rw [List.all_eq_true] at prop
      apply prop ⟨t', t'.property⟩
      apply List.mem_attach
    ⟩)
    have arity_ok : ts.length = f.arity := by
      have prop := t.property
      unfold PreGroundTerm.arity_ok at prop
      simp only [eq_val, Bool.and_eq_true, beq_iff_eq] at prop
      unfold ts
      rw [List.length_map, List.length_attach]
      exact prop.left
    have eq : t = GroundTerm.func f ts arity_ok := by
      apply Subtype.ext
      unfold GroundTerm.func
      simp only [eq_val, ts]
      unfold List.unattach
      rw [List.map_map, List.map_attach_eq_pmap]
      simp
    eq ▸ (func f ts arity_ok (by
      intro t' mem
      have : t'.val.depth < t.val.depth := by
        conv => right; unfold FiniteTree.depth
        simp only [eq_val]
        rw [Nat.add_comm]
        apply Nat.lt_add_one_of_le
        apply List.le_max?_getD_of_mem
        apply List.mem_map_of_mem
        rw [List.mem_map] at mem
        rcases mem with ⟨s, s_mem, t_eq⟩
        rw [← t_eq]
        unfold List.attach at s_mem
        unfold List.attachWith at s_mem
        rw [List.mem_pmap] at s_mem
        rcases s_mem with ⟨_, s_mem, s_eq⟩
        rw [← s_eq]
        exact s_mem
      apply GroundTerm.rec const func
    ))
termination_by t.val.depth

/-- A `GroundTerm` that has been constructed from a constant can be converted into this constants again. -/
def toConst (t : GroundTerm sig) (isConst : ∃ c, t = GroundTerm.const c) : sig.C :=
  match eq : t.val with
  | .leaf c => c
  | .inner _ _ => by
    apply False.elim
    rcases isConst with ⟨c, isConst⟩
    rw [isConst] at eq
    simp [GroundTerm.const] at eq

/-- For a `GroundTerm` that has been constructed as a functional term, we can obtain the function symbol. -/
def functionSymbol (t : GroundTerm sig) (isFunc : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok) : SkolemFS sig :=
  match eq : t.val with
  | .leaf _ => by apply False.elim; rcases isFunc with ⟨func, ts, arity_ok, eq2⟩; rw [eq2] at eq; simp [GroundTerm.func] at eq
  | .inner func _ => func

/-- The `depth` of a `GroundTerm` is the depth of the underlying `FiniteTree`, i.e. the deepest nesting of function symbols (+1). -/
@[expose]
def depth (t : GroundTerm sig) : Nat := t.val.depth

/-- The `constants` occurring in a `GroundTerm` are exactly the leaves of the underlying `FiniteTree`. -/
@[expose]
def constants (t : GroundTerm sig) : (List sig.C) := t.val.leaves

/-- The `functions` (i.e. function symbols `SkolemFS`) occurring in a `GroundTerm` are exactly the inner labels of the underlying `FiniteTree`. -/
@[expose]
def functions (t : GroundTerm sig) : (List (SkolemFS sig)) := t.val.innerLabels

/-- The `rules` that occur in the Skolem symbols of a `GroundTerm`. -/
@[expose]
def rules (t : GroundTerm sig) : (List (Rule sig)) := t.functions.map SkolemFS.rule

/-- Applying `toConst` to a `GroundTerm.const` yields exactly the contained constant. -/
@[simp, grind =]
theorem toConst_const {c : sig.C} : (GroundTerm.const c).toConst (by exists c) = c := by rfl

/-- Applying `functionSymbol` to a `GroundTerm.func` yields exactly the contained function symbol. -/
@[simp, grind =]
theorem functionSymbol_func {func : SkolemFS sig} {ts : List (GroundTerm sig)} {arity_ok : ts.length = func.arity} :
  (GroundTerm.func func ts arity_ok).functionSymbol (by exists func, ts, arity_ok) = func := by rfl

/-- Constants have `depth` 1. -/
@[simp, grind =]
theorem depth_const {c : sig.C} : (GroundTerm.const c).depth = 1 := by
  simp [GroundTerm.const, depth, FiniteTree.depth]

/-- The `depth` of a function term is the maximum depth of its children + 1. -/
@[simp, grind =]
theorem depth_func {f : SkolemFS sig} {ts : List (GroundTerm sig)} {arity_ok : ts.length = f.arity} :
    (GroundTerm.func f ts arity_ok).depth = 1 + (((ts.map (GroundTerm.depth)).max?).getD 1) := by
  simp only [GroundTerm.func, depth, FiniteTree.depth]
  have : ts.map depth = ts.unattach.map FiniteTree.depth := by rw [List.map_unattach]; rfl
  rw [this]

/-- Every term has a depth greater zero since constants already have depth 1. -/
theorem depth_gt_zero {t : GroundTerm sig} : 0 < t.depth := by cases t <;> grind

/-- The `constants` of a constant are the singleton list with the constant itself. -/
@[simp, grind =]
theorem constants_const {c : sig.C} : (GroundTerm.const c).constants = [c] := by
  simp [GroundTerm.const, constants, FiniteTree.leaves]

/-- The `constants` of a function term are the constants of its children. -/
@[simp, grind =]
theorem constants_func {f : SkolemFS sig} {ts : List (GroundTerm sig)} {arity_ok : ts.length = f.arity} :
    (GroundTerm.func f ts arity_ok).constants = ts.flatMap GroundTerm.constants := by
  simp only [GroundTerm.func, constants, FiniteTree.leaves]
  rw [List.flatMap_unattach]
  rfl

/-- A constant has no `functions`. -/
@[simp, grind =]
theorem functions_const {c : sig.C} : (GroundTerm.const c).functions = [] := by
  simp [GroundTerm.const, functions, FiniteTree.innerLabels]

/-- The `functions` of a function term consist of the function symbol of the current term and the function symbols of all its children. -/
@[simp, grind =]
theorem functions_func {f : SkolemFS sig} {ts : List (GroundTerm sig)} {arity_ok : ts.length = f.arity} :
    (GroundTerm.func f ts arity_ok).functions = f :: (ts.flatMap GroundTerm.functions) := by
  simp only [GroundTerm.func, functions, FiniteTree.innerLabels]
  rw [List.cons_eq_cons]
  constructor
  . rfl
  . rw [List.flatMap_unattach]; rfl

/-- A constant has no `rules`. -/
@[simp, grind =]
theorem rules_const {c : sig.C} : (GroundTerm.const c).rules = [] := by
  simp [rules]

/-- The `rules` of a function term consist of the rules of the current term and the rules of all its children. -/
@[simp, grind =]
theorem rules_func {f : SkolemFS sig} {ts : List (GroundTerm sig)} {arity_ok : ts.length = f.arity} :
    (GroundTerm.func f ts arity_ok).rules = f.rule :: (ts.flatMap GroundTerm.rules) := by
  unfold rules; simp [List.map_flatMap]

end GroundTerm

