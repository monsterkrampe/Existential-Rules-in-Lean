import BasicLeanDatastructures.List.Basic
import BasicLeanDatastructures.FiniteTree
import BasicLeanDatastructures.Set.Basic
import BasicLeanDatastructures.Set.Finite

/-!
# Terms

In this file, we define various kinds of terms that form some of the most basic building blocks of
other structures like atoms and rules.
-/

/-- First of all, almost all of our definitions consider a fixed but arbitrary `Signature` of predicate symbols `P`, variables `V`, and constants `C`. Also every predicate has a fixed `arity`. Note that `P`, `V`, and `C` can be arbitrary types so there are no requirements in terms of countability or finiteness. However, intuitively you can consider them to be countably infinite sets. This would allow to pick fresh elements for example. In places where we need this property, we express this through the `GetFreshInhabitant` type class. -/
structure Signature where
  P : Type u
  V : Type v
  C : Type w
  arity : P -> Nat

section SkolemTerms

/-!
## Skolem Terms

If you are familiar with existential rules, you may have expected (labelled) nulls to be part of the `Signature`.
These nulls would act as placeholders that are introduced during the chase to find fresh representatives for existentially quantified variables.
However, implementing this freshness is not really nice to model since it would require is to keep global state around to know
which nulls have already been used. Instead, we act as if the existentially quantified variables where Skolemized. By that, freshly
introduced terms simply become Skolem terms and we can show that these are indeed fresh by design. Some works on existential rules take this view,
first and foremost of course the ones considering the Skolem chase.
-/

/--  As a building block for Skolem terms, we introduce `SkolemFS` as a Skolem Function Symbol here. This structure captures the rule, disjunct, and (existential) variable for that the Skolem function was introduced. The arity corresponds to the size of the frontier of the rule, i.e. the universal variables that occur in both body and head. -/
structure SkolemFS (sig : Signature) [DecidableEq sig.V] where
  ruleId : Nat
  disjunctIndex : Nat
  var : sig.V
  arity : Nat
  deriving DecidableEq

/-- With `SkolemTerm` we mean the Skolemized version of an existential variable. That is, a `SkolemTerm` only consists of a function symbol (`SkolemFS`) and a list of universal variables. Beyond that, we allow this inductive structure also to be a plain variable or constant. Thereby, the `SkolemTerm` can represent any term occurring in a Skolemized rule. -/
inductive SkolemTerm (sig : Signature) [DecidableEq sig.C] [DecidableEq sig.V] where
| var (v : sig.V) : SkolemTerm sig
| const (c : sig.C) : SkolemTerm sig
| func (fs : SkolemFS sig) (frontier : List sig.V) (arity_ok : frontier.length = fs.arity) : SkolemTerm sig
deriving DecidableEq

namespace SkolemTerm

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

/-- We may obtain all variables from a `SkolemTerm` term as the list of all variables occurring in the functional term or, if the term is a plain variable, simply as the singleton list with this one variable. -/
def variables : SkolemTerm sig -> List sig.V
| .var v => List.cons v List.nil
| .const _ => List.nil
| .func _ vs _ => vs

end SkolemTerm

end SkolemTerms

section VarOrConst

/-!
## VarOrConst

We introduce `VarOrConst` as yet another inductive type representing a term.
This is a function free `SkolemTerm`, i.e. either a variable or a constant (thus the name).
Having this is a separate type is more convenient for us than restricting the `SkolemTerm` further.
`VarOrConst` is used to define `FunctionFreeAtom` later and is thus also the basic building block of (non-Skolemized) `Rule`s.
-/

/-- As the name suggests, a `VarOrConst` is either a variable or a constant. -/
inductive VarOrConst (sig : Signature) [DecidableEq sig.C] [DecidableEq sig.V] where
| var (v : sig.V) : VarOrConst sig
| const (c : sig.C) : VarOrConst sig
deriving DecidableEq

namespace VarOrConst

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

/-- A `VarOrConst` is a variable if it was built using the `var` constructor. -/
def isVar : VarOrConst sig -> Bool
| .var _ => true
| .const _ => false

/-- Given a list of `VarOrConst`, we can filter out all the variables. Note that we do not use `List.filter` here since we need to change the list type on the way. -/
def filterVars : List (VarOrConst sig) -> List sig.V
| .nil => List.nil
| .cons voc vocs => match voc with
  | .var v => List.cons v (filterVars vocs)
  | .const _ => filterVars vocs

/-- Analogous to `filterVars`, we can also filter for constants. -/
def filterConsts : List (VarOrConst sig) -> List sig.C
| .nil => List.nil
| .cons voc vocs => match voc with
  | .var _ => filterConsts vocs
  | .const c => List.cons c (filterConsts vocs)

/-- In the context of a rule and a disjunct (in that rule), we can turn a `VarOrConst` into a `SkolemTerm` using the frontier of the rule. This function is used for skolemizing existential variables in rules. -/
def skolemize (ruleId : Nat) (disjunctIndex : Nat) (frontier : List sig.V) (voc : VarOrConst sig) : SkolemTerm sig :=
  match voc with
    | .var v => ite (v ∈ frontier)
      (SkolemTerm.var v)
      (SkolemTerm.func { ruleId, disjunctIndex, var := v, arity := frontier.length } frontier rfl)
    | .const c => SkolemTerm.const c

/-- Each member of `filterVars` is in the original list (when applyign the `var` constructor again.) -/
theorem filterVars_occur_in_original_list (l : List (VarOrConst sig)) (v : sig.V) : v ∈ filterVars l -> VarOrConst.var v ∈ l := by
  induction l with
  | nil => intros; contradiction
  | cons head tail ih =>
    intro h
    unfold filterVars at h
    split at h
    . simp at h
      simp
      cases h with
      | inl h => apply Or.inl; exact h
      | inr h => apply Or.inr; apply ih; exact h
    . simp
      apply ih
      exact h

/-- If a variable is in a list of `VarOrConst`, then it occurs in `filterVars`. -/
theorem mem_filterVars_of_var (l : List (VarOrConst sig)) (v : sig.V) : VarOrConst.var v ∈ l -> v ∈ filterVars l := by
  induction l with
  | nil => intros; contradiction
  | cons head tail ih =>
    intro h
    simp at h
    unfold filterVars
    cases h with
    | inl h => rw [← h]; simp
    | inr h => split; rw [List.mem_cons]; apply Or.inr; apply ih; exact h; apply ih; exact h

/-- Each member of `filterConsts` is in the original list (when applyign the `const` constructor again.) -/
theorem filterConsts_occur_in_original_list (l : List (VarOrConst sig)) (c : sig.C) : c ∈ filterConsts l -> VarOrConst.const c ∈ l := by
  induction l with
  | nil => intros; contradiction
  | cons head tail ih =>
    intro h
    unfold filterConsts at h
    split at h
    . simp
      apply ih
      exact h
    . simp at h
      simp
      cases h with
      | inl h => apply Or.inl; exact h
      | inr h => apply Or.inr; apply ih; exact h

/-- If a constant is in a list of `VarOrConst`, then it occurs in `filterConsts`. -/
theorem mem_filterConsts_of_const (l : List (VarOrConst sig)) (c : sig.C) : VarOrConst.const c ∈ l -> c ∈ filterConsts l := by
  induction l with
  | nil => intros; contradiction
  | cons head tail ih =>
    intro h
    simp at h
    unfold filterConsts
    cases h with
    | inl h => rw [← h]; simp
    | inr h => split; apply ih; exact h; rw [List.mem_cons]; apply Or.inr; apply ih; exact h

/-- The `skolemize` function is injective. That is, if the produced `SkolemTerm`s are the same, then bey need to result from the same variable. This is important to ensure that introduced Skolem terms are indeed fresh (and unique) in the chase. -/
theorem skolemize_injective (ruleId : Nat) (i : Nat) (frontier : List sig.V) (s t : VarOrConst sig) :
    s.skolemize ruleId i frontier = t.skolemize ruleId i frontier -> s = t := by
  cases s with
  | var vs => cases t with
    | var vt =>
      simp [skolemize]
      split
      . split
        . simp
        . intros; contradiction
      . split
        . intros; contradiction
        . simp
    | const _ =>
      simp only [skolemize]
      split <;> intros <;> contradiction
  | const cs => cases t with
    | var vt =>
      simp only [skolemize]
      split <;> intros <;> contradiction
    | const _ => simp [skolemize]

end VarOrConst

end VarOrConst

section GroundTerms

/-!
## Ground Terms

A `GroundTerm` is a constant or a functional term with arbitrary nesting of function symbols (`SkolemFS`).
Aiming to define `GroundTerm`, we need to define a more basic structure first, where we do not demand yet that function symbol arities are respected.
`PreGroundTerm`s need to be able to model Skolem terms, i.e. function terms. We can represent those conveniently using inductively defined `FiniteTree`s.

With `PreGroundTerm`s in place, we merely define `GroundTerm`s to be the `PreGroundTerm`s where `arity_ok` holds.
We then define appropriate constructors and recursion principles on the `GroundTerm` to make it behave almost like an inductive type with a `const` and `func` constructor.
-/

/-- The `PreGroundTerm` is simply a `FiniteTree (SkolemFS sig) sig.C`. That is a tree that features Skolem function symbols in its inner nodes and constants in its leaf nodes. -/
abbrev PreGroundTerm (sig : Signature) [DecidableEq sig.C] [DecidableEq sig.V] := FiniteTree (SkolemFS sig) sig.C

namespace PreGroundTerm

/-- The arity of a functional term is ok if the defined arity of its function symbol matches its number of children and `arity_ok` also holds for each child. For constants, i.e. the leaf nodes, the arity is trivially ok. -/
def arity_ok {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] : FiniteTree (SkolemFS sig) sig.C -> Bool
| .leaf _ => true
| .inner func ts =>
  ts.length == func.arity && ts.attach.all (fun ⟨t, _⟩ => arity_ok t)

end PreGroundTerm

/-- As mentioned above, a `GroundTerm` is simply a `PreGroundTerm` subtype where `arity_ok` holds. -/
abbrev GroundTerm (sig : Signature) [DecidableEq sig.C] [DecidableEq sig.V] := { t : PreGroundTerm sig // PreGroundTerm.arity_ok t }

namespace GroundTerm

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

/-- A `GroundTerm` can be direclty constructed from a constant. -/
def const (c : sig.C) : GroundTerm sig := ⟨FiniteTree.leaf c, by simp [PreGroundTerm.arity_ok]⟩
/-- Also, a `GroundTerm` can be constructed from a `SkolemFS` and a list of `GroundTerm`s as long as the length of the list matches the function symbol's arity. -/
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
  | .inner f ts => by
    let ts : List (GroundTerm sig) := ts.attach.map (fun ⟨t', mem⟩ => ⟨t', by
      have prop := t.property
      unfold PreGroundTerm.arity_ok at prop
      simp only [eq, Bool.and_eq_true, beq_iff_eq] at prop
      have prop := prop.right
      rw [List.all_eq_true] at prop
      apply prop ⟨t', mem⟩
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
      simp [eq, ts]
      unfold List.unattach
      rw [List.map_map, List.map_attach_eq_pmap]
      simp
    exact eq ▸ (func f ts arity_ok)

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
  | .inner f ts => by
    let ts : List (GroundTerm sig) := ts.attach.map (fun ⟨t', mem⟩ => ⟨t', by
      have prop := t.property
      unfold PreGroundTerm.arity_ok at prop
      simp only [eq_val, Bool.and_eq_true, beq_iff_eq] at prop
      have prop := prop.right
      rw [List.all_eq_true] at prop
      apply prop ⟨t', mem⟩
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
      simp [eq_val, ts]
      unfold List.unattach
      rw [List.map_map, List.map_attach_eq_pmap]
      simp
    exact eq ▸ (func f ts arity_ok (by
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
        simp at t_eq
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

/-- A `GroundTerm` that has been constructed from a constants can be converted into this constants again. -/
def toConst (t : GroundTerm sig) (isConst : ∃ c, t = GroundTerm.const c) : sig.C :=
  match eq : t.val with
  | .leaf c => c
  | .inner _ _ => by
    apply False.elim
    rcases isConst with ⟨c, isConst⟩
    rw [isConst] at eq
    simp [GroundTerm.const] at eq

/-- The `depth` of a `GroundTerm` is the depth of the underlying `FiniteTree`, i.e. the deepest nesting of function symbols (+1). -/
def depth (t : GroundTerm sig) : Nat := t.val.depth

/-- The `constants` occurring in a `GroundTerm` are exactly the leaves of the underlying `FiniteTree`. -/
def constants (t : GroundTerm sig) : (List sig.C) := t.val.leaves

/-- The `functions` (i.e. function symbols `SkolemFS`) occurring in a `GroundTerm` are exactly the inner labels of the underlying `FiniteTree`. -/
def functions (t : GroundTerm sig) : (List (SkolemFS sig)) := t.val.innerLabels

/-- Constants have `depth` 1. -/
theorem depth_const (c : sig.C) : (GroundTerm.const c).depth = 1 := by
  simp [GroundTerm.const, depth, FiniteTree.depth]

/-- The `depth` of a function term is the maximum depth of its children + 1. -/
theorem depth_func (f : SkolemFS sig) (ts : List (GroundTerm sig)) (arity_ok : ts.length = f.arity) :
    (GroundTerm.func f ts arity_ok).depth = 1 + (((ts.map (GroundTerm.depth)).max?).getD 1) := by
  simp only [GroundTerm.func, depth, FiniteTree.depth]
  have : ts.map depth = ts.unattach.map FiniteTree.depth := by rw [List.map_unattach]; rfl
  rw [this]

/-- The `constants` of a constant are the singleton list with the constant itself. -/
theorem constants_const (c : sig.C) : (GroundTerm.const c).constants = [c] := by
  simp [GroundTerm.const, constants, FiniteTree.leaves]

/-- The `constants` of a function term are the constants of its children. -/
theorem constants_func (f : SkolemFS sig) (ts : List (GroundTerm sig)) (arity_ok : ts.length = f.arity) :
    (GroundTerm.func f ts arity_ok).constants = ts.flatMap GroundTerm.constants := by
  simp only [GroundTerm.func, constants, FiniteTree.leaves]
  rw [List.flatMap_unattach]
  rfl

/-- A constant has no `functions`. -/
theorem functions_const (c : sig.C) : (GroundTerm.const c).functions = [] := by
  simp [GroundTerm.const, functions, FiniteTree.innerLabels]

/-- The `functions` of a function term consist of the function symbol of the current term and the function symbols of all its children. -/
theorem functions_func (f : SkolemFS sig) (ts : List (GroundTerm sig)) (arity_ok : ts.length = f.arity) :
    (GroundTerm.func f ts arity_ok).functions = f :: (ts.flatMap GroundTerm.functions) := by
  simp only [GroundTerm.func, functions, FiniteTree.innerLabels]
  rw [List.cons_eq_cons]
  constructor
  . rfl
  . rw [List.flatMap_unattach]
    rfl

end GroundTerm

end GroundTerms

