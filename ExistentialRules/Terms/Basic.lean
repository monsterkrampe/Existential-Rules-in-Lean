import BasicLeanDatastructures.List.Basic
import BasicLeanDatastructures.FiniteTree
import BasicLeanDatastructures.Set.Basic
import BasicLeanDatastructures.Set.Finite

structure Signature where
  P : Type u
  V : Type v
  C : Type w
  arity : P -> Nat

structure SkolemFS (sig : Signature) [DecidableEq sig.V] where
  ruleId : Nat
  disjunctIndex : Nat
  var : sig.V
  arity : Nat -- NOTE: this is not enforced anywhere; we set this when skolemizing to remember the frontier size
  deriving DecidableEq

abbrev PreGroundTerm (sig : Signature) [DecidableEq sig.C] [DecidableEq sig.V] := FiniteTree (SkolemFS sig) sig.C

namespace PreGroundTerm

  def arity_ok {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] : FiniteTree (SkolemFS sig) sig.C -> Bool
  | .leaf _ => true
  | .inner func ts =>
    ts.length == func.arity && ts.attach.all (fun ⟨t, _⟩ => arity_ok t)

end PreGroundTerm

abbrev GroundTerm (sig : Signature) [DecidableEq sig.C] [DecidableEq sig.V] := { t : PreGroundTerm sig // PreGroundTerm.arity_ok t }

inductive SkolemTerm (sig : Signature) [DecidableEq sig.C] [DecidableEq sig.V] where
| var (v : sig.V) : SkolemTerm sig
| const (c : sig.C) : SkolemTerm sig
| func (fs : SkolemFS sig) (frontier : List sig.V) (arity_ok : frontier.length = fs.arity) : SkolemTerm sig
deriving DecidableEq

inductive VarOrConst (sig : Signature) [DecidableEq sig.C] [DecidableEq sig.V] where
| var (v : sig.V) : VarOrConst sig
| const (c : sig.C) : VarOrConst sig
deriving DecidableEq

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

namespace GroundTerm

  def const (c : sig.C) : GroundTerm sig := ⟨FiniteTree.leaf c, by simp [PreGroundTerm.arity_ok]⟩
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

  def toConst (t : GroundTerm sig) (isConst : ∃ c, t = GroundTerm.const c) : sig.C :=
    match eq : t.val with
    | .leaf c => c
    | .inner _ _ => by
      apply False.elim
      rcases isConst with ⟨c, isConst⟩
      rw [isConst] at eq
      simp [GroundTerm.const] at eq

  def depth (t : GroundTerm sig) : Nat := t.val.depth
  def constants (t : GroundTerm sig) : (List sig.C) := t.val.leaves
  def functions (t : GroundTerm sig) : (List (SkolemFS sig)) := t.val.innerLabels

  theorem depth_const (c : sig.C) : (GroundTerm.const c).depth = 1 := by
    simp [GroundTerm.const, depth, FiniteTree.depth]

  theorem depth_func (f : SkolemFS sig) (ts : List (GroundTerm sig)) (arity_ok : ts.length = f.arity) :
      (GroundTerm.func f ts arity_ok).depth = 1 + (((ts.map (GroundTerm.depth)).max?).getD 1) := by
    simp only [GroundTerm.func, depth, FiniteTree.depth]
    have : ts.map depth = ts.unattach.map FiniteTree.depth := by rw [List.map_unattach]; rfl
    rw [this]

  theorem constants_const (c : sig.C) : (GroundTerm.const c).constants = [c] := by
    simp [GroundTerm.const, constants, FiniteTree.leaves]

  theorem constants_func (f : SkolemFS sig) (ts : List (GroundTerm sig)) (arity_ok : ts.length = f.arity) :
      (GroundTerm.func f ts arity_ok).constants = ts.flatMap GroundTerm.constants := by
    simp only [GroundTerm.func, constants, FiniteTree.leaves]
    rw [List.flatMap_unattach]
    rfl

  theorem functions_const (c : sig.C) : (GroundTerm.const c).functions = [] := by
    simp [GroundTerm.const, functions, FiniteTree.innerLabels]

  theorem functions_func (f : SkolemFS sig) (ts : List (GroundTerm sig)) (arity_ok : ts.length = f.arity) :
      (GroundTerm.func f ts arity_ok).functions = f :: (ts.flatMap GroundTerm.functions) := by
    simp only [GroundTerm.func, functions, FiniteTree.innerLabels]
    rw [List.cons_eq_cons]
    constructor
    . rfl
    . rw [List.flatMap_unattach]
      rfl

end GroundTerm

namespace SkolemTerm

  def variables : SkolemTerm sig -> List sig.V
  | .var v => List.cons v List.nil
  | .const _ => List.nil
  | .func _ vs _ => vs

end SkolemTerm

namespace VarOrConst

  def isVar : VarOrConst sig -> Bool
  | .var _ => true
  | .const _ => false

  def filterVars : List (VarOrConst sig) -> List sig.V
  | .nil => List.nil
  | .cons voc vocs => match voc with
    | .var v => List.cons v (filterVars vocs)
    | .const _ => filterVars vocs

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

  def filterConsts : List (VarOrConst sig) -> List sig.C
  | .nil => List.nil
  | .cons voc vocs => match voc with
    | .var _ => filterConsts vocs
    | .const c => List.cons c (filterConsts vocs)

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

  def skolemize (ruleId : Nat) (disjunctIndex : Nat) (frontier : List sig.V) (voc : VarOrConst sig) : SkolemTerm sig :=
    match voc with
      | .var v => ite (v ∈ frontier)
        (SkolemTerm.var v)
        (SkolemTerm.func { ruleId, disjunctIndex, var := v, arity := frontier.length } frontier rfl)
      | .const c => SkolemTerm.const c

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

