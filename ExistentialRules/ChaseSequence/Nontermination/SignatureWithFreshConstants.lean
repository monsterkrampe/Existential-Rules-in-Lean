/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.AtomsAndRules.RuleSet
public import ExistentialRules.SubstitutionsAndHomomorphisms

open CustomBasicDatastructures

/-!
# Signature with Fresh Constants

For some constructions, we want to consider fresh constants.
If we know up front which constants we might need,
we can simply extend the signature using a Sum type to know which constants occurred before and which ones are fresh.
In particular, this gives us a trivial way to have a fresh constant for each variable or each Skolem function symbol.

Note that this is a bit different for what we do in the MFA backtracking.
There we introduce fresh constants on the fly during the construction of the backtracking.
Maybe this can be refactored at a later point but it is also not too obvious to see up front,
which constants would be required for the construction.
-/

public section

/-- We can extend a signature with a type for fresh constants by setting the constants to be a Sum type of the original constants and the fresh type. -/
abbrev Signature.withFreshConstants (sig : Signature) (Fresh : Type u) : Signature := {
  Preds := sig.Preds
  V := sig.V
  C := Sum sig.C Fresh
}

instance {sig : Signature} {Fresh : Type u} [Inhabited sig.C] : Inhabited (sig.withFreshConstants Fresh).C where
  default := .inl default

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]
variable {Fresh : Type u} [DecidableEq Fresh]

/-- Change the constant of a `VarOrConst` into the Sum type of `Signature.withFreshConstants`. -/
@[expose]
def VarOrConst.cast_withFreshConstants : TermMapping (VarOrConst sig) (VarOrConst (sig.withFreshConstants Fresh))
| .const c => .const (.inl c)
| .var v => .var v

/-- Calling `VarOrConst.filterConsts` after `cast_withFreshConstants` can be simplified to simply mapping over the original filtered constants. -/
@[simp, grind =]
theorem VarOrConst.filterConsts_after_cast_withFreshConstants {l : List (VarOrConst sig)} :
    VarOrConst.filterConsts (l.map (VarOrConst.cast_withFreshConstants (Fresh := Fresh))) = (VarOrConst.filterConsts l).map .inl := by
  induction l with
  | nil => simp [VarOrConst.filterConsts]
  | cons hd tl ih =>
    simp only [List.map_cons, VarOrConst.filterConsts]
    cases hd <;> (simp [VarOrConst.cast_withFreshConstants]; exact ih)

/-- Calling `VarOrConst.filterVars` after `cast_withFreshConstants` is the same as only calling `VarOrConst.filterVars`. -/
@[simp, grind =]
theorem VarOrConst.filterVars_after_cast_withFreshConstants {l : List (VarOrConst sig)} :
    VarOrConst.filterVars (l.map (VarOrConst.cast_withFreshConstants (Fresh := Fresh))) = VarOrConst.filterVars l := by
  induction l with
  | nil => simp [VarOrConst.filterVars]
  | cons hd tl ih =>
    simp only [List.map_cons, VarOrConst.filterVars]
    cases hd <;> (simp [VarOrConst.cast_withFreshConstants]; exact ih)

variable [DecidableEq sig.P]

/-- Then applying `cast_withFreshConstants` to a conjunction, the variables remain unchanged. -/
theorem FunctionFreeConjunction.vars_cast_withFreshConstants {conj : FunctionFreeConjunction sig} :
    FunctionFreeConjunction.vars ((VarOrConst.cast_withFreshConstants (Fresh := Fresh)).apply_generalized_atom_list conj) = conj.vars := by
  simp only [FunctionFreeConjunction.vars, TermMapping.apply_generalized_atom_list]
  rw [List.flatMap_map]
  congr
  apply funext
  intro a
  simp [FunctionFreeAtom.variables, TermMapping.apply_generalized_atom]

/-- Change the constant of a `Rule` into the Sum type of `Signature.withFreshConstants`. -/
@[expose]
def Rule.cast_withFreshConstants (r : Rule sig) : Rule (sig.withFreshConstants Fresh) where
  body := VarOrConst.cast_withFreshConstants.apply_generalized_atom_list r.body
  head := r.head.map VarOrConst.cast_withFreshConstants.apply_generalized_atom_list

/-- The constants of the cast rule are exactly the constants of the original rule (mapped to the left part of the sum type). -/
theorem Rule.constants_cast_withFreshConstants {r : Rule sig} :
    (r.cast_withFreshConstants (Fresh := Fresh)).constants = r.constants.map .inl := by
  simp only [Rule.constants, cast_withFreshConstants]
  rw [List.map_append, List.map_flatMap, List.flatMap_map]
  suffices ∀ conj : FunctionFreeConjunction sig, FunctionFreeConjunction.consts (VarOrConst.cast_withFreshConstants.apply_generalized_atom_list conj) = conj.consts.map .inl by rw [this]; simp [this]
  intro conj
  simp only [FunctionFreeConjunction.consts, TermMapping.apply_generalized_atom_list]
  rw [List.map_flatMap, List.flatMap_map]
  congr
  apply funext
  intro a
  simp [FunctionFreeAtom.constants, TermMapping.apply_generalized_atom]

/-- The length of the `Rule.head` is not changed by `cast_withFreshConstants`.  -/
@[simp, grind =]
theorem Rule.length_head_cast_withFreshConstants {r : Rule sig} :
    (r.cast_withFreshConstants (Fresh := Fresh)).head.length = r.head.length := by
  simp [cast_withFreshConstants]

/-- When calling `Rule.cast_withFreshConstants`, the variables in each head disjunct remain untouched. -/
theorem Rule.vars_head_disjunct_cast_withFreshConstants {r : Rule sig} :
    ∀ {i : Nat} (lt : i < r.head.length),
    ((r.cast_withFreshConstants (Fresh := Fresh)).head[i]'(by grind)).vars = r.head[i].vars := by
  intro i lt; simp [cast_withFreshConstants, FunctionFreeConjunction.vars_cast_withFreshConstants]

/-- When calling `Rule.cast_withFreshConstants`, the variables in the body remain untouched. -/
@[simp, grind =]
theorem Rule.vars_body_cast_withFreshConstants {r : Rule sig} :
    (r.cast_withFreshConstants (Fresh := Fresh)).body.vars = r.body.vars := by
  simp [cast_withFreshConstants, FunctionFreeConjunction.vars_cast_withFreshConstants]

/-- The frontier of the cast rule remains unchanged. -/
@[simp, grind =]
theorem Rule.frontier_cast_withFreshConstants {r : Rule sig} : (r.cast_withFreshConstants (Fresh := Fresh)).frontier = r.frontier := by
  simp only [Rule.frontier]
  rw [vars_body_cast_withFreshConstants]
  congr
  apply funext; intro v
  simp only [List.any_eq, decide_eq_decide]
  simp only [List.exists_mem_iff_exists_getElem]
  constructor
  . intro ⟨i, lt, h⟩; rw [vars_head_disjunct_cast_withFreshConstants (by grind)] at h; exact ⟨_, _, h⟩
  . intro ⟨i, lt, h⟩; exists i, (by grind); rw [vars_head_disjunct_cast_withFreshConstants (by grind)]; exact h

/-- The cast rule isDatalog if and only if the original rule isDatalog. -/
@[simp, grind =]
theorem Rule.isDatalog_cast_withFreshConstants {r : Rule sig} : (r.cast_withFreshConstants (Fresh := Fresh)).isDatalog ↔ r.isDatalog := by
  simp only [Rule.isDatalog]
  rw [vars_body_cast_withFreshConstants]
  simp only [List.all_eq, decide_eq_true_eq]
  simp only [List.forall_mem_iff_forall_getElem]
  constructor
  . intro h i lt; specialize h i (by grind); rw [vars_head_disjunct_cast_withFreshConstants (by grind)] at h; exact h
  . intro h i lt; specialize h i (by grind); rw [vars_head_disjunct_cast_withFreshConstants (by grind)]; exact h

/-- Change the constant of a `RuleSet` into the Sum type of `Signature.withFreshConstants`. -/
@[expose]
def RuleSet.cast_withFreshConstants (rs : RuleSet sig) : RuleSet (sig.withFreshConstants Fresh) :=
  rs.map Rule.cast_withFreshConstants

/-- The constants of the cast rule set are exactly the constants of the original rule set (mapped to the left part of the sum type). -/
theorem RuleSet.constants_cast_withFreshConstants {rs : RuleSet sig} :
    (rs.cast_withFreshConstants (Fresh := Fresh)).constants = rs.constants.map .inl := by
  apply Set.ext
  intro c; rw [Set.mem_map]
  simp only [cast_withFreshConstants]
  constructor
  . intro ⟨r, r_mem, c_mem⟩
    rw [Set.mem_map] at r_mem; rcases r_mem with ⟨r', r'_mem, r_mem⟩
    rw [← r_mem, Rule.constants_cast_withFreshConstants, List.mem_map] at c_mem
    rcases c_mem with ⟨d, d_mem, c_mem⟩
    exists d; constructor; exists r'; exact c_mem
  . intro ⟨d, ⟨r, r_mem, d_mem⟩, c_eq⟩
    exists r.cast_withFreshConstants; constructor; exact Set.mem_map_of_mem r_mem
    rw [Rule.constants_cast_withFreshConstants, ← c_eq]
    exact List.mem_map_of_mem d_mem

