/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import BasicLeanDatastructures.List.EraseDupsKeepRight
public import ExistentialRules.ChaseSequence.Termination.RenameConstantsApart.GroundTerm

/-!
# Renaming Constants apart in a GroundSubstitution and PreTrigger

We lift the `PreGroundTerm.rename_constants_apart` functionality to `GroundSubstitution` and `PreTrigger`.
This pretty much happens in the obvious way and apart from being technical, this is not interesting.
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace GroundSubstitution

@[expose]
def rename_constants_apart_for_vars [GetFreshInhabitant sig.C]
  (subs : GroundSubstitution sig) (forbidden_constants : List sig.C) : List sig.V -> GroundSubstitution sig
| .nil => subs
| .cons hd tl =>
  let renamed_term_for_hd := (subs hd).rename_constants_apart forbidden_constants
  let new_forbidden := forbidden_constants ++ renamed_term_for_hd.constants
  fun v => if v = hd then renamed_term_for_hd else
    subs.rename_constants_apart_for_vars new_forbidden tl v

theorem rename_constants_apart_for_vars_constants_fresh
    [GetFreshInhabitant sig.C]
    (subs : GroundSubstitution sig)
    (forbidden_constants : List sig.C)
    (vars : List sig.V) :
    ∀ v ∈ vars, ∀ c ∈ (subs.rename_constants_apart_for_vars forbidden_constants vars v).constants, c ∉ forbidden_constants := by
  induction vars generalizing forbidden_constants with
  | nil => intros; contradiction
  | cons hd tl ih =>
    intro v v_mem c c_mem
    cases Decidable.em (v = hd) with
    | inl v_eq_hd =>
      simp only [rename_constants_apart_for_vars, v_eq_hd, ↓reduceIte] at c_mem
      apply GroundTerm.rename_constants_apart_constants_fresh
      exact c_mem
    | inr v_neq_hd =>
      have v_mem : v ∈ tl := by cases v_mem; contradiction; assumption
      simp only [rename_constants_apart_for_vars, v_neq_hd, ↓reduceIte] at c_mem
      let new_forbidden := forbidden_constants ++ ((subs hd).rename_constants_apart forbidden_constants).constants
      specialize ih new_forbidden v v_mem c c_mem
      intro contra
      apply ih
      simp [new_forbidden, contra]

end GroundSubstitution

namespace PreTrigger

@[expose]
def rename_constants_apart [GetFreshInhabitant sig.C] (trg : PreTrigger sig) (forbidden_constants : List sig.C) : PreTrigger sig :=
  ⟨trg.rule, trg.subs.rename_constants_apart_for_vars forbidden_constants trg.rule.body.vars.eraseDupsKeepRight⟩

theorem rename_constants_apart_constants_fresh
    [GetFreshInhabitant sig.C]
    (trg : PreTrigger sig)
    (forbidden_constants : List sig.C) :
    ∀ c ∈ (trg.rule.body.vars.eraseDupsKeepRight.map (trg.rename_constants_apart forbidden_constants).subs).flatMap GroundTerm.constants,
    c ∉ forbidden_constants := by
  intro c c_mem
  rw [List.mem_flatMap] at c_mem
  rcases c_mem with ⟨t, t_mem, c_mem⟩
  rw [List.mem_map] at t_mem
  rcases t_mem with ⟨v, v_mem, t_eq⟩
  apply trg.subs.rename_constants_apart_for_vars_constants_fresh forbidden_constants trg.rule.body.vars.eraseDupsKeepRight v v_mem
  rw [← t_eq] at c_mem
  exact c_mem

end PreTrigger

