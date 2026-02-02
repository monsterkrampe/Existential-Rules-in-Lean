import BasicLeanDatastructures.List.Basic

import ExistentialRules.AtomsAndFacts.Basic

/-!
# Substitutions and other mappings on Terms

In this file, we define mainly `GroundSubstitution` and `GroundTermMapping`. The latter is used to define homomorphisms on `FactSet`s.
Both kinds of mapping are based on a (very general) `TermMapping`.
-/

section TermMapping

/-!
## TermMapping

The `TermMapping` is really just a function between two types but we
define a bit of machinery on it that captures how remapping terms in such a general way behaves in the context of a `GeneralizedAtom` or lists or sets thereof.
-/

/-- A `TermMapping` is nothing more than a function from one term type to another. -/
abbrev TermMapping (S : Type u) (T : Type v) := S -> T

namespace TermMapping

variable {sig : Signature} [DecidableEq sig.P]

/-- A `TermMapping` is applied to a `GeneralizedAtom` by simply applying it to each term. -/
def apply_generalized_atom (h : TermMapping S T) (a : GeneralizedAtom sig S) : GeneralizedAtom sig T := {
  predicate := a.predicate
  terms := a.terms.map h
  arity_ok := by rw [List.length_map, a.arity_ok]
}

/-- A `TermMapping` is applied to a list of `GeneralizedAtom`s by applying it to each atom. -/
def apply_generalized_atom_list (h : TermMapping S T) (l : List (GeneralizedAtom sig S)) : List (GeneralizedAtom sig T) :=
  l.map h.apply_generalized_atom

/-- A `TermMapping` is applied to a set of `GeneralizedAtom`s by applying it to each atom. -/
def apply_generalized_atom_set (h : TermMapping S T) (s : Set (GeneralizedAtom sig S)) : Set (GeneralizedAtom sig T) :=
  s.map h.apply_generalized_atom

/-- Applying a `TermMapping` to a `GeneralizedAtom` does not change the number of terms.-/
theorem length_terms_apply_generalized_atom (h : TermMapping S T) (a : GeneralizedAtom sig S) :
    (h.apply_generalized_atom a).terms.length = a.terms.length := by
  simp [apply_generalized_atom]

/-- We can split the application of a composed `TermMapping` on an atom. -/
theorem apply_generalized_atom_compose (g : TermMapping S T) (h : TermMapping T U) : apply_generalized_atom (sig := sig) (h ∘ g) = (apply_generalized_atom h) ∘ (apply_generalized_atom g) := by
  apply funext
  intro a
  simp [apply_generalized_atom]

/-- We can split the application of a composed `TermMapping` on an atom. -/
theorem apply_generalized_atom_compose' (g : TermMapping S T) (h : TermMapping T U) : ∀ (a : GeneralizedAtom sig S), apply_generalized_atom (h ∘ g) a = (apply_generalized_atom h) (apply_generalized_atom g a) := by
  intro a
  rw [← Function.comp_apply (f := h.apply_generalized_atom)]
  rw [← apply_generalized_atom_compose]

/-- To show that applying two `TermMapping`s on the same atom yields the same result, it is enough to show that the mappings behave identical on each term. -/
theorem apply_generalized_atom_congr_left (g h : TermMapping S T) (a : GeneralizedAtom sig S) :
    (∀ t ∈ a.terms, g t = h t) -> g.apply_generalized_atom a = h.apply_generalized_atom a := by
  intro same
  rw [GeneralizedAtom.mk.injEq]
  constructor
  . rfl
  . apply List.map_congr_left
    exact same

/-- Applying a `TermMapping` on a `GeneralizedAtom` is the identity if the mapping is the identity on each term. -/
theorem apply_generalized_atom_eq_self_of_id_on_terms (h : TermMapping T T) (a : GeneralizedAtom sig T) (id_on_terms : ∀ t ∈ a.terms, h t = t) :
    h.apply_generalized_atom a = a := by
  rw [GeneralizedAtom.mk.injEq]
  constructor
  . rfl
  . apply List.map_id_of_id_on_all_mem
    exact id_on_terms

/-- We can split the application of a composed `TermMapping` on a list of atoms. -/
theorem apply_generalized_atom_list_compose (g : TermMapping S T) (h : TermMapping T U) : apply_generalized_atom_list (sig := sig) (h ∘ g) = (apply_generalized_atom_list h) ∘ (apply_generalized_atom_list g) := by
  apply funext
  intro l
  unfold apply_generalized_atom_list
  rw [Function.comp_apply, List.map_map]
  rw [apply_generalized_atom_compose]

/-- We can split the application of a composed `TermMapping` on a list of atoms. -/
theorem apply_generalized_atom_list_compose' (g : TermMapping S T) (h : TermMapping T U) : ∀ l : List (GeneralizedAtom sig S), apply_generalized_atom_list (h ∘ g) l = (apply_generalized_atom_list h) (apply_generalized_atom_list g l) := by
  intro l
  rw [← Function.comp_apply (f := h.apply_generalized_atom_list)]
  rw [← apply_generalized_atom_list_compose]

/-- We can split the application of a composed `TermMapping` on a set of atoms. -/
theorem apply_generalized_atom_set_compose (g : TermMapping S T) (h : TermMapping T U) : apply_generalized_atom_set (sig := sig) (h ∘ g) = (apply_generalized_atom_set h) ∘ (apply_generalized_atom_set g) := by
  apply funext
  intro s
  apply Set.ext
  intro a
  constructor
  . intro pre
    rcases pre with ⟨a', a'_mem, a'_eq⟩
    rw [apply_generalized_atom_compose, Function.comp_apply] at a'_eq
    exists g.apply_generalized_atom a'
    constructor
    . exists a'
    . exact a'_eq
  . intro pre
    rcases pre with ⟨a', a'_mem, a'_eq⟩
    rcases a'_mem with ⟨a'', a''_mem, a''_eq⟩
    exists a''
    constructor
    . exact a''_mem
    . rw [apply_generalized_atom_compose, Function.comp_apply]
      rw [a'_eq, a''_eq]

/-- We can split the application of a composed `TermMapping` on a set of atoms. -/
theorem apply_generalized_atom_set_compose' (g : TermMapping S T) (h : TermMapping T U) : ∀ s : Set (GeneralizedAtom sig S), apply_generalized_atom_set (h ∘ g) s = (apply_generalized_atom_set h) (apply_generalized_atom_set g s) := by
  intro l
  rw [← Function.comp_apply (f := h.apply_generalized_atom_set)]
  rw [← apply_generalized_atom_set_compose]

/-- Applying a `TermMapping` to both an atom and a set of atoms retains membership of the atom in the set. -/
theorem apply_generalized_atom_mem_apply_generalized_atom_set
    (h : TermMapping S T) (a : GeneralizedAtom sig S) (as : Set (GeneralizedAtom sig S)) :
    a ∈ as -> h.apply_generalized_atom a ∈ h.apply_generalized_atom_set as := by
  intro a_mem
  exists a

/-- Applying the same `TermMapping` to two sets of atoms retains their subset relation. -/
theorem apply_generalized_atom_set_subset_of_subset (h : TermMapping S T) (as bs : Set (GeneralizedAtom sig S)) :
    as ⊆ bs -> h.apply_generalized_atom_set as ⊆ h.apply_generalized_atom_set bs := by
  intro subset
  intro a a_mem
  rcases a_mem with ⟨a', a'_mem, a'_eq⟩
  rw [a'_eq]
  apply apply_generalized_atom_mem_apply_generalized_atom_set
  apply subset
  exact a'_mem

/-- When mapping a set of atoms that results from the list, we can instead map on the list and then convert to the set. -/
theorem apply_generalized_atom_set_toSet {g : TermMapping S T} :
    ∀ l : List (GeneralizedAtom sig S), g.apply_generalized_atom_set l.toSet = (g.apply_generalized_atom_list l).toSet := by
  intro l; exact List.map_toSet_eq_toSet_map

end TermMapping

end TermMapping

section GroundSubstitution

/-!
## GroundSubstitution

`GroundSubstitution` is used mainly on rules to map the variables to some actual ground terms.
This is a key ingredient of `PrTrigger`s that model "rule applications" in the chase.
-/

/-- A `GroundSubstitution` is merely a `TermMapping` from variables to `GroundTerm`s. -/
abbrev GroundSubstitution (sig : Signature) [DecidableEq sig.C] [DecidableEq sig.V] := TermMapping sig.V (GroundTerm sig)

namespace GroundSubstitution

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

/-- We lift `GroundSubstitution`s to mappings from `VarOrConst` to `GroundTerm` in the obvious way. -/
def apply_var_or_const (σ : GroundSubstitution sig) : TermMapping (VarOrConst sig) (GroundTerm sig)
  | .var v => σ v
  | .const c => GroundTerm.const c

/-- We lift `GroundSubstitution`s to mappings from `SkolemTerm` to `GroundTerm` in the obvious way. -/
def apply_skolem_term (σ : GroundSubstitution sig) : TermMapping (SkolemTerm sig) (GroundTerm sig)
  | .var v => σ v
  | .const c => GroundTerm.const c
  | .func fs frontier arity_ok =>
    GroundTerm.func fs (frontier.map (fun fv => σ fv)) (by
      rw [List.length_map]
      exact arity_ok
    )

/-- On functional `SkolemTerm`s that share the same frontier, applying a `GroundSubstitution` is injective. -/
theorem apply_skolem_term_injective_on_func_of_frontier_eq
    (subs : GroundSubstitution sig) (s t : SkolemTerm sig)
    (hs : s = SkolemTerm.func a frontier arity_a) (ht : t = SkolemTerm.func b frontier arity_b) :
    subs.apply_skolem_term s = subs.apply_skolem_term t -> s = t := by
  simp only [hs, ht, apply_skolem_term]
  intro h
  simp only [GroundTerm.func, Subtype.mk.injEq, FiniteTree.inner.injEq, and_true] at h
  simp [h]

variable [DecidableEq sig.P]

/-- Using the standard functionality of `TermMapping`, we can apply `GroundSubstitution`s directly to an `Atom` yielding a `Fact`. -/
abbrev apply_atom (σ : GroundSubstitution sig) : Atom sig -> Fact sig :=
  σ.apply_skolem_term.apply_generalized_atom

/-- Using the standard functionality of `TermMapping`, we can apply `GroundSubstitution`s directly to a `FunctionFreeAtom` yielding a `Fact`. -/
abbrev apply_function_free_atom (σ : GroundSubstitution sig) : FunctionFreeAtom sig -> Fact sig :=
  σ.apply_var_or_const.apply_generalized_atom

/-- Using the standard functionality of `TermMapping`, we can apply `GroundSubstitution`s directly to a `FunctionFreeConjunction` yielding a list of `Fact`s. -/
abbrev apply_function_free_conj (σ : GroundSubstitution sig) : FunctionFreeConjunction sig -> List (Fact sig) :=
  σ.apply_var_or_const.apply_generalized_atom_list

end GroundSubstitution

end GroundSubstitution

section GroundTermMapping

/-!
## GroundTermMapping

A `GroundTermMapping` maps `GroundTerm`s to `GroundTerm`s and is used to define homomorphisms over `FactSet`s.
-/

/-- A `GroundTermMapping` is merely a `TermMapping` over `GroundTerm`s. -/
abbrev GroundTermMapping (sig : Signature) [DecidableEq sig.C] [DecidableEq sig.V] := TermMapping (GroundTerm sig) (GroundTerm sig)

namespace GroundTermMapping

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

def isIdOnConstants (h : GroundTermMapping sig) : Prop := ∀ {c}, h (.const c) = .const c

variable [DecidableEq sig.P]

/-- Using the standard functionality of `TermMapping`, we can list `GroundTermMapping`s to `Fact`s. -/
abbrev applyFact (h : GroundTermMapping sig) : Fact sig -> Fact sig := h.apply_generalized_atom

/-- Using the standard functionality of `TermMapping`, we can list `GroundTermMapping`s to `FactSet`s. -/
abbrev applyFactSet (h : GroundTermMapping sig) : FactSet sig -> FactSet sig := h.apply_generalized_atom_set

/-- A `GroundTermMapping` is a homomorphisms from `FactSet` A to B if each constant is mapped to itself and mapping A results in a subset of B. -/
def isHomomorphism (h : GroundTermMapping sig) (A B : FactSet sig) : Prop :=
  isIdOnConstants h ∧ (h.applyFactSet A ⊆ B)

/-- The terms in a mapped `FactSet` are the same as the mapped terms from the original `FactSet`. -/
theorem terms_applyFactSet {h : GroundTermMapping sig} {fs : FactSet sig} : (h.applyFactSet fs).terms = fs.terms.map h := by
  apply Set.ext; intro t
  constructor
  . rintro ⟨f, ⟨f', f'_mem, f_eq⟩, t_mem⟩
    rw [f_eq] at t_mem
    simp only [TermMapping.apply_generalized_atom, List.mem_map] at t_mem
    rcases t_mem with ⟨t', t'_mem, t_eq⟩
    rw [← t_eq]
    exists t'; simp only [and_true]
    exists f'
  . rintro ⟨t', ⟨f', f'_mem, t'_mem⟩, t_eq⟩
    rw [t_eq]
    exists h.applyFact f'; constructor
    . apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set; exact f'_mem
    . simp only [applyFact, TermMapping.apply_generalized_atom]; apply List.mem_map_of_mem; exact t'_mem

/-- We can compose homomorphisms. That is, given a homomorphism from A to B and from B to C, we can combine both to obtain a homomorphisms from A to C. -/
theorem isHomomorphism_compose (g h : GroundTermMapping sig) (A B C : FactSet sig) :
    g.isHomomorphism A B -> h.isHomomorphism B C -> isHomomorphism (h ∘ g) A C := by
  intro g_hom h_hom
  constructor
  . intro c
    rw [Function.comp_apply, g_hom.left, h_hom.left]
  . unfold applyFactSet
    rw [TermMapping.apply_generalized_atom_set_compose]
    intro f f_mem_compose
    rcases f_mem_compose with ⟨f', f'_mem, f'_eq⟩
    apply h_hom.right
    exists f'
    constructor
    . apply g_hom.right
      exact f'_mem
    . exact f'_eq

end GroundTermMapping

end GroundTermMapping

section GroundSubstitutionInteractionWithGroundTermMapping

/-!
## Interactions of GroundSubstitution and GroundTermMapping

Sometimes, a `GroundSubstitution` and `GroundTermMapping` might be composed into a single `GroundSubstitution`.
In such a case, it can be useful to be able to split them apart. But this is generally only possible if the `GroundTermMapping` leaves the relevant constants untouched.
-/

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

/-- The application of a composed substitution on a `VarOrConst` can be split if the involved `GroundTermMapping` maps the `VarOrConst` to itself, in the case where it is a constant. -/
theorem GroundSubstitution.apply_var_or_const_compose (s : GroundSubstitution sig) (h : GroundTermMapping sig) :
    ∀ (voc : VarOrConst sig), (∀ d, voc = VarOrConst.const d -> h (GroundTerm.const d) = GroundTerm.const d) -> GroundSubstitution.apply_var_or_const (h ∘ s) voc = h (s.apply_var_or_const voc) := by
  intro voc id_on_const
  unfold GroundSubstitution.apply_var_or_const
  cases voc with
  | var v => simp
  | const c =>
    simp only
    rw [id_on_const]
    rfl

/-- This is a special case of the above theorem where the `GroundTermMapping` is simply the id on all constants. -/
theorem GroundSubstitution.apply_var_or_const_compose_of_isIdOnConstants (s : GroundSubstitution sig)
    (h : GroundTermMapping sig) (id_on_const : h.isIdOnConstants) :
    GroundSubstitution.apply_var_or_const (h ∘ s) = h ∘ s.apply_var_or_const := by
  apply funext
  intro voc
  apply apply_var_or_const_compose
  intros
  exact id_on_const

variable [DecidableEq sig.P]

/-- The application of a composed substitution on a `FunctionFreeAtom` can be split if the involved `GroundTermMapping` maps all constants from the atom to themselves. -/
theorem GroundSubstitution.apply_function_free_atom_compose (s : GroundSubstitution sig) (h : GroundTermMapping sig) :
    ∀ (a : FunctionFreeAtom sig), (∀ d ∈ a.constants, h (GroundTerm.const d) = GroundTerm.const d) -> GroundSubstitution.apply_function_free_atom (h ∘ s) a = h.applyFact (s.apply_function_free_atom a) := by
  intro a id_on_const
  unfold GroundTermMapping.applyFact
  rw [← TermMapping.apply_generalized_atom_compose']
  apply TermMapping.apply_generalized_atom_congr_left
  intro voc voc_mem
  apply apply_var_or_const_compose
  intro d d_eq
  apply id_on_const
  unfold FunctionFreeAtom.constants
  apply VarOrConst.mem_filterConsts_of_const
  rw [d_eq] at voc_mem
  exact voc_mem

/-- This is a special case of the above theorem where the `GroundTermMapping` is simply the id on all constants. -/
theorem GroundSubstitution.apply_function_free_atom_compose_of_isIdOnConstants (s : GroundSubstitution sig) (h : GroundTermMapping sig) (id_on_const : h.isIdOnConstants) :
    GroundSubstitution.apply_function_free_atom (h ∘ s) = h.applyFact ∘ s.apply_function_free_atom := by
  apply funext
  intro a
  apply apply_function_free_atom_compose
  intros
  exact id_on_const

/-- The application of a composed substitution on a `FunctionFreeConjunction` can be split if the involved `GroundTermMapping` maps all constants from the conjucntion to themselves. -/
theorem GroundSubstitution.apply_function_free_conj_compose (s : GroundSubstitution sig) (h : GroundTermMapping sig) :
    ∀ (ffc : FunctionFreeConjunction sig), (∀ d ∈ ffc.consts, h (GroundTerm.const d) = GroundTerm.const d) -> GroundSubstitution.apply_function_free_conj (h ∘ s) ffc = h.apply_generalized_atom_list (s.apply_function_free_conj ffc) := by
  intro ffc id_on_const
  unfold GroundSubstitution.apply_function_free_conj TermMapping.apply_generalized_atom_list
  rw [List.map_map]
  apply List.map_congr_left
  intro f f_mem
  rw [← apply_function_free_atom.eq_def, apply_function_free_atom_compose]
  . rfl
  . intro d d_mem; apply id_on_const; simp only [FunctionFreeConjunction.consts, List.mem_flatMap]; exists f

/-- This is a special case of the above theorem where the `GroundTermMapping` is simply the id on all constants. -/
theorem GroundSubstitution.apply_function_free_conj_compose_of_isIdOnConstants (s : GroundSubstitution sig) (h : GroundTermMapping sig) (id_on_const : h.isIdOnConstants) :
    GroundSubstitution.apply_function_free_conj (h ∘ s) = h.apply_generalized_atom_list ∘ s.apply_function_free_conj := by
  apply funext
  intro ffc
  apply apply_function_free_conj_compose
  intros
  exact id_on_const

end GroundSubstitutionInteractionWithGroundTermMapping

