import BasicLeanDatastructures.List.Basic

import ExistentialRules.AtomsAndFacts.Basic

section Defs

  variable (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

  abbrev GroundSubstitution := sig.V -> GroundTerm sig

  abbrev GroundTermMapping := GroundTerm sig -> GroundTerm sig

end Defs

namespace GroundSubstitution

  variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

  def apply_var_or_const (σ : GroundSubstitution sig) : VarOrConst sig -> GroundTerm sig
    | .var v => σ v
    | .const c => GroundTerm.const c

  def apply_skolem_term (σ : GroundSubstitution sig) : SkolemTerm sig -> GroundTerm sig
    | .var v => σ v
    | .const c => GroundTerm.const c
    | .func fs frontier arity_ok =>
      GroundTerm.func fs (frontier.map (fun fv => σ fv)) (by
        rw [List.length_map]
        exact arity_ok
      )

  theorem apply_skolem_term_injective_on_func_of_frontier_eq (subs : GroundSubstitution sig) (s t : SkolemTerm sig)
      (hs : s = SkolemTerm.func a frontier arity_a) (ht : t = SkolemTerm.func b frontier arity_b) :
      subs.apply_skolem_term s = subs.apply_skolem_term t -> s = t := by
    simp only [hs, ht, apply_skolem_term]
    intro h
    unfold GroundTerm.func at h
    simp at h
    simp [h]


  variable [DecidableEq sig.P]

  def apply_atom (σ : GroundSubstitution sig) (a : Atom sig) : Fact sig :=
    { predicate := a.predicate, terms := List.map (apply_skolem_term σ) a.terms, arity_ok := by rw [List.length_map, a.arity_ok] }

  def apply_function_free_atom (σ : GroundSubstitution sig) (a : FunctionFreeAtom sig) : Fact sig :=
    { predicate := a.predicate, terms := List.map (apply_var_or_const σ) a.terms, arity_ok := by rw [List.length_map, a.arity_ok] }

  def apply_function_free_conj (σ : GroundSubstitution sig) (conj : FunctionFreeConjunction sig) : List (Fact sig) :=
    (List.map (apply_function_free_atom σ)) conj

  theorem length_terms_apply_atom (σ : GroundSubstitution sig) (a : Atom sig) :
      (σ.apply_atom a).terms.length = a.terms.length := by
    simp [apply_atom]

end GroundSubstitution


namespace GroundTermMapping

  variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

  def isIdOnConstants (h : GroundTermMapping sig) : Prop :=
    ∀ (t : GroundTerm sig), match t with
    | .const _ => h t = t
    | _ => True

  theorem apply_constant_is_id_of_isIdOnConstants {h : GroundTermMapping sig} (isId : h.isIdOnConstants) (c : sig.C) :
      h (GroundTerm.const c) = GroundTerm.const c :=
    isId (GroundTerm.const c)

  variable [DecidableEq sig.P]

  def applyFact (h : GroundTermMapping sig) (f : Fact sig) : Fact sig := {
    predicate := f.predicate,
    terms := List.map h f.terms,
    arity_ok := by rw [List.length_map, f.arity_ok]
  }

  theorem applyFact_compose (g h : GroundTermMapping sig) : applyFact (h ∘ g) = (applyFact h) ∘ (applyFact g) := by
    apply funext
    intro t
    simp [applyFact]

  def applyFactSet (h : GroundTermMapping sig) (fs : FactSet sig) : FactSet sig :=
    fun f' : Fact sig => ∃ (f : Fact sig), (f ∈ fs) ∧ ((h.applyFact f) = f')

  theorem applyFactSet_compose (g h : GroundTermMapping sig) : applyFactSet (h ∘ g) = (applyFactSet h) ∘ (applyFactSet g) := by
    apply funext
    intro fs
    apply funext
    intro f
    simp [applyFactSet, applyFact_compose]
    constructor
    . intro pre
      rcases pre with ⟨f', f'_mem, f'_eq⟩
      exists g.applyFact f'
      constructor
      . exists f'
      . exact f'_eq
    . intro pre
      rcases pre with ⟨f', f'_mem, f'_eq⟩
      rcases f'_mem with ⟨f'', f''_mem, f''_eq⟩
      exists f''
      constructor
      . exact f''_mem
      . rw [f''_eq, f'_eq]

  theorem applyPreservesElement (h : GroundTermMapping sig) (f : Fact sig) (fs : FactSet sig) :
      f ∈ fs -> applyFact h f ∈ applyFactSet h fs := by
    intro hf
    simp [Set.element] at *
    unfold applyFactSet
    exists f

  theorem applyFactSet_subset_of_subset (h : GroundTermMapping sig) (as bs : FactSet sig) :
      as ⊆ bs -> h.applyFactSet as ⊆ h.applyFactSet bs := by
    intro subset
    unfold GroundTermMapping.applyFactSet
    intro f f_mem
    rcases f_mem with ⟨f', f'_mem, f'_eq⟩
    exists f'
    constructor
    . apply subset; exact f'_mem
    . exact f'_eq

  def isHomomorphism (h : GroundTermMapping sig) (A B : FactSet sig) : Prop :=
    isIdOnConstants h ∧ (h.applyFactSet A ⊆ B)

  theorem isHomomorphism_compose (g h : GroundTermMapping sig) (A B C : FactSet sig) :
      g.isHomomorphism A B -> h.isHomomorphism B C -> isHomomorphism (h ∘ g) A C := by
    intro g_hom h_hom
    constructor
    . intro t
      cases eq : t with
      | func _ _ => simp [GroundTerm.func]
      | const c =>
        simp only [GroundTerm.const, Function.comp_apply]
        have g_const := g_hom.left t
        simp only [eq, GroundTerm.const] at g_const
        rw [g_const]
        have h_const := h_hom.left t
        simp only [eq, GroundTerm.const] at h_const
        rw [h_const]
    . rw [applyFactSet_compose]
      intro f f_mem_compose
      rcases f_mem_compose with ⟨f', f'_mem, f'_eq⟩
      apply h_hom.right
      exists f'
      constructor
      . apply g_hom.right
        exact f'_mem
      . exact f'_eq

end GroundTermMapping

section GroundSubstitutionInteractionWithGroundTermMapping

  variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

  theorem GroundSubstitution.apply_var_or_const_compose (s : GroundSubstitution sig)
      (h : GroundTermMapping sig) (id_on_const : h.isIdOnConstants) :
      ∀ (voc : VarOrConst sig), GroundSubstitution.apply_var_or_const (h ∘ s) voc = h (s.apply_var_or_const voc) := by
    intro voc
    unfold GroundSubstitution.apply_var_or_const
    cases voc with
    | var v => simp
    | const c =>
      simp only
      rw [id_on_const (GroundTerm.const c)]

  variable [DecidableEq sig.P]

  theorem GroundSubstitution.apply_function_free_atom_compose (s : GroundSubstitution sig) (h : GroundTermMapping sig) (id_on_const : h.isIdOnConstants) :
      ∀ (a : FunctionFreeAtom sig), GroundSubstitution.apply_function_free_atom (h ∘ s) a = h.applyFact (s.apply_function_free_atom a) := by
    unfold GroundTermMapping.applyFact
    unfold GroundSubstitution.apply_function_free_atom
    simp [apply_var_or_const_compose _ _ id_on_const]

end GroundSubstitutionInteractionWithGroundTermMapping

