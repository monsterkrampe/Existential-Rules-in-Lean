import BasicLeanDatastructures.List.Basic

import ExistentialRules.AtomsAndFacts.Basic

section Defs

  abbrev TermMapping (S : Type u) (T : Type v) := S -> T

  variable (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

  abbrev GroundSubstitution := TermMapping sig.V (GroundTerm sig)

  abbrev GroundTermMapping := TermMapping (GroundTerm sig) (GroundTerm sig)

end Defs

namespace TermMapping

  variable {sig : Signature} [DecidableEq sig.P]

  def apply_generalized_atom (h : TermMapping S T) (a : GeneralizedAtom sig S) : GeneralizedAtom sig T := {
    predicate := a.predicate
    terms := a.terms.map h
    arity_ok := by rw [List.length_map, a.arity_ok]
  }

  theorem length_terms_apply_generalized_atom (h : TermMapping S T) (a : GeneralizedAtom sig S) :
      (h.apply_generalized_atom a).terms.length = a.terms.length := by
    simp [apply_generalized_atom]

  theorem apply_generalized_atom_compose (g : TermMapping S T) (h : TermMapping T U) : apply_generalized_atom (sig := sig) (h ∘ g) = (apply_generalized_atom h) ∘ (apply_generalized_atom g) := by
    apply funext
    intro a
    simp [apply_generalized_atom]

  theorem apply_generalized_atom_compose' (g : TermMapping S T) (h : TermMapping T U) : ∀ (a : GeneralizedAtom sig S), apply_generalized_atom (h ∘ g) a = (apply_generalized_atom h) (apply_generalized_atom g a) := by
    intro a
    rw [← Function.comp_apply (f := h.apply_generalized_atom)]
    rw [← apply_generalized_atom_compose]

  theorem apply_generalized_atom_congr_left (g h : TermMapping S T) (a : GeneralizedAtom sig S) : (∀ t ∈ a.terms, g t = h t) -> g.apply_generalized_atom a = h.apply_generalized_atom a := by
    intro same
    rw [GeneralizedAtom.mk.injEq]
    constructor
    . rfl
    . apply List.map_congr_left
      exact same

  theorem apply_generalized_atom_eq_self_of_id_on_terms (h : TermMapping T T) (a : GeneralizedAtom sig T) (id_on_terms : ∀ t ∈ a.terms, h t = t) : h.apply_generalized_atom a = a := by
    rw [GeneralizedAtom.mk.injEq]
    constructor
    . rfl
    . apply List.map_id_of_id_on_all_mem
      exact id_on_terms

  def apply_generalized_atom_list (h : TermMapping S T) (l : List (GeneralizedAtom sig S)) : List (GeneralizedAtom sig T) :=
    l.map h.apply_generalized_atom

  theorem apply_generalized_atom_list_compose (g : TermMapping S T) (h : TermMapping T U) : apply_generalized_atom_list (sig := sig) (h ∘ g) = (apply_generalized_atom_list h) ∘ (apply_generalized_atom_list g) := by
    apply funext
    intro l
    unfold apply_generalized_atom_list
    rw [Function.comp_apply, List.map_map]
    rw [apply_generalized_atom_compose]

  theorem apply_generalized_atom_list_compose' (g : TermMapping S T) (h : TermMapping T U) : ∀ l : List (GeneralizedAtom sig S), apply_generalized_atom_list (h ∘ g) l = (apply_generalized_atom_list h) (apply_generalized_atom_list g l) := by
    intro l
    rw [← Function.comp_apply (f := h.apply_generalized_atom_list)]
    rw [← apply_generalized_atom_list_compose]

  def apply_generalized_atom_set (h : TermMapping S T) (s : Set (GeneralizedAtom sig S)) : Set (GeneralizedAtom sig T) :=
    s.map h.apply_generalized_atom

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

  theorem apply_generalized_atom_set_compose' (g : TermMapping S T) (h : TermMapping T U) : ∀ s : Set (GeneralizedAtom sig S), apply_generalized_atom_set (h ∘ g) s = (apply_generalized_atom_set h) (apply_generalized_atom_set g s) := by
    intro l
    rw [← Function.comp_apply (f := h.apply_generalized_atom_set)]
    rw [← apply_generalized_atom_set_compose]

  theorem apply_generalized_atom_mem_apply_generalized_atom_set
      (h : TermMapping S T) (a : GeneralizedAtom sig S) (as : Set (GeneralizedAtom sig S)) :
      a ∈ as -> h.apply_generalized_atom a ∈ h.apply_generalized_atom_set as := by
    intro a_mem
    exists a

  theorem apply_generalized_atom_set_subset_of_subset (h : TermMapping S T) (as bs : Set (GeneralizedAtom sig S)) :
      as ⊆ bs -> h.apply_generalized_atom_set as ⊆ h.apply_generalized_atom_set bs := by
    intro subset
    intro a a_mem
    rcases a_mem with ⟨a', a'_mem, a'_eq⟩
    rw [a'_eq]
    apply apply_generalized_atom_mem_apply_generalized_atom_set
    apply subset
    exact a'_mem

  theorem apply_generalized_atom_set_toSet {g : TermMapping S T} : ∀ l : List (GeneralizedAtom sig S), g.apply_generalized_atom_set l.toSet = (g.apply_generalized_atom_list l).toSet := by
    intro l; apply Set.ext; intro f; constructor
    . rintro ⟨f', f'_mem, f_eq⟩; rw [f_eq, List.mem_toSet]; apply List.mem_map_of_mem; rw [← List.mem_toSet]; exact f'_mem
    . simp only [List.mem_toSet, apply_generalized_atom_list, List.mem_map]; rintro ⟨f', f'_mem, f_eq⟩; rw [← f_eq]; apply apply_generalized_atom_mem_apply_generalized_atom_set; rw [List.mem_toSet]; exact f'_mem

end TermMapping

namespace GroundSubstitution

  variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

  -- TODO: maybe rename this one and alike to lift_to_var_or_const
  def apply_var_or_const (σ : GroundSubstitution sig) : TermMapping (VarOrConst sig) (GroundTerm sig)
    | .var v => σ v
    | .const c => GroundTerm.const c

  def apply_skolem_term (σ : GroundSubstitution sig) : TermMapping (SkolemTerm sig) (GroundTerm sig)
    | .var v => σ v
    | .const c => GroundTerm.const c
    | .func fs frontier arity_ok =>
      GroundTerm.func fs (frontier.map (fun fv => σ fv)) (by
        rw [List.length_map]
        exact arity_ok
      )

  theorem apply_skolem_term_injective_on_func_of_frontier_eq
      (subs : GroundSubstitution sig) (s t : SkolemTerm sig)
      (hs : s = SkolemTerm.func a frontier arity_a) (ht : t = SkolemTerm.func b frontier arity_b) :
      subs.apply_skolem_term s = subs.apply_skolem_term t -> s = t := by
    simp only [hs, ht, apply_skolem_term]
    intro h
    unfold GroundTerm.func at h
    simp at h
    simp [h]


  variable [DecidableEq sig.P]

  abbrev apply_atom (σ : GroundSubstitution sig) : Atom sig -> Fact sig :=
    σ.apply_skolem_term.apply_generalized_atom

  abbrev apply_function_free_atom (σ : GroundSubstitution sig) : FunctionFreeAtom sig -> Fact sig :=
    σ.apply_var_or_const.apply_generalized_atom

  abbrev apply_function_free_conj (σ : GroundSubstitution sig) : FunctionFreeConjunction sig -> List (Fact sig) :=
    σ.apply_var_or_const.apply_generalized_atom_list

end GroundSubstitution


namespace GroundTermMapping

  variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

  def isIdOnConstants (h : GroundTermMapping sig) : Prop := ∀ {c}, h (.const c) = .const c

  theorem apply_constant_is_id_of_isIdOnConstants {h : GroundTermMapping sig} (isId : h.isIdOnConstants) (c : sig.C) :
      h (GroundTerm.const c) = GroundTerm.const c := isId

  variable [DecidableEq sig.P]

  abbrev applyFact (h : GroundTermMapping sig) : Fact sig -> Fact sig := h.apply_generalized_atom

  abbrev applyFactSet (h : GroundTermMapping sig) : FactSet sig -> FactSet sig := h.apply_generalized_atom_set

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

  def isHomomorphism (h : GroundTermMapping sig) (A B : FactSet sig) : Prop :=
    isIdOnConstants h ∧ (h.applyFactSet A ⊆ B)

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

section GroundSubstitutionInteractionWithGroundTermMapping

  variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

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

  theorem GroundSubstitution.apply_var_or_const_compose_of_isIdOnConstants (s : GroundSubstitution sig)
      (h : GroundTermMapping sig) (id_on_const : h.isIdOnConstants) :
      GroundSubstitution.apply_var_or_const (h ∘ s) = h ∘ s.apply_var_or_const := by
    apply funext
    intro voc
    apply apply_var_or_const_compose
    intros
    exact id_on_const

  variable [DecidableEq sig.P]

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

  theorem GroundSubstitution.apply_function_free_atom_compose_of_isIdOnConstants (s : GroundSubstitution sig) (h : GroundTermMapping sig) (id_on_const : h.isIdOnConstants) :
      GroundSubstitution.apply_function_free_atom (h ∘ s) = h.applyFact ∘ s.apply_function_free_atom := by
    apply funext
    intro a
    apply apply_function_free_atom_compose
    intros
    exact id_on_const

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

  theorem GroundSubstitution.apply_function_free_conj_compose_of_isIdOnConstants (s : GroundSubstitution sig) (h : GroundTermMapping sig) (id_on_const : h.isIdOnConstants) :
      GroundSubstitution.apply_function_free_conj (h ∘ s) = h.apply_generalized_atom_list ∘ s.apply_function_free_conj := by
    apply funext
    intro ffc
    apply apply_function_free_conj_compose
    intros
    exact id_on_const

end GroundSubstitutionInteractionWithGroundTermMapping

