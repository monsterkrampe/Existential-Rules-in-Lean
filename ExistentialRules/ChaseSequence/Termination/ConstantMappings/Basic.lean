import BasicLeanDatastructures.GetFreshInhabitant
import ExistentialRules.ChaseSequence.Termination.RenameConstantsApart
import ExistentialRules.Triggers.Basic

-- This is essentially the same as a GroundSubstitution only that it maps constants instead of variables
abbrev ConstantMapping (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] := TermMapping sig.C (GroundTerm sig)

namespace ConstantMapping

  variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

  def id : ConstantMapping sig := fun c => .const c

  abbrev apply_pre_ground_term (g : ConstantMapping sig) : TermMapping (PreGroundTerm sig) (PreGroundTerm sig) :=
    FiniteTree.mapLeaves (fun c => (g c).val)

  theorem apply_pre_ground_term_id (t : FiniteTree (SkolemFS sig) sig.C) : id.apply_pre_ground_term t = t := by
    induction t with
    | leaf c => simp only [apply_pre_ground_term, FiniteTree.mapLeaves]; rfl
    | inner f ts ih =>
      simp only [apply_pre_ground_term, FiniteTree.mapLeaves]
      simp only [FiniteTree.inner.injEq, true_and]
      apply List.map_id_of_id_on_all_mem
      exact ih

  theorem apply_pre_ground_term_arity_ok (g : ConstantMapping sig) (t : FiniteTree (SkolemFS sig) sig.C) (arity_ok : PreGroundTerm.arity_ok t) : PreGroundTerm.arity_ok (g.apply_pre_ground_term t) := by
    induction t with
    | leaf c => simp only [apply_pre_ground_term, FiniteTree.mapLeaves]; exact (g c).property
    | inner f ts ih =>
      unfold PreGroundTerm.arity_ok at arity_ok
      rw [Bool.and_eq_true] at arity_ok
      simp only [apply_pre_ground_term, FiniteTree.mapLeaves, PreGroundTerm.arity_ok]
      rw [Bool.and_eq_true]
      constructor
      . rw [List.length_map]; exact arity_ok.left
      . rw [List.all_eq_true]
        intro ⟨t, t_mem⟩ _
        rw [List.mem_map] at t_mem
        rcases t_mem with ⟨t', t'_mem, t_eq⟩
        simp only [← t_eq]
        apply ih
        . exact t'_mem
        . have := arity_ok.right
          rw [List.all_eq_true] at this
          apply this ⟨t', t'_mem⟩
          simp

  -- naming inspired by List.map_congr_left
  theorem apply_pre_ground_term_congr_left (g g2 : ConstantMapping sig) (t : PreGroundTerm sig) : (∀ c ∈ t.leaves, g c = g2 c) -> g.apply_pre_ground_term t = g2.apply_pre_ground_term t := by
    intro h
    unfold ConstantMapping.apply_pre_ground_term
    apply FiniteTree.mapLeaves_eq_of_map_leaves_eq
    apply List.map_congr_left
    intro c c_mem
    specialize h c c_mem
    rw [h]

  theorem apply_pre_ground_term_eq_self_of_id_on_constants (g : ConstantMapping sig) (t : PreGroundTerm sig) (id_on_constants : ∀ c ∈ t.leaves, g c = .const c) : g.apply_pre_ground_term t = t := by
    unfold ConstantMapping.apply_pre_ground_term
    conv => right; rw [← apply_pre_ground_term_id t]
    apply apply_pre_ground_term_congr_left
    exact id_on_constants

  def apply_ground_term (g : ConstantMapping sig) : TermMapping (GroundTerm sig) (GroundTerm sig) :=
    fun t => ⟨g.apply_pre_ground_term t.val, g.apply_pre_ground_term_arity_ok t.val t.property⟩

  theorem apply_ground_term_constant (g : ConstantMapping sig) : ∀ c, g.apply_ground_term (.const c) = g c := by
    intro c
    simp [apply_ground_term, apply_pre_ground_term, FiniteTree.mapLeaves, GroundTerm.const]

  theorem apply_ground_term_func (g : ConstantMapping sig) : ∀ func ts arity_ok, g.apply_ground_term (.func func ts arity_ok) = .func func (ts.map g.apply_ground_term) (by rw [List.length_map]; exact arity_ok) := by
    intro func ts arity_ok
    simp only [GroundTerm.func, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves]
    simp only [Subtype.mk.injEq, FiniteTree.inner.injEq, true_and]
    unfold List.unattach
    rw [List.map_map, List.map_map]
    rw [List.map_inj_left]
    intro t t_mem
    simp only [Function.comp_apply, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term]

  theorem apply_ground_term_swap_apply_skolem_term (g : ConstantMapping sig) (subs : GroundSubstitution sig) : ∀ t, (∀ c, t ≠ SkolemTerm.const c) -> g.apply_ground_term (subs.apply_skolem_term t) = GroundSubstitution.apply_skolem_term (g.apply_ground_term ∘ subs) t := by
    intro t
    cases t with
    | var v =>
      intros
      unfold GroundSubstitution.apply_skolem_term
      simp
    | const c => simp
    | func f ts =>
      intros
      conv => left; unfold ConstantMapping.apply_ground_term; unfold GroundSubstitution.apply_skolem_term
      conv => right; unfold GroundSubstitution.apply_skolem_term
      unfold GroundTerm.func
      simp only [apply_pre_ground_term, FiniteTree.mapLeaves]
      simp only [Subtype.mk.injEq, FiniteTree.inner.injEq, true_and]
      unfold List.unattach
      rw [List.map_map]
      rw [List.map_map]
      rw [List.map_map]
      rfl

  -- naming inspired by List.map_congr_left
  theorem apply_ground_term_congr_left (g g2 : ConstantMapping sig) (t : GroundTerm sig) : (∀ c ∈ t.constants, g c = g2 c) -> g.apply_ground_term t = g2.apply_ground_term t := by
    intro h
    unfold ConstantMapping.apply_ground_term
    rw [Subtype.mk.injEq]
    apply apply_pre_ground_term_congr_left
    exact h

  theorem apply_ground_term_eq_self_of_id_on_constants (g : ConstantMapping sig) (t : GroundTerm sig) (id_on_constants : ∀ c ∈ t.constants, g c = .const c) : g.apply_ground_term t = t := by
    unfold ConstantMapping.apply_ground_term
    rw [Subtype.mk.injEq]
    apply apply_pre_ground_term_eq_self_of_id_on_constants
    exact id_on_constants

  abbrev apply_fact (g : ConstantMapping sig) : Fact sig -> Fact sig := TermMapping.apply_generalized_atom g.apply_ground_term

  -- TODO: do we still need this?
  theorem apply_fact_eq_groundTermMapping_applyFact (g : ConstantMapping sig) (f : Fact sig) : g.apply_fact f = GroundTermMapping.applyFact g.apply_ground_term f := by
    simp [apply_fact, GroundTermMapping.applyFact]

  theorem apply_fact_swap_apply_to_function_free_atom (g : ConstantMapping sig) (trg : PreTrigger sig) (a : FunctionFreeAtom sig) (h : ∀ d ∈ a.constants, g d = GroundTerm.const d) : ∀ i, g.apply_fact (trg.apply_to_function_free_atom i a) = PreTrigger.apply_to_function_free_atom { rule := trg.rule, subs := g.apply_ground_term ∘ trg.subs } i a := by
    intro i
    unfold PreTrigger.apply_to_function_free_atom
    unfold ConstantMapping.apply_fact
    unfold PreTrigger.apply_to_var_or_const
    rw [← TermMapping.apply_generalized_atom_compose']
    apply TermMapping.apply_generalized_atom_congr_left
    intro voc voc_mem
    simp only [Function.comp_apply]
    cases voc with
    | var v =>
      rw [ConstantMapping.apply_ground_term_swap_apply_skolem_term]
      . rfl
      . intro c contra
        simp only [PreTrigger.skolemize_var_or_const, VarOrConst.skolemize] at contra
        split at contra <;> contradiction
    | const d =>
      simp only [PreTrigger.skolemize_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term]
      rw [g.apply_ground_term_constant]
      apply h
      apply VarOrConst.mem_filterConsts_of_const
      exact voc_mem

  -- naming inspired by List.map_congr_left
  theorem apply_fact_congr_left (g g2 : ConstantMapping sig) (f : Fact sig) : (∀ c ∈ f.constants, g c = g2 c) -> g.apply_fact f = g2.apply_fact f := by
    intro h
    apply TermMapping.apply_generalized_atom_congr_left
    intro t t_mem
    apply apply_ground_term_congr_left
    intro c c_mem
    apply h
    unfold Fact.constants
    rw [List.mem_flatMap]
    exists t

  theorem apply_fact_eq_self_of_id_on_constants (g : ConstantMapping sig) (f : Fact sig) (id_on_constants : ∀ c ∈ f.constants, g c = .const c) : g.apply_fact f = f := by
    apply TermMapping.apply_generalized_atom_eq_self_of_id_on_terms
    intro t t_mem
    apply apply_ground_term_eq_self_of_id_on_constants
    intro c c_mem
    apply id_on_constants
    unfold Fact.constants
    rw [List.mem_flatMap]
    exists t

  abbrev apply_fact_set (g : ConstantMapping sig) : FactSet sig -> FactSet sig := TermMapping.apply_generalized_atom_set g.apply_ground_term

end ConstantMapping

