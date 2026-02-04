import BasicLeanDatastructures.GetFreshInhabitant
import ExistentialRules.ChaseSequence.Termination.RenameConstantsApart
import ExistentialRules.Triggers.Basic

/-!
# Constant Mappings

A `ConstantMapping` is a `TermMapping` from constants to `GroundTerm`s.
This is very similar to a GroundSubstitution only that it maps constants instead of variables
-/

abbrev ConstantMapping (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] := TermMapping sig.C (GroundTerm sig)

namespace ConstantMapping

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- The id `ConstantMapping` is the `GroundTerm.const` constructor. -/
def id : ConstantMapping sig := GroundTerm.const

/-- We apply a `ConstantMapping` to a `PreGroundTerm` by applying it to all leaves. -/
abbrev apply_pre_ground_term (g : ConstantMapping sig) : TermMapping (PreGroundTerm sig) (PreGroundTerm sig) :=
  FiniteTree.mapLeaves (fun c => (g c).val)

/-- Applying the `ConstantMapping.id` on a `PreGroundTerm` yields the same term. -/
theorem apply_pre_ground_term_id (t : FiniteTree (SkolemFS sig) sig.C) : id.apply_pre_ground_term t = t := by
  induction t with
  | leaf c => simp only [apply_pre_ground_term, FiniteTree.mapLeaves]; rfl
  | inner f ts ih =>
    simp only [apply_pre_ground_term, FiniteTree.mapLeaves]
    simp only [FiniteTree.inner.injEq, true_and]
    apply List.map_id_of_id_on_all_mem
    exact ih

/-- Applying a `ConstantMapping` to a `PreGroundTerm` retains the `PreGroundTerm.arity_ok` property. -/
theorem apply_pre_ground_term_arity_ok (g : ConstantMapping sig) (t : FiniteTree (SkolemFS sig) sig.C) (arity_ok : PreGroundTerm.arity_ok t) :
    PreGroundTerm.arity_ok (g.apply_pre_ground_term t) := by
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

/-- Mapping the same term using two `ConstantMapping`s yields the same term if the mappings agree on all leaves of the term. -/
theorem apply_pre_ground_term_congr_left (g g2 : ConstantMapping sig) (t : PreGroundTerm sig) : (∀ c ∈ t.leaves, g c = g2 c) -> g.apply_pre_ground_term t = g2.apply_pre_ground_term t := by
  intro h
  unfold ConstantMapping.apply_pre_ground_term
  apply FiniteTree.mapLeaves_eq_of_map_leaves_eq
  apply List.map_congr_left
  intro c c_mem
  specialize h c c_mem
  rw [h]

/-- If the `ConstantMapping` is the id on the leaves of a term, applying the mapping to the term is also the id. -/
theorem apply_pre_ground_term_eq_self_of_id_on_constants (g : ConstantMapping sig) (t : PreGroundTerm sig) (id_on_constants : ∀ c ∈ t.leaves, g c = .const c) : g.apply_pre_ground_term t = t := by
  unfold ConstantMapping.apply_pre_ground_term
  conv => right; rw [← apply_pre_ground_term_id t]
  apply apply_pre_ground_term_congr_left
  exact id_on_constants

/-- We lift `ConstantMapping`s to `GroundTerm`s in the obvious way. -/
def apply_ground_term (g : ConstantMapping sig) : TermMapping (GroundTerm sig) (GroundTerm sig) :=
  fun t => ⟨g.apply_pre_ground_term t.val, g.apply_pre_ground_term_arity_ok t.val t.property⟩

/-- Applying a `ConstantMapping` to a `GroundTerm.const` is the same as directly applying the mapping to the underlying constant. -/
theorem apply_ground_term_constant (g : ConstantMapping sig) : ∀ c, g.apply_ground_term (.const c) = g c := by
  intro c
  simp [apply_ground_term, apply_pre_ground_term, FiniteTree.mapLeaves, GroundTerm.const]

/-- Applyign a `ConstantMapping` to a `GroundTerm.func` is the same as applying the mapping to all child terms. -/
theorem apply_ground_term_func (g : ConstantMapping sig) :
    ∀ func ts arity_ok, g.apply_ground_term (.func func ts arity_ok) = .func func (ts.map g.apply_ground_term) (by rw [List.length_map]; exact arity_ok) := by
  intro func ts arity_ok
  simp only [GroundTerm.func, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves]
  simp only [Subtype.mk.injEq, FiniteTree.inner.injEq, true_and]
  unfold List.unattach
  rw [List.map_map, List.map_map]
  rw [List.map_inj_left]
  intro t t_mem
  simp only [Function.comp_apply, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term]

/-- For a non-constant `SkolemTerm`, if we apply a `ConstantMapping` after a `GroundSubstitution`, we can instead apply the substitution that is the composition of the `ConstantMapping` after the `GroundSubstitution`. Note that this does not work for constants since the `ConstantMapping` might map it some something else, whereas the composed substitution maps each constant to itself. -/
theorem apply_ground_term_swap_apply_skolem_term (g : ConstantMapping sig) (subs : GroundSubstitution sig) :
    ∀ t, (∀ c, t ≠ SkolemTerm.const c) ->
    g.apply_ground_term (subs.apply_skolem_term t) = GroundSubstitution.apply_skolem_term (g.apply_ground_term ∘ subs) t := by
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

/-- Mapping the same term using two `ConstantMapping`s yields the same term if the mappings agree on all constants of the term. -/
theorem apply_ground_term_congr_left (g g2 : ConstantMapping sig) (t : GroundTerm sig) : (∀ c ∈ t.constants, g c = g2 c) -> g.apply_ground_term t = g2.apply_ground_term t := by
  intro h
  unfold ConstantMapping.apply_ground_term
  rw [Subtype.mk.injEq]
  apply apply_pre_ground_term_congr_left
  exact h

/-- If the `ConstantMapping` is the id on the constants of a term, applying the mapping to the term is also the id. -/
theorem apply_ground_term_eq_self_of_id_on_constants (g : ConstantMapping sig) (t : GroundTerm sig) (id_on_constants : ∀ c ∈ t.constants, g c = .const c) : g.apply_ground_term t = t := by
  unfold ConstantMapping.apply_ground_term
  rw [Subtype.mk.injEq]
  apply apply_pre_ground_term_eq_self_of_id_on_constants
  exact id_on_constants

/-- We lift `ConstantMapping`s to `Fact`s in the obvious way. -/
abbrev apply_fact (g : ConstantMapping sig) : Fact sig -> Fact sig := TermMapping.apply_generalized_atom g.apply_ground_term

/-- Applying a `ConstantMapping` to a fact can be seens as applying a `GroundTermMapping` to the fact. -/
theorem apply_fact_eq_groundTermMapping_applyFact (g : ConstantMapping sig) (f : Fact sig) :
    g.apply_fact f = GroundTermMapping.applyFact g.apply_ground_term f := by
  simp [apply_fact, GroundTermMapping.applyFact]

/-- Consider a `ConstantMapping`, a `PreTrigger`, and a `FunctionFreeAtom`. If the constant mapping if the id on all constants in the atom, then applying the mapping after the trigger is the same a applying a trigger where the constant mapping is composed with the original substitution. -/
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

/-- Mapping the same fact using two `ConstantMapping`s yields the same fact if the mappings agree on all constants of the fact. -/
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

/-- If the `ConstantMapping` is the id on the constants of a fact, applying the mapping to the fact is also the id. -/
theorem apply_fact_eq_self_of_id_on_constants (g : ConstantMapping sig) (f : Fact sig) (id_on_constants : ∀ c ∈ f.constants, g c = .const c) : g.apply_fact f = f := by
  apply TermMapping.apply_generalized_atom_eq_self_of_id_on_terms
  intro t t_mem
  apply apply_ground_term_eq_self_of_id_on_constants
  intro c c_mem
  apply id_on_constants
  unfold Fact.constants
  rw [List.mem_flatMap]
  exists t

/-- We lift `ConstantMapping s to `FactSet`s in the obvious way. -/
abbrev apply_fact_set (g : ConstantMapping sig) : FactSet sig -> FactSet sig := TermMapping.apply_generalized_atom_set g.apply_ground_term

end ConstantMapping

