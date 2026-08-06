/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.AtomsAndRules.FactSet
public import ExistentialRules.AtomsAndRules.Rule
public import ExistentialRules.SubstitutionsAndHomomorphisms

/-!
# PreTriggers

Triggers are one of the most essential definitions for the chase. They are our primary way for modelling specific applications of rules.
Quite simply, a trigger is just a pair of a rule and a substitution that tells us how variables should be replaced.
For actual triggers, we will require a way to tell if they should still be applied or not. We refer to this with the notion of "obsolescence" later.
However, most of the machinery around triggers can be introduced agnostic of any kind of obsolescence.
Consequently, we call the "almost trigger" a `PreTrigger`.

A trigger is self contained in the sense that it "knows" what its result will be independant of the chase context.
This would not be so simple if we considered nulls instead of Skolem terms.
-/

public section

/-- A `PreTrigger` is nothing more than a pair of a `Rule` and a `GroundSubstitution`. -/
structure PreTrigger (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
  rule : Rule sig
  subs : GroundSubstitution sig

namespace PreTrigger

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- The `mapped_frontier` results from applying the triggers substitution to all frontier variables. -/
@[expose]
def mapped_frontier (trg : PreTrigger sig) : List (GroundTerm sig) := trg.rule.frontier.map trg.subs

/-- The lenth of the `mapped_frontier` is exactly the length of the frontier. -/
@[simp, grind =]
theorem length_mapped_frontier {trg : PreTrigger sig} : trg.mapped_frontier.length = trg.rule.frontier.length := by simp [mapped_frontier]

/-- Applying a term mapping after the trigger can be combined with the substitution without affecting the `mapped_frontier`. -/
theorem apply_mapping_after_mapped_frontier {trg : PreTrigger sig} {mapping : TermMapping (GroundTerm sig) (GroundTerm sig)} :
    trg.mapped_frontier.map mapping = {rule := trg.rule, subs := mapping ∘ trg.subs : PreTrigger sig}.mapped_frontier := by
  simp [mapped_frontier]

/-- In the context of a trigger, we Skolemize a `VarOrConst` by passing the rule in the trigger. -/
def skolemize_var_or_const (trg : PreTrigger sig) (i : Nat) (lt : i < trg.rule.head.length) (var_or_const : VarOrConst sig) : SkolemTerm sig :=
  var_or_const.skolemize trg.rule i lt

/-- We apply a trigger to a `VarOrConst` by Skolemizing and then applying the `GroundSubstitution` from the trigger. We need this to define the trigger result later. -/
def apply_to_var_or_const (trg : PreTrigger sig) (i : Nat) (lt : i < trg.rule.head.length) : TermMapping (VarOrConst sig) (GroundTerm sig) :=
  (trg.subs.apply_skolem_term ∘ (trg.skolemize_var_or_const i lt))

/-- Applying a trigger to a constant changes nothing. -/
@[simp, grind =]
theorem apply_to_var_or_const_for_const (trg : PreTrigger sig) (i : Nat) (lt : i < trg.rule.head.length) :
    ∀ c, trg.apply_to_var_or_const i lt (.const c) = GroundTerm.const c := by
  simp [apply_to_var_or_const, skolemize_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term]

/-- Applying a trigger to an non-existential variable does not skolemize but merely applied the substitution. -/
@[simp, grind =]
theorem apply_to_var_or_const_of_not_mem_existential_vars (trg : PreTrigger sig) (i : Nat) (lt : i < trg.rule.head.length) :
    ∀ v, v ∉ trg.rule.existential_vars_for_head_disjunct i lt -> trg.apply_to_var_or_const i lt (.var v) = trg.subs v := by
  intro v v_mem
  simp [apply_to_var_or_const, skolemize_var_or_const, VarOrConst.skolemize, v_mem, GroundSubstitution.apply_skolem_term]

/-- Applying a trigger to a frontier variable does not skolemize but merely applied the substitution. -/
@[simp, grind =]
theorem apply_to_var_or_const_frontier_var (trg : PreTrigger sig) (i : Nat) (lt : i < trg.rule.head.length) :
    ∀ v, v ∈ trg.rule.frontier -> trg.apply_to_var_or_const i lt (.var v) = trg.subs v := by
  intro v v_front
  suffices v ∉ trg.rule.existential_vars_for_head_disjunct i lt by exact apply_to_var_or_const_of_not_mem_existential_vars _ _ _ _ this
  intro contra; apply trg.rule.not_mem_frontier_of_mem_existential_vars_for_head_disjunct _ contra; exact v_front

/-- A shortcut definition for how the Skolem term resulting from applying the trigger to an existential variable will look. -/
@[expose]
def functional_term_for_var
    (trg : PreTrigger sig)
    (i : Nat) (lt : i < trg.rule.head.length)
    (v : sig.V)
    (v_mem : v ∈ trg.rule.existential_vars_for_head_disjunct i lt) :
    GroundTerm sig :=
  GroundTerm.func
    { rule := trg.rule, headIdx := i, headIdx_lt := lt, v, v_mem }
    trg.mapped_frontier
    (by rw [length_mapped_frontier]; rfl)

/-- The `functional_term_for_var` function is injective for a fixed trigger. -/
@[grind ->]
theorem functional_term_for_var.inj
    {trg : PreTrigger sig} {i1 i2 : Nat} {lt1 : i1 < trg.rule.head.length} {lt2 : i2 < trg.rule.head.length}
    {v1 : sig.V}
    {v1_mem : v1 ∈ trg.rule.existential_vars_for_head_disjunct i1 lt1}
    {v2 : sig.V}
    {v2_mem : v2 ∈ trg.rule.existential_vars_for_head_disjunct i2 lt2} :
    trg.functional_term_for_var i1 lt1 v1 v1_mem = trg.functional_term_for_var i2 lt2 v2 v2_mem -> i1 = i2 ∧ v1 = v2 := by
  unfold functional_term_for_var; grind
@[simp, grind =]
theorem functional_term_for_var.injEq
    {trg : PreTrigger sig} {i1 i2 : Nat} {lt1 : i1 < trg.rule.head.length} {lt2 : i2 < trg.rule.head.length}
    {v1 : sig.V}
    {v1_mem : v1 ∈ trg.rule.existential_vars_for_head_disjunct i1 lt1}
    {v2 : sig.V}
    {v2_mem : v2 ∈ trg.rule.existential_vars_for_head_disjunct i2 lt2} :
    trg.functional_term_for_var i1 lt1 v1 v1_mem = trg.functional_term_for_var i2 lt2 v2 v2_mem ↔ i1 = i2 ∧ v1 = v2 := by
  unfold functional_term_for_var; grind

/-- Applying a trigger to an existential variable, yields exactly the Skolem function term from the shortcup definition `functional_term_for_var`. -/
@[simp, grind =]
theorem apply_to_var_or_const_of_mem_existential_vars (trg : PreTrigger sig) (i : Nat) (lt : i < trg.rule.head.length) :
    ∀ v, (mem : v ∈ trg.rule.existential_vars_for_head_disjunct i lt) ->
    trg.apply_to_var_or_const i lt (.var v) = trg.functional_term_for_var i lt v mem := by
  intro v v_mem; simp [functional_term_for_var, apply_to_var_or_const, skolemize_var_or_const, VarOrConst.skolemize, v_mem, GroundSubstitution.apply_skolem_term, mapped_frontier]

/-- For existential variables, applying the trigger is injective. -/
theorem apply_to_var_or_const_injective_of_mem_existential_vars {v : sig.V}
    (trg : PreTrigger sig) (i : Nat) (lt : i < trg.rule.head.length) (v_mem : v ∈ trg.rule.existential_vars_for_head_disjunct i lt) :
    ∀ voc ∈ trg.rule.head[i].terms, (trg.apply_to_var_or_const i lt (VarOrConst.var v)) = (trg.apply_to_var_or_const i lt voc) -> VarOrConst.var v = voc := by
  intro voc voc_mem apply_eq
  cases voc with
  | const c => simp [v_mem, functional_term_for_var, GroundTerm.func_neq_const] at apply_eq
  | var u =>
    cases Decidable.em (u ∈ trg.rule.existential_vars_for_head_disjunct i lt) with
    | inl u_mem => grind
    | inr u_mem =>
      apply False.elim
      rw [apply_to_var_or_const_of_mem_existential_vars _ _ _ _ v_mem, apply_to_var_or_const_of_not_mem_existential_vars _ _ _ _ u_mem] at apply_eq
      unfold functional_term_for_var at apply_eq
      have u_front : u ∈ trg.rule.frontier := by
        apply trg.rule.mem_frontier_of_mem_head_disjunct_of_not_mem_existential_vars _ _ u_mem
        rw [FunctionFreeConjunction.mem_vars']; exact voc_mem
      have : trg.subs u ∈ trg.mapped_frontier := List.mem_map_of_mem u_front
      rw [← apply_eq] at this
      exact GroundTerm.eq_while_contained_is_impossible this

/-- Applying the trigger to non-frontier variables yields a term that cannot possibly be in the mapped frontier. In other words, terms for existential variables are fresh (although freshness entails more than that). -/
theorem result_term_not_in_frontier_image_of_var_existential (trg : PreTrigger sig) (i : Nat) (lt : i < trg.rule.head.length)
    (v : sig.V) (v_existential : v ∈ trg.rule.existential_vars_for_head_disjunct i lt) :
    ¬ trg.apply_to_var_or_const i lt (VarOrConst.var v) ∈ trg.mapped_frontier := by
  intro contra
  simp only [mapped_frontier, List.mem_map] at contra
  rcases contra with ⟨u, u_in_frontier, u_eq⟩
  rw [apply_to_var_or_const_of_mem_existential_vars _ _ _ _ v_existential] at u_eq
  unfold functional_term_for_var at u_eq
  have : trg.subs u ∈ trg.mapped_frontier := List.mem_map_of_mem u_in_frontier
  rw [u_eq] at this
  exact GroundTerm.eq_while_contained_is_impossible this

/-- We lift the trigger application from `VarOrConst` to `FunctionFreeAtom`. -/
abbrev apply_to_function_free_atom (trg : PreTrigger sig) (i : Nat) (lt : i < trg.rule.head.length) (atom : FunctionFreeAtom sig) : Fact sig :=
  (trg.apply_to_var_or_const i lt).apply_generalized_atom atom

/-- The body does not feature any existential variables. Therefore, we mapped body merely results from applying the trigger's substitution to the body of its rule. -/
@[expose]
def mapped_body (trg : PreTrigger sig) : List (Fact sig) := trg.subs.apply_function_free_conj trg.rule.body

/-- The length of the `mapped_body` is the same as the length of the rule body. -/
@[simp, grind =]
theorem length_mapped_body (trg : PreTrigger sig) : trg.mapped_body.length = trg.rule.body.length := by
  simp [mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]

/-- A term occurs in `mapped_body` if and only if it is a constant in the rule body of if there exists a variable in the rule body that is mapped to the term by the substitution. -/
theorem mem_terms_mapped_body_iff (trg : PreTrigger sig) :
    ∀ t, t ∈ trg.mapped_body.flatMap GeneralizedAtom.terms ↔
    ((∃ c ∈ trg.rule.body.consts, GroundTerm.const c = t) ∨ (∃ v ∈ trg.rule.body.vars, trg.subs v = t)) := by
  intro t
  rw [List.mem_flatMap]
  constructor
  . intro h
    rcases h with ⟨f, f_mem, t_mem⟩
    simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.mem_apply_generalized_atom_list] at f_mem
    rcases f_mem with ⟨a, a_mem, f_eq⟩
    rw [f_eq] at t_mem
    simp only [TermMapping.apply_generalized_atom] at t_mem
    rw [List.mem_map] at t_mem
    rcases t_mem with ⟨voc, voc_mem, t_eq⟩
    cases voc with
    | const c =>
      apply Or.inl
      exists c
      constructor
      . rw [FunctionFreeConjunction.mem_consts]; exists a
      . rw [← t_eq]; simp [GroundSubstitution.apply_var_or_const]
    | var v =>
      apply Or.inr
      exists v
      constructor
      . rw [FunctionFreeConjunction.mem_vars]; exists a
      . rw [← t_eq]; simp [GroundSubstitution.apply_var_or_const]
  . intro h
    cases h with
    | inl h =>
      rcases h with ⟨c, c_mem, t_eq⟩
      rcases FunctionFreeConjunction.mem_consts.mp c_mem with ⟨a, a_mem, c_mem⟩
      exists trg.subs.apply_function_free_atom a
      constructor
      . apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_list; exact a_mem
      . simp only [TermMapping.apply_generalized_atom]
        rw [List.mem_map]
        exists VarOrConst.const c
    | inr h =>
      rcases h with ⟨v, v_mem, t_eq⟩
      rcases FunctionFreeConjunction.mem_vars.mp v_mem with ⟨a, a_mem, v_mem⟩
      exists trg.subs.apply_function_free_atom a
      constructor
      . apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_list; exact a_mem
      . simp only [TermMapping.apply_generalized_atom]
        rw [List.mem_map]
        exists VarOrConst.var v

/-- If a term is in `the mapped_frontier`, then it is also in the `mapped_body`. -/
theorem mem_terms_mapped_body_of_mem_mapped_frontier {trg : PreTrigger sig} :
    ∀ t ∈ trg.mapped_frontier, t ∈ trg.mapped_body.flatMap GeneralizedAtom.terms := by
  simp only [mapped_frontier, List.mem_map]; intro t ⟨v, v_mem, t_mem⟩
  rw [mem_terms_mapped_body_iff]; apply Or.inr; exact ⟨v, trg.rule.frontier_subset_vars_body v_mem, t_mem⟩

/-- The mapped head is the result of the trigger and is simply the application to all head atoms. This result has a list of result facts for each of the head disjuncts. Note again that existential variables are Skolemized before the trigger's substitution is applied but this is hidden within the previously defined functions. -/
@[expose]
def mapped_head (trg : PreTrigger sig) : List (List (Fact sig)) :=
  trg.rule.head.zipIdx.attach.map (fun pair => pair.val.fst.map (trg.apply_to_function_free_atom pair.val.snd (List.snd_lt_of_mem_zipIdx pair.property)))

/-- The length of the `mapped_head` is the same as the length of the rule head. That is, the trigger result indeed has one list of facts for each of the head disjuncts. -/
@[simp, grind =]
theorem length_mapped_head (trg : PreTrigger sig) : trg.mapped_head.length = trg.rule.head.length := by
  unfold mapped_head; simp

/-- Also for each head disjunct, the number of result facts is equal to the number of atoms in the conjunction. -/
theorem length_each_mapped_head (trg : PreTrigger sig) : ∀ (n : Nat), trg.mapped_head[n]?.map (List.length) = trg.rule.head[n]?.map (List.length) := by
  intro n
  unfold mapped_head
  simp only [List.getElem?_map, Option.map_map]
  cases eq : trg.rule.head[n]? <;> grind

/-- For a fixed head index, we can view the trigger merely as a substitution that internally captures the Skolemization of existential variables. In other words, applying this substitution to the specified head disjunct yields exactly the trigger result for the same disjunct. Viewing the trigger as a substitution can be convenient for theorems and proofs. -/
@[expose]
def subs_for_mapped_head (trg : PreTrigger sig) (i : Nat) (lt : i < trg.rule.head.length) : GroundSubstitution sig :=
  fun v => trg.apply_to_var_or_const i lt (.var v)

/-- Applying the `subs_for_mapped_head` is the same as applying the trigger on `VarOrConst`. -/
@[simp, grind =]
theorem apply_subs_for_var_or_const_eq (trg : PreTrigger sig) (i : Nat) (lt : i < trg.rule.head.length) :
    ∀ voc, (trg.subs_for_mapped_head i lt).apply_var_or_const voc = trg.apply_to_var_or_const i lt voc := by
  intro voc
  unfold GroundSubstitution.apply_var_or_const
  unfold subs_for_mapped_head
  cases voc <;> simp

/-- Applying the `subs_for_mapped_head` is the same as applying the trigger on `FunctionFreeAtom`. -/
@[simp, grind =]
theorem apply_subs_for_atom_eq (trg : PreTrigger sig) (i : Nat) (lt : i < trg.rule.head.length) :
    ∀ a, (trg.subs_for_mapped_head i lt).apply_function_free_atom a = trg.apply_to_function_free_atom i lt a := by
  intro a
  unfold GroundSubstitution.apply_function_free_atom
  unfold apply_to_function_free_atom
  apply TermMapping.apply_generalized_atom_congr_left
  intros
  apply apply_subs_for_var_or_const_eq

/-- Applying the `subs_for_mapped_head` on the head is exactly the trigger result (`mapped_head`). -/
@[simp, grind =]
theorem apply_subs_for_mapped_head_eq (trg : PreTrigger sig) (i : Nat) (lt : i < trg.rule.head.length) :
    (trg.subs_for_mapped_head i lt).apply_function_free_conj trg.rule.head[i] = trg.mapped_head[i]'(by grind) := by
  unfold mapped_head
  unfold GroundSubstitution.apply_function_free_conj
  unfold TermMapping.apply_generalized_atom_list
  simp only [List.getElem_map, List.getElem_attach, List.getElem_zipIdx, List.map_inj_left, Nat.zero_add]
  intros
  apply apply_subs_for_atom_eq trg i lt

/-- The list of fresh terms are the function terms introduced for the existential variables. -/
@[expose]
def fresh_terms_for_head_disjunct (trg : PreTrigger sig) (i : Nat) (lt : i < trg.rule.head.length) : List (GroundTerm sig) :=
  (trg.rule.existential_vars_for_head_disjunct i lt).attach.map (fun v => trg.functional_term_for_var i lt v.val v.property)

/-- The functional term produces by an existential variable is one of the fresh terms. -/
theorem mem_fresh_terms_of_functional_for_exis_var {trg : PreTrigger sig} {i : Nat} {lt : i < trg.rule.head.length} {v : sig.V}
    (v_mem : v ∈ trg.rule.existential_vars_for_head_disjunct i lt) : trg.functional_term_for_var i lt v v_mem ∈ trg.fresh_terms_for_head_disjunct i lt := by
  unfold fresh_terms_for_head_disjunct; rw [List.map_attach_eq_pmap]; apply List.mem_pmap_of_mem; exact v_mem

/-- This theorem unfolds some of the internal definitions of `fresh_terms_for_head_disjunct`. -/
theorem mem_fresh_terms {trg : PreTrigger sig} {i : Nat} {lt : i < trg.rule.head.length} :
    ∀ t ∈ trg.fresh_terms_for_head_disjunct i lt, ∃ (v : sig.V) (v_mem : v ∈ trg.rule.existential_vars_for_head_disjunct i lt),
    t = GroundTerm.func { rule := trg.rule, headIdx := i, headIdx_lt := lt, v, v_mem } trg.mapped_frontier (by rw [length_mapped_frontier]; rfl) := by
  intro t t_mem
  simp only [fresh_terms_for_head_disjunct, List.mem_map, functional_term_for_var, List.mem_attach] at t_mem
  rcases t_mem with ⟨⟨v, v_mem⟩, _, t_mem⟩
  exists v, v_mem; exact Eq.symm t_mem

/-- Fresh terms are always functional. -/
theorem term_functional_of_mem_fresh_terms {trg : PreTrigger sig} {i : Nat} {lt : i < trg.rule.head.length} :
    ∀ t ∈ trg.fresh_terms_for_head_disjunct i lt, ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok := by
  intro t t_mem
  rcases mem_fresh_terms t t_mem with ⟨_, _, t_mem⟩
  exact ⟨_, _, _, t_mem⟩

/-- Constants can never be fresh. -/
theorem constant_not_mem_fresh_terms_for_head_disjunct {trg : PreTrigger sig} {i : Nat} {lt : i < trg.rule.head.length} :
    ∀ {c : sig.C}, ¬ .const c ∈ trg.fresh_terms_for_head_disjunct i lt := by
  intro c c_mem
  rcases term_functional_of_mem_fresh_terms _ c_mem with ⟨func, ts, arity_ok, eq⟩
  exact GroundTerm.func_neq_const (Eq.symm eq)

/-- Mappings of frontier variables can never be fresh. -/
theorem frontier_term_not_mem_fresh_terms_for_head_disjunct {trg : PreTrigger sig} {i : Nat} {lt : i < trg.rule.head.length} :
    ∀ {t}, t ∈ trg.mapped_frontier -> ¬ t ∈ trg.fresh_terms_for_head_disjunct i lt := by
  intro t t_frontier t_fresh
  simp only [fresh_terms_for_head_disjunct, List.mem_map, List.mem_attach] at t_fresh
  rcases t_fresh with ⟨⟨v, v_mem⟩, _, t_fresh⟩
  apply trg.result_term_not_in_frontier_image_of_var_existential i lt v v_mem
  rw [apply_to_var_or_const_of_mem_existential_vars _ _ _ _ v_mem]
  rw [t_fresh]
  exact t_frontier

/-- For a given fresh term, we can obtain the existential variable that introduced it. -/
def existential_var_for_fresh_term (trg : PreTrigger sig) (i : Nat) (lt : i < trg.rule.head.length) (t : GroundTerm sig) (t_mem : t ∈ trg.fresh_terms_for_head_disjunct i lt) : sig.V :=
  ((trg.rule.existential_vars_for_head_disjunct i lt).find? (fun v => (t.functionSymbol (term_functional_of_mem_fresh_terms _ t_mem)).v = v)).get (by
    simp only [List.find?_isSome, decide_eq_true_eq]
    simp only [fresh_terms_for_head_disjunct, List.mem_map, List.mem_attach] at t_mem
    rcases t_mem with ⟨⟨v, v_mem⟩, _, t_mem⟩
    exists v; constructor; exact v_mem
    simp only [← t_mem, functional_term_for_var, GroundTerm.functionSymbol_func])

/-- Indeed getting the existential variable for a functional term introduced for a variable yields exactly this variable (as expected). -/
@[simp, grind =]
theorem existential_var_for_fresh_term_after_functional_term_for_var
    {trg : PreTrigger sig}
    {i : Nat}
    (lt : i < trg.rule.head.length)
    {v : sig.V}
    (v_mem : v ∈ trg.rule.existential_vars_for_head_disjunct i lt) :
    trg.existential_var_for_fresh_term i lt (trg.functional_term_for_var i lt v v_mem) (mem_fresh_terms_of_functional_for_exis_var v_mem) = v := by
  simp only [existential_var_for_fresh_term]
  apply Option.get_of_eq_some
  simp only [List.find?_eq_some_iff_getElem, decide_eq_true_eq]
  constructor
  . simp only [functional_term_for_var, GroundTerm.functionSymbol_func]
  let j := (trg.rule.existential_vars_for_head_disjunct i lt).idxOf v
  exists j, (List.idxOf_lt_length_of_mem v_mem)
  constructor
  . rw [List.getElem_idxOf_of_mem v_mem]
  . intro k k_lt
    simp only [j, List.idxOf] at k_lt
    rw [List.lt_findIdx_iff] at k_lt
    rcases k_lt with ⟨_, k_lt⟩
    specialize k_lt k (by simp)
    rw [beq_eq_false_iff_ne] at k_lt
    rw [not_decide_eq_true]
    simp only [functional_term_for_var, GroundTerm.functionSymbol_func]
    intro contra; apply k_lt; rw [contra]

/-- For a fact in the trigger result, we can obtain the head atom that yields the fact. -/
def atom_for_result_fact (trg : PreTrigger sig) {f : Fact sig} (i : Nat) (lt : i < trg.rule.head.length)
    (f_mem : f ∈ trg.mapped_head[i]'(by grind)) : FunctionFreeAtom sig :=
  let j := (trg.mapped_head[i]'(by grind)).idxOf f
  trg.rule.head[i][j]'(by
    have := trg.length_each_mapped_head i
    rw [List.getElem?_eq_getElem lt] at this
    rw [List.getElem?_eq_getElem (by grind)] at this
    simp only [Option.map_some, Option.some_inj] at this
    rw [← this]
    apply List.idxOf_lt_length_of_mem
    exact f_mem
  )

/-- Applying the trigger on the atom from `atom_for_result_fact` indeed yields the correct fact. -/
@[simp, grind =]
theorem apply_on_atom_for_result_fact_is_fact (trg : PreTrigger sig) {f : Fact sig} (i : Nat) (lt : i < trg.rule.head.length)
    (f_mem : f ∈ trg.mapped_head[i]'(by grind)) :
    trg.apply_to_function_free_atom i lt (trg.atom_for_result_fact i lt f_mem) = f := by
  have lt' : i < trg.mapped_head.length := by rw [length_mapped_head]; exact lt
  have : f = trg.mapped_head[i][trg.mapped_head[i].idxOf f]'(List.idxOf_lt_length_of_mem f_mem) := by rw [List.getElem_idxOf_of_mem]; exact f_mem
  conv => right; rw [this]
  unfold atom_for_result_fact
  unfold mapped_head
  simp

/-- The atom from `atom_for_result_fact` occurs in the correct rule head disjunct. -/
theorem atom_for_result_fact_mem_head {trg : PreTrigger sig} {f : Fact sig} {i : Nat} {lt : i < trg.rule.head.length}
    {f_mem : f ∈ trg.mapped_head[i]'(by grind)} : trg.atom_for_result_fact i lt f_mem ∈ trg.rule.head[i] := by
  simp [atom_for_result_fact]

/-- For any term in the result (not just fresh ones), we can obtain the corresponding `VarOrConst` from the rule. -/
def var_or_const_for_result_term (trg : PreTrigger sig) {f : Fact sig} {t : GroundTerm sig} (i : Nat) (lt : i < trg.rule.head.length)
    (f_mem : f ∈ trg.mapped_head[i]'(by grind)) (t_mem : t ∈ f.terms) : VarOrConst sig :=
  let k := f.terms.idxOf t
  let atom := trg.atom_for_result_fact i lt f_mem
  have lt' : k < atom.terms.length := by
    have isLt := List.idxOf_lt_length_of_mem t_mem
    have := trg.apply_on_atom_for_result_fact_is_fact i lt f_mem
    conv at isLt => right; rw [← this]
    rw [TermMapping.length_terms_apply_generalized_atom] at isLt
    exact isLt
  atom.terms[k]

/-- Applying the trigger on the `VarOrConst` from `var_or_const_for_result_term` indeed yields the correct term. -/
@[simp, grind =]
theorem apply_on_var_or_const_for_result_term_is_term (trg : PreTrigger sig) {f : Fact sig} {t : GroundTerm sig}
    (i : Nat) (lt : i < trg.rule.head.length) (f_mem : f ∈ trg.mapped_head[i]'(by grind)) (t_mem : t ∈ f.terms) :
    trg.apply_to_var_or_const i lt (trg.var_or_const_for_result_term i lt f_mem t_mem) = t := by
  have t_eq : t = f.terms[f.terms.idxOf t]'(List.idxOf_lt_length_of_mem t_mem) := by rw [List.getElem_idxOf_of_mem]; exact t_mem
  have := trg.apply_on_atom_for_result_fact_is_fact i lt f_mem
  have : (trg.apply_to_function_free_atom i lt (trg.atom_for_result_fact i lt f_mem)).terms = f.terms := by rw [this]
  conv at t_eq => right; simp only [← this]
  conv at t_eq => right; left; simp only [this]
  conv => right; rw [t_eq]
  unfold apply_to_function_free_atom
  unfold TermMapping.apply_generalized_atom
  rw [List.getElem_map]
  rfl

/-- For a term in a result fact, `var_or_const_for_result_term` returns a `VarOrConst` that is in `atom_for_result_fact`. -/
theorem var_or_const_for_result_term_mem_atom_for_result_fact {trg : PreTrigger sig} {f : Fact sig} {t : GroundTerm sig}
    {i : Nat} {lt : i < trg.rule.head.length} {f_mem : f ∈ trg.mapped_head[i]'(by grind)} {t_mem : t ∈ f.terms} :
    trg.var_or_const_for_result_term i lt f_mem t_mem ∈ (trg.atom_for_result_fact i lt f_mem).terms := by
  simp [var_or_const_for_result_term]

/-- For a term in a result fact, `var_or_const_for_result_term` occurs in the correct head disjunct. -/
theorem var_or_const_for_result_term_mem_terms_head {trg : PreTrigger sig} {f : Fact sig} {t : GroundTerm sig}
    {i : Nat} {lt : i < trg.rule.head.length} {f_mem : f ∈ trg.mapped_head[i]'(by grind)} {t_mem : t ∈ f.terms} :
    trg.var_or_const_for_result_term i lt f_mem t_mem ∈ trg.rule.head[i].terms := by
  unfold FunctionFreeConjunction.terms; apply List.mem_flatMap_of_mem; apply atom_for_result_fact_mem_head; exact f_mem; apply var_or_const_for_result_term_mem_atom_for_result_fact

/-- A term occurs in the trigger result for a given head index if and only if one of the following three cases holds. 1. The term is a constant in the head. 2. The term results from mapping a frontier variable in the head. 3. The term is a fresh term of the head. -/
theorem mem_terms_mapped_head_iff (trg : PreTrigger sig) (i : Nat) (lt : i < trg.rule.head.length) :
    ∀ t, t ∈ (trg.mapped_head[i]'(by grind)).flatMap GeneralizedAtom.terms ↔ (∃ c, c ∈ trg.rule.head[i].consts ∧ GroundTerm.const c = t) ∨ t ∈ (trg.rule.frontier_for_head i lt).map trg.subs ∨ t ∈ trg.fresh_terms_for_head_disjunct i lt := by
  intro t
  rw [List.mem_flatMap, List.mem_map]
  constructor
  . rintro ⟨f, f_mem, t_mem⟩
    cases eq : trg.var_or_const_for_result_term i lt f_mem t_mem with
    | const c =>
      apply Or.inl
      exists c
      constructor
      . rw [FunctionFreeConjunction.mem_consts]
        exists trg.atom_for_result_fact i lt f_mem
        constructor
        . apply atom_for_result_fact_mem_head
        . rw [← eq]
          apply var_or_const_for_result_term_mem_atom_for_result_fact
      . rw [← trg.apply_on_var_or_const_for_result_term_is_term i lt f_mem t_mem, eq]; rfl
    | var v =>
      apply Or.inr
      cases Decidable.em (v ∈ trg.rule.existential_vars_for_head_disjunct i lt) with
      | inl v_exis =>
        apply Or.inr
        rw [← trg.apply_on_var_or_const_for_result_term_is_term i lt f_mem t_mem, eq]
        rw [trg.apply_to_var_or_const_of_mem_existential_vars _ _ _ v_exis]
        apply trg.mem_fresh_terms_of_functional_for_exis_var
      | inr v_not_exis =>
        apply Or.inl
        rw [← trg.apply_on_var_or_const_for_result_term_is_term i lt f_mem t_mem, eq]
        exists v; constructor
        . have v_mem_head : v ∈ trg.rule.head[i].vars := by
            rw [FunctionFreeConjunction.mem_vars', ← eq]
            apply var_or_const_for_result_term_mem_terms_head
          apply trg.rule.mem_frontier_for_head_of_mem_frontier_of_mem_head_terms _ _ (by rw [← FunctionFreeConjunction.mem_vars']; exact v_mem_head)
          exact trg.rule.mem_frontier_of_mem_head_disjunct_of_not_mem_existential_vars _ v_mem_head v_not_exis
        . rw [apply_to_var_or_const_of_not_mem_existential_vars _ _ _ _ v_not_exis]
  . intro h
    cases h with
    | inl h =>
      rcases h with ⟨c, c_mem, t_eq⟩
      rcases FunctionFreeConjunction.mem_consts.mp c_mem with ⟨a, a_mem, c_mem⟩
      exists trg.apply_to_function_free_atom i lt a
      constructor
      . unfold mapped_head; grind
      . simp only [apply_to_function_free_atom, TermMapping.apply_generalized_atom]
        rw [List.mem_map]
        exists .const c
    | inr h =>
    cases h with
    | inl h =>
      rcases h with ⟨v, v_mem, t_eq⟩
      rcases FunctionFreeConjunction.mem_vars.mp (trg.rule.frontier_for_head_subset_vars_head _ v_mem) with ⟨a, a_mem, v_mem'⟩
      exists trg.apply_to_function_free_atom i lt a
      constructor
      . unfold mapped_head; grind
      . simp only [apply_to_function_free_atom, TermMapping.apply_generalized_atom]
        rw [List.mem_map]
        exists .var v
        constructor
        . exact v_mem'
        . rw [apply_to_var_or_const_frontier_var _ _ _ _ (by apply Rule.mem_frontier_iff_mem_frontier_for_head.mpr; exists i, lt)]; exact t_eq
    | inr h =>
      unfold fresh_terms_for_head_disjunct at h
      simp only [List.mem_map, List.mem_attach] at h
      rcases h with ⟨⟨v, v_mem⟩, _, t_eq⟩
      have v_mem_head := trg.rule.mem_head_vars_of_mem_existential_vars_for_head_disjunct _ v_mem
      rw [FunctionFreeConjunction.mem_vars] at v_mem_head; rcases v_mem_head with ⟨a, a_mem, v_mem_a⟩
      exists trg.apply_to_function_free_atom i lt a
      constructor
      . unfold mapped_head; grind
      . simp only [apply_to_function_free_atom, TermMapping.apply_generalized_atom]
        rw [List.mem_map]
        exists .var v
        constructor
        . exact v_mem_a
        . rw [apply_to_var_or_const_of_mem_existential_vars _ _ _ _ v_mem]; exact t_eq

/-- The constants in the trigger result are a subset of the constants from the mapped frontier terms and the constants that occur directly in the rule head. -/
theorem mapped_head_constants_subset (trg : PreTrigger sig) (i : Nat) (lt : i < trg.rule.head.length) :
    FactSet.constants (trg.mapped_head[i]'(by grind)).toSet ⊆ ((trg.mapped_frontier.flatMap GroundTerm.constants) ++ trg.rule.head[i].consts).toSet := by
  intro c c_mem
  rw [List.mem_toSet, List.mem_append]
  rw [FactSet.mem_constants_toSet, List.mem_flatMap] at c_mem
  rcases c_mem with ⟨f, f_mem, c_mem⟩
  simp only [Fact.constants, List.mem_flatMap] at c_mem
  rcases c_mem with ⟨t, t_mem, c_mem⟩
  have t_mem : t ∈ (trg.mapped_head[i]'(by grind)).flatMap GeneralizedAtom.terms := by rw [List.mem_flatMap]; exists f
  rw [mem_terms_mapped_head_iff] at t_mem
  cases t_mem with
  | inl t_mem =>
    apply Or.inr
    rcases t_mem with ⟨d, d_mem, d_eq⟩
    rw [← d_eq, GroundTerm.constants_const, List.mem_singleton] at c_mem
    rw [c_mem]
    exact d_mem
  | inr t_mem =>
  cases t_mem with
  | inl t_mem =>
    apply Or.inl
    rw [List.mem_map] at t_mem; rcases t_mem with ⟨v, v_mem, t_mem⟩
    rw [List.mem_flatMap]; exists t; constructor
    . have v_mem : v ∈ trg.rule.frontier := by
        apply Rule.mem_frontier_iff_mem_frontier_for_head.mpr; exact ⟨_, ⟨_, v_mem⟩⟩
      rw [← t_mem]; apply List.mem_map_of_mem; exact v_mem
    . exact c_mem
  | inr t_mem =>
    apply Or.inl
    simp only [fresh_terms_for_head_disjunct, List.mem_map] at t_mem; rcases t_mem with ⟨v, v_mem, t_mem⟩
    rw [← t_mem] at c_mem
    simp only [functional_term_for_var, GroundTerm.constants_func, List.mem_flatMap] at c_mem
    rcases c_mem with ⟨t, t_mem, c_mem⟩
    simp only [List.mem_flatMap]; exists t

/-- The trigger is loaded for a `FactSet` if its mapped body occurs in the fact set. -/
@[expose]
def loaded (trg : PreTrigger sig) (fs : FactSet sig) : Prop :=
  trg.mapped_body.toSet ⊆ fs

/-- Applying a `GroundTermMapping` that is the id on constants after the trigger substitution and on the fact set preserves loadedness. -/
theorem term_mapping_preserves_loadedness (trg : PreTrigger sig) (fs : FactSet sig) (h : GroundTermMapping sig) (h_id : h.isIdOnConstants) :
    trg.loaded fs -> { rule := trg.rule, subs := h ∘ trg.subs : PreTrigger sig }.loaded (h.applyFactSet fs) := by
  unfold loaded
  unfold mapped_body
  intro loaded
  intro f f_mem
  rw [List.mem_toSet] at f_mem
  simp only [GroundSubstitution.apply_function_free_conj, TermMapping.mem_apply_generalized_atom_list] at f_mem
  rcases f_mem with ⟨a, a_mem, f_mem⟩
  rw [← GroundSubstitution.apply_function_free_atom.eq_def, GroundSubstitution.apply_function_free_atom_compose_of_isIdOnConstants _ _ h_id] at f_mem
  rw [f_mem]
  apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
  apply loaded
  unfold GroundSubstitution.apply_function_free_conj
  rw [List.mem_toSet, TermMapping.apply_generalized_atom_list.eq_def, List.mem_map]
  exists a

/-- A trigger head is satisfied for a `FactSet` if there exists a substitution that agrees with the trigger substitution on all frontier variable such that the mapping of the head occurs in the fact set. This corresponds to FOL semantics. It is **important** to note here that a trigger being satisfied in this sense does not necessarily mean that it is obsolete! Obsolescence might be defined almost arbitrarily and for example in the Skolem chase, a satisfied trigger is often not obsolete. However, for the restricted (aka. standard) chase, obsolescence is defined via satisfaction. -/
@[expose]
def satisfied_for_disj (trg : PreTrigger sig) (fs : FactSet sig) (i : Nat) (lt : i < trg.rule.head.length) : Prop :=
  ∃ (s : GroundSubstitution sig),
    (∀ v, v ∈ (Rule.frontier trg.rule) → s v = trg.subs v) ∧
    ((s.apply_function_free_conj (trg.rule.head[i])).toSet ⊆ fs)

/-- If the exact trigger result is contained in the fact set, then the trigger is also satisfied. -/
theorem satisfied_for_disj_of_mapped_head_contained (trg : PreTrigger sig) (fs : FactSet sig)
    (i : Nat) (lt : i < trg.rule.head.length) :
    (trg.mapped_head[i]'(by grind)).toSet ⊆ fs ->
    trg.satisfied_for_disj fs i lt := by
  intro h
  exists trg.subs_for_mapped_head i lt
  constructor
  . intro v v_mem; unfold subs_for_mapped_head; rw [trg.apply_to_var_or_const_frontier_var _ _ _ v_mem]
  . rw [trg.apply_subs_for_mapped_head_eq i lt]; exact h

/-- The trigger is satisfied if it is satisfied for some head. Note that this checks out with FOL semantics since the heads are part of a big disjunction. -/
@[expose]
def satisfied (trg : PreTrigger sig) (fs : FactSet sig) : Prop :=
  ∃ i lt, trg.satisfied_for_disj fs i lt

/-- If a trigger is satisfied, then it is also satisfied on all supersets. -/
theorem satisfied_of_satisfied_subset {trg : PreTrigger sig} {fs fs2 : FactSet sig} (sub : fs ⊆ fs2) :
    trg.satisfied fs -> trg.satisfied fs2 := by
  simp [PreTrigger.satisfied, PreTrigger.satisfied_for_disj]
  intro i lt subs frontier_same_under_subs applied_head_sub_fs
  exists i, lt, subs
  constructor
  . apply frontier_same_under_subs
  . apply Set.subset_trans
    . exact applied_head_sub_fs
    . exact sub

/-- We consider two trigger to be equivalent if they share the same rule and their substitutions agree on the frontier variables. This entails that they have the same result. -/
@[expose]
def equiv (trg1 trg2 : PreTrigger sig) : Prop :=
  trg1.rule = trg2.rule ∧ ∀ v, v ∈ trg1.rule.frontier -> trg1.subs v = trg2.subs v

/-- Trigger equivalence is reflexive. -/
@[grind <-]
theorem equiv_refl {trg : PreTrigger sig} : trg.equiv trg := by simp [equiv]

/-- Trigger equivalence is symmetric. -/
@[grind ->]
theorem equiv_symm {trg1 trg2 : PreTrigger sig} : trg1.equiv trg2 -> trg2.equiv trg1 := by unfold equiv; grind

/-- Trigger equivalence is transitive. -/
@[grind ->]
theorem equiv_trans {trg1 trg2 trg3 : PreTrigger sig} : trg1.equiv trg2 -> trg2.equiv trg3 -> trg1.equiv trg3 := by unfold equiv; grind

/-- Equivalent triggers have the same `mapped_frontier`. -/
theorem mapped_frontier_eq_of_equiv {trg1 trg2 : PreTrigger sig} (equiv : trg1.equiv trg2) : trg1.mapped_frontier = trg2.mapped_frontier := by
  unfold mapped_frontier
  rw [← equiv.left, List.map_inj_left]
  exact equiv.right

/-- Two triggers with same rule and same mapped_frontier are equivalent. -/
theorem equiv_of_rule_eq_of_mapped_frontier_equiv {trg1 trg2 : PreTrigger sig}
    (rule_eq : trg1.rule = trg2.rule) (mapped_front_eq : trg1.mapped_frontier = trg2.mapped_frontier) : trg1.equiv trg2 := by
  constructor; exact rule_eq
  unfold mapped_frontier at mapped_front_eq; rw [← rule_eq, List.map_inj_left] at mapped_front_eq
  exact mapped_front_eq

/-- We consider two trigger to be strongly equivalent if they share the same rule and their substitutions agree not only on the frontier variables but on all body variables. -/
@[expose]
def strong_equiv (trg1 trg2 : PreTrigger sig) : Prop :=
  trg1.rule = trg2.rule ∧ ∀ v, v ∈ trg1.rule.body.vars -> trg1.subs v = trg2.subs v

/-- Strong equivalence is reflexive. -/
@[grind <-]
theorem strong_equiv_refl {trg : PreTrigger sig} : trg.strong_equiv trg := by simp [strong_equiv]

/-- Strong equivalence is symmetric. -/
@[grind ->]
theorem strong_equiv_symm {trg1 trg2 : PreTrigger sig} : trg1.strong_equiv trg2 -> trg2.strong_equiv trg1 := by unfold strong_equiv; grind

/-- strong equivalence is transitive. -/
@[grind ->]
theorem strong_equiv_trans {trg1 trg2 trg3 : PreTrigger sig} : trg1.strong_equiv trg2 -> trg2.strong_equiv trg3 -> trg1.strong_equiv trg3 := by unfold strong_equiv; grind

/-- Strong equivalence implies equivalence. -/
@[grind ->]
theorem equiv_of_strong_equiv {trg1 trg2 : PreTrigger sig} : trg1.strong_equiv trg2 -> trg1.equiv trg2 := by
  intro ⟨r_eq, body_mapping_eq⟩
  constructor
  . exact r_eq
  . intro v v_mem
    apply body_mapping_eq
    exact trg1.rule.frontier_subset_vars_body v_mem

/-- Applying the substitutions of strongly equivalent triggers to a body atom yields the same result. (This is not necessarily true if the triggers are only equivalent.)-/
theorem subs_apply_function_free_atom_eq_of_strong_equiv {trg1 trg2 : PreTrigger sig} :
    trg1.strong_equiv trg2 -> ∀ a, a ∈ trg1.rule.body -> trg1.subs.apply_function_free_atom a = trg2.subs.apply_function_free_atom a := by
  intro equiv a a_mem
  apply TermMapping.apply_generalized_atom_congr_left
  intro voc voc_mem
  cases voc with
  | const c => simp only [GroundSubstitution.apply_var_or_const]
  | var v =>
    simp only [GroundSubstitution.apply_var_or_const]
    apply equiv.right
    rw [FunctionFreeConjunction.mem_vars]
    exists a

/-- Strongly equivalent triggers have the same `mapped_body`. Again, this is not necessarily true for triggers that are only equivalent. -/
@[grind ->]
theorem mapped_body_eq_of_strong_equiv {trg1 trg2 : PreTrigger sig} : trg1.strong_equiv trg2 -> trg1.mapped_body = trg2.mapped_body := by
  intro equiv
  unfold mapped_body
  rw [equiv.left]
  unfold GroundSubstitution.apply_function_free_conj
  rw [TermMapping.apply_generalized_atom_list.eq_def, TermMapping.apply_generalized_atom_list.eq_def, List.map_inj_left]
  intro a a_mem
  apply subs_apply_function_free_atom_eq_of_strong_equiv
  . exact equiv
  . rw [equiv.left]; exact a_mem

/-- Applying two equivalent triggers to the same (head) atom yields the same result. -/
theorem apply_to_function_free_atom_eq_of_equiv {trg1 trg2 : PreTrigger sig} (equiv : trg1.equiv trg2) :
    ∀ (i : Nat), (lt : i < trg1.rule.head.length) ->
    ∀ a ∈ trg1.rule.head[i], trg1.apply_to_function_free_atom i lt a = trg2.apply_to_function_free_atom i (by rw [← equiv.left]; exact lt) a := by
  intro i lt a a_mem
  apply TermMapping.apply_generalized_atom_congr_left
  intro voc voc_mem
  cases voc with
  | const c => simp
  | var v =>
    cases Decidable.em (v ∈ trg1.rule.existential_vars_for_head_disjunct i lt) with
    | inl v_exis =>
      rw [trg1.apply_to_var_or_const_of_mem_existential_vars _ _ _ v_exis]
      simp only [equiv.left] at v_exis
      rw [trg2.apply_to_var_or_const_of_mem_existential_vars _ _ _ v_exis]
      unfold PreTrigger.functional_term_for_var
      simp only [← equiv.left, mapped_frontier_eq_of_equiv equiv]
    | inr v_not_exis =>
      have v_front : v ∈ trg2.rule.frontier := by
        rw [← equiv.left]
        apply trg1.rule.mem_frontier_of_mem_head_disjunct_of_not_mem_existential_vars _ _ v_not_exis
        rw [FunctionFreeConjunction.mem_vars]; exists a
      rw [trg2.apply_to_var_or_const_frontier_var _ _ _ v_front]
      simp only [← equiv.left] at v_front
      rw [trg1.apply_to_var_or_const_frontier_var _ _ _ v_front]
      apply equiv.right
      exact v_front

/-- As intended, equivalent triggers have the same result. -/
@[grind ->]
theorem result_eq_of_equiv {trg1 trg2 : PreTrigger sig} : trg1.equiv trg2 -> trg1.mapped_head = trg2.mapped_head := by
  intro equiv
  unfold mapped_head
  simp only [List.map_attach_eq_pmap]
  simp only [equiv.left]
  apply List.pmap_congr_left
  intro pair _ pair_mem1 pair_mem2
  rw [List.map_inj_left]
  intro a a_mem
  apply apply_to_function_free_atom_eq_of_equiv
  . exact equiv
  . rw [← (List.mem_zipIdx' pair_mem1).right]; exact a_mem

/-- Equivalent triggers are satisfied on the same fact sets. -/
theorem satisfied_preserved_of_equiv {trg1 trg2 : PreTrigger sig} : trg1.equiv trg2 -> ∀ {fs}, trg1.satisfied fs ↔ trg2.satisfied fs := by
  intro equiv fs
  constructor
  . intro h
    rcases h with ⟨i, lt, s, front, subset⟩
    exists i, by rw [← equiv.left]; exact lt, s
    constructor
    . intro v v_mem
      rw [← equiv.right]
      . apply front; rw [equiv.left]; exact v_mem
      . rw [equiv.left]; exact v_mem
    . simp only [← equiv.left]; exact subset
  . intro h
    rcases h with ⟨i, lt, s, front, subset⟩
    exists i, by rw [equiv.left]; exact lt, s
    constructor
    . intro v v_mem
      rw [equiv.right]
      . apply front; rw [← equiv.left]; exact v_mem
      . exact v_mem
    . simp only [equiv.left]; exact subset

/-- If a ground term is fresh in two `PreTrigger`s for two head indices, then actually these two `PreTrigger`s (and indices) need to be equivalent (the same)! Why is this the case? Fresh terms are always Skolem function terms. Therefore they contain a rule, which needs to be the same for both triggers. The head indices are also part of the functional term so a similar argument can be made to show that these need to be equal. To see why the triggers also need to agree on their frontier mapping, we only need to remind ourselves that the Skolem term contains all the mapped frontier terms as arguments. -/
theorem equiv_of_term_mem_fresh_terms_for_head_disjunct
    {trg1 trg2 : PreTrigger sig}
    {i1 i2 : Nat}
    {lt1 : i1 < trg1.rule.head.length}
    {lt2 : i2 < trg2.rule.head.length}
    {t : GroundTerm sig} :
    (t ∈ trg1.fresh_terms_for_head_disjunct i1 lt1) ->
      (t ∈ trg2.fresh_terms_for_head_disjunct i2 lt2) ->
        trg1.equiv trg2 ∧ i1 = i2 := by
  unfold PreTrigger.fresh_terms_for_head_disjunct PreTrigger.functional_term_for_var
  simp only [List.mem_map]
  rintro ⟨v1, v1_mem, t_eq⟩ ⟨v2, v2_mem, t_eq2⟩
  rw [← t_eq2] at t_eq
  rw [GroundTerm.func.injEq, SkolemFS.mk.injEq] at t_eq
  have rules_eq : trg1.rule = trg2.rule := t_eq.left.left
  constructor
  . exact equiv_of_rule_eq_of_mapped_frontier_equiv rules_eq t_eq.right
  . exact t_eq.left.right.left

end PreTrigger

