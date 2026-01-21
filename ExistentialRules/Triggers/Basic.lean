import ExistentialRules.AtomsAndFacts.Basic
import ExistentialRules.AtomsAndFacts.SubstitutionsAndHomomorphisms

structure PreTrigger (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
  rule : Rule sig
  subs : GroundSubstitution sig

namespace PreTrigger

  variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

  def skolemize_var_or_const (trg : PreTrigger sig) (disjunctIndex : Nat) (var_or_const : VarOrConst sig) : SkolemTerm sig :=
    var_or_const.skolemize trg.rule.id disjunctIndex trg.rule.frontier

  def apply_to_var_or_const (trg : PreTrigger sig) (disjunctIndex : Nat) : TermMapping (VarOrConst sig) (GroundTerm sig) :=
    (trg.subs.apply_skolem_term ∘ (trg.skolemize_var_or_const disjunctIndex))

  theorem apply_to_var_or_const_for_const (trg : PreTrigger sig) (i : Nat) :
      ∀ c, trg.apply_to_var_or_const i (.const c) = GroundTerm.const c := by
    simp [apply_to_var_or_const, skolemize_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term]

  theorem apply_to_var_or_const_frontier_var (trg : PreTrigger sig) (i : Nat) :
      ∀ v, v ∈ trg.rule.frontier -> trg.apply_to_var_or_const i (.var v) = trg.subs v := by
    intro v v_front
    simp [apply_to_var_or_const, skolemize_var_or_const, VarOrConst.skolemize, v_front, GroundSubstitution.apply_skolem_term]

  def functional_term_for_var (trg : PreTrigger sig) (i : Nat) (v : sig.V) : GroundTerm sig :=
    GroundTerm.func
      { ruleId := trg.rule.id, disjunctIndex := i, var := v, arity := trg.rule.frontier.length }
      (trg.rule.frontier.map trg.subs)
      (by rw [List.length_map])

  theorem apply_to_var_or_const_non_frontier_var (trg : PreTrigger sig) (i : Nat) :
      ∀ v, ¬ v ∈ trg.rule.frontier -> trg.apply_to_var_or_const i (.var v) =
        trg.functional_term_for_var i v := by
    intro v v_front
    simp [functional_term_for_var, apply_to_var_or_const, skolemize_var_or_const, VarOrConst.skolemize, v_front, GroundSubstitution.apply_skolem_term]

  theorem apply_to_var_or_const_injective_of_not_in_frontier {v : sig.V}
      (trg : PreTrigger sig) (i : Fin trg.rule.head.length) (v_not_in_frontier : ¬ v ∈ trg.rule.frontier) :
      ∀ voc, (trg.apply_to_var_or_const i (VarOrConst.var v)) = (trg.apply_to_var_or_const i voc) ->
      VarOrConst.var v = voc := by
    intro voc apply_eq
    unfold apply_to_var_or_const at apply_eq
    simp only [Function.comp_apply] at apply_eq

    cases voc with
    | const c =>
      simp [GroundSubstitution.apply_skolem_term, skolemize_var_or_const, VarOrConst.skolemize, v_not_in_frontier, GroundTerm.func, GroundTerm.const] at apply_eq
    | var u =>
      cases Decidable.em (u ∈ trg.rule.frontier) with
      | inl u_front =>
        simp [GroundSubstitution.apply_skolem_term, skolemize_var_or_const, VarOrConst.skolemize, v_not_in_frontier, u_front, GroundTerm.func] at apply_eq
        rw [Subtype.mk.injEq] at apply_eq
        apply False.elim
        apply FiniteTree.tree_eq_while_contained_is_impossible _ _ _ apply_eq
        unfold List.unattach
        rw [List.map_map, List.mem_map]
        exists u
      | inr u_front =>
        apply VarOrConst.skolemize_injective trg.rule.id i trg.rule.frontier
        apply trg.subs.apply_skolem_term_injective_on_func_of_frontier_eq
        . unfold VarOrConst.skolemize
          simp only [v_not_in_frontier, ↓reduceIte]
          rfl
        . unfold VarOrConst.skolemize
          simp only [u_front, ↓reduceIte]
          rfl
        . exact apply_eq

  theorem result_term_not_in_frontier_image_of_var_not_in_frontier (trg : PreTrigger sig)
      (disj_index : Fin trg.rule.head.length) (v : sig.V) (v_not_in_frontier : ¬ v ∈ trg.rule.frontier) :
      ¬ trg.apply_to_var_or_const disj_index.val (VarOrConst.var v) ∈ trg.rule.frontier.map trg.subs := by
    intro contra
    apply v_not_in_frontier
    rw [List.mem_map] at contra
    rcases contra with ⟨u, u_in_frontier, u_eq⟩

    have := trg.apply_to_var_or_const_injective_of_not_in_frontier disj_index v_not_in_frontier (VarOrConst.var u)
    rw [VarOrConst.var.injEq] at this
    rw [this]
    . exact u_in_frontier
    . rw [← u_eq, PreTrigger.apply_to_var_or_const_frontier_var]; exact u_in_frontier

  abbrev apply_to_function_free_atom (trg : PreTrigger sig) (disjunctIndex : Nat) (atom : FunctionFreeAtom sig) : Fact sig :=
    (trg.apply_to_var_or_const disjunctIndex).apply_generalized_atom atom

  def mapped_body (trg : PreTrigger sig) : List (Fact sig) := trg.subs.apply_function_free_conj trg.rule.body

  theorem mem_terms_mapped_body_iff (trg : PreTrigger sig) : ∀ t, t ∈ trg.mapped_body.flatMap GeneralizedAtom.terms ↔ ((∃ c ∈ trg.rule.body.consts, GroundTerm.const c = t) ∨ (∃ v ∈ trg.rule.body.vars, trg.subs v = t)) := by
    intro t
    rw [List.mem_flatMap]
    constructor
    . intro h
      rcases h with ⟨f, f_mem, t_mem⟩
      simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list] at f_mem
      rw [List.mem_map] at f_mem
      rcases f_mem with ⟨a, a_mem, f_eq⟩
      rw [← f_eq] at t_mem
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
        . apply List.mem_map_of_mem; exact a_mem
        . simp only [TermMapping.apply_generalized_atom]
          rw [List.mem_map]
          exists VarOrConst.const c
      | inr h =>
        rcases h with ⟨v, v_mem, t_eq⟩
        rcases FunctionFreeConjunction.mem_vars.mp v_mem with ⟨a, a_mem, v_mem⟩
        exists trg.subs.apply_function_free_atom a
        constructor
        . apply List.mem_map_of_mem; exact a_mem
        . simp only [TermMapping.apply_generalized_atom]
          rw [List.mem_map]
          exists VarOrConst.var v

  def mapped_head (trg : PreTrigger sig) : List (List (Fact sig)) :=
    trg.rule.head.zipIdx.map (fun (h, i) => h.map (trg.apply_to_function_free_atom i))

  theorem length_mapped_head (trg : PreTrigger sig) : trg.mapped_head.length = trg.rule.head.length := by
    unfold mapped_head
    rw [List.length_map, List.length_zipIdx]

  theorem length_each_mapped_head (trg : PreTrigger sig) : ∀ (n : Nat), trg.mapped_head[n]?.map (List.length) = trg.rule.head[n]?.map (List.length) := by
    intro n
    unfold mapped_head
    simp only [List.getElem?_map, List.getElem?_zipIdx, Option.map_map]
    cases trg.rule.head[n]? <;> simp

  def subs_for_mapped_head (trg : PreTrigger sig) (i : Fin trg.mapped_head.length) : GroundSubstitution sig :=
    fun v => trg.apply_to_var_or_const i (.var v)

  theorem apply_subs_for_var_or_const_eq (trg : PreTrigger sig) (i : Fin trg.mapped_head.length) :
      ∀ voc, (trg.subs_for_mapped_head i).apply_var_or_const voc = trg.apply_to_var_or_const i voc := by
    intro voc
    unfold GroundSubstitution.apply_var_or_const
    unfold subs_for_mapped_head
    unfold apply_to_var_or_const
    cases voc <;> simp [skolemize_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term]

  theorem apply_subs_for_atom_eq (trg : PreTrigger sig) (i : Fin trg.mapped_head.length) :
      ∀ a, (trg.subs_for_mapped_head i).apply_function_free_atom a = trg.apply_to_function_free_atom i a := by
    intro a
    unfold GroundSubstitution.apply_function_free_atom
    unfold apply_to_function_free_atom
    apply TermMapping.apply_generalized_atom_congr_left
    intros
    apply apply_subs_for_var_or_const_eq

  theorem apply_subs_for_mapped_head_eq (trg : PreTrigger sig) (i : Fin trg.mapped_head.length) :
      (trg.subs_for_mapped_head i).apply_function_free_conj (trg.rule.head[i.val]'(by rw [← length_mapped_head]; exact i.isLt)) =
      trg.mapped_head[i.val] := by
    unfold mapped_head
    unfold subs_for_mapped_head
    unfold GroundSubstitution.apply_function_free_conj
    unfold TermMapping.apply_generalized_atom_list
    rw [List.getElem_map, List.getElem_zipIdx, List.map_inj_left, Nat.zero_add]
    intros
    apply apply_subs_for_atom_eq trg i

  def fresh_terms_for_head_disjunct (trg : PreTrigger sig) (i : Nat) (lt : i < trg.rule.head.length) : List (GroundTerm sig) :=
    (trg.rule.existential_vars_for_head_disjunct i lt).map (trg.functional_term_for_var i)

  theorem term_functional_of_mem_fresh_terms {trg : PreTrigger sig} {i : Nat} {lt : i < trg.rule.head.length} :
      ∀ t ∈ trg.fresh_terms_for_head_disjunct i lt, ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok := by
    intro t t_mem
    simp only [fresh_terms_for_head_disjunct, List.mem_map, functional_term_for_var] at t_mem
    rcases t_mem with ⟨_, _, t_mem⟩
    exact ⟨_, _, _, Eq.symm t_mem⟩

  theorem constant_not_mem_fresh_terms_for_head_disjunct {trg : PreTrigger sig} {i : Nat} {lt : i < trg.rule.head.length} :
      ∀ {c : sig.C}, ¬ .const c ∈ trg.fresh_terms_for_head_disjunct i lt := by
    intro c c_mem
    rcases term_functional_of_mem_fresh_terms _ c_mem with ⟨func, ts, arity_ok, eq⟩
    simp [GroundTerm.const, GroundTerm.func] at eq

  theorem frontier_term_not_mem_fresh_terms_for_head_disjunct {trg : PreTrigger sig} {i : Nat} {lt : i < trg.rule.head.length} :
      ∀ {t}, t ∈ trg.rule.frontier.map trg.subs -> ¬ t ∈ trg.fresh_terms_for_head_disjunct i lt := by
    intro t t_frontier t_fresh
    simp only [fresh_terms_for_head_disjunct, List.mem_map] at t_fresh
    rcases t_fresh with ⟨v, v_mem, t_fresh⟩; simp only [Rule.existential_vars_for_head_disjunct, List.mem_filter, decide_eq_true_eq] at v_mem
    apply trg.result_term_not_in_frontier_image_of_var_not_in_frontier ⟨i, lt⟩ v v_mem.right
    rw [apply_to_var_or_const_non_frontier_var _ _ _ v_mem.right]
    rw [t_fresh]
    exact t_frontier

  def existential_var_for_fresh_term (trg : PreTrigger sig) (i : Nat) (lt : i < trg.rule.head.length) (t : GroundTerm sig) (t_mem : t ∈ trg.fresh_terms_for_head_disjunct i lt) : sig.V :=
    ((trg.rule.existential_vars_for_head_disjunct i lt).find? (fun v => trg.functional_term_for_var i v = t)).get (by
      simp only [List.find?_isSome, decide_eq_true_eq]
      simp only [fresh_terms_for_head_disjunct, List.mem_map] at t_mem
      exact t_mem)

  theorem existential_var_for_fresh_term_after_functional_term_for_var
      {trg : PreTrigger sig}
      {i : Nat}
      (lt : i < trg.rule.head.length)
      {v : sig.V}
      (v_mem : v ∈ trg.rule.existential_vars_for_head_disjunct i lt) :
      trg.existential_var_for_fresh_term i lt (trg.functional_term_for_var i v) (List.mem_map_of_mem v_mem) = v := by
    simp only [existential_var_for_fresh_term]
    apply Option.get_of_eq_some
    simp only [List.find?_eq_some_iff_getElem, decide_eq_true_eq, true_and]
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
      simp only [not_decide_eq_true, functional_term_for_var, GroundTerm.func, Subtype.mk.injEq, FiniteTree.inner.injEq, and_true, SkolemFS.mk.injEq, true_and]
      intro contra
      apply k_lt
      rw [contra]

  def atom_for_result_fact (trg : PreTrigger sig) {f : Fact sig} (i : Fin trg.mapped_head.length)
      (f_mem : f ∈ trg.mapped_head[i.val]) : FunctionFreeAtom sig :=
    let j := trg.mapped_head[i.val].idxOf f
    let i' : Fin trg.rule.head.length := ⟨i.val, by rw [← length_mapped_head]; exact i.isLt⟩
    let j' : Fin (trg.rule.head[i'.val].length) := ⟨j, by
      have := trg.length_each_mapped_head i.val
      rw [List.getElem?_eq_getElem i.isLt] at this
      rw [List.getElem?_eq_getElem i'.isLt] at this
      simp only [Option.map_some, Option.some_inj] at this
      rw [← this]
      apply List.idxOf_lt_length_of_mem
      exact f_mem
    ⟩
    trg.rule.head[i'.val][j'.val]

  theorem apply_on_atom_for_result_fact_is_fact (trg : PreTrigger sig) {f : Fact sig} (i : Fin trg.mapped_head.length)
      (f_mem : f ∈ trg.mapped_head[i.val]) : trg.apply_to_function_free_atom i (trg.atom_for_result_fact i f_mem) = f := by
    have : f = trg.mapped_head[i.val][trg.mapped_head[i.val].idxOf f]'(List.idxOf_lt_length_of_mem f_mem) := by rw [List.getElem_idxOf_of_mem]; exact f_mem
    conv => right; rw [this]
    unfold atom_for_result_fact
    unfold mapped_head
    simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]

  theorem atom_for_result_fact_mem_head {trg : PreTrigger sig} {f : Fact sig} {i : Fin trg.mapped_head.length}
      {f_mem : f ∈ trg.mapped_head[i.val]} : trg.atom_for_result_fact i f_mem ∈ trg.rule.head[i.val]'(by rw [← length_mapped_head]; exact i.isLt) := by simp [atom_for_result_fact]

  def var_or_const_for_result_term (trg : PreTrigger sig) {f : Fact sig} {t : GroundTerm sig} (i : Fin trg.mapped_head.length)
      (f_mem : f ∈ trg.mapped_head[i.val]) (t_mem : t ∈ f.terms) : VarOrConst sig :=
    let k := f.terms.idxOf t
    let atom := trg.atom_for_result_fact i f_mem
    let k' : Fin atom.terms.length := ⟨k, by
      have isLt := List.idxOf_lt_length_of_mem t_mem
      have := trg.apply_on_atom_for_result_fact_is_fact i f_mem
      conv at isLt => right; rw [← this]
      rw [TermMapping.length_terms_apply_generalized_atom] at isLt
      exact isLt
    ⟩
    atom.terms[k'.val]

  theorem apply_on_var_or_const_for_result_term_is_term (trg : PreTrigger sig) {f : Fact sig} {t : GroundTerm sig}
      (i : Fin trg.mapped_head.length) (f_mem : f ∈ trg.mapped_head[i.val]) (t_mem : t ∈ f.terms) :
      trg.apply_to_var_or_const i (trg.var_or_const_for_result_term i f_mem t_mem) = t := by
    have t_eq : t = f.terms[f.terms.idxOf t]'(List.idxOf_lt_length_of_mem t_mem) := by rw [List.getElem_idxOf_of_mem]; exact t_mem
    have := trg.apply_on_atom_for_result_fact_is_fact i f_mem
    have : (trg.apply_to_function_free_atom i (trg.atom_for_result_fact i f_mem)).terms = f.terms := by rw [this]
    conv at t_eq => right; simp only [← this]
    conv at t_eq => right; left; simp only [this]
    conv => right; rw [t_eq]
    unfold apply_to_function_free_atom
    unfold TermMapping.apply_generalized_atom
    rw [List.getElem_map]
    rfl

  theorem var_or_const_for_result_term_mem_atom_for_result_fact {trg : PreTrigger sig} {f : Fact sig} {t : GroundTerm sig}
      {i : Fin trg.mapped_head.length} {f_mem : f ∈ trg.mapped_head[i.val]} {t_mem : t ∈ f.terms} :
      trg.var_or_const_for_result_term i f_mem t_mem ∈ (trg.atom_for_result_fact i f_mem).terms := by simp [var_or_const_for_result_term]

  theorem var_or_const_for_result_term_mem_terms_head {trg : PreTrigger sig} {f : Fact sig} {t : GroundTerm sig}
      {i : Fin trg.mapped_head.length} {f_mem : f ∈ trg.mapped_head[i.val]} {t_mem : t ∈ f.terms} :
      trg.var_or_const_for_result_term i f_mem t_mem ∈ (trg.rule.head[i.val]'(by rw [← length_mapped_head]; exact i.isLt)).terms := by unfold FunctionFreeConjunction.terms; apply List.mem_flatMap_of_mem; apply atom_for_result_fact_mem_head; exact f_mem; apply var_or_const_for_result_term_mem_atom_for_result_fact

  theorem mem_terms_mapped_head_iff (trg : PreTrigger sig) (i : Nat) (lt : i < trg.mapped_head.length) :
      ∀ t, t ∈ trg.mapped_head[i].flatMap GeneralizedAtom.terms ↔ (∃ c, c ∈ (trg.rule.head[i]'(by rw [← length_mapped_head]; exact lt)).consts ∧ GroundTerm.const c = t) ∨ t ∈ (trg.rule.frontier_for_head ⟨i, (by rw [← length_mapped_head]; exact lt)⟩).map trg.subs ∨ t ∈ trg.fresh_terms_for_head_disjunct i (by rw [← length_mapped_head]; exact lt) := by
    intro t
    rw [List.mem_flatMap, List.mem_map]
    constructor
    . rintro ⟨f, f_mem, t_mem⟩
      cases eq : trg.var_or_const_for_result_term ⟨i, lt⟩ f_mem t_mem with
      | const c =>
        apply Or.inl
        exists c
        constructor
        . rw [FunctionFreeConjunction.mem_consts]
          exists trg.atom_for_result_fact ⟨i, lt⟩ f_mem
          constructor
          . apply atom_for_result_fact_mem_head
          . rw [← eq]
            apply var_or_const_for_result_term_mem_atom_for_result_fact
        . rw [← trg.apply_on_var_or_const_for_result_term_is_term ⟨i, lt⟩ f_mem t_mem, eq]; rfl
      | var v =>
        apply Or.inr
        cases Decidable.em (v ∈ trg.rule.frontier) with
        | inl v_mem_frontier =>
          have v_mem_frontier : v ∈ trg.rule.frontier_for_head ⟨i, by rw [← length_mapped_head]; exact lt⟩ := by
            apply Rule.mem_frontier_for_head_of_mem_frontier_of_mem_head_terms
            . exact v_mem_frontier
            . rw [← eq]; apply var_or_const_for_result_term_mem_terms_head
          apply Or.inl
          exists v
          constructor
          . exact v_mem_frontier
          . rw [← trg.apply_on_var_or_const_for_result_term_is_term ⟨i, lt⟩ f_mem t_mem, eq, apply_to_var_or_const_frontier_var]; rw [Rule.mem_frontier_iff_mem_frontier_for_head]; exists ⟨i, by rw [← length_mapped_head]; exact lt⟩
        | inr v_nmem_frontier =>
          apply Or.inr
          unfold fresh_terms_for_head_disjunct Rule.existential_vars_for_head_disjunct
          simp only [List.mem_map, List.mem_filter, decide_eq_true_iff, FunctionFreeConjunction.mem_vars]
          exists v
          constructor
          constructor
          . exists trg.atom_for_result_fact ⟨i, lt⟩ f_mem
            constructor
            . apply atom_for_result_fact_mem_head
            . rw [← eq]
              apply var_or_const_for_result_term_mem_atom_for_result_fact
          . exact v_nmem_frontier
          . rw [← trg.apply_on_var_or_const_for_result_term_is_term ⟨i, lt⟩ f_mem t_mem, eq, apply_to_var_or_const_non_frontier_var]; exact v_nmem_frontier
    . intro h
      cases h with
      | inl h =>
        rcases h with ⟨c, c_mem, t_eq⟩
        rcases FunctionFreeConjunction.mem_consts.mp c_mem with ⟨a, a_mem, c_mem⟩
        exists trg.apply_to_function_free_atom i a
        constructor
        . unfold mapped_head; simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]; apply List.mem_map_of_mem; exact a_mem
        . simp only [apply_to_function_free_atom, TermMapping.apply_generalized_atom]
          rw [List.mem_map]
          exists .const c
      | inr h =>
      cases h with
      | inl h =>
        rcases h with ⟨v, v_mem, t_eq⟩
        rcases FunctionFreeConjunction.mem_vars.mp (trg.rule.frontier_for_head_subset_vars_head v_mem) with ⟨a, a_mem, v_mem'⟩
        exists trg.apply_to_function_free_atom i a
        constructor
        . unfold mapped_head; simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]; apply List.mem_map_of_mem; exact a_mem
        . simp only [apply_to_function_free_atom, TermMapping.apply_generalized_atom]
          rw [List.mem_map]
          exists .var v
          constructor
          . exact v_mem'
          . rw [apply_to_var_or_const_frontier_var _ _ _ (by apply Rule.mem_frontier_iff_mem_frontier_for_head.mpr; exists ⟨i, (by rw [← length_mapped_head]; exact lt)⟩)]; exact t_eq
      | inr h =>
        unfold fresh_terms_for_head_disjunct Rule.existential_vars_for_head_disjunct at h
        simp only [List.mem_map, List.mem_filter, decide_eq_true_iff, FunctionFreeConjunction.mem_vars] at h
        rcases h with ⟨v, ⟨⟨a, a_mem, v_mem⟩, v_not_frontier⟩, t_eq⟩
        exists trg.apply_to_function_free_atom i a
        constructor
        . unfold mapped_head; simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]; apply List.mem_map_of_mem; exact a_mem
        . simp only [apply_to_function_free_atom, TermMapping.apply_generalized_atom]
          rw [List.mem_map]
          exists .var v
          constructor
          . exact v_mem
          . rw [apply_to_var_or_const_non_frontier_var _ _ _ v_not_frontier]; exact t_eq

  theorem mapped_head_constants_subset (trg : PreTrigger sig) (i : Fin trg.mapped_head.length) :
      FactSet.constants trg.mapped_head[i.val].toSet ⊆ (((trg.rule.frontier.map (trg.subs_for_mapped_head i)).flatMap GroundTerm.constants) ++ (trg.rule.head[i.val]'(by rw [← length_mapped_head]; exact i.isLt)).consts).toSet := by
    intro c c_mem
    rw [List.mem_toSet, List.mem_append]
    rw [FactSet.mem_constants_toSet, List.mem_flatMap] at c_mem
    rcases c_mem with ⟨f, f_mem, c_mem⟩
    simp only [Fact.constants, List.mem_flatMap] at c_mem
    rcases c_mem with ⟨t, t_mem, c_mem⟩
    have t_mem : t ∈ trg.mapped_head[i.val].flatMap GeneralizedAtom.terms := by rw [List.mem_flatMap]; exists f
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
          apply Rule.mem_frontier_iff_mem_frontier_for_head.mpr; exact ⟨_, v_mem⟩
        rw [List.mem_map]; exists v; constructor;
        . exact v_mem
        . unfold subs_for_mapped_head; rw [apply_to_var_or_const_frontier_var]; exact t_mem; exact v_mem
      . exact c_mem
    | inr t_mem =>
      apply Or.inl
      simp only [fresh_terms_for_head_disjunct, List.mem_map] at t_mem; rcases t_mem with ⟨v, v_mem, t_mem⟩
      rw [← t_mem] at c_mem
      simp only [functional_term_for_var, GroundTerm.constants_func, List.mem_flatMap, List.mem_map] at c_mem
      rcases c_mem with ⟨t, ⟨v, v_mem, t_eq⟩, t_mem⟩
      simp only [List.mem_flatMap, List.mem_map]
      exists t; constructor; exists v; constructor
      . exact v_mem
      . unfold subs_for_mapped_head; rw [apply_to_var_or_const_frontier_var]; exact t_eq; exact v_mem
      . exact t_mem

  def loaded (trg : PreTrigger sig) (F : FactSet sig) : Prop :=
    trg.mapped_body.toSet ⊆ F

  theorem term_mapping_preserves_loadedness (trg : PreTrigger sig) (fs : FactSet sig) (h : GroundTermMapping sig) (h_id : h.isIdOnConstants) : trg.loaded fs -> { rule := trg.rule, subs := h ∘ trg.subs : PreTrigger sig }.loaded (h.applyFactSet fs) := by
    unfold loaded
    unfold mapped_body
    intro loaded
    intro f f_mem
    rw [List.mem_toSet] at f_mem
    simp only [GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list] at f_mem
    rw [List.mem_map] at f_mem
    rcases f_mem with ⟨a, a_mem, f_mem⟩
    rw [← GroundSubstitution.apply_function_free_atom.eq_def, GroundSubstitution.apply_function_free_atom_compose_of_isIdOnConstants _ _ h_id] at f_mem
    rw [← f_mem]
    apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
    apply loaded
    unfold GroundSubstitution.apply_function_free_conj
    rw [List.mem_toSet, TermMapping.apply_generalized_atom_list.eq_def, List.mem_map]
    exists a

  def satisfied_for_disj (trg : PreTrigger sig) (fs : FactSet sig) (disj_index : Fin trg.rule.head.length) : Prop :=
    ∃ (s : GroundSubstitution sig),
      (∀ v, v ∈ (Rule.frontier trg.rule) → s v = trg.subs v) ∧
      ((s.apply_function_free_conj (trg.rule.head[disj_index.val])).toSet ⊆ fs)

  theorem satisfied_for_disj_of_mapped_head_contained (trg : PreTrigger sig) (fs : FactSet sig)
      (disj_index : Fin trg.rule.head.length) :
      (trg.mapped_head[disj_index.val]'(by rw [length_mapped_head]; exact disj_index.isLt)).toSet ⊆ fs ->
      trg.satisfied_for_disj fs disj_index := by
    intro h
    let i : Fin trg.mapped_head.length := ⟨disj_index.val, by rw [length_mapped_head]; exact disj_index.isLt⟩
    exists trg.subs_for_mapped_head i
    constructor
    . intro v v_mem; unfold subs_for_mapped_head; rw [trg.apply_to_var_or_const_frontier_var i v v_mem]
    . rw [trg.apply_subs_for_mapped_head_eq i]; exact h

  def satisfied (trg : PreTrigger sig) (F : FactSet sig) : Prop :=
    ∃ disj_index, trg.satisfied_for_disj F disj_index

  def equiv (trg1 trg2 : PreTrigger sig) : Prop :=
    trg1.rule = trg2.rule ∧ ∀ v, v ∈ trg1.rule.frontier -> trg1.subs v = trg2.subs v

  theorem equiv_symm {trg1 trg2 : PreTrigger sig} : trg1.equiv trg2 -> trg2.equiv trg1 := by
    unfold equiv
    intro h
    constructor
    . apply Eq.symm; exact h.left
    . intro v v_mem
      apply Eq.symm
      apply h.right
      rw [h.left]
      exact v_mem

  def strong_equiv (trg1 trg2 : PreTrigger sig) : Prop :=
    trg1.rule = trg2.rule ∧ ∀ v, v ∈ trg1.rule.body.vars -> trg1.subs v = trg2.subs v

  theorem strong_equiv_symm {trg1 trg2 : PreTrigger sig} : trg1.strong_equiv trg2 -> trg2.strong_equiv trg1 := by
    unfold strong_equiv
    intro h
    constructor
    . apply Eq.symm; exact h.left
    . intro v v_mem
      apply Eq.symm
      apply h.right
      rw [h.left]
      exact v_mem

  theorem equiv_of_strong_equiv {trg1 trg2 : PreTrigger sig} : trg1.strong_equiv trg2 -> trg1.equiv trg2 := by
    intro ⟨r_eq, body_mapping_eq⟩
    constructor
    . exact r_eq
    . intro v v_mem
      apply body_mapping_eq
      exact trg1.rule.frontier_subset_vars_body v_mem

  theorem subs_apply_function_free_atom_eq_of_strong_equiv {trg1 trg2 : PreTrigger sig} : trg1.strong_equiv trg2 -> ∀ a, a ∈ trg1.rule.body -> trg1.subs.apply_function_free_atom a = trg2.subs.apply_function_free_atom a := by
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

  theorem apply_to_function_free_atom_eq_of_equiv {trg1 trg2 : PreTrigger sig} : trg1.equiv trg2 -> ∀ (i : Nat), ∀ a, trg1.apply_to_function_free_atom i a = trg2.apply_to_function_free_atom i a := by
    unfold equiv
    intro h i a
    apply TermMapping.apply_generalized_atom_congr_left
    intro voc voc_mem
    cases voc with
    | const c => simp only [PreTrigger.apply_to_var_or_const_for_const]
    | var v =>
      cases Decidable.em (v ∈ trg1.rule.frontier) with
      | inl v_front =>
        have v_front_2 : v ∈ trg2.rule.frontier := by rw [← h.left]; exact v_front
        rw [PreTrigger.apply_to_var_or_const_frontier_var _ _ _ v_front]
        rw [PreTrigger.apply_to_var_or_const_frontier_var _ _ _ v_front_2]
        apply h.right
        exact v_front
      | inr v_front =>
        have v_front_2 : ¬ v ∈ trg2.rule.frontier := by rw [← h.left]; exact v_front
        rw [PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v_front]
        rw [PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v_front_2]
        unfold PreTrigger.functional_term_for_var
        simp only [← h.left]
        have : trg1.rule.frontier.map trg1.subs = trg1.rule.frontier.map trg2.subs := by
          rw [List.map_inj_left]
          exact h.right
        simp only [this]

  theorem result_eq_of_equiv {trg1 trg2 : PreTrigger sig} : trg1.equiv trg2 -> trg1.mapped_head = trg2.mapped_head := by
    unfold equiv
    intro h
    unfold mapped_head
    rw [h.left]
    rw [List.map_inj_left]
    intro e e_mem
    rw [List.map_inj_left]
    intro a a_mem
    apply apply_to_function_free_atom_eq_of_equiv
    exact h

  theorem satisfied_preserved_of_equiv {trg1 trg2 : PreTrigger sig} : trg1.equiv trg2 -> ∀ {fs}, trg1.satisfied fs ↔ trg2.satisfied fs := by
    intro equiv fs
    constructor
    . intro h
      rcases h with ⟨i, s, front, subset⟩
      exists ⟨i, by rw [← equiv.left]; exact i.isLt⟩, s
      constructor
      . intro v v_mem
        rw [← equiv.right]
        . apply front; rw [equiv.left]; exact v_mem
        . rw [equiv.left]; exact v_mem
      . simp only [← equiv.left]; exact subset
    . intro h
      rcases h with ⟨i, s, front, subset⟩
      exists ⟨i, by rw [equiv.left]; exact i.isLt⟩, s
      constructor
      . intro v v_mem
        rw [equiv.right]
        . apply front; rw [← equiv.left]; exact v_mem
        . exact v_mem
      . simp only [equiv.left]; exact subset

end PreTrigger

