import ExistentialRules.ChaseSequence.Termination.BacktrackingOfFacts
import ExistentialRules.ChaseSequence.Termination.RenameConstantsApart
import ExistentialRules.Triggers.Basic

section Defs

  variable (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

  -- This is essentially the same as a GroundSubstitution only that it maps constants instead of variables
  abbrev ConstantMapping := sig.C -> GroundTerm sig

  abbrev StrictConstantMapping := sig.C -> sig.C

end Defs


namespace ConstantMapping

  variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

  def apply_pre_ground_term (g : ConstantMapping sig) (t : PreGroundTerm sig) : PreGroundTerm sig := t.mapLeaves (fun c => (g c).val)

  mutual

    theorem apply_pre_ground_term_arity_ok (g : ConstantMapping sig) (t : FiniteTree (SkolemFS sig) sig.C) (arity_ok : PreGroundTerm.arity_ok t) : PreGroundTerm.arity_ok (g.apply_pre_ground_term t) := by
      cases t with
      | leaf c =>
        unfold apply_pre_ground_term
        unfold FiniteTree.mapLeaves
        exact (g c).property
      | inner f ts =>
        unfold PreGroundTerm.arity_ok at arity_ok
        rw [Bool.and_eq_true] at arity_ok
        unfold apply_pre_ground_term
        unfold FiniteTree.mapLeaves
        unfold PreGroundTerm.arity_ok
        rw [Bool.and_eq_true]
        constructor
        . rw [FiniteTree.length_mapLeavesList]
          exact arity_ok.left
        . apply apply_pre_ground_term_list_arity_ok
          exact arity_ok.right

    theorem apply_pre_ground_term_list_arity_ok (g : ConstantMapping sig) (ts : FiniteTreeList (SkolemFS sig) sig.C) (arity_ok : PreGroundTerm.arity_ok_list ts) : PreGroundTerm.arity_ok_list (FiniteTree.mapLeavesList (fun c => (g c).val) ts) := by
      cases ts with
      | nil => simp [FiniteTree.mapLeavesList, PreGroundTerm.arity_ok_list]
      | cons hd tl =>
        unfold PreGroundTerm.arity_ok_list at arity_ok
        rw [Bool.and_eq_true] at arity_ok
        unfold FiniteTree.mapLeavesList
        unfold PreGroundTerm.arity_ok_list
        rw [Bool.and_eq_true]
        constructor
        . apply apply_pre_ground_term_arity_ok; exact arity_ok.left
        . apply apply_pre_ground_term_list_arity_ok; exact arity_ok.right

  end

  def apply_ground_term (g : ConstantMapping sig) (t : GroundTerm sig) : GroundTerm sig := ⟨g.apply_pre_ground_term t.val, g.apply_pre_ground_term_arity_ok t.val t.property⟩

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
      simp
      rw [FiniteTree.mapLeavesList_fromList_eq_fromList_map]
      apply congrArg
      unfold ConstantMapping.apply_ground_term
      unfold List.unattach
      rw [List.map_map]
      rw [List.map_map]
      rw [List.map_map]
      rfl


  variable [DecidableEq sig.P]

  def apply_fact (g : ConstantMapping sig) (f : Fact sig) : Fact sig := {
    predicate := f.predicate
    terms := f.terms.map g.apply_ground_term
    arity_ok := by rw [List.length_map]; exact f.arity_ok
  }

  theorem apply_fact_eq_groundTermMapping_applyFact (g : ConstantMapping sig) (f : Fact sig) : g.apply_fact f = GroundTermMapping.applyFact g.apply_ground_term f := by
    simp [apply_fact, GroundTermMapping.applyFact]

  theorem apply_fact_swap_apply_to_function_free_atom (g : ConstantMapping sig) (trg : PreTrigger sig) (a : FunctionFreeAtom sig) (h : ∀ d ∈ a.constants, g d = GroundTerm.const d) : ∀ i, g.apply_fact (trg.apply_to_function_free_atom i a) = PreTrigger.apply_to_function_free_atom { rule := trg.rule, subs := g.apply_ground_term ∘ trg.subs } i a := by
    intro i
    unfold PreTrigger.apply_to_function_free_atom
    unfold ConstantMapping.apply_fact
    unfold PreTrigger.apply_to_var_or_const
    unfold PreTrigger.skolemize_var_or_const
    simp
    intro voc voc_mem
    cases voc with
    | var v =>
      rw [ConstantMapping.apply_ground_term_swap_apply_skolem_term]
      intro c contra
      simp [VarOrConst.skolemize] at contra
      split at contra <;> contradiction
    | const d =>
      unfold VarOrConst.skolemize
      unfold GroundSubstitution.apply_skolem_term
      unfold ConstantMapping.apply_ground_term
      unfold ConstantMapping.apply_pre_ground_term
      unfold FiniteTree.mapLeaves
      unfold GroundTerm.const
      apply Subtype.eq
      simp only
      rw [h]
      . simp [GroundTerm.const]
      . unfold FunctionFreeAtom.constants
        apply VarOrConst.mem_filterConsts_of_const
        exact voc_mem

  def apply_fact_set (g : ConstantMapping sig) (fs : FactSet sig) : FactSet sig := fun f => ∃ f', f' ∈ fs ∧ f = g.apply_fact f'

  theorem apply_fact_mem_apply_fact_set_of_mem (g : ConstantMapping sig) (f : Fact sig) (fs : FactSet sig) : f ∈ fs -> g.apply_fact f ∈ g.apply_fact_set fs := by
    intro f_mem
    exists f

end ConstantMapping

namespace StrictConstantMapping

  variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

  def toConstantMapping (g : StrictConstantMapping sig) : ConstantMapping sig := fun c => GroundTerm.const (g c)

  def apply_var_or_const (g : StrictConstantMapping sig) : VarOrConst sig -> VarOrConst sig
  | .var v => .var v
  | .const c => .const (g c)

  theorem apply_var_or_const_filterVars_eq (g : StrictConstantMapping sig) (vocs : List (VarOrConst sig)) : VarOrConst.filterVars (vocs.map g.apply_var_or_const) = VarOrConst.filterVars vocs := by
    induction vocs with
    | nil => simp
    | cons hd tl ih =>
      cases hd <;> (
        simp only [List.map_cons, VarOrConst.filterVars, StrictConstantMapping.apply_var_or_const]
        rw [ih]
      )


  variable [DecidableEq sig.P]

  def apply_function_free_atom (g : StrictConstantMapping sig) (a : FunctionFreeAtom sig) : FunctionFreeAtom sig := {
    predicate := a.predicate
    terms := a.terms.map g.apply_var_or_const
    arity_ok := by rw [List.length_map]; exact a.arity_ok
  }

  theorem apply_function_free_atom_vars_eq (g : StrictConstantMapping sig) (a : FunctionFreeAtom sig) : (g.apply_function_free_atom a).variables = a.variables := by
    unfold apply_function_free_atom
    unfold FunctionFreeAtom.variables
    simp only
    rw [apply_var_or_const_filterVars_eq]

  def apply_function_free_conj (g : StrictConstantMapping sig) (conj : FunctionFreeConjunction sig) : FunctionFreeConjunction sig := conj.map g.apply_function_free_atom

  theorem apply_function_free_conj_vars_eq (g : StrictConstantMapping sig) (conj : FunctionFreeConjunction sig) : (g.apply_function_free_conj conj).vars = conj.vars := by
    unfold apply_function_free_conj
    unfold FunctionFreeConjunction.vars
    unfold List.flatMap
    rw [List.map_map]
    have : conj.map (FunctionFreeAtom.variables ∘ g.apply_function_free_atom) = conj.map FunctionFreeAtom.variables := by
      simp only [List.map_inj_left]
      intro a a_mem
      rw [Function.comp_apply]
      apply apply_function_free_atom_vars_eq
    rw [this]

end StrictConstantMapping

section ArgumentsForImages

  namespace StrictConstantMapping

    variable {sig : Signature} [DecidableEq sig.C]

    def arguments_for_constant (g : StrictConstantMapping sig) (possible_constants : List sig.C) (c : sig.C) : List sig.C :=
      possible_constants.filter (fun d => g d = c)

    theorem apply_to_arguments_yields_original_constant (g : StrictConstantMapping sig) (possible_constants : List sig.C) (c : sig.C) :
        ∀ arg, arg ∈ g.arguments_for_constant possible_constants c ↔ (arg ∈ possible_constants ∧ g arg = c) := by
      intro arg
      unfold arguments_for_constant
      simp

    variable [DecidableEq sig.V]

    mutual
      def arguments_for_pre_term (g : StrictConstantMapping sig) (possible_constants : List sig.C) : FiniteTree (SkolemFS sig) sig.C -> List (PreGroundTerm sig)
      | .leaf c => (g.arguments_for_constant possible_constants c).map (fun arg => .leaf arg)
      | .inner func ts =>
        (g.arguments_for_pre_term_list possible_constants ts).map (fun ts =>
          .inner func (FiniteTreeList.fromList ts)
        )
      def arguments_for_pre_term_list (g : StrictConstantMapping sig) (possible_constants : List sig.C) : FiniteTreeList (SkolemFS sig) sig.C -> List (List (PreGroundTerm sig))
      | .nil => [[]]
      | .cons hd tl =>
        let arguments_tail := g.arguments_for_pre_term_list possible_constants tl
        (g.arguments_for_pre_term possible_constants hd).flatMap (fun arg =>
          arguments_tail.map (fun arg_list =>
            arg :: arg_list
          )
        )
    end

    mutual
      theorem apply_to_arguments_yields_original_pre_term (g : StrictConstantMapping sig) (possible_constants : List sig.C) (term : FiniteTree (SkolemFS sig) sig.C) :
          ∀ arg, arg ∈ g.arguments_for_pre_term possible_constants term ↔ ((∀ c, c ∈ arg.leaves -> c ∈ possible_constants) ∧ g.toConstantMapping.apply_pre_ground_term arg = term) := by
        intro arg
        constructor
        . intro h
          cases term with
          | leaf c =>
            unfold arguments_for_pre_term at h
            rw [List.mem_map] at h
            rcases h with ⟨a, a_mem, arg_eq⟩
            rw [apply_to_arguments_yields_original_constant] at a_mem
            constructor
            . intro d d_mem
              rw [← arg_eq] at d_mem
              unfold FiniteTree.leaves at d_mem
              simp at d_mem
              rw [d_mem]
              exact a_mem.left
            . rw [← arg_eq]
              unfold ConstantMapping.apply_pre_ground_term
              unfold FiniteTree.mapLeaves
              unfold toConstantMapping
              rw [a_mem.right]
              rfl
          | inner func ts =>
            unfold arguments_for_pre_term at h
            rw [List.mem_map] at h
            rcases h with ⟨a, a_mem, arg_eq⟩
            rw [apply_to_arguments_yields_original_pre_term_list] at a_mem
            constructor
            . intro d d_mem
              rw [← arg_eq] at d_mem
              unfold FiniteTree.leaves at d_mem
              apply a_mem.left
              exact d_mem
            . rw [← arg_eq]
              unfold ConstantMapping.apply_pre_ground_term
              unfold FiniteTree.mapLeaves
              rw [a_mem.right]
        . intro h
          cases term with
          | leaf c =>
            unfold arguments_for_pre_term
            rw [List.mem_map]
            cases arg with
            | leaf d =>
              exists d
              rw [apply_to_arguments_yields_original_constant]
              constructor
              . constructor
                . apply h.left
                  unfold FiniteTree.leaves
                  simp
                . have r := h.right
                  unfold ConstantMapping.apply_pre_ground_term at r
                  unfold toConstantMapping at r
                  unfold FiniteTree.mapLeaves at r
                  injection r with r
              . rfl
            | inner func args =>
              have contra := h.right
              simp [ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves] at contra
          | inner func ts =>
            unfold arguments_for_pre_term
            rw [List.mem_map]
            cases arg with
            | leaf d =>
              have contra := h.right
              simp [ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, toConstantMapping, GroundTerm.const] at contra
            | inner func' args =>
              exists args
              rw [apply_to_arguments_yields_original_pre_term_list]
              constructor
              . constructor
                . intro d d_mem
                  apply h.left
                  unfold FiniteTree.leaves
                  rw [FiniteTreeList.toListFromListIsId] at d_mem
                  exact d_mem
                . have r := h.right
                  unfold ConstantMapping.apply_pre_ground_term at r
                  unfold FiniteTree.mapLeaves at r
                  injection r with func_eq args_eq
                  rw [FiniteTreeList.toListFromListIsId]
                  exact args_eq
              . have r := h.right
                unfold ConstantMapping.apply_pre_ground_term at r
                unfold FiniteTree.mapLeaves at r
                injection r with func_eq args_eq
                rw [FiniteTreeList.toListFromListIsId]
                rw [func_eq]

      theorem apply_to_arguments_yields_original_pre_term_list (g : StrictConstantMapping sig) (possible_constants : List sig.C) (ts : FiniteTreeList (SkolemFS sig) sig.C) :
          ∀ args, args ∈ g.arguments_for_pre_term_list possible_constants ts ↔ ((∀ c, c ∈ (FiniteTree.leavesList (FiniteTreeList.fromList args)) -> c ∈ possible_constants) ∧ ((FiniteTree.mapLeavesList (fun leaf => g.toConstantMapping leaf) (FiniteTreeList.fromList args)) = ts)) := by
        intro args
        constructor
        . intro h
          cases ts with
          | nil =>
            simp [arguments_for_pre_term_list] at h
            rw [h]
            simp [FiniteTreeList.fromList, FiniteTree.mapLeavesList, FiniteTree.leavesList]
          | cons hd tl =>
            unfold arguments_for_pre_term_list at h
            rw [List.mem_flatMap] at h
            rcases h with ⟨hd_arg, hd_arg_mem, args_mem⟩
            rw [List.mem_map] at args_mem
            rcases args_mem with ⟨tl_args, tl_args_mem, args_eq⟩
            rw [apply_to_arguments_yields_original_pre_term] at hd_arg_mem
            rw [apply_to_arguments_yields_original_pre_term_list] at tl_args_mem
            rw [← args_eq]
            constructor
            . intro d d_mem
              unfold FiniteTreeList.fromList at d_mem
              unfold FiniteTree.leavesList at d_mem
              rw [List.mem_append] at d_mem
              cases d_mem with
              | inl d_mem => apply hd_arg_mem.left; exact d_mem
              | inr d_mem => apply tl_args_mem.left; exact d_mem
            . unfold FiniteTreeList.fromList
              unfold FiniteTree.mapLeavesList
              unfold ConstantMapping.apply_pre_ground_term at hd_arg_mem
              rw [hd_arg_mem.right]
              rw [tl_args_mem.right]
        . intro h
          cases ts with
          | nil =>
            cases args with
            | nil => simp [arguments_for_pre_term_list]
            | cons hd_arg tl_arg =>
              have r := h.right
              simp [FiniteTreeList.fromList, FiniteTree.mapLeavesList] at r
          | cons hd tl =>
            cases args with
            | nil =>
              have r := h.right
              simp [FiniteTreeList.fromList, FiniteTree.mapLeavesList] at r
            | cons hd_arg tl_arg =>
              unfold arguments_for_pre_term_list
              unfold FiniteTreeList.fromList at h
              unfold FiniteTree.leavesList at h
              unfold FiniteTree.mapLeavesList at h
              rw [List.mem_flatMap]
              exists hd_arg
              constructor
              . rw [apply_to_arguments_yields_original_pre_term]
                constructor
                . intro d d_mem
                  apply h.left
                  rw [List.mem_append]
                  apply Or.inl
                  exact d_mem
                . injection h.right
              . rw [List.mem_map]
                exists tl_arg
                simp only [and_true]
                rw [apply_to_arguments_yields_original_pre_term_list]
                constructor
                . intro d d_mem
                  apply h.left
                  rw [List.mem_append]
                  apply Or.inr
                  exact d_mem
                . injection h.right
    end

    theorem arguments_for_pre_term_list_length_preserved (g : StrictConstantMapping sig) (possible_constants : List sig.C) (ts : FiniteTreeList (SkolemFS sig) sig.C) :
        ∀ res, res ∈ (g.arguments_for_pre_term_list possible_constants ts) -> res.length = ts.toList.length := by
      cases ts with
      | nil => simp [arguments_for_pre_term_list, FiniteTreeList.toList]
      | cons hd tl =>
        intro res res_mem
        unfold arguments_for_pre_term_list at res_mem
        rw [List.mem_flatMap] at res_mem
        rcases res_mem with ⟨arg, arg_for_hd, res_mem⟩
        rw [List.mem_map] at res_mem
        rcases res_mem with ⟨args, args_for_tl, res_mem⟩
        rw [← res_mem]
        unfold FiniteTreeList.toList
        rw [List.length_cons]
        rw [List.length_cons]
        rw [Nat.add_right_cancel_iff]
        exact g.arguments_for_pre_term_list_length_preserved possible_constants tl args args_for_tl

    mutual

      theorem arguments_for_pre_term_arity_ok (g : StrictConstantMapping sig) (possible_constants : List sig.C) (t : FiniteTree (SkolemFS sig) sig.C) (arity_ok : PreGroundTerm.arity_ok t) : ∀ t', t' ∈ (g.arguments_for_pre_term possible_constants t) -> PreGroundTerm.arity_ok t' := by
        intro t' t'_mem
        unfold arguments_for_pre_term at t'_mem
        cases t with
        | leaf c =>
          rw [List.mem_map] at t'_mem
          rcases t'_mem with ⟨d, d_mem, t'_eq⟩
          rw [← t'_eq]
          simp [PreGroundTerm.arity_ok]
        | inner f ts =>
          unfold PreGroundTerm.arity_ok at arity_ok
          rw [Bool.and_eq_true] at arity_ok
          rw [List.mem_map] at t'_mem
          rcases t'_mem with ⟨ts', ts'_mem, t'_eq⟩
          rw [← t'_eq]
          simp only [PreGroundTerm.arity_ok]
          rw [Bool.and_eq_true]
          constructor
          . rw [FiniteTreeList.fromListToListIsId]
            rw [g.arguments_for_pre_term_list_length_preserved possible_constants ts ts' ts'_mem]
            exact arity_ok.left
          . apply g.arguments_for_pre_term_list_arity_ok possible_constants ts _ ts' ts'_mem
            exact arity_ok.right

      theorem arguments_for_pre_term_list_arity_ok (g : StrictConstantMapping sig) (possible_constants : List sig.C) (ts : FiniteTreeList (SkolemFS sig) sig.C) (arity_ok : PreGroundTerm.arity_ok_list ts) : ∀ ts', ts' ∈ (g.arguments_for_pre_term_list possible_constants ts) -> PreGroundTerm.arity_ok_list (FiniteTreeList.fromList ts') := by
        intro ts' ts'_mem
        cases ts with
        | nil => simp [arguments_for_pre_term_list] at ts'_mem; rw [ts'_mem]; simp [FiniteTreeList.fromList, PreGroundTerm.arity_ok_list]
        | cons hd tl =>
          unfold PreGroundTerm.arity_ok_list at arity_ok
          rw [Bool.and_eq_true] at arity_ok
          unfold arguments_for_pre_term_list at ts'_mem
          simp only [List.mem_flatMap, List.mem_map] at ts'_mem
          rcases ts'_mem with ⟨arg_hd, arg_hd_mem, arg_tl, arg_tl_mem, ts'_eq⟩
          rw [← ts'_eq]
          unfold FiniteTreeList.fromList
          unfold PreGroundTerm.arity_ok_list
          rw [Bool.and_eq_true]
          constructor
          . apply g.arguments_for_pre_term_arity_ok possible_constants hd _ _ arg_hd_mem
            exact arity_ok.left
          . apply g.arguments_for_pre_term_list_arity_ok possible_constants tl _ _ arg_tl_mem
            exact arity_ok.right

    end

    def arguments_for_term_list (g : StrictConstantMapping sig) (possible_constants : List sig.C) (ts : List (GroundTerm sig)) : List (List (GroundTerm sig)) :=
      (g.arguments_for_pre_term_list possible_constants (FiniteTreeList.fromList ts.unattach)).attach.map (fun ⟨ts', mem⟩ =>
        have arity_ok := g.arguments_for_pre_term_list_arity_ok possible_constants (FiniteTreeList.fromList ts.unattach) (by
          rw [← PreGroundTerm.arity_ok_list_iff_arity_ok_each_mem]
          intro t t_mem
          rw [FiniteTreeList.fromListToListIsId] at t_mem
          unfold List.unattach at t_mem
          rw [List.mem_map] at t_mem
          rcases t_mem with ⟨t', _, t_eq⟩
          rw [← t_eq]
          exact t'.property
        ) ts' mem

        ts'.attach.map (fun ⟨t, mem⟩ =>
          ⟨t, by
            rw [← PreGroundTerm.arity_ok_list_iff_arity_ok_each_mem] at arity_ok
            apply arity_ok
            rw [FiniteTreeList.fromListToListIsId]
            exact mem
          ⟩
        )
      )

    theorem apply_to_arguments_yields_original_term_list (g : StrictConstantMapping sig) (possible_constants : List sig.C) (ts : List (GroundTerm sig)) :
        ∀ args, args ∈ g.arguments_for_term_list possible_constants ts ↔ ((∀ c, c ∈ (args.flatMap GroundTerm.constants) -> c ∈ possible_constants) ∧ (args.map (fun arg => g.toConstantMapping.apply_ground_term arg) = ts)) := by
      intro args

      have := g.apply_to_arguments_yields_original_pre_term_list possible_constants (FiniteTreeList.fromList ts.unattach)

      unfold arguments_for_term_list
      constructor
      . intro h
        simp at h
        rcases h with ⟨args', h, eq⟩
        rw [← List.pmap_eq_map_attach] at eq
        rw [← eq]

        rw [this] at h
        rw [FiniteTree.mapLeavesList_fromList_eq_fromList_map] at h
        rw [← FiniteTreeList.eqIffFromListEq] at h
        constructor
        . intro c c_mem
          rw [List.mem_flatMap] at c_mem
          rcases c_mem with ⟨t, t_mem, c_mem⟩
          rw [List.mem_pmap] at t_mem
          rcases t_mem with ⟨t, t_mem, eq⟩
          unfold GroundTerm.constants at c_mem
          rw [← eq] at c_mem
          apply h.left
          rw [FiniteTree.mem_leavesList]
          exists t
          constructor
          . rw [FiniteTreeList.fromListToListIsId]; exact t_mem
          . exact c_mem
        . rw [← List.eq_iff_unattach_eq]
          simp only [← h.right]
          unfold ConstantMapping.apply_ground_term
          unfold ConstantMapping.apply_pre_ground_term
          rw [List.map_pmap]
          unfold List.unattach
          rw [List.map_pmap]
          rw [List.pmap_eq_map]
      . intro h
        simp
        exists args.unattach
        exists (by
          rw [this]
          constructor
          . intro c c_mem
            rw [FiniteTree.mem_leavesList] at c_mem
            rcases c_mem with ⟨t, t_mem, c_mem⟩
            rw [FiniteTreeList.fromListToListIsId] at t_mem
            unfold List.unattach at t_mem
            rw [List.mem_map] at t_mem
            rcases t_mem with ⟨t', t'_mem, t_mem⟩
            apply h.left
            rw [List.mem_flatMap]
            exists t'
            constructor
            . exact t'_mem
            . unfold GroundTerm.constants
              rw [← t_mem] at c_mem
              exact c_mem
          . rw [← h.right]
            rw [FiniteTree.mapLeavesList_fromList_eq_fromList_map]
            rw [← FiniteTreeList.eqIffFromListEq]
            unfold ConstantMapping.apply_ground_term
            unfold ConstantMapping.apply_pre_ground_term
            unfold List.unattach
            simp
        )
        rw [← List.pmap_eq_map_attach]
        rw [← List.eq_iff_unattach_eq]
        unfold List.unattach
        rw [List.map_pmap]
        rw [List.pmap_eq_map]
        simp

    variable [DecidableEq sig.P]

    def arguments_for_fact (g : StrictConstantMapping sig) (possible_constants : List sig.C) (f : Fact sig) : List (Fact sig) :=
      (g.arguments_for_term_list possible_constants f.terms).attach.map (fun ⟨ts, mem⟩ =>
        {
          predicate := f.predicate
          terms := ts
          arity_ok := by
            unfold arguments_for_term_list at mem
            rw [List.mem_map] at mem
            rcases mem with ⟨ts', ts'_mem, ts_eq⟩
            rw [← ts_eq]
            simp only [List.length_map, List.length_attach]
            rw [g.arguments_for_pre_term_list_length_preserved possible_constants (FiniteTreeList.fromList f.terms.unattach) ts'.val _]
            . rw [FiniteTreeList.fromListToListIsId, List.length_unattach]
              exact f.arity_ok
            . unfold List.attach at ts'_mem
              unfold List.attachWith at ts'_mem
              rw [List.mem_pmap] at ts'_mem
              rcases ts'_mem with ⟨_, ts'_mem, eq⟩
              rw [← eq]
              exact ts'_mem
        }
      )

    theorem apply_to_arguments_yields_original_fact (g : StrictConstantMapping sig) (possible_constants : List sig.C) (f : Fact sig) :
        ∀ arg, arg ∈ g.arguments_for_fact possible_constants f ↔ ((∀ c, c ∈ arg.constants -> c ∈ possible_constants) ∧ g.toConstantMapping.apply_fact arg = f) := by
      intro arg
      unfold arguments_for_fact
      simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]

      have := g.apply_to_arguments_yields_original_term_list possible_constants f.terms

      constructor
      . intro h
        rcases h with ⟨ts, mem, arg_eq⟩
        rw [← arg_eq]
        unfold ConstantMapping.apply_fact
        rw [Fact.mk.injEq]
        simp only [true_and]

        specialize this ts
        rw [this] at mem
        exact mem
      . intro h
        specialize this arg.terms
        exists arg.terms
        exists (by
          apply this.mpr
          constructor
          . exact h.left
          . have r := h.right
            unfold ConstantMapping.apply_fact at r
            rw [Fact.mk.injEq] at r
            exact r.right
        )
        have r := h.right
        unfold ConstantMapping.apply_fact at r
        rw [Fact.mk.injEq] at r
        rw [Fact.mk.injEq]
        constructor
        . rw [← r.left]
        . rfl

  end StrictConstantMapping

end ArgumentsForImages

section SkolemTermValidityPreserved

  namespace StrictConstantMapping

    variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P]

    mutual

      theorem apply_pre_ground_term_preserves_ruleId_validity (g : StrictConstantMapping sig) (term : FiniteTree (SkolemFS sig) sig.C) :
          ∀ rl, PreGroundTerm.skolem_ruleIds_valid rl term -> PreGroundTerm.skolem_ruleIds_valid rl (g.toConstantMapping.apply_pre_ground_term term) := by
        intro rl valid
        cases term with
        | leaf _ => simp [PreGroundTerm.skolem_ruleIds_valid, StrictConstantMapping.toConstantMapping, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, GroundTerm.const]
        | inner func ts =>
          simp only [PreGroundTerm.skolem_ruleIds_valid, StrictConstantMapping.toConstantMapping, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves]
          simp only [PreGroundTerm.skolem_ruleIds_valid] at valid
          constructor
          . exact valid.left
          . rw [← ts.toListFromListIsId, FiniteTree.mapLeavesList_fromList_eq_fromList_map]
            apply apply_pre_ground_term_preserves_ruleId_validity_list
            exact valid.right

      theorem apply_pre_ground_term_preserves_ruleId_validity_list (g : StrictConstantMapping sig) (terms : FiniteTreeList (SkolemFS sig) sig.C) :
          ∀ rl, PreGroundTerm.skolem_ruleIds_valid_list rl terms -> PreGroundTerm.skolem_ruleIds_valid_list rl (FiniteTreeList.fromList (terms.toList.map (fun t => g.toConstantMapping.apply_pre_ground_term t))) := by
        intro rl valid
        cases terms with
        | nil =>
          simp only [StrictConstantMapping.toConstantMapping, ConstantMapping.apply_pre_ground_term]
          rw [← FiniteTree.mapLeavesList_fromList_eq_fromList_map, FiniteTreeList.toListFromListIsId]
          simp [FiniteTree.mapLeavesList, PreGroundTerm.skolem_ruleIds_valid_list]
        | cons hd tl =>
          simp only [StrictConstantMapping.toConstantMapping, ConstantMapping.apply_pre_ground_term]
          rw [← FiniteTree.mapLeavesList_fromList_eq_fromList_map, FiniteTreeList.toListFromListIsId]
          simp only [FiniteTree.mapLeavesList, PreGroundTerm.skolem_ruleIds_valid_list]
          simp only [PreGroundTerm.skolem_ruleIds_valid_list] at valid
          constructor
          . apply apply_pre_ground_term_preserves_ruleId_validity; exact valid.left
          . rw [← tl.toListFromListIsId, FiniteTree.mapLeavesList_fromList_eq_fromList_map]
            apply apply_pre_ground_term_preserves_ruleId_validity_list
            exact valid.right

    end

    mutual

      theorem apply_pre_ground_term_preserves_disjIdx_validity (g : StrictConstantMapping sig) (term : FiniteTree (SkolemFS sig) sig.C) :
          ∀ rl, (h : PreGroundTerm.skolem_ruleIds_valid rl term) -> PreGroundTerm.skolem_disjIdx_valid rl term h -> PreGroundTerm.skolem_disjIdx_valid rl (g.toConstantMapping.apply_pre_ground_term term) (g.apply_pre_ground_term_preserves_ruleId_validity term rl h) := by
        intro rl _ valid
        cases term with
        | leaf _ => simp [PreGroundTerm.skolem_disjIdx_valid, StrictConstantMapping.toConstantMapping, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, GroundTerm.const]
        | inner func ts =>
          simp only [PreGroundTerm.skolem_disjIdx_valid, StrictConstantMapping.toConstantMapping, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves]
          simp only [PreGroundTerm.skolem_disjIdx_valid] at valid
          constructor
          . exact valid.left
          . conv => left; rw [← ts.toListFromListIsId, FiniteTree.mapLeavesList_fromList_eq_fromList_map]
            apply apply_pre_ground_term_preserves_disjIdx_validity_list
            exact valid.right

      theorem apply_pre_ground_term_preserves_disjIdx_validity_list (g : StrictConstantMapping sig) (terms : FiniteTreeList (SkolemFS sig) sig.C) :
          ∀ rl, (h : PreGroundTerm.skolem_ruleIds_valid_list rl terms) -> PreGroundTerm.skolem_disjIdx_valid_list rl terms h -> PreGroundTerm.skolem_disjIdx_valid_list rl (FiniteTreeList.fromList (terms.toList.map (fun t => g.toConstantMapping.apply_pre_ground_term t))) (g.apply_pre_ground_term_preserves_ruleId_validity_list terms rl h) := by
        intro rl _ valid
        cases terms with
        | nil =>
          simp only [StrictConstantMapping.toConstantMapping, ConstantMapping.apply_pre_ground_term]
          simp only [← FiniteTree.mapLeavesList_fromList_eq_fromList_map, FiniteTreeList.toListFromListIsId]
          simp [FiniteTree.mapLeavesList, PreGroundTerm.skolem_disjIdx_valid_list]
        | cons hd tl =>
          simp only [StrictConstantMapping.toConstantMapping, ConstantMapping.apply_pre_ground_term]
          simp only [← FiniteTree.mapLeavesList_fromList_eq_fromList_map, FiniteTreeList.toListFromListIsId]
          simp only [FiniteTree.mapLeavesList, PreGroundTerm.skolem_ruleIds_valid_list]
          simp only [PreGroundTerm.skolem_disjIdx_valid_list] at valid
          constructor
          . apply apply_pre_ground_term_preserves_disjIdx_validity; exact valid.left
          . conv => left; rw [← tl.toListFromListIsId, FiniteTree.mapLeavesList_fromList_eq_fromList_map]
            apply apply_pre_ground_term_preserves_disjIdx_validity_list
            exact valid.right

    end

    mutual

      theorem apply_pre_ground_term_preserves_rule_arity_validity (g : StrictConstantMapping sig) (term : FiniteTree (SkolemFS sig) sig.C) :
          ∀ rl, (h : PreGroundTerm.skolem_ruleIds_valid rl term) -> PreGroundTerm.skolem_rule_arity_valid rl term h -> PreGroundTerm.skolem_rule_arity_valid rl (g.toConstantMapping.apply_pre_ground_term term) (g.apply_pre_ground_term_preserves_ruleId_validity term rl h) := by
        intro rl _ valid
        cases term with
        | leaf _ => simp [PreGroundTerm.skolem_rule_arity_valid, StrictConstantMapping.toConstantMapping, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, GroundTerm.const]
        | inner func ts =>
          simp only [PreGroundTerm.skolem_rule_arity_valid, StrictConstantMapping.toConstantMapping, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves]
          simp only [PreGroundTerm.skolem_rule_arity_valid] at valid
          constructor
          . exact valid.left
          . conv => left; rw [← ts.toListFromListIsId, FiniteTree.mapLeavesList_fromList_eq_fromList_map]
            apply apply_pre_ground_term_preserves_rule_arity_validity_list
            exact valid.right

      theorem apply_pre_ground_term_preserves_rule_arity_validity_list (g : StrictConstantMapping sig) (terms : FiniteTreeList (SkolemFS sig) sig.C) :
          ∀ rl, (h : PreGroundTerm.skolem_ruleIds_valid_list rl terms) -> PreGroundTerm.skolem_rule_arity_valid_list rl terms h -> PreGroundTerm.skolem_rule_arity_valid_list rl (FiniteTreeList.fromList (terms.toList.map (fun t => g.toConstantMapping.apply_pre_ground_term t))) (g.apply_pre_ground_term_preserves_ruleId_validity_list terms rl h) := by
        intro rl _ valid
        cases terms with
        | nil =>
          simp only [StrictConstantMapping.toConstantMapping, ConstantMapping.apply_pre_ground_term]
          simp only [← FiniteTree.mapLeavesList_fromList_eq_fromList_map, FiniteTreeList.toListFromListIsId]
          simp [FiniteTree.mapLeavesList, PreGroundTerm.skolem_rule_arity_valid_list]
        | cons hd tl =>
          simp only [StrictConstantMapping.toConstantMapping, ConstantMapping.apply_pre_ground_term]
          simp only [← FiniteTree.mapLeavesList_fromList_eq_fromList_map, FiniteTreeList.toListFromListIsId]
          simp only [FiniteTree.mapLeavesList, PreGroundTerm.skolem_ruleIds_valid_list]
          simp only [PreGroundTerm.skolem_rule_arity_valid_list] at valid
          constructor
          . apply apply_pre_ground_term_preserves_rule_arity_validity; exact valid.left
          . conv => left; rw [← tl.toListFromListIsId, FiniteTree.mapLeavesList_fromList_eq_fromList_map]
            apply apply_pre_ground_term_preserves_rule_arity_validity_list
            exact valid.right

    end

    theorem apply_ground_term_preserves_ruleId_validity (g : StrictConstantMapping sig) (term : GroundTerm sig) :
        ∀ rl, GroundTerm.skolem_ruleIds_valid rl term -> GroundTerm.skolem_ruleIds_valid rl (g.toConstantMapping.apply_ground_term term) := by
      intro rl valid
      apply apply_pre_ground_term_preserves_ruleId_validity
      exact valid

    theorem apply_ground_term_preserves_disjIdx_validity (g : StrictConstantMapping sig) (term : GroundTerm sig) :
        ∀ rl, (h : GroundTerm.skolem_ruleIds_valid rl term) -> GroundTerm.skolem_disjIdx_valid rl term h -> GroundTerm.skolem_disjIdx_valid rl (g.toConstantMapping.apply_ground_term term) (g.apply_ground_term_preserves_ruleId_validity term rl h) := by
      intro rl _ valid
      apply apply_pre_ground_term_preserves_disjIdx_validity
      exact valid

    theorem apply_ground_term_preserves_rule_arity_validity (g : StrictConstantMapping sig) (term : GroundTerm sig) :
        ∀ rl, (h : GroundTerm.skolem_ruleIds_valid rl term) -> GroundTerm.skolem_rule_arity_valid rl term h -> GroundTerm.skolem_rule_arity_valid rl (g.toConstantMapping.apply_ground_term term) (g.apply_ground_term_preserves_ruleId_validity term rl h) := by
      intro rl _ valid
      apply apply_pre_ground_term_preserves_rule_arity_validity
      exact valid

  end StrictConstantMapping

  namespace PreTrigger

    variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P]

    theorem compose_strict_constant_mapping_preserves_ruleId_validity (trg : PreTrigger sig) (g : StrictConstantMapping sig) :
        ∀ rl, trg.skolem_ruleIds_valid rl -> {rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ trg.subs : PreTrigger sig}.skolem_ruleIds_valid rl := by
      intro rl valid
      intro t t_mem
      rw [PreTrigger.mem_terms_mapped_body_iff] at t_mem
      cases t_mem with
      | inl t_mem =>
        rcases t_mem with ⟨c, c_mem, t_eq⟩
        simp only [← t_eq]
        apply GroundTerm.skolem_ruleIds_valid_const
      | inr t_mem =>
        rcases t_mem with ⟨v, v_mem, t_eq⟩
        simp only [← t_eq]
        apply StrictConstantMapping.apply_ground_term_preserves_ruleId_validity
        apply valid
        rw [PreTrigger.mem_terms_mapped_body_iff]
        apply Or.inr
        exists v

    theorem compose_strict_constant_mapping_preserves_disjIdx_validity (trg : PreTrigger sig) (g : StrictConstantMapping sig) :
        ∀ rl, (h : trg.skolem_ruleIds_valid rl) -> trg.skolem_disjIdx_valid rl h -> {rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ trg.subs : PreTrigger sig}.skolem_disjIdx_valid rl (trg.compose_strict_constant_mapping_preserves_ruleId_validity g rl h) := by
      intro rl _ valid
      intro t t_mem
      rw [PreTrigger.mem_terms_mapped_body_iff] at t_mem
      cases t_mem with
      | inl t_mem =>
        rcases t_mem with ⟨c, c_mem, t_eq⟩
        simp only [← t_eq]
        apply GroundTerm.skolem_disjIdx_valid_const
      | inr t_mem =>
        rcases t_mem with ⟨v, v_mem, t_eq⟩
        simp only [← t_eq]
        apply StrictConstantMapping.apply_ground_term_preserves_disjIdx_validity
        apply valid
        rw [PreTrigger.mem_terms_mapped_body_iff]
        apply Or.inr
        exists v

    theorem compose_strict_constant_mapping_preserves_rule_arity_validity (trg : PreTrigger sig) (g : StrictConstantMapping sig) :
        ∀ rl, (h : trg.skolem_ruleIds_valid rl) -> trg.skolem_rule_arity_valid rl h -> {rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ trg.subs : PreTrigger sig}.skolem_rule_arity_valid rl (trg.compose_strict_constant_mapping_preserves_ruleId_validity g rl h) := by
      intro rl _ valid
      intro t t_mem
      rw [PreTrigger.mem_terms_mapped_body_iff] at t_mem
      cases t_mem with
      | inl t_mem =>
        rcases t_mem with ⟨c, c_mem, t_eq⟩
        simp only [← t_eq]
        apply GroundTerm.skolem_rule_arity_valid_const
      | inr t_mem =>
        rcases t_mem with ⟨v, v_mem, t_eq⟩
        simp only [← t_eq]
        apply StrictConstantMapping.apply_ground_term_preserves_rule_arity_validity
        apply valid
        rw [PreTrigger.mem_terms_mapped_body_iff]
        apply Or.inr
        exists v

  end PreTrigger

end SkolemTermValidityPreserved

section InterplayWithRenamingConstantsApart

  variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

  namespace PreGroundTerm

    mutual

      def same_skeleton (term term2 : FiniteTree (SkolemFS sig) sig.C) : Prop :=
        match term with
        | .leaf _ => match term2 with | .leaf _ => True | .inner _ _ => False
        | .inner func ts => match term2 with | .leaf _ => False | .inner func' ts' => func = func' ∧ same_skeleton_list ts ts'

      def same_skeleton_list (terms terms2 : FiniteTreeList (SkolemFS sig) sig.C) : Prop :=
        match terms with
        | .nil => match terms2 with | .nil => True | .cons _ _ => False
        | .cons hd tl => match terms2 with | .nil => False | .cons hd' tl' => same_skeleton hd hd' ∧ same_skeleton_list tl tl'

    end

    mutual

      def same_skeleton_refl (term : FiniteTree (SkolemFS sig) sig.C) : same_skeleton term term := by
        cases term with
        | leaf => simp [same_skeleton]
        | inner func ts => simp only [same_skeleton, true_and]; apply same_skeleton_list_refl

      def same_skeleton_list_refl (terms : FiniteTreeList (SkolemFS sig) sig.C) : same_skeleton_list terms terms := by
        cases terms with
        | nil => simp [same_skeleton_list]
        | cons hd tl => simp only [same_skeleton_list]; constructor; apply same_skeleton_refl; apply same_skeleton_list_refl

    end

    mutual

      def same_skeleton_under_strict_constant_mapping (term : FiniteTree (SkolemFS sig) sig.C) (g : StrictConstantMapping sig) : same_skeleton term (g.toConstantMapping.apply_pre_ground_term term) := by
        cases term with
        | leaf => simp [same_skeleton, ConstantMapping.apply_pre_ground_term, StrictConstantMapping.toConstantMapping, GroundTerm.const, FiniteTree.mapLeaves]
        | inner func ts => simp only [same_skeleton, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, true_and]; apply same_skeleton_list_under_strict_constant_mapping

      def same_skeleton_list_under_strict_constant_mapping (terms : FiniteTreeList (SkolemFS sig) sig.C) (g : StrictConstantMapping sig) : same_skeleton_list terms (FiniteTree.mapLeavesList (fun c => (g.toConstantMapping c).val) terms) := by
        cases terms with
        | nil => simp [same_skeleton_list, FiniteTree.mapLeavesList]
        | cons hd tl => simp only [same_skeleton_list, FiniteTree.mapLeavesList]; constructor; apply same_skeleton_under_strict_constant_mapping; apply same_skeleton_list_under_strict_constant_mapping

    end

    mutual

      theorem exists_strict_constant_mapping_to_reverse_renaming [GetFreshRepresentant sig.C] (term term2 : FiniteTree (SkolemFS sig) sig.C) (terms_same_skeleton : same_skeleton term term2) (forbidden_constants : List sig.C) :
          ∃ (g : StrictConstantMapping sig),
            g.toConstantMapping.apply_pre_ground_term (PreGroundTerm.rename_constants_apart term forbidden_constants) = term2 ∧
            (∀ d, d ∉ (PreGroundTerm.rename_constants_apart term forbidden_constants).leaves -> g d = d) := by
        cases term with
        | leaf c =>
          cases term2 with
          | leaf c' =>
            exists (fun d => if GetFreshRepresentant.fresh forbidden_constants = d then c' else d); simp [PreGroundTerm.rename_constants_apart, StrictConstantMapping.toConstantMapping, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, GroundTerm.const]
            simp only [FiniteTree.leaves, List.mem_singleton]
            intro _ contra1 contra2
            rw [contra2] at contra1
            simp at contra1
          | inner _ _ => simp [same_skeleton] at terms_same_skeleton
        | inner func ts =>
          cases term2 with
          | leaf _ => simp [same_skeleton] at terms_same_skeleton
          | inner func' ts' =>
            simp only [same_skeleton] at terms_same_skeleton
            rcases exists_strict_constant_mapping_to_reverse_renaming_list ts ts' terms_same_skeleton.right forbidden_constants with ⟨g, g_eq, g_id⟩
            exists g
            simp only [PreGroundTerm.rename_constants_apart, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves]
            rw [FiniteTree.inner.injEq]
            constructor
            . constructor
              . exact terms_same_skeleton.left
              . rw [← FiniteTreeList.toListFromListIsId (rename_constants_apart_list ts forbidden_constants)]
                rw [FiniteTree.mapLeavesList_fromList_eq_fromList_map]
                unfold ConstantMapping.apply_pre_ground_term at g_eq
                rw [g_eq]
                rw [FiniteTreeList.toListFromListIsId]
            . unfold FiniteTree.leaves; exact g_id

      theorem exists_strict_constant_mapping_to_reverse_renaming_list [GetFreshRepresentant sig.C] (terms terms2 : FiniteTreeList (SkolemFS sig) sig.C) (terms_same_skeleton : same_skeleton_list terms terms2) (forbidden_constants : List sig.C) :
          ∃ (g : StrictConstantMapping sig),
            (PreGroundTerm.rename_constants_apart_list terms forbidden_constants).toList.map (fun term => g.toConstantMapping.apply_pre_ground_term term) = terms2.toList ∧
            (∀ d, d ∉ FiniteTree.leavesList (PreGroundTerm.rename_constants_apart_list terms forbidden_constants) -> g d = d) := by
        cases terms with
        | nil =>
          cases terms2 with
          | nil => exists id; simp [FiniteTreeList.toList, rename_constants_apart_list]
          | cons _ _ => simp [same_skeleton_list] at terms_same_skeleton
        | cons hd tl =>
          cases terms2 with
          | nil => simp [same_skeleton_list] at terms_same_skeleton
          | cons hd' tl' =>
            simp only [same_skeleton_list] at terms_same_skeleton
            let hd_res := PreGroundTerm.rename_constants_apart hd forbidden_constants

            rcases exists_strict_constant_mapping_to_reverse_renaming hd hd' terms_same_skeleton.left forbidden_constants with ⟨h, h_eq, h_id⟩

            rcases exists_strict_constant_mapping_to_reverse_renaming_list tl tl' terms_same_skeleton.right (forbidden_constants ++ hd_res.leaves) with ⟨g, g_eq, g_id⟩

            exists (fun d => if d ∈ hd_res.leaves then h d else g d)
            simp only [rename_constants_apart_list, FiniteTreeList.toList]
            rw [List.map_cons, List.cons_eq_cons]
            constructor
            . constructor
              . conv => right; rw [← h_eq]
                unfold ConstantMapping.apply_pre_ground_term
                apply FiniteTree.mapLeavesEqIfMapEqOnLeaves
                rw [List.map_inj_left]
                intro d d_mem
                simp [StrictConstantMapping.toConstantMapping, GroundTerm.const, hd_res, d_mem]
              . conv => right; rw [← g_eq]
                rw [List.map_inj_left]
                intro t t_mem
                unfold ConstantMapping.apply_pre_ground_term
                apply FiniteTree.mapLeavesEqIfMapEqOnLeaves
                rw [List.map_inj_left]
                intro d d_mem
                have : d ∈ FiniteTree.leavesList (rename_constants_apart_list tl (forbidden_constants ++ hd_res.leaves)) := by
                  rw [FiniteTree.mem_leavesList]
                  exists t
                have : ¬ d ∈ hd_res.leaves := by
                  intro contra
                  apply rename_constants_apart_leaves_fresh_list _ _ _ this
                  simp [contra]
                simp [StrictConstantMapping.toConstantMapping, GroundTerm.const, this]
            . unfold FiniteTree.leavesList
              intro d d_mem
              rw [List.mem_append] at d_mem
              cases Decidable.em (d ∈ hd_res.leaves) with
              | inl d_mem' => apply False.elim; apply d_mem; apply Or.inl; exact d_mem'
              | inr d_mem' => simp only [d_mem', ↓reduceIte]; apply g_id; intro contra; apply d_mem; apply Or.inr; exact contra

    end

  end PreGroundTerm

  namespace GroundTerm

    def same_skeleton (term term2 : GroundTerm sig) : Prop := PreGroundTerm.same_skeleton term.val term2.val

    theorem same_skeleton_refl (term : GroundTerm sig) : term.same_skeleton term := by unfold same_skeleton; apply PreGroundTerm.same_skeleton_refl

    theorem same_skeleton_under_strict_constant_mapping (term : GroundTerm sig) (g : StrictConstantMapping sig) : term.same_skeleton (g.toConstantMapping.apply_ground_term term) := by unfold same_skeleton; apply PreGroundTerm.same_skeleton_under_strict_constant_mapping

    theorem exists_strict_constant_mapping_to_reverse_renaming [GetFreshRepresentant sig.C] (term term2 : GroundTerm sig) (terms_same_skeleton : same_skeleton term term2) (forbidden_constants : List sig.C) :
        ∃ (g : StrictConstantMapping sig),
          g.toConstantMapping.apply_ground_term (term.rename_constants_apart forbidden_constants) = term2 ∧
          (∀ d, d ∉ (term.rename_constants_apart forbidden_constants).constants -> g d = d) := by
      unfold rename_constants_apart
      unfold ConstantMapping.apply_ground_term
      rcases PreGroundTerm.exists_strict_constant_mapping_to_reverse_renaming term.val term2.val terms_same_skeleton forbidden_constants with ⟨g, g_eq⟩
      exists g
      rw [Subtype.mk.injEq]
      exact g_eq

  end GroundTerm

  namespace GroundSubstitution

    def same_skeleton_for_vars (subs subs2 : GroundSubstitution sig) : List sig.V -> Prop
    | .nil => True
    | .cons hd tl => (subs hd).same_skeleton (subs2 hd) ∧ subs.same_skeleton_for_vars subs2 tl

    theorem same_skeleton_for_vars_refl (subs : GroundSubstitution sig) (vars : List sig.V) : subs.same_skeleton_for_vars subs vars := by
      induction vars with
      | nil => simp [same_skeleton_for_vars]
      | cons hd tl ih => unfold same_skeleton_for_vars; constructor; apply GroundTerm.same_skeleton_refl; exact ih

    theorem same_skeleton_for_vars_under_strict_constant_mapping (subs : GroundSubstitution sig) (vars : List sig.V) (g : StrictConstantMapping sig) : subs.same_skeleton_for_vars (g.toConstantMapping.apply_ground_term ∘ subs) vars := by
      induction vars with
      | nil => simp [same_skeleton_for_vars]
      | cons hd tl ih => unfold same_skeleton_for_vars; constructor; apply GroundTerm.same_skeleton_under_strict_constant_mapping; exact ih

    -- NOTE: induction over vars for rename_constants_apart_for_vars does not work nicely without assuming that the vars do not contain duplicates
    theorem exists_strict_constant_mapping_to_reverse_renaming_for_vars [GetFreshRepresentant sig.C] (subs subs2 : GroundSubstitution sig) (vars : List sig.V) (vars_nodup : vars.Nodup) (subs_same_skeleton : same_skeleton_for_vars subs subs2 vars) (forbidden_constants : List sig.C) :
        ∃ (g : StrictConstantMapping sig),
          (∀ v ∈ vars, g.toConstantMapping.apply_ground_term (subs.rename_constants_apart_for_vars forbidden_constants vars v) = subs2 v) ∧
          (∀ d, d ∉ ((vars.map (subs.rename_constants_apart_for_vars forbidden_constants vars)).flatMap GroundTerm.constants) -> g d = d) := by
      induction vars generalizing forbidden_constants with
      | nil => exists id; simp
      | cons hd tl ih =>
        simp only [same_skeleton_for_vars] at subs_same_skeleton
        have g_ex_hd := GroundTerm.exists_strict_constant_mapping_to_reverse_renaming (subs hd) (subs2 hd) subs_same_skeleton.left forbidden_constants
        rcases g_ex_hd with ⟨g_hd, g_hd_h⟩

        let renamed_term_for_hd := (subs hd).rename_constants_apart forbidden_constants
        let new_forbidden := forbidden_constants ++ renamed_term_for_hd.constants
        have g_ex_tl := ih (List.nodup_cons.mp vars_nodup).right subs_same_skeleton.right new_forbidden
        rcases g_ex_tl with ⟨g_tl, g_tl_h⟩

        let g : StrictConstantMapping sig := fun d =>
          if d ∈ renamed_term_for_hd.constants then g_hd d else g_tl d

        have g_aux : g.toConstantMapping.apply_ground_term renamed_term_for_hd = g_hd.toConstantMapping.apply_ground_term renamed_term_for_hd := by
          simp only [g, StrictConstantMapping.toConstantMapping, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, Subtype.mk.injEq]
          apply FiniteTree.mapLeavesEqIfMapEqOnLeaves
          rw [List.map_inj_left]
          intro d d_mem
          simp only [GroundTerm.const]
          simp [GroundTerm.constants, d_mem]

        have g_aux2 : ∀ v ∈ tl, g.toConstantMapping.apply_ground_term (subs.rename_constants_apart_for_vars new_forbidden tl v) = g_tl.toConstantMapping.apply_ground_term (subs.rename_constants_apart_for_vars new_forbidden tl v) := by
          intro v v_mem
          simp only [g, StrictConstantMapping.toConstantMapping, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, Subtype.mk.injEq]
          apply FiniteTree.mapLeavesEqIfMapEqOnLeaves
          rw [List.map_inj_left]
          intro d d_mem
          simp only [GroundTerm.const]
          have d_nmem : d ∉ renamed_term_for_hd.constants := by
            have : d ∉ new_forbidden := by
              apply subs.rename_constants_apart_for_vars_constants_fresh new_forbidden tl v v_mem
              exact d_mem
            intro contra
            apply this
            simp [new_forbidden, contra]
          simp [d_nmem]

        exists g
        constructor
        . intro v v_mem
          rw [List.mem_cons] at v_mem
          unfold rename_constants_apart_for_vars
          cases Decidable.em (v = hd) with
          | inl v_eq_hd =>
            simp only [v_eq_hd, ↓reduceIte]
            rw [g_aux]
            exact g_hd_h.left
          | inr v_neq_hd =>
            have v_mem : v ∈ tl := by cases v_mem; contradiction; assumption
            simp only [v_neq_hd, ↓reduceIte]
            rw [g_aux2 _ v_mem]
            exact g_tl_h.left _ v_mem
        . intro d d_nmem
          simp only [rename_constants_apart_for_vars, List.map_cons, List.flatMap_cons, ↓reduceIte] at d_nmem
          have : d ∉ renamed_term_for_hd.constants := by
            intro contra
            apply d_nmem
            rw [List.mem_append]
            apply Or.inl
            exact contra
          simp only [g, this, ↓reduceIte]
          apply g_tl_h.right
          intro contra
          apply d_nmem
          rw [List.mem_append]
          apply Or.inr

          rw [List.mem_flatMap] at contra
          rcases contra with ⟨t, t_mem, d_mem⟩
          rw [List.mem_map] at t_mem
          rcases t_mem with ⟨v, v_mem, t_eq⟩
          have v_neq : v ≠ hd := by
            intro contra
            apply (List.nodup_cons.mp vars_nodup).left
            rw [← contra]
            exact v_mem
          rw [List.mem_flatMap]
          exists t
          constructor
          . rw [List.mem_map]
            exists v
            constructor
            . exact v_mem
            . simp only [v_neq, ↓reduceIte]
              rw [← t_eq]
          . exact d_mem

  end GroundSubstitution

  variable [DecidableEq sig.P]

  namespace PreTrigger

    def same_skeleton (trg trg2 : PreTrigger sig) : Prop :=
      trg.rule = trg2.rule ∧
      trg.subs.same_skeleton_for_vars trg2.subs trg.rule.body.vars.eraseDupsKeepRight

    theorem same_skeleton_refl (trg : PreTrigger sig) : trg.same_skeleton trg := by unfold same_skeleton; simp [GroundSubstitution.same_skeleton_for_vars_refl]

    theorem same_skeleton_symm (trg trg2 : PreTrigger sig) : trg.same_skeleton trg2 -> trg2.same_skeleton trg := by sorry

    -- TODO: also show transitivity (but I think as of now we do not need it)

    theorem same_skeleton_under_strict_constant_mapping (trg : PreTrigger sig) (g : StrictConstantMapping sig) : trg.same_skeleton {rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ trg.subs} := by
      unfold same_skeleton
      simp [GroundSubstitution.same_skeleton_for_vars_under_strict_constant_mapping]

    theorem exists_strict_constant_mapping_to_reverse_renaming [GetFreshRepresentant sig.C] (trg trg2 : PreTrigger sig) (trgs_same_skeleton : same_skeleton trg trg2) (forbidden_constants : List sig.C) :
        ∃ (g : StrictConstantMapping sig),
          { rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ (trg.rename_constants_apart forbidden_constants).subs : PreTrigger sig }.strong_equiv trg2 ∧
          (∀ d, d ∉ ((trg.rename_constants_apart forbidden_constants).mapped_body.flatMap Fact.constants) -> g d = d) := by
      rcases trg.subs.exists_strict_constant_mapping_to_reverse_renaming_for_vars trg2.subs trg.rule.body.vars.eraseDupsKeepRight trg.rule.body.vars.nodup_eraseDupsKeepRight trgs_same_skeleton.right forbidden_constants with ⟨g, g_h⟩
      exists g
      constructor
      . constructor
        . exact trgs_same_skeleton.left
        . intro v v_mem
          simp only [rename_constants_apart, Function.comp_apply]
          apply g_h.left
          rw [List.mem_eraseDupsKeepRight]
          exact v_mem
      . intro d d_nmem
        apply g_h.right
        intro d_mem
        apply d_nmem
        rw [List.mem_flatMap] at d_mem
        rcases d_mem with ⟨t, t_mem, d_mem⟩
        rw [List.mem_map] at t_mem
        rcases t_mem with ⟨v, v_mem, t_eq⟩
        rw [List.mem_eraseDupsKeepRight] at v_mem
        unfold FunctionFreeConjunction.vars at v_mem
        rw [List.mem_flatMap] at v_mem
        rcases v_mem with ⟨a, a_mem, v_mem⟩
        rw [List.mem_flatMap]
        exists (trg.rename_constants_apart forbidden_constants).subs.apply_function_free_atom a
        constructor
        . apply List.mem_map_of_mem; exact a_mem
        . simp only [rename_constants_apart, GroundSubstitution.apply_function_free_atom, Fact.constants]
          rw [List.mem_flatMap]
          exists t
          constructor
          . rw [List.mem_map]
            exists VarOrConst.var v
            constructor
            . apply VarOrConst.filterVars_occur_in_original_list; exact v_mem
            . rw [← t_eq]; simp [GroundSubstitution.apply_var_or_const]
          . exact d_mem

  end PreTrigger


end InterplayWithRenamingConstantsApart

section InterplayWithObsoletenessCondition

  variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P]

  -- we want to assume this property for obsoleteness conditions for MFA
  def ObsoletenessCondition.propagates_under_constant_mapping (obs : ObsoletenessCondition sig) : Prop := ∀ {trg : PreTrigger sig} {fs : FactSet sig} {g : ConstantMapping sig}, (∀ c ∈ trg.rule.head_constants, g c = GroundTerm.const c) -> obs.cond trg fs -> obs.cond { rule := trg.rule, subs := g.apply_ground_term ∘ trg.subs } (g.apply_fact_set fs)

  -- we show in the following that this property indeed holds for skolem and restricted obsoleteness so the condition is not really a restriction

  theorem SkolemObsoleteness.propagates_under_constant_mapping : (SkolemObsoleteness sig).propagates_under_constant_mapping := by
    intro trg fs g g_id cond
    simp only [SkolemObsoleteness] at cond
    simp only [SkolemObsoleteness]
    let trg' : PreTrigger sig := { rule := trg.rule, subs := g.apply_ground_term ∘ trg.subs }
    rcases cond with ⟨i, cond⟩
    let i' : Fin trg'.mapped_head.length := ⟨i.val, by have isLt := i.isLt; simp only [PreTrigger.length_mapped_head] at *; exact isLt⟩
    exists i'
    intro f f_mem
    rw [List.mem_toSet] at f_mem
    unfold PreTrigger.mapped_head at f_mem
    simp only [List.getElem_map, List.getElem_zipIdx, List.mem_map, Nat.zero_add] at f_mem
    rcases f_mem with ⟨a, a_mem, f_eq⟩
    rw [← ConstantMapping.apply_fact_swap_apply_to_function_free_atom] at f_eq
    . rw [← f_eq]
      apply ConstantMapping.apply_fact_mem_apply_fact_set_of_mem
      apply cond
      rw [List.mem_toSet]
      simp only [PreTrigger.mapped_head, List.getElem_map, List.getElem_zipIdx, List.mem_map, Nat.zero_add]
      exists a
    . intro d d_mem
      apply g_id
      unfold Rule.head_constants
      rw [List.mem_flatMap]
      exists trg.rule.head[i.val]'(by rw [← PreTrigger.length_mapped_head]; exact i.isLt)
      constructor
      . apply List.getElem_mem
      . unfold FunctionFreeConjunction.consts
        rw [List.mem_flatMap]
        exists a

  theorem RestrictedObsoleteness.propagates_under_constant_mapping : (RestrictedObsoleteness sig).propagates_under_constant_mapping := by
    intro trg fs g g_id cond
    simp only [RestrictedObsoleteness, PreTrigger.satisfied, PreTrigger.satisfied_for_disj] at cond
    simp only [RestrictedObsoleteness, PreTrigger.satisfied, PreTrigger.satisfied_for_disj]
    let trg' : PreTrigger sig := { rule := trg.rule, subs := g.apply_ground_term ∘ trg.subs }
    rcases cond with ⟨i, cond⟩
    exists i
    rcases cond with ⟨s, id_front, cond⟩
    exists g.apply_ground_term ∘ s
    constructor
    . intro v v_mem; simp only [Function.comp_apply]; rw [id_front v v_mem]
    . unfold GroundSubstitution.apply_function_free_conj
      intro f f_mem
      rw [List.mem_toSet, List.mem_map] at f_mem
      rcases f_mem with ⟨a, a_mem, f_eq⟩
      rw [GroundSubstitution.apply_function_free_atom_compose] at f_eq
      . rw [← f_eq]
        rw [← ConstantMapping.apply_fact_eq_groundTermMapping_applyFact]
        apply ConstantMapping.apply_fact_mem_apply_fact_set_of_mem
        apply cond
        rw [List.mem_toSet]
        unfold GroundSubstitution.apply_function_free_conj
        apply List.mem_map_of_mem
        exact a_mem
      . intro d d_mem
        conv => left; simp only [ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, GroundTerm.const, FiniteTree.mapLeaves]
        apply g_id
        unfold Rule.head_constants
        rw [List.mem_flatMap]
        exists trg.rule.head[i.val]
        constructor
        . apply List.getElem_mem
        . unfold FunctionFreeConjunction.consts
          rw [List.mem_flatMap]
          exists a

end InterplayWithObsoletenessCondition

section InterplayWithBacktracking

  variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P]

  theorem PreTrigger.backtracking_under_constant_mapping_subset_of_composing_with_subs
      [GetFreshRepresentant sig.C]
      [Inhabited sig.C]
      (rl : RuleList sig)
      (trg : PreTrigger sig)
      (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl)
      (trg_disjIdx_valid : trg.skolem_disjIdx_valid rl trg_ruleIds_valid)
      (trg_rule_arity_valid : trg.skolem_rule_arity_valid rl trg_ruleIds_valid) :
      ∀ (g : StrictConstantMapping sig),
        g.toConstantMapping.apply_fact_set (trg.backtrackFacts rl trg_ruleIds_valid trg_disjIdx_valid trg_rule_arity_valid).toSet ⊆
        ({rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ trg.subs : PreTrigger sig}.backtrackFacts rl (trg.compose_strict_constant_mapping_preserves_ruleId_validity g rl trg_ruleIds_valid) (trg.compose_strict_constant_mapping_preserves_disjIdx_validity g rl trg_ruleIds_valid trg_disjIdx_valid) (trg.compose_strict_constant_mapping_preserves_rule_arity_validity g rl trg_ruleIds_valid trg_rule_arity_valid)).toSet := by sorry

end InterplayWithBacktracking

