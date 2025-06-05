import BasicLeanDatastructures.List.Repeat

import ExistentialRules.ChaseSequence.Termination.Basic
import ExistentialRules.ChaseSequence.Termination.BacktrackingOfFacts
import ExistentialRules.ChaseSequence.Termination.RenameConstantsApart
import ExistentialRules.Terms.Cyclic

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

  theorem apply_fact_swap_apply_to_function_free_atom (g : ConstantMapping sig) (trg : PreTrigger sig) (a : FunctionFreeAtom sig) (h : ∃ c, (∀ d, g d = c) ∧ (∀ d, VarOrConst.const d ∈ a.terms -> c = GroundTerm.const d)) : ∀ i, g.apply_fact (trg.apply_to_function_free_atom i a) = PreTrigger.apply_to_function_free_atom { rule := trg.rule, subs := g.apply_ground_term ∘ trg.subs } i a := by
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
      rcases h with ⟨c, g_eq, mem_a_eq⟩
      rw [g_eq]
      rw [mem_a_eq d]
      . simp [GroundTerm.const]
      . exact voc_mem

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


variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

-- TODO: check if can avoid the noncomputable definition; this could work by passing a mapping with the necessary property around and eventually show that such a mapping exists for finite rule sets; not sure if this is better than this though
-- NOTE: this is only used to state some theorems, hence its ok for it to be uncomputable
noncomputable def RuleSet.mfaConstantMapping (rs : RuleSet sig) (special_const : sig.C) : StrictConstantMapping sig :=
  fun c =>
    have : Decidable (c ∈ rs.constants) := Classical.propDecidable (c ∈ rs.constants)
    if (c ∈ rs.constants) then c else special_const

theorem RuleSet.mfaConstantMapping_id_on_rs_constants (rs : RuleSet sig) (special_const : sig.C) : ∀ (c : sig.C), c ∈ rs.constants -> rs.mfaConstantMapping special_const c = c := by
  intro c c_mem
  simp [mfaConstantMapping, c_mem]

theorem RuleSet.mfaConstantMapping_id_on_atom_from_rule (rs : RuleSet sig) (special_const : sig.C) (r : Rule sig) (r_mem : r ∈ rs.rules) : ∀ a, a ∈ r.body ++ r.head.flatten -> (rs.mfaConstantMapping special_const).apply_function_free_atom a = a := by
  intro a a_mem
  unfold StrictConstantMapping.apply_function_free_atom
  rw [FunctionFreeAtom.mk.injEq]
  constructor
  . rfl
  . apply List.map_id_of_id_on_all_mem
    intro voc voc_mem
    cases voc with
    | var v => simp [StrictConstantMapping.apply_var_or_const]
    | const s =>
      simp only [StrictConstantMapping.apply_var_or_const]
      rw [VarOrConst.const.injEq]
      apply mfaConstantMapping_id_on_rs_constants
      exists r
      constructor
      . exact r_mem
      . rw [List.mem_append] at a_mem
        unfold Rule.constants
        rw [List.mem_append]
        cases a_mem with
        | inl a_mem =>
          apply Or.inl
          unfold FunctionFreeConjunction.consts
          rw [List.mem_flatMap]
          exists a
          constructor
          . exact a_mem
          . apply VarOrConst.mem_filterConsts_of_const; exact voc_mem
        | inr a_mem =>
          rw [List.mem_flatten] at a_mem
          rcases a_mem with ⟨head, head_mem, a_mem⟩
          apply Or.inr
          rw [List.mem_flatMap]
          exists head
          constructor
          . exact head_mem
          . unfold FunctionFreeConjunction.consts
            rw [List.mem_flatMap]
            exists a
            constructor
            . exact a_mem
            . apply VarOrConst.mem_filterConsts_of_const; exact voc_mem

structure MfaObsoletenessCondition (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] extends LaxObsoletenessCondition sig

instance {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] : Coe (MfaObsoletenessCondition sig) (LaxObsoletenessCondition sig) where
  coe obs := { cond := obs.cond, monotone := obs.monotone }

def MfaObsoletenessCondition.blocks_obs (mfa_obs : MfaObsoletenessCondition sig) (obs : ObsoletenessCondition sig) (rs : RuleSet sig) (special_const : sig.C) : Prop :=
  ∀ {db : Database sig} (cb : ChaseBranch obs ⟨db, rs⟩) (step : Nat) (trg : RTrigger obs rs) (fs : FactSet sig),
  (∃ (i : Fin trg.val.mapped_head.length), ¬ ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact_set trg.val.mapped_head[i.val].toSet) ⊆ fs) ->
  (mfa_obs.cond { rule := trg.val.rule, subs := (rs.mfaConstantMapping special_const).toConstantMapping.apply_ground_term ∘ trg.val.subs } fs) ->
  (cb.branch.infinite_list step).is_none_or (fun node =>
    trg.val.loaded node.fact ->
    obs.cond trg.val node.fact
  )

def DeterministicSkolemObsoleteness (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] : MfaObsoletenessCondition sig := {
  cond := fun (trg : PreTrigger sig) (F : FactSet sig) => trg.mapped_head.length > 0 ∧ ∀ i : Fin trg.mapped_head.length, trg.mapped_head[i.val].toSet ⊆ F
  monotone := by
    intro trg A B A_sub_B
    simp only [and_imp]
    intro length_gt head_sub_A
    constructor
    . exact length_gt
    . intro i
      apply Set.subset_trans
      . apply head_sub_A
      . apply A_sub_B
}

theorem DeterministicSkolemObsoleteness.blocks_each_obs (obs : ObsoletenessCondition sig) (special_const : sig.C) : ∀ rs, (DeterministicSkolemObsoleteness sig).blocks_obs obs rs special_const := by
  intro rs _ _ _ trg fs f_not_in_prev cond
  rcases f_not_in_prev with ⟨disj_index, f_not_in_prev⟩
  apply False.elim
  apply f_not_in_prev

  intro f' f'_mem
  rcases f'_mem with ⟨f, f_mem, f'_mem⟩

  unfold DeterministicSkolemObsoleteness at cond
  apply cond.right ⟨disj_index.val, by
    have isLt := disj_index.isLt
    unfold PreTrigger.mapped_head
    simp only [List.length_map, List.length_zipIdx]
    simp only [PreTrigger.length_mapped_head] at isLt
    exact isLt
  ⟩

  rw [List.mem_toSet]
  unfold PreTrigger.mapped_head
  simp
  unfold PreTrigger.mapped_head at f_mem
  rw [List.mem_toSet, List.getElem_map, List.mem_map] at f_mem
  rcases f_mem with ⟨a, a_mem, f_eq⟩
  rw [List.get_eq_getElem, List.getElem_zipIdx] at a_mem
  rw [List.get_eq_getElem, List.getElem_zipIdx] at f_eq
  exists (rs.mfaConstantMapping special_const).apply_function_free_atom a
  constructor
  . rw [rs.mfaConstantMapping_id_on_atom_from_rule _ trg.val.rule trg.property]
    . exact a_mem
    . rw [List.mem_append]
      apply Or.inr
      apply List.mem_flatten_of_mem _ a_mem
      apply List.getElem_mem
  . rw [f'_mem, ← f_eq]
    simp only [ConstantMapping.apply_fact, PreTrigger.apply_to_function_free_atom, StrictConstantMapping.apply_function_free_atom, PreTrigger.apply_to_var_or_const, PreTrigger.skolemize_var_or_const, Fact.mk.injEq, true_and, List.map_map, List.map_inj_left, Function.comp_apply]
    intro voc voc_mem
    cases voc with
    | var v =>
      simp only [StrictConstantMapping.apply_var_or_const]
      rw [← ConstantMapping.apply_ground_term_swap_apply_skolem_term]
      . rw [Nat.zero_add]
      . intros
        unfold VarOrConst.skolemize
        simp only
        split <;> simp
    | const c =>
      simp only [StrictConstantMapping.apply_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, StrictConstantMapping.toConstantMapping, GroundTerm.const]

def Trigger.blocked_for_backtracking
    [GetFreshRepresentant sig.C]
    [Inhabited sig.C]
    {obs : LaxObsoletenessCondition sig}
    (trg : Trigger obs)
    (rl : RuleList sig) : Prop :=
  (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl)
  -> (trg_disjIdx_valid : trg.skolem_disjIdx_valid rl trg_ruleIds_valid)
  -> (trg_rule_arity_valid : trg.skolem_rule_arity_valid rl trg_ruleIds_valid)
  -> (obs.cond trg (trg.backtrackFacts rl trg_ruleIds_valid trg_disjIdx_valid trg_rule_arity_valid).toSet)

def BlockingObsoleteness [GetFreshRepresentant sig.C] [Inhabited sig.C] (obs : ObsoletenessCondition sig) (rs : RuleSet sig) : MfaObsoletenessCondition sig := {
  cond := fun (trg : PreTrigger sig) _ =>
    ∀ (rl : RuleList sig), (∀ r, r ∈ rl.rules ↔ r ∈ rs.rules) ->
      let trg' := trg.rename_constants_apart (rl.rules.flatMap Rule.constants)
      let trg'' : Trigger obs := { rule := trg'.rule, subs := trg'.subs }
      trg''.blocked_for_backtracking rl
  monotone := by
    -- trivial since the condition does not depend on the passed fact set
    intro trg A B A_sub_B
    intro h
    exact h
}

theorem BlockingObsoleteness.blocks_corresponding_obs [GetFreshRepresentant sig.C] [Inhabited sig.C] (obs : ObsoletenessCondition sig) (rs : RuleSet sig) (rs_finite : rs.rules.finite) (special_const : sig.C) :
    (BlockingObsoleteness obs rs).blocks_obs obs rs special_const := by
  intro db cb step trg _ _ blocked
  rw [Option.is_none_or_iff]
  intro node eq_node loaded
  simp only [BlockingObsoleteness] at blocked

  rcases rs_finite with ⟨rl, rl_nodup, rl_rs_eq⟩
  let rl : RuleList sig := ⟨rl, by intro r1 r2 h; apply rs.id_unique; rw [← rl_rs_eq]; rw [← rl_rs_eq]; exact h⟩

  have blocked : trg.val.blocked_for_backtracking rl := by
    -- should follow from original blocked and should be its own result
    -- it also relates to one theorem/lemma from the DMFA paper if I remember correctly
    -- not sure what to do about the rule adjustment though, maybe it just works?
    intro trg_ruleIds_valid trg_disjIdx_valid trg_rule_arity_valid
    specialize blocked rl rl_rs_eq
    specialize blocked (by
      apply PreTrigger.rename_constants_apart_preserves_ruleId_validity
      sorry
    )
    specialize blocked (by
      apply PreTrigger.rename_constants_apart_preserves_disjIdx_validity
      . sorry
      . sorry
    )
    specialize blocked (by
      apply PreTrigger.rename_constants_apart_preserves_rule_arity_validity
      . sorry
      . sorry
    )
    simp only at blocked
    sorry

  simp only [Trigger.blocked_for_backtracking] at blocked

  specialize blocked (by apply cb.trigger_ruleIds_valid_of_loaded step node eq_node rl rl_rs_eq; exact loaded)
  specialize blocked (by apply cb.trigger_disjIdx_valid_of_loaded step node eq_node rl rl_rs_eq; exact loaded)
  specialize blocked (by apply cb.trigger_rule_arity_valid_of_loaded step node eq_node rl rl_rs_eq; exact loaded)
  apply obs.monotone _ _ _ _ blocked
  sorry

namespace KnowledgeBase

  def parallelSkolemChase (kb : KnowledgeBase sig) (obs : LaxObsoletenessCondition sig) : InfiniteList (FactSet sig)
  | .zero => kb.db.toFactSet
  | .succ n =>
    let prev_step := parallelSkolemChase kb obs n
    fun f =>
      f ∈ prev_step ∨
      (∃ (trg : RTrigger obs kb.rules),
        trg.val.active prev_step ∧
        ∃ (i : Fin trg.val.mapped_head.length), f ∈ trg.val.mapped_head[i.val])

  theorem parallelSkolemChase_subset_all_following (kb : KnowledgeBase sig) (obs : LaxObsoletenessCondition sig) (n m : Nat) : kb.parallelSkolemChase obs n ⊆ kb.parallelSkolemChase obs (n+m) := by
    induction m with
    | zero => apply Set.subset_refl
    | succ m ih =>
      rw [← Nat.add_assoc]
      conv => right; unfold parallelSkolemChase
      intro f f_mem
      apply Or.inl
      apply ih
      exact f_mem

  theorem parallelSkolemChase_predicates (kb : KnowledgeBase sig) (obs : LaxObsoletenessCondition sig) :
      ∀ n, (kb.parallelSkolemChase obs n).predicates ⊆ (kb.rules.predicates ∪ kb.db.toFactSet.val.predicates) := by
    intro n
    induction n with
    | zero =>
      unfold parallelSkolemChase
      apply Set.subset_union_of_subset_right
      apply Set.subset_refl
    | succ n ih =>
      unfold parallelSkolemChase
      intro p p_mem
      rcases p_mem with ⟨f, f_mem, p_mem⟩
      cases f_mem with
      | inl f_mem => apply ih; exists f
      | inr f_mem =>
        rcases f_mem with ⟨trg, trg_act, f_mem⟩
        unfold PreTrigger.mapped_head at f_mem
        rcases f_mem with ⟨i, f_mem⟩
        rw [List.getElem_map, List.mem_map] at f_mem
        rcases f_mem with ⟨a, a_mem, f_mem⟩
        rw [List.get_eq_getElem, List.getElem_zipIdx] at a_mem
        apply Or.inl
        exists trg.val.rule
        constructor
        . exact trg.property
        . unfold Rule.predicates
          rw [List.mem_append]
          apply Or.inr
          rw [List.mem_flatMap]
          exists trg.val.rule.head[i]
          constructor
          . simp
          . unfold FunctionFreeConjunction.predicates
            rw [List.mem_map]
            exists a
            constructor
            . exact a_mem
            . rw [← p_mem, ← f_mem]
              simp [PreTrigger.apply_to_function_free_atom]

  theorem parallelSkolemChase_constants (kb : KnowledgeBase sig) (obs : LaxObsoletenessCondition sig) :
      ∀ n, (kb.parallelSkolemChase obs n).constants ⊆ (kb.rules.head_constants ∪ kb.db.constants) := by
    intro n
    induction n with
    | zero =>
      unfold parallelSkolemChase
      apply Set.subset_union_of_subset_right
      rw [Database.toFactSet_constants_same]
      apply Set.subset_refl
    | succ n ih =>
      unfold parallelSkolemChase
      intro c c_mem
      rcases c_mem with ⟨f, f_mem, c_mem⟩
      cases f_mem with
      | inl f_mem => apply ih; exists f
      | inr f_mem =>
        rcases f_mem with ⟨trg, trg_act, f_mem⟩
        unfold PreTrigger.mapped_head at f_mem
        rcases f_mem with ⟨i, f_mem⟩
        rw [List.getElem_map, List.mem_map] at f_mem
        rcases f_mem with ⟨a, a_mem, f_mem⟩
        rw [List.get_eq_getElem, List.getElem_zipIdx] at a_mem

        -- NOTE: heavily inspired by: constantsInChaseBranchAreFromDatabase

        rw [← f_mem] at c_mem
        unfold PreTrigger.apply_to_function_free_atom at c_mem
        unfold Fact.constants at c_mem
        rw [List.mem_flatMap] at c_mem
        rcases c_mem with ⟨tree, tree_mem, c_mem⟩
        rw [List.mem_map] at tree_mem
        rcases tree_mem with ⟨voc, voc_mem, tree_eq⟩
        unfold PreTrigger.apply_to_var_or_const at tree_eq

        cases voc with
        | const d =>
          simp only [Function.comp_apply, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize] at tree_eq
          apply Or.inl
          unfold RuleSet.head_constants
          exists trg.val.rule
          constructor
          . exact trg.property
          . unfold Rule.head_constants
            rw [List.mem_flatMap]
            exists trg.val.rule.head[i]
            constructor
            . simp
            . unfold FunctionFreeConjunction.consts
              rw [List.mem_flatMap]
              exists a
              constructor
              . exact a_mem
              . unfold FunctionFreeAtom.constants
                apply VarOrConst.mem_filterConsts_of_const
                rw [← tree_eq] at c_mem
                rw [GroundTerm.constants_const, List.mem_singleton] at c_mem
                rw [c_mem]
                exact voc_mem
        | var v =>
          simp only [Function.comp_apply, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize] at tree_eq

          cases Decidable.em (v ∈ trg.val.rule.frontier) with
          | inl v_frontier =>
            simp [v_frontier] at tree_eq

            apply ih
            rcases (trg.val.rule.frontier_occurs_in_body _ v_frontier) with ⟨b, b_mem, v_mem⟩
            exists trg.val.subs.apply_function_free_atom b
            constructor
            . apply trg_act.left
              rw [List.mem_toSet]
              unfold PreTrigger.mapped_body
              simp only [GroundSubstitution.apply_function_free_conj]
              rw [List.mem_map]
              exists b
            . unfold Fact.constants
              rw [List.mem_flatMap]
              exists tree
              constructor
              . rw [← tree_eq]
                unfold GroundSubstitution.apply_function_free_atom
                rw [List.mem_map]
                exists (VarOrConst.var v)
              . exact c_mem
          | inr v_frontier =>
            simp [v_frontier] at tree_eq
            rw [← tree_eq] at c_mem
            rw [GroundTerm.constants_func, List.mem_flatMap] at c_mem
            rcases c_mem with ⟨tree, tree_mem, c_mem⟩
            rw [List.mem_map] at tree_mem
            rcases tree_mem with ⟨v, v_frontier, tree_eq⟩

            -- from here its the same as in the inl case
            apply ih
            rcases (trg.val.rule.frontier_occurs_in_body _ v_frontier) with ⟨b, b_mem, v_mem⟩
            exists trg.val.subs.apply_function_free_atom b
            constructor
            . apply trg_act.left
              rw [List.mem_toSet]
              unfold PreTrigger.mapped_body
              simp only [GroundSubstitution.apply_function_free_conj]
              rw [List.mem_map]
              exists b
            . unfold Fact.constants
              rw [List.mem_flatMap]
              exists tree
              constructor
              . rw [← tree_eq]
                unfold GroundSubstitution.apply_function_free_atom
                rw [List.mem_map]
                exists (VarOrConst.var v)
              . exact c_mem

  theorem parallelSkolemChase_functions (kb : KnowledgeBase sig) (obs : LaxObsoletenessCondition sig) :
      ∀ n, (kb.parallelSkolemChase obs n).function_symbols ⊆ (kb.rules.skolem_functions) := by
    intro n
    induction n with
    | zero =>
      unfold parallelSkolemChase
      intro func func_mem
      unfold FactSet.function_symbols at func_mem
      rcases func_mem with ⟨f, f_mem, func_mem⟩
      unfold Fact.function_symbols at func_mem
      rw [List.mem_flatMap] at func_mem
      rcases func_mem with ⟨t, t_mem, func_mem⟩
      cases eq : t with
      | const c => simp [eq, GroundTerm.functions_const] at func_mem
      | func _ _ =>
        have func_free := kb.db.toFactSet.property.right
        specialize func_free f f_mem t t_mem
        rcases func_free with ⟨c, t_eq⟩
        rw [t_eq] at eq
        simp [GroundTerm.const, GroundTerm.func] at eq
    | succ n ih =>
      unfold parallelSkolemChase
      intro func func_mem
      rcases func_mem with ⟨f, f_mem, func_mem⟩
      cases f_mem with
      | inl f_mem => apply ih; exists f
      | inr f_mem =>
        rcases f_mem with ⟨trg, trg_act, f_mem⟩
        unfold PreTrigger.mapped_head at f_mem
        rcases f_mem with ⟨i, f_mem⟩
        rw [List.getElem_map, List.mem_map] at f_mem
        rcases f_mem with ⟨a, a_mem, f_mem⟩
        rw [List.get_eq_getElem, List.getElem_zipIdx] at a_mem

        unfold Fact.function_symbols at func_mem
        rw [List.mem_flatMap] at func_mem
        rcases func_mem with ⟨t, t_mem, func_mem⟩
        rw [← f_mem] at t_mem
        simp only [PreTrigger.apply_to_function_free_atom] at t_mem
        rw [List.mem_map] at t_mem
        rcases t_mem with ⟨voc, voc_mem, t_mem⟩
        simp only [PreTrigger.apply_to_var_or_const, Function.comp_apply, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize] at t_mem
        cases voc with
        | const c =>
          simp only at t_mem
          rw [← t_mem] at func_mem
          simp [GroundTerm.functions_const] at func_mem
        | var v =>
          simp only at t_mem
          cases Decidable.em (v ∈ trg.val.rule.frontier) with
          | inl v_frontier =>
            simp [v_frontier] at t_mem
            -- apply ih here with some massaging
            apply ih
            rcases trg.val.rule.frontier_occurs_in_body _ v_frontier with ⟨body_atom, body_atom_mem, v_mem⟩
            unfold FactSet.function_symbols
            exists (trg.val.subs.apply_function_free_atom body_atom)
            constructor
            . apply trg_act.left
              rw [List.mem_toSet]
              simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj]
              rw [List.mem_map]
              exists body_atom
            . unfold Fact.function_symbols
              rw [List.mem_flatMap]
              exists t
              constructor
              . unfold GroundSubstitution.apply_function_free_atom
                rw [List.mem_map]
                exists VarOrConst.var v
              . exact func_mem
          | inr v_frontier =>
            simp only [v_frontier, ↓reduceIte] at t_mem
            rw [← t_mem] at func_mem
            simp only [GroundTerm.functions_func] at func_mem
            rw [List.mem_cons] at func_mem
            cases func_mem with
            | inl func_mem =>
              exists trg.val.rule
              constructor
              . exact trg.property
              . unfold Rule.skolem_functions
                rw [List.mem_flatMap]
                exists (trg.val.rule.head[i], i)
                constructor
                . rw [List.mem_zipIdx_iff_getElem?]
                  simp
                . rw [func_mem]
                  simp
                  constructor
                  . unfold FunctionFreeConjunction.vars
                    rw [List.mem_flatMap]
                    exists a
                    constructor
                    . exact a_mem
                    . unfold FunctionFreeAtom.variables
                      apply VarOrConst.mem_filterVars_of_var
                      exact voc_mem
                  . exact v_frontier
            | inr func_mem =>
              rw [List.mem_flatMap] at func_mem
              rcases func_mem with ⟨tree, tree_mem, func_mem⟩
              rw [List.mem_map] at tree_mem
              rcases tree_mem with ⟨frontier_var, frontier_var_mem, tree_mem⟩

              -- apply ih here with some massaging (should be similar to inl case for v_frontier
              apply ih
              rcases trg.val.rule.frontier_occurs_in_body _ frontier_var_mem with ⟨body_atom, body_atom_mem, frontier_var_mem⟩
              unfold FactSet.function_symbols
              exists (trg.val.subs.apply_function_free_atom body_atom)
              constructor
              . apply trg_act.left
                rw [List.mem_toSet]
                simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj]
                rw [List.mem_map]
                exists body_atom
              . unfold Fact.function_symbols
                rw [List.mem_flatMap]
                exists (trg.val.subs frontier_var)
                constructor
                . unfold GroundSubstitution.apply_function_free_atom
                  rw [List.mem_map]
                  exists VarOrConst.var frontier_var
                . rw [← tree_mem] at func_mem
                  exact func_mem

  def deterministicSkolemChaseResult (kb : KnowledgeBase sig) (obs : LaxObsoletenessCondition sig) : FactSet sig := fun f => ∃ n, f ∈ parallelSkolemChase kb obs n

  theorem deterministicSkolemChaseResult_eq_every_chase_branch_result (kb : KnowledgeBase sig) (det : kb.rules.isDeterministic) : ∀ (cb : ChaseBranch (SkolemObsoleteness sig) kb), cb.result = kb.deterministicSkolemChaseResult (DeterministicSkolemObsoleteness sig) := by
    intro cb
    apply Set.ext
    intro f
    unfold ChaseBranch.result
    unfold deterministicSkolemChaseResult
    constructor
    . intro h
      rcases h with ⟨n, h⟩
      induction n generalizing f with
      | zero =>
        rw [cb.database_first, Option.is_some_and] at h
        exists 0
      | succ n ih =>
        -- should be easy enough: get n from induction hypothesis and then use n+1
        rw [Option.is_some_and_iff] at h
        rcases h with ⟨node, eq_node, h⟩
        rw [cb.origin_trg_result_yields_next_node_fact n node eq_node] at h
        cases h with
        | inl h =>
          specialize ih f
          rw [cb.prev_node_eq n (by simp [eq_node]), Option.is_some_and] at ih
          specialize ih h
          exact ih
        | inr h =>
          let prev_node := cb.prev_node n (by simp [eq_node])

          have : ∃ n, prev_node.fact.val ⊆ kb.parallelSkolemChase (DeterministicSkolemObsoleteness sig) n := by
            have prev_finite := prev_node.fact.property
            rcases prev_finite with ⟨prev_l, _, prev_l_eq⟩

            have : ∀ (l : List (Fact sig)), (∀ e, e ∈ l -> e ∈  prev_node.fact.val) -> ∃ n, (∀ e, e ∈ l -> e ∈ kb.parallelSkolemChase (DeterministicSkolemObsoleteness sig) n) := by
              intro l l_sub
              induction l with
              | nil => exists 0; intro e; simp
              | cons hd tl ih_inner =>
                have from_ih := ih_inner (by intro e e_mem; apply l_sub; simp [e_mem])
                rcases from_ih with ⟨n_from_ih, from_ih⟩

                have from_hd := ih hd
                rw [cb.prev_node_eq n (by simp [eq_node]), Option.is_some_and] at from_hd
                specialize from_hd (by apply l_sub; simp)
                rcases from_hd with ⟨n_from_hd, from_hd⟩

                cases Decidable.em (n_from_ih ≤ n_from_hd) with
                | inl le =>
                  exists n_from_hd
                  intro f f_mem
                  simp at f_mem
                  cases f_mem with
                  | inl f_mem => rw [f_mem]; exact from_hd
                  | inr f_mem =>
                    rcases Nat.exists_eq_add_of_le le with ⟨diff, le⟩
                    rw [le]
                    apply kb.parallelSkolemChase_subset_all_following (DeterministicSkolemObsoleteness sig) n_from_ih diff
                    apply from_ih; exact f_mem
                | inr lt =>
                  simp at lt
                  have le := Nat.le_of_lt lt
                  exists n_from_ih
                  intro f f_mem
                  simp at f_mem
                  cases f_mem with
                  | inr f_mem => apply from_ih; exact f_mem
                  | inl f_mem =>
                    rcases Nat.exists_eq_add_of_le le with ⟨diff, le⟩
                    rw [le]
                    apply kb.parallelSkolemChase_subset_all_following (DeterministicSkolemObsoleteness sig) n_from_hd diff
                    rw [f_mem]; exact from_hd

            specialize this prev_l (by intro f; exact (prev_l_eq f).mp)
            rcases this with ⟨n, this⟩
            exists n
            intro f
            rw [← prev_l_eq]
            exact this f
          rcases this with ⟨n, prev_subs⟩

          exists n+1
          unfold parallelSkolemChase

          -- TODO: would be Decidable if we define sets in the parallelSkolemChase to be finite
          cases Classical.em (f ∈ kb.parallelSkolemChase (DeterministicSkolemObsoleteness sig) n) with
          | inl mem => apply Or.inl; exact mem
          | inr not_mem =>
            apply Or.inr
            let origin := node.origin.get (cb.origin_isSome _ eq_node)
            exists ⟨{ rule := origin.fst.val.rule, subs := origin.fst.val.subs }, origin.fst.property⟩
            constructor
            . unfold Trigger.active
              constructor
              . unfold PreTrigger.loaded
                apply Set.subset_trans (b := prev_node.fact.val)
                . exact (cb.origin_trg_is_active _ _ eq_node).left
                . exact prev_subs
              . intro contra
                apply not_mem
                apply contra.right origin.snd
                exact h
            . rw [List.mem_toSet] at h
              exists origin.snd
    . intro h
      rcases h with ⟨n, h⟩
      induction n generalizing f with
      | zero =>
        exists 0
        rw [cb.database_first, Option.is_some_and]
        exact h
      | succ n ih =>
        -- we need to invoke fairness somehow
        unfold parallelSkolemChase at h
        cases h with
        | inl h => exact ih _ h
        | inr h =>
          rcases h with ⟨trg, trg_active, f_mem⟩

          have trg_loaded_somewhere : ∃ n, (cb.branch.infinite_list n).is_some_and (fun node => trg.val.loaded node.fact.val) := by
            have : ∀ (l : List (Fact sig)), (∀ e, e ∈ l -> e ∈ trg.val.mapped_body) -> ∃ n, (cb.branch.infinite_list n).is_some_and (fun node => (∀ e, e ∈ l -> e ∈ node.fact.val)) := by
              intro l l_sub
              induction l with
              | nil => exists 0; rw [cb.database_first, Option.is_some_and]; simp
              | cons hd tl ih_inner =>
                have from_ih := ih_inner (by intro f f_mem; apply l_sub; simp [f_mem])
                rcases from_ih with ⟨n_from_ih, from_ih⟩

                cases eq_from_ih : cb.branch.infinite_list n_from_ih with
                | none => rw [eq_from_ih, Option.is_some_and] at from_ih; simp at from_ih
                | some node_from_ih =>
                rw [eq_from_ih, Option.is_some_and] at from_ih

                have from_hd := ih hd (by apply trg_active.left; rw [List.mem_toSet]; apply l_sub; simp)
                rcases from_hd with ⟨n_from_hd, from_hd⟩

                cases eq_from_hd : cb.branch.infinite_list n_from_hd with
                | none => rw [eq_from_hd, Option.is_some_and] at from_hd; simp at from_hd
                | some node_from_hd =>
                rw [eq_from_hd, Option.is_some_and] at from_hd

                cases Decidable.em (n_from_ih ≤ n_from_hd) with
                | inl le =>
                  exists n_from_hd
                  rw [eq_from_hd, Option.is_some_and]
                  intro f f_mem
                  simp at f_mem
                  cases f_mem with
                  | inl f_mem => rw [f_mem]; exact from_hd
                  | inr f_mem =>
                    rcases Nat.exists_eq_add_of_le le with ⟨diff, le⟩
                    have subsetAllFollowing := ChaseBranch.stepIsSubsetOfAllFollowing cb n_from_ih _ eq_from_ih diff
                    rw [← le, eq_from_hd, Option.is_none_or] at subsetAllFollowing
                    apply subsetAllFollowing
                    apply from_ih; exact f_mem
                | inr lt =>
                  simp at lt
                  have le := Nat.le_of_lt lt
                  exists n_from_ih
                  rw [eq_from_ih, Option.is_some_and]
                  intro f f_mem
                  simp at f_mem
                  cases f_mem with
                  | inr f_mem => apply from_ih; exact f_mem
                  | inl f_mem =>
                    rcases Nat.exists_eq_add_of_le le with ⟨diff, le⟩
                    have subsetAllFollowing := ChaseBranch.stepIsSubsetOfAllFollowing cb n_from_hd _ eq_from_hd diff
                    rw [← le, eq_from_ih, Option.is_none_or] at subsetAllFollowing
                    apply subsetAllFollowing
                    rw [f_mem]; exact from_hd

            specialize this trg.val.mapped_body (by simp)
            rcases this with ⟨n, this⟩
            exists n
            cases eq : cb.branch.infinite_list n with
            | none => rw [eq, Option.is_some_and] at this; simp at this
            | some node =>
              rw [Option.is_some_and]
              rw [eq, Option.is_some_and] at this
              intro f
              rw [List.mem_toSet]
              apply this
          rcases trg_loaded_somewhere with ⟨loaded_n, trg_loaded_somewhere⟩
          cases eq_node_loaded : cb.branch.infinite_list loaded_n with
          | none => rw [eq_node_loaded, Option.is_some_and] at trg_loaded_somewhere; simp at trg_loaded_somewhere
          | some node_loaded =>
          rw [eq_node_loaded, Option.is_some_and] at trg_loaded_somewhere

          have fair := cb.fairness ⟨{ rule := trg.val.rule, subs:= trg.val.subs }, trg.property⟩
          rcases fair with ⟨fairness_n, fair⟩
          cases eq_node_fairness : cb.branch.infinite_list fairness_n with
          | none => rw [eq_node_fairness, Option.is_some_and] at fair; simp at fair
          | some node_fairness =>
          rw [eq_node_fairness, Option.is_some_and] at fair

          cases Decidable.em (loaded_n ≤ fairness_n) with
          | inl le =>
            exists fairness_n
            rw [eq_node_fairness, Option.is_some_and]
            have trg_not_active := fair.left
            unfold Trigger.active at trg_not_active
            simp only [not_and, Classical.not_not] at trg_not_active

            have trg_loaded : trg.val.loaded node_fairness.fact.val := by
              intro f f_mem
              rcases Nat.exists_eq_add_of_le le with ⟨diff, le⟩
              have subsetAllFollowing := ChaseBranch.stepIsSubsetOfAllFollowing cb loaded_n _ eq_node_loaded diff
              rw [← le, eq_node_fairness, Option.is_none_or] at subsetAllFollowing
              apply subsetAllFollowing
              apply trg_loaded_somewhere
              exact f_mem

            specialize trg_not_active trg_loaded
            rcases trg_not_active with ⟨disj_index, trg_not_active⟩
            apply trg_not_active
            have disj_index_zero : disj_index.val = 0 := by
              have isLt := disj_index.isLt
              simp only [PreTrigger.length_mapped_head] at isLt
              specialize det _ trg.property
              unfold Rule.isDeterministic at det
              rw [decide_eq_true_iff] at det
              rw [det, Nat.lt_one_iff] at isLt
              exact isLt
            rcases f_mem with ⟨i, f_mem⟩
            have i_zero : i.val = 0 := by
              have isLt := i.isLt
              simp only [PreTrigger.length_mapped_head] at isLt
              specialize det _ trg.property
              unfold Rule.isDeterministic at det
              rw [decide_eq_true_iff] at det
              rw [det, Nat.lt_one_iff] at isLt
              exact isLt
            rw [List.mem_toSet]
            simp only [disj_index_zero]
            simp only [i_zero] at f_mem
            exact f_mem
          | inr lt =>
            simp at lt

            exists loaded_n
            rw [eq_node_loaded, Option.is_some_and]
            have trg_not_active := fair.right loaded_n lt
            rw [eq_node_loaded, Option.is_none_or] at trg_not_active
            unfold Trigger.active at trg_not_active
            simp only [not_and, Classical.not_not] at trg_not_active

            specialize trg_not_active trg_loaded_somewhere
            rcases trg_not_active with ⟨disj_index, trg_not_active⟩
            apply trg_not_active
            have disj_index_zero : disj_index.val = 0 := by
              have isLt := disj_index.isLt
              simp only [PreTrigger.length_mapped_head] at isLt
              specialize det _ trg.property
              unfold Rule.isDeterministic at det
              rw [decide_eq_true_iff] at det
              rw [det, Nat.lt_one_iff] at isLt
              exact isLt
            rcases f_mem with ⟨i, f_mem⟩
            have i_zero : i.val = 0 := by
              have isLt := i.isLt
              simp only [PreTrigger.length_mapped_head] at isLt
              specialize det _ trg.property
              unfold Rule.isDeterministic at det
              rw [decide_eq_true_iff] at det
              rw [det, Nat.lt_one_iff] at isLt
              exact isLt
            rw [List.mem_toSet]
            simp only [disj_index_zero]
            simp only [i_zero] at f_mem
            exact f_mem

  theorem deterministicSkolemChaseResult_predicates (kb : KnowledgeBase sig) (obs : LaxObsoletenessCondition sig) :
      (kb.deterministicSkolemChaseResult obs).predicates ⊆ (kb.rules.predicates ∪ kb.db.toFactSet.val.predicates) := by
    intro p p_mem
    rcases p_mem with ⟨f, f_mem, p_mem⟩
    rcases f_mem with ⟨n, f_mem⟩
    apply kb.parallelSkolemChase_predicates obs n
    exists f

  theorem deterministicSkolemChaseResult_constants (kb : KnowledgeBase sig) (obs : LaxObsoletenessCondition sig) :
      (kb.deterministicSkolemChaseResult obs).constants ⊆ (kb.rules.head_constants ∪ kb.db.constants) := by
    intro c c_mem
    rcases c_mem with ⟨f, f_mem, c_mem⟩
    rcases f_mem with ⟨n, f_mem⟩
    apply kb.parallelSkolemChase_constants obs n
    exists f

  theorem deterministicSkolemChaseResult_functions (kb : KnowledgeBase sig) (obs : LaxObsoletenessCondition sig) :
      (kb.deterministicSkolemChaseResult obs).function_symbols ⊆ (kb.rules.skolem_functions) := by
    intro func func_mem
    rcases func_mem with ⟨f, f_mem, func_mem⟩
    rcases f_mem with ⟨n, f_mem⟩
    apply kb.parallelSkolemChase_functions obs n
    exists f

end KnowledgeBase

namespace RuleSet

  def criticalInstance (rs : RuleSet sig) (finite : rs.rules.finite) (special_const : sig.C) : Database sig :=
    ⟨fun f => f.predicate ∈ rs.predicates ∧ ∀ t, t ∈ f.terms -> (t = special_const ∨ t ∈ rs.constants), by
      -- TODO: this is very close to part of the proof of FactSet.finite_of_preds_finite_of_terms_finite
      -- but we cannot use it since our set is not Set (Fact sig) but Set (FunctionFreeFact sig)...
      -- maybe we can generalize this someday

      have preds_finite := rs.predicates_finite_of_finite finite
      rcases preds_finite with ⟨l_preds, _, preds_eq⟩
      have consts_finite := rs.constants_finite_of_finite finite
      rcases consts_finite with ⟨l_consts, _, consts_eq⟩

      exists (l_preds.flatMap (fun p =>
        (all_lists_of_length (special_const :: l_consts) (sig.arity p)).attach.map (fun ⟨ts, mem⟩ =>
          {
            predicate := p
            terms := ts
            arity_ok := ((mem_all_lists_of_length (special_const :: l_consts) (sig.arity p) ts).mp mem).left
          }
        )
      )).eraseDupsKeepRight

      constructor
      . apply List.nodup_eraseDupsKeepRight
      . intro f
        rw [List.mem_eraseDupsKeepRight]
        simp only [List.mem_flatMap, List.mem_map, List.mem_attach, true_and, Subtype.exists]
        constructor
        . intro h
          rcases h with ⟨pred, pred_mem, ts, ts_mem, f_eq⟩
          rw [← f_eq]
          constructor
          . rw [preds_eq] at pred_mem
            exact pred_mem
          . rw [mem_all_lists_of_length] at ts_mem
            intro t t_mem
            rw [← consts_eq]
            rw [← List.mem_cons]
            apply ts_mem.right
            exact t_mem
        . intro h
          rcases h with ⟨pred_mem, ts_mem⟩
          exists f.predicate
          constructor
          . rw [preds_eq]; exact pred_mem
          . exists f.terms
            exists (by
              rw [mem_all_lists_of_length]
              constructor
              . exact f.arity_ok
              . intro t t_mem; rw [List.mem_cons]; rw [consts_eq]; apply ts_mem; exact t_mem
            )
    ⟩

  def mfaKb (rs : RuleSet sig) (finite : rs.rules.finite) (special_const : sig.C) : KnowledgeBase sig := {
    rules := rs
    db := criticalInstance rs finite special_const
  }

  theorem mfaKb_db_constants (rs : RuleSet sig) (finite : rs.rules.finite) (special_const : sig.C) :
      ∀ c, c ∈ (rs.mfaKb finite special_const).db.constants.val -> (c = special_const ∨ c ∈ rs.constants) := by
    intro c c_mem
    unfold mfaKb at c_mem
    unfold criticalInstance at c_mem
    unfold Database.constants at c_mem
    simp only at c_mem
    rcases c_mem with ⟨f, f_mem, c_mem⟩
    apply f_mem.right
    exact c_mem

  def mfaSet (rs : RuleSet sig) (finite : rs.rules.finite) (special_const : sig.C) (obs : MfaObsoletenessCondition sig) : FactSet sig :=
    (rs.mfaKb finite special_const).deterministicSkolemChaseResult obs

  theorem mfaSet_contains_every_chase_step_for_every_kb_except_for_facts_with_predicates_not_from_rs (rs : RuleSet sig) (finite : rs.rules.finite) (special_const : sig.C) (mfa_obs : MfaObsoletenessCondition sig) : ∀ {db : Database sig} {obs : ObsoletenessCondition sig}, (mfa_obs.blocks_obs obs rs special_const) -> ∀ (cb : ChaseBranch obs { rules := rs, db := db }) (n : Nat), (cb.branch.infinite_list n).is_none_or (fun node => ∀ f, f.predicate ∈ rs.predicates -> f ∈ node.fact.val -> ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact f) ∈ (rs.mfaSet finite special_const mfa_obs)) := by
    intro db obs blocks cb n
    induction n with
    | zero =>
      rw [cb.database_first, Option.is_none_or]
      simp only
      intro f f_predicate f_mem
      exists 0
      unfold KnowledgeBase.parallelSkolemChase
      unfold Database.toFactSet
      unfold RuleSet.mfaKb
      unfold criticalInstance
      simp only

      have every_t_const : ∀ t, t ∈ ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact f).terms -> ∃ c, t = GroundTerm.const c ∧ (c = special_const ∨ c ∈ rs.constants) := by
        intro t t_mem
        unfold ConstantMapping.apply_fact at t_mem
        simp only [List.mem_map] at t_mem
        rcases t_mem with ⟨s, s_mem, t_eq⟩

        have isFunctionFree := db.toFactSet.property.right
        specialize isFunctionFree _ f_mem
        specialize isFunctionFree _ s_mem
        rcases isFunctionFree with ⟨c, s_eq⟩
        exists (rs.mfaConstantMapping special_const) c
        constructor
        . rw [← t_eq, s_eq]
          simp [StrictConstantMapping.toConstantMapping, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, GroundTerm.const]
        . cases Classical.em (c ∈ rs.constants) with
          | inl c_mem => apply Or.inr; simp [mfaConstantMapping, c_mem]
          | inr c_mem => apply Or.inl; simp [mfaConstantMapping, c_mem]
      have f_func_free : ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact f).isFunctionFree := by
        intro t t_mem
        rcases every_t_const t t_mem with ⟨c, t_eq, _⟩
        exists c

      exists ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact f).toFunctionFreeFact f_func_free
      constructor
      . unfold Fact.toFunctionFreeFact
        constructor
        . exact f_predicate
        . simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists, forall_exists_index]
          intro c t t_arity_ok t_mem c_eq
          specialize every_t_const ⟨t, t_arity_ok⟩ t_mem
          rcases every_t_const with ⟨d, d_eq, goal⟩
          rw [← c_eq]
          simp only [d_eq]
          simp [GroundTerm.const, GroundTerm.toConst, goal]
      . rw [Fact.toFact_after_toFunctionFreeFact_is_id]
    | succ n ih =>
      rw [Option.is_none_or_iff]
      intro node eq_node
      rw [cb.prev_node_eq n (by simp [eq_node]), Option.is_none_or] at ih
      intro f f_predicate f_mem
      rw [cb.origin_trg_result_yields_next_node_fact _ _ eq_node] at f_mem
      cases f_mem with
      | inl f_mem =>
        apply ih
        . exact f_predicate
        . exact f_mem
      | inr f_mem =>
        let prev_node := cb.prev_node n (by simp [eq_node])
        unfold RuleSet.mfaSet
        unfold KnowledgeBase.deterministicSkolemChaseResult

        have : ∃ n, ∀ f, f.predicate ∈ rs.predicates -> f ∈ prev_node.fact.val -> ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact f) ∈ (rs.mfaKb finite special_const).parallelSkolemChase mfa_obs n := by
          let kb := rs.mfaKb finite special_const
          let prev_filtered : FactSet sig := fun f => f.predicate ∈ rs.predicates ∧ f ∈ prev_node.fact.val
          have prev_finite : prev_filtered.finite := by
            rcases prev_node.fact.property with ⟨prev_l, _, prev_l_eq⟩
            rcases (RuleSet.predicates_finite_of_finite _ finite) with ⟨preds_l, _, preds_l_eq⟩
            exists (prev_l.filter (fun f => f.predicate ∈ preds_l)).eraseDupsKeepRight
            constructor
            . apply List.nodup_eraseDupsKeepRight
            . intro f
              rw [List.mem_eraseDupsKeepRight, List.mem_filter]
              rw [prev_l_eq]
              unfold prev_filtered
              simp [preds_l_eq, Set.element, And.comm]
          rcases prev_finite with ⟨prev_l, _, prev_l_eq⟩

          have : ∀ (l : List (Fact sig)), (∀ e, e ∈ l -> e.predicate ∈ rs.predicates ∧ e ∈ prev_node.fact.val) -> ∃ n, (∀ e, e ∈ l -> ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact e) ∈ (kb.parallelSkolemChase mfa_obs n)) := by
            intro l l_sub
            induction l with
            | nil => exists 0; intro e; simp
            | cons hd tl ih_inner =>
              have from_ih := ih_inner (by intro e e_mem; apply l_sub; simp [e_mem])
              rcases from_ih with ⟨n_from_ih, from_ih⟩

              have from_hd := ih hd (l_sub hd (by simp)).left (l_sub hd (by simp)).right
              rcases from_hd with ⟨n_from_hd, from_hd⟩

              cases Decidable.em (n_from_ih ≤ n_from_hd) with
              | inl le =>
                exists n_from_hd
                intro f f_mem
                simp at f_mem
                cases f_mem with
                | inl f_mem => rw [f_mem]; exact from_hd
                | inr f_mem =>
                  rcases Nat.exists_eq_add_of_le le with ⟨diff, le⟩
                  rw [le]
                  apply kb.parallelSkolemChase_subset_all_following mfa_obs n_from_ih diff
                  apply from_ih; exact f_mem
              | inr lt =>
                simp at lt
                have le := Nat.le_of_lt lt
                exists n_from_ih
                intro f f_mem
                simp at f_mem
                cases f_mem with
                | inr f_mem => apply from_ih; exact f_mem
                | inl f_mem =>
                  rcases Nat.exists_eq_add_of_le le with ⟨diff, le⟩
                  rw [le]
                  apply kb.parallelSkolemChase_subset_all_following mfa_obs n_from_hd diff
                  rw [f_mem]; exact from_hd

          specialize this prev_l (by
            intro f f_mem
            rw [prev_l_eq] at f_mem
            unfold prev_filtered at f_mem
            exact f_mem
          )

          rcases this with ⟨m, this⟩
          exists m
          intro f f_pred f_mem
          specialize this f (by
            rw [prev_l_eq]
            unfold prev_filtered
            constructor
            . exact f_pred
            . exact f_mem
          )
          exact this

        rcases this with ⟨m, prev_node_subs_parallel_chase⟩
        exists (m+1)
        unfold KnowledgeBase.parallelSkolemChase
        simp only [Set.element]

        rw [Classical.or_iff_not_imp_left]
        intro f_not_in_prev

        let origin := node.origin.get (cb.origin_isSome _ eq_node)
        let trg := origin.fst
        let disj_index := origin.snd

        let adjusted_trg : RTrigger mfa_obs (rs.mfaKb finite special_const).rules := ⟨⟨trg.val.rule, (rs.mfaConstantMapping special_const).toConstantMapping.apply_ground_term ∘ trg.val.subs⟩, trg.property⟩

        exists adjusted_trg
        constructor
        . constructor
          . apply Set.subset_trans (b := fun f => f.predicate ∈ rs.predicates ∧ f ∈ ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact_set prev_node.fact.val))
            . intro f f_mem
              rw [List.mem_toSet] at f_mem
              simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, List.mem_map] at f_mem
              rcases f_mem with ⟨a, a_mem, f_eq⟩
              unfold adjusted_trg at a_mem
              simp only [Set.element]
              constructor
              . rw [← f_eq]
                simp only [GroundSubstitution.apply_function_free_atom]
                unfold RuleSet.predicates
                exists trg.val.rule
                constructor
                . exact trg.property
                . unfold Rule.predicates
                  rw [List.mem_append]
                  apply Or.inl
                  unfold FunctionFreeConjunction.predicates
                  rw [List.mem_map]
                  exists a
              . exists trg.val.subs.apply_function_free_atom a
                constructor
                . apply (cb.origin_trg_is_active _ _ eq_node).left
                  rw [List.mem_toSet]
                  simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, List.mem_map]
                  exists a
                . rw [← f_eq]
                  unfold ConstantMapping.apply_fact
                  unfold GroundSubstitution.apply_function_free_atom
                  rw [Fact.mk.injEq]
                  constructor
                  . rfl
                  . simp only [adjusted_trg, List.map_map]
                    rw [List.map_inj_left]
                    intro voc voc_mem
                    cases voc with
                    | var v =>
                      simp [GroundSubstitution.apply_var_or_const, StrictConstantMapping.apply_var_or_const]
                    | const c =>
                      simp only [Function.comp_apply, GroundSubstitution.apply_var_or_const, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, StrictConstantMapping.toConstantMapping, GroundTerm.const]
                      apply Subtype.eq
                      simp only [FiniteTree.leaf.injEq]
                      rw [rs.mfaConstantMapping_id_on_rs_constants]
                      exists trg.val.rule
                      constructor
                      . exact trg.property
                      unfold Rule.constants
                      rw [List.mem_append]
                      apply Or.inl
                      unfold FunctionFreeConjunction.consts
                      rw [List.mem_flatMap]
                      exists a
                      constructor
                      . exact a_mem
                      . apply VarOrConst.mem_filterConsts_of_const; exact voc_mem
            . intro f f_mem
              rcases f_mem with ⟨f_pred, f', f'_mem, f_eq⟩
              rw [f_eq]
              apply prev_node_subs_parallel_chase
              . rw [f_eq] at f_pred
                simp only [ConstantMapping.apply_fact] at f_pred
                exact f_pred
              . exact f'_mem
          . intro contra
            have contra := blocks cb n trg _ (by
              exists disj_index
              intro contra
              apply f_not_in_prev
              apply contra
              apply ConstantMapping.apply_fact_mem_apply_fact_set_of_mem
              exact f_mem
            ) contra
            rw [ChaseBranch.prev_node_eq _ _ (by simp [eq_node])] at contra
            simp only [Option.is_none_or] at contra
            specialize contra (cb.origin_trg_is_active _ _ eq_node).left

            apply (cb.origin_trg_is_active _ _ eq_node).right
            exact contra
        . rw [List.mem_toSet] at f_mem
          unfold ChaseNode.origin_result at f_mem
          unfold PreTrigger.mapped_head at f_mem
          simp at f_mem
          rcases f_mem with ⟨a, a_mem, f_eq⟩

          let adjusted_disj_index : Fin adjusted_trg.val.mapped_head.length := ⟨disj_index.val, by
            have isLt := disj_index.isLt
            simp only [PreTrigger.length_mapped_head]
            unfold adjusted_trg
            simp only [PreTrigger.length_mapped_head] at isLt
            exact isLt
          ⟩
          exists adjusted_disj_index
          unfold PreTrigger.mapped_head
          simp

          exists (rs.mfaConstantMapping special_const).apply_function_free_atom a
          constructor
          . rw [rs.mfaConstantMapping_id_on_atom_from_rule _ adjusted_trg.val.rule adjusted_trg.property]
            . exact a_mem
            . rw [List.mem_append]
              apply Or.inr
              apply List.mem_flatten_of_mem _ a_mem
              apply List.getElem_mem
          . rw [← f_eq]
            simp only [ConstantMapping.apply_fact, PreTrigger.apply_to_function_free_atom, StrictConstantMapping.apply_function_free_atom, PreTrigger.apply_to_var_or_const, PreTrigger.skolemize_var_or_const, Fact.mk.injEq, true_and, List.map_map, List.map_inj_left, Function.comp_apply]
            intro voc voc_mem
            cases voc with
            | var v =>
              simp only [StrictConstantMapping.apply_var_or_const]
              rw [← ConstantMapping.apply_ground_term_swap_apply_skolem_term]
              intros
              unfold VarOrConst.skolemize
              simp only
              split <;> simp
            | const c =>
              simp only [StrictConstantMapping.apply_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, StrictConstantMapping.toConstantMapping, GroundTerm.const]

  theorem filtered_cb_result_subset_mfaSet (rs : RuleSet sig) (finite : rs.rules.finite) (special_const : sig.C) (mfa_obs : MfaObsoletenessCondition sig) : ∀ {db : Database sig} {obs : ObsoletenessCondition sig}, (mfa_obs.blocks_obs obs rs special_const) -> ∀ (cb : ChaseBranch obs { rules := rs, db := db }), ((rs.mfaConstantMapping special_const).toConstantMapping.apply_fact_set (fun f => f.predicate ∈ rs.predicates ∧ f ∈ cb.result)) ⊆ (rs.mfaSet finite special_const mfa_obs) := by
    intro db obs blocks cb f f_mem

    rcases f_mem with ⟨f', f'_mem, f_eq⟩
    rcases f'_mem with ⟨f'_pred, f'_mem⟩
    rcases f'_mem with ⟨n, f'_mem⟩
    rw [f_eq]

    cases eq : cb.branch.infinite_list n with
    | none => simp [eq, Option.is_some_and] at f'_mem
    | some node =>
      have := rs.mfaSet_contains_every_chase_step_for_every_kb_except_for_facts_with_predicates_not_from_rs finite special_const mfa_obs blocks cb n
      rw [eq, Option.is_none_or] at this
      apply this
      . exact f'_pred
      . rw [eq, Option.is_some_and] at f'_mem
        exact f'_mem

  theorem terminates_of_mfaSet_finite [Inhabited sig.C] (rs : RuleSet sig) (rs_finite : rs.rules.finite) (mfa_obs : MfaObsoletenessCondition sig) :
      ∀ {obs : ObsoletenessCondition sig}, (mfa_obs.blocks_obs obs rs Inhabited.default) -> (rs.mfaSet rs_finite Inhabited.default mfa_obs).finite -> rs.terminates obs := by
    intro obs blocks mfa_finite
    unfold RuleSet.terminates
    intro db
    unfold KnowledgeBase.terminates
    intro ct
    unfold ChaseTree.terminates
    intro cb cb_mem
    rw [ChaseBranch.terminates_iff_result_finite]

    let res_filtered : FactSet sig := fun f => f.predicate ∈ rs.predicates ∧ f ∈ cb.result
    have res_filtered_finite : res_filtered.finite := by
      have : ((rs.mfaConstantMapping Inhabited.default).toConstantMapping.apply_fact_set (fun f => f.predicate ∈ rs.predicates ∧ f ∈ cb.result)).finite :=
        Set.finite_of_subset_finite mfa_finite (rs.filtered_cb_result_subset_mfaSet rs_finite Inhabited.default mfa_obs blocks cb)

      rcases this with ⟨l, _, l_eq⟩

      let db_constants := db.constants
      rcases db_constants.property with ⟨l_db_c, _, l_db_c_eq⟩

      let rs_constants := rs.head_constants
      have rs_constants_finite : rs_constants.finite := RuleSet.head_constants_finite_of_finite _ rs_finite
      rcases rs_constants_finite with ⟨l_rs_c, _, l_rs_c_eq⟩

      let arguments : FactSet sig := fun f => (∀ c, c ∈ f.constants -> (c ∈ l_db_c ++ l_rs_c)) ∧ ((rs.mfaConstantMapping default).toConstantMapping.apply_fact f) ∈ ((rs.mfaConstantMapping default).toConstantMapping.apply_fact_set res_filtered)
      have arguments_fin : arguments.finite := by
        exists (l.flatMap (fun f => (rs.mfaConstantMapping default).arguments_for_fact (l_db_c ++ l_rs_c) f)).eraseDupsKeepRight
        constructor
        . apply List.nodup_eraseDupsKeepRight
        . intro f
          rw [List.mem_eraseDupsKeepRight, List.mem_flatMap]
          constructor
          . intro h
            rcases h with ⟨f', f'_mem, f_mem⟩
            rw [l_eq] at f'_mem
            have : f' = (rs.mfaConstantMapping default).toConstantMapping.apply_fact f := by
              have := (rs.mfaConstantMapping default).apply_to_arguments_yields_original_fact (l_db_c ++ l_rs_c) f'
              rw [((this _).mp _).right]
              exact f_mem
            rw [this] at f'_mem
            constructor
            . have := (rs.mfaConstantMapping default).apply_to_arguments_yields_original_fact (l_db_c ++ l_rs_c) f' f
              apply (this.mp _).left
              exact f_mem
            . exact f'_mem
          . intro h
            exists (rs.mfaConstantMapping default).toConstantMapping.apply_fact f
            constructor
            . rw [l_eq]
              exact h.right
            . rw [(rs.mfaConstantMapping default).apply_to_arguments_yields_original_fact (l_db_c ++ l_rs_c)]
              simp only [and_true]
              exact h.left

      apply Set.finite_of_subset_finite arguments_fin
      intro f f_mem
      constructor
      . rcases f_mem.right with ⟨step, f_mem⟩
        intro c c_mem
        rw [Option.is_some_and_iff] at f_mem
        rcases f_mem with ⟨node, eq_step, f_mem⟩
        have := ChaseBranch.constantsInStepAreFromDatabaseOrRuleSet cb step node eq_step c (by exists f)
        rw [List.mem_append]
        cases this with
        | inl this => apply Or.inl; rw [l_db_c_eq]; exact this
        | inr this => apply Or.inr; rw [l_rs_c_eq]; exact this
      . apply ConstantMapping.apply_fact_mem_apply_fact_set_of_mem
        exact f_mem

    have res_sub_db_and_filtered : cb.result ⊆ db.toFactSet.val ∪ res_filtered := by
      have each_step_sub_db_and_filtered : ∀ n, (cb.branch.infinite_list n).is_none_or (fun node => node.fact.val ⊆ db.toFactSet.val ∪ res_filtered) := by
        intro n
        induction n with
        | zero => rw [cb.database_first, Option.is_none_or]; intro f f_mem; apply Or.inl; exact f_mem
        | succ n ih =>
          rw [Option.is_none_or_iff]
          intro node eq_node
          rw [cb.origin_trg_result_yields_next_node_fact n node eq_node]
          intro f f_mem
          cases f_mem with
          | inl f_mem =>
            rw [cb.prev_node_eq n (by simp [eq_node]), Option.is_none_or] at ih
            apply ih
            exact f_mem
          | inr f_mem =>
            apply Or.inr
            constructor
            . -- since f occur in the trigger result, its predicate occurs in the rule and must therefore occur in the ruleset
              let origin := node.origin.get (cb.origin_isSome n eq_node)
              rw [List.mem_toSet] at f_mem
              simp only [ChaseNode.origin_result, PreTrigger.mapped_head] at f_mem
              simp at f_mem
              rcases f_mem with ⟨a, a_mem, f_eq⟩
              rw [← f_eq]
              simp only [PreTrigger.apply_to_function_free_atom]
              exists origin.fst.val.rule
              constructor
              . exact origin.fst.property
              . unfold Rule.predicates
                rw [List.mem_append]
                apply Or.inr
                rw [List.mem_flatMap]
                exists origin.fst.val.rule.head[origin.snd.val]'(by rw [← PreTrigger.length_mapped_head]; exact origin.snd.isLt)
                simp only [List.getElem_mem, true_and]
                unfold FunctionFreeConjunction.predicates
                rw [List.mem_map]
                exists a
            . exists (n+1)
              rw [eq_node, Option.is_some_and]
              rw [cb.origin_trg_result_yields_next_node_fact n node eq_node]
              apply Or.inr
              exact f_mem

      intro f f_mem
      rcases f_mem with ⟨n, f_mem⟩
      cases eq_node : cb.branch.infinite_list n with
      | none => simp [eq_node, Option.is_some_and] at f_mem
      | some node =>
        rw [eq_node, Option.is_some_and] at f_mem
        specialize each_step_sub_db_and_filtered n
        rw [eq_node, Option.is_none_or] at each_step_sub_db_and_filtered
        apply each_step_sub_db_and_filtered
        exact f_mem

    apply Set.finite_of_subset_finite _ res_sub_db_and_filtered
    apply Set.union_finite_of_both_finite
    . exact db.toFactSet.property.left
    . exact res_filtered_finite

  def isMfa [Inhabited sig.C] (rs : RuleSet sig) (finite : rs.rules.finite) (mfa_obs : MfaObsoletenessCondition sig) : Prop :=
    ∀ t, t ∈ (rs.mfaSet finite default mfa_obs).terms -> ¬ PreGroundTerm.cyclic t.val

  theorem terminates_of_isMfa [Inhabited sig.C] (rs : RuleSet sig) (rs_finite : rs.rules.finite) (mfa_obs : MfaObsoletenessCondition sig) :
      ∀ {obs : ObsoletenessCondition sig}, (mfa_obs.blocks_obs obs rs Inhabited.default) -> rs.isMfa rs_finite mfa_obs -> rs.terminates obs := by
    intro obs blocks isMfa
    apply rs.terminates_of_mfaSet_finite rs_finite mfa_obs blocks
    apply FactSet.finite_of_preds_finite_of_terms_finite
    . apply Set.finite_of_subset_finite _ (KnowledgeBase.deterministicSkolemChaseResult_predicates (rs.mfaKb rs_finite default) mfa_obs)
      apply Set.union_finite_of_both_finite
      . apply RuleSet.predicates_finite_of_finite
        exact rs_finite
      . have prop := (rs.mfaKb rs_finite default).db.toFactSet.property.left
        rcases prop with ⟨l, _, l_eq⟩
        exists (l.map (fun f => f.predicate)).eraseDupsKeepRight
        constructor
        . apply List.nodup_eraseDupsKeepRight
        . intro p
          rw [List.mem_eraseDupsKeepRight]
          rw [List.mem_map]
          unfold FactSet.predicates
          constructor
          . intro h
            rcases h with ⟨f, f_mem, p_eq⟩
            exists f
            constructor
            . rw [← l_eq]
              exact f_mem
            . exact p_eq
          . intro h
            rcases h with ⟨f, f_mem, p_eq⟩
            exists f
            constructor
            . rw [l_eq]
              exact f_mem
            . exact p_eq
    . unfold RuleSet.isMfa at isMfa
      let consts := rs.constants
      have consts_finite := rs.constants_finite_of_finite rs_finite
      rcases consts_finite with ⟨l_consts, l_consts_nodup, consts_eq⟩
      let funcs : Set (SkolemFS sig) := rs.skolem_functions
      have funcs_finite : funcs.finite := rs.skolem_functions_finite_of_finite rs_finite
      rcases funcs_finite with ⟨l_funcs, l_funcs_nodup, funcs_eq⟩
      let overapproximation : Set (GroundTerm sig) := fun t => (t.val.depth ≤ l_funcs.length + 1 ∧ (∀ c, c ∈ t.val.leaves -> c = default ∨ c ∈ l_consts) ∧ (∀ func, func ∈ t.val.innerLabels -> func ∈ l_funcs))
      have overapproximation_finite : overapproximation.finite := by
        exists (all_terms_limited_by_depth (default :: l_consts) l_funcs (l_funcs.length + 1)).eraseDupsKeepRight
        constructor
        . apply List.nodup_eraseDupsKeepRight
        . intro t
          rw [List.mem_eraseDupsKeepRight]
          rw [mem_all_terms_limited_by_depth]
          simp only [overapproximation, List.mem_cons]
          rfl
      apply Set.finite_of_subset_finite overapproximation_finite
      intro t t_mem

      have : ∀ func, func ∈ t.val.innerLabels -> func ∈ l_funcs := by
        intro func func_mem
        rw [funcs_eq]
        unfold funcs

        apply (KnowledgeBase.deterministicSkolemChaseResult_functions (rs.mfaKb rs_finite default))
        rcases t_mem with ⟨f, f_mem, t_mem⟩
        exists f
        constructor
        . exact f_mem
        . unfold Fact.function_symbols
          rw [List.mem_flatMap]
          exists t

      unfold overapproximation
      constructor
      . apply Decidable.byContradiction
        intro contra
        apply isMfa t t_mem
        apply PreGroundTerm.cyclic_of_depth_too_big t l_funcs
        . exact l_funcs_nodup
        . exact this
        . simp at contra
          apply Nat.succ_le_of_lt
          exact contra
      constructor
      . intro c c_mem

        have := (KnowledgeBase.deterministicSkolemChaseResult_constants (rs.mfaKb rs_finite default) mfa_obs)
        specialize this c (by
          unfold FactSet.constants
          rcases t_mem with ⟨f, f_mem, t_mem⟩
          exists f
          constructor
          . exact f_mem
          . unfold Fact.constants
            rw [List.mem_flatMap]
            exists t
        )
        rw [consts_eq]
        cases this with
        | inl this =>
          apply Or.inr
          apply RuleSet.head_constants_subset_constants
          exact this
        | inr this =>
          apply rs.mfaKb_db_constants rs_finite default
          exact this
      . exact this

  theorem terminates_of_isMfa_with_DeterministicSkolemObsoleteness [Inhabited sig.C] (rs : RuleSet sig) (rs_finite : rs.rules.finite) :
      rs.isMfa rs_finite (DeterministicSkolemObsoleteness sig) -> rs.terminates obs :=
    rs.terminates_of_isMfa rs_finite (DeterministicSkolemObsoleteness sig) (DeterministicSkolemObsoleteness.blocks_each_obs obs default rs)

  theorem terminates_of_isMfa_with_BlockingObsoleteness [GetFreshRepresentant sig.C] [Inhabited sig.C] (rs : RuleSet sig) (rs_finite : rs.rules.finite) (obs : ObsoletenessCondition sig) :
      rs.isMfa rs_finite (BlockingObsoleteness obs rs) -> rs.terminates obs :=
    rs.terminates_of_isMfa rs_finite (BlockingObsoleteness obs rs) (BlockingObsoleteness.blocks_corresponding_obs obs rs rs_finite default)

end RuleSet

