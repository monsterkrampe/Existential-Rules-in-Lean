import ExistentialRules.ChaseSequence.Termination.ConstantMappings.Basic

abbrev StrictConstantMapping (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] := TermMapping sig.C sig.C

namespace StrictConstantMapping

  variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

  def toConstantMapping (g : StrictConstantMapping sig) : ConstantMapping sig := fun c => GroundTerm.const (g c)

  def apply_var_or_const (g : StrictConstantMapping sig) : TermMapping (VarOrConst sig) (VarOrConst sig)
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

  theorem map_leaves_eq_leaves_mapLeaves (g : StrictConstantMapping sig) (t : FiniteTree (SkolemFS sig) sig.C) : t.leaves.map g = (t.mapLeaves (fun c => (g.toConstantMapping c).val)).leaves := by
    induction t with
    | leaf c => simp [FiniteTree.leaves, FiniteTree.mapLeaves, toConstantMapping, GroundTerm.const]
    | inner func ts ih =>
      simp only [FiniteTree.leaves, FiniteTree.mapLeaves]
      rw [List.map_flatMap, List.flatMap_map]
      unfold List.flatMap
      apply congrArg
      apply List.map_congr_left
      exact ih

  abbrev apply_function_free_atom (g : StrictConstantMapping sig) : FunctionFreeAtom sig -> FunctionFreeAtom sig := TermMapping.apply_generalized_atom g.apply_var_or_const

  theorem apply_function_free_atom_vars_eq (g : StrictConstantMapping sig) (a : FunctionFreeAtom sig) : (g.apply_function_free_atom a).variables = a.variables := by
    unfold apply_function_free_atom
    unfold TermMapping.apply_generalized_atom
    unfold FunctionFreeAtom.variables
    simp only
    rw [apply_var_or_const_filterVars_eq]

  abbrev apply_function_free_conj (g : StrictConstantMapping sig) : FunctionFreeConjunction sig -> FunctionFreeConjunction sig :=
    TermMapping.apply_generalized_atom_list g.apply_var_or_const

  theorem apply_function_free_conj_vars_eq (g : StrictConstantMapping sig) (conj : FunctionFreeConjunction sig) : (g.apply_function_free_conj conj).vars = conj.vars := by
    unfold apply_function_free_conj
    unfold TermMapping.apply_generalized_atom_list
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

