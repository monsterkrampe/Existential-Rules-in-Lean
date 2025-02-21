import ExistentialRules.Triggers.Obsoleteness

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {obs : LaxObsoletenessCondition sig}

def RTrigger (obs : LaxObsoletenessCondition sig) (r : RuleSet sig) := { trg : Trigger obs // trg.rule ∈ r.rules}

namespace RTrigger

  def equiv (trg1 trg2 : RTrigger obs rs) : Prop := trg1.val.equiv trg2.val

  theorem funcTermForExisVarInMultipleTriggersMeansTheyAreTheSame
    {rs : RuleSet sig}
    (trg1 trg2 : RTrigger obs rs)
    (disjIndex1 : Fin trg1.val.rule.head.length)
    (disjIndex2 : Fin trg2.val.rule.head.length)
    (var1 var2 : sig.V)
    (var1_not_in_frontier : ¬ var1 ∈ trg1.val.rule.frontier)
    (var2_not_in_frontier : ¬ var2 ∈ trg2.val.rule.frontier)
    :
    (trg1.val.apply_to_var_or_const disjIndex1 (VarOrConst.var var1)) = (trg2.val.apply_to_var_or_const disjIndex2 (VarOrConst.var var2))
    ->
    trg1.equiv trg2 ∧ disjIndex1.val = disjIndex2.val := by
    intro applications_eq
    rw [PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ var1_not_in_frontier] at applications_eq
    rw [PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ var2_not_in_frontier] at applications_eq
    simp only [PreTrigger.functional_term_for_var, GroundTerm.func] at applications_eq
    rw [Subtype.mk.injEq, FiniteTree.inner.injEq, SkolemFS.mk.injEq] at applications_eq
    have rules_eq : trg1.val.rule = trg2.val.rule := by
      apply rs.id_unique
      constructor
      . exact trg1.property
      constructor
      . exact trg2.property
      . exact applications_eq.left.left
    constructor
    . unfold equiv
      unfold PreTrigger.equiv
      constructor
      . exact rules_eq
      . have right := applications_eq.right
        rw [← FiniteTreeList.eqIffFromListEq _ _] at right
        have : trg1.val.rule.frontier = trg2.val.rule.frontier := by rw [rules_eq]
        rw [← this] at right
        rw [List.eq_iff_unattach_eq, List.map_eq_map_iff] at right
        intro v v_mem
        apply right
        exact v_mem
    . exact applications_eq.left.right.left

end RTrigger

