import ExistentialRules.Triggers.Obsoleteness

/-!
# Ruleset Triggers

`Trigger`s are still not enough yet. We introduce one more layer on top, which we call `RTrigger` for Ruleset Trigger.
It makes sense that, when we want to chase a set of rules, we only consider triggers that feature rules that indeed occur in the rule set.
We capture this simply in a subtype.
-/

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {obs : LaxObsoletenessCondition sig}

/-- An `RTrigger` for a `RuleSet` $R$ is a `Trigger` with a rule in $R$. -/
def RTrigger (obs : LaxObsoletenessCondition sig) (r : RuleSet sig) := { trg : Trigger obs // trg.rule ∈ r.rules}

namespace RTrigger

/-- Two `RTrigger`s are equivalent if the underlying `PreTrigger`s are. -/
def equiv (trg1 trg2 : RTrigger obs rs) : Prop := trg1.val.equiv trg2.val

/-- If a ground term is fresh in two `RTriggers` for two head indices, then actually these two `RTriggers` (and indices) need to be equivalent (the same)! Why is this the case? Fresh terms are always Skolem function terms. Therefore they contain a rule id. Since we know that rules are uniquely identified by their id in a `RuleSet`, we can infer that the rules of the triggers are the same. The head indices are also part of the functional term so a similar argument can be made to show that these need to be equal. To see why the triggers also need to agree on their frontier mapping, we only need to remind ourselves that the Skolem term contains all the mapped frontier terms as arguments. -/
theorem equiv_of_term_mem_fresh_terms_for_head_disjunct
    {rs : RuleSet sig}
    {trg1 trg2 : RTrigger obs rs}
    {i1 i2 : Nat}
    {lt1 : i1 < trg1.val.rule.head.length}
    {lt2 : i2 < trg2.val.rule.head.length}
    {t : GroundTerm sig} :
    (t ∈ trg1.val.fresh_terms_for_head_disjunct i1 lt1) ->
      (t ∈ trg2.val.fresh_terms_for_head_disjunct i2 lt2) ->
        trg1.equiv trg2 ∧ i1 = i2 := by
  unfold PreTrigger.fresh_terms_for_head_disjunct PreTrigger.functional_term_for_var
  simp only [List.mem_map]
  rintro ⟨v1, v1_mem, t_eq⟩ ⟨v2, v2_mem, t_eq2⟩
  rw [← t_eq2] at t_eq
  simp only [GroundTerm.func] at t_eq
  rw [Subtype.mk.injEq, FiniteTree.inner.injEq, SkolemFS.mk.injEq] at t_eq
  have rules_eq : trg1.val.rule = trg2.val.rule := by
    apply rs.id_unique
    constructor
    . exact trg1.property
    constructor
    . exact trg2.property
    . exact t_eq.left.left
  constructor
  . unfold equiv
    unfold PreTrigger.equiv
    constructor
    . exact rules_eq
    . have right := t_eq.right
      have : trg1.val.rule.frontier = trg2.val.rule.frontier := by rw [rules_eq]
      rw [← this] at right
      rw [List.eq_iff_unattach_eq, List.map_eq_map_iff] at right
      intro v v_mem
      apply right
      exact v_mem
  . exact t_eq.left.right.left

end RTrigger

