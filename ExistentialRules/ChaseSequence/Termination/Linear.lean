import ExistentialRules.ChaseSequence.Termination.Basic

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

section Rules

  def Rule.isLinear (rule : Rule sig) : Prop := rule.body.length = 1 -- maybe this should be ≤ 1 but equality makes things more elegant for now
  def Rule.exactlyTwoHeadAtoms (rule : Rule sig) (det : rule.isDeterministic) : Prop := (rule.head[0]'(by simp only [isDeterministic, decide_eq_true_iff] at det; simp [det])).length = 2

  -- in the context of the target paper, linear rules have the following properties
  structure LinearRule (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
    rule : Rule sig
    linear : rule.isLinear
    deterministic : rule.isDeterministic
    exactlyTwoHeadAtoms : rule.exactlyTwoHeadAtoms deterministic

  namespace LinearRule

    def body (rule : LinearRule sig) : FunctionFreeAtom sig := rule.rule.body[0]'(by have linear := rule.linear; simp only [Rule.isLinear] at linear; simp [linear])
    def head (rule : LinearRule sig) : FunctionFreeAtom sig × FunctionFreeAtom sig :=
      let conj := rule.rule.head[0]'(by have det := rule.deterministic; simp only [Rule.isDeterministic, decide_eq_true_iff] at det; simp [det])
      have length_conj : conj.length = 2 := by sorry
      (conj[0], conj[1])

  end LinearRule

  -- TODO for Lukas: unify this with regular RuleSet at some point
  structure LinearRuleSet (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
    rules : Set (LinearRule sig)
    id_unique : ∀ r1 r2, r1 ∈ rules ∧ r2 ∈ rules ∧ r1.rule.id = r2.rule.id -> r1 = r2

end Rules

section SubstitutionsAndTriggers

  -- The paper just calles this a homomorphism but we call this special kind of homomorphism a (ground) substitution.
  -- This will require auxiliary definitions.
  def GroundSubstitution.from_atom_and_fact (atom : FunctionFreeAtom sig) (fact : Fact sig) : Option (GroundSubstitution sig) := sorry

  theorem GroundSubstitution.apply_function_free_atom_from_atom_and_fact {atom : FunctionFreeAtom sig} {fact : Fact sig} :
      ∀ subs, (GroundSubstitution.from_atom_and_fact atom fact) = some subs -> subs.apply_function_free_atom atom = fact := by
    sorry

  theorem GroundSubstitution.from_atom_and_fact_some_iff {atom : FunctionFreeAtom sig} {fact : Fact sig} :
      ∃ subs, (GroundSubstitution.from_atom_and_fact atom fact) = some subs ↔ ∃ (subs : GroundSubstitution sig), subs.apply_function_free_atom atom = fact := by
    sorry

  def PreTrigger.from_rule_and_fact (rule : LinearRule sig) (fact : Fact sig) : Option (PreTrigger sig) :=
    (GroundSubstitution.from_atom_and_fact rule.body fact).map (fun subs => {
      rule := rule.rule
      subs := subs
    })

  -- this is definition 6 but we do not need the address u
  -- we use the already existing (Pre)Triggers to define the actual result of the rule application
  def ruleApply (rule : LinearRule sig) (fact : Fact sig) : Option (Fact sig × Fact sig) :=
    (PreTrigger.from_rule_and_fact rule fact).map (fun trg =>
      let mapped_head : List (List (Fact sig)) := trg.mapped_head
      have length_mapped_head : mapped_head.length = 1 := by simp only [mapped_head, PreTrigger.length_mapped_head]; sorry
      let conj := mapped_head[0]
      have length_conj : conj.length = 2 := by sorry
      (conj[0], conj[1])
    )

  -- This allows us to take a bit of a shortcut when we try to unfold the ruleApply definition in proofs.
  -- We could also use this for the definition instead but the above should be more canonical.
  theorem ruleApply_eq {rule : LinearRule sig} {fact : Fact sig} :
      let trg_opt := PreTrigger.from_rule_and_fact rule fact
      ruleApply rule fact = trg_opt.map (fun trg => (trg.apply_to_function_free_atom 0 rule.head.fst, trg.apply_to_function_free_atom 0 rule.head.snd)) := by
    sorry

end SubstitutionsAndTriggers

section Addresses

  structure AddressSymbol (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
    rule : Rule sig
    headIndex : Fin 2

  -- address symbols for a rule set
  def addressSymbols (rs : LinearRuleSet sig) : Set (AddressSymbol sig) :=
    fun sym => sym.rule ∈ rs.rules.map (LinearRule.rule)

  -- NOTE: Maybe an inductive definition with multiple cases would be more useful here, not sure yet...
  structure Address (fs : FactSet sig) (rs : LinearRuleSet sig) where
    initialAtom : {f : Fact sig // f ∈ fs}
    path : List {sym : AddressSymbol sig // sym ∈ addressSymbols rs}

  structure Forest (fs : FactSet sig) (rs : LinearRuleSet sig) where
    f : Set (Address fs rs)
    fs_contained : sorry -- fs shall be contained in f (this should likely involve auxiliary definitions)
    isPrefixClosed : sorry

end Addresses

section ObvliviousChaseRepresentation

  -- TODO for Laila: formalize definition 7; this should mostly come down to recursively define the fact associated with an address
  -- Maybe we need to discuss this as it might not be quite obvious how to do it.
  -- I think the idea would be to first define the labelling function returning an option and then to define the oblivious chase representation as the forest of all addresses where the labelling function returns some ... on each address.

end ObvliviousChaseRepresentation

