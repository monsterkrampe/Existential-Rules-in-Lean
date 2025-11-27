import ExistentialRules.ChaseSequence.Termination.Basic

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] [Inhabited sig.C]

section Rules

  def Rule.isLinear (rule : Rule sig) : Prop := rule.body.length = 1 -- maybe this should be ≤ 1 but equality makes things more elegant for now
  def Rule.exactlyTwoHeadAtoms (rule : Rule sig) (det : rule.isDeterministic) : Prop := (rule.head[0]'(by simp only [isDeterministic, decide_eq_true_iff] at det; simp [det])).length = 2
  --general rules in (AtomsAndFacts.Basic) allow lists of conjunctions in their head (instead of just cunjunctions of atoms), this is why the above def. is so complicated

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
      have length_conj : conj.length = 2 := by have twohead := rule.exactlyTwoHeadAtoms; simp only [Rule.exactlyTwoHeadAtoms] at twohead; simp[conj,twohead];
      (conj[0], conj[1])

  end LinearRule

  -- TODO for Lukas: unify this with regular RuleSet at some point
  structure LinearRuleSet (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
    rules : Set (LinearRule sig)
    id_unique : ∀ r1 r2, r1 ∈ rules ∧ r2 ∈ rules ∧ r1.rule.id = r2.rule.id -> r1 = r2

end Rules

section SubstitutionsAndTriggers

  def extend_Substitutution  (s: GroundSubstitution sig) (v: sig.V) (c: GroundTerm sig) : GroundSubstitution sig := fun x => if x = v then c else s x

  def matchVarorCons (s: GroundSubstitution sig) (t : VarOrConst sig) (gt : GroundTerm sig)(vars : List (sig.V)) : Option (GroundSubstitution sig) :=
    match t with
      | .const c => if gt = GroundTerm.const c then Option.some s else Option.none
      | .var v =>
          if v ∈ vars -- Varas ist liste von variablen, die schon eine zuordnung in s haben
          then if gt = s v then Option.some s else Option.none--triit auf, wenn es für v schon eine andere substitution gab
          else some (extend_Substitutution s v gt)

  def matchTermList (s: GroundSubstitution sig) (vars : List (sig.V)) (l : List ((VarOrConst sig) × (GroundTerm sig))) : Option (GroundSubstitution sig) :=
    match l with
    | .nil => Option.some s
    | (t, gt) :: ls =>
      have s' := matchVarorCons s t gt vars
      match s' with
      |Option.none => Option.none
      |Option.some s' =>
        match t with
        | .var v => matchTermList s' (v::vars) ls
        | .const _ => matchTermList s' vars ls

  -- The paper just calles this a homomorphism but we call this special kind of homomorphism a (ground) substitution.
  -- This will require auxiliary definitions.
  def GroundSubstitution.from_atom_and_fact (atom : FunctionFreeAtom sig) (fact : Fact sig) : Option (GroundSubstitution sig) :=
    if atom.predicate = fact.predicate
    then matchTermList (fun _ => default) List.nil (List.zip atom.terms fact.terms)  --> wie kann ich die substiution initial definieren?
    else Option.none


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

  theorem PreTrigger.from_rule_and_fact_some_implies {rule : LinearRule sig} {fact : Fact sig} :
      ∀ {trg}, PreTrigger.from_rule_and_fact rule fact = some trg → trg.rule = rule.rule ∧ GroundSubstitution.from_atom_and_fact rule.body fact = some trg.subs := by
        unfold PreTrigger.from_rule_and_fact;
        cases PreTrigger.from_rule_and_fact rule fact;
        repeat simp;


  -- this is definition 6 but we do not need the address u
  -- we use the already existing (Pre)Triggers to define the actual result of the rule application
  def ruleApply (rule : LinearRule sig) (fact : Fact sig) : Option (Fact sig × Fact sig) :=
    (PreTrigger.from_rule_and_fact rule fact).attach.map (fun ⟨trg, trg_orig⟩ =>
      have h:= And.left (PreTrigger.from_rule_and_fact_some_implies trg_orig);
      have det := rule.deterministic;
      let mapped_head : List (List (Fact sig)) := trg.mapped_head
      have length_mapped_head : mapped_head.length = 1 := by
        simp only [mapped_head, PreTrigger.length_mapped_head];
        rw[h]
        simp [Rule.isDeterministic] at det;
        exact det;
      let conj := mapped_head[0]
      have length_conj : conj.length = 2 := by
        simp only [mapped_head, conj];
        have h2 := (PreTrigger.length_each_mapped_head trg 0);
          simp[mapped_head, length_mapped_head] at h2;
          simp [Rule.isDeterministic] at det; simp[h, det] at h2;
          rw[h2];
          have twohead := rule.exactlyTwoHeadAtoms; simp only [Rule.exactlyTwoHeadAtoms] at twohead;
          simp[twohead];
      (conj[0], conj[1])
    )

  -- This allows us to take a bit of a shortcut when we try to unfold the ruleApply definition in proofs.
  -- We could also use this for the definition instead but the above should be more canonical.
  theorem ruleApply_eq {rule : LinearRule sig} {fact : Fact sig} :
      let trg_opt := (PreTrigger.from_rule_and_fact rule fact)
      ruleApply rule fact = trg_opt.map (fun trg => (trg.apply_to_function_free_atom 0 rule.head.fst, trg.apply_to_function_free_atom 0 rule.head.snd)) := by
      intro tr;
      rw[ruleApply];
      have htr : PreTrigger.from_rule_and_fact rule fact = tr := rfl;
      rcases tr ;
      -- case none
      simp;
      rw[htr];
      --case some
      simp;
      simp [PreTrigger.mapped_head];
      simp[LinearRule.head];
      expose_names;
      exists val;
      exists htr;
      simp[And.left (PreTrigger.from_rule_and_fact_some_implies htr)];

end SubstitutionsAndTriggers

section Addresses

  structure AddressSymbol (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
    rule : LinearRule sig
    headIndex : Fin 2

  -- address symbols for a rule set
  def addressSymbols (rs : LinearRuleSet sig) : Set (AddressSymbol sig) :=
    fun sym => sym.rule ∈ rs.rules

  -- NOTE: Maybe an inductive definition with multiple cases would be more useful here, not sure yet...
  structure Address (fs : FactSet sig) (rs : LinearRuleSet sig) where
    initialAtom : {f : Fact sig // f ∈ fs}
    path : List {sym : AddressSymbol sig // sym ∈ addressSymbols rs} --Frage: wie herum die liste besser füllen? (in lesrichtung, oder so, dass das neue elem. immer vorne drangehängt wird)


/-
  def all_prefix_addresses_in_set {fs: FactSet sig} (a: Address fs rs) (f: Set (Address fs rs)) : Prop :=
    match a.path with
    |[] => true
    |list => let b:= {a with path := list.dropLastTR}; b ∈ f ∧ all_prefix_addresses_in_set b f
 -/

 -- with this definition, we use the List of address-symbols that bulids the path from rigth to left (contrary on how it's written in the paper)
 -- therefore we would write an address wuv ∈ IA* (with w ∈ I, u,v ∈ A) as {initialAtom := w , path :=[v,u]}
  def immed_prefix_address_in_set {fs: FactSet sig} (a: Address fs rs) (f : Set (Address fs rs)) : Prop :=
    match a.path with
    |[] => true
    |_::ls => let b:= {a with path := ls}; b ∈ f


  structure Forest (fs : FactSet sig) (rs : LinearRuleSet sig) where
    f : Set (Address fs rs)
    fs_contained : ∀ fact ∈ fs, ∃ a ∈ f , fact = a.initialAtom ∧ a.path = []  -- fs shall be contained in f (this should likely involve auxiliary definitions)
    isPrefixClosed : ∀ a ∈ f, immed_prefix_address_in_set a f --as we enforce this check on all a ∈ f, we only need to veryfy that it's immediate predecessor is in f as well

end Addresses

section ObvliviousChaseRepresentation

  -- TODO for Laila: formalize definition 7; this should mostly come down to recursively define the fact associated with an address
  -- Maybe we need to discuss this as it might not be quite obvious how to do it.
  -- I think the idea would be to first define the labelling function returning an option and then to define the oblivious chase representation as the forest of all addresses where the labelling function returns some ... on each address.

  def labellingFunction {rs: LinearRuleSet sig} (w : Address fs rs) : Option (Fact sig) :=
    match eq : w.path with
    |[] => w.initialAtom
    |r::u =>
      have termination_hint : u.length < w.path.length := by simp [eq]
      let lu := labellingFunction {w with path := u};
      match lu with
      |Option.none => Option.none
      |some lu => (ruleApply r.val.rule lu ).map (fun x => if r.val.headIndex = 0 then x.fst else x.snd) --wie kann ich hier zeigen, dass u : AddressSymbol ist? --
  termination_by w.path.length

  def oblivious_chase (fs : FactSet sig) (rs : LinearRuleSet sig) : Forest fs rs where
    f := fun addr => (labellingFunction addr).isSome
    fs_contained := by
      intro fact fact_mem
      exists {initialAtom := ⟨fact, fact_mem⟩, path := []}
      constructor
      . unfold labellingFunction; simp only [Membership.mem, Option.isSome_some]
      . simp
    isPrefixClosed := by
      intro addr
      simp only [Option.isSome_iff_ne_none, immed_prefix_address_in_set]
      intro addr_ne_none
      cases eq : addr.path with
      | nil => simp
      | cons r u =>
        simp only
        intro contra
        apply addr_ne_none
        unfold labellingFunction
        split
        case h_1 heq => rw [eq] at heq; simp at heq
        case h_2 r' u' heq =>
          simp only
          rw [eq, List.cons_eq_cons] at heq
          rw [← heq.right, contra]

end ObvliviousChaseRepresentation
