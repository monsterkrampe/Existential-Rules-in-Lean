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

  def matchVarorConst (s: GroundSubstitution sig) (t : VarOrConst sig) (gt : GroundTerm sig)(vars : List (sig.V)) : Option (GroundSubstitution sig) :=
  -- modifies Substitustion s such that t->gt if possible
    match t with
      | .const c => if gt = GroundTerm.const c then Option.some s else Option.none
      | .var v =>
          if v ∈ vars -- vars: List of variables, for which the substitutiion s is already 'properly' defined (has not just the dummy value anymore)
          then if gt = s v then Option.some s else Option.none--triit auf, wenn es für v schon eine andere substitution gab
          else some (extend_Substitutution s v gt)

  theorem matchVarorConst.apply_var_or_const {t: VarOrConst sig} {gt: GroundTerm sig}: ∀ subs , matchVarorConst s t gt vars = some subs -> subs.apply_var_or_const t = gt := by
    intro subs
    unfold matchVarorConst
    unfold GroundSubstitution.apply_var_or_const
    cases t with
    |var x =>
      simp only
      split
      . simp only [Option.ite_none_right_eq_some, Option.some.injEq, and_imp]
        intro eq_ap
        intro eq_sub
        rw[eq_ap]
        simp only [eq_sub]
      . unfold extend_Substitutution
        simp only [Option.some.injEq]
        intro fun_eq
        rw[<-fun_eq]
        simp
    |const c =>
      simp only
      by_cases eq_c: gt=GroundTerm.const c
      . simp[eq_c]
      . simp[eq_c]


  theorem matchVarorConst.noChange_vars {t: VarOrConst sig} : ∀ subs,  matchVarorConst s t gt vars = some subs -> v∈ vars ->  subs v = s v := by
    intro subs
    unfold matchVarorConst
    cases t with
    |var x =>
      simp
      by_cases var_x: x ∈ vars
      . simp only [var_x, ↓reduceIte, Option.ite_none_right_eq_some, Option.some.injEq, and_imp]
        intro a eq_sub var_v
        simp[eq_sub]
      . simp only [var_x, ↓reduceIte, Option.some.injEq]
        unfold extend_Substitutution
        intro a var_v
        have v_ne_x:¬  v = x := by intro eq; rw[eq] at var_v; contradiction
        rw[<- a]
        simp only [ite_eq_right_iff]
        intro v_eq_x
        contradiction
    |const c =>
      simp only [Option.ite_none_right_eq_some, Option.some.injEq, and_imp];
      intro a eq_sub var_v
      simp[eq_sub]


  def matchTermList (s: GroundSubstitution sig) (vars : List (sig.V)) (l : List ((VarOrConst sig) × (GroundTerm sig))) : Option (GroundSubstitution sig) :=
    --if possible, gives substitution subs s.t.  subs maps the List of VarOrConst to the List of GroundTerms
    match l with
    | .nil => Option.some s
    | (t, gt) :: ls =>
      have s' := matchVarorConst s t gt vars
      match s' with
      |Option.none => Option.none
      |Option.some s' =>
        match t with
        | .var v => matchTermList s' (v::vars) ls
        | .const _ => matchTermList s' vars ls


  theorem matchTermList.v_in_vars_noChange  {v: sig.V} :  ∀ s' s vars, v ∈ vars -> (matchTermList s vars ls) = some s' -> s' v = s v := by
    intro s'
    induction ls with
    |nil =>
      intro s vars mem_v
      unfold matchTermList
      simp only [Option.some.injEq]
      intro s_eq_s'
      rw[s_eq_s']
    |cons f fs ih =>
      unfold matchTermList
      simp only
      intro s vars var_v
      cases h: matchVarorConst s f.fst f.snd vars with
      |none => simp
      |some s'' =>
        have fun_eq: s'' v = s v := by
          revert var_v;
          apply matchVarorConst.noChange_vars;
          rw[h];
        simp only
        cases f.fst with
        |var x =>
          simp only
          intro a
          rw[<- fun_eq]
          have mem_v_ext : v ∈ (x::vars) := by simp[var_v]
          apply ih
          exact mem_v_ext
          exact a
        |const _ =>
          simp only
          rw[<-fun_eq]
          revert var_v
          apply ih

--this is my current idea how to do this -> works keep it
theorem matchTermList.apply_lists {l: List ((VarOrConst sig) × (GroundTerm sig))}:
∀ subs s vars, matchTermList s vars l = some subs -> l.unzip.fst.map subs.apply_var_or_const = l.unzip.snd := by
  intro subs
  induction l with
  |nil =>
    simp
  |cons f fs ih =>
    intro s vars
    unfold matchTermList
    cases s': matchVarorConst s f.fst f.snd vars with
    |none => simp
    |some s'' =>
      simp only[List.unzip_cons, List.map_cons, List.cons_eq_cons]
      intro h
      constructor
      . have fun_eq_on_x: subs.apply_var_or_const f.fst = s''.apply_var_or_const f.fst := by
          unfold GroundSubstitution.apply_var_or_const
          revert h
          cases f.fst with
          |var x => simp only; apply matchTermList.v_in_vars_noChange; simp;
          |const c => simp
        rw[fun_eq_on_x]
        apply matchVarorConst.apply_var_or_const
        exact s'
      . revert h
        cases f.fst with
        |var x => simp only; apply ih;
        |const c => simp only; apply ih;

    theorem matchTermList.some_if  {l: List ((VarOrConst sig) × (GroundTerm sig))}:
      (∃ (subs: GroundSubstitution sig), l.unzip.fst.map subs.apply_var_or_const = l.unzip.snd ∧ (∀ (x:sig.V), x∈ vars -> s x = subs x) ) ->  ∃ subs, matchTermList s vars l = some subs  := by
        intro h
        apply Exists.elim h
        intro a b
        --unfold matchTermList
        --have a := l.unzip.fst
        induction l generalizing s vars with
        |nil => unfold matchTermList; simp
        |cons t ts ih =>
          unfold matchTermList
          simp only
          unfold matchVarorConst
          simp only[List.unzip_cons, List.map_cons, List.cons_eq_cons] at b
          --unfold GroundSubstitution.apply_var_or_const at b
          revert b
          cases  t.fst with
          |var v =>
            simp only
            intro b
            by_cases v_mem_vars: v∈ vars
            . simp only[v_mem_vars, b, ite_cond_eq_true];
              have eq: a v = t.snd := by unfold GroundSubstitution.apply_var_or_const at b; simp only at b; exact b.left.left;
              simp[eq]
              apply ih
              exists a
              constructor
              . exact b.left.right
              . intro x x_in_v_vars; apply b.right; apply List.mem_of_mem_cons_of_mem; assumption;simp only[v_mem_vars]
              constructor
              . exact b.left.right
              . intro x x_in_v_vars; apply b.right; apply List.mem_of_mem_cons_of_mem; assumption;simp only[v_mem_vars]

            . simp[v_mem_vars]
              have precond_s : (extend_Substitutution s v t.snd) v = t.snd := by unfold extend_Substitutution; simp
              have x_vars_ext : ∀ x, x ∈ (v::vars) -> (extend_Substitutution s v t.snd) x = a x := by
                intro x
                simp[List.mem_cons, or_imp]
                constructor
                . intro xv; rw[xv] ; simp[precond_s]; apply Eq.symm; apply b.left.left;
                . simp[extend_Substitutution];
                  intro xv;
                  by_cases h: x=v
                  . rw[h] at xv; contradiction
                  . simp[h]; revert xv;  apply b.right;
              apply ih
              exists a
              constructor
              . exact b.left.right
              . assumption
              constructor
              . exact b.left.right
              . assumption
          |const c =>
            simp only
            intro b
            rw[<-b.left.left]
            unfold GroundSubstitution.apply_var_or_const
            simp
            apply ih
            exists a
            repeat exact And.intro b.left.right b.right



  -- The paper just calles this a homomorphism but we call this special kind of homomorphism a (ground) substitution.
  -- This will require auxiliary definitions.
  def GroundSubstitution.from_atom_and_fact (atom : FunctionFreeAtom sig) (fact : Fact sig) : Option (GroundSubstitution sig) :=
    if atom.predicate = fact.predicate
    then matchTermList (fun _ => default) List.nil (List.zip atom.terms fact.terms)  -- calls matchTermList with a dummy substiution and the Notion, that no variables have a meaningful substitution yet (Empty List)
    else Option.none


  theorem GroundSubstitution.apply_function_free_atom_from_atom_and_fact {atom : FunctionFreeAtom sig} {fact : Fact sig} :
      ∀ subs, (GroundSubstitution.from_atom_and_fact atom fact) = some subs -> subs.apply_function_free_atom atom = fact := by
        intro subs;
        unfold from_atom_and_fact;
        simp only [Option.ite_none_right_eq_some];
        simp only [and_imp];
        intro pred_eq;
        simp only [apply_function_free_atom]
        simp only [TermMapping.apply_generalized_atom]
        intro s
        have terms_length_eq : atom.terms.length = fact.terms.length := by simp only[GeneralizedAtom.arity_ok, pred_eq]
        let l:= atom.terms.zip fact.terms
        have a: l.unzip.fst = atom.terms:= by unfold l; apply List.unzip_zip_left; simp[terms_length_eq]
        have b: l.unzip.snd = fact.terms := by unfold l; apply List.unzip_zip_right; simp[terms_length_eq]
        have terms_eq : List.map subs.apply_var_or_const atom.terms = fact.terms
          := by rw[<-a,<-b];apply matchTermList.apply_lists; assumption
        simp[pred_eq, terms_eq]



  theorem GroundSubstitution.from_atom_and_fact_some_iff {atom : FunctionFreeAtom sig} {fact : Fact sig} :
      (∃ subs, (GroundSubstitution.from_atom_and_fact atom fact) = some subs) ↔ ∃ (subs : GroundSubstitution sig), subs.apply_function_free_atom atom = fact := by
        apply Iff.intro
        . intro h;
          apply Exists.elim h;
          intro a b;
          exists a;
          apply GroundSubstitution.apply_function_free_atom_from_atom_and_fact
          assumption
        . intro h;
          apply Exists.elim h
          intro a b
          unfold from_atom_and_fact
          simp only [Option.ite_none_right_eq_some, exists_and_left]
          constructor
          . unfold apply_function_free_atom at b
            unfold TermMapping.apply_generalized_atom at b
            rw[<-b]
          . apply matchTermList.some_if
            simp only[List.not_mem_nil, false_implies, implies_true, and_true]
            unfold apply_function_free_atom at b
            unfold TermMapping.apply_generalized_atom at b
            have len_eq: atom.terms.length = fact.terms.length := by rw[<-b]; simp;
            simp only [len_eq, List.unzip_zip]
            exists a
            rw[<-b]



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
