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

    theorem Atom_pred_eq_implies_eq_term_length {a b : GeneralizedAtom sig (T)}:
      a.predicate = b.predicate -> a.terms.length = b.terms.length := by
        intro pred_eq
        rw[GeneralizedAtom.arity_ok]
        rw[pred_eq]
        rw[GeneralizedAtom.arity_ok]

    theorem LinearRule.body_eq {rule : LinearRule sig}: rule.rule.body = [rule.body] := by
      unfold LinearRule.body
      have rule_body_len: rule.rule.body.length = 1 := by apply rule.linear
      rw[List.length_eq_one_iff] at rule_body_len
      rcases rule_body_len with ⟨a, rule_body_len ⟩
      simp[rule_body_len]

    theorem LinearRule.head_eq {rule : LinearRule sig}: rule.rule.head = [[rule.head.fst, rule.head.snd]] := by
      unfold LinearRule.head
      simp
      have rule_head_len: rule.rule.head.length = 1 := by have det := rule.deterministic; simp only [Rule.isDeterministic, decide_eq_true_iff] at det; exact det
      have two_atoms: rule.rule.head[0].length = 2 := by have twohead := rule.exactlyTwoHeadAtoms; simp only [Rule.exactlyTwoHeadAtoms] at twohead; exact twohead;
      revert two_atoms
      rw[List.length_eq_one_iff] at rule_head_len
      rcases rule_head_len with ⟨head, rule_head_eq⟩
      simp[rule_head_eq]
      --intro lentwo
      cases head with
      |nil =>
        simp
      |cons a rest =>
        simp
        rw[List.length_eq_one_iff]
        intro rest
        rcases rest with ⟨x, y ⟩
        simp[y]

   def is_frontier_position_fst (rule: LinearRule sig)  (i: Nat) (i_valid: i < rule.head.fst.terms.length) : Prop :=
      ∃ v, (rule.head.fst.terms[i]'(by exact i_valid)) = VarOrConst.var v ∧ v ∈ rule.rule.frontier

    theorem frontier_pos_fst_iff_in_body {rule: LinearRule sig} {i: Nat} {i_valid: i < rule.head.fst.terms.length} :
      is_frontier_position_fst rule i i_valid ↔
      ∃ j , ∃ h: j < rule.body.terms.length, rule.head.fst.terms[i].isVar ∧ rule.head.fst.terms[i] = rule.body.terms[j] := by
      unfold is_frontier_position_fst
      constructor
      . intro h
        rcases h with ⟨v, h⟩
        simp only [exists_and_left]
        constructor
        . unfold VarOrConst.isVar
          simp only[h.left]
        . rcases rule.rule.frontier_occurs_in_body v h.right with ⟨a, a_body, v_a⟩
          simp only[h]
          simp only[List.mem_iff_getElem] at v_a
          simp only [LinearRule.body_eq, List.mem_cons, List.not_mem_nil, or_false] at a_body
          rw[a_body] at v_a
          rcases v_a with ⟨c, len, v_a⟩
          exists c, len
          simp[v_a]
      . intro h
        rcases h with ⟨j, j_lt, t_var , t_eq⟩
        have v_ex: ∃ v, rule.head.fst.terms[i] = VarOrConst.var v := by
          unfold VarOrConst.isVar at t_var
          cases h: rule.head.fst.terms[i]
          . simp
          . simp [h] at t_var
        rcases v_ex with ⟨v, v_eq⟩
        exists v
        simp only[v_eq]
        unfold Rule.frontier
        simp only [List.mem_filter, List.any_eq_true, decide_eq_true_eq, true_and]
        constructor
        . unfold FunctionFreeConjunction.vars
          simp only [LinearRule.body_eq, List.flatMap_cons, List.flatMap_nil, List.append_nil]
          unfold FunctionFreeAtom.variables
          apply VarOrConst.mem_filterVars_of_var
          simp only [List.mem_iff_getElem]
          exists j, j_lt
          rw[← t_eq]
          exact v_eq
        . have rle_head_len: rule.rule.head.length = 1 := by have det := rule.deterministic; simp only [Rule.isDeterministic, decide_eq_true_iff] at det; exact det
          simp only [List.mem_iff_getElem, rle_head_len]
          simp only[← List.mem_iff_getElem]
          unfold FunctionFreeConjunction.vars
          simp only [LinearRule.head_eq]
          unfold FunctionFreeAtom.variables
          simp only [List.getElem_singleton, Nat.lt_one_iff, exists_prop, exists_eq_left,
            List.mem_flatMap, exists_eq_left', List.mem_cons, List.not_mem_nil, or_false,
            exists_eq_or_imp]
          apply Or.inl
          apply VarOrConst.mem_filterVars_of_var
          simp only[List.mem_iff_getElem]
          exists i, i_valid

    def is_frontier_position_snd (rule: LinearRule sig)  (i: Nat) (i_valid: i < rule.head.snd.terms.length) : Prop :=
      ∃ v, (rule.head.snd.terms[i]'(by exact i_valid)) = VarOrConst.var v ∧ v ∈ rule.rule.frontier

    theorem frontier_pos_snd_iff_in_body {rule: LinearRule sig} {i: Nat} {i_valid: i < rule.head.snd.terms.length} :
      is_frontier_position_snd rule i i_valid ↔
      ∃ j , ∃ h: j < rule.body.terms.length, rule.head.snd.terms[i].isVar ∧ rule.head.snd.terms[i] = rule.body.terms[j] := by
      unfold is_frontier_position_snd
      constructor
      . intro h
        rcases h with ⟨v, h⟩
        simp
        constructor
        . unfold VarOrConst.isVar
          simp[h.left]
        . rcases rule.rule.frontier_occurs_in_body v h.right with ⟨a, a_body, v_a⟩
          simp only[h]
          simp only[List.mem_iff_getElem] at v_a
          simp only [LinearRule.body_eq, List.mem_cons, List.not_mem_nil, or_false] at a_body
          rw[a_body] at v_a
          rcases v_a with ⟨c, len, v_a⟩
          exists c, len
          simp[v_a]
      . intro h
        rcases h with ⟨j, j_lt, t_var , t_eq⟩
        have v_ex: ∃ v, rule.head.snd.terms[i] = VarOrConst.var v := by
          unfold VarOrConst.isVar at t_var
          cases h: rule.head.snd.terms[i]
          . simp
          . simp [h] at t_var
        rcases v_ex with ⟨v, v_eq⟩
        exists v
        simp only[v_eq]
        unfold Rule.frontier
        simp only [List.mem_filter, List.any_eq_true, decide_eq_true_eq, true_and]
        constructor
        . unfold FunctionFreeConjunction.vars
          simp only [LinearRule.body_eq, List.flatMap_cons, List.flatMap_nil, List.append_nil]
          unfold FunctionFreeAtom.variables
          apply VarOrConst.mem_filterVars_of_var
          simp only [List.mem_iff_getElem]
          exists j, j_lt
          rw[← t_eq]
          exact v_eq
        . have rle_head_len: rule.rule.head.length = 1 := by have det := rule.deterministic; simp only [Rule.isDeterministic, decide_eq_true_iff] at det; exact det
          simp only [List.mem_iff_getElem, rle_head_len]
          simp only[← List.mem_iff_getElem]
          unfold FunctionFreeConjunction.vars
          simp only [LinearRule.head_eq]
          unfold FunctionFreeAtom.variables
          simp only [List.getElem_singleton, Nat.lt_one_iff, exists_prop, exists_eq_left,
            List.mem_flatMap, exists_eq_left', List.mem_cons, List.not_mem_nil, or_false,
            exists_eq_or_imp]
          apply Or.inr
          apply VarOrConst.mem_filterVars_of_var
          simp only[List.mem_iff_getElem]
          exists i, i_valid


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

  theorem matchVarorConst.apply_var_or_const {s : GroundSubstitution sig} {t : VarOrConst sig} {gt : GroundTerm sig} {vars : List sig.V} :
    ∀ subs ∈  matchVarorConst s t gt vars, subs.apply_var_or_const t = gt := by
    simp only [Option.mem_def]
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


  theorem matchVarorConst.noChange_vars {s : GroundSubstitution sig} {t : VarOrConst sig} {gt : GroundTerm sig} {vars : List sig.V} :
      ∀ subs ∈ matchVarorConst s t gt vars, v∈ vars ->  subs v = s v := by
    simp only [Option.mem_def]
    intro subs
    unfold matchVarorConst
    cases t with
    |var x =>
      simp
      -- cases Decidable.em (x ∈ vars) with -- would also work
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


  theorem matchTermList.v_in_vars_noChange  {v: sig.V} :  ∀ s vars, v ∈ vars -> ∀ s' ∈ (matchTermList s vars ls) , s' v = s v := by
    induction ls with
    |nil =>
      intro s vars mem_v s'
      unfold matchTermList
      simp only [Option.mem_def,Option.some.injEq]
      intro s_eq_s'
      rw[s_eq_s']
    |cons f fs ih =>
      unfold matchTermList
      simp only
      intro s vars var_v s'
      cases h: matchVarorConst s f.fst f.snd vars with
      |none => simp
      |some s'' =>
        have fun_eq: s'' v = s v := by
          revert var_v;
          apply matchVarorConst.noChange_vars;
          simp only[Option.mem_def]
          exact h
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
          apply ih
          exact var_v

  theorem matchTermList.apply_lists {l: List ((VarOrConst sig) × (GroundTerm sig))}:
  ∀ s vars, ∀ subs ∈ matchTermList s vars l , l.unzip.fst.map subs.apply_var_or_const = l.unzip.snd := by
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
        intro subs
        intro h
        constructor
        . have fun_eq_on_x: subs.apply_var_or_const f.fst = s''.apply_var_or_const f.fst := by
            unfold GroundSubstitution.apply_var_or_const
            revert h
            cases f.fst with
            |var x => simp only; apply matchTermList.v_in_vars_noChange; simp;
            |const c => simp
          rw[fun_eq_on_x]
          apply matchVarorConst.apply_var_or_const;
          exact s'
        . revert h
          cases f.fst with
          |var x => simp only; apply ih;
          |const c => simp only; apply ih;

  theorem matchTermList.some_if
    {l : List ((VarOrConst sig) × (GroundTerm sig))}
    {subs : GroundSubstitution sig}
    (map_unzip_eq : l.unzip.fst.map subs.apply_var_or_const = l.unzip.snd)
    (subs_agrees_on_vars : ∀ (x:sig.V), x∈ vars -> s x = subs x) :
    -- TODO for Laila: Does it make sense to not only show existence of some subs here but to actually show something like the following?: (matchTermList s vars l).is_some_and (fun subs' => ∀ v ∈ vars, subs v = subs' v)
    --I'm not sure if that's necessary because we also have the prevoius theorem nce we showed the existence of the subs... (It's not exactly the same statement though)
    ∃ subs, matchTermList s vars l = some subs  := by
      induction l generalizing s vars with
      |nil => unfold matchTermList; simp
          |cons t ts ih =>
            unfold matchTermList
            simp only
            unfold matchVarorConst
            simp only[List.unzip_cons, List.map_cons, List.cons_eq_cons] at map_unzip_eq
            revert map_unzip_eq
            cases  t.fst with
            |var v =>
              simp only
              intro map_unzip_eq
              by_cases v_mem_vars: v∈ vars
              . simp only[v_mem_vars, subs_agrees_on_vars, ite_cond_eq_true];
                have eq: subs v = t.snd := by unfold GroundSubstitution.apply_var_or_const at map_unzip_eq; simp only at map_unzip_eq; exact map_unzip_eq.left;
                simp[eq]
                apply ih
                . exact map_unzip_eq.right
                . intro v v_mem; apply subs_agrees_on_vars; exact List.mem_of_mem_cons_of_mem v_mem v_mem_vars
              . simp[v_mem_vars]
                have precond_s : (extend_Substitutution s v t.snd) v = t.snd := by unfold extend_Substitutution; simp
                have x_vars_ext : ∀ x, x ∈ (v::vars) -> (extend_Substitutution s v t.snd) x = subs x := by
                  intro x
                  simp[List.mem_cons, or_imp]
                  constructor
                  . intro xv; rw[xv] ; simp[precond_s]; apply Eq.symm; apply map_unzip_eq.left;
                  . simp[extend_Substitutution];
                    intro xv;
                    by_cases h: x=v
                    . rw[h] at xv; contradiction
                    . simp[h]; revert xv;  apply subs_agrees_on_vars;
                apply ih
                . exact map_unzip_eq.right
                . exact x_vars_ext
            |const c =>
              simp only
              intro map_unzip_eq
              rw[<- map_unzip_eq.left]
              unfold GroundSubstitution.apply_var_or_const
              simp
              apply ih
              . exact map_unzip_eq.right
              . exact subs_agrees_on_vars



  -- The paper just calles this a homomorphism but we call this special kind of homomorphism a (ground) substitution.
  -- This will require auxiliary definitions.
  def GroundSubstitution.from_atom_and_fact (atom : FunctionFreeAtom sig) (fact : Fact sig) : Option (GroundSubstitution sig) :=
    if atom.predicate = fact.predicate
    then matchTermList (fun _ => default) List.nil (List.zip atom.terms fact.terms)  -- calls matchTermList with a dummy substiution and the Notion, that no variables have a meaningful substitution yet (Empty List)
    else Option.none


  theorem GroundSubstitution.apply_function_free_atom_from_atom_and_fact {atom : FunctionFreeAtom sig} {fact : Fact sig} :
      ∀ subs ∈ GroundSubstitution.from_atom_and_fact atom fact, subs.apply_function_free_atom atom = fact := by
        intro subs;
        unfold from_atom_and_fact;
        simp only [Option.mem_def, Option.ite_none_right_eq_some, and_imp]
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

  theorem GroundSubstitution.i_lt_atom_terms_len_iff_fact_terms_len {atom: FunctionFreeAtom sig} {fact : Fact sig} :
    ∀ subs ∈ GroundSubstitution.from_atom_and_fact atom fact, ∀ i, (i < atom.terms.length) ↔  i < fact.terms.length := by
      intro subs subs_mem i
      constructor
      . intro i_valid
        have subs_appy: subs.apply_function_free_atom atom = fact := by rw[GroundSubstitution.apply_function_free_atom_from_atom_and_fact]; exact subs_mem
        rw[← subs_appy]
        simp only [GroundSubstitution.apply_function_free_atom, TermMapping.length_terms_apply_generalized_atom]
        exact i_valid
      . intro i_valid
        have subs_appy: subs.apply_function_free_atom atom = fact := by rw[GroundSubstitution.apply_function_free_atom_from_atom_and_fact]; exact subs_mem
        rw[← subs_appy] at i_valid
        simp only [GroundSubstitution.apply_function_free_atom, TermMapping.length_terms_apply_generalized_atom] at i_valid
        exact i_valid

  theorem GroundSubstitution.from_atom_and_fact_some_iff {atom : FunctionFreeAtom sig} {fact : Fact sig} :
      (∃ subs, (GroundSubstitution.from_atom_and_fact atom fact) = some subs) ↔ ∃ (subs : GroundSubstitution sig), subs.apply_function_free_atom atom = fact := by
        apply Iff.intro
        . intro h;
          rcases h with ⟨subs, h⟩
          exists subs
          apply GroundSubstitution.apply_function_free_atom_from_atom_and_fact
          exact h
        . intro h;
          rcases h with ⟨subs, h⟩
          unfold from_atom_and_fact
          simp only [Option.ite_none_right_eq_some, exists_and_left]
          constructor
          . unfold apply_function_free_atom at h
            unfold TermMapping.apply_generalized_atom at h
            rw[<-h]
          . apply matchTermList.some_if
            . unfold apply_function_free_atom at h
              unfold TermMapping.apply_generalized_atom at h
              have len_eq: atom.terms.length = fact.terms.length := by rw[<-h]; simp;
              simp only [len_eq, List.unzip_zip]
              rw[<-h]
            . simp only[List.not_mem_nil, false_implies, implies_true]



  def PreTrigger.from_rule_and_fact (rule : LinearRule sig) (fact : Fact sig) : Option (PreTrigger sig) :=
    (GroundSubstitution.from_atom_and_fact rule.body fact).map (fun subs => {
      rule := rule.rule
      subs := subs
    })

  theorem PreTrigger.from_rule_and_fact_some_implies {rule : LinearRule sig} {fact : Fact sig} :
    -- TODO for Laila: again that could use Option.is_none_or again. Actually there is even the possibility of writing
    -- ∀ trg ∈ PreTrigger.from_rule_and_fact rule fact -> ...
    -- since Membership is defined on Option. Now that I think about it, maybe this is in fact the best option (no pun intended) all throughout.
      ∀ trg ∈ PreTrigger.from_rule_and_fact rule fact,  trg.rule = rule.rule ∧ GroundSubstitution.from_atom_and_fact rule.body fact = some trg.subs := by
        unfold PreTrigger.from_rule_and_fact;
        cases PreTrigger.from_rule_and_fact rule fact;
        repeat simp;


  -- this is definition 6 but we do not need the address u
  -- we use the already existing (Pre)Triggers to define the actual result of the rule application
  def ruleApply (rule : LinearRule sig) (fact : Fact sig) : Option (Fact sig × Fact sig) :=
    (PreTrigger.from_rule_and_fact rule fact).attach.map (fun ⟨trg, trg_orig⟩ =>
      have h:= And.left (PreTrigger.from_rule_and_fact_some_implies trg trg_orig);
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
      simp[And.left (PreTrigger.from_rule_and_fact_some_implies val htr)];

  theorem ruleApply.some_implies_PreTrigger_some {rule: LinearRule sig} {fact: Fact sig}:
    (ruleApply rule fact).isSome -> (PreTrigger.from_rule_and_fact rule fact).isSome := by
    rw[ruleApply_eq]
    simp

  theorem ruleApply_fst_term_lenght_eq_rule_head_length {rule:LinearRule sig} {fact: Fact sig} {ruleApply_some: (ruleApply rule fact).isSome}:
    ((ruleApply rule fact).get ruleApply_some).fst.terms.length = rule.head.fst.terms.length := by
      have trg_some : (PreTrigger.from_rule_and_fact rule fact).isSome := by apply ruleApply.some_implies_PreTrigger_some; exact ruleApply_some
      rw[Option.isSome_iff_exists] at trg_some
      rcases trg_some with ⟨trg, trg_some⟩
      simp only [ruleApply_eq, trg_some, Option.map_some, Option.get_some]
      simp only [PreTrigger.apply_to_function_free_atom]
      simp only [TermMapping.apply_generalized_atom, List.length_map]

  theorem ruleApply_snd_term_lenght_eq_rule_head_length {rule:LinearRule sig} {fact: Fact sig} {ruleApply_some: (ruleApply rule fact).isSome}:
    ((ruleApply rule fact).get ruleApply_some).snd.terms.length = rule.head.snd.terms.length := by
      have trg_some : (PreTrigger.from_rule_and_fact rule fact).isSome := by apply ruleApply.some_implies_PreTrigger_some; exact ruleApply_some
      rw[Option.isSome_iff_exists] at trg_some
      rcases trg_some with ⟨trg, trg_some⟩
      simp only [ruleApply_eq, trg_some, Option.map_some, Option.get_some]
      simp only [PreTrigger.apply_to_function_free_atom]
      simp only [TermMapping.apply_generalized_atom, List.length_map]

  theorem ruleApply_frontierPos_fstHead {rule : LinearRule sig} {fact : Fact sig} {i : Nat} (i_valid: i < rule.head.fst.terms.length) (h_frontier : is_frontier_position_fst rule i i_valid):
     (ruleApplySome: (ruleApply rule fact).isSome) ->
    ∃ j: Nat, ∃ (j_valid: j < fact.terms.length), ((ruleApply rule fact).get ruleApplySome).fst.terms[i]'(by
      rw[ruleApply_fst_term_lenght_eq_rule_head_length]; exact i_valid) = fact.terms[j]:= by
    intro ruleApplyIsSome
    rcases (frontier_pos_fst_iff_in_body).mp h_frontier with ⟨j, j_valid, h_frontier'⟩

    have trg_some : (PreTrigger.from_rule_and_fact rule fact).isSome := by apply ruleApply.some_implies_PreTrigger_some; exact ruleApplyIsSome
    rw[Option.isSome_iff_exists] at trg_some
    rcases trg_some with ⟨trg, trg_some⟩
    have trg_some' := trg_some
    unfold PreTrigger.from_rule_and_fact at trg_some
    simp[Option.map_eq_some_iff] at trg_some
    rcases trg_some with ⟨sub, sub_def, trg_eq⟩
    have sub_apply: sub.apply_function_free_atom rule.body = fact := by
      rw[GroundSubstitution.apply_function_free_atom_from_atom_and_fact]
      exact sub_def

    exists j, (by rw[← (GroundSubstitution.i_lt_atom_terms_len_iff_fact_terms_len sub sub_def j)]; exact j_valid)
    conv => right; simp only [← sub_apply, GroundSubstitution.apply_function_free_atom]; simp only[TermMapping.apply_generalized_atom, List.getElem_map]
    rw [← h_frontier'.right]

    simp only [ruleApply_eq, trg_some', Option.map_some, Option.get_some]
    simp only [PreTrigger.apply_to_function_free_atom, TermMapping.apply_generalized_atom, List.getElem_map]
    rcases h_frontier with ⟨v, v_eq, v_front⟩
    rw [v_eq]
    rw [PreTrigger.apply_to_var_or_const_frontier_var _ _ _ (by rw [← trg_eq]; exact v_front)]
    rw [← trg_eq]
    rfl

  theorem ruleApply_frontierPos_sndHead {rule : LinearRule sig} {fact : Fact sig} {i : Nat} (i_valid: i < rule.head.snd.terms.length) (h_frontier : is_frontier_position_snd rule i i_valid):
     (ruleApplySome: (ruleApply rule fact).isSome) ->
    ∃ j: Nat, ∃ (j_valid: j < fact.terms.length), ((ruleApply rule fact).get ruleApplySome).snd.terms[i]'(by
      have trg_some : (PreTrigger.from_rule_and_fact rule fact).isSome := by apply ruleApply.some_implies_PreTrigger_some; exact ruleApplySome
      rw[Option.isSome_iff_exists] at trg_some
      rcases trg_some with ⟨trg, trg_some⟩
      simp only [ruleApply_eq, trg_some, Option.map_some, Option.get_some]
      simp only [PreTrigger.apply_to_function_free_atom]
      simp only [TermMapping.apply_generalized_atom, List.length_map]
      exact i_valid
    ) = fact.terms[j]:= by
    intro ruleApplyIsSome
    rcases (frontier_pos_snd_iff_in_body).mp h_frontier with ⟨j, j_valid, h_frontier'⟩

    have trg_some : (PreTrigger.from_rule_and_fact rule fact).isSome := by apply ruleApply.some_implies_PreTrigger_some; exact ruleApplyIsSome
    rw[Option.isSome_iff_exists] at trg_some
    rcases trg_some with ⟨trg, trg_some⟩
    have trg_some' := trg_some
    unfold PreTrigger.from_rule_and_fact at trg_some
    simp[Option.map_eq_some_iff] at trg_some
    rcases trg_some with ⟨sub, sub_def, trg_eq⟩
    have sub_apply: sub.apply_function_free_atom rule.body = fact := by
      rw[GroundSubstitution.apply_function_free_atom_from_atom_and_fact]
      exact sub_def

    exists j, (by rw[← (GroundSubstitution.i_lt_atom_terms_len_iff_fact_terms_len sub sub_def j)]; exact j_valid)
    conv => right; simp only [← sub_apply, GroundSubstitution.apply_function_free_atom]; simp only[TermMapping.apply_generalized_atom, List.getElem_map]
    rw [← h_frontier'.right]

    simp only [ruleApply_eq, trg_some', Option.map_some, Option.get_some]
    simp only [PreTrigger.apply_to_function_free_atom, TermMapping.apply_generalized_atom, List.getElem_map]
    rcases h_frontier with ⟨v, v_eq, v_front⟩
    rw [v_eq]
    rw [PreTrigger.apply_to_var_or_const_frontier_var _ _ _ (by rw [← trg_eq]; exact v_front)]
    rw [← trg_eq]
    rfl

   theorem ruleApply_non_frontier_var_fstHead_is_fun {rule: LinearRule sig} {fact: Fact sig} {i : Nat} (i_valid: i < rule.head.fst.terms.length):
     (ruleApplySome: (ruleApply rule fact).isSome) -> (∃ v, rule.head.fst.terms[i] = VarOrConst.var v ∧  v ∉ rule.rule.frontier) ->
      ∃ a b c, ((ruleApply rule fact).get ruleApplySome).fst.terms[i]'(by rw[ruleApply_fst_term_lenght_eq_rule_head_length]; exact i_valid) = GroundTerm.func a b c := by
    intro ruleApplySome t_isVar
    simp only [ruleApply_eq, Option.get_map]
    unfold PreTrigger.apply_to_function_free_atom
    unfold TermMapping.apply_generalized_atom
    simp only [List.getElem_map]
    rcases t_isVar with ⟨v, v_eq, not_frontier⟩
    rw[v_eq]

    have trg_some : (PreTrigger.from_rule_and_fact rule fact).isSome := by apply ruleApply.some_implies_PreTrigger_some; exact ruleApplySome
    rw[Option.isSome_iff_exists] at trg_some
    rcases trg_some with ⟨trg, trg_some⟩
    simp only [trg_some, Option.get_some]
    unfold PreTrigger.from_rule_and_fact at trg_some
    simp[Option.map_eq_some_iff] at trg_some
    rcases trg_some with ⟨sub, sub_def, trg_eq⟩

    rw[PreTrigger.apply_to_var_or_const_non_frontier_var trg 0 v (by simp only[← trg_eq]; exact not_frontier)]
    unfold PreTrigger.functional_term_for_var
    unfold GroundTerm.func
    simp only [Subtype.mk.injEq, FiniteTree.inner.injEq, exists_and_left, exists_prop,
      exists_eq_left']
    exists (List.map trg.subs trg.rule.frontier)
    simp

   theorem ruleApply_non_frontier_var_sndHead_is_fun {rule: LinearRule sig} {fact: Fact sig} {i : Nat} (i_valid: i < rule.head.snd.terms.length):
     (ruleApplySome: (ruleApply rule fact).isSome) -> (∃ v, rule.head.snd.terms[i] = VarOrConst.var v ∧  v ∉ rule.rule.frontier) ->
      ∃ a b c, ((ruleApply rule fact).get ruleApplySome).snd.terms[i]'(by rw[ruleApply_snd_term_lenght_eq_rule_head_length]; exact i_valid) = GroundTerm.func a b c := by
    intro ruleApplySome t_isVar
    simp only [ruleApply_eq, Option.get_map]
    unfold PreTrigger.apply_to_function_free_atom
    unfold TermMapping.apply_generalized_atom
    simp only [List.getElem_map]
    rcases t_isVar with ⟨v, v_eq, not_frontier⟩
    rw[v_eq]

    have trg_some : (PreTrigger.from_rule_and_fact rule fact).isSome := by apply ruleApply.some_implies_PreTrigger_some; exact ruleApplySome
    rw[Option.isSome_iff_exists] at trg_some
    rcases trg_some with ⟨trg, trg_some⟩
    simp only [trg_some, Option.get_some]
    unfold PreTrigger.from_rule_and_fact at trg_some
    simp[Option.map_eq_some_iff] at trg_some
    rcases trg_some with ⟨sub, sub_def, trg_eq⟩

    rw[PreTrigger.apply_to_var_or_const_non_frontier_var trg 0 v (by simp only[← trg_eq]; exact not_frontier)]
    unfold PreTrigger.functional_term_for_var
    unfold GroundTerm.func
    simp only [Subtype.mk.injEq, FiniteTree.inner.injEq, exists_and_left, exists_prop,
      exists_eq_left']
    exists (List.map trg.subs trg.rule.frontier)
    simp

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
    path : List {sym : AddressSymbol sig // sym ∈ addressSymbols rs} --This List is intended to be filled from right to left (i.e. the last element of the List is the Address symbol that is direct successor of the initial Atom)


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

  def Forest.subforest_of {fs: FactSet sig} (g : Forest fs rs) (f : Forest fs rs) : Prop := g.f ⊆ f.f

  def FactSet.toForest (fs: FactSet sig) : Forest fs rs where
  f:= fun x => x.path = []
  fs_contained := by intro fact fact_mem;  exists {initialAtom := ⟨fact, fact_mem⟩, path := []}
  isPrefixClosed:= by intro fact fact_addr; unfold immed_prefix_address_in_set; rw[fact_addr]


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
      |some lu => (ruleApply r.val.rule lu ).map (fun x => if r.val.headIndex = 0 then x.fst else x.snd)
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

  def materialization_labelling {fs: FactSet sig} (g: Forest fs rs) : FactSet sig :=
    fun a => ∃ b∈ g.f, labellingFunction b = Option.some a

  theorem subforest_of_oblivious_chase_labelling_some {fs: FactSet sig} {g: Forest fs rs} {h: Forest.subforest_of g (oblivious_chase fs rs)}:
    ∀a, a ∈ g.f -> (labellingFunction a).isSome  := by
      intro a a_mem
      unfold Forest.subforest_of at h
      rw[h]
      exact a_mem


end ObvliviousChaseRepresentation


section TriggersAndChaseDerivation

  structure LinearRuleTrigger (fs: FactSet sig) (rs: LinearRuleSet sig) where
  rule : {r: LinearRule sig // r ∈ rs.rules}
  addr : {u: Address fs rs // (labellingFunction u).isSome}
  hom_exists : (GroundSubstitution.from_atom_and_fact (LinearRule.body rule) (Option.get (labellingFunction addr.val) addr.property )).isSome = true

  namespace LinearRuleTrigger

    def apply {fs:FactSet sig} (pi : LinearRuleTrigger fs rs) : (Address fs rs) × (Address fs rs) :=
      -- NOTE: using let instead of have since have only remembers the type but not the actual expression. let remembers the expression.
      let fst: {f : AddressSymbol sig // f ∈ addressSymbols rs}:=
        {val:= {rule:= pi.rule.val,headIndex:=0}, property:= by unfold addressSymbols; exact pi.rule.property;}
      let snd: {f : AddressSymbol sig // f ∈ addressSymbols rs}:=
        {val:= {rule:= pi.rule.val,headIndex:=1}, property:= by unfold addressSymbols; exact pi.rule.property;}
      ({initialAtom:= pi.addr.val.initialAtom, path:=(fst ::pi.addr.val.path)},
      {initialAtom:= pi.addr.val.initialAtom, path:=(snd ::pi.addr.val.path)})

    theorem ruleApply_of_trigger_labelling_is_some {fs: FactSet sig} {pi: LinearRuleTrigger fs rs}:
      (ruleApply pi.rule.val (Option.get (labellingFunction pi.addr.val) pi.addr.property)).isSome := by
        rw[ruleApply_eq]
        unfold PreTrigger.from_rule_and_fact
        simp only [Option.map_map, Option.isSome_map]
        exact pi.hom_exists


    --this gives some shortcut that avoids dealing with the "Option" ...
    def labelling_of_apply {fs: FactSet sig} (pi: LinearRuleTrigger fs rs) : (Fact sig) × (Fact sig) :=
      let lu := Option.get (labellingFunction pi.addr.val) pi.addr.property
      have ruleApply_some: (ruleApply pi.rule.val lu).isSome := by unfold lu; simp[ruleApply_of_trigger_labelling_is_some]
      Option.get (ruleApply pi.rule.val lu) ruleApply_some

    --this shows that the schortcut of 'labelling_of_apply' is actually correct
    theorem labelling_of_apply_eq {fs: FactSet sig} {pi : LinearRuleTrigger fs rs} :
      (labelling_of_apply pi).map Option.some Option.some = (labellingFunction pi.apply.fst,labellingFunction pi.apply.snd) := by
        unfold labellingFunction
        unfold apply
        simp only [↓reduceIte ]
        have l_some: (labellingFunction pi.addr.val).isSome := by exact pi.addr.property;
        cases h: labellingFunction pi.addr.val with
        |none => rw[← Option.not_isSome_iff_eq_none] at h; contradiction
        |some label =>
          simp only
          unfold labelling_of_apply
          simp only[h, Prod.map]
          repeat
            rw[← Option.map_some]
            simp[Option.some_get]

    theorem trg_apply_labelling_fst_predicate_eq {fs: FactSet sig} {pi: LinearRuleTrigger fs rs} :
          pi.rule.val.head.fst.predicate = (labelling_of_apply pi).fst.predicate := by
            unfold labelling_of_apply;
            simp only[ruleApply_eq];
            unfold PreTrigger.apply_to_function_free_atom PreTrigger.apply_to_var_or_const TermMapping.apply_generalized_atom;
            simp;

    theorem trg_apply_labelling_snd_predicate_eq {fs: FactSet sig} {pi: LinearRuleTrigger fs rs} :
          pi.rule.val.head.snd.predicate = (labelling_of_apply pi).snd.predicate := by
            unfold labelling_of_apply;
            simp only[ruleApply_eq];
            unfold PreTrigger.apply_to_function_free_atom PreTrigger.apply_to_var_or_const TermMapping.apply_generalized_atom;
            simp;

    theorem trg_apply_labelling_fst_terms_len {fs: FactSet sig} {pi: LinearRuleTrigger fs rs} :
          pi.rule.val.head.fst.terms.length = (labelling_of_apply pi).fst.terms.length := by
        rw[GeneralizedAtom.arity_ok]
        simp only[trg_apply_labelling_fst_predicate_eq]
        rw[← GeneralizedAtom.arity_ok]

    theorem trg_apply_labelling_snd_terms_len {fs: FactSet sig} {pi: LinearRuleTrigger fs rs} :
          pi.rule.val.head.snd.terms.length = (labelling_of_apply pi).snd.terms.length := by
        rw[GeneralizedAtom.arity_ok]
        simp only[trg_apply_labelling_snd_predicate_eq]
        rw[← GeneralizedAtom.arity_ok]


    def appears_in_forest {fs: FactSet sig} (pi: LinearRuleTrigger fs rs) (g: Forest fs rs): Prop := pi.addr.val ∈ g.f

    -- TODO for Laila: If you want, you can instantiate the Membership typeclass for triggers and forests to be able to write: pi ∈ g and define this to be pi.appears_in_forest g

    def isActive_in_forest {fs: FactSet sig} (pi:LinearRuleTrigger fs rs) (g: Forest fs rs) : Prop :=
      pi.appears_in_forest g ∧ ¬ (pi.apply.fst ∈ g.f ∧ pi.apply.snd ∈ g.f)

    def forest_Address {fs: FactSet sig} (g : Forest fs rs) := {addr : Address fs rs // addr ∈ g.f }

    theorem forest_addr_label_some {fs: FactSet sig} {g: Forest fs rs} {g_sub: g.subforest_of (oblivious_chase fs rs)} {b: forest_Address g}:
      (labellingFunction b.val).isSome := by
        revert b
        unfold forest_Address
        simp only [Subtype.forall]
        apply subforest_of_oblivious_chase_labelling_some
        exact g_sub

    def forest_Trigger {fs: FactSet sig} (g : Forest fs rs) := {trg : LinearRuleTrigger fs rs // trg.appears_in_forest g}

    def blockingTeam {fs: FactSet sig} {g : Forest fs rs} (g_sub : g.subforest_of (oblivious_chase fs rs)) (b1 b2 : forest_Address g) (pi : forest_Trigger g) : Prop :=
      ∃ h: GroundTermMapping sig, h.applyFact (Option.get (labellingFunction pi.val.addr.val) pi.val.addr.property) = Option.get (labellingFunction pi.val.addr.val) pi.val.addr.property
      ∧ h.applyFact (labelling_of_apply pi.val).fst = Option.get (labellingFunction b1.val) (by apply forest_addr_label_some; exact g_sub)
      ∧ h.applyFact (labelling_of_apply pi.val).snd = Option.get (labellingFunction b2.val) (by apply forest_addr_label_some; exact g_sub)
      ∧ h.isIdOnConstants --Frage: ist diese Bedingung hinreichend & notwendig?
      -- Antwort: Ich glaube es genügt in der letzten Zeile zu fordern, dass `h.isIdOnConstants` gilt. Ehrlicherweise scheint diese Bedingung im Paper bei der Homomorphismen Definition zu fehlen.
      -- Alternativ könnte man die Bedingungen so schreiben:
      /- ∃ h: GroundTermMapping sig, h.applyFact (Option.get (labellingFunction pi.val.addr.val) pi.val.addr.property) = Option.get (labellingFunction pi.val.addr.val) pi.val.addr.property -/
      /- ∧ h.isHomomorphism (labelling_of_apply pi.val).fst (Option.get (labellingFunction b1.val) (by apply forest_addr_label_some; exact g_sub)) -/
      /- ∧ h.isHomomorphism (labelling_of_apply pi.val).snd (Option.get (labellingFunction b2.val) (by apply forest_addr_label_some; exact g_sub)) -/
      -- In der ersten Zeile könnte man wahrscheinlich sogar fordern, dass `h` die Identität auf allen Termen aus (Option.get (labellingFunction pi.val.addr.val) pi.val.addr.property) ist. Das klingt erstmal stärker, ist es aber wahrscheinlich nicht.


    structure Conditions {fs: FactSet sig} {g : Forest fs rs} (g_sub: g.subforest_of (oblivious_chase fs rs)) (b1 b2: forest_Address g) (pi: forest_Trigger g) where
      b1_label := Option.get (labellingFunction b1.val) (by apply forest_addr_label_some; exact g_sub)
      b2_label:= Option.get (labellingFunction b2.val) (by apply forest_addr_label_some; exact g_sub)
      b1_label_eq : b1_label = Option.get (labellingFunction b1.val) (by apply forest_addr_label_some; exact g_sub) := by rfl
      b2_label_eq : b2_label = Option.get (labellingFunction b2.val) (by apply forest_addr_label_some; exact g_sub) := by rfl
      --rule := pi.val.rule.val
      first : (b1_label.predicate = (labelling_of_apply pi.val).fst.predicate)
        ∧ (b2_label.predicate = (labelling_of_apply pi.val).snd.predicate)
      second : --note that this slightly differs from the original paper as constant were neglected there
        (∀ j, (lt_fst: j < pi.val.rule.val.head.fst.terms.length) -> (is_frontier_position_fst pi.val.rule.val j lt_fst) ∨ (∃ c, pi.val.rule.val.head.fst.terms[j] = VarOrConst.const c) ->
          (labelling_of_apply pi.val).fst.terms[j]'(by rw[← trg_apply_labelling_fst_terms_len]; exact lt_fst) = b1_label.terms[j]'(by rw[GeneralizedAtom.arity_ok, first.left, ← trg_apply_labelling_fst_predicate_eq, ← GeneralizedAtom.arity_ok]; simp[lt_fst]))
        ∧ (∀ j, (lt_snd: j < pi.val.rule.val.head.snd.terms.length) -> (is_frontier_position_snd pi.val.rule.val j lt_snd) ∨ (∃ c, pi.val.rule.val.head.snd.terms[j] = VarOrConst.const c) ->
          (labelling_of_apply pi.val).snd.terms[j]'(by rw[← trg_apply_labelling_snd_terms_len]; exact lt_snd) = b2_label.terms[j]'(by rw[GeneralizedAtom.arity_ok, first.right, ← trg_apply_labelling_snd_predicate_eq, ← GeneralizedAtom.arity_ok]; simp[lt_snd]))
      third : (∀ i j:Nat, (labelling_of_apply pi.val).fst.terms[i]? = (labelling_of_apply pi.val).fst.terms[j]? -> b1_label.terms[i]? = b1_label.terms[j]?) --funktioniert das mit dem indizieren mit [.]? so?
        ∧ (∀ i j:Nat, (labelling_of_apply pi.val).fst.terms[i]? = (labelling_of_apply pi.val).snd.terms[j]? -> b1_label.terms[i]? = b2_label.terms[j]?)
        ∧ (∀ i j:Nat, (labelling_of_apply pi.val).snd.terms[i]? = (labelling_of_apply pi.val).snd.terms[j]? -> b2_label.terms[i]? = b2_label.terms[j]?)

    theorem b1_label_terms_idxOf_eq {fs: FactSet sig} {g : Forest fs rs} {g_sub: g.subforest_of (oblivious_chase fs rs)} {b1 b2: forest_Address g} {pi: forest_Trigger g} {cond: Conditions g_sub b1 b2 pi}:
        ∀i, (i_lt:  i < pi.val.labelling_of_apply.fst.terms.length) -> cond.b1_label.terms[List.idxOf pi.val.labelling_of_apply.fst.terms[i] pi.val.labelling_of_apply.fst.terms]'
          (by rw[GeneralizedAtom.arity_ok, cond.first.left, ← GeneralizedAtom.arity_ok]; simp[List.idxOf_lt_length_iff])
        = cond.b1_label.terms[i]'(by rw[GeneralizedAtom.arity_ok, cond.first.left, ← GeneralizedAtom.arity_ok]; exact i_lt) := by
      intro i i_lt
      by_cases i_eq: i = List.idxOf pi.val.labelling_of_apply.fst.terms[i] pi.val.labelling_of_apply.fst.terms
      . simp[← i_eq]
      . have mem_l: pi.val.labelling_of_apply.fst.terms[i] ∈ pi.val.labelling_of_apply.fst.terms := by
          simp[List.mem_iff_getElem]
          exists i, i_lt
        have idxLt: List.idxOf pi.val.labelling_of_apply.fst.terms[i] pi.val.labelling_of_apply.fst.terms < pi.val.labelling_of_apply.fst.terms.length:= by
          simp[List.idxOf_lt_length_iff]
        let trd:= cond.third.left
        rw[← Option.some_inj]
        simp[← List.getElem?_eq_getElem]
        apply trd
        rw[List.getElem?_eq_getElem idxLt];
        rw[List.getElem_idxOf_of_mem mem_l]
        simp

    theorem b2_label_terms_idxOf_eq {fs: FactSet sig} {g : Forest fs rs} {g_sub: g.subforest_of (oblivious_chase fs rs)} {b1 b2: forest_Address g} {pi: forest_Trigger g} {cond: Conditions g_sub b1 b2 pi}:
        ∀i, (i_lt:  i < pi.val.labelling_of_apply.snd.terms.length) -> cond.b2_label.terms[List.idxOf pi.val.labelling_of_apply.snd.terms[i] pi.val.labelling_of_apply.snd.terms]'
          (by rw[GeneralizedAtom.arity_ok, cond.first.right, ← GeneralizedAtom.arity_ok]; simp[List.idxOf_lt_length_iff])
        = cond.b2_label.terms[i]'(by rw[GeneralizedAtom.arity_ok, cond.first.right, ← GeneralizedAtom.arity_ok]; exact i_lt) := by
      intro i i_lt
      by_cases i_eq: i = List.idxOf pi.val.labelling_of_apply.snd.terms[i] pi.val.labelling_of_apply.snd.terms
      . simp[← i_eq]
      . have mem_l: pi.val.labelling_of_apply.snd.terms[i] ∈ pi.val.labelling_of_apply.snd.terms := by
          simp[List.mem_iff_getElem]
          exists i, i_lt
        have idxLt: List.idxOf pi.val.labelling_of_apply.snd.terms[i] pi.val.labelling_of_apply.snd.terms < pi.val.labelling_of_apply.snd.terms.length:= by
          simp[List.idxOf_lt_length_iff]
        let trd:= cond.third.right.right
        rw[← Option.some_inj]
        simp[← List.getElem?_eq_getElem]
        apply trd
        rw[List.getElem?_eq_getElem idxLt];
        rw[List.getElem_idxOf_of_mem mem_l]
        simp

    theorem blockingTeam.iff {fs: FactSet sig} {g : Forest fs rs} {g_sub: g.subforest_of (oblivious_chase fs rs)} {b1 b2: forest_Address g} {pi: forest_Trigger g} :
      blockingTeam g_sub b1 b2 pi ↔ ∃ cond : Conditions g_sub b1 b2 pi, True := by
        unfold blockingTeam
        constructor
        -- direction →
        . unfold GroundTermMapping.applyFact TermMapping.apply_generalized_atom--GroundTermMapping.isIdOnConstants
          intro a
          rcases a with ⟨h, a ⟩
          let b1_label := Option.get (labellingFunction b1.val) (by apply forest_addr_label_some; exact g_sub)
          let b2_label:= Option.get (labellingFunction b2.val) (by apply forest_addr_label_some; exact g_sub)
          have fst_cond:  b1_label.predicate = (labelling_of_apply pi.val).fst.predicate ∧ b2_label.predicate = (labelling_of_apply pi.val).snd.predicate := by
            unfold b1_label b2_label
            constructor
            . rw[← a.right.left]
            . rw[ ← a.right.right.left]
          have snd_cond:
           (∀ j, (lt_fst: j < pi.val.rule.val.head.fst.terms.length) -> (is_frontier_position_fst pi.val.rule.val j lt_fst) ∨ (∃ c, pi.val.rule.val.head.fst.terms[j] = VarOrConst.const c) ->
           (labelling_of_apply pi.val).fst.terms[j]'(by rw[← trg_apply_labelling_fst_terms_len]; exact lt_fst)
            = b1_label.terms[j]'(by rw[GeneralizedAtom.arity_ok, fst_cond.left,  ← trg_apply_labelling_fst_predicate_eq, ← GeneralizedAtom.arity_ok]; simp[lt_fst]))
            ∧
            (∀ j, (lt_snd: j < pi.val.rule.val.head.snd.terms.length) -> (is_frontier_position_snd pi.val.rule.val j lt_snd) ∨ (∃ c, pi.val.rule.val.head.snd.terms[j] = VarOrConst.const c) ->
           (labelling_of_apply pi.val).snd.terms[j]'(by rw[← trg_apply_labelling_snd_terms_len]; exact lt_snd)
           = b2_label.terms[j]'(by rw[GeneralizedAtom.arity_ok, fst_cond.right,  ← trg_apply_labelling_snd_predicate_eq, ← GeneralizedAtom.arity_ok]; simp[lt_snd])):= by
           constructor
           .intro j j_valid
            unfold b1_label
            simp only [or_imp, forall_exists_index]
            constructor
            . intro j_frontier_pos
              simp only [← a.right.left, List.getElem_map]
              unfold labelling_of_apply
              rcases ruleApply_frontierPos_fstHead (rule := pi.val.rule.val) (fact := (Option.get (labellingFunction pi.val.addr.val) pi.val.addr.property)) (i := j) j_valid j_frontier_pos (by
                simp[ruleApply_of_trigger_labelling_is_some]) with ⟨k, k_valid, eq⟩
              rw [eq]
              have a_left := a.left
              rw [GeneralizedAtom.mk.injEq] at a_left
              conv => left; arg 1; rw [← a_left.right]
              rw [List.getElem_map]
            . intro c c_eq
              simp only [← a.right.left, List.getElem_map]

              have hc_id : h (GroundTerm.const c) = (GroundTerm.const c) := by
                unfold GroundTerm.const
                let h_const_id:= a.right.right.right
                unfold GroundTermMapping.isIdOnConstants at h_const_id
                rw[h_const_id ⟨FiniteTree.leaf c, GroundTerm.const._proof_1 c⟩ ]

              unfold labelling_of_apply
              simp only [ruleApply_eq, Option.get_map]
              unfold PreTrigger.apply_to_function_free_atom
              unfold TermMapping.apply_generalized_atom
              rw[List.getElem_map]
              rw[c_eq]
              rw[PreTrigger.apply_to_var_or_const_for_const]
              simp[hc_id]
           .intro j j_valid
            unfold b2_label
            simp only [or_imp, forall_exists_index]
            constructor
            . intro j_frontier_pos
              simp only[← a.right.right.left, List.getElem_map]
              unfold labelling_of_apply
              rcases ruleApply_frontierPos_sndHead (rule := pi.val.rule.val) (fact := (Option.get (labellingFunction pi.val.addr.val) pi.val.addr.property)) (i := j) j_valid j_frontier_pos (by
                simp[ruleApply_of_trigger_labelling_is_some]) with ⟨k, k_valid, eq⟩
              rw [eq]
              have a_left := a.left
              rw [GeneralizedAtom.mk.injEq] at a_left
              conv => left; arg 1; rw [← a_left.right]
              rw [List.getElem_map]
            . intro c c_eq
              simp only [← a.right.right.left, List.getElem_map]

              have hc_id : h (GroundTerm.const c) = (GroundTerm.const c) := by
                unfold GroundTerm.const
                let h_const_id:= a.right.right.right
                unfold GroundTermMapping.isIdOnConstants at h_const_id
                rw[h_const_id ⟨FiniteTree.leaf c, GroundTerm.const._proof_1 c⟩ ]

              unfold labelling_of_apply
              simp only [ruleApply_eq, Option.get_map]
              unfold PreTrigger.apply_to_function_free_atom
              unfold TermMapping.apply_generalized_atom
              rw[List.getElem_map]
              rw[c_eq]
              rw[PreTrigger.apply_to_var_or_const_for_const]
              simp[hc_id]

          have trd_cond:
          (∀ i j:Nat, (labelling_of_apply pi.val).fst.terms[i]? = (labelling_of_apply pi.val).fst.terms[j]? -> b1_label.terms[i]? = b1_label.terms[j]?)
          ∧ (∀ i j:Nat, (labelling_of_apply pi.val).fst.terms[i]? = (labelling_of_apply pi.val).snd.terms[j]? -> b1_label.terms[i]? = b2_label.terms[j]?)
          ∧ (∀ i j:Nat, (labelling_of_apply pi.val).snd.terms[i]? = (labelling_of_apply pi.val).snd.terms[j]? -> b2_label.terms[i]? = b2_label.terms[j]?):= by
            unfold b1_label b2_label
            rw[← a.right.left, ← a.right.right.left]
            constructor
            . intro i j hyp
              simp[hyp]
            . constructor
              . intro i j hyp
                simp[hyp]
              . intro i j hyp
                simp[hyp]
          exists {first := fst_cond , second:= snd_cond, third:= trd_cond}
        -- direction ←
        . intro a
          rcases a with ⟨cond, a⟩
          let fst := cond.first
          let snd := cond.second
          let trd := cond.third

          --have b1_label_terms_len: cond.b1_label.terms.length = pi.val.rule.val.head.fst.terms.length := by sorry
          --unfold Conditions.b1_label at fst
          unfold GroundTermMapping.applyFact TermMapping.apply_generalized_atom
          let h: GroundTermMapping sig := fun t =>
            if tInFst: t ∈ (labelling_of_apply pi.val).fst.terms
            then cond.b1_label.terms[(labelling_of_apply pi.val).fst.terms.idxOf t]'(by
              rw[Atom_pred_eq_implies_eq_term_length cond.first.left];
              rw[List.idxOf_lt_length_iff]; exact tInFst)
            else if tInSnd: t ∈ (labelling_of_apply pi.val).snd.terms
              then cond.b2_label.terms[(labelling_of_apply pi.val).snd.terms.idxOf t]'(by
                rw[Atom_pred_eq_implies_eq_term_length cond.first.right];
                rw[List.idxOf_lt_length_iff]; exact tInSnd)
              else t
          exists h
          constructor
          -- show h(⟨u⟩) = ⟨u⟩
          . rw[GeneralizedAtom.mk.injEq]
            simp only[true_and]
            rw[List.map_eq_iff]
            intro i
            unfold Option.map
            by_cases i_len: i <  ((labellingFunction pi.val.addr.val).get pi.val.addr.property).terms.length
            . simp[i_len]
              simp[h]
              by_cases mem_labelling_of_apply_fst: ((labellingFunction pi.val.addr.val).get pi.val.addr.property).terms[i] ∈ pi.val.labelling_of_apply.fst.terms
              -- ⟨u⟩_i occurs in ⟨up1⟩  (in pi.val.labelling_of_apply.fst.terms )
              . simp only[mem_labelling_of_apply_fst]
                simp only[List.mem_iff_getElem] at mem_labelling_of_apply_fst
                rcases mem_labelling_of_apply_fst with ⟨idx, idx_lt, t_eq⟩
                simp only [← t_eq, ↓reduceDIte]
                have idx_lt_rulehead: idx < pi.val.rule.val.head.fst.terms.length := by rw[trg_apply_labelling_fst_terms_len]; exact idx_lt
                by_cases inFrontier: is_frontier_position_fst pi.val.rule.val idx idx_lt_rulehead
                . let idx_of:= List.idxOf pi.val.labelling_of_apply.fst.terms[idx] pi.val.labelling_of_apply.fst.terms
                  have mem_l: pi.val.labelling_of_apply.fst.terms[idx] ∈ pi.val.labelling_of_apply.fst.terms := by
                    simp only[List.mem_iff_getElem]
                    exists idx, idx_lt
                  rw[b1_label_terms_idxOf_eq]
                  simp[snd.left idx idx_lt_rulehead (Or.inl inFrontier)]

                -- term not in frontier -> this may be hard to show, should end up in a contradiction since non-frontier-variables will me mapped to FRESH nulls in the labelling
                . sorry
              --term not in labelling_of_apply.fst.terms
              . simp only [mem_labelling_of_apply_fst, ↓reduceDIte, right_eq_dite_iff]
                intro mem_labelling_of_apply_snd
                simp only[List.mem_iff_getElem] at mem_labelling_of_apply_snd
                rcases mem_labelling_of_apply_snd with ⟨idx, idx_lt, t_eq⟩
                simp only [← t_eq]
                have idx_lt_rulehead: idx < pi.val.rule.val.head.snd.terms.length := by rw[trg_apply_labelling_snd_terms_len]; exact idx_lt
                by_cases inFrontier: is_frontier_position_snd pi.val.rule.val idx idx_lt_rulehead
                . let idx_of:= List.idxOf pi.val.labelling_of_apply.snd.terms[idx] pi.val.labelling_of_apply.snd.terms
                  have mem_l: pi.val.labelling_of_apply.snd.terms[idx] ∈ pi.val.labelling_of_apply.snd.terms := by
                    simp only[List.mem_iff_getElem]
                    exists idx, idx_lt
                  rw[b2_label_terms_idxOf_eq]
                  simp[snd.right idx idx_lt_rulehead (Or.inl inFrontier)]

                -- term not in frontier -> this may be hard to show
                . sorry

            . simp [i_len]
          . constructor
            --shows h(⟨up_1⟩) = ⟨v_1⟩  i.e. h (pi.val.labelling_of_apply.fst) = (labellingFunction b1.val).get ...
            . rw[GeneralizedAtom.mk.injEq]
              rw[← fst.left]
              simp only [cond.b1_label_eq, true_and]
              rw[List.map_eq_iff]
              intro i
              unfold Option.map
              by_cases i_len: i <  pi.val.labelling_of_apply.fst.terms.length
              . simp[i_len] --, List.getElem?_eq_some_iff];
                have i_lt : i < ((labellingFunction b1.val).get (by apply forest_addr_label_some; exact g_sub)).terms.length := by
                  rw[← cond.b1_label_eq]
                  rw[Atom_pred_eq_implies_eq_term_length fst.left]
                  exact i_len
                simp only [List.getElem_mem, ↓reduceDIte, h, List.getElem?_eq_some_iff]
                exists i_lt
                rw[b1_label_terms_idxOf_eq]
                simp only[cond.b1_label_eq]
              . simp only [i_len, not_false_eq_true, getElem?_neg, getElem?_eq_none_iff, Nat.not_lt]
                rw[← cond.b1_label_eq]
                rw[Atom_pred_eq_implies_eq_term_length fst.left]
                rw[← Nat.not_lt]
                exact i_len
            . constructor
              --shows h(⟨up_2⟩) = ⟨v_2⟩  i.e. h (pi.val.labelling_of_apply.snd) = (labellingFunction b2.val).get ...
              . rw[GeneralizedAtom.mk.injEq]
                rw[← fst.right]
                simp only [cond.b2_label_eq, true_and]
                rw[List.map_eq_iff]
                intro i
                unfold Option.map
                by_cases i_len: i <  pi.val.labelling_of_apply.snd.terms.length
                . simp only [i_len, getElem?_pos]
                  have i_lt : i < ((labellingFunction b2.val).get (by apply forest_addr_label_some; exact g_sub)).terms.length := by
                    rw[← cond.b2_label_eq]
                    rw[Atom_pred_eq_implies_eq_term_length fst.right]
                    exact i_len
                  simp only [List.getElem_mem, ↓reduceDIte, h, List.getElem?_eq_some_iff]
                  exists i_lt
                  by_cases term_mem_labelling_of_apply_fst: pi.val.labelling_of_apply.snd.terms[i] ∈ pi.val.labelling_of_apply.fst.terms
                  . simp only [term_mem_labelling_of_apply_fst, ↓reduceDIte]
                    have idxLt: List.idxOf pi.val.labelling_of_apply.snd.terms[i] pi.val.labelling_of_apply.fst.terms < pi.val.labelling_of_apply.fst.terms.length:= by
                        simp[List.idxOf_lt_length_iff]
                        exact term_mem_labelling_of_apply_fst
                    let trd:= cond.third.right.left
                    rw[← Option.some_inj]
                    simp only[← List.getElem?_eq_getElem]
                    rw[← cond.b2_label_eq, eq_comm]
                    apply trd
                    rw[List.getElem?_eq_getElem idxLt]
                    rw[List.getElem_idxOf_of_mem term_mem_labelling_of_apply_fst]
                    simp
                  . simp only[term_mem_labelling_of_apply_fst]
                    rw[b2_label_terms_idxOf_eq]
                    simp[cond.b2_label_eq]
                . simp only [i_len, not_false_eq_true, getElem?_neg, getElem?_eq_none_iff]
                  rw[← cond.b2_label_eq]
                  rw[Atom_pred_eq_implies_eq_term_length fst.right]
                  exact i_len

              -- shows h.isIdOnConstants
              . unfold GroundTermMapping.isIdOnConstants
                intro t
                by_cases e_def: ∃ c, t = GroundTerm.const c
                . rcases e_def with ⟨c, c_def⟩
                  unfold GroundTerm.const at c_def
                  simp only[c_def]
                  rw[← c_def]
                  unfold h
                  by_cases mem_apply_label: t ∈ pi.val.labelling_of_apply.fst.terms
                  -- t occurs in pi.val.labelling_of_apply
                  -- Baisically t can either be in a frontier position, then h(t) = t by the snd.condition,
                  -- or t is not frontier, then
                  -- either c was a Constant already in the rule or it was an ex. Vatiable and therefore will be mapped to a null, not a constant which gives a contradiction
                  . simp[mem_apply_label]
                    have listIdx_lt_rule_head: List.idxOf t pi.val.labelling_of_apply.fst.terms < pi.val.rule.val.head.fst.terms.length := by
                      rw[trg_apply_labelling_fst_terms_len]
                      simp only[List.idxOf_lt_length_iff]
                      exact mem_apply_label

                    simp[List.mem_iff_getElem] at mem_apply_label
                    rcases mem_apply_label with ⟨i, i_lt, t_eq⟩

                    by_cases inFrontier: is_frontier_position_fst pi.val.rule.val (List.idxOf t pi.val.labelling_of_apply.fst.terms) listIdx_lt_rule_head
                     -- term is in frontier
                    . rw[← snd.left (List.idxOf t pi.val.labelling_of_apply.fst.terms) listIdx_lt_rule_head (Or.inl inFrontier)]
                      rw[List.getElem_idxOf_of_mem mem_apply_label]

                      -- term not in frontier
                    . cases const_var: pi.val.rule.val.head.fst.terms[(List.idxOf t pi.val.labelling_of_apply.fst.terms)] with
                      |const c =>
                        rw[← snd.left (List.idxOf t pi.val.labelling_of_apply.fst.terms) listIdx_lt_rule_head (Or.inr (Exists.intro c const_var))]
                        rw[List.getElem_idxOf_of_mem mem_apply_label]
                      |var v =>
                        -- term is non-frontier-variable; should lead to contradiction
                        simp only[cond.b1_label_eq]

                        have list_elem_eq: pi.val.labelling_of_apply.fst.terms[i] =
                          pi.val.labelling_of_apply.fst.terms[List.idxOf pi.val.labelling_of_apply.fst.terms[i] pi.val.labelling_of_apply.fst.terms]'(by simp only[← t_eq] at listIdx_lt_rule_head; rw[← trg_apply_labelling_fst_terms_len]; exact listIdx_lt_rule_head) := by
                           simp[List.getElem_idxOf_of_mem]

                        unfold is_frontier_position_fst at inFrontier
                        rw[not_exists] at inFrontier
                        simp[const_var] at inFrontier

                        simp  only[← t_eq]
                        simp only[← t_eq] at const_var

                        rcases ruleApply_non_frontier_var_fstHead_is_fun (rule := pi.val.rule.val) (fact := (Option.get (labellingFunction pi.val.addr.val) pi.val.addr.property))
                          (i := List.idxOf pi.val.labelling_of_apply.fst.terms[i] pi.val.labelling_of_apply.fst.terms)
                          (by rw[← t_eq] at listIdx_lt_rule_head; exact listIdx_lt_rule_head) (by simp[ruleApply_of_trigger_labelling_is_some]) (Exists.intro v (And.intro const_var inFrontier))
                          with ⟨x, y, z, rA_eq_func⟩

                        rw[list_elem_eq] at t_eq
                        conv at t_eq => left; arg 1; unfold labelling_of_apply

                        rw[rA_eq_func] at t_eq
                        simp[c_def] at t_eq
                        unfold GroundTerm.func at t_eq
                        simp at t_eq

                  . simp[mem_apply_label]
                    intro t_in_snd_label
                    have listIdx_lt_rule_head: List.idxOf t pi.val.labelling_of_apply.snd.terms < pi.val.rule.val.head.snd.terms.length := by
                      rw[trg_apply_labelling_snd_terms_len]
                      simp only[List.idxOf_lt_length_iff]
                      exact t_in_snd_label

                    simp[List.mem_iff_getElem] at t_in_snd_label
                    rcases t_in_snd_label with ⟨i, i_lt, t_eq⟩

                    by_cases inFrontier: is_frontier_position_snd pi.val.rule.val (List.idxOf t pi.val.labelling_of_apply.snd.terms) listIdx_lt_rule_head
                     -- term is in frontier
                    . rw[← snd.right (List.idxOf t pi.val.labelling_of_apply.snd.terms) listIdx_lt_rule_head (Or.inl inFrontier)]
                      rw[List.getElem_idxOf_of_mem t_in_snd_label]

                      -- term not in frontier
                    . cases const_var: pi.val.rule.val.head.snd.terms[(List.idxOf t pi.val.labelling_of_apply.snd.terms)] with
                      |const c =>
                        rw[← snd.right (List.idxOf t pi.val.labelling_of_apply.snd.terms) listIdx_lt_rule_head (Or.inr (Exists.intro c const_var))]
                        rw[List.getElem_idxOf_of_mem t_in_snd_label]
                      |var v =>
                        -- term is non-frontier-variable; should lead to contradiction
                        simp only[cond.b2_label_eq]

                        have list_elem_eq: pi.val.labelling_of_apply.snd.terms[i] =
                          pi.val.labelling_of_apply.snd.terms[List.idxOf pi.val.labelling_of_apply.snd.terms[i] pi.val.labelling_of_apply.snd.terms]'(by simp only[← t_eq] at listIdx_lt_rule_head; rw[← trg_apply_labelling_snd_terms_len]; exact listIdx_lt_rule_head) := by
                           simp[List.getElem_idxOf_of_mem]

                        unfold is_frontier_position_snd at inFrontier
                        rw[not_exists] at inFrontier
                        simp[const_var] at inFrontier

                        simp  only[← t_eq]
                        simp only[← t_eq] at const_var

                        rcases ruleApply_non_frontier_var_sndHead_is_fun (rule := pi.val.rule.val) (fact := (Option.get (labellingFunction pi.val.addr.val) pi.val.addr.property))
                          (i := List.idxOf pi.val.labelling_of_apply.snd.terms[i] pi.val.labelling_of_apply.snd.terms)
                          (by rw[← t_eq] at listIdx_lt_rule_head; exact listIdx_lt_rule_head) (by simp[ruleApply_of_trigger_labelling_is_some]) (Exists.intro v (And.intro const_var inFrontier))
                          with ⟨x, y, z, rA_eq_func⟩

                        rw[list_elem_eq] at t_eq
                        conv at t_eq => left; arg 1; unfold labelling_of_apply

                        rw[rA_eq_func] at t_eq
                        simp[c_def] at t_eq
                        unfold GroundTerm.func at t_eq
                        simp at t_eq

                . unfold GroundTerm.const at e_def
                  simp[not_exists] at e_def
                  simp




    def active_trigger_apply_resulting_forest {fs: FactSet sig} (pi: LinearRuleTrigger fs rs) (g: Forest fs rs) (pi_active: pi.isActive_in_forest g) : Forest fs rs where
    --returns the resulting forest if one adds the result of pi.apply to forest g if pi is a Trigger that is active in g
      f:= fun x => x∈ g.f ∨  x= pi.apply.fst ∨  x= pi.apply.snd
      fs_contained := by
        intro fact fact_mem;
        obtain ⟨a, a_mem, c⟩ := g.fs_contained fact fact_mem
        exists a
        simp only [c, and_self, and_true]
        apply Or.inl;
        simp[a_mem]
      isPrefixClosed := by
        --simp only [Membership.mem]
        intro addr addr_mem
        unfold immed_prefix_address_in_set
        apply Or.elim addr_mem
        . intro addr_mem_g
          have addr_prefix_in_g := g.isPrefixClosed addr addr_mem_g
          unfold immed_prefix_address_in_set at addr_prefix_in_g
          revert addr_prefix_in_g
          cases add_p: addr.path with
          |nil => simp
          |cons _ ls =>
            exact Or.inl
        . cases add_p: addr.path with
          |nil => simp
          |cons _ ls =>
            intro addr_eq
            apply Or.inl
            unfold isActive_in_forest appears_in_forest at pi_active
            apply Or.elim addr_eq
            . intro addr_eq
              revert add_p
              rw[addr_eq]
              unfold apply
              simp only [List.cons.injEq, and_imp]
              intro a b
              rw[← b]
              apply pi_active.left
            . intro addr_eq
              revert add_p
              rw[addr_eq]
              unfold apply
              simp only [List.cons.injEq, and_imp]
              intro a b
              rw[← b]
              apply pi_active.left

    theorem forest_subforest_trigger_apply_result {fs: FactSet sig} {g: Forest fs rs} {pi: LinearRuleTrigger fs rs} {pi_active: pi.isActive_in_forest g}:
    g.subforest_of (active_trigger_apply_resulting_forest pi g pi_active) := by
      unfold Forest.subforest_of
      unfold active_trigger_apply_resulting_forest
      simp only[Subset, Membership.mem]
      intro e e_in_g
      apply Or.intro_left
      exact e_in_g


  end LinearRuleTrigger

    -- Lukas: List ist induktiv definiert und damit immer endlich(!) Das ist nicht offensichtlich, aber wichtig zu wissen.
    -- Du willst hier wahrscheinlich `PossiblyInfiniteList` benutzen. Das kommt aus einem Repo von mir und orientiert sich an mathlib's `Stream'`. (Du kannst bei `ChaseBranch` abgucken.)
    -- Außerdem ist es wahrscheinlich möglicherweise nützlich nur die Trigger Sequenz in der Struktur zu halten und die Sequenz aus Forests nur daraus abzuleiten.
    -- Da wird man aber eine Prästruktur brauchen, wo man erstmal nur die Trigger Sequenz hat, dann da alle möglichen Bedingungen definiert und dann ist die tatsächliche ChaseDerivation eine Struktur bestehend aus der Prästruktur und eben den Bedingungen. (Wahrscheinlich beschränkt sich das im ersten Moment darauf, dass jeder Trigger aktiv sein muss.)
    -- Bei der ChaseBranch werden Faktenmengen und Trigger gemeinsam in den Elementen der Sequenz gehalten. Falls du denkst, dass das hilfreich ist, wäre das auch hier eine Option. (Nur, dass es hier Trigger und Forests sind.) Ich bin mir nicht mehr sicher, ob ich einen guten Grund hatte das bei der `ChaseBranch` so zu machen oder ob das einfach das erste war, was mir eingefallen ist :D
    -- Nur die Trigger zu speichern und Fakten/Forests daraus abzuleiten, kommt mir etwas sauberer vor und wenn ich mal Zeit habe, passe ich vielleicht auch die `ChaseBranch` dahingehend an :)
    abbrev PreChaseDerivation (fs: FactSet sig) (rs: LinearRuleSet sig) := PossiblyInfiniteList (LinearRuleTrigger fs rs)

    namespace PreChaseDerivation

    structure trg_application_cond {fs: FactSet sig} (trg: LinearRuleTrigger fs rs) (before : Forest fs rs) (after : Option (Forest fs rs)) where
      active : trg.isActive_in_forest before
      result : after = some (LinearRuleTrigger.active_trigger_apply_resulting_forest trg before active)

    def Forest_seq_valid {fs: FactSet sig} (trg_seq : PreChaseDerivation fs rs) (forest_seq : PossiblyInfiniteList (Forest fs rs)):=
      forest_seq.infinite_list 0 = some fs.toForest ∧
      ∀ n : Nat, (trg_seq.infinite_list n).is_none_or (fun trg =>
        (forest_seq.infinite_list n).is_some_and (fun before =>
          let after := forest_seq.infinite_list (n+1)
          trg_application_cond trg before after))

    def Forest_seq_valid_implies_unique {fs: FactSet sig}{trg_seq: PreChaseDerivation fs rs}:
      --Was, wenn die trg_sequenz (mehr als 1 element) kürzer ist, als die forest-sequenz?
      --Dann könnte die forest seqeunz ab dort beliebig sein.
      --Will man das zulassen, oder verhindern?
      ∀ forest_seq_1 forest_seq_2, Forest_seq_valid trg_seq forest_seq_1 ∧ Forest_seq_valid trg_seq forest_seq_2
      -> forest_seq_1 = forest_seq_2 := by
      intro forest_seq_1 forest_seq_2

      unfold Forest_seq_valid
      simp[and_imp]
      intro valid_1_start valid_1_rest valid_2_start valid_2_rest
      --unfold Forest_seq_valid
      rw[PossiblyInfiniteList.eq_iff_same_on_all_indices]
      intro n
      --revert valid_1_rest
      induction n with
      |zero =>
        --unfold Forest_seq_valid at valid_1 valid_2
        simp[valid_1_start, valid_2_start]
      |succ n ih =>
        revert valid_1_rest
        simp[Option.is]
        rw[ih] at valid_1_rest
        sorry

    end PreChaseDerivation

    structure chaseDerivation(fs: FactSet sig) (rs: LinearRuleSet sig) where
      trigger_seq : PreChaseDerivation fs rs
      cond : ∃ forest_seq , PreChaseDerivation.Forest_seq_valid trigger_seq forest_seq

    theorem chase_subset_of_obliviousChase {fs: FactSet sig} {chasederiv: chaseDerivation fs rs}:
      ∀ forests_seq, PreChaseDerivation.Forest_seq_valid chasederiv.trigger_seq forests_seq ->
      ∀ n, (forests_seq.infinite_list n).is_none_or (fun f => f.subforest_of (oblivious_chase fs rs)) := by sorry


end TriggersAndChaseDerivation
