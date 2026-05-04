import ExistentialRules.ChaseSequence.Termination.Basic


section AtomPositions
/-
The following definitions around Atom Positions aren't used in the rest of this file yet
but could hopefully make some definitions and proofs for linear chase termination a bit easier.
-/

/--An `AtomPos` consists of a `GeneralizedAtom` and a Number i that refers to the term at Position i in that Atom-/
structure AtomPos (sig : Signature) (T : Type u) [DecidableEq sig.P] where
  a: GeneralizedAtom sig T
  i: Fin a.terms.length

namespace AtomPos

  variable {sig : Signature} {T: Type u} [DecidableEq sig.P]

  /--Returns the term at the position referred by `AtomPos`-/
  def term (pos: AtomPos sig T) : T := pos.a.terms[pos.i]

  /--i is a valid index for a `GeneralizedAtom` a if it refers to an actual term of the atom a-/
  def idx_valid (a: GeneralizedAtom sig T)(i: Nat) : Bool :=
    if i < a.terms.length then true else false

  /--We apply a `TermMapping` to an `AtomPos` by applying the Mapping to the Atom and keeping the same positional Number-/
  def mapping (h: TermMapping T S)(pos: AtomPos sig T) :  AtomPos sig S where
    a:= TermMapping.apply_generalized_atom h pos.a
    i:= Fin.cast (by rw[TermMapping.length_terms_apply_generalized_atom]) pos.i

  /--It doesn't matter if we first get the term from a `AtomPos` and then apply a `TermMapping` or if we first apply the mapping on the `AtomPos` and the retrieve the Term-/
  theorem term_map_eq (pos: AtomPos sig T) (h: TermMapping T S): h pos.term = term (mapping h pos) := by
    unfold term mapping TermMapping.apply_generalized_atom
    simp

  /--We get the same result if we first apply a `TermMapping` to an atom and then build an `AtomPos` from the result or vice versa-/
  theorem termMapping_AtomPos_eq (h: TermMapping T S) (a : GeneralizedAtom sig T) (i : Fin a.terms.length) :
      {a:= TermMapping.apply_generalized_atom h a, i:= Fin.cast (by rw[TermMapping.length_terms_apply_generalized_atom]) i} = mapping h {a:=a, i:= i} := by
    unfold mapping TermMapping.apply_generalized_atom
    simp

end AtomPos

end AtomPositions


instance {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [Inhabited sig.C] : Inhabited (PreGroundTerm sig) where
  default := .leaf default

instance {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [Inhabited sig.C] : Inhabited (GroundTerm sig) where
  default := ⟨default, by unfold PreGroundTerm.arity_ok; rfl⟩

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] [Inhabited sig.C]
--some of those variables are not needed for all definitions. Therefore it might be advisable to think about including them more fine-grained in the specific sections. However this would need some careful code restructuring
--most of the later definitions and theorem include  `FactSet sig` and  `RuleSet sig` as parameters. Maybe one could think about declaring them as section variables too.

section Rules
  /-!
  ## Linear Existential Rule

  A linear rule is an existential Rule that has only a single atom in the body.
  Here we additionally restrict the rule heads to be a conjunction of exactly two head atoms
  (usually linear rule heads admit conjunctions of an arbitrary numberof atoms).
  -/

  /-- A Rule is linear if it's body consists of exactli one atom-/
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
    /-- This function returns the body of a linear rule-/
    def body (rule : LinearRule sig) : FunctionFreeAtom sig := rule.rule.body[0]'(by have linear := rule.linear; simp only [Rule.isLinear] at linear; simp [linear])

    /--This function returns the head of a linear rule as a Pair of the two head-atoms-/
    def head (rule : LinearRule sig) : FunctionFreeAtom sig × FunctionFreeAtom sig :=
      let conj := rule.rule.head[0]'(by have det := rule.deterministic; simp only [Rule.isDeterministic, decide_eq_true_iff] at det; simp [det])
      have length_conj : conj.length = 2 := by have twohead := rule.exactlyTwoHeadAtoms; simp only [Rule.exactlyTwoHeadAtoms] at twohead; simp[conj,twohead];
      (conj[0], conj[1])

  end LinearRule

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

    /--An integer i is frontier position in the body of a rule, if the term at the i'th position in the body atom is a frontier variable -/
    def is_frontier_position_body (rule: LinearRule sig) (i:Nat) (i_valid: i < rule.body.terms.length) : Prop :=
      ∃ v, rule.body.terms[i] = VarOrConst.var v ∧ v ∈ rule.rule.frontier

    /--If i is a frontier position in the body of a rule r, then the term at this position occurs in the head of the rule-/
    theorem frontier_occus_in_head {rule: LinearRule sig}:
        ∀ i, (i_valid : i < rule.body.terms.length) -> is_frontier_position_body rule i i_valid ->
        rule.body.terms[i] ∈ rule.head.fst.terms ∨ rule.body.terms[i] ∈ rule.head.snd.terms := by
      intro idxB idxB_valid idxB_frontierPos
      unfold is_frontier_position_body at idxB_frontierPos
      rcases idxB_frontierPos with ⟨v, v_eq, v_frontier⟩
      unfold Rule.frontier at v_frontier
      rw[LinearRule.head_eq] at v_frontier
      simp only [List.any_cons, List.any_nil, Bool.or_false, List.mem_filter,
        decide_eq_true_eq] at v_frontier
      let v_mem := v_frontier.right
      unfold FunctionFreeConjunction.vars at v_mem
      rw [List.mem_flatMap] at v_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
        exists_eq_left] at v_mem
      unfold FunctionFreeAtom.variables at v_mem
      cases v_mem with
      | inl hl =>
        apply Or.inl
        rw[v_eq]
        apply VarOrConst.filterVars_occur_in_original_list
        exact hl
      | inr hr =>
        apply Or.inr
        rw[v_eq]
        apply VarOrConst.filterVars_occur_in_original_list
        exact hr

    /--if v is a frontier variable of rule r, then v occurs in the body of r-/
    theorem frontier_occurs_in_body (r : Rule sig) : ∀ v, v ∈ r.frontier -> ∃ f, f ∈ r.body ∧ (VarOrConst.var v) ∈ f.terms := by
      unfold Rule.frontier
      cases r.body with
      | nil => intros; contradiction
      | cons head tail =>
        intro v vInFrontier
        rw [List.mem_filter] at vInFrontier
        have mem_body := vInFrontier.left
        unfold FunctionFreeConjunction.vars at mem_body
        rw [List.mem_flatMap] at mem_body
        rcases mem_body with ⟨a, a_mem, v_mem⟩
        exists a
        constructor
        . exact a_mem
        . unfold FunctionFreeAtom.variables at v_mem
          apply VarOrConst.filterVars_occur_in_original_list
          exact v_mem

    /--i is frontier position in the first head atom of a rule, if the term at the i'th position in that atom is a frontier variable-/
    def is_frontier_position_fst (rule: LinearRule sig)  (i: Nat) (i_valid: i < rule.head.fst.terms.length) : Prop :=
      ∃ v, rule.head.fst.terms[i] = VarOrConst.var v ∧ v ∈ rule.rule.frontier

    /--i is frontier position in the first head atom of a rule iff the term at this position is a variable and also occurs in the rulebody-/
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
        . rcases frontier_occurs_in_body rule.rule v h.right with ⟨a, a_body, v_a⟩
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

    /--i is frontier position in the second head atom of a rule, if the term at the i'th position in that atom is a frontier variable-/
    def is_frontier_position_snd (rule: LinearRule sig)  (i: Nat) (i_valid: i < rule.head.snd.terms.length) : Prop :=
      ∃ v, (rule.head.snd.terms[i]'(by exact i_valid)) = VarOrConst.var v ∧ v ∈ rule.rule.frontier

    /--i is frontier position in the second head atom of a rule iff the term at this position is a variable and also occurs in the rulebody-/
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
        . rcases frontier_occurs_in_body rule.rule v h.right with ⟨a, a_body, v_a⟩
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

  /--This function modifies the Substitution s such that v ↦ c and otherwise s is the same as before-/
  def extend_Substitutution  (s: GroundSubstitution sig) (v: sig.V) (c: GroundTerm sig) : GroundSubstitution sig := fun x => if x = v then c else s x

  /--This function modifies the Substitution s such that t ↦ gt and returns the modified substitution if possible. Otherwise it returns Option.none
  The parameter 'vars' serves as a list of variables for which the substition is already 'properly' defined and cannot be changed anymore -/
  def matchVarorConst (s: GroundSubstitution sig) (t : VarOrConst sig) (gt : GroundTerm sig)(vars : List (sig.V)) : Option (GroundSubstitution sig) :=
    match t with
      | .const c => if gt = GroundTerm.const c then Option.some s else Option.none
      | .var v =>
          if v ∈ vars -- vars: List of variables, for which the substitutiion s is already 'properly' defined (has not just the dummy value anymore)
          then if gt = s v then Option.some s else Option.none --triit auf, wenn es für v schon eine andere substitution gab
          else some (extend_Substitutution s v gt)

  /--if 'matchVarOrConst s t gt' returns an actual substitution (Option.some subs) then subs applied on t will return gt-/
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

  /--If a variable v occurs in vars, then the resulting substitution from any call of matchVarorConst (with vars) will behave on v exactly as the substituion before the call -/
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

  /--If possible, this function returns substitution subs s.t. subs the List of VarOrConst to the List of GroundTerms (elementwise).
  Variables in 'vars' need to be mapped exactly as in Substitution s.
  If such a substitution is not possible, the function returns  Option.none-/
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

  /--Variables that occur in vars are (in the resulting substitution from `matchTermList`) mapped exactly as in Substitution s-/
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

  /--The resulting substitution s from `matchTermList` (if there is one) will map for each pair of l the first element(VarOrConst) to the second one (GroundTerm) when s is applied to l -/
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

  /--If there exists a substitution than maps the first element to the second in each pair of l, then `matchTermList` will find such a substitution-/
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

  /--A ground substitution is a homomorphism from an atom to a fact. This function returns such a GroundSubstitution if there exists one. (Otherwise returns Option.none) -/
  def GroundSubstitution.from_atom_and_fact (atom : FunctionFreeAtom sig) (fact : Fact sig) : Option (GroundSubstitution sig) :=
    if atom.predicate = fact.predicate
    then matchTermList (fun _ => default) List.nil (List.zip atom.terms fact.terms)  -- calls matchTermList with a dummy substiution and the Notion, that no variables have a meaningful substitution yet (Empty List)
    else Option.none

  /--If `GroundSubstitution.from_atom_and_fact` finds a Substitution s, then s applied on the atom retruns exactly the fact-/
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

  /--If a substitution is returned by `GroundSubstitution.from_atom_and_fact`,then the atom and fact have the same number of terms.-/
  theorem GroundSubstitution.atom_terms_len_eq_fact_terms_len {atom: FunctionFreeAtom sig} {fact : Fact sig} :
    ∀ subs ∈ GroundSubstitution.from_atom_and_fact atom fact, atom.terms.length = fact.terms.length := by
      intro subs subs_mem
      have subs_appy: subs.apply_function_free_atom atom = fact := by rw[GroundSubstitution.apply_function_free_atom_from_atom_and_fact]; exact subs_mem
      rw[← subs_appy]
      simp only [GroundSubstitution.apply_function_free_atom, TermMapping.length_terms_apply_generalized_atom]

  /--If a substitution is returned by `GroundSubstitution.from_atom_and_fact`,then every number i is less than than the length of the term list of the atomm iff it is also less than the term list lenght of the fact  -/
  theorem GroundSubstitution.i_lt_atom_terms_len_iff_fact_terms_len {atom: FunctionFreeAtom sig} {fact : Fact sig} :
    ∀ subs ∈ GroundSubstitution.from_atom_and_fact atom fact, ∀ i, (i < atom.terms.length) ↔  i < fact.terms.length := by
      intro subs subs_mem i
      have len_eq := GroundSubstitution.atom_terms_len_eq_fact_terms_len subs subs_mem
      rw[len_eq]

  /--`GroundSubstitution.from_atom_and_fact` finds a substituition iff there exists one that maps the atom to the fact-/
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


  /--A PreTrigger consists of a rule and a substitution form the rulebody to a fact. Here we get this substitution via `GroundSubstitution.from_atom_and_fact`-/
  def PreTrigger.from_rule_and_fact (rule : LinearRule sig) (fact : Fact sig) : Option (PreTrigger sig) :=
    (GroundSubstitution.from_atom_and_fact rule.body fact).map (fun subs => {
      rule := rule.rule
      subs := subs
    })

  --this is just a slight variation of the definition given above
  theorem PreTrigger.from_rule_and_fact_some_implies {rule : LinearRule sig} {fact : Fact sig} :
      ∀ trg ∈ PreTrigger.from_rule_and_fact rule fact,  trg.rule = rule.rule ∧ GroundSubstitution.from_atom_and_fact rule.body fact = some trg.subs := by
        unfold PreTrigger.from_rule_and_fact;
        cases PreTrigger.from_rule_and_fact rule fact;
        repeat simp;


  -- this is definition 6 but we do not need the address u
  -- we use the already existing (Pre)Triggers to define the actual result of the rule application
  /--A rule can be appiled to a fact, if there exists a homomorphism from the rulebody to the fact (iff `PreTrigger.from_rule_and_fact` is some).
  The result of the Rule Applycation is then given by `trg.mapped_head` and consist of two facts (that are obtained from the rulehaed by applying the substitution and skolemization)-/
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

  /--If `ruleApply` returns some value for a rule and a fact, then `PreTrigger.from_rule_and_fact` also returns some value for the same rule and fact-/
  theorem ruleApply.some_implies_PreTrigger_some {rule: LinearRule sig} {fact: Fact sig}:
    (ruleApply rule fact).isSome -> (PreTrigger.from_rule_and_fact rule fact).isSome := by
    rw[ruleApply_eq]
    simp

  /--If `ruleApply` returns some for a rule and a fact, then this means, that rulebody and fact have the same number of terms in their resp. atom-/
  theorem ruleApply.body_length_eq_fact_length {rule: LinearRule sig} {fact: Fact sig} :
  (ruleApply_some : (ruleApply rule fact).isSome) -> rule.body.terms.length = fact.terms.length := by
  intro ruleApply_some
  have trg_some : (PreTrigger.from_rule_and_fact rule fact).isSome := by apply ruleApply.some_implies_PreTrigger_some; exact ruleApply_some
  rw[Option.isSome_iff_exists] at trg_some
  rcases trg_some with ⟨trg, trg_some⟩
  rcases PreTrigger.from_rule_and_fact_some_implies trg trg_some with ⟨rule_eq, some_subs⟩
  rw[GroundSubstitution.atom_terms_len_eq_fact_terms_len trg.subs]
  simp[some_subs]

  /--The resulting first Atom from `ruleApply` (if it doesn'r return none) hase the same number of terms as the first head atom of the rule -/
  theorem ruleApply_fst_term_lenght_eq_rule_head_length {rule:LinearRule sig} {fact: Fact sig} {ruleApply_some: (ruleApply rule fact).isSome}:
    ((ruleApply rule fact).get ruleApply_some).fst.terms.length = rule.head.fst.terms.length := by
      have trg_some : (PreTrigger.from_rule_and_fact rule fact).isSome := by apply ruleApply.some_implies_PreTrigger_some; exact ruleApply_some
      rw[Option.isSome_iff_exists] at trg_some
      rcases trg_some with ⟨trg, trg_some⟩
      simp only [ruleApply_eq, trg_some, Option.map_some, Option.get_some]
      simp only [PreTrigger.apply_to_function_free_atom]
      simp only [TermMapping.apply_generalized_atom, List.length_map]

  /--The resulting second Atom from `ruleApply` (if it doesn'r return none) hase the same number of terms as the second head atom of the rule -/
  theorem ruleApply_snd_term_lenght_eq_rule_head_length {rule:LinearRule sig} {fact: Fact sig} {ruleApply_some: (ruleApply rule fact).isSome}:
    ((ruleApply rule fact).get ruleApply_some).snd.terms.length = rule.head.snd.terms.length := by
      have trg_some : (PreTrigger.from_rule_and_fact rule fact).isSome := by apply ruleApply.some_implies_PreTrigger_some; exact ruleApply_some
      rw[Option.isSome_iff_exists] at trg_some
      rcases trg_some with ⟨trg, trg_some⟩
      simp only [ruleApply_eq, trg_some, Option.map_some, Option.get_some]
      simp only [PreTrigger.apply_to_function_free_atom]
      simp only [TermMapping.apply_generalized_atom, List.length_map]

  /--If i is a frontier-Position in the first head of the rule, then there exists some position j in fact such that `ruleApply rule fact` will map the term at the frontier-Position to the term at position j in the fact.-/
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

  /--If some positions in the first atom of the rule head and the body contain the same term, then the heads position of the second fact produced by `ruleApply`  will contain the term that occurs at the rule bodies position in the fact that is given as parameter to ruleApply.-/
  theorem rule_terms_eq_implies_ruleApply_terms_eq_fstHead {rule: LinearRule sig} {fact : Fact sig} {idxH idxB: Nat} (idxH_valid: idxH < rule.head.fst.terms.length) (idxB_valid: idxB < rule.body.terms.length) :
      (ruleApplySome: (ruleApply rule fact).isSome) -> rule.head.fst.terms[idxH] = rule.body.terms[idxB] ->
      ((ruleApply rule fact).get ruleApplySome).fst.terms[idxH]'(by rw[ruleApply_fst_term_lenght_eq_rule_head_length]; exact idxH_valid)
      = fact.terms[idxB]'(by rw[← ruleApply.body_length_eq_fact_length ruleApplySome]; exact idxB_valid) := by
    intro ruleApplySome terms_eq
    have trg_some : (PreTrigger.from_rule_and_fact rule fact).isSome := by apply ruleApply.some_implies_PreTrigger_some; exact ruleApplySome
    rw[Option.isSome_iff_exists] at trg_some
    rcases trg_some with ⟨trg, trg_some⟩
    have trg_some' := trg_some
    unfold PreTrigger.from_rule_and_fact at trg_some
    simp only[Option.map_eq_some_iff] at trg_some
    rcases trg_some with ⟨sub, sub_def, trg_eq⟩
    have sub_apply: sub.apply_function_free_atom rule.body = fact := by
      rw[GroundSubstitution.apply_function_free_atom_from_atom_and_fact]
      exact sub_def

    conv => right; simp only [← sub_apply, GroundSubstitution.apply_function_free_atom]; simp only[TermMapping.apply_generalized_atom, List.getElem_map]
    rw [← terms_eq]
    simp only [ruleApply_eq, trg_some', Option.map_some, Option.get_some]
    simp only [PreTrigger.apply_to_function_free_atom, TermMapping.apply_generalized_atom, List.getElem_map]
    cases ter_var: rule.head.fst.terms[idxH] with
    |const c => simp[PreTrigger.apply_to_var_or_const_for_const, GroundSubstitution.apply_var_or_const];
    |var var =>
      have h_frontier : is_frontier_position_fst rule idxH idxH_valid := by
        rw[frontier_pos_fst_iff_in_body]
        exists idxB, idxB_valid
        rw[← terms_eq]
        simp[ter_var, VarOrConst.isVar]
      rcases h_frontier with ⟨v, v_eq, v_front⟩
      rw[v_eq] at ter_var
      rw[← ter_var]
      rw [PreTrigger.apply_to_var_or_const_frontier_var _ _ _ (by rw [← trg_eq]; exact v_front)]
      rw [← trg_eq]
      rfl

  /--If some positions in rule head and body contain the same term, then the heads position of the second fact produced by `ruleApply`  will contain the term that occurs at the rule bodies position in the fact that is given as parameter to ruleApply.-/
  theorem rule_terms_eq_implies_ruleApply_terms_eq_sndHead {rule: LinearRule sig} {fact : Fact sig} {idxH idxB: Nat} (idxH_valid: idxH < rule.head.snd.terms.length) (idxB_valid: idxB < rule.body.terms.length) :
      (ruleApplySome: (ruleApply rule fact).isSome) -> rule.head.snd.terms[idxH] = rule.body.terms[idxB] ->
      ((ruleApply rule fact).get ruleApplySome).snd.terms[idxH]'(by rw[ruleApply_snd_term_lenght_eq_rule_head_length]; exact idxH_valid)
      = fact.terms[idxB]'(by rw[← ruleApply.body_length_eq_fact_length ruleApplySome]; exact idxB_valid) := by
    intro ruleApplySome terms_eq
    have trg_some : (PreTrigger.from_rule_and_fact rule fact).isSome := by apply ruleApply.some_implies_PreTrigger_some; exact ruleApplySome
    rw[Option.isSome_iff_exists] at trg_some
    rcases trg_some with ⟨trg, trg_some⟩
    have trg_some' := trg_some
    unfold PreTrigger.from_rule_and_fact at trg_some
    simp only[Option.map_eq_some_iff] at trg_some
    rcases trg_some with ⟨sub, sub_def, trg_eq⟩
    have sub_apply: sub.apply_function_free_atom rule.body = fact := by
      rw[GroundSubstitution.apply_function_free_atom_from_atom_and_fact]
      exact sub_def

    conv => right; simp only [← sub_apply, GroundSubstitution.apply_function_free_atom]; simp only[TermMapping.apply_generalized_atom, List.getElem_map]
    rw [← terms_eq]
    simp only [ruleApply_eq, trg_some', Option.map_some, Option.get_some]
    simp only [PreTrigger.apply_to_function_free_atom, TermMapping.apply_generalized_atom, List.getElem_map]
    cases ter_var: rule.head.snd.terms[idxH] with
    |const c => simp[PreTrigger.apply_to_var_or_const_for_const, GroundSubstitution.apply_var_or_const];
    |var var =>
      have h_frontier : is_frontier_position_snd rule idxH idxH_valid := by
        rw[frontier_pos_snd_iff_in_body]
        exists idxB, idxB_valid; rw[← terms_eq]
        simp[ter_var, VarOrConst.isVar]
      rcases h_frontier with ⟨v, v_eq, v_front⟩
      rw[v_eq] at ter_var
      rw[← ter_var]
      rw [PreTrigger.apply_to_var_or_const_frontier_var _ _ _ (by rw [← trg_eq]; exact v_front)]
      rw [← trg_eq]
      rfl

  --If i is a frontier-Position in the second head of the rule, then there exists some position j in fact such that `ruleApply rule fact` will map the term at the frontier-Position to the term at position j in the fact.-/
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

  /--If i is a position in the first rule head containing a non-frontier-variable (i.e. an existential variable),then `ruleApply` will map the term at this position to a functional term (a SkolemFunction)-/
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

   /--If i is a position in the second rule head containing a non-frontier-variable (i.e. an existential variable),then `ruleApply` will map the term at this position to a functional term (a SkolemFunction)-/
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

  /--an AddressSymbol consists of a Linear Rule and a Number 0 or 1 that references the first(0) or second(1) head of that rule-/
  structure AddressSymbol (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
    rule : LinearRule sig
    headIndex : Fin 2

  /--This function defines the set of all possible Address symbols of a rule set -/
  def addressSymbols (rs : LinearRuleSet sig) : Set (AddressSymbol sig) :=
    fun sym => sym.rule ∈ rs.rules

  /--An Address consists of an initial fact from the fat set and a list of address symbols from the rule set. The paper considers them a a word wu ∈ (fact set)(addressSymbols)* which allows talking about prefixes of addresses-/
  structure Address (fs : FactSet sig) (rs : LinearRuleSet sig) where
    initialAtom : {f : Fact sig // f ∈ fs}
    path : List {sym : AddressSymbol sig // sym ∈ addressSymbols rs} --This List is intended to be filled from right to left (i.e. the last element of the List is the Address symbol that is direct successor of the initial Atom)


  /--This definition returns true iff the immediate prefix of an address (i.e. the same Address just with the Address-path being shortend by the first symbol) is contained is Set f-/
  def immed_prefix_address_in_set {fs: FactSet sig} (a: Address fs rs) (f : Set (Address fs rs)) : Prop :=
  -- with this definition, we use the List of address-symbols that bulids the path from rigth to left (contrary on how it's written in the paper)
  -- therefore we would write an address wuv ∈ IA* (with w ∈ I, u,v ∈ A) as {initialAtom := w , path :=[v,u]}
    match a.path with
    |[] => true
    |_::ls => let b:= {a with path := ls}; b ∈ f

  /--A forest is a set of addresses with the following two properties: (1) the fact set is fully contained in the forest and (2) for each addresses all its prefixae are in the forest too-/
  structure Forest (fs : FactSet sig) (rs : LinearRuleSet sig) where
    f : Set (Address fs rs)
    fs_contained : ∀ fact ∈ fs, ∃ a ∈ f , fact = a.initialAtom ∧ a.path = []  -- fs shall be contained in f (this should likely involve auxiliary definitions)
    isPrefixClosed : ∀ a ∈ f, immed_prefix_address_in_set a f --as we enforce this check on all a ∈ f, we only need to verify that it's immediate predecessor is in f as well

  namespace Forest

  /--A forest is subforest of another one if it is a subset-/
  def subforest_of {fs: FactSet sig} (g : Forest fs rs) (f : Forest fs rs) : Prop := g.f ⊆ f.f

  /--The subforest relation is reflexive-/
  theorem subforest_refl {fs: FactSet sig} {f: Forest fs rs}: --subforest relation is reflexive
      f.subforest_of f := by
    unfold subforest_of
    simp[Subset]

  /-the subforest relation is transitive-/
  theorem subforest_trans {fs: FactSet sig} {f g h : Forest fs rs}: --subforest-relation is transitive
      f.subforest_of g ->  g.subforest_of h -> f.subforest_of h := by
    unfold subforest_of
    apply Set.subset_trans

  end Forest

  /--A Fact set can be seen as a forest too where all adresses have an empty path-/
  def FactSet.toForest (fs: FactSet sig) : Forest fs rs where
  f:= fun x => x.path = []
  fs_contained := by intro fact fact_mem;  exists {initialAtom := ⟨fact, fact_mem⟩, path := []}
  isPrefixClosed:= by intro fact fact_addr; unfold immed_prefix_address_in_set; rw[fact_addr]


end Addresses

section ObvliviousChaseRepresentation

  /--The Labelling Function maps an address to a fact if possible.
  The fact is created by successively applying the rules of the address symbols.
  Starting from the initial atom of the address, the rule of the first address symbol is applied then from the result one takes the head atom that is referenced by the address symbol and applies the naxt rule onto that.
  As rule applycation may fail (if there is no homomorphism) the labelling can also return none
   -/
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

  /--The oblivious chase representation is the forest of all addresses where the labelling function returns Option.some fact -/
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

  /--The materialization of a forest is the set of all facts that can be produced by labellings from addresses of the forest-/
  def materialization_labelling {fs: FactSet sig} (g: Forest fs rs) : FactSet sig :=
    fun a => ∃ b∈ g.f, labellingFunction b = Option.some a

  /--For all Addresses that are part of a subforest of the obllivious chase the labbeling function returns some fact-/
  theorem subforest_of_oblivious_chase_labelling_some {fs: FactSet sig} {g: Forest fs rs} {h: Forest.subforest_of g (oblivious_chase fs rs)}:
    ∀a, a ∈ g.f -> (labellingFunction a).isSome  := by
      intro a a_mem
      unfold Forest.subforest_of at h
      rw[h]
      exact a_mem


end ObvliviousChaseRepresentation


section TriggersAndChaseDerivation

  /--A trigger consists of a Linear rule from the rule set and an address such that there exists an homomorphism from the rulebody to the labelling of the address-/
  structure LinearRuleTrigger (fs: FactSet sig) (rs: LinearRuleSet sig) where
  rule : {r: LinearRule sig // r ∈ rs.rules}
  addr : {u: Address fs rs // (labellingFunction u).isSome}
  hom_exists : (GroundSubstitution.from_atom_and_fact (LinearRule.body rule) (Option.get (labellingFunction addr.val) addr.property )).isSome = true

  namespace LinearRuleTrigger

    /--from the trigger's rule on can bild two address symbols (one for each head). The Appplication of the trigger produces the two addresses that arise from adding one of those address symbols each to the trigger's address -/
    def apply {fs:FactSet sig} (pi : LinearRuleTrigger fs rs) : (Address fs rs) × (Address fs rs) :=
      let fst: {f : AddressSymbol sig // f ∈ addressSymbols rs}:=
        {val:= {rule:= pi.rule.val,headIndex:=0}, property:= by unfold addressSymbols; exact pi.rule.property;}
      let snd: {f : AddressSymbol sig // f ∈ addressSymbols rs}:=
        {val:= {rule:= pi.rule.val,headIndex:=1}, property:= by unfold addressSymbols; exact pi.rule.property;}
      ({initialAtom:= pi.addr.val.initialAtom, path:=(fst ::pi.addr.val.path)},
      {initialAtom:= pi.addr.val.initialAtom, path:=(snd ::pi.addr.val.path)})

    /--If you call `ruleApply` on the trigger's rule and labelling of the address, then you get Option.some value-/
    theorem ruleApply_of_trigger_labelling_is_some {fs: FactSet sig} {pi: LinearRuleTrigger fs rs}:
      (ruleApply pi.rule.val (Option.get (labellingFunction pi.addr.val) pi.addr.property)).isSome := by
        rw[ruleApply_eq]
        unfold PreTrigger.from_rule_and_fact
        simp only [Option.map_map, Option.isSome_map]
        exact pi.hom_exists

    /--The labelling of the addresses produced by the trigger applicstion is some-/
    theorem labellingFunction_trg_apply_is_some {fs: FactSet sig} {pi: LinearRuleTrigger fs rs}:
        (labellingFunction pi.apply.fst).isSome ∧ (labellingFunction pi.apply.snd).isSome := by
      unfold labellingFunction apply
      simp only [Fin.isValue, ↓reduceIte]
      have l_some: (labellingFunction pi.addr.val).isSome := by exact pi.addr.property;
      cases h: labellingFunction pi.addr.val with
      |none =>
        rw[← Option.not_isSome_iff_eq_none] at h
        contradiction
      |some a =>
        simp only [Option.isSome_map]
        rw[← Option.get_of_eq_some l_some h]
        simp[ruleApply_of_trigger_labelling_is_some]

    /--this function gives a shortcut for retrieving the actual labellings for the addresses created by the trigger application-/
    def labelling_of_apply {fs: FactSet sig} (pi: LinearRuleTrigger fs rs) : (Fact sig) × (Fact sig) :=
      let lu := Option.get (labellingFunction pi.addr.val) pi.addr.property
      have ruleApply_some: (ruleApply pi.rule.val lu).isSome := by unfold lu; simp[ruleApply_of_trigger_labelling_is_some]
      Option.get (ruleApply pi.rule.val lu) ruleApply_some

    /--this shows that the schortcut of `labelling_of_apply` is actually correct-/
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

    /--The predicates of the first atom of the trigger'st rule head and the first fact produced by `labelling_of_apply` are the same-/
    theorem trg_apply_labelling_fst_predicate_eq {fs: FactSet sig} {pi: LinearRuleTrigger fs rs} :
          pi.rule.val.head.fst.predicate = (labelling_of_apply pi).fst.predicate := by
            unfold labelling_of_apply;
            simp only[ruleApply_eq];
            unfold PreTrigger.apply_to_function_free_atom PreTrigger.apply_to_var_or_const TermMapping.apply_generalized_atom;
            simp;

    /--The predicates of the  second atom of the  rule head and the second fact produced by `labelling_of_apply` are the same-/
    theorem trg_apply_labelling_snd_predicate_eq {fs: FactSet sig} {pi: LinearRuleTrigger fs rs} :
          pi.rule.val.head.snd.predicate = (labelling_of_apply pi).snd.predicate := by
            unfold labelling_of_apply;
            simp only[ruleApply_eq];
            unfold PreTrigger.apply_to_function_free_atom PreTrigger.apply_to_var_or_const TermMapping.apply_generalized_atom;
            simp;

    /--The number of terms in the first atom of the trigger's rule head and in the first fact produced by `labelling_of_apply` are the same-/
    theorem trg_apply_labelling_fst_terms_len {fs: FactSet sig} {pi: LinearRuleTrigger fs rs} :
          pi.rule.val.head.fst.terms.length = (labelling_of_apply pi).fst.terms.length := by
        rw[GeneralizedAtom.arity_ok]
        simp only[trg_apply_labelling_fst_predicate_eq]
        rw[← GeneralizedAtom.arity_ok]

    /--The number of terms in the second atom of the trigger's rule head and in the second fact produced by `labelling_of_apply` are the same-/
    theorem trg_apply_labelling_snd_terms_len {fs: FactSet sig} {pi: LinearRuleTrigger fs rs} :
          pi.rule.val.head.snd.terms.length = (labelling_of_apply pi).snd.terms.length := by
        rw[GeneralizedAtom.arity_ok]
        simp only[trg_apply_labelling_snd_predicate_eq]
        rw[← GeneralizedAtom.arity_ok]

    /--The atom in the trigger's rule's body has the same number of terms ar the fact produced by the labelling of the trigger's address-/
    theorem rule_body_terms_len_eq_addr_labelling_terms_len {fs: FactSet sig} {pi: LinearRuleTrigger fs rs} :
        pi.rule.val.body.terms.length = (Option.get (labellingFunction pi.addr.val) pi.addr.property).terms.length := by
      let sub := pi.hom_exists
      rw[Option.isSome_iff_exists] at sub
      rcases sub with ⟨sub, sub_eq⟩
      rw [GroundSubstitution.atom_terms_len_eq_fact_terms_len sub]
      simp [sub_eq]

    /--If some positions idxH,idxB in the trigger's first rule head and body (resp.) contain the same term (this is then either a frontier variable or constant), then the first fact produced by `labelling_of_apply` contains the same term at position idxH, as the labelling of the trigger's address contains at idxB.-/
    theorem term_in_rule_eq_implies_in_labelling_eq_fstHead {fs: FactSet sig} {pi: LinearRuleTrigger fs rs} {idxB idxH : Nat} (idxB_valid : idxB < pi.rule.val.body.terms.length) (idxH_valid: idxH < pi.rule.val.head.fst.terms.length):
        pi.rule.val.body.terms[idxB] = pi.rule.val.head.fst.terms[idxH] ->
        (Option.get (labellingFunction pi.addr.val) pi.addr.property).terms[idxB]'(by rw[rule_body_terms_len_eq_addr_labelling_terms_len] at idxB_valid; exact idxB_valid)
        = (labelling_of_apply pi).fst.terms[idxH]'(by rw[trg_apply_labelling_fst_terms_len] at idxH_valid; exact idxH_valid) := by
      intro t_eq
      unfold labelling_of_apply
      simp
      rw[rule_terms_eq_implies_ruleApply_terms_eq_fstHead (idxB:= idxB) (idxH := idxH) idxH_valid idxB_valid]
      rw[eq_comm]
      exact t_eq

    /--If some positions idxH,idxB in the trigger's second rule head and body (resp.) contain the same term (this is then either a frontier variable or constant), then the second fact produced by `labelling_of_apply` contains the same term at position idxH, as the labelling of the trigger's address contains at idxB.-/
    theorem term_in_rule_eq_implies_in_labelling_eq_sndHead {fs: FactSet sig} {pi: LinearRuleTrigger fs rs} {idxB idxH : Nat} (idxB_valid : idxB < pi.rule.val.body.terms.length) (idxH_valid: idxH < pi.rule.val.head.snd.terms.length):
        pi.rule.val.body.terms[idxB] = pi.rule.val.head.snd.terms[idxH] ->
        (Option.get (labellingFunction pi.addr.val) pi.addr.property).terms[idxB]'(by rw[rule_body_terms_len_eq_addr_labelling_terms_len] at idxB_valid; exact idxB_valid)
        = (labelling_of_apply pi).snd.terms[idxH]'(by rw[trg_apply_labelling_snd_terms_len] at idxH_valid; exact idxH_valid) := by
      intro t_eq
      unfold labelling_of_apply
      simp
      rw[rule_terms_eq_implies_ruleApply_terms_eq_sndHead (idxB:= idxB) (idxH := idxH) idxH_valid idxB_valid]
      rw[eq_comm]
      exact t_eq

    /--A trigger appears in a forest, if it's address is part of the forest-/
    def appears_in_forest {fs: FactSet sig} (pi: LinearRuleTrigger fs rs) (g: Forest fs rs): Prop := pi.addr.val ∈ g.f

    -- TODO for Laila: If you want, you can instantiate the Membership typeclass for triggers and forests to be able to write: pi ∈ g and define this to be pi.appears_in_forest g

    /--A trigger is active in a forest, if it's address is part of that forest, but at least one of the addresses that are produced by trigger application isn't part of the forest.-/
    def isActive_in_forest {fs: FactSet sig} (pi:LinearRuleTrigger fs rs) (g: Forest fs rs) : Prop :=
      pi.appears_in_forest g ∧ ¬ (pi.apply.fst ∈ g.f ∧ pi.apply.snd ∈ g.f)

    /--A forest-address is just an address that occurs in a specific forest-/
    def forest_Address {fs: FactSet sig} (g : Forest fs rs) := {addr : Address fs rs // addr ∈ g.f }

    /--every forest address where the forest is subforest of the oblivious chase is labelled to Option.some ... by the `labellingFunction`-/
    theorem forest_addr_label_some {fs: FactSet sig} {g: Forest fs rs} {g_sub: g.subforest_of (oblivious_chase fs rs)} {b: forest_Address g}:
      (labellingFunction b.val).isSome := by
        revert b
        unfold forest_Address
        simp only [Subtype.forall]
        apply subforest_of_oblivious_chase_labelling_some
        exact g_sub

    /--A forest_trigger of a forest is a trigger that appears in that specific forest-/
    def forest_Trigger {fs: FactSet sig} (g : Forest fs rs) := {trg : LinearRuleTrigger fs rs // trg.appears_in_forest g}

    /--Two addresses b1, b2 are Blocking team for a trigger iff ...(See definition 11 in the paper). Note that this definition slighliy differs from the definition in the paper in the sense that we don't requite h to be the identity on ⟨u⟩ but only on the frontier-positional terms in ⟨u⟩-/
    def blockingTeam {fs: FactSet sig} {g : Forest fs rs} (g_sub : g.subforest_of (oblivious_chase fs rs)) (b1 b2 : forest_Address g) (pi : forest_Trigger g) : Prop :=
      -- Note: this definition differs from the original paper
      ∃ h: GroundTermMapping sig,
      -- h is the identity on frontier-terms in the labelling of te trigger's address
      (∀ i, (i_valid: i < pi.val.rule.val.body.terms.length) -> is_frontier_position_body pi.val.rule.val i i_valid ->
        (h.applyFact (Option.get (labellingFunction pi.val.addr.val) pi.val.addr.property)).terms[i]'(by unfold GroundTermMapping.applyFact; rw[TermMapping.length_terms_apply_generalized_atom]; rw[← rule_body_terms_len_eq_addr_labelling_terms_len]; exact i_valid)
        = (Option.get (labellingFunction pi.val.addr.val) pi.val.addr.property).terms[i]'(by rw[← rule_body_terms_len_eq_addr_labelling_terms_len]; exact i_valid))
      -- h on the first fact from the labelling of the trigger application equals the labelling of b1
      ∧ h.applyFact (labelling_of_apply pi.val).fst = Option.get (labellingFunction b1.val) (by apply forest_addr_label_some; exact g_sub)
      -- h on the second fact from the labelling of the trigger application equals the labelling of b2
      ∧ h.applyFact (labelling_of_apply pi.val).snd = Option.get (labellingFunction b2.val) (by apply forest_addr_label_some; exact g_sub)
      ∧ h.isIdOnConstants

    /--these are the three conditions from the alternative blocking-team definition. If they hold true then b1 and b2 are a plocking team for the trigger (see Observation 12 in the paper). Note that we needed to add the treatment of constants at condition two. -/
    structure Conditions {fs: FactSet sig} {g : Forest fs rs} (g_sub: g.subforest_of (oblivious_chase fs rs)) (b1 b2: forest_Address g) (pi: forest_Trigger g) where
      b1_label := Option.get (labellingFunction b1.val) (by apply forest_addr_label_some; exact g_sub)
      b2_label:= Option.get (labellingFunction b2.val) (by apply forest_addr_label_some; exact g_sub)
      b1_label_eq : b1_label = Option.get (labellingFunction b1.val) (by apply forest_addr_label_some; exact g_sub) := by rfl
      b2_label_eq : b2_label = Option.get (labellingFunction b2.val) (by apply forest_addr_label_some; exact g_sub) := by rfl
      first : (b1_label.predicate = (labelling_of_apply pi.val).fst.predicate)
        ∧ (b2_label.predicate = (labelling_of_apply pi.val).snd.predicate)
      second : --note that this slightly differs from the original paper as constant were neglected there
        (∀ j, (lt_fst: j < pi.val.rule.val.head.fst.terms.length) -> (is_frontier_position_fst pi.val.rule.val j lt_fst) ∨ (∃ c, pi.val.rule.val.head.fst.terms[j] = VarOrConst.const c) ->
          (labelling_of_apply pi.val).fst.terms[j]'(by rw[← trg_apply_labelling_fst_terms_len]; exact lt_fst) = b1_label.terms[j]'(by rw[GeneralizedAtom.arity_ok, first.left, ← trg_apply_labelling_fst_predicate_eq, ← GeneralizedAtom.arity_ok]; simp[lt_fst]))
        ∧ (∀ j, (lt_snd: j < pi.val.rule.val.head.snd.terms.length) -> (is_frontier_position_snd pi.val.rule.val j lt_snd) ∨ (∃ c, pi.val.rule.val.head.snd.terms[j] = VarOrConst.const c) ->
          (labelling_of_apply pi.val).snd.terms[j]'(by rw[← trg_apply_labelling_snd_terms_len]; exact lt_snd) = b2_label.terms[j]'(by rw[GeneralizedAtom.arity_ok, first.right, ← trg_apply_labelling_snd_predicate_eq, ← GeneralizedAtom.arity_ok]; simp[lt_snd]))
      third : (∀ i j:Nat, (labelling_of_apply pi.val).fst.terms[i]? = (labelling_of_apply pi.val).fst.terms[j]? -> b1_label.terms[i]? = b1_label.terms[j]?)
        ∧ (∀ i j:Nat, (labelling_of_apply pi.val).fst.terms[i]? = (labelling_of_apply pi.val).snd.terms[j]? -> b1_label.terms[i]? = b2_label.terms[j]?)
        ∧ (∀ i j:Nat, (labelling_of_apply pi.val).snd.terms[i]? = (labelling_of_apply pi.val).snd.terms[j]? -> b2_label.terms[i]? = b2_label.terms[j]?)

    /--this is just a helper theorem to simplify the expression `cond.b1_label.terms[List.idxOf pi.val.labelling_of_apply.fst.terms[i] pi.val.labelling_of_apply.fst.terms]` Maybe this could be stated in a more general result (?) -/
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

    /--this is just a helper theorem to simplify the expression `cond.b2_label.terms[List.idxOf pi.val.labelling_of_apply.snd.terms[i] pi.val.labelling_of_apply.snd.terms]` -/
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

    /--this shows the equivalence of the two definitons for blocking teams (This is the proof for observation 12 in the paper)-/
    theorem blockingTeam.iff {fs: FactSet sig} {g : Forest fs rs} {g_sub: g.subforest_of (oblivious_chase fs rs)} {b1 b2: forest_Address g} {pi: forest_Trigger g} :
      blockingTeam g_sub b1 b2 pi ↔ ∃ _: Conditions g_sub b1 b2 pi, True := by
        unfold blockingTeam
        constructor
        -- direction →
        . unfold GroundTermMapping.applyFact TermMapping.apply_generalized_atom
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
              rw[frontier_pos_fst_iff_in_body] at j_frontier_pos
              rcases j_frontier_pos with ⟨idx,idx_lt,term_var,in_body_at_idx⟩
              unfold labelling_of_apply
              rw[rule_terms_eq_implies_ruleApply_terms_eq_fstHead (rule := pi.val.rule.val) (fact := (Option.get (labellingFunction pi.val.addr.val) pi.val.addr.property)) (idxH := j) (idxB := idx) j_valid idx_lt (by
                simp[ruleApply_of_trigger_labelling_is_some]) in_body_at_idx ]
              have a_left := a.left
              simp only [List.getElem_map] at a_left
              rw[eq_comm]
              apply a_left
              have frontier_pos_h: is_frontier_position_fst pi.val.rule.val j j_valid := by
                rw[frontier_pos_fst_iff_in_body]
                exists idx, idx_lt
              unfold is_frontier_position_fst at frontier_pos_h
              rcases frontier_pos_h with ⟨v, v_frontier⟩
              unfold is_frontier_position_body
              exists v
              rw[← in_body_at_idx]
              exact v_frontier
            . intro c c_eq
              simp only [← a.right.left, List.getElem_map]
              have hc_id : h (GroundTerm.const c) = (GroundTerm.const c) := by
                let h_const_id:= a.right.right--.right.right
                unfold GroundTermMapping.isIdOnConstants at h_const_id
                rw[h_const_id.right]
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
              rw[frontier_pos_snd_iff_in_body] at j_frontier_pos
              rcases j_frontier_pos with ⟨idx,idx_lt,term_var,in_body_at_idx⟩
              rw[rule_terms_eq_implies_ruleApply_terms_eq_sndHead (rule := pi.val.rule.val) (fact := (Option.get (labellingFunction pi.val.addr.val) pi.val.addr.property)) (idxH := j) (idxB := idx) j_valid idx_lt (by
                simp[ruleApply_of_trigger_labelling_is_some]) in_body_at_idx ]
              have a_left := a.left
              simp only [List.getElem_map] at a_left
              rw[eq_comm]
              apply a_left
              have frontier_pos_h: is_frontier_position_snd pi.val.rule.val j j_valid := by
                rw[frontier_pos_snd_iff_in_body]
                exists idx, idx_lt
              unfold is_frontier_position_snd at frontier_pos_h
              rcases frontier_pos_h with ⟨v, v_frontier⟩
              unfold is_frontier_position_body
              exists v
              rw[← in_body_at_idx]
              exact v_frontier
            . intro c c_eq
              simp only [← a.right.right.left, List.getElem_map]
              have hc_id : h (GroundTerm.const c) = (GroundTerm.const c) := by
                let h_const_id:= a.right.right
                unfold GroundTermMapping.isIdOnConstants at h_const_id
                rw[h_const_id.right]
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
          -- show h(⟨u⟩) = ⟨u⟩ for frontier positions
          . intro idxB idxB_valid frontier_body
            have inAnyHead: pi.val.rule.val.body.terms[idxB] ∈ pi.val.rule.val.head.fst.terms ∨ pi.val.rule.val.body.terms[idxB] ∈ pi.val.rule.val.head.snd.terms := by
              simp[frontier_occus_in_head idxB idxB_valid frontier_body]
            unfold is_frontier_position_body at frontier_body
            rcases frontier_body with ⟨v, v_frontier⟩
            simp[h]

            cases inAnyHead with
            |inl in_fstHead =>
              simp only[List.mem_iff_getElem] at in_fstHead
              rcases in_fstHead with ⟨idxH,idxH_valid, rule_terms_eq⟩
              rw[← rule_terms_eq] at v_frontier
              have frontierHead: is_frontier_position_fst pi.val.rule.val idxH idxH_valid := by
                unfold is_frontier_position_fst
                exact (Exists.intro v v_frontier)
              rw[eq_comm] at rule_terms_eq
              let label_terms_eq := rule_terms_eq
              rw[term_in_rule_eq_implies_in_labelling_eq_fstHead (idxB:=idxB) (idxH:=idxH) idxB_valid idxH_valid rule_terms_eq]
              simp only [List.getElem_mem, ↓reduceDIte]
              rw[b1_label_terms_idxOf_eq]
              simp[snd.left idxH idxH_valid (Or.inl frontierHead)]
            |inr in_sndHead =>
              simp only[List.mem_iff_getElem] at in_sndHead
              rcases in_sndHead with ⟨idxH, idxH_valid, rule_terms_eq⟩
              rw[← rule_terms_eq] at v_frontier
              have frontierHead: is_frontier_position_snd pi.val.rule.val idxH idxH_valid := by
                unfold is_frontier_position_snd
                exact (Exists.intro v v_frontier)
              rw[eq_comm] at rule_terms_eq
              let label_terms_eq := rule_terms_eq
              rw[term_in_rule_eq_implies_in_labelling_eq_sndHead (idxB:=idxB) (idxH:=idxH) idxB_valid idxH_valid rule_terms_eq]
              simp only [List.getElem_mem, ↓reduceDIte]
              rw[b2_label_terms_idxOf_eq]
              simp only [snd.right idxH idxH_valid (Or.inl frontierHead), dite_eq_right_iff]
              intro b2_in_fstHead_terms
              simp only[List.mem_iff_getElem] at b2_in_fstHead_terms
              rcases b2_in_fstHead_terms with ⟨idx_fstH, idx_fstH_len, terms_eq⟩
              conv => left; simp[← terms_eq]
              rw[b1_label_terms_idxOf_eq]
              rw[← Option.some_inj]
              simp only[← List.getElem?_eq_getElem]
              apply trd.right.left
              rw[List.getElem?_eq_getElem idx_fstH_len]
              let snd_right := snd.right
              have idxH_lt: idxH < pi.val.labelling_of_apply.snd.terms.length := by rw[← trg_apply_labelling_snd_terms_len]; exact idxH_valid
              rw[List.getElem?_eq_getElem idxH_lt]
              simp only [snd.right idxH idxH_valid (Or.inl frontierHead), Option.some.injEq]
              exact terms_eq

          . constructor
            --shows h(⟨up_1⟩) = ⟨v_1⟩  i.e. h (pi.val.labelling_of_apply.fst) = (labellingFunction b1.val).get ...
            . rw[GeneralizedAtom.mk.injEq]
              rw[← fst.left]
              simp only [cond.b1_label_eq, true_and]
              rw[List.map_eq_iff]
              intro i
              unfold Option.map
              by_cases i_len: i <  pi.val.labelling_of_apply.fst.terms.length
              . simp[i_len]
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
                unfold h
                by_cases mem_apply_label: GroundTerm.const t ∈ pi.val.labelling_of_apply.fst.terms
                -- if t occurs in pi.val.labelling_of_apply.fst then:
                -- t can either be in a frontier position, then h(t) = t by the snd.condition,
                -- or t is not frontier, then
                -- either c was a Constant already in the rule or it was an ex. Variable and therefore will be mapped to a null, not a constant which gives a contradiction
                . simp only [mem_apply_label, ↓reduceDIte]
                  have listIdx_lt_rule_head: List.idxOf (GroundTerm.const t) pi.val.labelling_of_apply.fst.terms < pi.val.rule.val.head.fst.terms.length := by
                    rw[trg_apply_labelling_fst_terms_len]
                    simp only[List.idxOf_lt_length_iff]
                    exact mem_apply_label
                  simp only[List.mem_iff_getElem] at mem_apply_label
                  rcases mem_apply_label with ⟨i, i_lt, t_eq⟩
                  by_cases inFrontier: is_frontier_position_fst pi.val.rule.val (List.idxOf (GroundTerm.const t) pi.val.labelling_of_apply.fst.terms) listIdx_lt_rule_head
                  . rw[← snd.left (List.idxOf (GroundTerm.const t) pi.val.labelling_of_apply.fst.terms) listIdx_lt_rule_head (Or.inl inFrontier)]
                    rw[List.getElem_idxOf_of_mem mem_apply_label]

                  . cases const_var: pi.val.rule.val.head.fst.terms[(List.idxOf (GroundTerm.const t) pi.val.labelling_of_apply.fst.terms)] with
                      |const c =>
                        rw[← snd.left (List.idxOf (GroundTerm.const t) pi.val.labelling_of_apply.fst.terms) listIdx_lt_rule_head (Or.inr (Exists.intro c const_var))]
                        rw[List.getElem_idxOf_of_mem mem_apply_label]
                      |var v => -- term is non-frontier-variable; should lead to contradiction
                        simp only[cond.b1_label_eq]
                        have list_elem_eq: pi.val.labelling_of_apply.fst.terms[i] =
                          pi.val.labelling_of_apply.fst.terms[List.idxOf pi.val.labelling_of_apply.fst.terms[i] pi.val.labelling_of_apply.fst.terms]'(by simp only[← t_eq] at listIdx_lt_rule_head; rw[← trg_apply_labelling_fst_terms_len]; exact listIdx_lt_rule_head) := by
                           simp[List.getElem_idxOf_of_mem]
                        unfold is_frontier_position_fst at inFrontier
                        rw[not_exists] at inFrontier
                        simp only [const_var, VarOrConst.var.injEq, not_and, forall_eq'] at inFrontier
                        simp only[← t_eq]
                        simp only[← t_eq] at const_var
                        rcases ruleApply_non_frontier_var_fstHead_is_fun (rule := pi.val.rule.val) (fact := (Option.get (labellingFunction pi.val.addr.val) pi.val.addr.property))
                          (i := List.idxOf pi.val.labelling_of_apply.fst.terms[i] pi.val.labelling_of_apply.fst.terms)
                          (by rw[← t_eq] at listIdx_lt_rule_head; exact listIdx_lt_rule_head) (by simp[ruleApply_of_trigger_labelling_is_some]) (Exists.intro v (And.intro const_var inFrontier))
                          with ⟨x, y, z, rA_eq_func⟩

                        rw[list_elem_eq] at t_eq
                        conv at t_eq => left; arg 1; unfold labelling_of_apply
                        rw[rA_eq_func] at t_eq
                        unfold GroundTerm.func GroundTerm.const at t_eq
                        simp at t_eq
                . simp only [mem_apply_label, ↓reduceDIte, dite_eq_right_iff]
                  intro t_in_snd_label
                  have listIdx_lt_rule_head: List.idxOf (GroundTerm.const t) pi.val.labelling_of_apply.snd.terms < pi.val.rule.val.head.snd.terms.length := by
                    rw[trg_apply_labelling_snd_terms_len]
                    simp only[List.idxOf_lt_length_iff]
                    exact t_in_snd_label
                  simp only[List.mem_iff_getElem] at t_in_snd_label
                  rcases t_in_snd_label with ⟨i, i_lt, t_eq⟩

                  by_cases inFrontier: is_frontier_position_snd pi.val.rule.val (List.idxOf ( GroundTerm.const t) pi.val.labelling_of_apply.snd.terms) listIdx_lt_rule_head
                    -- term is in frontier
                  . rw[← snd.right (List.idxOf (GroundTerm.const t) pi.val.labelling_of_apply.snd.terms) listIdx_lt_rule_head (Or.inl inFrontier)]
                    rw[List.getElem_idxOf_of_mem t_in_snd_label]
                    -- term not in frontier
                  . cases const_var: pi.val.rule.val.head.snd.terms[(List.idxOf (GroundTerm.const t) pi.val.labelling_of_apply.snd.terms)] with
                    |const c =>
                      rw[← snd.right (List.idxOf (GroundTerm.const t) pi.val.labelling_of_apply.snd.terms) listIdx_lt_rule_head (Or.inr (Exists.intro c const_var))]
                      rw[List.getElem_idxOf_of_mem t_in_snd_label]
                    |var v =>
                      simp only[cond.b2_label_eq]
                      have list_elem_eq: pi.val.labelling_of_apply.snd.terms[i] =
                        pi.val.labelling_of_apply.snd.terms[List.idxOf pi.val.labelling_of_apply.snd.terms[i] pi.val.labelling_of_apply.snd.terms]'(by simp only[← t_eq] at listIdx_lt_rule_head; rw[← trg_apply_labelling_snd_terms_len]; exact listIdx_lt_rule_head) := by
                          simp[List.getElem_idxOf_of_mem]
                      unfold is_frontier_position_snd at inFrontier
                      rw[not_exists] at inFrontier
                      simp only [const_var, VarOrConst.var.injEq, not_and, forall_eq'] at inFrontier
                      simp  only[← t_eq]
                      simp only[← t_eq] at const_var

                      rcases ruleApply_non_frontier_var_sndHead_is_fun (rule := pi.val.rule.val) (fact := (Option.get (labellingFunction pi.val.addr.val) pi.val.addr.property))
                        (i := List.idxOf pi.val.labelling_of_apply.snd.terms[i] pi.val.labelling_of_apply.snd.terms)
                        (by rw[← t_eq] at listIdx_lt_rule_head; exact listIdx_lt_rule_head) (by simp[ruleApply_of_trigger_labelling_is_some]) (Exists.intro v (And.intro const_var inFrontier))
                        with ⟨x, y, z, rA_eq_func⟩

                      rw[list_elem_eq] at t_eq
                      conv at t_eq => left; arg 1; unfold labelling_of_apply
                      rw[rA_eq_func] at t_eq

                      unfold GroundTerm.func GroundTerm.const at t_eq
                      simp at t_eq

    /--returns the resulting forest that arises if one adds the result of pi.apply to forest g if pi is a Trigger that is active in g-/
    def active_trigger_apply_resulting_forest {fs: FactSet sig} (pi: LinearRuleTrigger fs rs) (g: Forest fs rs) (pi_active: pi.isActive_in_forest g) : Forest fs rs where
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

    /--the original forest g is a subforest of the one produced by `active_trigger_apply_resulting_forest`-/
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

    /--A `PossiblyInfiniteList` of triggers is called `PreChaseDerivation`-/
    abbrev PreChaseDerivation (fs: FactSet sig) (rs: LinearRuleSet sig) := PossiblyInfiniteList (LinearRuleTrigger fs rs)

    namespace PreChaseDerivation

    /--This structure defines two conditions that must hold for the correspondence between a trigger and two forests. It is be needed to define chase derivations.
    (1) the trigger must be active in the forest 'before'
    (2) adding the application of the trigger to forest 'before' results in the forest 'after' -/
    structure trg_application_cond {fs: FactSet sig} (trg: LinearRuleTrigger fs rs) (before : Forest fs rs) (after : Option (Forest fs rs)) where
      active : trg.isActive_in_forest before
      result : after = some (LinearRuleTrigger.active_trigger_apply_resulting_forest trg before active)

    /--A forest sequence is valid for a `PreChaseDerivation`-trigger sequence, if it (1) starts with the fact set and then (2) for each number n on which the trigger sequence is defined, the `trg_application_condition` holds for that trigger together with the forests at positions n and n+1 in the forest-sequence-/
    def forest_seq_valid {fs: FactSet sig} (trg_seq : PreChaseDerivation fs rs) (forest_seq : PossiblyInfiniteList (Forest fs rs)): Prop :=
      forest_seq.get? 0 = some fs.toForest ∧
      ∀ n : Nat, match (trg_seq.get? n) with
        | none => (forest_seq.get? (n+1)).isNone
        | some trg => (forest_seq.get? n).elim False (fun before =>
          let after := forest_seq.get? (n+1)
          trg_application_cond trg before after)

    /--if two forest sequences are both valid for the same trigger-sequence, then they are equal-/
    theorem forest_seq_valid_implies_unique {fs: FactSet sig}{trg_seq: PreChaseDerivation fs rs}:
        ∀ forest_seq_1 forest_seq_2, forest_seq_valid trg_seq forest_seq_1 ∧ forest_seq_valid trg_seq forest_seq_2
        -> forest_seq_1 = forest_seq_2 := by
      intro forest_seq_1 forest_seq_2
      unfold forest_seq_valid
      simp only [Option.isNone_iff_eq_none, and_imp]
      intro valid_1_start valid_1_rest valid_2_start valid_2_rest
      rw[PossiblyInfiniteList.ext_iff]
      intro n
      induction n with
      |zero =>
        simp[valid_1_start, valid_2_start]
      |succ n ih =>
        specialize valid_1_rest (n)
        specialize valid_2_rest (n)
        cases trg_n: trg_seq.get? n with
        |none =>
          simp only [trg_n] at valid_1_rest valid_2_rest
          rw[valid_1_rest,valid_2_rest]
        |some trg =>
          simp only[trg_n] at valid_1_rest valid_2_rest
          rw[ih] at valid_1_rest
          cases h : forest_seq_2.get? n with
          |none =>
            simp[h] at valid_1_rest valid_2_rest
          |some f =>
            simp[h] at valid_1_rest valid_2_rest
            let cond_result := valid_1_rest.result
            let cond2_result := valid_2_rest.result
            simp[cond2_result, cond_result]

    /--every forest that occurs in a valid forest-sequence is subforest of the oblivious chase-/
    theorem forest_seq_valid_subset_oblivious_chase {fs: FactSet sig}{trg_seq: PreChaseDerivation fs rs}:
          ∀ forest_seq, forest_seq_valid trg_seq forest_seq -> ∀ n, (forest_seq.get? n).elim True (fun f => f.subforest_of (oblivious_chase fs rs)) := by
        intro forest_seq seq_valid n
        induction n with
        |zero =>
          unfold forest_seq_valid at seq_valid
          cases h: forest_seq.get? 0 with
          |none => simp
          |some f0 =>
            simp only [Option.elim_some]--only[Option.is_none_or_iff]
            --intro f0 fn
            simp only [seq_valid, Option.some.injEq] at h
            rw[← h]
            unfold Forest.subforest_of oblivious_chase labellingFunction FactSet.toForest
            simp only[Subset, Membership.mem]
            intro addr addr_fs
            rw[addr_fs]
            simp
        |succ n ih =>
          cases h: forest_seq.get? (n+1) with
          |none => simp
          |some fn1 =>
            simp
            --intro fn1 fn1_eq
            unfold PreChaseDerivation.forest_seq_valid at seq_valid
            let seq_valid' := And.right seq_valid
            specialize seq_valid' n
            cases trg_n: trg_seq.get? n with
            |none =>
              simp [trg_n, Option.isNone_iff_eq_none] at seq_valid'
              rw[seq_valid'] at h
              simp at h
            |some trg =>
              simp only[trg_n] at seq_valid'
              cases forest_eq: forest_seq.get? (n) with
              |none => simp[forest_eq] at seq_valid'
              |some fn =>
                simp[forest_eq] at seq_valid'
                rcases seq_valid' with ⟨trg_active, after_eq⟩
                simp only [forest_eq, Option.elim_some] at ih
                simp only [h, Option.some.injEq] at after_eq
                rw[after_eq]
                unfold LinearRuleTrigger.active_trigger_apply_resulting_forest
                unfold Forest.subforest_of
                simp only[Subset, Membership.mem]
                intro addr addr_from
                apply Or.elim addr_from
                . unfold Forest.subforest_of at ih
                  simp only [Subset, Membership.mem] at ih
                  specialize ih addr
                  exact ih
                . unfold oblivious_chase
                  intro addr_eq
                  apply Or.elim addr_eq
                  repeat intro addr_eq;simp[addr_eq, LinearRuleTrigger.labellingFunction_trg_apply_is_some]

    end PreChaseDerivation

    /--A chase derivation consists of a Possibly infinite trigger sequence, together with a forest sequence that is valid for the trigger sequence-/
    structure LChaseDerivation(fs: FactSet sig) (rs: LinearRuleSet sig) where
      trigger_seq : PreChaseDerivation fs rs
      forest_seq: PossiblyInfiniteList (Forest fs rs)
      cond : PreChaseDerivation.forest_seq_valid trigger_seq forest_seq

    namespace LChaseDerivation

    /--If the trigger sequence of a chasederivation is defined (Option.isSome) at position n the so is the forest sequence-/
    theorem trg_seq_n_some_then_forest_seq_n_some {fs: FactSet sig} {deriv: LChaseDerivation fs rs} :
        ∀ n, (deriv.trigger_seq.get? n).isSome -> (deriv.forest_seq.get? n).isSome := by
      intro n trg_some
      let c := deriv.cond.right
      unfold PreChaseDerivation.forest_seq_valid at c
      specialize c n
      revert c
      cases trg_eq: deriv.trigger_seq.get? n with
      |none =>
        simp[trg_eq] at trg_some
      |some trg =>
        cases deriv.forest_seq.get? n with
        |none => simp
        |some _ => simp

    /--if the forest sequence is defined (Option.isSome) at position n+1 then the trigger sequence is defined at position n-/
    theorem forest_succc_n_some_then_trg_n_some {fs: FactSet sig} {deriv : LChaseDerivation fs rs} :
        ∀ n, (deriv.forest_seq.get? (n+1)).isSome -> (deriv.trigger_seq.get? n).isSome := by
      intro n f1_some
      let c:= deriv.cond.right n
      cases trg_eq: deriv.trigger_seq.get? n with
      |none =>
        simp only [trg_eq, Option.isNone_iff_eq_none] at c
        simp[c] at f1_some
      |some trg =>
        simp

    /--for every n, the trigger in the trigger sequence at position n (if there is some) is active in the forest of the forest-sequence at position n-/
    theorem trg_n_active {fs: FactSet sig} {deriv: LChaseDerivation fs rs}:
        ∀ n, ∀ trg, (trg_n: trg ∈ deriv.trigger_seq.get? n)
        -> trg.isActive_in_forest ((deriv.forest_seq.get? n).get (by apply trg_seq_n_some_then_forest_seq_n_some; simp only[Option.isSome_iff_exists]; exists trg)) := by
      intro n trg trg_elem
      simp only[Membership.mem] at trg_elem
      let h := deriv.cond.right n
      simp only[trg_elem] at h
      by_cases f_some: (deriv.forest_seq.get? n).isSome
      . simp[Option.isSome_iff_exists] at f_some
        rcases f_some with ⟨f, f_eq⟩
        simp only[f_eq] at h
        simp only[f_eq]
        exact h.active
      . simp only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at f_some
        simp only [f_some, Option.elim_none] at h

    /--/--for every n, the trigger in the trigger sequence at position n (if there is some) appears in the forest of the forest-sequence at position n-/-/
    theorem trg_n_forest_trigger {fs: FactSet sig} {deriv: LChaseDerivation fs rs}:
        ∀ n, ∀ trg, (trg_n: trg ∈ deriv.trigger_seq.get? n)
        -> trg.appears_in_forest ((deriv.forest_seq.get? n).get (by apply trg_seq_n_some_then_forest_seq_n_some; simp only[Option.isSome_iff_exists]; exists trg)) := by
      intro n trg trg_elem
      have trg_active := trg_n_active n trg trg_elem
      unfold LinearRuleTrigger.isActive_in_forest at trg_active
      exact trg_active.left

    /--every forest in the forest sequence is subforest of its successor forest in that sequence-/
    theorem forest_n_subforest_succ {fs: FactSet sig} {deriv: LChaseDerivation fs rs}:
        ∀ n, ∀ f ∈ deriv.forest_seq.get? n, ∀ f2 ∈ deriv.forest_seq.get? (n.succ), f.subforest_of f2 := by
      intro n f f_elem f2 f2_elem
      let cond := deriv.cond.right n
      simp only [Membership.mem] at f_elem f2_elem
      have trg_some : (deriv.trigger_seq.get? n).isSome := by
        rw[forest_succc_n_some_then_trg_n_some]
        simp[f2_elem]
      simp only[Option.isSome_iff_exists] at trg_some
      rcases trg_some with ⟨trg, trg_eq⟩
      simp[trg_eq, f_elem] at cond
      let res := cond.result
      simp only [f2_elem, Option.some.injEq] at res
      rw[res]
      simp[LinearRuleTrigger.forest_subforest_trigger_apply_result]

    /--every forest in the forest sequence is subforest of all its successor forests in that sequence-/
    theorem forest_n_subforest_all_succ {fs:FactSet sig} {deriv: LChaseDerivation fs rs}:
        ∀ n, ∀ f ∈ deriv.forest_seq.get? n, ∀ n2 ≥  n, ∀ f2 ∈ deriv.forest_seq.get? (n2), f.subforest_of f2 := by
      intro n f f_elem n2 n2_gt f2 f2_elem
      simp[ge_iff_le] at n2_gt
      induction diff: n2 - n generalizing n2 f2 with
      |zero =>
        rw[Nat.sub_eq_iff_eq_add n2_gt] at diff
        simp only [Nat.zero_add] at diff
        rw[diff] at f2_elem
        simp only [Option.mem_def] at f_elem f2_elem
        simp only [f2_elem, Option.some.injEq] at f_elem
        simp only[f_elem]
        simp[Forest.subforest_refl]
      |succ k h =>
        rw[Nat.sub_eq_iff_eq_add n2_gt] at diff

        specialize h (n+k)
        simp at h
        simp at f2_elem
        simp only[Nat.add_comm, ← Nat.add_assoc, Nat.add_one] at diff
        rw[diff] at f2_elem
        simp only[Nat.add_succ] at f2_elem
        have some_g : ∃ g, deriv.forest_seq.get? (n+k) = some g := by
          simp[← Option.isSome_iff_exists]

          simp[Option.isSome_iff_ne_none]
          false_or_by_contra
          rename_i fk_none
          --simp only[Nat.add_succ] at f2_elem
          simp [PossiblyInfiniteList.no_holes' (n+k) fk_none] at f2_elem
        rcases some_g with ⟨g, g_eq⟩
        specialize h g g_eq
        have g_sub: g.subforest_of f2 := by apply forest_n_subforest_succ (n+k) g g_eq f2 f2_elem
        simp[Forest.subforest_trans h g_sub]


    /--a chase forest is defined as the union of all forests that occur in the forest sequence of the chase derivation. This is also a forest.-/
    def chaseForest {fs : FactSet sig} (deriv : LChaseDerivation fs rs) : Forest fs rs where
      f := fun addr => ∃ forest, addr ∈ forest.f ∧ forest ∈  (deriv.forest_seq)
      fs_contained := by
        intro fact fact_mem
        exists {initialAtom := ⟨fact, fact_mem⟩, path := []}
        constructor
        . exists fs.toForest
          constructor
          . unfold FactSet.toForest; simp only [Membership.mem]
          . simp only[Membership.mem]; exists 0; rw[← PossiblyInfiniteList.get?]; simp[deriv.cond.left]
        . simp
      isPrefixClosed := by
        intro addr addr_mem
        rcases addr_mem with ⟨forest, addr_mem⟩
        let h:=forest.isPrefixClosed
        specialize h addr
        revert h
        unfold immed_prefix_address_in_set
        cases add_p: addr.path with
          |nil => simp
          |cons _ ls =>
            simp only
            intro mem_f
            conv => arg 2;  simp[Membership.mem]
            exists forest
            simp[mem_f,addr_mem]

    /--the chase forest is subforest of the oblivious chase-/
    theorem chaseForest_subforest_obliviousChase {fs: FactSet sig} {deriv: LChaseDerivation fs rs}:
      (chaseForest deriv).subforest_of (oblivious_chase fs rs) := by
      unfold chaseForest
      simp [Membership.mem]
      intro a b
      rcases b with ⟨forest, a_mem, forest_mem⟩
      rcases forest_mem with ⟨n, forest_mem⟩
      rw[← PossiblyInfiniteList.get?]  at forest_mem
      have h := PreChaseDerivation.forest_seq_valid_subset_oblivious_chase (trg_seq := deriv.trigger_seq) deriv.forest_seq deriv.cond n
      rw[forest_mem] at h
      simp at h
      unfold Forest.subforest_of at h
      simp only[Subset] at h
      specialize h a
      simp only[Membership.mem, a_mem] at h
      simp only[Membership.mem, h]

    /--a chase derivation is called oblivous, if its chase forest equals the oblivious chase representation (defined by `oblivious_chase`) -/
    def is_oblivious {fs: FactSet sig} (deriv: LChaseDerivation fs rs) : Prop :=
      chaseForest deriv = oblivious_chase fs rs

    /--In a chase derivation, the trigger at position n in the trigger sequence is not blocked in forest at position n (in the forest sequence), if there doesn't exist a blocking team for the trigger in that forest. -/
    def trg_n_not_blocked_in_forest {fs: FactSet sig} (n: Nat) (deriv: LChaseDerivation fs rs): Prop :=
      (trgn_some: (deriv.trigger_seq.get? n).isSome) ->
      have fn_some : (deriv.forest_seq.get? n).isSome := by
        apply trg_seq_n_some_then_forest_seq_n_some
        exact trgn_some
      have fn_sub: ((deriv.forest_seq.get? n).get fn_some).subforest_of (oblivious_chase fs rs) := by
        have h := PreChaseDerivation.forest_seq_valid_subset_oblivious_chase (trg_seq := deriv.trigger_seq) deriv.forest_seq deriv.cond n
        simp only [Option.isSome_iff_exists] at fn_some
        rcases fn_some with ⟨fn', fn_eq⟩
        rw[fn_eq] at h
        simp only [Option.elim_some] at h
        simp only [fn_eq, Option.get_some]
        exact h
      have trg_in_f : ((deriv.trigger_seq.get? n).get trgn_some).appears_in_forest ((deriv.forest_seq.get? n).get fn_some) := by
        simp[Option.isSome_iff_exists] at trgn_some
        rcases trgn_some with ⟨trg, trg_eq⟩
        have trg_in_f := trg_n_forest_trigger n trg trg_eq
        simp[trg_eq]
        exact trg_in_f
      ¬ ∃ b1 b2, LinearRuleTrigger.blockingTeam fn_sub b1 b2 ⟨((deriv.trigger_seq.get? n).get trgn_some), trg_in_f⟩

    /--a chese derivation is called restricted if no trigger of the trigger-sequence is blocked in its corresponding forest-/
    def is_resricted {fs: FactSet sig} (deriv: LChaseDerivation fs rs) : Prop :=
      ∀ n , trg_n_not_blocked_in_forest n deriv

    /--a chase derivation is called fair, if every trigger that is active in the `chaseForest` of that derivation also has a blocking team in the chaseForest-/
    def is_fair {fs: FactSet sig} (deriv: LChaseDerivation fs rs) : Prop :=
      let m := chaseForest deriv
      ∀ trg: LinearRuleTrigger.forest_Trigger m, LinearRuleTrigger.isActive_in_forest trg.val m ->
      ∃ b1 b2, LinearRuleTrigger.blockingTeam (by apply chaseForest_subforest_obliviousChase) b1 b2 trg


    /--Derivation deriv1 is a subsequence of deriv2, if it can be created from deriv2 by dropping 'unneccessary' elements.-/
    def subsequence {fs: FactSet sig} (deriv1 deriv2: LChaseDerivation fs rs) : Prop :=
      ∀ n, ∃ k, ∀ trg ∈ deriv1.trigger_seq.get? n, trg ∈ deriv2.trigger_seq.get? k ∧ ∀ trg2 ∈ deriv1.trigger_seq.drop n, trg2 ∈ deriv2.trigger_seq.drop k
     --können sich Trigger wiederholen? Eigentlich nicht, oder?

    /--A mixed derivation consists of a oblivious chase derivation m, a restricted chase derivation r that is subsequence of m and we additionally have the condition that every trigger of m at position n that also occurs somewhere in r is not blocked in the forest at position n from m-/
    structure mixedDerivation (fs: FactSet sig) (rs: LinearRuleSet sig) where
      m : LChaseDerivation fs rs
      m_obliv : m.is_oblivious ∧ ¬ m.trigger_seq.finite
      r : LChaseDerivation fs rs
      r_restr: r.is_resricted ∧ r.is_fair ∧ ¬ r.trigger_seq.finite
      sub: r.subsequence m
      trg_blocked: ∀ n, ∃ trg, m.trigger_seq.get? n = some trg ∧ trg ∈ r.trigger_seq -> trg_n_not_blocked_in_forest n m


    end LChaseDerivation


end TriggersAndChaseDerivation
