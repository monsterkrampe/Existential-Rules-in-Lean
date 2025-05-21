import ExistentialRules.ChaseSequence.Termination.Basic

-- Gets a fresh element of the type that does not occur in the given list
class GetFreshRepresentant (t : Type u) where
  fresh (l : List t) : { e : t // e ∉ l }

def GetFreshRepresentant.fresh_n {t : Type u} [GetFreshRepresentant t] (l : List t) (n : Nat) :
    { l' : List t // l'.length = n ∧ l'.Nodup ∧ ∀ e ∈ l', e ∉ l } :=
  match n with
  | .zero => ⟨[], by simp⟩
  | .succ n =>
    let rec_res := GetFreshRepresentant.fresh_n l n
    let fresh_e := GetFreshRepresentant.fresh (rec_res.val ++ l)
    ⟨fresh_e.val :: rec_res.val, by
      constructor
      . simp [rec_res.property.left]
      constructor
      . rw [List.nodup_cons]
        constructor
        . intro contra
          apply fresh_e.property
          rw [List.mem_append]
          apply Or.inl
          exact contra
        . exact rec_res.property.right.left
      . intro e e_mem
        rw [List.mem_cons] at e_mem
        cases e_mem with
        | inr e_mem => apply rec_res.property.right.right; exact e_mem
        | inl e_mem =>
          intro contra
          apply fresh_e.property
          rw [List.mem_append]
          apply Or.inr
          rw [e_mem] at contra
          exact contra
    ⟩

-- Just using Nat as an example / proof of concept here
def Nat.fresh (l : List Nat) : { n : Nat // n ∉ l} :=
  ⟨(l.max?.getD 0).succ, by
    intro contra
    have le : (l.max?.getD 0).succ ≤ l.max?.getD 0 := List.le_max?_getD_of_mem contra
    rw [Nat.succ_le] at le
    simp at le
  ⟩

instance : GetFreshRepresentant Nat where
  fresh := Nat.fresh

#eval GetFreshRepresentant.fresh_n [2,27,6,3] 5


structure RuleList (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
  rules : List (Rule sig)
  id_unique : ∀ r1 r2, r1 ∈ rules ∧ r2 ∈ rules ∧ r1.id = r2.id -> r1 = r2


variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]


def RuleList.get_by_id (rl : RuleList sig) (id : Nat) (id_mem : ∃ r ∈ rl.rules, r.id = id) : Rule sig :=
  (rl.rules.find? (fun r => r.id = id)).get (by simp [id_mem])

theorem RuleList.get_by_id_self (rl : RuleList sig) (r : Rule sig) (mem : r ∈ rl.rules) : rl.get_by_id r.id (by exists r) = r := by
  apply rl.id_unique
  constructor
  . apply List.get_find?_mem
  constructor
  . exact mem
  . unfold get_by_id
    have eq : rl.rules.find? (fun r' => r'.id = r.id) = some ((rl.rules.find? (fun r' => r'.id = r.id)).get (by rw [List.find?_isSome]; exists r; constructor; exact mem; simp)) := by simp
    apply of_decide_eq_true
    apply List.find?_some eq

def SkolemFS.ruleId_valid (sfs : SkolemFS sig) (rl : RuleList sig) : Prop :=
  ∃ r ∈ rl.rules, r.id = sfs.ruleId

def SkolemFS.disjunctIndex_valid (sfs : SkolemFS sig) (rl : RuleList sig) (ruleId_valid : sfs.ruleId_valid rl) : Prop :=
  sfs.disjunctIndex < (rl.get_by_id sfs.ruleId ruleId_valid).head.length

def SkolemFS.arity_valid (sfs : SkolemFS sig) (rl : RuleList sig) (ruleId_valid : sfs.ruleId_valid rl) : Prop :=
  sfs.arity = (rl.get_by_id sfs.ruleId ruleId_valid).frontier.length

mutual

  def PreGroundTerm.skolem_ruleIds_valid (rl : RuleList sig) : FiniteTree (SkolemFS sig) sig.C -> Prop
  | .leaf _ => True
  | .inner func ts => func.ruleId_valid rl ∧ PreGroundTerm.skolem_ruleIds_valid_list rl ts

  def PreGroundTerm.skolem_ruleIds_valid_list (rl : RuleList sig) : FiniteTreeList (SkolemFS sig) sig.C -> Prop
  | .nil => True
  | .cons t ts => PreGroundTerm.skolem_ruleIds_valid rl t ∧ PreGroundTerm.skolem_ruleIds_valid_list rl ts

end

mutual

  def PreGroundTerm.skolem_disjIdx_valid
      (rl : RuleList sig)
      (term : FiniteTree (SkolemFS sig) sig.C)
      (term_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid rl term) : Prop :=
    match term with
    | .leaf _ => True
    | .inner func ts => func.disjunctIndex_valid rl term_ruleIds_valid.left ∧ PreGroundTerm.skolem_disjIdx_valid_list rl ts term_ruleIds_valid.right

  def PreGroundTerm.skolem_disjIdx_valid_list
      (rl : RuleList sig)
      (terms : FiniteTreeList (SkolemFS sig) sig.C)
      (terms_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid_list rl terms) : Prop :=
    match terms with
    | .nil => True
    | .cons t ts => PreGroundTerm.skolem_disjIdx_valid rl t terms_ruleIds_valid.left ∧ PreGroundTerm.skolem_disjIdx_valid_list rl ts terms_ruleIds_valid.right

end

mutual

  def PreGroundTerm.skolem_rule_arity_valid
      (rl : RuleList sig)
      (term : FiniteTree (SkolemFS sig) sig.C)
      (term_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid rl term) : Prop :=
    match term with
    | .leaf _ => True
    | .inner func ts => func.arity_valid rl term_ruleIds_valid.left ∧ PreGroundTerm.skolem_rule_arity_valid_list rl ts term_ruleIds_valid.right

  def PreGroundTerm.skolem_rule_arity_valid_list
      (rl : RuleList sig)
      (terms : FiniteTreeList (SkolemFS sig) sig.C)
      (terms_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid_list rl terms) : Prop :=
    match terms with
    | .nil => True
    | .cons t ts => PreGroundTerm.skolem_rule_arity_valid rl t terms_ruleIds_valid.left ∧ PreGroundTerm.skolem_rule_arity_valid_list rl ts terms_ruleIds_valid.right

end

def GroundTerm.skolem_ruleIds_valid (rl : RuleList sig) (term : GroundTerm sig) : Prop := PreGroundTerm.skolem_ruleIds_valid rl term.val
def GroundTerm.skolem_disjIdx_valid (rl : RuleList sig) (term : GroundTerm sig) (term_ruleIds_valid : term.skolem_ruleIds_valid rl) : Prop :=
  PreGroundTerm.skolem_disjIdx_valid rl term.val term_ruleIds_valid
def GroundTerm.skolem_rule_arity_valid (rl : RuleList sig) (term : GroundTerm sig) (term_ruleIds_valid : term.skolem_ruleIds_valid rl) : Prop :=
  PreGroundTerm.skolem_rule_arity_valid rl term.val term_ruleIds_valid

theorem GroundTerm.skolem_ruleIds_valid_const (rl : RuleList sig) (c : sig.C) : (GroundTerm.const c).skolem_ruleIds_valid rl := by
  simp [skolem_ruleIds_valid, PreGroundTerm.skolem_ruleIds_valid, GroundTerm.const]
theorem GroundTerm.skolem_disjIdx_valid_const (rl : RuleList sig) (c : sig.C) : (GroundTerm.const c).skolem_disjIdx_valid rl (skolem_ruleIds_valid_const rl c) := by
  simp [skolem_disjIdx_valid, PreGroundTerm.skolem_disjIdx_valid, GroundTerm.const]
theorem GroundTerm.skolem_rule_arity_valid_const (rl : RuleList sig) (c : sig.C) : (GroundTerm.const c).skolem_rule_arity_valid rl (skolem_ruleIds_valid_const rl c) := by
  simp [skolem_rule_arity_valid, PreGroundTerm.skolem_rule_arity_valid, GroundTerm.const]

mutual

  def PreGroundTerm.backtrackFacts
      [GetFreshRepresentant sig.C]
      [Inhabited sig.C]
      (rl : RuleList sig)
      (term : FiniteTree (SkolemFS sig) sig.C)
      (term_arity_ok : PreGroundTerm.arity_ok term)
      (term_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid rl term)
      (term_disjIdx_valid : PreGroundTerm.skolem_disjIdx_valid rl term term_ruleIds_valid)
      (term_rule_arity_valid : PreGroundTerm.skolem_rule_arity_valid rl term term_ruleIds_valid) :
      -- we return the backtracked facts and all the constants that have already been used (as a basis for picking fresh ones)
      (List (Fact sig)) × (List sig.C) :=
    match term with
    | .leaf c => ([], [c])
    | .inner func ts =>
      let recursive_result := PreGroundTerm.backtrackFacts_list rl ts (Bool.and_eq_true_iff.mp term_arity_ok).right term_ruleIds_valid.right term_disjIdx_valid.right term_rule_arity_valid.right

      let rule : Rule sig := rl.get_by_id func.ruleId term_ruleIds_valid.left
      let pure_body_vars := rule.body.vars.filter (fun x => x ∉ rule.frontier)
      let fresh_consts_for_pure_body_vars := GetFreshRepresentant.fresh_n recursive_result.snd pure_body_vars.length

      let subs : GroundSubstitution sig := fun x =>
        if mem : x ∈ rule.frontier
        then
          let idx := rule.frontier.idxOf x
          have : idx < ts.toList.length := by
            have := LawfulBEq.eq_of_beq (Bool.and_eq_true_iff.mp term_arity_ok).left
            rw [this, term_rule_arity_valid.left]
            apply List.idxOf_lt_length
            exact mem
          ⟨ts.toList[idx], by
            have := (PreGroundTerm.arity_ok_list_iff_arity_ok_each_mem ts).mpr (Bool.and_eq_true_iff.mp term_arity_ok).right
            apply this
            simp
          ⟩
        else
          if mem : x ∈ pure_body_vars
          then
            let idx := pure_body_vars.idxOf x
            have : idx < fresh_consts_for_pure_body_vars.val.length := by
              rw [fresh_consts_for_pure_body_vars.property.left]
              apply List.idxOf_lt_length
              exact mem
            GroundTerm.const fresh_consts_for_pure_body_vars.val[idx]
          else
            -- it should not matter what we return here so we also do NOT need to make sure that this does not collide with other constants
            GroundTerm.const default

      let trg : PreTrigger sig := { rule, subs }
      let disjIdx := func.disjunctIndex
      have : disjIdx < trg.mapped_head.length := by rw [PreTrigger.length_mapped_head]; exact term_disjIdx_valid.left

      ((trg.mapped_body ++ trg.mapped_head[disjIdx]) ++ recursive_result.fst, recursive_result.snd ++ fresh_consts_for_pure_body_vars)

  def PreGroundTerm.backtrackFacts_list
      [GetFreshRepresentant sig.C]
      [Inhabited sig.C]
      (rl : RuleList sig)
      (terms : FiniteTreeList (SkolemFS sig) sig.C)
      (terms_arity_ok : PreGroundTerm.arity_ok_list terms)
      (terms_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid_list rl terms)
      (terms_disjIdx_valid : PreGroundTerm.skolem_disjIdx_valid_list rl terms terms_ruleIds_valid)
      (terms_rule_arity_valid : PreGroundTerm.skolem_rule_arity_valid_list rl terms terms_ruleIds_valid) : (List (Fact sig)) × (List sig.C) :=
    match terms with
    | .nil => ([], [])
    | .cons t ts =>
      let t_res := PreGroundTerm.backtrackFacts rl t (Bool.and_eq_true_iff.mp terms_arity_ok).left terms_ruleIds_valid.left terms_disjIdx_valid.left terms_rule_arity_valid.left
      let ts_res := PreGroundTerm.backtrackFacts_list rl ts (Bool.and_eq_true_iff.mp terms_arity_ok).right terms_ruleIds_valid.right terms_disjIdx_valid.right terms_rule_arity_valid.right
      (t_res.fst ++ ts_res.fst, t_res.snd ++ ts_res.snd)

end

def GroundTerm.backtrackFacts
    [GetFreshRepresentant sig.C]
    [Inhabited sig.C]
    (rl : RuleList sig)
    (term : GroundTerm sig)
    (term_ruleIds_valid : term.skolem_ruleIds_valid rl)
    (term_disjIdx_valid : term.skolem_disjIdx_valid rl term_ruleIds_valid)
    (term_rule_arity_valid : term.skolem_rule_arity_valid rl term_ruleIds_valid) : List (Fact sig) :=
  (PreGroundTerm.backtrackFacts rl term.val term.property term_ruleIds_valid term_disjIdx_valid term_rule_arity_valid).fst



def PreTrigger.skolem_ruleIds_valid (rl : RuleList sig) (trg : PreTrigger sig) : Prop := ∀ t ∈ trg.mapped_body.flatMap Fact.terms, t.skolem_ruleIds_valid rl
def PreTrigger.skolem_disjIdx_valid (rl : RuleList sig) (trg : PreTrigger sig) (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl) : Prop :=
  ∀ t, (h : t ∈ trg.mapped_body.flatMap Fact.terms) -> t.skolem_disjIdx_valid rl (trg_ruleIds_valid t h)
def PreTrigger.skolem_rule_arity_valid (rl : RuleList sig) (trg : PreTrigger sig) (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl) : Prop :=
  ∀ t, (h : t ∈ trg.mapped_body.flatMap Fact.terms) -> t.skolem_rule_arity_valid rl (trg_ruleIds_valid t h)

-- TODO: extract this result
theorem List.getElem_idxOf_of_mem [BEq α] [LawfulBEq α] {l : List α} {e : α} (mem : e ∈ l) : l[l.idxOf e]'(by apply List.idxOf_lt_length; exact mem) = e := by
  induction l with
  | nil => simp at mem
  | cons hd tl ih =>
    unfold List.idxOf
    unfold List.findIdx
    unfold List.findIdx.go
    cases Decidable.em (hd == e) with
    | inl eq => simp only [eq, cond_true]; rw [List.getElem_cons_zero]; apply LawfulBEq.eq_of_beq eq
    | inr neq =>
      simp only [neq, cond_false]
      simp only [List.findIdx_cons.findIdx_go_succ]
      rw [List.getElem_cons_succ]
      apply ih
      rw [List.mem_cons] at mem
      cases mem with
      | inl mem => rw [mem] at neq; simp at neq
      | inr mem => exact mem

theorem PreTrigger.skolem_ruleIds_remain_valid_in_head (rl : RuleList sig) (trg : PreTrigger sig) (rule_mem : trg.rule ∈ rl.rules) (body_valid : trg.skolem_ruleIds_valid rl) :
    ∀ t ∈ trg.mapped_head.flatten.flatMap Fact.terms, t.skolem_ruleIds_valid rl := by
  intro t t_mem
  rw [List.mem_flatMap] at t_mem
  rcases t_mem with ⟨f, f_mem, t_mem⟩
  rw [List.mem_flatten] at f_mem
  rcases f_mem with ⟨l, l_mem, f_mem⟩
  let disj_idx : Fin trg.mapped_head.length := ⟨trg.mapped_head.idxOf l, by apply List.idxOf_lt_length; exact l_mem⟩
  let voc : VarOrConst sig := trg.var_or_const_for_result_term disj_idx (by rw [List.getElem_idxOf_of_mem l_mem]; exact f_mem) t_mem
  rw [← trg.apply_on_var_or_const_for_result_term_is_term disj_idx (by rw [List.getElem_idxOf_of_mem l_mem]; exact f_mem) t_mem]
  cases eq : voc with
  | const c =>
    unfold voc at eq
    rw [eq, trg.apply_to_var_or_const_for_const disj_idx.val _]
    apply GroundTerm.skolem_ruleIds_valid_const
  | var v =>
    cases Decidable.em (v ∈ trg.rule.frontier) with
    | inl mem_frontier =>
      unfold voc at eq
      rw [eq, trg.apply_to_var_or_const_frontier_var disj_idx.val _ mem_frontier]
      apply body_valid
      rcases trg.rule.frontier_occurs_in_body v mem_frontier with ⟨a, a_mem, v_mem⟩
      rw [List.mem_flatMap]
      exists trg.subs.apply_function_free_atom a
      constructor
      . apply List.mem_map_of_mem; exact a_mem
      . unfold GroundSubstitution.apply_function_free_atom
        rw [List.mem_map]
        exists VarOrConst.var v
    | inr mem_frontier =>
      unfold voc at eq
      rw [eq, trg.apply_to_var_or_const_non_frontier_var disj_idx.val _ mem_frontier]
      simp only [GroundTerm.skolem_ruleIds_valid, PreGroundTerm.skolem_ruleIds_valid, PreTrigger.functional_term_for_var, GroundTerm.func]
      constructor
      . exists trg.rule
      . have : ∀ (l : List sig.V), (∀ e ∈ l, e ∈ trg.rule.frontier) -> PreGroundTerm.skolem_ruleIds_valid_list rl (FiniteTreeList.fromList (l.map trg.subs).unattach) := by
          intro l
          induction l with
          | nil => intro _; simp [FiniteTreeList.fromList, PreGroundTerm.skolem_ruleIds_valid_list]
          | cons hd tl ih =>
            intro mem_frontier
            rw [List.map_cons]
            rw [List.unattach_cons]
            unfold FiniteTreeList.fromList
            unfold PreGroundTerm.skolem_ruleIds_valid_list
            constructor
            . apply body_valid
              rcases trg.rule.frontier_occurs_in_body hd (by apply mem_frontier; simp) with ⟨a, a_mem, hd_mem⟩
              rw [List.mem_flatMap]
              exists trg.subs.apply_function_free_atom a
              constructor
              . apply List.mem_map_of_mem; exact a_mem
              . unfold GroundSubstitution.apply_function_free_atom
                rw [List.mem_map]
                exists VarOrConst.var hd
            . apply ih; intro e e_mem; apply mem_frontier; simp [e_mem]
        apply this
        simp

theorem PreTrigger.skolem_disjIdx_remains_valid_in_head
    (rl : RuleList sig)
    (trg : PreTrigger sig)
    (rule_mem : trg.rule ∈ rl.rules)
    (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl)
    (body_valid : trg.skolem_disjIdx_valid rl trg_ruleIds_valid) :
    ∀ t, (t_mem : t ∈ trg.mapped_head.flatten.flatMap Fact.terms) -> t.skolem_disjIdx_valid rl (trg.skolem_ruleIds_remain_valid_in_head rl rule_mem trg_ruleIds_valid t t_mem) := by
  intro t t_mem
  rw [List.mem_flatMap] at t_mem
  rcases t_mem with ⟨f, f_mem, t_mem⟩
  rw [List.mem_flatten] at f_mem
  rcases f_mem with ⟨l, l_mem, f_mem⟩
  let disj_idx : Fin trg.mapped_head.length := ⟨trg.mapped_head.idxOf l, by apply List.idxOf_lt_length; exact l_mem⟩

  cases t with
  | const c => apply GroundTerm.skolem_disjIdx_valid_const
  | func fs ts arity_ok =>
    cases Decidable.em ((GroundTerm.func fs ts arity_ok) ∈ trg.rule.frontier.map trg.subs) with
    | inl t_mem_frontier =>
      rw [List.mem_map] at t_mem_frontier
      rcases t_mem_frontier with ⟨v, v_mem, v_eq⟩
      apply body_valid
      rcases trg.rule.frontier_occurs_in_body v v_mem with ⟨a, a_mem, v_mem⟩
      rw [List.mem_flatMap]
      exists trg.subs.apply_function_free_atom a
      constructor
      . apply List.mem_map_of_mem; exact a_mem
      . unfold GroundSubstitution.apply_function_free_atom
        rw [List.mem_map]
        exists VarOrConst.var v
    | inr t_mem_frontier =>
      let voc : VarOrConst sig := trg.var_or_const_for_result_term disj_idx (by rw [List.getElem_idxOf_of_mem l_mem]; exact f_mem) t_mem
      have voc_eq := trg.apply_on_var_or_const_for_result_term_is_term disj_idx (by rw [List.getElem_idxOf_of_mem l_mem]; exact f_mem) t_mem
      cases eq : voc with
      | const c =>
        unfold voc at eq
        rw [eq, trg.apply_to_var_or_const_for_const disj_idx.val _] at voc_eq
        simp [GroundTerm.const, GroundTerm.func] at voc_eq
      | var v =>
        unfold voc at eq
        rw [eq] at voc_eq
        cases Decidable.em (v ∈ trg.rule.frontier) with
        | inl v_mem_frontier =>
          rw [trg.apply_to_var_or_const_frontier_var disj_idx.val _ v_mem_frontier] at voc_eq
          apply False.elim
          apply t_mem_frontier
          rw [List.mem_map]
          exists v
        | inr v_mem_frontier =>
          rw [trg.apply_to_var_or_const_non_frontier_var disj_idx.val _ v_mem_frontier] at voc_eq
          unfold PreTrigger.functional_term_for_var at voc_eq
          unfold GroundTerm.func at voc_eq
          rw [Subtype.mk.injEq, FiniteTree.inner.injEq] at voc_eq
          simp only [GroundTerm.skolem_disjIdx_valid, PreGroundTerm.skolem_disjIdx_valid, GroundTerm.func]
          constructor
          . have voc_eq := voc_eq.left
            unfold SkolemFS.disjunctIndex_valid
            simp only [← voc_eq]
            rw [rl.get_by_id_self _ rule_mem]
            rw [← trg.length_mapped_head]
            exact disj_idx.isLt
          . have voc_eq := voc_eq.right

            have : ∀ (l : List sig.V), (∀ e ∈ l, e ∈ trg.rule.frontier) -> PreGroundTerm.skolem_ruleIds_valid_list rl (FiniteTreeList.fromList (l.map trg.subs).unattach) := by
              intro l
              induction l with
              | nil => intro _; simp [FiniteTreeList.fromList, PreGroundTerm.skolem_ruleIds_valid_list]
              | cons hd tl ih =>
                intro mem_frontier
                simp only [List.map_cons]
                simp only [List.unattach_cons]
                unfold FiniteTreeList.fromList
                unfold PreGroundTerm.skolem_ruleIds_valid_list
                constructor
                . apply trg_ruleIds_valid
                  rcases trg.rule.frontier_occurs_in_body hd (by apply mem_frontier; simp) with ⟨a, a_mem, hd_mem⟩
                  rw [List.mem_flatMap]
                  exists trg.subs.apply_function_free_atom a
                  constructor
                  . apply List.mem_map_of_mem; exact a_mem
                  . unfold GroundSubstitution.apply_function_free_atom
                    rw [List.mem_map]
                    exists VarOrConst.var hd
                . apply ih; intro e e_mem; apply mem_frontier; simp [e_mem]

            have : ∀ (l : List sig.V), (h : ∀ e ∈ l, e ∈ trg.rule.frontier) -> PreGroundTerm.skolem_disjIdx_valid_list rl (FiniteTreeList.fromList (l.map trg.subs).unattach) (this l h) := by
              intro l
              induction l with
              | nil => intro _; simp [FiniteTreeList.fromList, PreGroundTerm.skolem_disjIdx_valid_list]
              | cons hd tl ih =>
                intro mem_frontier
                simp only [List.map_cons]
                simp only [List.unattach_cons]
                unfold FiniteTreeList.fromList
                unfold PreGroundTerm.skolem_disjIdx_valid_list
                constructor
                . apply body_valid
                  rcases trg.rule.frontier_occurs_in_body hd (by apply mem_frontier; simp) with ⟨a, a_mem, hd_mem⟩
                  rw [List.mem_flatMap]
                  exists trg.subs.apply_function_free_atom a
                  constructor
                  . apply List.mem_map_of_mem; exact a_mem
                  . unfold GroundSubstitution.apply_function_free_atom
                    rw [List.mem_map]
                    exists VarOrConst.var hd
                . apply ih; intro e e_mem; apply mem_frontier; simp [e_mem]

            rw [← FiniteTreeList.eqIffFromListEq] at voc_eq
            simp only [← voc_eq]
            apply this
            simp

theorem PreTrigger.skolem_rule_arity_remains_valid_in_head
    (rl : RuleList sig)
    (trg : PreTrigger sig)
    (rule_mem : trg.rule ∈ rl.rules)
    (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl)
    (body_valid : trg.skolem_rule_arity_valid rl trg_ruleIds_valid) :
    ∀ t, (t_mem : t ∈ trg.mapped_head.flatten.flatMap Fact.terms) -> t.skolem_rule_arity_valid rl (trg.skolem_ruleIds_remain_valid_in_head rl rule_mem trg_ruleIds_valid t t_mem) := by
  intro t t_mem
  rw [List.mem_flatMap] at t_mem
  rcases t_mem with ⟨f, f_mem, t_mem⟩
  rw [List.mem_flatten] at f_mem
  rcases f_mem with ⟨l, l_mem, f_mem⟩
  let disj_idx : Fin trg.mapped_head.length := ⟨trg.mapped_head.idxOf l, by apply List.idxOf_lt_length; exact l_mem⟩

  cases t with
  | const c => apply GroundTerm.skolem_rule_arity_valid_const
  | func fs ts arity_ok =>
    cases Decidable.em ((GroundTerm.func fs ts arity_ok) ∈ trg.rule.frontier.map trg.subs) with
    | inl t_mem_frontier =>
      rw [List.mem_map] at t_mem_frontier
      rcases t_mem_frontier with ⟨v, v_mem, v_eq⟩
      apply body_valid
      rcases trg.rule.frontier_occurs_in_body v v_mem with ⟨a, a_mem, v_mem⟩
      rw [List.mem_flatMap]
      exists trg.subs.apply_function_free_atom a
      constructor
      . apply List.mem_map_of_mem; exact a_mem
      . unfold GroundSubstitution.apply_function_free_atom
        rw [List.mem_map]
        exists VarOrConst.var v
    | inr t_mem_frontier =>
      let voc : VarOrConst sig := trg.var_or_const_for_result_term disj_idx (by rw [List.getElem_idxOf_of_mem l_mem]; exact f_mem) t_mem
      have voc_eq := trg.apply_on_var_or_const_for_result_term_is_term disj_idx (by rw [List.getElem_idxOf_of_mem l_mem]; exact f_mem) t_mem
      cases eq : voc with
      | const c =>
        unfold voc at eq
        rw [eq, trg.apply_to_var_or_const_for_const disj_idx.val _] at voc_eq
        simp [GroundTerm.const, GroundTerm.func] at voc_eq
      | var v =>
        unfold voc at eq
        rw [eq] at voc_eq
        cases Decidable.em (v ∈ trg.rule.frontier) with
        | inl v_mem_frontier =>
          rw [trg.apply_to_var_or_const_frontier_var disj_idx.val _ v_mem_frontier] at voc_eq
          apply False.elim
          apply t_mem_frontier
          rw [List.mem_map]
          exists v
        | inr v_mem_frontier =>
          rw [trg.apply_to_var_or_const_non_frontier_var disj_idx.val _ v_mem_frontier] at voc_eq
          unfold PreTrigger.functional_term_for_var at voc_eq
          unfold GroundTerm.func at voc_eq
          rw [Subtype.mk.injEq, FiniteTree.inner.injEq] at voc_eq
          simp only [GroundTerm.skolem_rule_arity_valid, PreGroundTerm.skolem_rule_arity_valid, GroundTerm.func]
          constructor
          . have voc_eq := voc_eq.left
            unfold SkolemFS.arity_valid
            simp only [← voc_eq]
            rw [rl.get_by_id_self _ rule_mem]
          . have voc_eq := voc_eq.right

            have : ∀ (l : List sig.V), (∀ e ∈ l, e ∈ trg.rule.frontier) -> PreGroundTerm.skolem_ruleIds_valid_list rl (FiniteTreeList.fromList (l.map trg.subs).unattach) := by
              intro l
              induction l with
              | nil => intro _; simp [FiniteTreeList.fromList, PreGroundTerm.skolem_ruleIds_valid_list]
              | cons hd tl ih =>
                intro mem_frontier
                simp only [List.map_cons]
                simp only [List.unattach_cons]
                unfold FiniteTreeList.fromList
                unfold PreGroundTerm.skolem_ruleIds_valid_list
                constructor
                . apply trg_ruleIds_valid
                  rcases trg.rule.frontier_occurs_in_body hd (by apply mem_frontier; simp) with ⟨a, a_mem, hd_mem⟩
                  rw [List.mem_flatMap]
                  exists trg.subs.apply_function_free_atom a
                  constructor
                  . apply List.mem_map_of_mem; exact a_mem
                  . unfold GroundSubstitution.apply_function_free_atom
                    rw [List.mem_map]
                    exists VarOrConst.var hd
                . apply ih; intro e e_mem; apply mem_frontier; simp [e_mem]

            have : ∀ (l : List sig.V), (h : ∀ e ∈ l, e ∈ trg.rule.frontier) -> PreGroundTerm.skolem_rule_arity_valid_list rl (FiniteTreeList.fromList (l.map trg.subs).unattach) (this l h) := by
              intro l
              induction l with
              | nil => intro _; simp [FiniteTreeList.fromList, PreGroundTerm.skolem_rule_arity_valid_list]
              | cons hd tl ih =>
                intro mem_frontier
                simp only [List.map_cons]
                simp only [List.unattach_cons]
                unfold FiniteTreeList.fromList
                unfold PreGroundTerm.skolem_rule_arity_valid_list
                constructor
                . apply body_valid
                  rcases trg.rule.frontier_occurs_in_body hd (by apply mem_frontier; simp) with ⟨a, a_mem, hd_mem⟩
                  rw [List.mem_flatMap]
                  exists trg.subs.apply_function_free_atom a
                  constructor
                  . apply List.mem_map_of_mem; exact a_mem
                  . unfold GroundSubstitution.apply_function_free_atom
                    rw [List.mem_map]
                    exists VarOrConst.var hd
                . apply ih; intro e e_mem; apply mem_frontier; simp [e_mem]

            rw [← FiniteTreeList.eqIffFromListEq] at voc_eq
            simp only [← voc_eq]
            apply this
            simp


def PreTrigger.backtrackFacts
    [GetFreshRepresentant sig.C]
    [Inhabited sig.C]
    (rl : RuleList sig)
    (trg : PreTrigger sig)
    (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl)
    (trg_disjIdx_valid : trg.skolem_disjIdx_valid rl trg_ruleIds_valid)
    (trg_rule_arity_valid : trg.skolem_rule_arity_valid rl trg_ruleIds_valid) : List (Fact sig) :=
  trg.mapped_body ++ ((trg.mapped_body.flatMap Fact.terms).attach.flatMap (fun ⟨t, h⟩ => t.backtrackFacts rl (trg_ruleIds_valid t h) (trg_disjIdx_valid t h) (trg_rule_arity_valid t h)))

