import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.Basic

import ExistentialRules.Models.Basic
import ExistentialRules.Triggers.RTrigger

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

structure ChaseNode (obs : ObsoletenessCondition sig) (rules : RuleSet sig) where
  facts : { fs : FactSet sig // fs.finite }
  -- the origin is none only for the database
  origin : Option ((trg : RTrigger (obs : LaxObsoletenessCondition sig) rules) × Fin trg.val.mapped_head.length)
  facts_contain_origin_result : origin.is_none_or (fun origin => origin.fst.val.mapped_head[origin.snd.val].toSet ⊆ facts)

namespace ChaseNode

  def origin_result {obs : ObsoletenessCondition sig} (node : ChaseNode obs rules) (isSome : node.origin.isSome) :
      List (Fact sig) :=
    let origin := node.origin.get isSome
    origin.fst.val.mapped_head[origin.snd.val]

end ChaseNode

def exists_trigger_opt_fs (obs : ObsoletenessCondition sig) (rules : RuleSet sig) (before : ChaseNode obs rules) (after : Option (ChaseNode obs rules)) : Prop :=
  ∃ trg : (RTrigger (obs : LaxObsoletenessCondition sig) rules), trg.val.active before.facts ∧ ∃ i, some {
    facts := ⟨
      before.facts ∪ (trg.val.mapped_head[i.val]'(i.isLt)).toSet,
      by
        rcases before.facts.property with ⟨l_before, _, l_eq⟩
        let new_list := (l_before ++ trg.val.mapped_head[i.val]).eraseDupsKeepRight
        exists new_list
        constructor
        . apply List.nodup_eraseDupsKeepRight
        . intro e
          unfold new_list
          rw [List.mem_eraseDupsKeepRight, List.mem_append]
          rw [l_eq]
          simp only [Union.union, List.mem_toSet]
          rfl
    ⟩
    origin := some ⟨trg, i⟩
    facts_contain_origin_result := by simp [Option.is_none_or]; apply Set.subset_union_of_subset_right; apply Set.subset_refl
  } = after

def exists_trigger_list_condition (obs : ObsoletenessCondition sig) (rules : RuleSet sig) (before : ChaseNode obs rules) (after : List (ChaseNode obs rules)) (trg : RTrigger obs rules) : Prop :=
  trg.val.active before.facts ∧ trg.val.mapped_head.zipIdx_with_lt.attach.map (fun ⟨⟨head, i⟩, h⟩ => {
    facts := ⟨
      before.facts ∪ head.toSet,
      by
        rw [List.mk_mem_zipIdx_with_lt_iff_getElem] at h
        rcases before.facts.property with ⟨l_before, _, l_eq⟩
        let new_list := (l_before ++ trg.val.mapped_head[i.val]).eraseDupsKeepRight
        exists new_list
        constructor
        . apply List.nodup_eraseDupsKeepRight
        . intro e
          unfold new_list
          rw [List.mem_eraseDupsKeepRight, List.mem_append]
          rw [l_eq]
          simp only [Union.union, List.mem_toSet]
          rw [← h]
          rfl
    ⟩
    origin := some ⟨trg, i⟩
    facts_contain_origin_result := by
      have : head = trg.val.mapped_head[i.val] := by rw [List.mk_mem_zipIdx_with_lt_iff_getElem] at h; rw [h]
      simp only [Option.is_none_or]
      apply Set.subset_union_of_subset_right
      rw [this]
      apply Set.subset_refl
  }) = after

def exists_trigger_list (obs : ObsoletenessCondition sig) (rules : RuleSet sig) (before : ChaseNode obs rules) (after : List (ChaseNode obs rules)) : Prop :=
  ∃ trg : (RTrigger obs rules), exists_trigger_list_condition obs rules before after trg

def not_exists_trigger_opt_fs (obs : ObsoletenessCondition sig) (rules : RuleSet sig) (before : ChaseNode obs rules) (after : Option (ChaseNode obs rules)) : Prop :=
  ¬(∃ trg : (RTrigger obs rules), trg.val.active before.facts) ∧ after = none

def not_exists_trigger_list (obs : ObsoletenessCondition sig) (rules : RuleSet sig) (before : ChaseNode obs rules) (after : List (ChaseNode obs rules)) : Prop :=
  ¬(∃ trg : (RTrigger obs rules), trg.val.active before.facts) ∧ after = []

structure ChaseBranch (obs : ObsoletenessCondition sig) (kb : KnowledgeBase sig) where
  branch : PossiblyInfiniteList (ChaseNode obs kb.rules)
  database_first : branch.head = some {
    facts := (
      let fs := kb.db.toFactSet
      ⟨fs.val, fs.property.left⟩
    ),
    origin := none,
    facts_contain_origin_result := by simp [Option.is_none_or]
  }
  triggers_exist : ∀ n : Nat, (branch.drop n).head.is_none_or (fun before =>
    let after := (branch.drop n).tail.head
    (exists_trigger_opt_fs obs kb.rules before after) ∨
    (not_exists_trigger_opt_fs obs kb.rules before after))
  fairness : ∀ trg : (RTrigger obs kb.rules), ∃ i : Nat, ((branch.drop i).head.is_some_and (fun fs => ¬ trg.val.active fs.facts))
    ∧ (∀ j : Nat, ((branch.drop i).tail.get? j).is_none_or (fun fs => ¬ trg.val.active fs.facts))

namespace ChaseBranch

  variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

  def result (cb : ChaseBranch obs kb) : FactSet sig :=
    fun f => ∃ n : Nat, (cb.branch.get? n).is_some_and (fun fs => f ∈ fs.facts.val)

  theorem predecessor_isSome_of_isSome (cb : ChaseBranch obs kb) (i : Nat) (isSome : (cb.branch.drop i).tail.head.isSome) :
      (cb.branch.drop i).head.isSome := by
    cases eq : (cb.branch.drop i).head with
    | none =>
      have : (cb.branch.drop i).tail.head = none := by apply cb.branch.no_holes; exact eq
      simp [this] at isSome
    | some _ => simp

  def prev_node (cb : ChaseBranch obs kb) (i : Nat) (isSome : (cb.branch.drop i).tail.head.isSome) : ChaseNode obs kb.rules :=
    (cb.branch.drop i).head.get (cb.predecessor_isSome_of_isSome i isSome)

  theorem prev_node_eq (cb : ChaseBranch obs kb) (i : Nat) (isSome : (cb.branch.drop i).tail.head.isSome) :
      (cb.branch.drop i).head = some (cb.prev_node i isSome) := by
    simp [prev_node]

  theorem origin_isSome (cb : ChaseBranch obs kb) (i : Nat) {node : ChaseNode obs kb.rules}
      (eq : (cb.branch.drop i).tail.head = some node) : node.origin.isSome := by
    have trg_ex := cb.triggers_exist i
    rw [prev_node_eq _ _ (by simp [eq]), Option.is_none_or] at trg_ex
    cases trg_ex with
    | inl trg_ex =>
      unfold exists_trigger_opt_fs at trg_ex
      rcases trg_ex with ⟨trg, _, disj, trg_eq⟩
      simp only [eq] at trg_eq
      injection trg_eq with trg_eq
      rw [← trg_eq]
      simp
    | inr trg_ex =>
      unfold not_exists_trigger_opt_fs at trg_ex
      simp only [eq] at trg_ex
      simp at trg_ex

  theorem origin_trg_is_active (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : (cb.branch.drop i).tail.head = some node) :
      (node.origin.get (cb.origin_isSome i eq)).fst.val.active (cb.prev_node i (by simp [eq])).facts.val := by
    have trg_ex := cb.triggers_exist i
    rw [prev_node_eq _ _ (by simp [eq]), Option.is_none_or] at trg_ex
    cases trg_ex with
    | inr trg_ex => unfold not_exists_trigger_opt_fs at trg_ex; rw [trg_ex.right] at eq; simp at eq
    | inl trg_ex =>
      unfold exists_trigger_opt_fs at trg_ex
      rcases trg_ex with ⟨trg, trg_active, disj, trg_eq⟩
      simp only [eq] at trg_eq
      injection trg_eq with trg_eq
      simp only [← trg_eq]
      exact trg_active

  theorem origin_trg_result_yields_next_node_facts (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : (cb.branch.drop i).tail.head = some node) :
      node.facts.val = (cb.prev_node i (by simp [eq])).facts.val ∪ (node.origin_result (cb.origin_isSome i eq)).toSet := by
    have trg_ex := cb.triggers_exist i
    rw [prev_node_eq _ _ (by simp [eq]), Option.is_none_or] at trg_ex
    cases trg_ex with
    | inr trg_ex => unfold not_exists_trigger_opt_fs at trg_ex; rw [trg_ex.right] at eq; simp at eq
    | inl trg_ex =>
      unfold exists_trigger_opt_fs at trg_ex
      rcases trg_ex with ⟨trg, trg_active, disj, trg_eq⟩
      simp only [eq] at trg_eq
      injection trg_eq with trg_eq
      simp only [← trg_eq]
      unfold ChaseNode.origin_result
      simp

  theorem stepIsSubsetOfAllFollowing (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : (cb.branch.drop i).head = some node) :
      ∀ j, ((cb.branch.drop i).get? j).is_none_or (fun node2 => node.facts.val ⊆ node2.facts.val) := by
    intro j
    induction j with
    | zero => rw [← PossiblyInfiniteList.head_eq, eq]; simp only [Option.is_none_or]; apply Set.subset_refl
    | succ j ih =>
      rw [Option.is_none_or_iff]
      intro node2 eq2
      let prev_node := (cb.prev_node (i + j) (by rw [PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?_tail, PossiblyInfiniteList.get?_drop]; rw [PossiblyInfiniteList.get?_drop, ← Nat.add_assoc] at eq2; rw [eq2]; simp))
      apply Set.subset_trans (b := prev_node.facts.val)
      . rw [Option.is_none_or_iff] at ih
        specialize ih prev_node (by apply cb.prev_node_eq)
        exact ih
      . rw [cb.origin_trg_result_yields_next_node_facts (i + j) node2 eq2]
        apply Set.subset_union_of_subset_left
        apply Set.subset_refl

  theorem stepIsSubsetOfResult (cb : ChaseBranch obs kb) : ∀ n : Nat, (cb.branch.get? n).is_none_or (fun fs => fs.facts.val ⊆ cb.result) := by
    intro n
    rw [Option.is_none_or_iff]
    intro fs _
    intro f h
    exists n
    rw [Option.is_some_and_iff]
    exists fs

  theorem constantsInStepAreFromDatabaseOrRuleSet (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.get? i = some node) :
      node.facts.val.constants ⊆ (kb.db.constants.val ∪ kb.rules.head_constants) := by
    induction i generalizing node with
    | zero =>
      rw [← PossiblyInfiniteList.head_eq, cb.database_first] at eq
      injection eq with eq
      rw [← eq]
      rw [Database.toFactSet_constants_same]
      apply Set.subset_union_of_subset_left
      apply Set.subset_refl
    | succ i ih =>
      let prev_node := (cb.prev_node i (by simp [PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?_tail, PossiblyInfiniteList.get?_drop, eq]))

      rw [cb.origin_trg_result_yields_next_node_facts i node eq]
      unfold FactSet.constants
      intro c c_mem
      rcases c_mem with ⟨f, f_mem, c_mem⟩
      cases f_mem with
      | inl f_mem =>
        apply ih prev_node
        . apply cb.prev_node_eq
        . exists f
      | inr f_mem =>
        unfold ChaseNode.origin_result at f_mem
        let origin := node.origin.get (cb.origin_isSome i eq)
        have c_mem : c ∈ FactSet.constants (origin.fst.val.mapped_head[origin.snd.val]).toSet := by unfold FactSet.constants; exists f
        apply Set.subset_trans (origin.fst.val.mapped_head_constants_subset origin.snd)
        . intro c c_mem
          rw [List.mem_toSet, List.mem_append] at c_mem
          cases c_mem with
          | inl c_mem =>
            apply ih prev_node
            . apply cb.prev_node_eq
            . rw [List.mem_flatMap] at c_mem
              rcases c_mem with ⟨t, t_mem, c_mem⟩
              rw [List.mem_map] at t_mem
              rcases t_mem with ⟨v, v_mem, t_mem⟩
              rcases FunctionFreeConjunction.mem_vars.mp (origin.fst.val.rule.frontier_subset_vars_body v_mem) with ⟨a, a_mem, v_mem'⟩
              exists origin.fst.val.subs.apply_function_free_atom a
              constructor
              . have := cb.origin_trg_is_active i node eq
                apply this.left
                rw [List.mem_toSet]
                unfold PreTrigger.mapped_body
                unfold GroundSubstitution.apply_function_free_conj
                apply List.mem_map_of_mem
                exact a_mem
              . unfold Fact.constants
                rw [List.mem_flatMap]
                exists t
                constructor
                . unfold GroundSubstitution.apply_function_free_atom
                  unfold TermMapping.apply_generalized_atom
                  rw [List.mem_map]
                  exists VarOrConst.var v
                  constructor
                  . exact v_mem'
                  . unfold PreTrigger.subs_for_mapped_head at t_mem
                    rw [PreTrigger.apply_to_var_or_const_frontier_var] at t_mem
                    . exact t_mem
                    . exact v_mem
                . exact c_mem
          | inr c_mem =>
            apply Or.inr
            exists origin.fst.val.rule
            constructor
            . exact origin.fst.property
            . unfold Rule.head_constants
              rw [List.mem_flatMap]
              exists origin.fst.val.rule.head[origin.snd.val]'(by rw [← PreTrigger.length_mapped_head]; exact origin.snd.isLt)
              constructor
              . apply List.get_mem
              . exact c_mem
        . exact c_mem

  theorem trg_loaded_at_some_step_of_trg_loaded_for_result (cb : ChaseBranch obs kb) : ∀ trg : Trigger obs, trg.loaded cb.result -> ∃ n : Nat, (cb.branch.get? n).is_some_and (fun fs => trg.loaded fs.facts.val) := by
    intro trg
    unfold ChaseBranch.result
    unfold PreTrigger.loaded

    induction trg.mapped_body
    case nil =>
      intro _
      exists 0
      rw [← PossiblyInfiniteList.head_eq, cb.database_first]
      simp [Option.is_some_and]
      intro _ contra
      simp [List.mem_toSet] at contra
    case cons hd tl ih =>
      intro loaded
      rcases loaded hd (by simp [List.mem_toSet]) with ⟨hd_idx, hd_mem⟩
      rw [Option.is_some_and_iff] at hd_mem

      rcases ih (by intro e e_mem; rw [List.mem_toSet] at e_mem; apply loaded; simp [List.mem_toSet, e_mem]) with ⟨tl_idx, tl_mem⟩
      rw [Option.is_some_and_iff] at tl_mem

      exists max hd_idx tl_idx
      rw [Option.is_some_and_iff]

      cases Decidable.em (tl_idx ≤ hd_idx) with
      | inl le =>
        rcases hd_mem with ⟨node, node_eq, hd_mem⟩
        exists node
        constructor
        . rw [Nat.max_eq_left le]
          exact node_eq
        . intro e e_mem
          rw [List.mem_toSet, List.mem_cons] at e_mem
          cases e_mem with
          | inl e_mem => rw [e_mem]; exact hd_mem
          | inr e_mem =>
            rcases tl_mem with ⟨tl_node, tl_node_eq, tl_mem⟩
            have := cb.stepIsSubsetOfAllFollowing tl_idx tl_node tl_node_eq (hd_idx - tl_idx)
            rw [PossiblyInfiniteList.get?_drop, Nat.add_sub_cancel' le] at this
            rw [node_eq, Option.is_none_or] at this
            apply this
            apply tl_mem
            rw [List.mem_toSet]
            exact e_mem
      | inr le =>
        have le := Nat.le_of_not_le le
        rcases tl_mem with ⟨node, node_eq, tl_mem⟩
        exists node
        constructor
        . rw [Nat.max_eq_right le]
          exact node_eq
        . intro e e_mem
          rw [List.mem_toSet, List.mem_cons] at e_mem
          cases e_mem with
          | inr e_mem => apply tl_mem; rw [List.mem_toSet]; exact e_mem
          | inl e_mem =>
            rcases hd_mem with ⟨hd_node, hd_node_eq, hd_mem⟩
            have := cb.stepIsSubsetOfAllFollowing hd_idx hd_node hd_node_eq (tl_idx - hd_idx)
            rw [PossiblyInfiniteList.get?_drop, Nat.add_sub_cancel' le] at this
            rw [node_eq, Option.is_none_or] at this
            apply this
            rw [e_mem]
            exact hd_mem

  theorem trg_active_at_some_step_of_trg_active_for_result (cb : ChaseBranch obs kb) : ∀ trg : Trigger obs, trg.active cb.result -> ∃ n : Nat, (cb.branch.get? n).is_some_and (fun fs => trg.active fs.facts) := by
    intro trg
    intro active
    rcases cb.trg_loaded_at_some_step_of_trg_loaded_for_result trg active.left with ⟨step, loaded_step⟩
    rw [Option.is_some_and_iff] at loaded_step
    rcases loaded_step with ⟨node, node_eq, loaded_step⟩
    exists step
    rw [Option.is_some_and_iff]
    exists node
    constructor
    . exact node_eq
    . constructor
      . exact loaded_step
      . intro contra
        apply active.right
        apply obs.monotone
        . have := cb.stepIsSubsetOfResult step
          rw [node_eq, Option.is_none_or] at this
          exact this
        . exact contra

  theorem result_models_kb (cb : ChaseBranch obs kb) : cb.result.modelsKb kb := by
    constructor
    . unfold FactSet.modelsDb
      unfold ChaseBranch.result
      intro f h
      exists 0
      rw [← PossiblyInfiniteList.head_eq, cb.database_first, Option.is_some_and]
      exact h
    . unfold FactSet.modelsRules
      intro r h
      unfold FactSet.modelsRule
      intro subs subs_loaded
      apply Classical.byContradiction
      intro subs_not_obsolete
      let trg : Trigger obs := ⟨r, subs⟩
      have trg_loaded : trg.loaded cb.result := by apply subs_loaded
      have trg_not_obsolete : ¬ obs.cond trg cb.result := by
        intro contra
        have obs_impl_sat := obs.cond_implies_trg_is_satisfied contra
        apply subs_not_obsolete
        rcases obs_impl_sat with ⟨i, s', obs_impl_sat⟩
        exists i
        exists s'

      rcases cb.trg_active_at_some_step_of_trg_active_for_result trg ⟨trg_loaded, trg_not_obsolete⟩ with ⟨step, step_active⟩
      rw [Option.is_some_and_iff] at step_active
      rcases step_active with ⟨node, node_eq, step_active⟩

      rcases cb.fairness ⟨trg, by apply h⟩ with ⟨step', step'_not_active⟩
      rw [Option.is_some_and_iff] at step'_not_active
      rcases step'_not_active.left with ⟨node', node'_eq, step'_not_active_left⟩

      apply step'_not_active_left
      constructor
      . cases Decidable.em (step ≤ step') with
        | inl le =>
          apply Set.subset_trans (b := node.facts.val)
          . exact step_active.left
          . have := cb.stepIsSubsetOfAllFollowing step node node_eq (step' - step)
            rw [PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?_drop, Nat.add_zero] at node'_eq
            rw [PossiblyInfiniteList.get?_drop, Nat.add_sub_cancel' le, node'_eq, Option.is_none_or] at this
            exact this
        | inr le =>
          have gt := Nat.gt_of_not_le le
          apply False.elim
          rcases Nat.exists_eq_add_of_lt gt with ⟨j, gt⟩
          have := step'_not_active.right j
          rw [Nat.add_one, ← Nat.add_succ] at gt
          rw [PossiblyInfiniteList.get?_tail, PossiblyInfiniteList.get?_drop, ← gt] at this
          rw [node_eq, Option.is_none_or] at this
          apply this
          exact step_active
      . intro contra
        apply trg_not_obsolete
        apply obs.monotone
        . have := cb.stepIsSubsetOfResult step'
          rw [PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?_drop, Nat.add_zero] at node'_eq
          rw [node'_eq, Option.is_none_or] at this
          exact this
        . exact contra

  theorem functional_term_originates_from_some_trigger
      {cb : ChaseBranch obs kb} {step : Nat} {node : ChaseNode obs kb.rules}
      (eq : (cb.branch.drop step).head = some node)
      {t : GroundTerm sig}
      (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok)
      (t_mem : t ∈ node.facts.val.terms) :
      ∃ step2, step2 ≤ step ∧ (cb.branch.drop step2).head.is_some_and (fun node2 => node2.origin.is_some_and (fun origin => t ∈ origin.fst.val.fresh_terms_for_head_disjunct origin.snd.val (by rw [← PreTrigger.length_mapped_head]; exact origin.snd.isLt))) := by
    induction step generalizing node with
    | zero =>
      rw [PossiblyInfiniteList.drop_zero, cb.database_first] at eq
      rw [Option.some.injEq] at eq
      have func_free := kb.db.toFactSet.property.right
      unfold FactSet.isFunctionFree at func_free
      rcases t_mem with ⟨f, f_mem, t_mem⟩
      rw [← eq] at f_mem
      specialize func_free f f_mem
      unfold Fact.isFunctionFree at func_free
      specialize func_free _ t_mem
      rcases func_free with ⟨_, func_free⟩
      rcases t_is_func with ⟨_, _, _, t_is_func⟩
      rw [t_is_func] at func_free
      simp [GroundTerm.func, GroundTerm.const] at func_free
    | succ step ih =>
      let prev_node := (cb.prev_node step (by rw [PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?_drop] at eq; simp [PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?_tail, PossiblyInfiniteList.get?_drop, eq]))
      cases Classical.em (t ∈ prev_node.facts.val.terms) with
      | inl term_in_prev_node =>
        rcases ih (by apply cb.prev_node_eq) term_in_prev_node with ⟨step2, ih⟩
        exists step2, (Nat.le_succ_of_le ih.left)
        exact ih.right
      | inr term_not_in_prev_node =>
        exists (step+1), (by simp)
        rw [Option.is_some_and_iff]
        exists node
        constructor
        . exact eq
        rw [Option.is_some_and_iff]
        let origin := node.origin.get (cb.origin_isSome step eq)
        exists origin
        constructor
        . simp [origin]
        rcases t_mem with ⟨f, f_mem, t_mem⟩
        rw [cb.origin_trg_result_yields_next_node_facts _ _ eq] at f_mem
        cases f_mem with
        | inl f_mem => apply False.elim; apply term_not_in_prev_node; exists f
        | inr f_mem =>
          have t_mem : t ∈ origin.fst.val.mapped_head[origin.snd.val].flatMap GeneralizedAtom.terms := by
            rw [List.mem_flatMap]; exists f
          rw [PreTrigger.mem_terms_mapped_head_iff] at t_mem
          cases t_mem with
          | inl t_mem =>
            rcases t_is_func with ⟨_, _, _, t_is_func⟩
            rcases t_mem with ⟨_, _, t_mem⟩
            rw [t_is_func] at t_mem
            simp [GroundTerm.const, GroundTerm.func] at t_mem
          | inr t_mem =>
          cases t_mem with
          | inl t_mem =>
            apply False.elim; apply term_not_in_prev_node
            apply FactSet.terms_subset_of_subset (cb.origin_trg_is_active step node eq).left
            rw [FactSet.mem_terms_toSet]
            rw [PreTrigger.mem_terms_mapped_body_iff]
            apply Or.inr
            rw [List.mem_map] at t_mem; rcases t_mem with ⟨v, v_mem, t_mem⟩
            exists v
            constructor
            . apply Rule.frontier_subset_vars_body; apply Rule.mem_frontier_iff_mem_frontier_for_head.mpr; exact ⟨_, v_mem⟩
            . exact t_mem
          | inr t_mem => exact t_mem

  theorem trigger_introducing_functional_term_occurs_in_chase
      {cb : ChaseBranch obs kb} {step : Nat} {node : ChaseNode obs kb.rules}
      (eq : (cb.branch.drop step).head = some node)
      {t : GroundTerm sig}
      (t_mem_node : t ∈ node.facts.val.terms)
      {trg : RTrigger obs kb.rules}
      {disj_idx : Nat}
      {lt : disj_idx < trg.val.rule.head.length}
      (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
      ∃ step2, step2 ≤ step ∧ (cb.branch.drop step2).head.is_some_and (fun node2 => node2.origin.is_some_and (fun origin => origin.fst.equiv trg ∧ origin.snd.val = disj_idx)) := by
    rcases functional_term_originates_from_some_trigger eq (by
      cases eq : t with
      | const _ =>
        rw [eq] at t_mem_trg
        simp [PreTrigger.fresh_terms_for_head_disjunct, PreTrigger.functional_term_for_var, GroundTerm.func, GroundTerm.const] at t_mem_trg
      | func func ts arity_ok => exists func, ts, arity_ok
    ) t_mem_node with ⟨step2, le, h⟩
    simp only [Option.is_some_and_iff] at h
    rcases h with ⟨node2, node2_eq, origin, origin_eq, t_mem_origin⟩
    simp only [Option.is_some_and_iff]
    exists step2; constructor
    . exact le
    exists node2; constructor
    . exact node2_eq
    exists origin; constructor
    . exact origin_eq
    exact RTrigger.equiv_of_term_mem_fresh_terms_for_head_disjunct t_mem_origin t_mem_trg

  theorem result_of_trigger_introducing_functional_term_occurs_in_chase
      {cb : ChaseBranch obs kb} {step : Nat} {node : ChaseNode obs kb.rules}
      (eq : (cb.branch.drop step).head = some node)
      {t : GroundTerm sig}
      (t_mem_node : t ∈ node.facts.val.terms)
      {trg : RTrigger obs kb.rules}
      {disj_idx : Nat}
      {lt : disj_idx < trg.val.rule.head.length}
      (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
      (trg.val.mapped_head[disj_idx]'(by rw [PreTrigger.length_mapped_head]; exact lt)).toSet ⊆ node.facts.val := by
    rcases trigger_introducing_functional_term_occurs_in_chase eq t_mem_node t_mem_trg with ⟨step2, le, h⟩
    simp only [Option.is_some_and_iff] at h
    rcases h with ⟨node2, node2_eq, origin, origin_eq, equiv, index_eq⟩
    have subset_following := cb.stepIsSubsetOfAllFollowing step2 node2 node2_eq (step - step2)
    rw [PossiblyInfiniteList.get?_drop, Nat.add_sub_of_le le] at subset_following
    rw [PossiblyInfiniteList.head_drop] at eq
    simp only [eq, Option.is_none_or] at subset_following
    apply Set.subset_trans _ subset_following
    have := node2.facts_contain_origin_result
    simp only [origin_eq, Option.is_none_or] at this
    simp only [← PreTrigger.result_eq_of_equiv equiv, ← index_eq]
    exact this

end ChaseBranch

structure ChaseTree (obs : ObsoletenessCondition sig) (kb : KnowledgeBase sig) where
  tree : FiniteDegreeTree (ChaseNode obs kb.rules)
  database_first : tree.root = some {
      facts := (
        let fs := kb.db.toFactSet
        ⟨fs.val, fs.property.left⟩
      )
      origin := none
      facts_contain_origin_result := by simp [Option.is_none_or]
    }
  triggers_exist : ∀ ns : List Nat, (tree.drop ns).root.is_none_or (fun before =>
    let after := (tree.drop ns).childNodes
    (exists_trigger_list obs kb.rules before after) ∨
    (not_exists_trigger_list obs kb.rules before after))

  fairness_leaves : ∀ leaf, leaf ∈ tree.leaves -> ∀ trg : (RTrigger obs kb.rules), ¬ trg.val.active leaf.facts
  fairness_infinite_branches : ∀ trg : (RTrigger obs kb.rules), ∃ i : Nat, ∀ ns : List Nat, ns.length ≥ i ->
    (tree.get? ns).is_none_or (fun fs => ¬ trg.val.active fs.facts)

namespace ChaseTree

  variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

  def chase_branch_for_tree_branch (ct : ChaseTree obs kb) (branch : PossiblyInfiniteList (ChaseNode obs kb.rules)) (branch_mem : branch ∈ ct.tree.branches) : ChaseBranch obs kb := {
    branch := branch,
    database_first := by
      rw [FiniteDegreeTree.branches_eq] at branch_mem
      rcases branch_mem with ⟨head_eq, _⟩
      rw [head_eq]
      exact ct.database_first
    triggers_exist := by
      rcases branch_mem with ⟨ns, branch_eq, ns_max⟩
      have branch_eq2 : ∀ n, (branch.drop n).head = (ct.tree.drop (ns.take n)).root := by intro n; rw [branch_eq, FiniteDegreeTree.root_drop]; rfl

      intro n
      rw [Option.is_none_or_iff]
      intro node node_eq
      have trg_ex := ct.triggers_exist (ns.take n)
      rw [Option.is_none_or_iff] at trg_ex
      specialize trg_ex node (by rw [← branch_eq2, node_eq])
      cases trg_ex with
      | inl trg_ex =>
        apply Or.inl
        rcases trg_ex with ⟨trg, trg_ex⟩
        exists trg
        constructor
        . exact trg_ex.left
        . cases Decidable.em (ns.get n < trg.val.rule.head.length) with
          | inl n_lt_head_length =>
            have length_aux_1 : ns.get n < trg.val.mapped_head.length := by
              rw [trg.val.length_mapped_head]
              exact n_lt_head_length
            exists ⟨ns.get n, length_aux_1⟩
            specialize branch_eq2 n.succ
            rw [PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?_drop] at branch_eq2
            rw [PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?_tail, PossiblyInfiniteList.get?_drop, branch_eq2]
            rw [InfiniteList.take_succ', ← FiniteDegreeTree.drop_drop]
            rw [← FiniteDegreeTree.FiniteDegreeTreeWithRoot.opt_to_tree_after_tree_to_opt (t := ((ct.tree.drop (ns.take n)).drop [ns.get n]))]
            rw [← FiniteDegreeTree.get?_childTrees]
            rw [← FiniteDegreeTree.get?_childNodes]
            rw [← trg_ex.right]
            simp only
            rw [List.getElem?_eq_getElem (by rw [List.length_map, List.length_attach, List.length_zipIdx_with_lt]; exact length_aux_1)]
            rw [Option.some_inj]
            rw [List.getElem_map, List.getElem_attach, ChaseNode.mk.injEq, Subtype.mk.injEq]
            rw [List.zipIdx_with_lt_getElem_fst_eq_getElem]
            rw [List.zipIdx_with_lt_getElem_snd_eq_index]
            constructor
            . rfl
            . rfl
          | inr n_lt_head_length =>
            have : (ct.tree.drop (ns.take n)).childNodes[ns.get n]? = none := by
              rw [← trg_ex.right]
              apply List.getElem?_eq_none
              apply Nat.le_of_not_lt
              rw [List.length_map, List.length_attach, List.length_zipIdx_with_lt, trg.val.length_mapped_head]
              exact n_lt_head_length
            have : node ∈ ct.tree.leaves := by
              unfold FiniteDegreeTree.leaves
              unfold PossiblyInfiniteTree.leaves
              exists (ns.take n)
              constructor
              . rw [branch_eq2, FiniteDegreeTree.root_drop] at node_eq
                exact node_eq
              . apply ns_max
                rw [PossiblyInfiniteTree.get?_branchForAddress, InfiniteList.take_succ']
                rw [FiniteDegreeTree.get?_childNodes, ← FiniteDegreeTree.FiniteDegreeTreeWithRoot.opt_to_tree_none_iff] at this
                rw [FiniteDegreeTree.get?_childTrees, FiniteDegreeTree.FiniteDegreeTreeWithRoot.tree_to_opt_none_iff] at this
                rw [FiniteDegreeTree.drop_drop, FiniteDegreeTree.root_drop] at this
                exact this
            have not_active : ¬ trg.val.active node.facts := by apply ct.fairness_leaves; exact this
            have active : trg.val.active node.facts := trg_ex.left
            contradiction
      | inr trg_ex =>
        apply Or.inr
        constructor
        . exact trg_ex.left
        . specialize branch_eq2 n.succ
          rw [PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?_drop] at branch_eq2
          rw [PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?_tail, PossiblyInfiniteList.get?_drop, branch_eq2]
          rw [InfiniteList.take_succ', ← FiniteDegreeTree.drop_drop]
          rw [← FiniteDegreeTree.FiniteDegreeTreeWithRoot.opt_to_tree_after_tree_to_opt (t := ((ct.tree.drop (ns.take n)).drop [ns.get n]))]
          rw [← FiniteDegreeTree.get?_childTrees]
          rw [← FiniteDegreeTree.get?_childNodes]
          rw [trg_ex.right]
          simp
    fairness := by
      rcases branch_mem with ⟨ns, branch_eq, ns_max⟩
      have branch_eq2 : ∀ n, (branch.drop n).head = (ct.tree.drop (ns.take n)).root := by intro n; rw [branch_eq, FiniteDegreeTree.root_drop]; rfl

      intro trg
      -- Case Distinction: Is branch finite?
      cases Classical.em (∃ n : Nat, ct.tree.get? (ns.take n) ≠ none ∧ ∀ m : Nat, m > n -> ct.tree.get? (ns.take m) = none) with
      | inl h =>
        rcases h with ⟨n, h⟩
        exists n
        constructor
        . rw [Option.is_some_and_iff]
          rcases Option.ne_none_iff_exists'.mp h.left with ⟨node, node_eq⟩
          exists node
          constructor
          . rw [branch_eq2, FiniteDegreeTree.root_drop]; exact node_eq
          . apply ct.fairness_leaves
            exists ns.take n
            constructor
            . exact node_eq
            . apply ns_max
              apply h.right
              simp
        . intro m
          rw [PossiblyInfiniteList.tail_drop, PossiblyInfiniteList.get?_drop, ← PossiblyInfiniteList.head_drop]
          rw [branch_eq2]
          rw [FiniteDegreeTree.root_drop]
          rw [h.right _ (by omega)]
          simp [Option.is_none_or]
      | inr h =>
        have h : ∀ n, ct.tree.get? (ns.take n) ≠ none := by
          intro n contra
          induction n with
          | zero => rw [InfiniteList.take_zero] at contra; rw [← FiniteDegreeTree.root_eq, ct.database_first] at contra; contradiction
          | succ n ih =>
            apply h
            exists n
            constructor
            . exact ih
            . intro m m_gt
              rw [← FiniteDegreeTree.root_drop] at contra
              simp only [FiniteDegreeTree.root] at contra
              rw [← PossiblyInfiniteTree.empty_iff_root_none] at contra
              rw [gt_iff_lt, ← Nat.succ_le_iff] at m_gt
              rcases Nat.exists_eq_add_of_le m_gt with ⟨K, m_gt⟩
              rw [m_gt, InfiniteList.take_add, ← FiniteDegreeTree.get?_drop]
              simp only [FiniteDegreeTree.get?]
              rw [contra, PossiblyInfiniteTree.get?_empty]
        rcases ct.fairness_infinite_branches trg with ⟨i, fairness⟩
        exists i
        constructor
        . rcases Option.ne_none_iff_exists'.mp (h i) with ⟨node, node_eq⟩
          rw [branch_eq2, Option.is_some_and_iff]
          exists node
          constructor
          . rw [FiniteDegreeTree.root_drop]
            exact node_eq
          . specialize fairness (ns.take i) (by rw [InfiniteList.length_take]; simp)
            rw [Option.is_none_or_iff] at fairness
            apply fairness
            exact node_eq
        . intro m
          rw [PossiblyInfiniteList.tail_drop, PossiblyInfiniteList.get?_drop, ← PossiblyInfiniteList.head_drop]
          rw [branch_eq2]
          rw [FiniteDegreeTree.root_drop]
          apply fairness
          rw [InfiniteList.length_take]
          omega
  }

  def branches (ct : ChaseTree obs kb) : Set (ChaseBranch obs kb) := fun branch =>
    branch.branch ∈ ct.tree.branches

  def result (ct : ChaseTree obs kb) : Set (FactSet sig) := fun fs => ∃ branch, branch ∈ ct.branches ∧ branch.result = fs

  theorem predecessor_isSome_of_isSome (ct : ChaseTree obs kb) (path : List Nat) (i : Nat) (isSome : (ct.tree.drop path).childNodes[i]?.isSome) :
      (ct.tree.drop path).root.isSome := by
    cases eq : (ct.tree.drop path).root with
    | none =>
      have : (ct.tree.drop path).childNodes[i]? = none := by apply ct.tree.no_orphans; rw [FiniteDegreeTree.root_drop] at eq; exact eq
      simp [this] at isSome
    | some _ => simp

  def prev_node (ct : ChaseTree obs kb) (path : List Nat) (i : Nat) (isSome : (ct.tree.drop path).childNodes[i]?.isSome) : ChaseNode obs kb.rules :=
    (ct.tree.drop path).root.get (ct.predecessor_isSome_of_isSome path i isSome)

  theorem prev_node_eq (ct : ChaseTree obs kb) (path : List Nat) (i : Nat) (isSome : (ct.tree.drop path).childNodes[i]?.isSome) :
      (ct.tree.drop path).root = some (ct.prev_node path i isSome) := by
    simp [prev_node]

  theorem origin_isSome (ct : ChaseTree obs kb) (path : List Nat) (i : Nat) {node : ChaseNode obs kb.rules}
      (eq : (ct.tree.drop path).childNodes[i]? = some node) : node.origin.isSome := by
    have trg_ex := ct.triggers_exist path
    rw [prev_node_eq _ _ i (by simp [eq]), Option.is_none_or] at trg_ex
    cases trg_ex with
    | inl trg_ex =>
      unfold exists_trigger_list at trg_ex
      unfold exists_trigger_list_condition at trg_ex
      rcases trg_ex with ⟨trg, _, trg_eq⟩
      rw [List.getElem?_eq_some_iff] at eq
      rcases eq with ⟨i_lt, eq⟩
      have := List.getElem_of_eq (Eq.symm trg_eq) i_lt
      rw [List.getElem_map] at this
      simp only at this
      rw [← Option.some.injEq] at this
      rw [Option.some.injEq] at this
      rw [this] at eq
      rw [← eq]
      simp
    | inr trg_ex =>
      rw [trg_ex.right] at eq
      simp at eq

  theorem origin_trg_is_active (ct : ChaseTree obs kb) (path : List Nat) (i : Nat) (node : ChaseNode obs kb.rules) (eq : (ct.tree.drop path).childNodes[i]? = some node) :
      (node.origin.get (ct.origin_isSome path i eq)).fst.val.active (ct.prev_node path i (by simp [eq])).facts.val := by
    have trg_ex := ct.triggers_exist path
    rw [prev_node_eq _ _ i (by simp [eq]), Option.is_none_or] at trg_ex
    cases trg_ex with
    | inl trg_ex =>
      unfold exists_trigger_list at trg_ex
      unfold exists_trigger_list_condition at trg_ex
      rcases trg_ex with ⟨trg, trg_active, trg_eq⟩
      rw [List.getElem?_eq_some_iff] at eq
      rcases eq with ⟨i_lt, eq⟩
      have := List.getElem_of_eq (Eq.symm trg_eq) i_lt
      rw [List.getElem_map] at this
      simp only at this
      rw [this] at eq
      simp only [← eq]
      exact trg_active
    | inr trg_ex =>
      rw [trg_ex.right] at eq
      simp at eq

  theorem origin_trg_result_yields_next_node_facts (ct : ChaseTree obs kb) (path : List Nat) (i : Nat) (node : ChaseNode obs kb.rules) (eq : (ct.tree.drop path).childNodes[i]? = some node) :
      node.facts.val = (ct.prev_node path i (by simp [eq])).facts.val ∪ (node.origin_result (ct.origin_isSome path i eq)).toSet := by
    have trg_ex := ct.triggers_exist path
    rw [prev_node_eq _ _ i (by simp [eq]), Option.is_none_or] at trg_ex
    cases trg_ex with
    | inl trg_ex =>
      unfold exists_trigger_list at trg_ex
      unfold exists_trigger_list_condition at trg_ex
      rcases trg_ex with ⟨trg, trg_active, trg_eq⟩
      rw [List.getElem?_eq_some_iff] at eq
      rcases eq with ⟨i_lt, eq⟩
      have := List.getElem_of_eq (Eq.symm trg_eq) i_lt
      rw [List.getElem_map] at this
      simp only at this
      rw [this] at eq
      simp only [← eq, ChaseNode.origin_result, Option.get_some, List.get_eq_getElem, List.getElem_attach]
      have i_lt : i < trg.val.mapped_head.length := by
        rw [← trg_eq, List.length_map, List.length_attach, List.length_zipIdx_with_lt] at i_lt
        exact i_lt
      simp only [List.zipIdx_with_lt_getElem_fst_eq_getElem i_lt]
      have origin_eq : node.origin.get (by simp [← eq]) = ⟨trg, ⟨i, i_lt⟩⟩ := by simp only [← eq]; simp [List.zipIdx_with_lt_getElem_snd_eq_index i_lt]
      have idx_eq : (node.origin.get (by simp [← eq])).snd.val = i := by rw [origin_eq]
      simp only [idx_eq]
    | inr trg_ex =>
      rw [trg_ex.right] at eq
      simp at eq

  theorem origin_index_eq_child_index (ct : ChaseTree obs kb) (path : List Nat) (i : Nat) (node : ChaseNode obs kb.rules) (eq : (ct.tree.drop path).childNodes[i]? = some node) :
      (node.origin.get (ct.origin_isSome path i eq)).snd.val = i := by
    have trg_ex := ct.triggers_exist path
    rw [prev_node_eq _ _ i (by simp [eq]), Option.is_none_or] at trg_ex
    cases trg_ex with
    | inl trg_ex =>
      unfold exists_trigger_list at trg_ex
      unfold exists_trigger_list_condition at trg_ex
      rcases trg_ex with ⟨trg, trg_active, trg_eq⟩
      rw [List.getElem?_eq_some_iff] at eq
      rcases eq with ⟨i_lt, eq'⟩
      have := List.getElem_of_eq (Eq.symm trg_eq) i_lt
      rw [List.getElem_map] at this
      simp only at this
      rw [this] at eq'
      have : node.origin.get (ct.origin_isSome path i eq) = ⟨trg, ⟨i, by rw [← trg_eq, List.length_map, List.length_attach, List.length_zipIdx_with_lt] at i_lt; exact i_lt⟩⟩ := by
        simp only [← eq', Option.get_some, List.get_eq_getElem, List.getElem_attach]
        rw [List.zipIdx_with_lt_getElem_snd_eq_index]
      rw [this]
    | inr trg_ex =>
      rw [trg_ex.right] at eq
      simp at eq

  theorem stepIsSubsetOfAllFollowing (ct : ChaseTree obs kb) (path : List Nat) (node : ChaseNode obs kb.rules) (eq : (ct.tree.drop path).root = some node) :
      ∀ path2, ((ct.tree.drop path).get? path2).is_none_or (fun node2 => node.facts.val ⊆ node2.facts.val) := by
    intro path2
    induction path2 generalizing path node with
    | nil => rw [← FiniteDegreeTree.root_eq, eq]; simp only [Option.is_none_or]; apply Set.subset_refl
    | cons hd tl ih =>
      rw [Option.is_none_or_iff]
      intro node2 eq2
      have mid_node_some : (ct.tree.drop path).childNodes[hd]?.isSome := by
        rw [Option.isSome_iff_ne_none]
        intro contra
        rw [FiniteDegreeTree.get?_childNodes, ← FiniteDegreeTree.FiniteDegreeTreeWithRoot.opt_to_tree_none_iff] at contra
        rw [FiniteDegreeTree.get?_childTrees, FiniteDegreeTree.FiniteDegreeTreeWithRoot.tree_to_opt_none_iff] at contra
        rw [FiniteDegreeTree.drop_drop, FiniteDegreeTree.root_drop] at contra
        apply Option.some_ne_none node2
        rw [← eq2, FiniteDegreeTree.get?_drop, List.append_cons, ← FiniteDegreeTree.get?_drop]
        apply FiniteDegreeTree.no_orphans_closure
        exact contra
      let mid_node := (ct.tree.drop path).childNodes[hd]?.get mid_node_some
      specialize ih (path ++ [hd]) mid_node (by
        unfold mid_node
        rw [Option.some_get]
        rw [FiniteDegreeTree.get?_childNodes, FiniteDegreeTree.get?_childTrees, FiniteDegreeTree.FiniteDegreeTreeWithRoot.opt_to_tree_after_tree_to_opt, FiniteDegreeTree.drop_drop])
      rw [FiniteDegreeTree.get?_drop, List.append_assoc, List.singleton_append] at ih
      rw [FiniteDegreeTree.get?_drop] at eq2
      simp only [eq2, Option.is_none_or] at ih
      apply Set.subset_trans _ ih
      rw [ct.origin_trg_result_yields_next_node_facts path hd mid_node (by simp [mid_node])]
      apply Set.subset_union_of_subset_left
      simp only [prev_node, eq]
      apply Set.subset_refl

  theorem result_models_kb (ct : ChaseTree obs kb) : ∀ fs, fs ∈ ct.result -> fs.modelsKb kb := by
    intro fs fs_mem
    rcases fs_mem with ⟨branch, _, fs_mem⟩
    rw [← fs_mem]
    apply branch.result_models_kb

  -- TODO: We are considering reverse paths here to make the induction work.
  -- We could instead define chase derivations that do not necessarily start on a database and show similar results for them,
  -- which should then work indictively without reverseing the path. I think eventually we want such derivations anyway.
  -- Things might not be as easy as they sound now though.
  theorem functional_term_originates_from_some_trigger
      {ct : ChaseTree obs kb} {rev_path : List Nat} {node : ChaseNode obs kb.rules}
      (eq : (ct.tree.drop rev_path.reverse).root = some node)
      {t : GroundTerm sig}
      (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok)
      (t_mem : t ∈ node.facts.val.terms) :
      ∃ (rev_path2 : List Nat), rev_path2 <:+ rev_path ∧ (ct.tree.drop rev_path2.reverse).root.is_some_and (fun node2 => node2.origin.is_some_and (fun origin => t ∈ origin.fst.val.fresh_terms_for_head_disjunct origin.snd.val (by rw [← PreTrigger.length_mapped_head]; exact origin.snd.isLt))) := by
    induction rev_path generalizing node with
    | nil =>
      rw [List.reverse_nil, FiniteDegreeTree.drop_nil, ct.database_first] at eq
      rw [Option.some.injEq] at eq
      have func_free := kb.db.toFactSet.property.right
      unfold FactSet.isFunctionFree at func_free
      rcases t_mem with ⟨f, f_mem, t_mem⟩
      rw [← eq] at f_mem
      specialize func_free f f_mem
      unfold Fact.isFunctionFree at func_free
      specialize func_free _ t_mem
      rcases func_free with ⟨_, func_free⟩
      rcases t_is_func with ⟨_, _, _, t_is_func⟩
      rw [t_is_func] at func_free
      simp [GroundTerm.func, GroundTerm.const] at func_free
    | cons i rev_path ih =>
      have eq' : (ct.tree.drop rev_path.reverse).childNodes[i]? = some node := by
        rw [FiniteDegreeTree.get?_childNodes, FiniteDegreeTree.get?_childTrees]
        rw [FiniteDegreeTree.FiniteDegreeTreeWithRoot.opt_to_tree_after_tree_to_opt]
        rw [FiniteDegreeTree.drop_drop]
        rw [List.reverse_cons] at eq
        exact eq
      let prev_node := (ct.prev_node rev_path.reverse i (by rw [eq']; simp))
      cases Classical.em (t ∈ prev_node.facts.val.terms) with
      | inl term_in_prev_node =>
        rcases ih (by apply ct.prev_node_eq) term_in_prev_node with ⟨rev_path2, path_prefix, ih⟩
        exists rev_path2
        constructor
        . rw [List.suffix_cons_iff]; apply Or.inr; exact path_prefix
        . exact ih
      | inr term_not_in_prev_node =>
        exists (i::rev_path); constructor; apply List.suffix_rfl
        rw [Option.is_some_and_iff]
        exists node
        constructor
        . exact eq
        rw [Option.is_some_and_iff]
        let origin := node.origin.get (ct.origin_isSome rev_path.reverse i eq')
        exists origin
        constructor
        . simp [origin]
        rcases t_mem with ⟨f, f_mem, t_mem⟩
        rw [ct.origin_trg_result_yields_next_node_facts _ _ _ eq'] at f_mem
        cases f_mem with
        | inl f_mem => apply False.elim; apply term_not_in_prev_node; exists f
        | inr f_mem =>
          have t_mem : t ∈ origin.fst.val.mapped_head[origin.snd.val].flatMap GeneralizedAtom.terms := by
            rw [List.mem_flatMap]; exists f
          rw [PreTrigger.mem_terms_mapped_head_iff] at t_mem
          cases t_mem with
          | inl t_mem =>
            rcases t_is_func with ⟨_, _, _, t_is_func⟩
            rcases t_mem with ⟨_, _, t_mem⟩
            rw [t_is_func] at t_mem
            simp [GroundTerm.const, GroundTerm.func] at t_mem
          | inr t_mem =>
          cases t_mem with
          | inl t_mem =>
            apply False.elim; apply term_not_in_prev_node
            apply FactSet.terms_subset_of_subset (ct.origin_trg_is_active _ _ _ eq').left
            rw [FactSet.mem_terms_toSet]
            rw [PreTrigger.mem_terms_mapped_body_iff]
            apply Or.inr
            rw [List.mem_map] at t_mem; rcases t_mem with ⟨v, v_mem, t_mem⟩
            exists v
            constructor
            . apply Rule.frontier_subset_vars_body; apply Rule.mem_frontier_iff_mem_frontier_for_head.mpr; exact ⟨_, v_mem⟩
            . exact t_mem
          | inr t_mem => exact t_mem

  theorem trigger_introducing_functional_term_occurs_in_chase
      {ct : ChaseTree obs kb} {path : List Nat} {node : ChaseNode obs kb.rules}
      (eq : (ct.tree.drop path).root = some node)
      {t : GroundTerm sig}
      (t_mem_node : t ∈ node.facts.val.terms)
      {trg : RTrigger obs kb.rules}
      {disj_idx : Nat}
      {lt : disj_idx < trg.val.rule.head.length}
      (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
      ∃ (path2 : List Nat), path2 <+: path ∧ (ct.tree.drop path2).root.is_some_and (fun node2 => node2.origin.is_some_and (fun origin => origin.fst.equiv trg ∧ origin.snd.val = disj_idx)) := by
    rw [← path.reverse_reverse] at eq
    rcases functional_term_originates_from_some_trigger eq (by
      cases eq : t with
      | const _ =>
        rw [eq] at t_mem_trg
        simp [PreTrigger.fresh_terms_for_head_disjunct, PreTrigger.functional_term_for_var, GroundTerm.func, GroundTerm.const] at t_mem_trg
      | func func ts arity_ok => exists func, ts, arity_ok
    ) t_mem_node with ⟨rev_path2, suffix, h⟩
    simp only [Option.is_some_and_iff] at h
    rcases h with ⟨node2, node2_eq, origin, origin_eq, t_mem_origin⟩
    simp only [Option.is_some_and_iff]
    exists rev_path2.reverse; constructor
    . rw [← path.reverse_reverse, List.reverse_prefix]; exact suffix
    exists node2; constructor
    . exact node2_eq
    exists origin; constructor
    . exact origin_eq
    exact RTrigger.equiv_of_term_mem_fresh_terms_for_head_disjunct t_mem_origin t_mem_trg

  theorem result_of_trigger_introducing_functional_term_occurs_in_chase
      {ct : ChaseTree obs kb} {path : List Nat} {node : ChaseNode obs kb.rules}
      (eq : (ct.tree.drop path).root = some node)
      {t : GroundTerm sig}
      (t_mem_node : t ∈ node.facts.val.terms)
      {trg : RTrigger obs kb.rules}
      {disj_idx : Nat}
      {lt : disj_idx < trg.val.rule.head.length}
      (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
      (trg.val.mapped_head[disj_idx]'(by rw [PreTrigger.length_mapped_head]; exact lt)).toSet ⊆ node.facts.val := by
    rcases trigger_introducing_functional_term_occurs_in_chase eq t_mem_node t_mem_trg with ⟨path2, ⟨diff, path2_prefix⟩, h⟩
    simp only [Option.is_some_and_iff] at h
    rcases h with ⟨node2, node2_eq, origin, origin_eq, equiv, index_eq⟩
    have subset_following := ct.stepIsSubsetOfAllFollowing path2 node2 node2_eq diff
    rw [FiniteDegreeTree.get?_drop, path2_prefix] at subset_following
    rw [FiniteDegreeTree.root_drop] at eq
    simp only [eq, Option.is_none_or] at subset_following
    apply Set.subset_trans _ subset_following
    have := node2.facts_contain_origin_result
    simp only [origin_eq, Option.is_none_or] at this
    simp only [← PreTrigger.result_eq_of_equiv equiv, ← index_eq]
    exact this

end ChaseTree

