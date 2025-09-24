import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.Basic

import ExistentialRules.Models.Basic
import ExistentialRules.Triggers.RTrigger

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

structure ChaseNode (obs : ObsoletenessCondition sig) (rules : RuleSet sig) where
  facts : { fs : FactSet sig // fs.finite }
  -- the origin is none only for the database
  origin : Option ((trg : RTrigger (obs : LaxObsoletenessCondition sig) rules) × Fin trg.val.mapped_head.length)
  facts_contain_origin_result : origin.is_none_or (fun origin => origin.fst.val.mapped_head[origin.snd.val].toSet ⊆ facts)

def ChaseNode.origin_result {obs : ObsoletenessCondition sig} (node : ChaseNode obs rules) (isSome : node.origin.isSome) :
    List (Fact sig) :=
  let origin := node.origin.get isSome
  origin.fst.val.mapped_head[origin.snd.val]

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
  database_first : branch.infinite_list 0 = some {
    facts := (
      let fs := kb.db.toFactSet
      ⟨fs.val, fs.property.left⟩
    ),
    origin := none,
    facts_contain_origin_result := by simp [Option.is_none_or]
  }
  triggers_exist : ∀ n : Nat, (branch.infinite_list n).is_none_or (fun before =>
    let after := branch.infinite_list (n+1)
    (exists_trigger_opt_fs obs kb.rules before after) ∨
    (not_exists_trigger_opt_fs obs kb.rules before after))
  fairness : ∀ trg : (RTrigger obs kb.rules), ∃ i : Nat, ((branch.infinite_list i).is_some_and (fun fs => ¬ trg.val.active fs.facts))
    ∧ (∀ j : Nat, j > i -> (branch.infinite_list j).is_none_or (fun fs => ¬ trg.val.active fs.facts))

namespace ChaseBranch

  variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

  def result (cb : ChaseBranch obs kb) : FactSet sig :=
    fun f => ∃ n : Nat, (cb.branch.infinite_list n).is_some_and (fun fs => f ∈ fs.facts.val)

  theorem predecessor_isSome_of_isSome (cb : ChaseBranch obs kb) (i : Nat) (isSome : (cb.branch.infinite_list (i + 1)).isSome) :
      (cb.branch.infinite_list i).isSome := by
    cases eq : cb.branch.infinite_list (i+1) with
    | none => rw [eq] at isSome; simp at isSome
    | some node =>
      cases eq_prev : cb.branch.infinite_list i with
      | some prev => simp
      | none =>
        apply False.elim
        have no_holes := cb.branch.no_holes (i+1)
        simp [eq] at no_holes
        specialize no_holes ⟨i, by simp⟩
        apply no_holes
        exact eq_prev

  def prev_node (cb : ChaseBranch obs kb) (i : Nat) (isSome : (cb.branch.infinite_list (i + 1)).isSome) : ChaseNode obs kb.rules :=
    (cb.branch.infinite_list i).get (cb.predecessor_isSome_of_isSome i isSome)

  theorem prev_node_eq (cb : ChaseBranch obs kb) (i : Nat) (isSome : (cb.branch.infinite_list (i + 1)).isSome) :
      cb.branch.infinite_list i = some (cb.prev_node i isSome) := by
    simp [prev_node]

  theorem origin_isSome (cb : ChaseBranch obs kb) (i : Nat) {node : ChaseNode obs kb.rules}
      (eq : cb.branch.infinite_list (i + 1) = some node) : node.origin.isSome := by
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

  theorem origin_trg_is_active (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list (i + 1) = some node) :
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

  theorem origin_trg_result_yields_next_node_facts (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list (i + 1) = some node) :
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

  theorem stepIsSubsetOfAllFollowing (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) :
      ∀ j, (cb.branch.infinite_list (i + j)).is_none_or (fun node2 => node.facts.val ⊆ node2.facts.val) := by
    intro j
    induction j with
    | zero => rw [Nat.add_zero, eq]; simp only [Option.is_none_or]; apply Set.subset_refl
    | succ j ih =>
      rw [Option.is_none_or_iff]
      intro node2 eq2
      let prev_node := (cb.prev_node (i + j) (by rw [Nat.add_assoc]; simp [eq2]))
      apply Set.subset_trans (b := prev_node.facts.val)
      . rw [Option.is_none_or_iff] at ih
        specialize ih prev_node (by apply cb.prev_node_eq)
        exact ih
      . rw [cb.origin_trg_result_yields_next_node_facts (i + j) node2 eq2]
        apply Set.subset_union_of_subset_left
        apply Set.subset_refl

  theorem stepIsSubsetOfResult (cb : ChaseBranch obs kb) : ∀ n : Nat, (cb.branch.infinite_list n).is_none_or (fun fs => fs.facts.val ⊆ cb.result) := by
    intro n
    unfold Option.is_none_or

    cases eq : cb.branch.infinite_list n with
    | none => simp
    | some fs =>
      simp only
      unfold ChaseBranch.result
      intro f h
      exists n
      rw [Option.is_some_and_iff]
      exists fs

  theorem constantsInStepAreFromDatabaseOrRuleSet (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) :
      node.facts.val.constants ⊆ (kb.db.constants.val ∪ kb.rules.head_constants) := by
    induction i generalizing node with
    | zero =>
      rw [cb.database_first] at eq
      injection eq with eq
      rw [← eq]
      rw [Database.toFactSet_constants_same]
      apply Set.subset_union_of_subset_left
      apply Set.subset_refl
    | succ i ih =>
      let prev_node := (cb.prev_node i (by simp [eq]))

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
              rcases origin.fst.val.rule.frontier_occurs_in_body v v_mem with ⟨a, a_mem, v_mem'⟩
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

  theorem trg_loaded_at_some_step_of_trg_loaded_for_result (cb : ChaseBranch obs kb) : ∀ trg : Trigger obs, trg.loaded cb.result -> ∃ n : Nat, (cb.branch.infinite_list n).is_some_and (fun fs => trg.loaded fs.facts.val) := by
    intro trg
    unfold ChaseBranch.result
    unfold PreTrigger.loaded

    induction trg.mapped_body
    case nil =>
      intro _
      exists 0
      rw [cb.database_first]
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
            rw [Nat.add_sub_cancel' le] at this
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
            rw [Nat.add_sub_cancel' le] at this
            rw [node_eq, Option.is_none_or] at this
            apply this
            rw [e_mem]
            exact hd_mem

  theorem trg_active_at_some_step_of_trg_active_for_result (cb : ChaseBranch obs kb) : ∀ trg : Trigger obs, trg.active cb.result -> ∃ n : Nat, (cb.branch.infinite_list n).is_some_and (fun fs => trg.active fs.facts) := by
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
      rw [cb.database_first, Option.is_some_and]
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
            rw [Nat.add_sub_cancel' le, node'_eq, Option.is_none_or] at this
            exact this
        | inr le =>
          have gt := Nat.gt_of_not_le le
          apply False.elim
          have := step'_not_active.right step gt
          rw [node_eq, Option.is_none_or] at this
          apply this
          exact step_active
      . intro contra
        apply trg_not_obsolete
        apply obs.monotone
        . have := cb.stepIsSubsetOfResult step'
          rw [node'_eq, Option.is_none_or] at this
          exact this
        . exact contra

  theorem funcTermForExisVarInChaseMeansTriggerIsUsed (cb : ChaseBranch obs kb) (i : Nat) {node : ChaseNode obs kb.rules} (eq : cb.branch.infinite_list i = some node)
      (trg : RTrigger obs kb.rules) (trg_idx : Fin trg.val.mapped_head.length) {v : sig.V} (v_front : ¬ v ∈ trg.val.rule.frontier)
      (term_in_node : ∃ (f : Fact sig), f ∈ node.facts.val ∧ (trg.val.functional_term_for_var trg_idx.val v) ∈ f.terms) :
      ∃ drop_number : Fin i, (cb.branch.infinite_list (i - drop_number.val)).is_some_and (fun prev_node => prev_node.origin.is_some_and (fun origin => trg.equiv origin.fst ∧ trg_idx.val = origin.snd.val)) := by
    induction i generalizing node with
    | zero =>
      rw [cb.database_first] at eq
      rw [Option.some.injEq] at eq
      have func_free := kb.db.toFactSet.property.right
      unfold FactSet.isFunctionFree at func_free
      rcases term_in_node with ⟨f, f_mem, term_in_node⟩
      rw [← eq] at f_mem
      specialize func_free f f_mem
      unfold Fact.isFunctionFree at func_free
      specialize func_free _ term_in_node
      rcases func_free with ⟨_, func_free⟩
      simp [PreTrigger.functional_term_for_var, GroundTerm.func, GroundTerm.const] at func_free
    | succ i ih =>
      let prev_node := (cb.prev_node i (by simp [eq]))
      cases Classical.em (∃ (f : Fact sig), f ∈ prev_node.facts.val ∧ (trg.val.functional_term_for_var trg_idx.val v) ∈ f.terms) with
      | inl term_in_prev_node =>
        rcases ih (by apply cb.prev_node_eq) term_in_prev_node with ⟨drop, ih⟩
        exists ⟨drop.val + 1, by simp⟩
        rw [Nat.add_sub_add_right]
        exact ih
      | inr term_not_in_prev_node =>
        exists ⟨0, by simp⟩
        rw [Nat.sub_zero, eq]
        rw [Option.is_some_and]
        rw [Option.is_some_and_iff]

        let origin := node.origin.get (cb.origin_isSome i eq)
        exists origin
        constructor
        . simp [origin]
        . rcases term_in_node with ⟨f, f_mem, t_mem⟩
          rw [cb.origin_trg_result_yields_next_node_facts _ _ eq] at f_mem
          cases f_mem with
          | inl f_mem => apply False.elim; apply term_not_in_prev_node; exists f
          | inr f_mem =>
            rw [List.mem_toSet] at f_mem
            unfold ChaseNode.origin_result at f_mem
            rw [← PreTrigger.apply_subs_for_mapped_head_eq] at f_mem
            unfold GroundSubstitution.apply_function_free_conj at f_mem
            rw [List.mem_map] at f_mem
            rcases f_mem with ⟨a, a_mem, f_mem⟩
            rw [← f_mem] at t_mem
            unfold GroundSubstitution.apply_function_free_atom at t_mem
            rw [List.mem_map] at t_mem
            rcases t_mem with ⟨voc, voc_mem, t_mem⟩
            cases voc with
            | const c => simp [GroundSubstitution.apply_var_or_const, PreTrigger.functional_term_for_var, GroundTerm.func, GroundTerm.const] at t_mem
            | var v2 =>
              have v2_front : ¬ v2 ∈ origin.fst.val.rule.frontier := by
                intro contra
                rw [PreTrigger.apply_subs_for_var_or_const_eq, PreTrigger.apply_to_var_or_const_frontier_var _ _ _ contra] at t_mem
                apply term_not_in_prev_node
                rcases origin.fst.val.rule.frontier_occurs_in_body _ contra with ⟨b, b_mem, v2_mem⟩
                exists origin.fst.val.subs.apply_function_free_atom b
                constructor
                . have active := cb.origin_trg_is_active i node eq
                  apply active.left
                  rw [List.mem_toSet]
                  unfold PreTrigger.mapped_body
                  unfold GroundSubstitution.apply_function_free_conj
                  apply List.mem_map_of_mem
                  exact b_mem
                . rw [← t_mem]
                  unfold GroundSubstitution.apply_function_free_atom
                  rw [List.mem_map]
                  exists VarOrConst.var v2
              rw [PreTrigger.apply_subs_for_var_or_const_eq, PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v2_front] at t_mem

              have := RTrigger.funcTermForExisVarInMultipleTriggersMeansTheyAreTheSame
                trg
                origin.fst
                ⟨trg_idx.val, by rw [← PreTrigger.length_mapped_head]; exact trg_idx.isLt⟩
                ⟨origin.snd.val, by rw [← PreTrigger.length_mapped_head]; exact origin.snd.isLt⟩
                v
                v2
                v_front
                v2_front
              apply this
              rw [PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v_front]
              rw [PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v2_front]
              exact Eq.symm t_mem

  theorem funcTermForExisVarInChaseMeansTriggerResultOccurs (cb : ChaseBranch obs kb) (i : Nat) {node : ChaseNode obs kb.rules} (eq : cb.branch.infinite_list i = some node)
      (trg : RTrigger obs kb.rules) (trg_idx : Fin trg.val.mapped_head.length) {v : sig.V} (v_front : ¬ v ∈ trg.val.rule.frontier)
      (term_in_node : ∃ (f : Fact sig), f ∈ node.facts.val ∧ (trg.val.functional_term_for_var trg_idx.val v) ∈ f.terms) :
      trg.val.mapped_head[trg_idx.val].toSet ⊆ node.facts.val := by
    rcases cb.funcTermForExisVarInChaseMeansTriggerIsUsed i eq trg trg_idx v_front term_in_node with ⟨drop, h⟩
    rw [Option.is_some_and_iff] at h
    rcases h with ⟨prev_node, prev_node_eq, h⟩
    rw [Option.is_some_and_iff] at h
    rcases h with ⟨origin, origin_eq, h⟩
    simp only [PreTrigger.result_eq_of_equiv _ _ h.left, h.right]
    have := prev_node.facts_contain_origin_result
    rw [origin_eq, Option.is_none_or] at this
    apply Set.subset_trans this
    have := cb.stepIsSubsetOfAllFollowing (i - drop.val) prev_node prev_node_eq drop.val
    rw [Nat.sub_add_cancel (Nat.le_of_lt drop.isLt), eq, Option.is_none_or] at this
    exact this

end ChaseBranch

structure ChaseTree (obs : ObsoletenessCondition sig) (kb : KnowledgeBase sig) where
  tree : FiniteDegreeTree (ChaseNode obs kb.rules)
  database_first : tree.get [] = some {
      facts := (
        let fs := kb.db.toFactSet
        ⟨fs.val, fs.property.left⟩
      )
      origin := none
      facts_contain_origin_result := by simp [Option.is_none_or]
    }
  triggers_exist : ∀ node : List Nat, (tree.get node).is_none_or (fun before =>
    let after := tree.children node
    (exists_trigger_list obs kb.rules before after) ∨
    (not_exists_trigger_list obs kb.rules before after))

  fairness_leaves : ∀ leaf, leaf ∈ tree.leaves -> ∀ trg : (RTrigger obs kb.rules), ¬ trg.val.active leaf.facts
  fairness_infinite_branches : ∀ trg : (RTrigger obs kb.rules), ∃ i : Nat, ∀ node : List Nat, node.length ≥ i ->
    (tree.get node).is_none_or (fun fs => ¬ trg.val.active fs.facts)

namespace ChaseTree

  variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

  def chase_branch_for_tree_branch (ct : ChaseTree obs kb) (branch : PossiblyInfiniteList (ChaseNode obs kb.rules)) (branch_mem : branch ∈ ct.tree.branches) : ChaseBranch obs kb := {
    branch := branch,
    database_first := by
      rcases branch_mem with ⟨nodes, ⟨nodes_mem, nodes_maximal⟩, branch_eq⟩
      unfold InfiniteTreeSkeleton.branch_addresses_through at nodes_mem
      rw [List.length_nil] at nodes_mem
      have branch_eq2 : ∀ n, branch.infinite_list n = ct.tree.get (nodes.take n).reverse := by intro n; rw [branch_eq]; rfl

      rw [branch_eq2]
      rw [nodes_mem]
      rw [ct.database_first]
    triggers_exist := by
      rcases branch_mem with ⟨nodes, ⟨nodes_mem, nodes_maximal⟩, branch_eq⟩
      unfold InfiniteTreeSkeleton.branch_addresses_through at nodes_mem
      rw [List.length_nil] at nodes_mem
      have branch_eq2 : ∀ n, branch.infinite_list n = ct.tree.get (nodes.take n).reverse := by intro n; rw [branch_eq]; rfl

      intro n
      rw [Option.is_none_or_iff]
      intro node node_eq
      have trg_ex := ct.triggers_exist (nodes.take n).reverse
      rw [Option.is_none_or_iff] at trg_ex
      specialize trg_ex node (by rw [← branch_eq2, node_eq])
      cases trg_ex with
      | inl trg_ex =>
        apply Or.inl
        rcases trg_ex with ⟨trg, trg_ex⟩
        exists trg
        constructor
        . exact trg_ex.left
        . cases Decidable.em (nodes n < trg.val.rule.head.length) with
          | inl n_lt_head_length =>
            have length_aux_1 : nodes n < trg.val.mapped_head.length := by
              rw [trg.val.length_mapped_head]
              exact n_lt_head_length
            have length_aux_2 : nodes n < (ct.tree.children (nodes.take n).reverse).length := by
              rw [← trg_ex.right]
              rw [List.length_map, List.length_attach, List.length_zipIdx_with_lt]
              exact length_aux_1
            exists ⟨nodes n, length_aux_1⟩
            rw [branch_eq2]
            simp only [InfiniteList.take, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
            rw [← ct.tree.getElem_children_eq_get (nodes.take n).reverse ⟨nodes n, length_aux_2⟩]
            rw [Option.some_inj]
            simp only [← trg_ex.right]
            rw [List.getElem_map, ChaseNode.mk.injEq, List.getElem_attach, Subtype.mk.injEq]
            rw [List.zipIdx_with_lt_getElem_fst_eq_getElem]
            rw [List.zipIdx_with_lt_getElem_snd_eq_index]
            constructor
            . rfl
            . rfl
          | inr n_lt_head_length =>
            have : ct.tree.get (nodes n :: (nodes.take n).reverse) = none := by
              unfold FiniteDegreeTree.get
              rw [← PossiblyInfiniteTree.getElem_children_eq_get, ← FiniteDegreeTree.getElem_children_eq_getElem_lifted_children]
              apply List.getElem?_eq_none
              apply Nat.le_of_not_lt
              rw [← trg_ex.right]
              rw [List.length_map, List.length_attach, List.length_zipIdx_with_lt, trg.val.length_mapped_head]
              exact n_lt_head_length
            have : ct.tree.children (nodes.take n).reverse = [] := by
              apply ct.tree.children_empty_of_first_successor_none
              apply nodes_maximal
              simp only [InfiniteList.take, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
              exact this
            have : node ∈ ct.tree.leaves := by
              unfold FiniteDegreeTree.leaves
              unfold PossiblyInfiniteTree.leaves
              exists (nodes.take n).reverse
              constructor
              . rw [branch_eq2] at node_eq
                exact node_eq
              . rw [← ct.tree.children_eq_lifted_children, this]; rfl
            have not_active : ¬ trg.val.active node.facts := by apply ct.fairness_leaves; exact this
            have active : trg.val.active node.facts := trg_ex.left
            contradiction
      | inr trg_ex =>
        apply Or.inr
        constructor
        . exact trg_ex.left
        . rw [branch_eq2]
          simp only [InfiniteList.take, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
          apply ct.tree.each_successor_none_of_children_empty
          exact trg_ex.right
    fairness := by
      rcases branch_mem with ⟨nodes, ⟨nodes_mem, nodes_maximal⟩, branch_eq⟩
      unfold InfiniteTreeSkeleton.branch_addresses_through at nodes_mem
      rw [List.length_nil] at nodes_mem
      have branch_eq2 : ∀ n, branch.infinite_list n = ct.tree.get (nodes.take n).reverse := by intro n; rw [branch_eq]; rfl

      intro trg
      -- Case Distinction: Is branch finite?
      cases Classical.em (∃ n : Nat, ct.tree.get (nodes.take n).reverse ≠ none ∧ ∀ m : Nat, m > n -> ct.tree.get (nodes.take m).reverse = none) with
      | inl h =>
        rcases h with ⟨n, h⟩
        exists n
        constructor
        . rw [Option.is_some_and_iff]
          rcases Option.ne_none_iff_exists'.mp h.left with ⟨node, node_eq⟩
          exists node
          constructor
          . rw [branch_eq2]; exact node_eq
          . apply ct.fairness_leaves
            exists (nodes.take n).reverse
            constructor
            . exact node_eq
            . apply ct.tree.tree.children_empty_of_first_successor_none
              apply nodes_maximal
              apply h.right
              simp
        . intro m m_gt
          rw [branch_eq2]
          rw [h.right m m_gt]
          simp [Option.is_none_or]
      | inr h =>
        have h : ∀ n, ct.tree.get (nodes.take n).reverse ≠ none := by
          intro n contra
          induction n with
          | zero => simp only [InfiniteList.take] at contra; rw [List.reverse_nil, ct.database_first] at contra; contradiction
          | succ n ih =>
            apply h
            exists n
            constructor
            . exact ih
            . intro m m_gt
              apply Option.decidableEqNone.byContradiction
              intro neq_none
              apply ct.tree.tree.no_orphans (nodes.take m).reverse neq_none ⟨(nodes.take (n+1)).reverse, by
                exists ((nodes.skip (n+1)).take (m - (n+1))).reverse
                rw [← List.reverse_append]
                cases Decidable.em (n + 1 < m) with
                | inl lt => rw [InfiniteList.combine_skip_take nodes m ⟨n + 1, lt⟩]
                | inr le =>
                  have : n + 1 = m := by
                    apply Nat.eq_of_lt_succ_of_not_lt
                    . apply Nat.succ_lt_succ; exact m_gt
                    . exact le
                  rw [this]
                  simp only [Nat.sub_self, InfiniteList.take, List.append_nil]⟩
              exact contra
        rcases ct.fairness_infinite_branches trg with ⟨i, fairness⟩
        exists i
        constructor
        . rcases Option.ne_none_iff_exists'.mp (h i) with ⟨node, node_eq⟩
          rw [branch_eq2, Option.is_some_and_iff]
          exists node
          constructor
          . exact node_eq
          . specialize fairness (nodes.take i).reverse (by rw [List.length_reverse, InfiniteList.length_take]; simp)
            rw [Option.is_none_or_iff] at fairness
            apply fairness
            exact node_eq
        . intro j j_gt
          rw [branch_eq2]
          apply fairness
          rw [List.length_reverse, InfiniteList.length_take]
          apply Nat.le_of_lt
          exact j_gt
  }

  def branches (ct : ChaseTree obs kb) : Set (ChaseBranch obs kb) := fun branch =>
    branch.branch ∈ ct.tree.branches

  def branches_through (ct : ChaseTree obs kb) (node : List Nat) : Set (ChaseBranch obs kb) := fun branch =>
    branch.branch ∈ ct.tree.branches_through node

  def result (ct : ChaseTree obs kb) : Set (FactSet sig) := fun fs => ∃ branch, branch ∈ ct.branches ∧ branch.result = fs

  theorem predecessor_isSome_of_isSome (ct : ChaseTree obs kb) (path : List Nat) (i : Nat) (isSome : (ct.tree.get (i::path)).isSome) :
      (ct.tree.get path).isSome := by
    cases eq : ct.tree.get (i::path) with
    | none => rw [eq] at isSome; simp at isSome
    | some node =>
      cases eq_prev : ct.tree.get path with
      | some prev => simp
      | none =>
        apply False.elim
        have no_holes := ct.tree.tree.no_orphans (i::path)
        unfold FiniteDegreeTree.get at eq
        unfold PossiblyInfiniteTree.get at eq
        simp [eq] at no_holes
        specialize no_holes path [i] (by simp)
        apply no_holes
        exact eq_prev

  def prev_node (ct : ChaseTree obs kb) (path : List Nat) (i : Nat) (isSome : (ct.tree.get (i::path)).isSome) : ChaseNode obs kb.rules :=
    (ct.tree.get path).get (ct.predecessor_isSome_of_isSome path i isSome)

  theorem prev_node_eq (ct : ChaseTree obs kb) (path : List Nat) (i : Nat) (isSome : (ct.tree.get (i::path)).isSome) :
      ct.tree.get path = some (ct.prev_node path i isSome) := by
    simp [prev_node]

  theorem origin_isSome (ct : ChaseTree obs kb) (path : List Nat) (i : Nat) {node : ChaseNode obs kb.rules}
      (eq : ct.tree.get (i::path) = some node) : node.origin.isSome := by
    have trg_ex := ct.triggers_exist path
    rw [prev_node_eq _ _ i (by simp [eq]), Option.is_none_or] at trg_ex
    cases trg_ex with
    | inl trg_ex =>
      unfold exists_trigger_list at trg_ex
      unfold exists_trigger_list_condition at trg_ex
      rcases trg_ex with ⟨trg, _, trg_eq⟩
      let i_fin : Fin (ct.tree.children path).length := ⟨i, by
        unfold FiniteDegreeTree.get at eq
        rw [← ct.tree.tree.getElem_children_eq_get path i] at eq
        rw [← ct.tree.getElem_children_eq_getElem_lifted_children path] at eq
        rw [List.getElem?_eq_some_iff] at eq
        rcases eq with ⟨h, _⟩
        exact h
      ⟩
      have := List.getElem_of_eq (Eq.symm trg_eq) i_fin.isLt
      rw [List.getElem_map] at this
      simp only at this
      rw [← Option.some.injEq] at this
      rw [ct.tree.getElem_children_eq_get path i_fin] at this
      simp only [i_fin, eq] at this
      rw [Option.some.injEq] at this
      rw [this]
      simp
    | inr trg_ex =>
      unfold not_exists_trigger_list at trg_ex
      have := ct.tree.each_successor_none_of_children_empty _ trg_ex.right i
      rw [this] at eq
      simp at eq

  theorem origin_trg_is_active (ct : ChaseTree obs kb) (path : List Nat) (i : Nat) (node : ChaseNode obs kb.rules) (eq : ct.tree.get (i::path) = some node) :
      (node.origin.get (ct.origin_isSome path i eq)).fst.val.active (ct.prev_node path i (by simp [eq])).facts.val := by
    have trg_ex := ct.triggers_exist path
    rw [prev_node_eq _ _ i (by simp [eq]), Option.is_none_or] at trg_ex
    cases trg_ex with
    | inl trg_ex =>
      unfold exists_trigger_list at trg_ex
      unfold exists_trigger_list_condition at trg_ex
      rcases trg_ex with ⟨trg, trg_active, trg_eq⟩
      let i_fin : Fin (ct.tree.children path).length := ⟨i, by
        unfold FiniteDegreeTree.get at eq
        rw [← ct.tree.tree.getElem_children_eq_get path i] at eq
        rw [← ct.tree.getElem_children_eq_getElem_lifted_children path] at eq
        rw [List.getElem?_eq_some_iff] at eq
        rcases eq with ⟨h, _⟩
        exact h
      ⟩
      have := List.getElem_of_eq (Eq.symm trg_eq) i_fin.isLt
      rw [List.getElem_map] at this
      simp only at this
      rw [← Option.some.injEq] at this
      rw [ct.tree.getElem_children_eq_get path i_fin] at this
      simp only [i_fin, eq] at this
      rw [Option.some.injEq] at this
      simp [this, trg_active]
    | inr trg_ex =>
      unfold not_exists_trigger_list at trg_ex
      have := ct.tree.each_successor_none_of_children_empty _ trg_ex.right i
      rw [this] at eq
      simp at eq

  theorem origin_trg_result_yields_next_node_facts (ct : ChaseTree obs kb) (path : List Nat) (i : Nat) (node : ChaseNode obs kb.rules) (eq : ct.tree.get (i::path) = some node) :
      node.facts.val = (ct.prev_node path i (by simp [eq])).facts.val ∪ (node.origin_result (ct.origin_isSome path i eq)).toSet := by
    have trg_ex := ct.triggers_exist path
    rw [prev_node_eq _ _ i (by simp [eq]), Option.is_none_or] at trg_ex
    cases trg_ex with
    | inl trg_ex =>
      unfold exists_trigger_list at trg_ex
      unfold exists_trigger_list_condition at trg_ex
      rcases trg_ex with ⟨trg, trg_active, trg_eq⟩
      let i_fin : Fin (ct.tree.children path).length := ⟨i, by
        unfold FiniteDegreeTree.get at eq
        rw [← ct.tree.tree.getElem_children_eq_get path i] at eq
        rw [← ct.tree.getElem_children_eq_getElem_lifted_children path] at eq
        rw [List.getElem?_eq_some_iff] at eq
        rcases eq with ⟨h, _⟩
        exact h
      ⟩
      have := List.getElem_of_eq (Eq.symm trg_eq) i_fin.isLt
      rw [List.getElem_map] at this
      simp only at this
      rw [← Option.some.injEq] at this
      rw [ct.tree.getElem_children_eq_get path i_fin] at this
      simp only [i_fin, eq] at this
      rw [Option.some.injEq] at this
      unfold ChaseNode.origin_result
      have i_lt : i < trg.val.mapped_head.length := by
        have : trg.val.mapped_head.length = (ct.tree.children path).length := by
          rw [← trg_eq]
          rw [List.length_map, List.length_attach, List.length_zipIdx_with_lt]
        rw [this]
        exact i_fin.isLt
      have origin_eq : node.origin.get (by simp [this]) = ⟨trg, ⟨i, i_lt⟩⟩ := by simp only [this]; simp [List.zipIdx_with_lt_getElem_snd_eq_index i_lt]
      have idx_eq : (node.origin.get (by simp [this])).snd.val = i := by rw [origin_eq]
      simp only [this]
      simp [List.zipIdx_with_lt_getElem_fst_eq_getElem i_lt, idx_eq]
    | inr trg_ex =>
      unfold not_exists_trigger_list at trg_ex
      have := ct.tree.each_successor_none_of_children_empty _ trg_ex.right i
      rw [this] at eq
      simp at eq

  theorem stepIsSubsetOfAllFollowing (ct : ChaseTree obs kb) (path : List Nat) (node : ChaseNode obs kb.rules) (eq : ct.tree.get path = some node) :
      ∀ path2, (ct.tree.get (path2 ++ path)).is_none_or (fun node2 => node.facts.val ⊆ node2.facts.val) := by
    intro path2
    induction path2 with
    | nil => rw [List.nil_append, eq]; simp only [Option.is_none_or]; apply Set.subset_refl
    | cons hd tl ih =>
      rw [Option.is_none_or_iff]
      intro node2 eq2
      let prev_node := (ct.prev_node (tl ++ path) hd (by rw [← List.cons_append, eq2]; simp))
      apply Set.subset_trans (b := prev_node.facts.val)
      . rw [Option.is_none_or_iff] at ih
        specialize ih prev_node (by apply ct.prev_node_eq)
        exact ih
      . rw [ct.origin_trg_result_yields_next_node_facts (tl ++ path) hd node2 eq2]
        apply Set.subset_union_of_subset_left
        apply Set.subset_refl

  theorem result_models_kb (ct : ChaseTree obs kb) : ∀ fs, fs ∈ ct.result -> fs.modelsKb kb := by
    intro fs fs_mem
    rcases fs_mem with ⟨branch, _, fs_mem⟩
    rw [← fs_mem]
    apply branch.result_models_kb

  theorem funcTermForExisVarInChaseMeansTriggerIsUsed (ct : ChaseTree obs kb) (path : List Nat) {node : ChaseNode obs kb.rules} (eq : ct.tree.get path = some node)
      (trg : RTrigger obs kb.rules) (trg_idx : Fin trg.val.mapped_head.length) {v : sig.V} (v_front : ¬ v ∈ trg.val.rule.frontier)
      (term_in_node : ∃ (f : Fact sig), f ∈ node.facts.val ∧ (trg.val.functional_term_for_var trg_idx.val v) ∈ f.terms) :
      ∃ drop_number : Fin path.length, (ct.tree.get (path.drop drop_number.val)).is_some_and (fun prev_node => prev_node.origin.is_some_and (fun origin => trg.equiv origin.fst ∧ trg_idx.val = origin.snd.val)) := by
    induction path generalizing node with
    | nil =>
      rw [ct.database_first] at eq
      rw [Option.some.injEq] at eq
      have func_free := kb.db.toFactSet.property.right
      unfold FactSet.isFunctionFree at func_free
      rcases term_in_node with ⟨f, f_mem, term_in_node⟩
      rw [← eq] at f_mem
      specialize func_free f f_mem
      unfold Fact.isFunctionFree at func_free
      specialize func_free _ term_in_node
      rcases func_free with ⟨_, func_free⟩
      simp [PreTrigger.functional_term_for_var, GroundTerm.func, GroundTerm.const] at func_free
    | cons i path ih =>
      let prev_node := (ct.prev_node path i (by simp [eq]))
      cases Classical.em (∃ (f : Fact sig), f ∈ prev_node.facts.val ∧ (trg.val.functional_term_for_var trg_idx.val v) ∈ f.terms) with
      | inl term_in_prev_node =>
        rcases ih (by apply ct.prev_node_eq) term_in_prev_node with ⟨drop, ih⟩
        exists ⟨drop.val + 1, by simp⟩
      | inr term_not_in_prev_node =>
        exists ⟨0, by simp⟩
        rw [List.drop_zero, eq]
        rw [Option.is_some_and]
        rw [Option.is_some_and_iff]

        let origin := node.origin.get (ct.origin_isSome path i eq)
        exists origin
        constructor
        . simp [origin]
        . rcases term_in_node with ⟨f, f_mem, t_mem⟩
          rw [ct.origin_trg_result_yields_next_node_facts _ _ _ eq] at f_mem
          cases f_mem with
          | inl f_mem => apply False.elim; apply term_not_in_prev_node; exists f
          | inr f_mem =>
            rw [List.mem_toSet] at f_mem
            unfold ChaseNode.origin_result at f_mem
            rw [← PreTrigger.apply_subs_for_mapped_head_eq] at f_mem
            unfold GroundSubstitution.apply_function_free_conj at f_mem
            rw [List.mem_map] at f_mem
            rcases f_mem with ⟨a, a_mem, f_mem⟩
            rw [← f_mem] at t_mem
            unfold GroundSubstitution.apply_function_free_atom at t_mem
            rw [List.mem_map] at t_mem
            rcases t_mem with ⟨voc, voc_mem, t_mem⟩
            cases voc with
            | const c => simp [GroundSubstitution.apply_var_or_const, PreTrigger.functional_term_for_var, GroundTerm.func, GroundTerm.const] at t_mem
            | var v2 =>
              have v2_front : ¬ v2 ∈ origin.fst.val.rule.frontier := by
                intro contra
                rw [PreTrigger.apply_subs_for_var_or_const_eq, PreTrigger.apply_to_var_or_const_frontier_var _ _ _ contra] at t_mem
                apply term_not_in_prev_node
                rcases origin.fst.val.rule.frontier_occurs_in_body _ contra with ⟨b, b_mem, v2_mem⟩
                exists origin.fst.val.subs.apply_function_free_atom b
                constructor
                . have active := ct.origin_trg_is_active path i node eq
                  apply active.left
                  rw [List.mem_toSet]
                  unfold PreTrigger.mapped_body
                  unfold GroundSubstitution.apply_function_free_conj
                  apply List.mem_map_of_mem
                  exact b_mem
                . rw [← t_mem]
                  unfold GroundSubstitution.apply_function_free_atom
                  rw [List.mem_map]
                  exists VarOrConst.var v2
              rw [PreTrigger.apply_subs_for_var_or_const_eq, PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v2_front] at t_mem

              have := RTrigger.funcTermForExisVarInMultipleTriggersMeansTheyAreTheSame
                trg
                origin.fst
                ⟨trg_idx.val, by rw [← PreTrigger.length_mapped_head]; exact trg_idx.isLt⟩
                ⟨origin.snd.val, by rw [← PreTrigger.length_mapped_head]; exact origin.snd.isLt⟩
                v
                v2
                v_front
                v2_front
              apply this
              rw [PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v_front]
              rw [PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v2_front]
              exact Eq.symm t_mem

  theorem funcTermForExisVarInChaseMeansTriggerResultOccurs (ct : ChaseTree obs kb) (path : List Nat) {node : ChaseNode obs kb.rules} (eq : ct.tree.get path = some node)
      (trg : RTrigger obs kb.rules) (trg_idx : Fin trg.val.mapped_head.length) {v : sig.V} (v_front : ¬ v ∈ trg.val.rule.frontier)
      (term_in_node : ∃ (f : Fact sig), f ∈ node.facts.val ∧ (trg.val.functional_term_for_var trg_idx.val v) ∈ f.terms) :
      trg.val.mapped_head[trg_idx.val].toSet ⊆ node.facts.val := by
    rcases ct.funcTermForExisVarInChaseMeansTriggerIsUsed path eq trg trg_idx v_front term_in_node with ⟨drop, h⟩
    rw [Option.is_some_and_iff] at h
    rcases h with ⟨prev_node, prev_node_eq, h⟩
    rw [Option.is_some_and_iff] at h
    rcases h with ⟨origin, origin_eq, h⟩
    simp only [PreTrigger.result_eq_of_equiv _ _ h.left, h.right]
    have := prev_node.facts_contain_origin_result
    rw [origin_eq, Option.is_none_or] at this
    apply Set.subset_trans this
    have := ct.stepIsSubsetOfAllFollowing (path.drop drop.val) prev_node prev_node_eq (path.take drop.val)
    rw [List.take_append_drop, eq, Option.is_none_or] at this
    exact this

end ChaseTree

