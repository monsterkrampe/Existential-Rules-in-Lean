import BasicLeanDatastructures.List.Repeat

import ExistentialRules.ChaseSequence.Basic
import ExistentialRules.ChaseSequence.Universality

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

def ChaseTree.firstResult (ct : ChaseTree obs kb) : FactSet sig := fun f => ∃ n, (ct.tree.get (List.repeat 0 n)).is_some_and (fun node => f ∈ node.facts.val)

theorem ChaseTree.firstResult_is_in_result (ct : ChaseTree obs kb) : ct.firstResult ∈ ct.result := by
  let nodes : PossiblyInfiniteList (ChaseNode obs kb.rules) := {
    infinite_list := fun n => ct.tree.get (List.repeat 0 n)
    no_holes := by
      simp only [ne_eq]
      intro n h m
      have no_orphans := ct.tree.tree.no_orphans (List.repeat 0 n) h ⟨List.repeat 0 m, by exists List.repeat 0 (n-m); rw [List.repeat_split n (n-m) m]; simp⟩
      exact no_orphans
  }
  have nodes_is_tree_branch : nodes ∈ ct.tree.branches := by
    let indices : InfiniteList Nat := fun _ => 0
    exists indices
    constructor
    . constructor
      . rfl
      . intro n eq_none
        simp only [InfiniteList.take, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append] at eq_none
        exact eq_none
    . unfold nodes
      unfold PossiblyInfiniteTree.branch_for_address
      unfold InfiniteTreeSkeleton.branch_for_address
      simp only [PossiblyInfiniteList.eq_iff_same_on_all_indices]
      intro n
      have : List.repeat 0 n = (indices.take n).reverse := by
        simp only [indices]
        induction n with
        | zero => simp only [List.repeat, InfiniteList.take, List.reverse_nil]
        | succ n ih =>
          unfold List.repeat
          unfold InfiniteList.take
          rw [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
          rw [ih]
      rw [this]
      rfl

  exists ct.chase_branch_for_tree_branch nodes nodes_is_tree_branch

theorem ChaseTree.firstResult_is_result_when_deterministic (ct : ChaseTree obs kb) : kb.isDeterministic -> ct.result = fun fs => fs = ct.firstResult := by
  intro h_deterministic
  unfold ChaseTree.result
  apply Set.ext
  intro fs
  constructor
  . intro h
    rcases h with ⟨branch, h⟩
    rw [← h.right]
    have branch_in_ct := h.left
    rcases branch_in_ct with ⟨nodes, branch_in_ct⟩
    have : ∀ n, (branch.branch.infinite_list (n+1)).is_none_or (fun _ => nodes n = 0) := by
      intro n
      cases eq : branch.branch.infinite_list (n+1) with
      | none => simp only [Option.is_none_or]
      | some node =>
        have trg_ex := ct.triggers_exist (nodes.take n).reverse
        simp only [Option.is_none_or]
        have n_succ_in_ct := eq
        rw [branch_in_ct.right] at n_succ_in_ct
        unfold FiniteDegreeTree.get at trg_ex
        unfold PossiblyInfiniteTree.get at trg_ex
        cases eq_prev : branch.branch.infinite_list n with
        | none =>
          have no_holes := branch.branch.no_holes (n+1) (by rw [eq]; simp) ⟨n, by simp⟩
          rw [eq_prev] at no_holes
          contradiction
        | some prev_node =>
          rw [branch_in_ct.right] at eq_prev
          simp only [PossiblyInfiniteTree.branch_for_address, InfiniteTreeSkeleton.branch_for_address] at eq_prev
          rw [eq_prev] at trg_ex
          simp only [Option.is_none_or] at trg_ex
          cases trg_ex with
          | inl trg_ex =>
            unfold exists_trigger_list at trg_ex
            unfold exists_trigger_list_condition at trg_ex
            rcases trg_ex with ⟨trg, h_trg⟩
            simp only [PossiblyInfiniteTree.branch_for_address, InfiniteTreeSkeleton.branch_for_address] at n_succ_in_ct
            unfold InfiniteList.take at n_succ_in_ct
            rw [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append] at n_succ_in_ct
            have children_get_eq := ct.tree.tree.getElem_children_eq_get (nodes.take n).reverse (nodes n)
            unfold PossiblyInfiniteTree.get at children_get_eq
            rw [← children_get_eq] at n_succ_in_ct
            rw [← FiniteDegreeTree.children_eq_lifted_children] at n_succ_in_ct
            rw [← h_trg.right] at n_succ_in_ct
            rw [PossiblyInfiniteList.get_fromList_eq_list_getElem] at n_succ_in_ct
            rw [List.getElem?_eq_some_iff] at n_succ_in_ct
            rcases n_succ_in_ct with ⟨isLt, n_succ_in_ct⟩
            rw [List.length_map, List.length_attach, List.length_zipIdx_with_lt] at isLt
            rw [PreTrigger.length_mapped_head] at isLt
            unfold KnowledgeBase.isDeterministic at h_deterministic
            unfold RuleSet.isDeterministic at h_deterministic
            unfold Rule.isDeterministic at h_deterministic
            specialize h_deterministic _ trg.property
            rw [decide_eq_true_iff] at h_deterministic
            rw [h_deterministic, Nat.lt_succ, Nat.le_zero_eq] at isLt
            exact isLt
          | inr trg_ex =>
            unfold not_exists_trigger_list at trg_ex
            have contra := ct.tree.each_successor_none_of_children_empty (nodes.take n).reverse trg_ex.right (nodes n)
            have branch_in_ct := branch_in_ct.right
            rw [PossiblyInfiniteList.eq_iff_same_on_all_indices] at branch_in_ct
            specialize branch_in_ct (n+1)
            simp only [PossiblyInfiniteTree.branch_for_address, InfiniteTreeSkeleton.branch_for_address] at branch_in_ct
            unfold InfiniteList.take at branch_in_ct
            rw [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append] at branch_in_ct
            unfold FiniteDegreeTree.get at contra
            unfold PossiblyInfiniteTree.get at contra
            rw [contra] at branch_in_ct
            rw [eq] at branch_in_ct
            contradiction
    have : ∀ n, (branch.branch.infinite_list n).is_none_or (fun _ => (nodes.take n).reverse = List.repeat 0 n) := by
      intro n
      cases eq : branch.branch.infinite_list n with
      | none => simp only [Option.is_none_or]
      | some val =>
        simp only [Option.is_none_or]
        induction n generalizing val with
        | zero => unfold List.repeat; unfold InfiniteList.take; exact List.reverse_nil
        | succ n ih =>
          unfold List.repeat
          unfold InfiniteList.take
          rw [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
          rw [List.cons_eq_cons]
          constructor
          . specialize this n
            rw [eq] at this
            simp only [Option.is_none_or] at this
            exact this
          . have no_holes := branch.branch.no_holes (n+1)
            rw [eq] at no_holes
            simp at no_holes
            specialize no_holes ⟨n, by simp⟩
            simp only [Option.ne_none_iff_exists] at no_holes
            cases no_holes with | intro prev_node no_holes =>
              apply ih prev_node
              rw [no_holes]
    have nodes_none_means_first_branch_none : ∀ n, ct.tree.get (nodes.take n).reverse = none -> ct.tree.get (List.repeat 0 n) = none := by
      intro n
      induction n with
      | zero => unfold InfiniteList.take; unfold List.repeat; simp
      | succ n ih =>
        intro h
        cases eq : ct.tree.get (nodes.take n).reverse with
        | none =>
          specialize ih eq
          apply Option.decidableEqNone.byContradiction
          intro contra
          have no_orphans := ct.tree.tree.no_orphans (List.repeat 0 (n+1)) contra ⟨(List.repeat 0 n), by exists [0]⟩
          contradiction
        | some node =>
          have eq' := eq
          unfold FiniteDegreeTree.get at eq
          unfold PossiblyInfiniteTree.get at eq
          specialize this n
          rw [branch_in_ct.right] at this
          simp only [PossiblyInfiniteTree.branch_for_address, InfiniteTreeSkeleton.branch_for_address] at this
          rw [eq] at this; simp only [Option.is_none_or] at this
          rw [this] at eq'
          have trg_ex := branch.triggers_exist n
          rw [branch_in_ct.right] at trg_ex
          simp only [PossiblyInfiniteTree.branch_for_address, InfiniteTreeSkeleton.branch_for_address] at trg_ex
          rw [eq] at trg_ex; simp only [Option.is_none_or] at trg_ex
          cases trg_ex with
          | inl trg_ex =>
            unfold exists_trigger_opt_fs at trg_ex
            cases trg_ex with | intro _ trg_ex => cases trg_ex.right with | intro _ trg_ex =>
              unfold FiniteDegreeTree.get at h
              unfold PossiblyInfiniteTree.get at h
              rw [h] at trg_ex
              contradiction
          | inr trg_ex =>
            unfold not_exists_trigger_opt_fs at trg_ex
            have trg_ex' := ct.triggers_exist (List.repeat 0 n)
            rw [eq'] at trg_ex'; simp only [Option.is_none_or] at trg_ex'
            cases trg_ex' with
            | inl trg_ex' =>
              unfold exists_trigger_list at trg_ex'
              unfold exists_trigger_list_condition at trg_ex'
              cases trg_ex' with | intro trg' trg_ex' =>
                apply False.elim
                apply trg_ex.left
                exists trg'
                exact trg_ex'.left
            | inr trg_ex' =>
              unfold not_exists_trigger_list at trg_ex'
              apply FiniteDegreeTree.each_successor_none_of_children_empty
              exact trg_ex'.right
    apply Set.ext
    intro f
    unfold ChaseBranch.result
    unfold ChaseTree.firstResult
    constructor
    . intro h; cases h with | intro n h =>
      exists n
      cases eq : branch.branch.infinite_list n with
      | none => rw [eq] at h; simp only [Option.is_some_and] at h
      | some node =>
        specialize this n
        rw [eq] at this
        simp only [Option.is_none_or] at this
        rw [← this]
        unfold FiniteDegreeTree.get; unfold PossiblyInfiniteTree.get; rw [branch_in_ct.right] at h; exact h
    . intro h; cases h with | intro n h =>
      exists n
      rw [branch_in_ct.right]
      simp only [PossiblyInfiniteTree.branch_for_address, InfiniteTreeSkeleton.branch_for_address]
      cases eq : branch.branch.infinite_list n with
      | none =>
        rw [nodes_none_means_first_branch_none n (by
          unfold FiniteDegreeTree.get
          unfold PossiblyInfiniteTree.get
          rw [branch_in_ct.right] at eq
          exact eq
        )] at h
        simp only [Option.is_some_and] at h
      | some node =>
        specialize this n
        rw [eq] at this
        simp only [Option.is_none_or] at this
        rw [this]
        exact h
  . intro h
    have firstResult_is_in_result := ct.firstResult_is_in_result
    unfold ChaseTree.result at firstResult_is_in_result
    rw [h]
    exact firstResult_is_in_result

theorem deterministicChaseTreeResultUniversallyModelsKb (ct : ChaseTree obs kb) : kb.isDeterministic -> ct.firstResult.universallyModelsKb kb := by
  intro h
  unfold FactSet.universallyModelsKb
  constructor
  . apply ChaseTree.result_models_kb; apply ct.firstResult_is_in_result
  . intro m m_is_model
    cases chaseTreeResultIsUniversal ct m m_is_model with | intro fs h' =>
      cases h' with | intro hom h' =>
        rw [ct.firstResult_is_result_when_deterministic h] at h'
        exists hom
        rw [← h'.left]
        exact h'.right

def ChaseBranch.intoTree (cb : ChaseBranch obs kb) (deterministic : kb.isDeterministic) : ChaseTree obs kb :=
  {
    tree := FiniteDegreeTree.from_branch cb.branch
    database_first := by
      simp only [FiniteDegreeTree.get, PossiblyInfiniteTree.get]
      exact cb.database_first
    triggers_exist := by
      simp only [FiniteDegreeTree.get, PossiblyInfiniteTree.get]
      intro l
      cases eq : l.all (fun e => e = 0) with
      | false => simp only [FiniteDegreeTree.from_branch, PossiblyInfiniteTree.from_branch, eq]; simp [Option.is_none_or]
      | true =>
        simp only [FiniteDegreeTree.from_branch, PossiblyInfiniteTree.from_branch, eq, ↓reduceIte]
        rw [Option.is_none_or_iff]
        intro node eq2
        have cb_trgs := cb.triggers_exist l.length
        rw [Option.is_none_or_iff] at cb_trgs
        specialize cb_trgs node eq2
        cases cb_trgs with
        | inl cb_trgs =>
          apply Or.inl
          rcases cb_trgs with ⟨trg, trg_active, trg_result⟩
          exists trg
          constructor
          . exact trg_active
          . rcases trg_result with ⟨i, trg_result⟩
            have res_length : trg.val.mapped_head.length = 1 := by
              rw [PreTrigger.length_mapped_head]
              unfold KnowledgeBase.isDeterministic at deterministic
              unfold RuleSet.isDeterministic at deterministic
              unfold Rule.isDeterministic at deterministic
              simp only [decide_eq_true_iff] at deterministic
              apply deterministic
              exact trg.property
            have i_eq : i = (⟨0, by simp [res_length]⟩ : Fin trg.val.mapped_head.length) := by
              cases eq : i.val with
              | zero => ext; rw [eq]
              | succ _ =>
                have isLt := i.isLt
                rw [eq, res_length] at isLt
                simp at isLt
            rw [List.map_eq_iff]
            intro j
            cases j with
            | zero =>
              rw [FiniteDegreeTree.getElem_children_eq_getElem_lifted_children]
              rw [PossiblyInfiniteTree.getElem_children_eq_get]
              unfold PossiblyInfiniteTree.get
              rw [List.getElem?_eq_getElem (by rw [List.length_attach, List.length_zipIdx_with_lt]; rw [res_length]; simp)]
              have : (0::l).all (fun e => e = 0) = true := by
                rw [List.all_cons, eq]
                simp
              conv => left; simp [this]
              rw [← trg_result]
              simp only [Option.map_some, Option.some.injEq, List.getElem_attach, ChaseNode.mk.injEq]
              constructor
              . rw [Subtype.mk.injEq, i_eq, List.zipIdx_with_lt_getElem_fst_eq_getElem]
              . rw [i_eq, List.zipIdx_with_lt_getElem_snd_eq_index]
            | succ j =>
              rw [FiniteDegreeTree.getElem_children_eq_getElem_lifted_children]
              rw [PossiblyInfiniteTree.getElem_children_eq_get]
              unfold PossiblyInfiniteTree.get
              rw [List.getElem?_eq_none]
              . simp
              . rw [List.length_attach, List.length_zipIdx_with_lt, res_length]
                simp
        | inr cb_trgs =>
          apply Or.inr
          constructor
          . exact cb_trgs.left
          . apply FiniteDegreeTree.children_empty_of_first_successor_none
            unfold FiniteDegreeTree.get
            unfold PossiblyInfiniteTree.get
            have : (0::l).all (fun e => e = 0) = true := by
              rw [List.all_cons]
              rw [eq]
              simp
            simp [this]
            exact cb_trgs.right
    fairness_leaves := by
      unfold FiniteDegreeTree.from_branch
      unfold PossiblyInfiniteTree.from_branch
      intro leaf leaf_mem
      unfold FiniteDegreeTree.leaves at leaf_mem
      unfold PossiblyInfiniteTree.leaves at leaf_mem
      unfold PossiblyInfiniteTree.get at leaf_mem
      rcases leaf_mem with ⟨node, node_eq, node_children⟩
      have all_none := PossiblyInfiniteTree.each_successor_none_of_children_empty _ _ node_children
      cases eq : node.all (fun e => e = 0) with
      | false => simp [eq] at node_eq
      | true =>
        simp [eq] at node_eq
        have : (0::node).all (fun e => e = 0) = true := by
          rw [List.all_cons, eq]
          simp
        specialize all_none 0
        unfold PossiblyInfiniteTree.get at all_none
        simp [this] at all_none

        intro trg
        have fair := cb.fairness trg
        rcases fair with ⟨i, fair⟩
        rw [Option.is_some_and_iff] at fair
        have : i ≤ node.length := by
          apply Decidable.byContradiction
          intro n_le
          rw [Nat.not_le] at n_le
          -- all cases should result in contradictions
          cases eq2 : i - node.length with
          | zero =>
            rw [Nat.sub_eq_iff_eq_add (by apply Nat.le_of_lt; exact n_le)] at eq2
            rw [eq2] at n_le
            simp at n_le
          | succ j =>
            rw [Nat.sub_eq_iff_eq_add (by apply Nat.le_of_lt; exact n_le)] at eq2
            cases j with
            | zero =>
              cases eq3 : cb.branch.infinite_list i with
              | none => rw [eq3] at fair; simp at fair
              | some _ =>
                rw [eq2, Nat.zero_add, Nat.add_comm, all_none] at eq3
                simp at eq3
            | succ _ =>
              cases eq3 : cb.branch.infinite_list i with
              | none => rw [eq3] at fair; simp at fair
              | some _ =>
                have no_holes := cb.branch.no_holes i (by simp [eq3]) ⟨
                  node.length + 1,
                  by
                    rw [eq2]
                    conv => right; rw [Nat.add_assoc, Nat.add_assoc]
                    apply Nat.lt_add_left
                    rw [← Nat.add_assoc, Nat.add_comm]
                    simp
                ⟩
                rw [all_none] at no_holes
                simp at no_holes
        cases Nat.lt_or_eq_of_le this with
        | inr eq =>
          rcases fair.left with ⟨leaf', fair_left⟩
          rw [eq, node_eq, Option.some_inj] at fair_left
          rw [fair_left.left]
          exact fair_left.right
        | inl lt =>
          have fair_right := fair.right node.length lt
          rw [Option.is_none_or_iff] at fair_right
          apply fair_right
          exact node_eq
    fairness_infinite_branches := by
      unfold FiniteDegreeTree.from_branch
      unfold PossiblyInfiniteTree.from_branch
      intro trg
      have fair := cb.fairness trg
      rcases fair with ⟨i, fair⟩
      exists i + 1
      intro node node_length_ge
      unfold FiniteDegreeTree.get
      unfold PossiblyInfiniteTree.get
      cases eq : node.all (fun e => e = 0) with
      | false => simp [eq, Option.is_none_or]
      | true =>
        simp [eq]
        apply fair.right
        apply Nat.lt_of_succ_le
        exact node_length_ge
  }

theorem ChaseBranch.intoTree_same_result (cb : ChaseBranch obs kb) (deterministic : kb.isDeterministic) : (cb.intoTree deterministic).firstResult = cb.result := by
  unfold ChaseBranch.intoTree
  unfold ChaseBranch.result
  unfold ChaseTree.firstResult
  unfold FiniteDegreeTree.from_branch
  unfold PossiblyInfiniteTree.from_branch
  apply Set.ext
  intro f
  simp only [FiniteDegreeTree.get, PossiblyInfiniteTree.get]
  constructor
  . intro h
    rcases h with ⟨n, h⟩
    rw [List.all_eq_val_repeat 0, List.length_repeat] at h
    simp at h
    exists n
  . intro h
    rcases h with ⟨n, h⟩
    exists n
    rw [List.all_eq_val_repeat 0, List.length_repeat]
    simp
    exact h

theorem deterministicChaseBranchResultUniversallyModelsKb (cb : ChaseBranch obs kb) : kb.isDeterministic -> cb.result.universallyModelsKb kb := by
  intro deterministic
  rw [← cb.intoTree_same_result deterministic]
  apply deterministicChaseTreeResultUniversallyModelsKb
  exact deterministic

