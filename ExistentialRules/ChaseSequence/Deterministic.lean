import BasicLeanDatastructures.List.Repeat

import ExistentialRules.ChaseSequence.Basic
import ExistentialRules.ChaseSequence.Universality

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

def ChaseTree.firstResult (ct : ChaseTree obs kb) : FactSet sig := fun f => ∃ n, (ct.tree.get? (List.repeat 0 n)).is_some_and (fun node => f ∈ node.facts.val)

theorem ChaseTree.firstResult_is_in_result (ct : ChaseTree obs kb) : ct.firstResult ∈ ct.result := by
  let nodes : PossiblyInfiniteList (ChaseNode obs kb.rules) := {
    infinite_list := fun n => ct.tree.get? (List.repeat 0 n)
    no_holes := by
      intro n
      simp only [InfiniteList.get]
      intro eq
      have := FiniteDegreeTree.no_orphans_closure _ eq (List.repeat 0 1)
      rw [FiniteDegreeTree.get?_drop, ← List.repeat_split _ _ _ rfl] at this
      exact this
  }
  have nodes_is_tree_branch : nodes ∈ ct.tree.branches := by
    let indices : InfiniteList Nat := fun _ => 0
    exists indices
    constructor
    . unfold nodes
      apply PossiblyInfiniteList.ext
      intro n
      rw [PossiblyInfiniteTree.get?_branchForAddress]
      simp only [PossiblyInfiniteList.get?, InfiniteList.get]
      have : List.repeat 0 n = (indices.take n) := by
        simp only [indices]
        induction n with
        | zero => simp only [List.repeat, InfiniteList.take]
        | succ n ih =>
          rw [InfiniteList.take_succ]
          unfold List.repeat
          rw [ih]
          rfl
      rw [this]
      rfl
    . intro n eq_none
      rw [PossiblyInfiniteTree.get?_branchForAddress, InfiniteList.take_succ'] at eq_none
      rw [PossiblyInfiniteList.head_eq, PossiblyInfiniteTree.get?_childNodes, PossiblyInfiniteTree.get?_childTrees, PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.opt_to_tree_after_tree_to_opt, PossiblyInfiniteTree.drop_drop, PossiblyInfiniteTree.root_drop]
      exact eq_none

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
    have : ∀ n, (branch.branch.get? (n+1)).is_none_or (fun _ => nodes.get n = 0) := by
      intro n
      rw [Option.is_none_or_iff]
      intro node eq
      rw [branch_in_ct.left, PossiblyInfiniteTree.get?_branchForAddress] at eq
      have eq : (ct.tree.drop (nodes.take n)).childNodes[nodes.get n]? = some node := by
        rw [FiniteDegreeTree.get?_childNodes, FiniteDegreeTree.get?_childTrees, FiniteDegreeTree.FiniteDegreeTreeWithRoot.opt_to_tree_after_tree_to_opt, FiniteDegreeTree.drop_drop, FiniteDegreeTree.root_drop]
        rw [InfiniteList.take_succ'] at eq
        exact eq
      have := ct.origin_index_eq_child_index _ _ _ eq
      rw [← this]
      let origin := node.origin.get (ct.origin_isSome _ _ eq)
      have := origin.snd.isLt
      simp only [PreTrigger.length_mapped_head] at this
      specialize h_deterministic origin.fst.val.rule origin.fst.property
      simp only [Rule.isDeterministic, decide_eq_true_iff] at h_deterministic
      rw [h_deterministic] at this
      rw [Nat.lt_one_iff] at this
      rw [this]
    have : ∀ n, (branch.branch.get? n).is_none_or (fun _ => nodes.take n = List.repeat 0 n) := by
      intro n
      rw [Option.is_none_or_iff]
      intro val eq
      induction n generalizing val with
      | zero => unfold List.repeat; rw [InfiniteList.take_zero]
      | succ n ih =>
        rw [List.repeat_split (n+1) n 1 rfl]
        rw [InfiniteList.take_succ']
        cases eq' : branch.branch.get? n with
        | none => simp only [PossiblyInfiniteList.get?] at eq; rw [branch.branch.no_holes n eq'] at eq; simp at eq
        | some val' =>
        rw [ih _ eq']
        specialize this n
        rw [eq] at this
        simp only [Option.is_none_or] at this
        rw [this]
        simp [List.repeat]
    have nodes_none_means_first_branch_none : ∀ n, ct.tree.get? (nodes.take n) = none -> ct.tree.get? (List.repeat 0 n) = none := by
      intro n
      induction n with
      | zero => unfold InfiniteList.take; unfold List.repeat; simp
      | succ n ih =>
        rw [List.repeat_split (n+1) n 1 rfl]
        specialize this n
        rw [branch_in_ct.left, PossiblyInfiniteTree.get?_branchForAddress] at this
        cases eq : ct.tree.tree.get? (nodes.take n) with
        | none =>
          specialize ih eq
          have := ct.tree.no_orphans_closure _ ih (List.repeat 0 1)
          rw [FiniteDegreeTree.get?_drop] at this
          intros; exact this
        | some node =>
          simp only [eq, Option.is_none_or] at this
          rw [← this]; simp only [List.repeat]
          intro eq_none
          have := branch_in_ct.right n (by
            rw [PossiblyInfiniteTree.get?_branchForAddress]
            exact eq_none
          )
          rw [PossiblyInfiniteList.head_eq, PossiblyInfiniteTree.get?_childNodes, PossiblyInfiniteTree.get?_childTrees, PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.opt_to_tree_after_tree_to_opt, PossiblyInfiniteTree.drop_drop, PossiblyInfiniteTree.root_drop] at this
          exact this
    apply Set.ext
    intro f
    unfold ChaseBranch.result
    unfold ChaseTree.firstResult
    constructor
    . rintro ⟨n, h⟩
      rw [Option.is_some_and_iff] at h
      rcases h with ⟨node, eq, h⟩
      exists n
      specialize this n
      rw [eq] at this
      simp only [Option.is_none_or] at this
      rw [← this]
      rw [branch_in_ct.left, PossiblyInfiniteTree.get?_branchForAddress] at eq
      simp only [FiniteDegreeTree.get?, eq, Option.is_some_and]
      exact h
    . rintro ⟨n, h⟩
      exists n
      cases eq : branch.branch.get? n with
      | none =>
        rw [branch_in_ct.left, PossiblyInfiniteTree.get?_branchForAddress] at eq
        rw [nodes_none_means_first_branch_none n eq] at h
        simp only [Option.is_some_and] at h
      | some node =>
        simp only [Option.is_some_and]
        specialize this n; rw [eq] at this; simp only [Option.is_none_or] at this
        rw [branch_in_ct.left, PossiblyInfiniteTree.get?_branchForAddress] at eq
        simp only [FiniteDegreeTree.get?] at h; rw [← this, eq] at h; simp only [Option.is_some_and] at h
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
    database_first := cb.database_first
    triggers_exist := by
      simp only [Option.is_none_or_iff]
      intro ns node eq
      simp only [FiniteDegreeTree.from_branch, PossiblyInfiniteTree.from_branch, FiniteDegreeTree.root_drop, FiniteDegreeTree.get?, PossiblyInfiniteTree.get?, InfiniteTreeSkeleton.get] at eq
      cases all_zero : ns.all (fun e => e = 0) with
      | false => simp [all_zero] at eq
      | true =>
        simp only [all_zero, ↓reduceIte] at eq
        have trg_ex := cb.triggers_exist ns.length
        simp only [PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?, InfiniteList.get] at trg_ex
        simp only [eq, Option.is_none_or] at trg_ex
        cases trg_ex with
        | inl trg_ex =>
          apply Or.inl
          rcases trg_ex with ⟨trg, trg_active, i, trg_eq⟩
          exists trg; constructor; exact trg_active
          have length_mapped_head_eq : trg.val.mapped_head.length = 1 := by
            rw [PreTrigger.length_mapped_head]
            specialize deterministic trg.val.rule trg.property
            simp only [Rule.isDeterministic, decide_eq_true_iff] at deterministic
            exact deterministic
          have i_zero : i.val = 0 := by have isLt := i.isLt; simp only [length_mapped_head_eq, Nat.lt_one_iff] at isLt; exact isLt
          apply List.ext_getElem?
          intro j
          cases j with
          | succ j =>
            rw [FiniteDegreeTree.get?_childNodes, FiniteDegreeTree.get?_childTrees, FiniteDegreeTree.FiniteDegreeTreeWithRoot.opt_to_tree_after_tree_to_opt, FiniteDegreeTree.drop_drop, FiniteDegreeTree.root_drop]
            simp only [FiniteDegreeTree.from_branch, PossiblyInfiniteTree.from_branch, FiniteDegreeTree.get?, PossiblyInfiniteTree.get?, InfiniteTreeSkeleton.get]
            simp [List.length_zipIdx_with_lt, length_mapped_head_eq]
          | zero =>
            rw [FiniteDegreeTree.get?_childNodes, FiniteDegreeTree.get?_childTrees, FiniteDegreeTree.FiniteDegreeTreeWithRoot.opt_to_tree_after_tree_to_opt, FiniteDegreeTree.drop_drop, FiniteDegreeTree.root_drop]
            simp only [FiniteDegreeTree.from_branch, PossiblyInfiniteTree.from_branch, FiniteDegreeTree.get?, PossiblyInfiniteTree.get?, InfiniteTreeSkeleton.get]
            simp only [List.all_append, all_zero, List.all_cons, List.all_nil, Bool.and_true, decide_eq_true, ↓reduceIte, List.length_append, List.length_singleton]
            rw [PossiblyInfiniteList.tail_drop, PossiblyInfiniteList.head_drop] at trg_eq
            simp only [PossiblyInfiniteList.get?, InfiniteList.get] at trg_eq
            rw [← trg_eq]
            rw [List.getElem?_eq_getElem (by simp [List.length_zipIdx_with_lt, length_mapped_head_eq]), Option.some_inj, List.getElem_map, List.getElem_attach]
            rw [ChaseNode.mk.injEq, Subtype.mk.injEq]; constructor
            . rw [List.zipIdx_with_lt_getElem_fst_eq_getElem (by simp [length_mapped_head_eq])]; simp only [i_zero]
            . rw [List.zipIdx_with_lt_getElem_snd_eq_index (by simp [length_mapped_head_eq])]; rw [Option.some_inj, Sigma.mk.injEq]; simp only [true_and, heq_eq_eq]; apply Fin.eq_of_val_eq; rw [i_zero]
        | inr trg_ex =>
          apply Or.inr
          constructor
          . exact trg_ex.left
          . have trg_ex := trg_ex.right
            rw [← List.head?_eq_none_iff, List.head?_eq_getElem?, FiniteDegreeTree.get?_childNodes, FiniteDegreeTree.get?_childTrees, FiniteDegreeTree.FiniteDegreeTreeWithRoot.opt_to_tree_after_tree_to_opt, FiniteDegreeTree.drop_drop, FiniteDegreeTree.root_drop]
            simp only [FiniteDegreeTree.from_branch, PossiblyInfiniteTree.from_branch, FiniteDegreeTree.get?, PossiblyInfiniteTree.get?, InfiniteTreeSkeleton.get]
            simp only [List.all_append, all_zero, List.all_cons, List.all_nil, Bool.and_true, decide_eq_true, ↓reduceIte, List.length_append, List.length_singleton]
            rw [PossiblyInfiniteList.tail_drop, PossiblyInfiniteList.head_drop] at trg_ex
            exact trg_ex
    fairness_leaves := by
      rintro leaf ⟨node, node_eq, node_children⟩ trg
      simp only [FiniteDegreeTree.from_branch, PossiblyInfiniteTree.from_branch, PossiblyInfiniteTree.get?, InfiniteTreeSkeleton.get] at node_eq
      cases eq : node.all (fun e => e = 0) with
      | false => simp [eq] at node_eq
      | true =>
        simp only [eq, ↓reduceIte] at node_eq
        rcases cb.fairness trg with ⟨fairness_step, fairness⟩
        have : fairness_step ≤ node.length := by
          rw [PossiblyInfiniteList.head_eq, PossiblyInfiniteTree.get?_childNodes, PossiblyInfiniteTree.get?_childTrees, PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.opt_to_tree_after_tree_to_opt, PossiblyInfiniteTree.drop_drop, PossiblyInfiniteTree.root_drop] at node_children
          simp only [FiniteDegreeTree.from_branch, PossiblyInfiniteTree.from_branch, PossiblyInfiniteTree.get?, InfiniteTreeSkeleton.get] at node_children
          simp only [List.all_append, eq, List.all_cons, List.all_nil, Bool.and_true, decide_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at node_children
          apply Decidable.byContradiction
          intro lt; have le := Nat.succ_le_of_lt (Nat.lt_of_not_le lt)
          have := cb.branch.get?_eq_none_of_le_of_eq_none node_children _ le
          rw [PossiblyInfiniteList.head_drop] at fairness
          rw [this] at fairness
          simp [Option.is_some_and] at fairness
        cases Nat.lt_or_eq_of_le this with
        | inr eq =>
          have fairness := fairness.left
          rw [eq, PossiblyInfiniteList.head_drop] at fairness; simp only [PossiblyInfiniteList.get?, InfiniteList.get, node_eq, Option.is_some_and] at fairness
          exact fairness
        | inl lt =>
          have fairness := fairness.right (node.length - fairness_step - 1)
          rw [PossiblyInfiniteList.get?_tail, PossiblyInfiniteList.get?_drop] at fairness
          have : fairness_step + (node.length - fairness_step - 1).succ = node.length := by omega
          rw [this] at fairness
          simp only [PossiblyInfiniteList.get?, InfiniteList.get, node_eq, Option.is_none_or] at fairness
          exact fairness
    fairness_infinite_branches := by
      intro trg
      rcases cb.fairness trg with ⟨fairness_step, fairness⟩
      exists fairness_step + 1
      intro ns ns_length
      simp only [FiniteDegreeTree.from_branch, PossiblyInfiniteTree.from_branch, FiniteDegreeTree.get?, PossiblyInfiniteTree.get?, InfiniteTreeSkeleton.get]
      cases eq : ns.all (fun e => e = 0) with
      | false => simp [Option.is_none_or]
      | true =>
        simp only [↓reduceIte]
        have fairness := fairness.right (ns.length - fairness_step - 1)
        rw [PossiblyInfiniteList.get?_tail, PossiblyInfiniteList.get?_drop] at fairness
        have : fairness_step + (ns.length - fairness_step - 1).succ = ns.length := by omega
        rw [this] at fairness
        exact fairness
  }

theorem ChaseBranch.intoTree_same_result (cb : ChaseBranch obs kb) (deterministic : kb.isDeterministic) : (cb.intoTree deterministic).firstResult = cb.result := by
  unfold ChaseBranch.intoTree
  apply Set.ext
  intro f
  constructor
  . rintro ⟨n, h⟩
    simp only [FiniteDegreeTree.from_branch, PossiblyInfiniteTree.from_branch, FiniteDegreeTree.get?, PossiblyInfiniteTree.get?, InfiniteTreeSkeleton.get] at h
    rw [List.all_eq_val_repeat 0, List.length_repeat] at h
    simp only [↓reduceIte] at h
    exists n
  . rintro ⟨n, h⟩
    exists n
    simp only [FiniteDegreeTree.from_branch, PossiblyInfiniteTree.from_branch, FiniteDegreeTree.get?, PossiblyInfiniteTree.get?, InfiniteTreeSkeleton.get]
    rw [List.all_eq_val_repeat 0, List.length_repeat]
    simp only [↓reduceIte]
    exact h

theorem deterministicChaseBranchResultUniversallyModelsKb (cb : ChaseBranch obs kb) : kb.isDeterministic -> cb.result.universallyModelsKb kb := by
  intro deterministic
  rw [← cb.intoTree_same_result deterministic]
  apply deterministicChaseTreeResultUniversallyModelsKb
  exact deterministic

