import BasicLeanDatastructures.List.Repeat

import ExistentialRules.ChaseSequence.ChaseTree
import ExistentialRules.ChaseSequence.Universality

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace TreeDerivation

  variable {obs : ObsoletenessCondition sig} {rules : RuleSet sig}

  def firstBranch (td : TreeDerivation obs rules) : ChaseDerivation obs rules :=
    let start : Option (TreeDerivation obs rules) := some td
    let generator (td : TreeDerivation obs rules) : Option (TreeDerivation obs rules) := td.childTrees[0]?
    let nodes : PossiblyInfiniteList (ChaseNode obs rules) := FiniteDegreeTree.generate_branch start generator (fun res => res.toFiniteDegreeTreeWithRoot)
    have nodes_mem : nodes ∈ td.tree.branches := by
      apply FiniteDegreeTree.generate_branch_mem_branches
      . intro prev res res_mem
        conv => left; simp only [TreeDerivation.toFiniteDegreeTreeWithRoot]
        rw [← TreeDerivation.mem_childTrees_iff]
        apply List.mem_of_getElem?
        exact res_mem
      . intro prev eq_none
        simp only [TreeDerivation.toFiniteDegreeTreeWithRoot]
        simp only [generator, List.getElem?_eq_none_iff, Nat.le_zero, TreeDerivation.childTrees, List.length_map, List.length_attach] at eq_none
        rw [List.eq_nil_iff_length_eq_zero]
        exact eq_none
      . simp [start]
    td.derivation_for_branch _ nodes_mem

  def firstResult (td : TreeDerivation obs rules) : FactSet sig := td.firstBranch.result

  theorem firstResult_mem_result {td : TreeDerivation obs rules} : td.firstResult ∈ td.result := by
    exists td.firstBranch; constructor;
    . simp only [firstBranch]; exact td.derivation_for_branch_mem_branches
    . rfl

  theorem branches_eq_firstBranch_of_determinsitic {td : TreeDerivation obs rules} (det : rules.isDeterministic) : td.branches = fun b => b = td.firstBranch := by
    apply Set.ext
    intro deriv
    conv => right; simp only [Membership.mem]
    constructor
    . intro deriv_mem
      simp only [Membership.mem, TreeDerivation.branches] at deriv_mem
      rw [ChaseDerivation.mk.injEq]
      apply PossiblyInfiniteList.ext
      intro n
      induction n generalizing td deriv with
      | zero =>
        rw [FiniteDegreeTree.branches_eq] at deriv_mem
        rw [← PossiblyInfiniteList.head_eq, ← PossiblyInfiniteList.head_eq]
        simp only [firstBranch, derivation_for_branch, toFiniteDegreeTreeWithRoot]
        rw [FiniteDegreeTree.head_generate_branch, Option.map_some]
        simp only [Option.some_get]
        rw [deriv_mem.left]
      | succ n ih =>
        rw [FiniteDegreeTree.branches_eq] at deriv_mem
        rw [← PossiblyInfiniteList.get?_tail, ← PossiblyInfiniteList.get?_tail]
        cases eq_next : deriv.next with
        | none =>
          have contra : ¬∃ (trg : RTrigger obs rules), trg.val.active deriv.head.facts := by rw [← deriv.isSome_next_iff_trg_ex, Option.isSome_iff_ne_none]; intro h; apply h; exact eq_next
          have head_eq_head : deriv.head = td.firstBranch.head := by
            simp only [firstBranch, derivation_for_branch, toFiniteDegreeTreeWithRoot, ChaseDerivation.head]
            apply Option.get_congr
            rw [FiniteDegreeTree.head_generate_branch, Option.map_some]
            simp only [Option.some_get]
            exact deriv_mem.left
          have : td.firstBranch.next = none := by
            rw [head_eq_head] at contra
            apply Decidable.byContradiction
            intro contra'
            apply contra
            rw [← td.firstBranch.isSome_next_iff_trg_ex, Option.isSome_iff_ne_none]
            exact contra'
          unfold ChaseDerivation.next at eq_next
          unfold ChaseDerivation.next at this
          rw [← PossiblyInfiniteList.empty_iff_head_none] at eq_next
          rw [← PossiblyInfiniteList.empty_iff_head_none] at this
          rw [eq_next, this]
        | some next =>
          have next_isSome : deriv.next.isSome := by rw [Option.isSome_iff_exists]; exists next
          cases deriv_mem.right with
          | inl deriv_mem_r => rw [PossiblyInfiniteList.empty_iff_head_none] at deriv_mem_r ;simp [ChaseDerivation.next, deriv_mem_r.right] at next_isSome
          | inr deriv_mem_r =>
            rcases deriv_mem_r with ⟨child, child_mem, tail_mem⟩
            have one_childTree : td.childTrees.length = 1 := by
              have head_eq_root : deriv.head = td.root := by simp [ChaseDerivation.head, root, deriv_mem.left]
              have trg_ex := td.triggers_exist []
              rw [FiniteDegreeTree.drop_nil] at trg_ex
              specialize trg_ex td.root (by simp [root])
              cases trg_ex with
              | inr trg_ex => rw [ChaseDerivation.isSome_next_iff_trg_ex] at next_isSome; apply False.elim; apply trg_ex.left; rw [← head_eq_root]; exact next_isSome
              | inl trg_ex =>
                rcases trg_ex with ⟨trg, act, children_eq⟩
                have : td.childNodes.length = 1 := by
                  unfold childNodes
                  rw [children_eq, List.length_map, List.length_attach, List.length_zipIdx_with_lt, PreTrigger.length_mapped_head]
                  have := det trg.val.rule trg.property
                  simp only [Rule.isDeterministic, decide_eq_true_eq] at this
                  exact this
                rw [childNodes_eq, List.length_map] at this
                exact this
            have one_childTree' : td.tree.childTrees.length = 1 := by
              simp only [childTrees, List.length_map, List.length_attach] at one_childTree
              exact one_childTree
            have : child = td.tree.childTrees[0]'(by simp [one_childTree']) := by
              rw [List.mem_iff_getElem] at child_mem
              rcases child_mem with ⟨i, h, child_mem⟩
              rw [one_childTree'] at h
              simp only [Nat.lt_one_iff] at h
              simp only [h] at child_mem
              apply Eq.symm; exact child_mem
            have : (deriv.tail next_isSome) ∈ (td.childTrees[0]'(by simp [one_childTree])).branches := by
              simp only [ChaseDerivation.tail, ChaseDerivation.derivation_for_branch_suffix, Membership.mem]
              simp only [branches, childTrees, List.getElem_map, List.getElem_attach, derivation_for_suffix]
              rw [← this]
              exact tail_mem
            specialize ih (deriv.tail next_isSome) this
            simp only [ChaseDerivation.tail, ChaseDerivation.derivation_for_branch_suffix] at ih
            simp only [firstBranch, derivation_for_branch]
            rw [ih, FiniteDegreeTree.tail_generate_branch, Option.bind_some]
            simp only [firstBranch, derivation_for_branch]
            congr
            simp
    . intro eq; rw [eq]; simp only [firstBranch]; exact td.derivation_for_branch_mem_branches

end TreeDerivation

namespace ChaseTree

  variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

  theorem deterministicChaseTreeResultUniversallyModelsKb {ct : ChaseTree obs kb} : kb.isDeterministic -> ct.firstResult.universallyModelsKb kb := by
    intro det
    constructor
    . apply ChaseTree.result_models_kb; exact ct.firstResult_mem_result
    . intro m m_is_model
      rcases chaseTreeResultIsUniversal ct m m_is_model with ⟨res, hom, ⟨b, b_mem, res_mem⟩, hom_is_hom⟩
      rw [TreeDerivation.branches_eq_firstBranch_of_determinsitic det] at b_mem
      unfold TreeDerivation.firstResult
      rw [← b_mem, res_mem]
      exact ⟨_, hom_is_hom⟩

end ChaseTree

namespace ChaseDerivation

  variable {obs : ObsoletenessCondition sig} {rules : RuleSet sig}

  def intoTree (cd : ChaseDerivation obs rules) (deterministic : rules.isDeterministic) : TreeDerivation obs rules :=
    {
      tree := FiniteDegreeTree.from_branch cd.branch
      isSome_root := cd.isSome_head
      triggers_exist := by
        intro ns node eq
        simp only [FiniteDegreeTree.from_branch, PossiblyInfiniteTree.from_branch, FiniteDegreeTree.root_drop, FiniteDegreeTree.get?, PossiblyInfiniteTree.get?, InfiniteTreeSkeleton.get] at eq
        cases all_zero : ns.all (fun e => e = 0) with
        | false => simp [all_zero] at eq
        | true =>
          simp only [all_zero, ↓reduceIte] at eq
          have trg_ex := cd.triggers_exist ns.length
          simp only [PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?, InfiniteList.get] at trg_ex
          specialize trg_ex _ eq
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
              rw [trg_eq]
              rw [List.getElem?_eq_getElem (by simp [List.length_zipIdx_with_lt, length_mapped_head_eq]), Option.some_inj, List.getElem_map, List.getElem_attach]
              rw [ChaseNode.mk.injEq]; constructor
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
          rcases cd.fairness trg with ⟨fairness_step, fairness⟩
          have : fairness_step ≤ node.length := by
            rw [PossiblyInfiniteList.head_eq, PossiblyInfiniteTree.get?_childNodes, PossiblyInfiniteTree.get?_childTrees, PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.opt_to_tree_after_tree_to_opt, PossiblyInfiniteTree.drop_drop, PossiblyInfiniteTree.root_drop] at node_children
            simp only [FiniteDegreeTree.from_branch, PossiblyInfiniteTree.from_branch, PossiblyInfiniteTree.get?, InfiniteTreeSkeleton.get] at node_children
            simp only [List.all_append, eq, List.all_cons, List.all_nil, Bool.and_true, decide_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at node_children
            apply Decidable.byContradiction
            intro lt; have le := Nat.succ_le_of_lt (Nat.lt_of_not_le lt)
            have := cd.branch.get?_eq_none_of_le_of_eq_none node_children _ le
            rw [PossiblyInfiniteList.head_drop] at fairness
            rw [this] at fairness
            simp at fairness
          cases Nat.lt_or_eq_of_le this with
          | inr eq =>
            have fairness := fairness.left
            rw [eq, PossiblyInfiniteList.head_drop] at fairness; simp only [PossiblyInfiniteList.get?, InfiniteList.get, node_eq] at fairness
            rcases fairness with ⟨_, eq, fairness⟩
            rw [Option.mem_def, Option.some_inj] at eq; rw [eq]
            exact fairness
          | inl lt =>
            have fairness := fairness.right (node.length - fairness_step - 1)
            rw [PossiblyInfiniteList.get?_tail, PossiblyInfiniteList.get?_drop] at fairness
            have : fairness_step + (node.length - fairness_step - 1).succ = node.length := by omega
            rw [this] at fairness
            simp only [PossiblyInfiniteList.get?, InfiniteList.get, node_eq] at fairness
            apply fairness
            simp
      fairness_infinite_branches := by
        intro trg
        rcases cd.fairness trg with ⟨fairness_step, fairness⟩
        exists fairness_step + 1
        intro ns ns_length
        simp only [FiniteDegreeTree.from_branch, PossiblyInfiniteTree.from_branch, FiniteDegreeTree.get?, PossiblyInfiniteTree.get?, InfiniteTreeSkeleton.get]
        cases eq : ns.all (fun e => e = 0) with
        | false => simp
        | true =>
          simp only [↓reduceIte]
          have fairness := fairness.right (ns.length - fairness_step - 1)
          rw [PossiblyInfiniteList.get?_tail, PossiblyInfiniteList.get?_drop] at fairness
          have : fairness_step + (ns.length - fairness_step - 1).succ = ns.length := by omega
          rw [this] at fairness
          exact fairness
    }

  theorem firstBranch_intoTree_eq_self (cd : ChaseDerivation obs rules) (deterministic : rules.isDeterministic) : (cd.intoTree deterministic).firstBranch = cd := by
    rw [ChaseDerivation.mk.injEq]
    apply PossiblyInfiniteList.ext
    intro n
    induction n generalizing cd with
    | zero =>
      simp only [intoTree, TreeDerivation.firstBranch, TreeDerivation.derivation_for_branch, FiniteDegreeTree.from_branch, PossiblyInfiniteTree.from_branch]
      rw [← PossiblyInfiniteList.head_eq, FiniteDegreeTree.head_generate_branch, Option.map_some]; simp only [TreeDerivation.toFiniteDegreeTreeWithRoot, Option.some_get]; rfl
    | succ n ih =>
      rw [← PossiblyInfiniteList.get?_tail, ← PossiblyInfiniteList.get?_tail]
      cases eq_next : cd.next with
      | none =>
        have : (cd.intoTree deterministic).firstBranch.next = none := by
          simp only [intoTree, TreeDerivation.firstBranch, TreeDerivation.derivation_for_branch, FiniteDegreeTree.from_branch, PossiblyInfiniteTree.from_branch]
          unfold next
          simp only [FiniteDegreeTree.tail_generate_branch, FiniteDegreeTree.head_generate_branch, Option.bind_some, Option.map_eq_none_iff]
          simp only [TreeDerivation.childTrees, List.getElem?_map, List.getElem?_attach, Option.map_eq_none_iff, Option.pmap_eq_none_iff]
          rw [FiniteDegreeTree.get?_childTrees, FiniteDegreeTree.FiniteDegreeTreeWithRoot.tree_to_opt_none_iff, FiniteDegreeTree.root_drop]
          simp only [FiniteDegreeTree.get?, PossiblyInfiniteTree.get?, InfiniteTreeSkeleton.get]
          simp only [next, PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?_tail] at eq_next
          simp only [PossiblyInfiniteList.get?, InfiniteList.get] at eq_next
          simp [eq_next]
        unfold ChaseDerivation.next at eq_next
        unfold ChaseDerivation.next at this
        rw [← PossiblyInfiniteList.empty_iff_head_none] at eq_next
        rw [← PossiblyInfiniteList.empty_iff_head_none] at this
        rw [eq_next, this]
      | some next =>
        have next_isSome : cd.next.isSome := by rw [Option.isSome_iff_exists]; exists next
        simp only [intoTree, TreeDerivation.firstBranch, TreeDerivation.derivation_for_branch, FiniteDegreeTree.from_branch, PossiblyInfiniteTree.from_branch]
        specialize ih (cd.tail next_isSome)
        simp only [ChaseDerivation.tail, ChaseDerivation.derivation_for_branch_suffix] at ih
        rw [← ih, FiniteDegreeTree.tail_generate_branch]
        congr
        simp only [Option.bind_some]
        have : (cd.intoTree deterministic).childTrees[0]? = some ((cd.tail next_isSome).intoTree deterministic) := by
          simp only [TreeDerivation.childTrees, List.getElem?_map, List.getElem?_attach, Option.map_pmap, Option.pmap_eq_some_iff]
          have : (cd.intoTree deterministic).tree.childTrees[0]? = some ((cd.tail next_isSome).intoTree deterministic).toFiniteDegreeTreeWithRoot := by
            rw [FiniteDegreeTree.get?_childTrees, FiniteDegreeTree.FiniteDegreeTreeWithRoot.tree_to_opt_some_iff]
            simp only [TreeDerivation.toFiniteDegreeTreeWithRoot, intoTree, FiniteDegreeTree.from_branch, PossiblyInfiniteTree.from_branch, FiniteDegreeTree.root_drop]
            constructor
            . apply FiniteDegreeTree.ext; intro ns; rw [FiniteDegreeTree.get?_drop]
              simp only [FiniteDegreeTree.get?, PossiblyInfiniteTree.get?, InfiniteTreeSkeleton.get]
              simp only [tail, derivation_for_branch_suffix, PossiblyInfiniteList.tail, InfiniteList.tail, InfiniteList.get]
              simp
            . simp only [FiniteDegreeTree.get?, PossiblyInfiniteTree.get?, InfiniteTreeSkeleton.get]
              simp only [ChaseDerivation.next, PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?_tail] at next_isSome
              simp only [PossiblyInfiniteList.get?, InfiniteList.get] at next_isSome
              simp [next_isSome]
          exists ((cd.tail next_isSome).intoTree deterministic).toFiniteDegreeTreeWithRoot
          exists (by rw [List.getElem?_eq_some_iff] at this; rcases this with ⟨_, this⟩; simp [← this])
        conv at this => left; simp only [intoTree, FiniteDegreeTree.from_branch, PossiblyInfiniteTree.from_branch]
        rw [this, Option.some_inj]
        rfl

  theorem firstResult_intoTree_eq_result (cd : ChaseDerivation obs rules) (deterministic : rules.isDeterministic) : (cd.intoTree deterministic).firstResult = cd.result := by
    unfold TreeDerivation.firstResult; rw [cd.firstBranch_intoTree_eq_self deterministic]

end ChaseDerivation

namespace ChaseBranch

  variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

  def intoTree (cb : ChaseBranch obs kb) (deterministic : kb.isDeterministic) : ChaseTree obs kb :=
    let td := cb.toChaseDerivation.intoTree deterministic
    {
      tree := td.tree
      isSome_root := td.isSome_root
      triggers_exist := td.triggers_exist
      fairness_leaves := td.fairness_leaves
      fairness_infinite_branches := td.fairness_infinite_branches
      database_first := cb.database_first
    }

  theorem deterministicChaseBranchResultUniversallyModelsKb (cb : ChaseBranch obs kb) : kb.isDeterministic -> cb.result.universallyModelsKb kb := by
    intro det
    rw [← ChaseDerivation.firstResult_intoTree_eq_result cb.toChaseDerivation det]
    exact (cb.intoTree det).deterministicChaseTreeResultUniversallyModelsKb det

end ChaseBranch

