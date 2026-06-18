/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.Termination.Basic
import ExistentialRules.ChaseSequence.Nontermination.CondenseGenerator
import ExistentialRules.ChaseSequence.Nontermination.SparseSubderivationGenerator

/-!
# RPC-like Non-Termination

We are going to formalize sufficient conditions for chase non-termination.
Mainly, we will introduce the necessary machinery from Restricted Prefix Cyclicity (RPC) [RPC]
but we also aim to generalize this to capture (Disjunctive) Model-Faithful Cyclicity ((D)MFC) [DMFA] [RMFA] at the same time.

SO FAR, WE ONLY HAVE A FEW VERY BASIC DEFINITIONS. THERE IS A LONG WAY TO GO.
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

section BasicDefinitions

/-- A `KnowledgeBase` never-terminates if none of its `ChaseTree`s terminates. -/
def KnowledgeBase.neverTerminates (kb : KnowledgeBase sig) (obs : ObsolescenceCondition sig) : Prop :=
  ∀ (ct : ChaseTree obs kb), ¬ ct.terminates

/-- Maybe this seems counterintuitive but a `RuleSet` never-terminates if for at least one `Database` the corresponding `KnowledgeBase.neverTerminates`. Asking this question for all Databases would be trivial, at least for the restricted chase, since for every rule set there is a database that satisfies all the rules directly and therefore only has terminating restricted chase trees. -/
def RuleSet.neverTerminates (rs : RuleSet sig) (obs : ObsolescenceCondition sig) : Prop :=
  ∃ (db : Database sig), { rules := rs, db := db : KnowledgeBase sig }.neverTerminates obs

end BasicDefinitions


/-- A trigger is unblockable if its result necessarily occurs in every derivation where the trigger is loaded. In the introducing paper this is called g-unblockable. -/
def Trigger.unblockable
    {obs : ObsolescenceCondition sig}
    (trg : Trigger obs.toLaxObsolescenceCondition)
    (disjIdx : Fin trg.mapped_head.length)
    (rules : RuleSet sig) : Prop :=
  ∀ td : TreeDerivation obs rules, ∀ node : td.NodeWithAddress, trg.loaded node.node.facts ->
  ∃ node2 : td.NodeWithAddress, node ≼ node2 ∧
  trg.mapped_head[disjIdx.val].toSet ⊆ node2.node.facts

/-- A `CyclicityDerivation` is an infinite list of `ChaseNode`s. We demand only that triggers are loaded, new terms keep being added (growing) and that triggers are unblockable. This is much different from a `ChaseDerivation` but intuitively, we can view a `CyclicityDerivation` as a very special non-continuous subderivation of a suitable `ChaseDerivation`. -/
structure CyclicityDerivation (obs : ObsolescenceCondition sig) (rules : RuleSet sig) extends ChaseDerivationSkeleton obs rules where
  triggers_loaded : ∀ n : Nat, ∀ before ∈ (branch.drop n).head,
    ∀ after ∈ (branch.drop n).tail.head, ∃ orig ∈ after.origin, orig.fst.val.loaded before.facts
  growing : ∀ n, ∃ m, ∃ t, (∀ node ∈ (branch.drop n).head, ¬ t ∈ node.facts.terms) ∧ (∃ node ∈ (branch.drop (n+m)).head, t ∈ node.facts.terms)
  unblockable : ∀ node ∈ branch, ∀ orig ∈ node.origin, (orig.fst.val.unblockable orig.snd rules)

namespace CyclicityDerivation

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig}

instance : Membership (ChaseNode obs rules) (CyclicityDerivation obs rules) where
  mem cd node := node ∈ cd.toChaseDerivationSkeleton

/-- Each suffix of the underlying `ChaseDerivationSkeleton` is itself a `CyclicityDerivation`. -/
def derivation_for_skeleton
    (cd : CyclicityDerivation obs rules)
    (l2 : ChaseDerivationSkeleton obs rules)
    (suffix : l2 <:+ cd.toChaseDerivationSkeleton) :
    CyclicityDerivation obs rules where
  branch := l2.branch
  isSome_head := l2.isSome_head
  triggers_exist := l2.triggers_exist
  triggers_loaded := by
    rw [ChaseDerivationSkeleton.IsSuffix_iff] at suffix
    rcases suffix with ⟨m, suffix⟩
    rw [← suffix]
    intro n
    have := cd.triggers_loaded (m + n)
    simp only [PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?_drop, PossiblyInfiniteList.tail_drop] at *
    exact this
  growing := by
    rw [ChaseDerivationSkeleton.IsSuffix_iff] at suffix
    rcases suffix with ⟨m, suffix⟩
    rw [← suffix]
    intro n
    have := cd.growing (m + n)
    simp only [PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?_drop, Nat.add_assoc] at *
    exact this
  unblockable := by
    intro node node_mem
    apply cd.unblockable
    exact ChaseDerivationSkeleton.mem_of_mem_suffix suffix _ node_mem

/-- We restate the `growing` property using vocabulary available for `ChaseDerivationSkeleton`s. -/
theorem growing' {cd : CyclicityDerivation obs rules} : ∀ node : cd.Node,
    ∃ node2 : cd.Node, node ≺ node2 ∧ ∃ t, ¬ t ∈ node.val.facts.terms ∧ t ∈ node2.val.facts.terms := by
  intro ⟨node, node_mem⟩
  rw [ChaseDerivationSkeleton.mem_iff] at node_mem
  rcases node_mem with ⟨n, node_eq⟩
  rcases cd.growing n with ⟨m, t, t_not_mem, ⟨node2, node2_mem, t_mem⟩⟩
  specialize t_not_mem node (by simpa using node_eq)

  let cd2 : ChaseDerivationSkeleton obs rules := cd.derivation_for_branch_suffix _ (cd.branch.IsSuffix_drop n) (by simp [node_eq])
  have cd2_suffix : cd2 <:+ cd.toChaseDerivationSkeleton := cd.branch.IsSuffix_drop n
  have node_head : node = cd2.head := by simp only [cd2, ChaseDerivationSkeleton.derivation_for_branch_suffix, ChaseDerivationSkeleton.head]; rcases Option.eq_some_iff_get_eq.mp node_eq with ⟨_, node_eq⟩; simp [← node_eq]
  have cd2_branch : cd2.branch = cd.branch.drop n := rfl
  have node2_mem : node2 ∈ (cd2.branch.drop m).head := by rw [cd2_branch]; grind

  let cd3 : ChaseDerivationSkeleton obs rules := cd2.derivation_for_branch_suffix _ (cd2.branch.IsSuffix_drop m) (by rw [node2_mem]; simp)
  have cd3_suffix : cd3 <:+ cd2 := cd2.branch.IsSuffix_drop m
  have node2_head : node2 = cd3.head := by simp only [cd3, ChaseDerivationSkeleton.derivation_for_branch_suffix, ChaseDerivationSkeleton.head]; rw [Option.mem_def] at node2_mem; simp [node2_mem]

  let node_cd2 : cd2.Node := ⟨node, by rw [node_head]; exact cd2.head_mem⟩
  let node2_cd2 : cd2.Node := ⟨node2, by rw [node2_head]; apply cd3.mem_of_mem_suffix cd3_suffix; exact cd3.head_mem⟩
  have prec : node_cd2 ≺ node2_cd2 := by
    constructor
    . exists cd2; constructor; exact PossiblyInfiniteList.IsSuffix_refl; constructor; rw [← node_head]; exact node2_cd2.property
    . intro contra; rw [Subtype.mk.injEq] at contra; apply t_not_mem; rw [contra]; exact t_mem

  exists node2_cd2.cast_suffix cd2_suffix; constructor
  . show node_cd2.cast_suffix cd2_suffix ≺ node2_cd2.cast_suffix cd2_suffix
    apply ChaseDerivationSkeleton.strict_predecessor_of_suffix
    exact prec
  . exists t

/-- Since the derivation is growing, a next node always exists. -/
theorem isSome_next {cd : CyclicityDerivation obs rules} : cd.toChaseDerivationSkeleton.next.isSome := by
  rcases growing' ⟨cd.head, cd.head_mem⟩ with ⟨n2, prec, _⟩
  have n2_mem := n2.property
  rw [ChaseDerivationSkeleton.mem_iff_eq_head_or_mem_tail] at n2_mem
  cases n2_mem with
  | inl n2_mem => exfalso; apply prec.right; rw [Subtype.mk.injEq]; exact Eq.symm n2_mem
  | inr n2_mem => rcases n2_mem with ⟨n2_mem, _⟩; exact n2_mem

/-- Lifting `ChaseDerivationSkeleton.next` to the `CyclicityDerivation`. -/
def next (cd : CyclicityDerivation obs rules) : ChaseNode obs rules := cd.toChaseDerivationSkeleton.next.get (isSome_next)

/-- The `next` node is a member. -/
@[grind <-]
theorem next_mem {cd : CyclicityDerivation obs rules} : cd.next ∈ cd := by
  apply ChaseDerivationSkeleton.next_mem_of_mem; simp [next]

/-- The origin of the `next` `ChaseNode` needs to be set. -/
@[grind <-]
theorem isSome_origin_next {cd : CyclicityDerivation obs rules} : cd.next.origin.isSome := by
  apply cd.toChaseDerivationSkeleton.isSome_origin_next; simp [next]

/-- The fact set of the `next` `ChaseNode` consists exactly of the facts from `head` and the result of the trigger that introduces `next`. -/
theorem facts_next {cd : CyclicityDerivation obs rules} :
    cd.next.facts = cd.head.facts ∪ (cd.next.origin_result cd.isSome_origin_next).toSet := by
  apply cd.toChaseDerivationSkeleton.facts_next; simp [next]

/-- The trigger used to derive `ChaseDerivationSkeleton.next` is loaded for `ChaseDerivationSkeleton.head`. -/
@[grind <-]
theorem loaded_trigger_origin_next {cd : CyclicityDerivation obs rules} :
    (cd.next.origin.get cd.isSome_origin_next).fst.val.loaded cd.head.facts := by
  have trg_loaded := cd.triggers_loaded 0 cd.head (by simp [ChaseDerivationSkeleton.head]) cd.next (by simp [next, ChaseDerivationSkeleton.next])
  rcases trg_loaded with ⟨orig, orig_mem, trg_loaded⟩
  rw [Option.mem_def] at orig_mem
  simp only [orig_mem, Option.get_some]
  exact trg_loaded

/-- The tail of a `CyclicityDerivation` is again a `CyclicityDerivation`. -/
def tail (cd : CyclicityDerivation obs rules) : CyclicityDerivation obs rules :=
  cd.derivation_for_skeleton (ChaseDerivationSkeleton.tail cd.toChaseDerivationSkeleton isSome_next) (cd.branch.IsSuffix_tail)

/-- The `ChaseDerivationSkeleton.head` of the `tail` is `ChaseDerivationSkeleton.next`. -/
@[simp, grind =]
theorem head_tail {cd : CyclicityDerivation obs rules} : cd.tail.head = cd.next := ChaseDerivationSkeleton.head_tail'

/-- The result of a `CyclicityDerivation` is infinite due to the `growing` property. -/
theorem result_infinite {cd : CyclicityDerivation obs rules} : ¬ cd.result.finite := by
  intro ⟨l, _, eq⟩
  have sub_res : l.toSet ⊆ cd.result := by intro e e_mem; rw [← eq, ← List.mem_toSet]; exact e_mem
  have res_sub : cd.result ⊆ l.toSet := by intro e e_mem; rw [List.mem_toSet, eq]; exact e_mem
  rcases cd.facts_mem_some_node_of_mem_result l sub_res with ⟨node, node_mem, sub⟩
  rcases growing' ⟨node, node_mem⟩ with ⟨node2, prec, ⟨t, t_not_mem, t_mem⟩⟩
  apply t_not_mem
  apply FactSet.terms_subset_of_subset sub
  apply FactSet.terms_subset_of_subset res_sub
  apply FactSet.terms_subset_of_subset (cd.facts_node_subset_result node2.val node2.property)
  exact t_mem

/-- Each `CyclicityDerivation` is infinite because it is `growing`. It might surprise that this is independant from the above result. However, note that we can only relate finiteness of the result and termination for proper ChaseBranches so corresponding results are not applicable here. -/
theorem infinite {cd : CyclicityDerivation obs rules} : ¬ cd.terminates := by
  intro contra
  rcases cd.has_last_node_of_terminates contra with ⟨node, node_last⟩
  rcases cd.growing' node with ⟨node2, prec, ⟨t, t_not_mem, t_mem⟩⟩
  apply t_not_mem
  apply FactSet.terms_subset_of_subset (cd.facts_node_subset_of_prec (node_last node2))
  exact t_mem

/-- In every `TreeDerivation` that starts on the same initial fact set as the `CyclicityDerivation`, there exists a branch that corresponds to the `CyclicityDerivation`, meaning that it has the same result. -/
theorem corresponding_tree_branch_exists {cd : CyclicityDerivation obs rules} (td : TreeDerivation obs rules) (same_start : cd.head.facts = td.root.facts) :
    ∃ deriv ∈ td.branches, cd.result ⊆ deriv.result := by
  let β := { pair : CyclicityDerivation obs rules × td.NodeWithAddress // pair.fst.head.facts ⊆ pair.snd.node.facts}
  let mapper : β -> td.NodeWithAddress := Prod.snd ∘ Subtype.val
  let start : β := ⟨(cd, TreeDerivation.NodeWithAddress.root td), by rw [same_start]; simp only [TreeDerivation.NodeWithAddress.root]; exact Set.subset_refl⟩
  let generator : β -> β := fun b =>
    let next := b.val.fst.next
    let origin := next.origin.get b.val.fst.isSome_origin_next
    have unblk := b.val.fst.unblockable next b.val.fst.next_mem origin (by simp [origin]) td b.val.snd (by
      have loaded : origin.fst.val.loaded b.val.fst.head.facts := b.val.fst.loaded_trigger_origin_next
      apply Set.subset_trans loaded
      exact b.property)
    let new_snd := Classical.choose unblk
    have new_snd_spec := Classical.choose_spec unblk
    ⟨(b.val.fst.tail, new_snd), by
      simp only
      rw [head_tail, b.val.fst.facts_next]
      rw [Set.union_subset_iff_both_subset]; constructor
      . apply Set.subset_trans b.property
        exact td.facts_node_subset_of_prec new_snd_spec.left
      . exact new_snd_spec.right⟩
  have different_value_exists : ∀ b, ∃ n, mapper (generator.repeat_fun n b) ≠ mapper b := by sorry
  let condensed_generator := Function.condense_generator generator mapper different_value_exists
  let deriv := td.generate_subderivation_from_sparse_of_total_generator start condensed_generator mapper (by
    suffices ∀ b n, mapper b ≼ mapper (generator.repeat_fun n b) by
      intro b; constructor
      . rcases Function.condense_generator_eq_repeat_generator generator mapper different_value_exists b with ⟨n, eq⟩
        unfold condensed_generator; rw [eq]; exact this b n
      . apply Ne.symm; apply Function.condense_generator_next_ne

    intro b n
    induction n with
    | zero => rw [Function.repeat_zero]; grind
    | succ n ih =>
      rw [Function.repeat_succ]
      apply TreeDerivation.predecessor_trans ih
      let next := (generator.repeat_fun n b).val.fst.next
      let origin := next.origin.get (generator.repeat_fun n b).val.fst.isSome_origin_next
      have unblk := (generator.repeat_fun n b).val.fst.unblockable next (generator.repeat_fun n b).val.fst.next_mem origin (by simp [origin]) td (generator.repeat_fun n b).val.snd (by
        have loaded : origin.fst.val.loaded (generator.repeat_fun n b).val.fst.head.facts := (generator.repeat_fun n b).val.fst.loaded_trigger_origin_next
        apply Set.subset_trans loaded
        exact (generator.repeat_fun n b).property)
      exact (Classical.choose_spec unblk).left)

  exists deriv; constructor
  . apply td.generate_subderivation_from_sparse_of_total_generator_mem_branches
    simp [mapper, start]
  . suffices ∀ node : cd.Node, ∃ (node2 : cd.Node), node ≼ node2 ∧ node2.val ∈ (InfiniteList.iterate start condensed_generator).map (fun e => e.val.fst.head) by
      intro f ⟨node, node_mem, f_mem⟩
      rcases this ⟨node, node_mem⟩ with ⟨node2, prec, node2_mem⟩
      rw [InfiniteList.mem_map] at node2_mem
      rcases node2_mem with ⟨b, b_mem, node2_mem⟩
      exists b.val.snd.node; constructor
      . rw [← deriv.mem_def]
        apply td.mem_generate_subderivation_from_sparse_of_total_generator_of_mem_original_generator
        exact b_mem
      . apply b.property
        rw [node2_mem]
        apply ChaseDerivationSkeleton.facts_node_subset_of_prec prec
        exact f_mem
    suffices ∀ i, ∃ j, (condensed_generator.repeat_fun j start).val.fst.branch <:+ cd.branch.drop i by
      intro ⟨node, node_mem⟩
      rcases ChaseDerivationSkeleton.mem_iff.mp node_mem with ⟨i, node_mem⟩
      rcases this i with ⟨j, suffix⟩
      exists ⟨(condensed_generator.repeat_fun j start).val.fst.head, by apply ChaseDerivationSkeleton.mem_of_mem_suffix (PossiblyInfiniteList.IsSuffix_trans suffix (PossiblyInfiniteList.IsSuffix_drop _)); exact ChaseDerivationSkeleton.head_mem⟩
      constructor
      . exists cd.derivation_for_branch_suffix (cd.branch.drop i) (PossiblyInfiniteList.IsSuffix_drop _) (by grind)
        constructor; exact PossiblyInfiniteList.IsSuffix_drop _
        constructor; simp only [ChaseDerivationSkeleton.derivation_for_branch_suffix, ChaseDerivationSkeleton.head]; grind
        simp only [ChaseDerivationSkeleton.derivation_for_branch_suffix]
        apply PossiblyInfiniteList.mem_of_mem_suffix suffix
        exact ChaseDerivationSkeleton.head_mem
      . rw [InfiniteList.mem_map]
        exists condensed_generator.repeat_fun j start; constructor
        . rw [InfiniteList.mem_iff]
          exists j
          rw [InfiniteList.get_iterate]
        . rfl
    suffices ∀ i, ∃ j, (condensed_generator.repeat_fun j start).val.fst.toChaseDerivationSkeleton <:+ (generator.repeat_fun i start).val.fst.toChaseDerivationSkeleton by
      suffices branch_eq : ∀ i, cd.branch.drop i = ((InfiniteList.iterate start generator).get i).val.fst.branch by
        intro i; rw [branch_eq i]; simp only [InfiniteList.get_iterate]; exact this i
      intro i
      induction i with
      | zero => rw [← InfiniteList.head_eq, InfiniteList.head_iterate]; simp [start]
      | succ i ih =>
        rw [InfiniteList.get_iterate] at ih
        rw [InfiniteList.get_succ_iterate]
        conv => right; right; right; right; right; fun; unfold generator
        simp only [tail, ChaseDerivationSkeleton.tail, derivation_for_skeleton, ChaseDerivationSkeleton.derivation_for_branch_suffix]
        rw [← ih]
        simp
    suffices ∀ b i, (generator.repeat_fun i b).val.fst.toChaseDerivationSkeleton <:+ b.val.fst.toChaseDerivationSkeleton by
      suffices condensed_exceeds_generator : ∀ b i, ∃ j k, (condensed_generator.repeat_fun j b) = (generator.repeat_fun (i+k) b) by
        intro i; rcases condensed_exceeds_generator start i with ⟨j, k, eq⟩
        exists j; rw [eq, Function.repeat_add, Function.repeat_swap]
        apply this
      intro b i
      induction i with
      | zero => exists 0, 0
      | succ i ih =>
        rcases ih with ⟨j, k, ih⟩
        rcases Function.condense_generator_eq_repeat_generator generator mapper different_value_exists (condensed_generator.repeat_fun j b) with ⟨k', eq⟩
        exists j.succ, k + k' - 1
        rw [Nat.add_assoc, Nat.add_comm 1 _, Nat.sub_one_add_one (by
          suffices k' ≠ 0 by grind
          intro contra
          rw [contra, Function.repeat_zero] at eq
          apply Function.condense_generator_next_ne (generator := generator) (mapper := mapper)
          rw [eq]
        )]
        rw [Function.repeat_succ]
        unfold condensed_generator
        rw [eq, ih]
        conv => right; rw [← Nat.add_assoc, Function.repeat_add, Function.repeat_swap]
    intro b i
    induction i with
    | zero =>  simp only [Function.repeat_zero]; exact PossiblyInfiniteList.IsSuffix_refl
    | succ i ih => rw [Function.repeat_succ]; exact PossiblyInfiniteList.IsSuffix_trans PossiblyInfiniteList.IsSuffix_tail ih

end CyclicityDerivation


/-- This is the CyclicitySequence from the RPC paper. For us, it is a `CyclicityDerivation` that starts on a database.  -/
structure CyclicityBranch (obs : ObsolescenceCondition sig) (kb : KnowledgeBase sig) extends CyclicityDerivation obs kb.rules where
  database_first : branch.head = some {
    facts := kb.db.toFactSet,
    origin := none,
    facts_contain_origin_result := by simp
  }

namespace CyclicityBranch

variable {obs : ObsolescenceCondition sig} {kb : KnowledgeBase sig}

/-- We restate the `database_first` condition in terms of the `CyclicityDerivation` vocabulary. -/
theorem database_first' {cb : CyclicityBranch obs kb} : cb.head = {
  facts := kb.db.toFactSet,
  origin := none,
  facts_contain_origin_result := by simp
} := by simp only [ChaseDerivationSkeleton.head, cb.database_first, Option.get_some]

/-- In every `ChaseTree`, there exists a branch that corresponds to the `CyclicityBranch`, meaning that it has the same result. -/
theorem corresponding_tree_branch_exists {cb : CyclicityBranch obs kb} (ct : ChaseTree obs kb) :
    ∃ branch : ChaseBranch obs kb, branch.toChaseDerivation ∈ ct.branches ∧ cb.result ⊆ branch.result := by
  rcases cb.toCyclicityDerivation.corresponding_tree_branch_exists ct.toTreeDerivation (by simp [cb.database_first', ct.database_first']) with ⟨cd, cd_mem, res_sub⟩
  exists ct.chaseBranch_for_branch cd_mem

/-- If a KB admist a `CyclicityBranch`, then its rule set `neverTerminates`. -/
theorem neverTerminates_of_cyclicityBranch {obs : ObsolescenceCondition sig} {kb : KnowledgeBase sig}
    (cb : CyclicityBranch obs kb) : kb.rules.neverTerminates obs := by
  exists kb.db
  intro ct terminates
  rcases cb.corresponding_tree_branch_exists ct with ⟨branch, branch_mem, res_sub⟩
  specialize terminates _ branch_mem
  apply cb.result_infinite
  apply Set.finite_of_subset_finite _ res_sub
  rw [← branch.terminates_iff_result_finite]
  exact terminates

end CyclicityBranch

