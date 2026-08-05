/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.Termination.Basic
import ExistentialRules.ChaseSequence.Nontermination.CondenseGenerator
import ExistentialRules.ChaseSequence.Nontermination.SparseSubderivationGenerator
public import ExistentialRules.ChaseSequence.Nontermination.Unblockability

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
def KnowledgeBase.neverTerminates (kb : KnowledgeBase sig) (obs : ObsolescenceCondition sig) (N : Type u) [CN : ChaseNode N obs kb.rules] : Prop :=
  ∀ (ct : ChaseTree N obs kb), ¬ ct.terminates

/-- Maybe this seems counterintuitive but a `RuleSet` never-terminates if for at least one `Database` the corresponding `KnowledgeBase.neverTerminates`. Asking this question for all Databases would be trivial, at least for the restricted chase, since for every rule set there is a database that satisfies all the rules directly and therefore only has terminating restricted chase trees. -/
def RuleSet.neverTerminates (rs : RuleSet sig) (obs : ObsolescenceCondition sig) (N : Type u) [CN : ChaseNode N obs rs] : Prop :=
  ∃ (db : Database sig), { rules := rs, db := db : KnowledgeBase sig }.neverTerminates obs N

end BasicDefinitions

/-- A `CyclicityDerivation` is an infinite list of `ChaseNode`s. We demand only that triggers are loaded, new terms keep being added (growing) and that triggers are unblockable. This is much different from a `ChaseDerivation` but intuitively, we can view a `CyclicityDerivation` as a very special non-continuous subderivation of a suitable `ChaseDerivation`. -/
structure CyclicityDerivation (obs : ObsolescenceCondition sig) (rules : RuleSet sig) (hc : HeadChoice sig)
    extends RegularChaseDerivationSkeleton obs rules where
  adheres_to_headChoice : ChaseDerivationSkeleton.adheres_to_headChoice toChaseDerivationSkeleton hc
  triggers_loaded : ∀ cd2, cd2 <:+ toChaseDerivationSkeleton -> ∀ next ∈ cd2.next, ∃ orig ∈ next.origin, orig.fst.val.loaded cd2.head.facts
  growing : ∀ cd2, cd2 <:+ toChaseDerivationSkeleton -> ∃ node ∈ cd2, ∃ t, ¬ t ∈ cd2.head.facts.terms ∧ t ∈ node.facts.terms
  unblockable : ∀ node ∈ toChaseDerivationSkeleton, ∀ orig ∈ node.origin, (orig.fst.val.unblockable rules hc)

namespace CyclicityDerivation

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig} {hc : HeadChoice sig}

instance : Membership (RegularChaseNode obs rules) (CyclicityDerivation obs rules hc) where
  mem cd node := node ∈ cd.toChaseDerivationSkeleton

/-- An element is a member of the derivation iff it occurs at some index in the underlying branch. -/
theorem mem_iff {cd : CyclicityDerivation obs rules hc} : ∀ {e}, e ∈ cd ↔ ∃ n, cd.branch.get? n = some e := ChaseDerivationSkeleton.mem_iff

/-- Each suffix of the underlying `ChaseDerivationSkeleton` is itself a `CyclicityDerivation`. -/
def derivation_for_skeleton
    (cd : CyclicityDerivation obs rules hc)
    (l2 : RegularChaseDerivationSkeleton obs rules)
    (suffix : l2 <:+ cd.toChaseDerivationSkeleton) :
    CyclicityDerivation obs rules hc where
  branch := l2.branch
  isSome_head := l2.isSome_head
  triggers_exist := l2.triggers_exist
  adheres_to_headChoice := by intro n n_mem; apply cd.adheres_to_headChoice; exact l2.mem_of_mem_suffix suffix _ n_mem
  triggers_loaded := by intro cd2 suffix2; apply cd.triggers_loaded; exact PossiblyInfiniteList.IsSuffix_trans suffix2 suffix
  growing := by intro cd2 suffix2; apply cd.growing; exact PossiblyInfiniteList.IsSuffix_trans suffix2 suffix
  unblockable := by
    intro node node_mem
    apply cd.unblockable
    exact ChaseDerivationSkeleton.mem_of_mem_suffix suffix _ node_mem

/-- We state a simplified version of the `growing` property. -/
theorem growing' {cd : CyclicityDerivation obs rules hc} : ∃ node ∈ cd, ∃ t, t ∉ cd.head.facts.terms ∧ t ∈ node.facts.terms :=
  cd.growing _ (cd.branch.IsSuffix_refl)

/-- Given a list of terms, we can find a suffix that contains a term that is not part of this list because of the growing property. This result is closest to the `growing'` statement. -/
theorem growing'_for_list (cd : CyclicityDerivation obs rules hc) (l : List (GroundTerm sig)) :
    ∃ node ∈ cd, ∃ t, t ∉ cd.head.facts.terms ∧ t ∈ node.facts.terms ∧ t ∉ l := by
  induction l generalizing cd with
  | nil => rcases cd.growing' with ⟨node, node_mem, t, t_not_mem, t_mem⟩; exact ⟨node, node_mem, t, t_not_mem, t_mem, by simp⟩
  | cons hd tl ih =>
    rcases ih cd with ⟨node, node_mem, t, t_not_mem, t_mem, t_not_mem_l⟩
    rcases cd.subderivation_of_node_mem node_mem with ⟨cd2, head_eq, suf⟩
    rcases ih (cd.derivation_for_skeleton cd2 suf) with ⟨node2, node2_mem, s, s_not_mem, s_mem, s_not_mem_l⟩
    cases Decidable.em (hd = t) with
    | inr ne => exists node; constructor; exact node_mem; exists t; grind
    | inl eq =>
      exists node2; constructor; exact cd2.mem_of_mem_suffix suf _ node2_mem
      exists s
      constructor
      . intro contra; apply s_not_mem; apply FactSet.terms_subset_of_subset (RegularChaseDerivationSkeleton.facts_node_subset_every_mem _ (ChaseDerivationSkeleton.mem_of_mem_suffix suf _ cd2.head_mem)); exact contra
      constructor; exact s_mem
      . intro contra; rw [List.mem_cons] at contra; cases contra with
        | inr contra => apply s_not_mem_l; exact contra
        | inl contra => apply s_not_mem; rw [contra, eq]; simp only [derivation_for_skeleton, head_eq]; exact t_mem

/-- We restate the `growing` property using predecessor vocabulary available for `ChaseDerivationSkeleton`s. -/
theorem growing'' {cd : CyclicityDerivation obs rules hc} : ∀ node : cd.Node,
    ∃ node2 : cd.Node, node ≺ node2 ∧ ∃ t, ¬ t ∈ node.val.facts.terms ∧ t ∈ node2.val.facts.terms := by
  intro ⟨node, node_mem⟩
  rw [ChaseDerivationSkeleton.mem_iff] at node_mem
  rcases node_mem with ⟨n, node_eq⟩

  let cd2 : RegularChaseDerivationSkeleton obs rules := cd.derivation_for_branch_suffix _ (cd.branch.IsSuffix_drop n) (by simp [node_eq])
  have cd2_suffix : cd2 <:+ cd.toChaseDerivationSkeleton := cd.branch.IsSuffix_drop n
  have node_head : node = cd2.head := by simp only [cd2, ChaseDerivationSkeleton.derivation_for_branch_suffix, ChaseDerivationSkeleton.head]; rcases Option.eq_some_iff_get_eq.mp node_eq with ⟨_, node_eq⟩; simp [← node_eq]

  rcases (cd.derivation_for_skeleton cd2 cd2_suffix).growing' with ⟨node2, node2_mem, t, t_not_mem, t_mem⟩
  simp only [derivation_for_skeleton] at node2_mem
  simp only [derivation_for_skeleton] at t_not_mem
  let node_cd2 : cd2.Node := ⟨node, by rw [node_head]; exact cd2.head_mem⟩
  let node2_cd2 : cd2.Node := ⟨node2, node2_mem⟩
  have prec : node_cd2 ≺ node2_cd2 := by
    constructor
    . exists cd2; constructor; exact PossiblyInfiniteList.IsSuffix_refl; constructor; rw [← node_head]; exact node2_cd2.property
    . intro contra; rw [Subtype.mk.injEq] at contra; apply t_not_mem; rw [← node_head, contra]; exact t_mem
  exists node2_cd2.cast_suffix cd2_suffix; constructor
  . show node_cd2.cast_suffix cd2_suffix ≺ node2_cd2.cast_suffix cd2_suffix
    apply ChaseDerivationSkeleton.strict_predecessor_of_suffix
    exact prec
  . exists t; simp only [node_head, t_not_mem, node2_cd2, not_false_iff, true_and]; exact t_mem

/-- Since the derivation is growing, a next node always exists. -/
theorem isSome_next {cd : CyclicityDerivation obs rules hc} : cd.toChaseDerivationSkeleton.next.isSome := by
  rcases growing'' ⟨cd.head, cd.head_mem⟩ with ⟨n2, prec, _⟩
  have n2_mem := n2.property
  rw [ChaseDerivationSkeleton.mem_iff_eq_head_or_mem_tail] at n2_mem
  cases n2_mem with
  | inl n2_mem => exfalso; apply prec.right; rw [Subtype.mk.injEq]; exact Eq.symm n2_mem
  | inr n2_mem => rcases n2_mem with ⟨n2_mem, _⟩; exact n2_mem

/-- Lifting `ChaseDerivationSkeleton.next` to the `CyclicityDerivation`. -/
def next (cd : CyclicityDerivation obs rules hc) : RegularChaseNode obs rules := cd.toChaseDerivationSkeleton.next.get (isSome_next)

/-- The `next` node is a member. -/
@[grind <-]
theorem next_mem {cd : CyclicityDerivation obs rules hc} : cd.next ∈ cd := by
  apply ChaseDerivationSkeleton.next_mem_of_mem; simp [next]

/-- The origin of the `next` `ChaseNode` needs to be set. -/
@[grind <-]
theorem isSome_origin_next {cd : CyclicityDerivation obs rules hc} : cd.next.origin.isSome := by
  apply cd.toChaseDerivationSkeleton.isSome_origin_next; simp [next]

/-- The fact set of the `next` `ChaseNode` consists exactly of the facts from `head` and the result of the trigger that introduces `next`. -/
theorem facts_next {cd : CyclicityDerivation obs rules hc} :
    cd.next.facts = cd.head.facts ∪ (ChaseNode.origin_result cd.next cd.isSome_origin_next).toSet := by
  apply cd.toChaseDerivationSkeleton.facts_next; simp [next]

/-- The trigger used to derive `ChaseDerivationSkeleton.next` is loaded for `ChaseDerivationSkeleton.head`. -/
@[grind <-]
theorem loaded_trigger_origin_next {cd : CyclicityDerivation obs rules hc} :
    (cd.next.origin.get cd.isSome_origin_next).fst.val.loaded cd.head.facts := by
  have trg_loaded := cd.triggers_loaded _ (cd.branch.IsSuffix_refl) cd.next (by simp [next, ChaseDerivationSkeleton.next])
  rcases trg_loaded with ⟨orig, orig_mem, trg_loaded⟩
  rw [Option.mem_def] at orig_mem
  simp only [orig_mem, Option.get_some]
  exact trg_loaded

/-- The tail of a `CyclicityDerivation` is again a `CyclicityDerivation`. -/
def tail (cd : CyclicityDerivation obs rules hc) : CyclicityDerivation obs rules hc :=
  cd.derivation_for_skeleton (ChaseDerivationSkeleton.tail cd.toChaseDerivationSkeleton isSome_next) (cd.branch.IsSuffix_tail)

/-- The `ChaseDerivationSkeleton.head` of the `tail` is `ChaseDerivationSkeleton.next`. -/
@[simp, grind =]
theorem head_tail {cd : CyclicityDerivation obs rules hc} : cd.tail.head = cd.next := ChaseDerivationSkeleton.head_tail'

/-- We define a shortcut for `RegularChaseDerivationSkeleton.result`. -/
abbrev result (cd : CyclicityDerivation obs rules hc) := RegularChaseDerivationSkeleton.result cd.toChaseDerivationSkeleton

/-- The result of a `CyclicityDerivation` is infinite due to the `growing` property. -/
theorem result_infinite {cd : CyclicityDerivation obs rules hc} : ¬ cd.result.finite := by
  intro ⟨l, _, eq⟩
  have sub_res : l.toSet ⊆ cd.result := by intro e e_mem; rw [← eq, ← List.mem_toSet]; exact e_mem
  have res_sub : cd.result ⊆ l.toSet := by intro e e_mem; rw [List.mem_toSet, eq]; exact e_mem
  rcases RegularChaseDerivationSkeleton.facts_mem_some_node_of_mem_result l sub_res with ⟨node, node_mem, sub⟩
  rcases growing'' ⟨node, node_mem⟩ with ⟨node2, prec, ⟨t, t_not_mem, t_mem⟩⟩
  apply t_not_mem
  apply FactSet.terms_subset_of_subset sub
  apply FactSet.terms_subset_of_subset res_sub
  apply FactSet.terms_subset_of_subset (RegularChaseDerivationSkeleton.facts_node_subset_result node2.val node2.property)
  exact t_mem

/-- Each `CyclicityDerivation` is infinite because it is `growing`. It might surprise that this is independant from the above result. However, note that we can only relate finiteness of the result and termination for proper ChaseBranches so corresponding results are not applicable here. -/
theorem infinite {cd : CyclicityDerivation obs rules hc} : ¬ cd.terminates := by
  intro contra
  let node : cd.Node := ⟨cd.last contra, cd.last_mem contra⟩
  rcases cd.growing'' node with ⟨node2, prec, ⟨t, t_not_mem, t_mem⟩⟩
  apply t_not_mem
  apply FactSet.terms_subset_of_subset (RegularChaseDerivationSkeleton.facts_node_subset_of_prec (cd.each_prec_last contra node2))
  exact t_mem

/-- For each node in the `CyclicityDerivation`, there is a node in the `subderivation_for_headChoice` for every `TreeDerivation` subsumes the facts. -/
theorem mem_subderivation_for_headChoice_of_mem {cd : CyclicityDerivation obs rules hc}
    (td : RegularTreeDerivation obs rules) (same_start : cd.head.facts = td.root.facts) :
    ∀ node ∈ cd, ∃ node' ∈ td.subderivation_for_headChoice hc, node.facts ⊆ node'.facts := by
  intro node node_mem; let node : cd.Node := ⟨node, node_mem⟩; show ∃ node' ∈ td.subderivation_for_headChoice hc, node.val.facts ⊆ node'.facts
  induction node using cd.mem_rec with
  | head =>
    exists (td.subderivation_for_headChoice hc).head; constructor; exact ChaseDerivationSkeleton.head_mem
    rw [td.head_subderivation_for_headChoice, same_start]; exact Set.subset_refl
  | step cd2 suf ih next next_mem =>
    rcases ih with ⟨node', node'_mem, sub⟩
    let cd2' : CyclicityDerivation obs rules hc := cd.derivation_for_skeleton cd2 suf
    have next_eq : next = cd2'.next := by simp only [CyclicityDerivation.next, cd2', derivation_for_skeleton]; rw [Option.mem_def] at next_mem; simp [next_mem]
    let orig := next.origin.get (cd2.isSome_origin_next next_mem)
    rcases cd2'.unblockable next (cd2'.next_mem_of_mem _ next_mem) orig (by simp [orig]) td ⟨node', node'_mem⟩ (by apply Set.subset_trans _ sub; simp only [orig, next_eq]; exact cd2'.loaded_trigger_origin_next) with ⟨node2, node2_succ, next_result_sub⟩
    exists node2.val; constructor; exact node2.property
    have := cd2.facts_next next_mem
    rw [← next.ingoingFacts_eq, cd2.facts_next next_mem]
    rw [Set.union_subset_iff_both_subset]; constructor
    . rw [cd2.head.outgoingFacts_eq]; apply Set.subset_trans sub
      exact RegularChaseDerivationSkeleton.facts_node_subset_of_prec node2_succ
    . have index_eq : (hc orig.fst.val).val = orig.snd.val := by
        rw [cd2'.adheres_to_headChoice _ (cd2'.next_mem_of_mem _ next_mem) orig (by simp [orig, ChaseNode.origin])]
      rw [ChaseNode.origin_result_eq (cd2.isSome_origin_next next_mem) (trg := orig.fst.val) rfl index_eq]
      exact next_result_sub

/-- The result of a `CyclicityDerivation` is a subset of the result of the `subderivation_for_headChoice` for every `TreeDerivation`. -/
theorem result_subset_result_subderivation_for_headChoice {cd : CyclicityDerivation obs rules hc}
    (td : RegularTreeDerivation obs rules) (same_start : cd.head.facts = td.root.facts) :
    cd.result ⊆ RegularChaseDerivation.result (td.subderivation_for_headChoice hc) := by
  intro f ⟨node, node_mem, f_mem⟩
  rcases cd.mem_subderivation_for_headChoice_of_mem td same_start node node_mem with ⟨node', node'_mem, sub⟩
  exists node'; constructor; exact node'_mem; apply sub; exact f_mem

end CyclicityDerivation


/-- This is the CyclicitySequence from the RPC paper. For us, it is a `CyclicityDerivation` that starts on a database.  -/
structure CyclicityBranch (obs : ObsolescenceCondition sig) (kb : KnowledgeBase sig) (hc : HeadChoice sig) extends CyclicityDerivation obs kb.rules hc where
  database_first :
    toChaseDerivationSkeleton.head.facts = kb.db.toFactSet ∧
    toChaseDerivationSkeleton.head.origin = none

namespace CyclicityBranch

variable {obs : ObsolescenceCondition sig} {kb : KnowledgeBase sig} {hc : HeadChoice sig}

/-- The result of a `CyclicityBranch` is a subset of the result of the `subderivation_for_headChoice` for every `ChaseTree`. -/
theorem result_subset_result_subderivation_for_headChoice {cb : CyclicityBranch obs kb hc} (ct : RegularChaseTree obs kb) :
    cb.result ⊆ RegularChaseBranch.result (ct.subderivation_for_headChoice hc) := by
  apply CyclicityDerivation.result_subset_result_subderivation_for_headChoice
  rw [cb.database_first.left, ← RegularChaseNode.outgoingFacts_eq, ct.database_first.right.left]

/-- If a KB admist a `CyclicityBranch`, then its rule set `neverTerminates`. -/
theorem neverTerminates_of_cyclicityBranch {obs : ObsolescenceCondition sig} {kb : KnowledgeBase sig}
    (cb : CyclicityBranch obs kb hc) : kb.rules.neverTerminates obs (RegularChaseNode obs kb.rules) := by
  exists kb.db
  intro ct terminates
  let branch : RegularChaseBranch obs kb := ct.subderivation_for_headChoice hc
  specialize terminates branch.toChaseDerivation (ct.subderivation_for_headChoice_mem_branches)
  apply cb.result_infinite
  apply Set.finite_of_subset_finite _ (cb.result_subset_result_subderivation_for_headChoice ct)
  rw [← branch.terminates_iff_result_finite]
  exact terminates

end CyclicityBranch

