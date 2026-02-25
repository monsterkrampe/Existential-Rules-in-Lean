import ExistentialRules.ChaseSequence.Termination.Basic

/-!
# RPC-like Non-Termination

TODO
-/

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

section BasicDefinitions

/-- A `KnowledgeBase` never-terminates if none of its `ChaseTree`s terminates. -/
def KnowledgeBase.neverTerminates (kb : KnowledgeBase sig) (obs : ObsoletenessCondition sig) : Prop :=
  ∀ (ct : ChaseTree obs kb), ¬ ct.terminates

/-- Maybe this seems counterintuitive but a `RuleSet` never-terminates if for at least one `Database` the corresponding `KnowledgeBase.neverTerminates`. Asking this question for all Databases would be trivial, at least for the restricted chase, since for every rule set there is a database that satisfies all the rules directly and therefore only has terminating restricted chase trees. -/
def RuleSet.neverTerminates (rs : RuleSet sig) (obs : ObsoletenessCondition sig) : Prop :=
  ∃ (db : Database sig), { rules := rs, db := db : KnowledgeBase sig }.neverTerminates obs

end BasicDefinitions


/-- TODO -/
def Trigger.unblockable
    {obs : ObsoletenessCondition sig}
    (trg : Trigger obs.toLaxObsoletenessCondition)
    (disjIdx : Fin trg.mapped_head.length)
    (rules : RuleSet sig) : Prop :=
  ∀ td : TreeDerivation obs rules, ∀ node : td.NodeWithAddress, trg.loaded node.node.facts ->
  ∃ node2 : td.NodeWithAddress, node ≼ node2 ∧
  trg.mapped_head[disjIdx.val].toSet ⊆ node2.node.facts

/-- TODO -/
structure CyclicityDerivation (obs : ObsoletenessCondition sig) (rules : RuleSet sig) extends ChaseDerivationSkeleton obs rules where
  triggers_loaded : ∀ n : Nat, ∀ before ∈ (branch.drop n).head,
    ∀ after ∈ (branch.drop n).tail.head, ∃ orig ∈ after.origin, orig.fst.val.loaded before.facts
  growing : ∀ n, ∃ m, ∃ t, (∀ node ∈ (branch.drop n).head, ¬ t ∈ node.facts.terms) ∧ (∃ node ∈ (branch.drop (n+m)).head, t ∈ node.facts.terms)
  unblockable : ∀ node ∈ branch, ∀ orig ∈ node.origin, (orig.fst.val.unblockable orig.snd rules)

namespace CyclicityDerivation

variable {obs : ObsoletenessCondition sig} {rules : RuleSet sig}

instance : Membership (ChaseNode obs rules) (CyclicityDerivation obs rules) where
  mem cd node := node ∈ cd.toChaseDerivationSkeleton

theorem growing' {cd : CyclicityDerivation obs rules} : ∀ node : cd.Node,
    ∃ node2 : cd.Node, node ≺ node2 ∧ ∃ t, ¬ t ∈ node.val.facts.terms ∧ t ∈ node2.val.facts.terms := by
  rintro ⟨node, ⟨n, node_eq⟩⟩
  rcases cd.growing n with ⟨m, t, t_not_mem, ⟨node2, node2_mem, t_mem⟩⟩
  specialize t_not_mem node node_eq

  let cd2 : ChaseDerivationSkeleton obs rules := cd.derivation_for_branch_suffix _ (cd.branch.IsSuffix_drop n) (by show (cd.branch.infinite_list.get n).isSome; rw [node_eq]; simp)
  have cd2_suffix : cd2 <:+ cd.toChaseDerivationSkeleton := cd.branch.IsSuffix_drop n
  have node_head : node = cd2.head := by simp only [cd2, ChaseDerivationSkeleton.derivation_for_branch_suffix, ChaseDerivationSkeleton.head]; rcases Option.eq_some_iff_get_eq.mp node_eq with ⟨_, node_eq⟩; rw [← node_eq]; rfl
  have cd2_branch : cd2.branch = cd.branch.drop n := rfl
  have node2_mem : node2 ∈ (cd2.branch.drop m).head := by rw [cd2_branch]; exact node2_mem

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

theorem result_infinite {cd : CyclicityDerivation obs rules} : ¬ cd.result.finite := by
  rintro ⟨l, _, eq⟩
  have sub_res : l.toSet ⊆ cd.result := by intro e e_mem; rw [← eq, ← List.mem_toSet]; exact e_mem
  have res_sub : cd.result ⊆ l.toSet := by intro e e_mem; rw [List.mem_toSet, eq]; exact e_mem
  rcases cd.facts_mem_some_node_of_mem_result l sub_res with ⟨node, node_mem, sub⟩
  rcases growing' ⟨node, node_mem⟩ with ⟨node2, prec, ⟨t, t_not_mem, t_mem⟩⟩
  apply t_not_mem
  apply FactSet.terms_subset_of_subset sub
  apply FactSet.terms_subset_of_subset res_sub
  apply FactSet.terms_subset_of_subset (cd.facts_node_subset_result node2.val node2.property)
  exact t_mem

end CyclicityDerivation


/-- TODO; (called CyclicitySequence in the RPC paper) -/
structure CyclicityBranch (obs : ObsoletenessCondition sig) (kb : KnowledgeBase sig) extends CyclicityDerivation obs kb.rules where
  database_first : branch.head = some {
    facts := kb.db.toFactSet,
    origin := none,
    facts_contain_origin_result := by simp
  }

/-- TODO -/
theorem neverTerminates_of_cyclicityBranch {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}
    (cb : CyclicityBranch obs kb) : kb.rules.neverTerminates obs := by
  exists kb.db
  intro ct
  sorry

