/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.ChaseTree

/-!
# HeadChoice

Here we define `HeadChoice`s, which are merely functions from triggers to head indices.
We also define machinery to get a branch from a tree that corresponds to a given `HeadChoice`.
-/

public section

/-- A `HeadChoice` is a function that maps each trigger to one of its head indices. -/
abbrev HeadChoice (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] := (trg : PreTrigger sig) -> Fin trg.rule.head.length

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- A `ChaseDerivationSkeleton` adheres to a `HeadChoice` if every origin uses the index that is the head choice of its trigger. -/
@[expose]
def ChaseDerivationSkeleton.adheres_to_headChoice
    {obs : ObsolescenceCondition sig} {rules : RuleSet sig} {N : Type u} [CN : ChaseNode N obs rules]
    (cd : ChaseDerivationSkeleton N obs rules) (hc : HeadChoice sig) : Prop :=
  ∀ n ∈ cd, ∀ orig ∈ (CN.origin n), orig.snd = hc orig.fst.val

namespace TreeDerivation

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig} {N : Type u} [CN : ChaseNode N obs rules]

/-- The generator function used to generate the tree branch corresponding to the given `HeadChoice`. -/
def generator_for_headChoice (td : TreeDerivation N obs rules) (hc : HeadChoice sig) (n : td.NodeWithAddress) : Option td.NodeWithAddress :=
  let next_trg_opt : Option (PreTrigger sig) := (n.childNodes.head?.bind (fun c => CN.origin c.node)).map (fun o => o.fst.val)
  next_trg_opt.bind (fun trg => n.childNodes[hc trg]?)

/-- The generator function produces a child node if it produces a value at all. -/
theorem generator_for_headChoice_mem_childNodes {td : TreeDerivation N obs rules} {hc : HeadChoice sig} (n : td.NodeWithAddress) :
    ∀ next ∈ td.generator_for_headChoice hc n, next ∈ n.childNodes := by
  intro next next_mem
  simp only [generator_for_headChoice] at next_mem; rw [Option.mem_def, Option.bind_eq_some_iff] at next_mem
  rcases next_mem with ⟨_, _, next_mem⟩
  rw [List.mem_iff_getElem?]
  exact ⟨_, next_mem⟩

/-- The generator function does not yield a new value if and only if the childNodes are empty. -/
theorem generator_for_headChoice_eq_none_iff_childNodes_eq_nil {td : TreeDerivation N obs rules} {hc : HeadChoice sig} (n : td.NodeWithAddress) :
    td.generator_for_headChoice hc n = none ↔ n.childNodes = [] := by
  simp only [generator_for_headChoice]
  cases n.childNodes.instDecidableEqNil.em with
  | inl eq_nil => simp [eq_nil]
  | inr ne_nil =>
    have ne_nil' : n.subderivation.childNodes ≠ [] := by rw [n.childNodes_eq_childNodes]; simp [ne_nil]
    rcases n.triggers_exist ne_nil' with ⟨trg, act, ingoing_eq, trg_eq, orig_eq⟩
    apply iff_of_false _ ne_nil
    intro contra
    simp only [Option.bind_eq_none_iff] at contra
    specialize contra trg.val (by
      rw [List.head?_eq_some_head ne_nil, Option.bind_some]
      suffices (ChaseNode.origin (n.childNodes.head ne_nil).node).map (fun o => o.fst.val.toPreTrigger) = ((ChaseNode.origin (n.childNodes.head ne_nil).node).map (fun o => o.fst)).map (fun trg => trg.val.toPreTrigger) by
        rw [this, trg_eq]
        . simp
        . rw [n.childNodes_eq_childNodes]; apply List.mem_map_of_mem; simp
      simp; rfl)

    suffices (hc trg.val).val < (n.subderivation.childNodes.map (ChaseNode.ingoingFacts obs rules)).length by
      apply Nat.not_le_of_lt this; rw [n.childNodes_eq_childNodes]; simp only [List.length_map]; rw [← List.getElem?_eq_none_iff]; exact contra
    rw [ingoing_eq, List.length_map, PreTrigger.length_mapped_head]; exact (hc trg.val).isLt

/-- This function generates the tree branch that corresponds to the given `HeadChoice`. -/
def subderivation_for_headChoice (td : TreeDerivation N obs rules) (hc : HeadChoice sig) : ChaseDerivation N obs rules :=
  td.generate_subderivation (NodeWithAddress.root td) (td.generator_for_headChoice hc) id td.generator_for_headChoice_mem_childNodes (by intro n; rw [generator_for_headChoice_eq_none_iff_childNodes_eq_nil]; rw [List.eq_nil_iff_length_eq_zero, List.eq_nil_iff_length_eq_zero, n.length_childNodes, n.subderivation.childNodes_eq]; simp)

/-- The `subderivation_for_headChoice` is a branch, which follows since we use `TreeDerivation.generate_subderivation` to build it. -/
theorem subderivation_for_headChoice_mem_branches {td : TreeDerivation N obs rules} {hc : HeadChoice sig} :
  td.subderivation_for_headChoice hc ∈ td.branches := by apply td.generate_subderivation_mem_branches; rfl

/-- The head of `subderivation_for_headChoice` is the root of the tree derivation. -/
theorem head_subderivation_for_headChoice {td : TreeDerivation N obs rules} {hc : HeadChoice sig} :
  (td.subderivation_for_headChoice hc).head = td.root := td.head_generate_subderivation

end TreeDerivation

namespace ChaseTree

variable {obs : ObsolescenceCondition sig} {kb : KnowledgeBase sig} {N : Type u} [CN : ChaseNode N obs kb.rules]

/-- This function generates the tree branch that corresponds to the given `HeadChoice`. -/
@[expose]
def subderivation_for_headChoice (ct : ChaseTree N obs kb) (hc : HeadChoice sig) : ChaseBranch N obs kb :=
  let deriv := ct.toTreeDerivation.subderivation_for_headChoice hc
  {
    branch := deriv.branch,
    isSome_head := deriv.isSome_head,
    triggers_exist := deriv.triggers_exist,
    triggers_active := deriv.triggers_active,
    fairness := deriv.fairness,
    database_first := by rw [TreeDerivation.head_subderivation_for_headChoice]; exact ct.database_first
  }

end ChaseTree

