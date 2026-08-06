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

/-- Often we want to assume that a `HeadChoice` for equivalent triggers returns the same index. -/
@[expose]
def HeadChoice.consistent_for_equivalent_triggers (hc : HeadChoice sig) : Prop := ∀ {trg trg2 : PreTrigger sig}, trg.equiv trg2 -> (hc trg).val = (hc trg2).val

/-- A shortcut for the trigger output dictaded by a head choice. -/
@[expose]
def PreTrigger.output_for_headChoice (trg : PreTrigger sig) (hc : HeadChoice sig) : List (Fact sig) :=
  trg.mapped_head[(hc trg).val]

/-- The head choice output for equivalent triggers is the same given that the head choice is `consistent_for_equivalent_triggers`. -/
theorem PreTrigger.output_for_headChoice_eq_of_equiv {trg trg2 : PreTrigger sig} {hc : HeadChoice sig}
    (hc_consistent : hc.consistent_for_equivalent_triggers) (equiv : trg.equiv trg2) : trg.output_for_headChoice hc = trg2.output_for_headChoice hc := by
  unfold output_for_headChoice; simp only [hc_consistent equiv, PreTrigger.result_eq_of_equiv equiv]

namespace ChaseNode

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig} {N : Type u} [CN : ChaseNode N obs rules]

/-- A `ChaseNode` adheres to a `HeadChoice` if its origin uses the index that is the head choice of its trigger. -/
@[expose]
def adheres_to_headChoice (node : N) (hc : HeadChoice sig) : Prop :=
  ∀ orig ∈ (CN.origin node), orig.snd.val = (hc orig.fst.val).val

theorem origin_result_eq_of_adheres_to_headChoice {node : N} (isSome : (CN.origin node).isSome)
    {hc : HeadChoice sig} (adheres : CN.adheres_to_headChoice node hc) :
    CN.origin_result node isSome = ((CN.origin node).get isSome).fst.val.output_for_headChoice hc := by
  rw [CN.origin_result_eq isSome rfl (by apply Eq.symm; apply adheres; simp)]; rfl

end ChaseNode

/-- A `ChaseDerivationSkeleton` adheres to a `HeadChoice` if every node adheres to the `HeadChoice`. -/
@[expose]
def ChaseDerivationSkeleton.adheres_to_headChoice
    {obs : ObsolescenceCondition sig} {rules : RuleSet sig} {N : Type u} [CN : ChaseNode N obs rules]
    (cd : ChaseDerivationSkeleton N obs rules) (hc : HeadChoice sig) : Prop :=
  ∀ n ∈ cd, CN.adheres_to_headChoice n hc

namespace TreeDerivation

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig} {N : Type u} [CN : ChaseNode N obs rules]

/-- The generator function used to generate the tree branch corresponding to the given `HeadChoice`. -/
def generator_for_headChoice (td : TreeDerivation N obs rules) (hc : HeadChoice sig) (n : td.NodeWithAddress) : Option td.NodeWithAddress :=
  let next_trg_opt : Option (PreTrigger sig) := (n.childNodes.head?.bind (fun c => CN.origin c.node)).map (fun o => o.fst.val)
  next_trg_opt.bind (fun trg => n.childNodes[(hc trg).val]?)

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

/-- The node produced by `generator_for_headChoice` adheres to the head choice. -/
theorem generator_for_headChoice_adheres_to_headChoice {td : TreeDerivation N obs rules} {hc : HeadChoice sig} (n : td.NodeWithAddress) :
    ∀ next ∈ td.generator_for_headChoice hc n, CN.adheres_to_headChoice next.node hc := by
  intro next next_mem orig orig_mem; simp only [generator_for_headChoice, Option.mem_def, Option.bind_eq_some_iff] at next_mem
  rcases next_mem with ⟨head_trg, head_trg_eq, next_mem⟩
  have childNodes_ne_nil : n.childNodes ≠ [] := by apply List.ne_nil_of_mem; rw [List.mem_iff_getElem?]; exact ⟨_, next_mem⟩
  rcases n.triggers_exist (by rw [TreeDerivation.NodeWithAddress.childNodes_eq_childNodes]; intro contra; rw [List.map_eq_nil_iff] at contra; apply childNodes_ne_nil; exact contra) with ⟨trg, act, ingoing_eq, trg_eq, orig_eq⟩
  specialize orig_eq (next.node, (hc head_trg).val) (by simp only [List.mem_zipIdx_iff_getElem?, TreeDerivation.NodeWithAddress.childNodes_eq_childNodes, List.getElem?_map]; rw [next_mem]; simp)
  rw [Option.mem_def] at orig_mem
  simp only [orig_mem, Option.map_some, Option.some_inj] at orig_eq
  rw [orig_eq]
  suffices head_trg = orig.fst.val by rw [this]
  have trg_eq' := trg_eq next.node (by rw [TreeDerivation.NodeWithAddress.childNodes_eq_childNodes]; apply List.mem_map_of_mem; apply List.mem_of_getElem?; exact next_mem)
  rw [orig_mem, Option.map_some, Option.some_inj] at trg_eq'
  rw [trg_eq']
  rw [List.head?_eq_some_head childNodes_ne_nil, Option.bind_some] at head_trg_eq
  have trg_eq' := trg_eq (n.childNodes.head childNodes_ne_nil).node (by rw [TreeDerivation.NodeWithAddress.childNodes_eq_childNodes]; apply List.mem_map_of_mem; exact List.head_mem _)
  rw [Option.map_eq_some_iff] at trg_eq'; rcases trg_eq' with ⟨head_orig, trg_eq'⟩
  rw [trg_eq'.left, Option.map_some, Option.some_inj] at head_trg_eq
  rw [← head_trg_eq, trg_eq'.right]

/-- This function generates the tree branch that corresponds to the given `HeadChoice`. -/
def subderivation_for_headChoice (td : TreeDerivation N obs rules) (hc : HeadChoice sig) : ChaseDerivation N obs rules :=
  td.generate_subderivation (NodeWithAddress.root td) (td.generator_for_headChoice hc) id td.generator_for_headChoice_mem_childNodes (by intro n; rw [generator_for_headChoice_eq_none_iff_childNodes_eq_nil]; rw [List.eq_nil_iff_length_eq_zero, List.eq_nil_iff_length_eq_zero, n.length_childNodes, n.subderivation.childNodes_eq]; simp)

/-- The `subderivation_for_headChoice` is a branch, which follows since we use `TreeDerivation.generate_subderivation` to build it. -/
theorem subderivation_for_headChoice_mem_branches {td : TreeDerivation N obs rules} {hc : HeadChoice sig} :
  td.subderivation_for_headChoice hc ∈ td.branches := by apply td.generate_subderivation_mem_branches; rfl

/-- The head of `subderivation_for_headChoice` is the root of the tree derivation. -/
theorem head_subderivation_for_headChoice {td : TreeDerivation N obs rules} {hc : HeadChoice sig} :
  (td.subderivation_for_headChoice hc).head = td.root := td.head_generate_subderivation

/-- The subderivation for a head choice adheres to that head choice. -/
theorem subderivation_for_headChoice_adheres_to_headChoice_of_root_adheres {td : TreeDerivation N obs rules} {hc : HeadChoice sig} :
    CN.adheres_to_headChoice td.root hc -> (td.subderivation_for_headChoice hc).adheres_to_headChoice hc := by
  simp only [subderivation_for_headChoice]
  intro root_adheres node node_mem; rw [← ChaseDerivation.mem_def, td.mem_generate_subderivation] at node_mem
  rcases node_mem with ⟨n, node_mem⟩
  cases n with
  | zero => simp only [Function.repeat_zero, Option.map_some, Option.mem_some] at node_mem; rw [← node_mem]; exact root_adheres
  | succ n =>
    rw [Function.repeat_succ, Option.mem_def, Option.map_map, Option.map_eq_some_iff] at node_mem
    rcases node_mem with ⟨next, next_mem, node_mem⟩
    rw [Option.bind_eq_some_iff] at next_mem; rcases next_mem with ⟨_, _, goal⟩
    rw [← node_mem]
    apply generator_for_headChoice_adheres_to_headChoice
    exact goal

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

/-- The subderivation for a head choice adheres to that head choice. -/
theorem subderivation_for_headChoice_adheres_to_headChoice {ct : ChaseTree N obs kb} {hc : HeadChoice sig} :
    (ct.subderivation_for_headChoice hc).adheres_to_headChoice hc := by
  apply TreeDerivation.subderivation_for_headChoice_adheres_to_headChoice_of_root_adheres
  intro orig orig_mem; rw [ct.database_first.right.right] at orig_mem; simp at orig_mem

end ChaseTree

