/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.Nontermination.CyclicitySequence
public import ExistentialRules.ChaseSequence.Nontermination.TermSkeleton
public import ExistentialRules.ChaseSequence.Nontermination.RepeatableUnblockability
public import ExistentialRules.ChaseSequence.Nontermination.ReversibleConstantMappings
public import ExistentialRules.Terms.Cyclic

open CustomBasicDatastructures

/-!
# Cyclicity Prefixes

This is section 5 of the [RPC] paper.
A `CyclicityPrefix` is a finite sequence of triggers that are all unblockable according to a `RepeatableUnblockability` condition.
This allows to repeat the prefix indefinitely, which yields a `CyclicitySequence`. This is of course something that we need to prove here.
Then the existence of a `CyclicityPrefix` directly implies that the underlying `RuleSet.neverTerminates`.
-/

public section

/-- We can extend a signature with a type for fresh constants by setting the constants to be a Sum type of the original constants and the fresh type. -/
abbrev Signature.withFreshConstants (sig : Signature) (Fresh : Type u) : Signature := {
  Preds := sig.Preds
  V := sig.V
  C := Sum sig.C Fresh
}

instance {sig : Signature} {Fresh : Type u} [Inhabited sig.C] : Inhabited (sig.withFreshConstants Fresh).C where
  default := .inl default

/-- In particular, we can simply use the variables as fresh constants. Think of this as constants that just happen to have the same name as the variables. -/
abbrev Signature.withFreshConstantsForVars (sig : Signature) : Signature := sig.withFreshConstants sig.V

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- This turns a `VarOrConst` into the constant Sum type of `Signature.withFreshConstants`. -/
def VarOrConst.toConst_withFreshConstantsForVars : TermMapping (VarOrConst sig) sig.withFreshConstantsForVars.C
| .const c => .inl c
| .var v => .inr v

/-- Change the constant of a `VarOrConst` into the Sum type of `Signature.withFreshConstants`. -/
def VarOrConst.cast_withFreshConstantsForVars : TermMapping (VarOrConst sig) (VarOrConst sig.withFreshConstantsForVars)
| .const c => .const (.inl c)
| .var v => .var v

/-- Change the constant of a `Rule` into the Sum type of `Signature.withFreshConstants`. -/
def Rule.cast_withFreshConstantsForVars (r : Rule sig) : Rule sig.withFreshConstantsForVars where
  body := VarOrConst.cast_withFreshConstantsForVars.apply_generalized_atom_list r.body
  head := r.head.map VarOrConst.cast_withFreshConstantsForVars.apply_generalized_atom_list

/-- Change the constant of a `RuleSet` into the Sum type of `Signature.withFreshConstants`. -/
def RuleSet.cast_withFreshConstantsForVars (rs : RuleSet sig) : RuleSet sig.withFreshConstantsForVars :=
  rs.map Rule.cast_withFreshConstantsForVars

/-- The `body_database` of a rule is the body where each variable is replaced by a fresh constant.
We achieve this by extending the signature and mapping all terms in the body using `VarOrConst.cast_withFreshConstantsForVars`. -/
def Rule.body_database (r : Rule sig) : Database sig.withFreshConstantsForVars :=
  ⟨(VarOrConst.toConst_withFreshConstantsForVars.apply_generalized_atom_list r.body).toSet, List.finite_toSet _⟩

def Rule.body_kb (r : Rule sig) (rules : RuleSet sig) : KnowledgeBase sig.withFreshConstantsForVars :=
  { rules := rules.cast_withFreshConstantsForVars, db := r.body_database }

/-- The trigger for a rule that matches its `body_database`. -/
def Rule.body_database_trigger (r : Rule sig) : PreTrigger sig.withFreshConstantsForVars where
  rule := r.cast_withFreshConstantsForVars
  subs := .const ∘ .inr

/-- The `body_database_trigger` is loaded for the `body_database`. -/
theorem Rule.body_database_trigger_loaded {r : Rule sig} : r.body_database_trigger.loaded r.body_database.toFactSet.val := by
  unfold body_database body_database_trigger
  intro f f_mem
  simp only [PreTrigger.mapped_body, List.mem_toSet, TermMapping.mem_apply_generalized_atom_list] at f_mem
  rcases f_mem with ⟨b, b_mem, f_mem⟩
  simp only [cast_withFreshConstantsForVars, TermMapping.mem_apply_generalized_atom_list] at b_mem
  rcases b_mem with ⟨a, a_mem, b_mem⟩
  simp only [Database.toFactSet, List.mem_toSet]
  exists VarOrConst.toConst_withFreshConstantsForVars.apply_generalized_atom a
  constructor
  . apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_list; exact a_mem
  . rw [f_mem, b_mem]
    rw [FunctionFreeFact.toFact_eq]
    rw [← TermMapping.apply_generalized_atom_compose', ← TermMapping.apply_generalized_atom_compose']
    apply TermMapping.apply_generalized_atom_congr_left
    intro t t_mem
    cases t <;> simp [VarOrConst.cast_withFreshConstantsForVars, VarOrConst.toConst_withFreshConstantsForVars, GroundSubstitution.apply_var_or_const]

/-- The `ChaseNodeOrigin` for a rule that matches its `body_database`. -/
def Rule.body_database_origin
    (obs : ObsolescenceCondition sig.withFreshConstantsForVars)
    (rules : RuleSet sig)
    (hc : HeadChoice sig.withFreshConstantsForVars)
    (r : Rule sig)
    (r_mem : r ∈ rules) :
    ChaseNodeOrigin obs rules.cast_withFreshConstantsForVars :=
  let trg := r.body_database_trigger
  ⟨⟨Trigger.fromPreTrigger trg obs, by simp only [trg, RuleSet.cast_withFreshConstantsForVars, Rule.body_database_trigger]; apply Set.mem_map_of_mem; exact r_mem⟩, hc r.body_database_trigger⟩

/-- The `body_database_origin` adheres to the head choice. -/
theorem Rule.body_database_origin_adheres_to_headChoice
    {obs : ObsolescenceCondition sig.withFreshConstantsForVars}
    {rules : RuleSet sig}
    {hc : HeadChoice sig.withFreshConstantsForVars}
    {r : Rule sig}
    {r_mem : r ∈ rules} :
    (r.body_database_origin obs rules hc r_mem).adheres_to_headChoice hc := by
  simp only [body_database_origin, ChaseNodeOrigin.adheres_to_headChoice]
  congr

/-- For a signature `withFreshConstantsForVars`, we can turn a `GroundSubstitution` into a `ConstantMapping`. -/
def GroundSubstitution.toConstantMapping_for_sig_withFreshConstantsForVars (subs : GroundSubstitution sig.withFreshConstantsForVars) :
    ConstantMapping sig.withFreshConstantsForVars
| .inl c => .const (.inl c) -- we leave original constants untouched
| .inr v => subs v

/--
We define a structure, which is almost a `CyclicityPrefix` (missing some last conditions).
We split this mainly to add some auxiliary definitions that we can use to express the remaining conditions more easily.
-/
structure PreCyclicityPrefix
    [Inhabited sig.C]
    (obs : ObsolescenceCondition sig.withFreshConstantsForVars)
    {rules : RuleSet sig}
    {hc : HeadChoice sig.withFreshConstantsForVars}
    (hc_consistent : hc.consistent_for_same_rule)
    {rule : Rule sig}
    (rule_mem : rule ∈ rules) where
  body_database_trigger_unblockable : (Trigger.fromPreTrigger rule.body_database_trigger obs).unblockable rules.cast_withFreshConstantsForVars hc
  -- this list does not include the initial database trigger
  triggers : FiniteTriggerList obs rules.cast_withFreshConstantsForVars
  -- the first conditions are also found in the `CyclicityDerivation`; `growing` and `unblockable` are missing though
  adheres_to_headChoice : triggers.adheres_to_headChoice hc
  triggers_loaded : triggers.loaded (rule.body_database.toFactSet.val ∪ (rule.body_database_origin obs rules hc rule_mem).result.toSet)
  -- from here things are different
  ex_last_trigger : ∃ last ∈ triggers.getLast?, last.fst.val.rule = rule.cast_withFreshConstantsForVars ∧
    ∃ term ∈ last.result.flatMap GeneralizedAtom.terms, PreGroundTerm.ruleCyclic rule.cast_withFreshConstantsForVars term.val

namespace PreCyclicityPrefix

variable [Inhabited sig.C] {obs : ObsolescenceCondition sig.withFreshConstantsForVars} {rules : RuleSet sig} {hc : HeadChoice sig.withFreshConstantsForVars} {hc_consistent : hc.consistent_for_same_rule} {rule : Rule sig} {rule_mem : rule ∈ rules}

/-- The triggers are not empty. -/
theorem triggers_ne_nil {cp : PreCyclicityPrefix obs hc_consistent rule_mem} : cp.triggers ≠ [] := by
  rcases cp.ex_last_trigger with ⟨_, mem, _⟩
  intro contra; simp [contra] at mem

/-- We can cast the triggers into a `FiniteNonEmptyTriggerList`. -/
def to_FiniteNonEmptyTriggerList (cp : PreCyclicityPrefix obs hc_consistent rule_mem) :
    FiniteNonEmptyTriggerList obs rules.cast_withFreshConstantsForVars :=
  NonEmptyList.from_ne_nil cp.triggers cp.triggers_ne_nil

/-- Since the trigger list is not empty, we can get the last trigger. -/
def last_trigger (cp : PreCyclicityPrefix obs hc_consistent rule_mem) :
    ChaseNodeOrigin obs rules.cast_withFreshConstantsForVars :=
  cp.triggers.getLast cp.triggers_ne_nil

/-- The first part of the `ex_last_trigger` property expressed for the `last_trigger` shortcut. -/
theorem rule_last_trigger {cp : PreCyclicityPrefix obc hc_consistent rule_mem} :
    cp.last_trigger.fst.val.rule = rule.cast_withFreshConstantsForVars := by
  rcases cp.ex_last_trigger with ⟨last, mem, h, _⟩
  suffices last = cp.last_trigger by rw [← this]; exact h
  apply Eq.symm
  apply List.getLast_of_mem_getLast?
  exact mem

/-- The second part of the `ex_last_trigger` property expressed for the `last_trigger` shortcut. -/
theorem ruleCyclic_term_in_last_trigger {cp : PreCyclicityPrefix obc hc_consistent rule_mem} :
    ∃ term ∈ cp.last_trigger.result.flatMap GeneralizedAtom.terms, PreGroundTerm.ruleCyclic rule.cast_withFreshConstantsForVars term.val := by
  rcases cp.ex_last_trigger with ⟨last, mem, _, h⟩
  suffices last = cp.last_trigger by rw [← this]; exact h
  apply Eq.symm
  apply List.getLast_of_mem_getLast?
  exact mem

/--
In the end, we want to repeat the prefix using a constant mapping expressing the mapping from the database trigger to the last trigger.
This mapping is what is defined here.
-/
def constantMappingForRepetition (cp : PreCyclicityPrefix obs hc_consistent rule_mem) :
    ConstantMapping sig.withFreshConstantsForVars :=
  cp.last_trigger.fst.val.subs.toConstantMapping_for_sig_withFreshConstantsForVars

/--
Returns the ith repetition of the trigger list obtained by extending the triggers with the `constantMappingForRepetition` i times.
This is used for constructing an infinite list of finite trigger lists.
-/
def ithRepetition (cp : PreCyclicityPrefix obs hc_consistent rule_mem) (i : Nat) :
    FiniteNonEmptyTriggerList obs rules.cast_withFreshConstantsForVars :=
  let trgs : FiniteTriggerList obs rules.cast_withFreshConstantsForVars :=
    cp.triggers.map (fun orig => ⟨
      orig.fst.extend_with_groundTermMapping
        (Function.repeat_fun cp.constantMappingForRepetition.apply_ground_term i),
      orig.snd⟩)
  NonEmptyList.from_ne_nil trgs (by
    suffices cp.triggers = cp.to_FiniteNonEmptyTriggerList.toList by
      simp only [trgs, this]
      intro contra
      apply cp.to_FiniteNonEmptyTriggerList.toList_ne_nil
      exact List.eq_nil_of_map_eq_nil contra
    simp [to_FiniteNonEmptyTriggerList])

/-- The 0-th repetition is the original trigger list. -/
theorem ithRepetition_zero {cp : PreCyclicityPrefix obs hc_consistent rule_mem} : cp.ithRepetition 0 = cp.to_FiniteNonEmptyTriggerList := by
  simp only [ithRepetition, to_FiniteNonEmptyTriggerList]
  congr
  apply List.map_id''
  intro _; constructor

/-- Every following repetition results from extending the triggers with a single application of the `constantMappingForRepetition`. -/
theorem ithRepetition_succ {cp : PreCyclicityPrefix obs hc_consistent rule_mem} {i : Nat} :
    cp.ithRepetition i.succ = NonEmptyList.from_ne_nil ((cp.ithRepetition i).toList.map (fun orig => ⟨
      orig.fst.extend_with_groundTermMapping cp.constantMappingForRepetition.apply_ground_term,
      orig.snd
    ⟩)) (by simpa using NonEmptyList.toList_ne_nil) := by
  simp only [ithRepetition, NonEmptyList.toList_from_ne_nil, List.map_map]; congr

/-- We can arrange the i-th repetitions into an infinite list. -/
def infiniteList_of_finiteLists (cp : PreCyclicityPrefix obs hc_consistent rule_mem) :
    InfiniteList (FiniteNonEmptyTriggerList obs rules.cast_withFreshConstantsForVars) :=
  fun i => cp.ithRepetition i

/-- Each repetition adheres to the headChoice. -/
theorem infiniteList_of_finiteLists_adheres {cp : PreCyclicityPrefix obs hc_consistent rule_mem} : ∀ l ∈ cp.infiniteList_of_finiteLists,
    FiniteTriggerList.adheres_to_headChoice l.toList hc := by
  intro l l_mem orig orig_mem
  simp only [InfiniteList.mem_iff, InfiniteList.compute_get, infiniteList_of_finiteLists, ithRepetition] at l_mem
  rcases l_mem with ⟨_, l_mem⟩
  rw [← l_mem, NonEmptyList.toList_from_ne_nil] at orig_mem
  rw [List.mem_map] at orig_mem; rcases orig_mem with ⟨orig', orig'_mem, orig_eq⟩
  rw [← orig_eq]; simp only [ChaseNodeOrigin.adheres_to_headChoice]
  rw [cp.adheres_to_headChoice orig' orig'_mem]
  apply hc_consistent; simp

/-- Each repetition is loaded. -/
theorem infiniteList_of_finiteLists_loaded {cp : PreCyclicityPrefix obs hc_consistent rule_mem} :
    ∀ i, FiniteTriggerList.loaded (InfiniteTriggerList.startForFiniteList cp.infiniteList_of_finiteLists (rule.body_database.toFactSet.val ∪ (rule.body_database_origin obs rules hc rule_mem).result.toSet) i) (cp.infiniteList_of_finiteLists.get i).toList := by
  suffices ∀ i j, (GroundTermMapping.applyFactSet (Function.repeat_fun cp.constantMappingForRepetition.apply_ground_term i) (FiniteTriggerList.result (rule.body_database.toFactSet.val ∪ (rule.body_database_origin obs rules hc rule_mem).result.toSet) (cp.triggers.take j))) ⊆ FiniteTriggerList.result (InfiniteTriggerList.startForFiniteList cp.infiniteList_of_finiteLists (rule.body_database.toFactSet.val ∪ (rule.body_database_origin obs rules hc rule_mem).result.toSet) i) ((cp.infiniteList_of_finiteLists.get i).toList.take j) by
    intro i
    unfold FiniteTriggerList.loaded
    rw [FiniteTriggerList.trigger_property_holds_iff]
    intro j j_lt
    apply Set.subset_trans _ (this i j)
    simp only [infiniteList_of_finiteLists, InfiniteList.compute_get, ithRepetition, NonEmptyList.toList_from_ne_nil, List.getElem_map]
    apply PreTrigger.extend_with_groundTermMapping_loaded_of_loaded
    . sorry
    . have triggers_loaded := cp.triggers_loaded
      unfold FiniteTriggerList.loaded at triggers_loaded
      rw [FiniteTriggerList.trigger_property_holds_iff] at triggers_loaded
      exact triggers_loaded _
  intro i
  induction i with
  | zero => intro j; simp only [InfiniteTriggerList.startForFiniteList]; sorry
  | succ i ih_i =>
    intro j
    induction j with
    | zero =>
      simp only [List.take_zero, FiniteTriggerList.result_nil]
      simp only [InfiniteTriggerList.startForFiniteList]
      unfold GroundTermMapping.applyFactSet
      rw [TermMapping.apply_generalized_atom_set_union, Set.union_subset_iff_both_subset]; constructor
      . sorry
      . sorry
    | succ j ih_j =>
      simp only [List.take_add_one, FiniteTriggerList.result_append]
      cases Decidable.em (j < cp.triggers.length) with
      | inr j_not_lt =>
        have j_not_lt' : ¬ j < (cp.infiniteList_of_finiteLists.get (i+1)).toList.length := by
          simpa [infiniteList_of_finiteLists, InfiniteList.compute_get, ithRepetition] using j_not_lt
        simpa [j_not_lt, j_not_lt'] using ih_j
      | inl j_lt =>
        have j_lt' : j < (cp.infiniteList_of_finiteLists.get (i+1)).toList.length := by
          simpa [infiniteList_of_finiteLists, InfiniteList.compute_get, ithRepetition] using j_lt
        simp only [j_lt, j_lt', getElem?_pos, Option.toList_some, FiniteTriggerList.result_singleton]
        unfold GroundTermMapping.applyFactSet
        rw [TermMapping.apply_generalized_atom_set_union]
        rw [Set.union_subset_iff_both_subset]; constructor
        . apply Set.subset_union_of_subset_left; exact ih_j
        . apply Set.subset_union_of_subset_right
          sorry
  sorry
  intro i j
  induction j with
  | zero =>
    simp only [List.take_zero, FiniteTriggerList.result_nil]
    cases i with
    | zero => simp only [InfiniteTriggerList.startForFiniteList]; sorry
    | succ i =>
      simp only [InfiniteTriggerList.startForFiniteList]
      sorry
  | succ j ih =>
    simp only [List.take_add_one, FiniteTriggerList.result_append]
    cases Decidable.em (j < cp.triggers.length) with
    | inr j_not_lt =>
      have j_not_lt' : ¬ j < (cp.infiniteList_of_finiteLists.get i).toList.length := by
        simpa [infiniteList_of_finiteLists, InfiniteList.compute_get, ithRepetition] using j_not_lt
      simpa [j_not_lt, j_not_lt'] using ih
    | inl j_lt =>
      have j_lt' : j < (cp.infiniteList_of_finiteLists.get i).toList.length := by
        simpa [infiniteList_of_finiteLists, InfiniteList.compute_get, ithRepetition] using j_lt
      simp only [j_lt, j_lt', getElem?_pos, Option.toList_some, FiniteTriggerList.result_singleton]
      unfold GroundTermMapping.applyFactSet
      rw [TermMapping.apply_generalized_atom_set_union]
      rw [Set.union_subset_iff_both_subset]; constructor
      . apply Set.subset_union_of_subset_left; exact ih
      . apply Set.subset_union_of_subset_right
        sorry

/-- Then, we can turn the infinite list of i-th repetitions into a single infinite list and also prepend the initial trigger. -/
def infiniteTriggerList (cp : PreCyclicityPrefix obs hc_consistent rule_mem) : InfiniteTriggerList obs rules.cast_withFreshConstantsForVars :=
  InfiniteList.cons (rule.body_database_origin obs rules hc rule_mem) (InfiniteTriggerList.fromFiniteLists cp.infiniteList_of_finiteLists)

/-- The `infiniteTriggerList` adheres to the head choice because the `PreCyclicityPrefix` does. -/
theorem infiniteTriggerList_adheres {cp : PreCyclicityPrefix obs hc_consistent rule_mem} : cp.infiniteTriggerList.adheres_to_headChoice hc := by
  unfold infiniteTriggerList
  intro orig orig_mem
  cases InfiniteList.mem_cons.mp orig_mem with
  | inl orig_mem => rw [orig_mem]; exact Rule.body_database_origin_adheres_to_headChoice
  | inr orig_mem =>
    apply InfiniteTriggerList.fromFiniteLists_headChoice_preserved _ orig orig_mem
    exact infiniteList_of_finiteLists_adheres

/-- The `infiniteTriggerList` is loaded because the `PreCyclicityPrefix` is. -/
theorem infiniteTriggerList_loaded {cp : PreCyclicityPrefix obs hc_consistent rule_mem} : cp.infiniteTriggerList.loaded rule.body_database.toFactSet.val := by
  unfold infiniteTriggerList
  apply (InfiniteTriggerList.trigger_property_holds_iff_holds_for_head_and_tail (property := fun orig => orig.fst.val.loaded)).mpr
  simp only [InfiniteList.head_cons, InfiniteList.tail_cons]
  constructor
  . exact Rule.body_database_trigger_loaded
  . apply InfiniteTriggerList.fromFiniteLists_loadedness_preserved
    exact cp.infiniteList_of_finiteLists_loaded

/-- The infinite list of triggers can be turned into a regularChaseDerivationSkeleton. -/
def infiniteRegularChaseDerivationSkeleton (cp : PreCyclicityPrefix obs hc_consistent rule_mem) :
    RegularChaseDerivationSkeleton obs rules.cast_withFreshConstantsForVars :=
  cp.infiniteTriggerList.to_regularChaseDerivationSkeleton rule.body_database.toFactSet.val

/-- The `infiniteRegularChaseDerivationSkeleton` also adheres to the head choice since the `infiniteTriggerList` does. (This holds by definition.) -/
theorem infiniteRegularChaseDerivationSkeleton_adheres {cp : PreCyclicityPrefix obs hc_consistent rule_mem} :
    cp.infiniteRegularChaseDerivationSkeleton.adheres_to_headChoice hc := by
  intro node node_mem orig orig_mem
  apply cp.infiniteTriggerList_adheres
  simp only [infiniteRegularChaseDerivationSkeleton, InfiniteTriggerList.to_regularChaseDerivationSkeleton] at node_mem
  simp only [ChaseDerivationSkeleton.mem_iff, PossiblyInfiniteList.get?_from_infiniteList, Option.some_inj] at node_mem
  rcases node_mem with ⟨n, node_mem⟩
  rw [← node_mem] at orig_mem
  cases n with
  | zero => simp at orig_mem
  | succ n =>
    simp only [InfiniteTriggerList.origin_get_succ_to_ChaseNode_list, Option.mem_def, Option.some_inj] at orig_mem
    rw [← orig_mem]; exact InfiniteList.get_mem

end PreCyclicityPrefix

/-- The actual `CyclicityPrefix` definition based on `PreCyclicityPrefix` with extra conditions. -/
structure CyclicityPrefix
    [Inhabited sig.C]
    (obs : ObsolescenceCondition sig.withFreshConstantsForVars)
    (unblk : RepeatableUnblockability obs)
    {rules : RuleSet sig}
    {hc : HeadChoice sig.withFreshConstantsForVars}
    (hc_consistent : hc.consistent_for_same_rule)
    {rule : Rule sig}
    (rule_mem : rule ∈ rules)
    extends PreCyclicityPrefix obs hc_consistent rule_mem where
  triggers_unblockable : ∀ orig ∈ triggers, unblk.trigger_unblockable rules.cast_withFreshConstantsForVars hc orig.fst.val
  constantMapping_reversible_in_each_step : ∀ i : Nat, ∀ orig ∈ (toPreCyclicityPrefix.ithRepetition i).toList,
    toPreCyclicityPrefix.constantMappingForRepetition.isReversible orig.fst.val.termSkeleton.toSet

namespace CyclicityPrefix

variable [Inhabited sig.C] {obs : ObsolescenceCondition sig.withFreshConstantsForVars} {unblk : RepeatableUnblockability obs} {rules : RuleSet sig} {hc : HeadChoice sig.withFreshConstantsForVars} {hc_consistent : hc.consistent_for_same_rule} {rule : Rule sig} {rule_mem : rule ∈ rules}

def to_cyclicityBranch (cp : CyclicityPrefix obs unblk hc_consistent rule_mem) : CyclicityBranch obs (rule.body_kb rules) hc :=
  let deriv := cp.infiniteRegularChaseDerivationSkeleton
  {
    branch := deriv.branch,
    isSome_head := deriv.isSome_head,
    triggers_exist := deriv.triggers_exist
    adheres_to_headChoice := cp.infiniteRegularChaseDerivationSkeleton_adheres
    triggers_loaded := sorry
    growing := sorry
    unblockable := sorry
    database_first := sorry
  }

/-- If a rule set admist a `CyclicityPrefix`, then it `RuleSet.neverTerminates`. -/
theorem neverTerminates_of_cyclicityBranch (cp : CyclicityPrefix obs unblk hc_consistent rule_mem) :
    rules.cast_withFreshConstantsForVars.neverTerminates obs (RegularChaseNode obs rules.cast_withFreshConstantsForVars) :=
  cp.to_cyclicityBranch.neverTerminates_of_cyclicityBranch

end CyclicityPrefix

