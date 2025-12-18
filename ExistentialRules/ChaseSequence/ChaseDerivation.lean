import PossiblyInfiniteTrees.PossiblyInfiniteList.PossiblyInfiniteList

import ExistentialRules.Models.Basic
import ExistentialRules.ChaseSequence.ChaseNode

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

def exists_trigger_opt_fs (obs : ObsoletenessCondition sig) (rules : RuleSet sig) (before : ChaseNode obs rules) (after : Option (ChaseNode obs rules)) : Prop :=
  ∃ trg : (RTrigger (obs : LaxObsoletenessCondition sig) rules), trg.val.active before.facts ∧ ∃ i, after = some {
    facts := before.facts ∪ (trg.val.mapped_head[i.val]'(i.isLt)).toSet,
    origin := some ⟨trg, i⟩
    facts_contain_origin_result := by simp [Option.is_none_or]; apply Set.subset_union_of_subset_right; apply Set.subset_refl
  }

def not_exists_trigger_opt_fs (obs : ObsoletenessCondition sig) (rules : RuleSet sig) (before : ChaseNode obs rules) (after : Option (ChaseNode obs rules)) : Prop :=
  ¬(∃ trg : (RTrigger obs rules), trg.val.active before.facts) ∧ after = none

structure ChaseDerivation (obs : ObsoletenessCondition sig) (rules : RuleSet sig) where
  branch : PossiblyInfiniteList (ChaseNode obs rules)
  isSome_head : branch.head.isSome
  triggers_exist : ∀ n : Nat, (branch.drop n).head.is_none_or (fun before =>
    let after := (branch.drop n).tail.head
    (exists_trigger_opt_fs obs rules before after) ∨
    (not_exists_trigger_opt_fs obs rules before after))
  fairness : ∀ trg : (RTrigger obs rules), ∃ i : Nat, ((branch.drop i).head.is_some_and (fun fs => ¬ trg.val.active fs.facts))
    ∧ (∀ j : Nat, ((branch.drop i).tail.get? j).is_none_or (fun fs => ¬ trg.val.active fs.facts))

namespace ChaseDerivation

  variable {obs : ObsoletenessCondition sig} {rules : RuleSet sig}

  instance : Membership (ChaseNode obs rules) (ChaseDerivation obs rules) where
    mem cd node := node ∈ cd.branch

  def result (cd : ChaseDerivation obs rules) : FactSet sig :=
    fun f => ∃ node ∈ cd, f ∈ node.facts

  -- inspired by List.IsSuffix; see https://github.com/leanprover/lean4/blob/9d4ad1273f6cea397c3066c2c83062a4410d16bf/src/Init/Data/List/Basic.lean#L1205
  def IsSuffix (cd1 cd2 : ChaseDerivation obs rules) : Prop := cd1.branch <:+ cd2.branch
  infixl:50 " <:+ " => IsSuffix

  theorem mem_of_mem_suffix {cd1 cd2 : ChaseDerivation obs rules} (suffix : cd1 <:+ cd2) : ∀ node ∈ cd1, node ∈ cd2 := by
    rintro node ⟨n, node_eq⟩
    rcases suffix with ⟨m, suffix⟩
    exists m + n
    rw [← suffix, InfiniteList.get_drop] at node_eq
    exact node_eq

  def derivation_for_branch_suffix
      (cd : ChaseDerivation obs rules)
      (l2 : PossiblyInfiniteList (ChaseNode obs rules))
      (suffix : l2 <:+ cd.branch)
      (l2_head_some : l2.head.isSome) :
      ChaseDerivation obs rules where
    branch := l2
    isSome_head := l2_head_some
    triggers_exist := by
      rw [PossiblyInfiniteList.IsSuffix_iff] at suffix
      rcases suffix with ⟨m, suffix⟩
      rw [← suffix]
      intro n
      have := cd.triggers_exist (m + n)
      simp only [PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?_drop] at *
      exact this
    fairness := by
      rw [Option.isSome_iff_exists] at l2_head_some; rcases l2_head_some with ⟨l2_head, l2_head_eq⟩
      rw [PossiblyInfiniteList.IsSuffix_iff] at suffix
      rcases suffix with ⟨m, suffix⟩
      rw [← suffix]
      intro trg
      rcases cd.fairness trg with ⟨i, fairness⟩
      cases Decidable.em (i < m) with
      | inl lt =>
        rcases Nat.exists_eq_add_of_lt lt with ⟨diff, lt⟩
        exists 0
        constructor
        . have fairness := fairness.right diff
          rw [Option.is_none_or_iff] at fairness
          rw [Option.is_some_and_iff]
          simp only [PossiblyInfiniteList.drop_zero]
          exists l2_head; constructor
          . rw [suffix, l2_head_eq]
          . apply fairness
            rw [PossiblyInfiniteList.get?_tail, PossiblyInfiniteList.get?_drop, ← PossiblyInfiniteList.head_drop, Nat.succ_eq_add_one, ← Nat.add_assoc, ← lt]
            rw [suffix, l2_head_eq]
        . intro j
          have fairness := fairness.right (diff.succ + j)
          simp only [PossiblyInfiniteList.drop_zero, PossiblyInfiniteList.get?_tail, PossiblyInfiniteList.get?_drop] at *
          have : (i + diff + 1 + j.succ) = (i + (diff.succ + j).succ) := by omega
          rw [lt, this]
          exact fairness
      | inr le =>
        have le := Nat.le_of_not_lt le
        simp only [PossiblyInfiniteList.tail_drop, PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?_drop, Nat.succ_add] at *
        exists (i - m)
        simp only [← Nat.add_succ, ← Nat.add_assoc, Nat.add_sub_of_le le] at *
        exact fairness

  theorem fairness' {cd : ChaseDerivation obs rules} : ∀ (trg : RTrigger obs rules), ∃ (cd2 : ChaseDerivation obs rules), cd2 <:+ cd ∧ ∀ node ∈ cd2, ¬ trg.val.active node.facts := by
    intro trg
    rcases cd.fairness trg with ⟨n, fairness_head, fairness_tail⟩
    rw [Option.is_some_and_iff] at fairness_head
    rcases fairness_head with ⟨node, node_eq, fairness_head⟩
    exists cd.derivation_for_branch_suffix (cd.branch.drop n) (cd.branch.IsSuffix_drop n) (by simp [node_eq])
    constructor
    . exact cd.branch.IsSuffix_drop n
    . intro node2 node2_mem
      rcases node2_mem with ⟨m, node2_mem⟩
      simp only [derivation_for_branch_suffix, PossiblyInfiniteList.drop, InfiniteList.get_drop] at node2_mem
      cases m with
      | zero => simp only [PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?] at node_eq; rw [Nat.add_zero, node_eq, Option.some_inj] at node2_mem; rw [← node2_mem]; exact fairness_head
      | succ m =>
        specialize fairness_tail m
        simp only [PossiblyInfiniteList.get?_tail, PossiblyInfiniteList.get?_drop] at fairness_tail
        simp only [PossiblyInfiniteList.get?] at fairness_tail
        simp only [node2_mem, Option.is_none_or] at fairness_tail
        exact fairness_tail

  def head (cd : ChaseDerivation obs rules) : ChaseNode obs rules := cd.branch.head.get (cd.isSome_head)
  theorem head_mem {cd : ChaseDerivation obs rules} : cd.head ∈ cd := by exists 0; simp [head, PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?]

  theorem subderivation_of_node_mem {cd : ChaseDerivation obs rules} {node : ChaseNode obs rules} (node_mem : node ∈ cd) :
      ∃ (cd2 : ChaseDerivation obs rules), cd2.head = node ∧ cd2 <:+ cd := by
    rcases node_mem with ⟨n, node_mem⟩
    exists cd.derivation_for_branch_suffix (cd.branch.drop n) (cd.branch.IsSuffix_drop n) (by simp only [PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?, node_mem]; simp)
    constructor
    . simp only [derivation_for_branch_suffix, head, PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?, node_mem, Option.get_some]
    . exact cd.branch.IsSuffix_drop n

  def Node (cd : ChaseDerivation obs rules) := { node : ChaseNode obs rules // node ∈ cd}

  def Node.cast_suffix {cd cd2 : ChaseDerivation obs rules} (suffix : cd <:+ cd2) (node : Node cd) : Node cd2 := ⟨node.val, mem_of_mem_suffix suffix _ node.property⟩

  def predecessor {cd : ChaseDerivation obs rules} (n1 n2 : Node cd) : Prop := ∃ cd2, cd2 <:+ cd ∧ cd2.head = n1.val ∧ n2.val ∈ cd2
  infixl:50 " ≼ " => predecessor

  theorem predecessor_refl {cd : ChaseDerivation obs rules} {node : Node cd} : node ≼ node := by rcases cd.subderivation_of_node_mem node.property with ⟨cd2, head_eq, suffix⟩; exists cd2; simp only [suffix, head_eq, true_and]; rw [← head_eq]; exact cd2.head_mem
  theorem predecessor_of_suffix {cd cd2 : ChaseDerivation obs rules} {n1 n2 : Node cd} (suffix : cd <:+ cd2) : n1 ≼ n2 -> (n1.cast_suffix suffix) ≼ (n2.cast_suffix suffix) := by
    rintro ⟨cd3, suffix', head_eq, mem⟩
    exists cd3; constructor
    . exact cd3.branch.IsSuffix_trans suffix' suffix
    constructor
    . rw [head_eq]; rfl
    . exact mem

  def next (cd : ChaseDerivation obs rules) : Option (ChaseNode obs rules) := cd.branch.tail.head
  theorem next_mem_of_mem {cd : ChaseDerivation obs rules} : ∀ next ∈ cd.next, next ∈ cd := by intro next next_mem; apply cd.branch.tail.mem_of_mem_suffix cd.branch.IsSuffix_tail; apply cd.branch.tail.head_mem; exact next_mem
  theorem isSome_origin_next {cd : ChaseDerivation obs rules} {next : ChaseNode obs rules} (eq : cd.next = some next) : next.origin.isSome := by
    have trg_ex := cd.triggers_exist 0
    rw [PossiblyInfiniteList.drop_zero, Option.is_none_or_iff] at trg_ex
    specialize trg_ex cd.head (by simp [head])
    cases trg_ex with
    | inl trg_ex => rcases trg_ex with ⟨_, _, _, trg_ex⟩; unfold ChaseDerivation.next at eq; rw [eq, Option.some_inj] at trg_ex; rw [trg_ex]; simp
    | inr trg_ex => have contra := trg_ex.right; unfold ChaseDerivation.next at eq; simp [eq] at contra
  theorem active_trigger_origin_next {cd : ChaseDerivation obs rules} {next : ChaseNode obs rules} (eq : cd.next = some next) :
      (next.origin.get (cd.isSome_origin_next eq)).fst.val.active cd.head.facts := by
    have trg_ex := cd.triggers_exist 0
    rw [PossiblyInfiniteList.drop_zero, Option.is_none_or_iff] at trg_ex
    specialize trg_ex cd.head (by simp [head])
    cases trg_ex with
    | inl trg_ex => rcases trg_ex with ⟨trg', trg'_active, _, trg_ex⟩; unfold ChaseDerivation.next at eq; rw [eq, Option.some_inj] at trg_ex; simp only [trg_ex, Option.get_some]; exact trg'_active
    | inr trg_ex => have contra := trg_ex.right; unfold ChaseDerivation.next at eq; simp [eq] at contra
  theorem isSome_next_iff_trg_ex {cd : ChaseDerivation obs rules} : cd.next.isSome ↔ ∃ (trg : RTrigger obs rules), trg.val.active cd.head.facts := by
    constructor
    . rw [Option.isSome_iff_exists]
      rintro ⟨next, eq⟩
      exists (next.origin.get (cd.isSome_origin_next eq)).fst
      exact active_trigger_origin_next eq
    . rintro ⟨trg, active⟩
      apply Decidable.byContradiction
      rw [Option.not_isSome_iff_eq_none]
      intro eq_none
      have trg_ex := cd.triggers_exist 0
      rw [PossiblyInfiniteList.drop_zero, Option.is_none_or_iff] at trg_ex
      specialize trg_ex cd.head (by simp [head])
      cases trg_ex with
      | inl trg_ex => rcases trg_ex with ⟨_, _, _, contra⟩; unfold next at eq_none; simp [eq_none] at contra
      | inr trg_ex => apply trg_ex.left; exists trg
  theorem facts_next {cd : ChaseDerivation obs rules} {next : ChaseNode obs rules} (eq : cd.next = some next) :
      next.facts = cd.head.facts ∪ (next.origin_result (cd.isSome_origin_next eq)).toSet := by
    have trg_ex := cd.triggers_exist 0
    rw [PossiblyInfiniteList.drop_zero, Option.is_none_or_iff] at trg_ex
    specialize trg_ex cd.head (by simp [head])
    cases trg_ex with
    | inl trg_ex => rcases trg_ex with ⟨trg', trg'_active, _, trg_ex⟩; unfold ChaseDerivation.next at eq; rw [eq, Option.some_inj] at trg_ex; simp only [trg_ex]; rfl
    | inr trg_ex => have contra := trg_ex.right; unfold ChaseDerivation.next at eq; simp [eq] at contra

  theorem head_prec_next {cd : ChaseDerivation obs rules} : ∀ {next}, (mem : next ∈ cd.next) -> ⟨cd.head, cd.head_mem⟩ ≼ ⟨next, cd.next_mem_of_mem _ mem⟩ := by
    intro next next_mem; exact ⟨cd, cd.branch.IsSuffix_refl, rfl, cd.next_mem_of_mem _ next_mem⟩

  theorem mem_rec
      {cd : ChaseDerivation obs rules}
      {motive : Node cd -> Prop}
      (head : motive ⟨cd.head, cd.head_mem⟩)
      (step : ∀ (cd2 : ChaseDerivation obs rules), (suffix : cd2 <:+ cd) -> motive ⟨cd2.head, mem_of_mem_suffix suffix _ cd2.head_mem⟩ -> ∀ next, (next_mem : next ∈ cd2.next) -> motive ⟨next, mem_of_mem_suffix suffix _ (cd2.next_mem_of_mem _ next_mem)⟩)
      (node : Node cd) :
      motive node := by
    induction node using PossiblyInfiniteList.mem_rec with
    | head head' mem => unfold ChaseDerivation.head at head; rw [Option.mem_def] at mem; simp only [mem, Option.get_some] at head; exact head
    | step l2 suffix ih next next_mem =>
      rcases ih with ⟨head, head_mem, ih⟩
      let cd2 : ChaseDerivation obs rules := cd.derivation_for_branch_suffix l2 suffix (by rw [head_mem]; simp)
      apply step cd2 suffix
      . simp only [cd2, derivation_for_branch_suffix, ChaseDerivation.head];
        conv => right; left; left; rw [head_mem]
        simp only [Option.get_some]
        exact ih
      . exact next_mem

  def tail (cd : ChaseDerivation obs rules) (next_some : cd.next.isSome) : ChaseDerivation obs rules :=
    cd.derivation_for_branch_suffix cd.branch.tail (cd.branch.IsSuffix_tail) next_some
  theorem head_tail {cd : ChaseDerivation obs rules} {next_some : cd.next.isSome} : some (cd.tail next_some).head = cd.next := by
    unfold tail head ChaseDerivation.next derivation_for_branch_suffix
    simp only [Option.some_get]
  theorem head_tail' {cd : ChaseDerivation obs rules} {next_some : cd.next.isSome} : (cd.tail next_some).head = cd.next.get next_some := by rfl

  theorem suffix_iff_eq_or_suffix_tail {cd1 cd2 : ChaseDerivation obs rules} : cd1 <:+ cd2 ↔ cd1 = cd2 ∨ ∃ h, cd1 <:+ cd2.tail h := by
    -- TODO: maybe we should extract a result like this to InfiniteList directly
    constructor
    . rintro ⟨n, suffix⟩
      cases n with
      | zero => apply Or.inl; rw [InfiniteList.drop_zero] at suffix; apply Eq.symm; rw [ChaseDerivation.mk.injEq, PossiblyInfiniteList.mk.injEq]; exact suffix
      | succ n =>
        apply Or.inr
        exists (by
          rw [Option.isSome_iff_ne_none]
          intro contra
          have := cd2.branch.get?_eq_none_of_le_of_eq_none contra (n+1) (by simp)
          simp only [PossiblyInfiniteList.get?] at this
          rw [InfiniteList.ext_iff] at suffix
          specialize suffix 0
          rw [InfiniteList.get_drop, Nat.add_zero, this] at suffix
          have contra := cd1.isSome_head
          rw [Option.isSome_iff_ne_none] at contra
          apply contra
          simp only [PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?]
          rw [← suffix])
        exists n
        simp only [tail, derivation_for_branch_suffix, PossiblyInfiniteList.tail]
        apply InfiniteList.ext
        intro m
        simp only [InfiniteList.get_tail, InfiniteList.get_drop]
        rw [InfiniteList.ext_iff] at suffix
        simp only [InfiniteList.get_drop] at suffix
        have : (n+m).succ = (n + 1 + m) := by omega
        rw [this]
        apply suffix m
    . intro h; cases h with
      | inl eq => rw [eq]; exact PossiblyInfiniteList.IsSuffix_refl
      | inr suffix => rcases suffix with ⟨h, suffix⟩; apply PossiblyInfiniteList.IsSuffix_trans suffix; exact PossiblyInfiniteList.IsSuffix_tail

  theorem mem_tail_iff {cd : ChaseDerivation obs rules} {next_some : cd.next.isSome} {node : ChaseNode obs rules} :
      node ∈ cd.tail next_some ↔ ∃ cd2, cd2 <:+ cd ∧ cd2.next = some node := by
    constructor
    . intro node_mem
      let node' : (cd.tail next_some).Node := ⟨node, node_mem⟩
      show ∃ cd2, cd2 <:+ cd ∧ cd2.next = some node'.val
      induction node' using mem_rec with
      | head => exists cd; constructor; exact cd.branch.IsSuffix_refl; rw [head_tail]
      | step cd3 suffix ih next next_mem =>
        exists cd3; constructor
        . apply cd3.branch.IsSuffix_trans suffix; exact cd.branch.IsSuffix_tail
        . exact next_mem
    . rintro ⟨cd2, suffix, next_eq⟩
      have : cd2.tail (by simp [next_eq]) <:+ cd.tail next_some := by
        -- TODO: maybe we should extract a result like this to InfiniteList directly
        rcases suffix with ⟨n, suffix⟩
        exists n
        simp only [tail, derivation_for_branch_suffix, PossiblyInfiniteList.tail]
        apply InfiniteList.ext
        intro m
        simp only [InfiniteList.get_tail, InfiniteList.get_drop]
        rw [InfiniteList.ext_iff] at suffix
        simp only [InfiniteList.get_drop] at suffix
        apply suffix m.succ
      apply mem_of_mem_suffix this
      rw [← head_tail (next_some := by simp [next_eq]), Option.some_inj] at next_eq
      simp only [← next_eq]
      apply head_mem

  theorem facts_node_subset_every_mem {cd : ChaseDerivation obs rules} : ∀ node ∈ cd, cd.head.facts ⊆ node.facts := by
    intro node node_mem
    let node' : cd.Node := ⟨node, node_mem⟩
    show cd.head.facts ⊆ node'.val.facts
    induction node' using mem_rec with
    | head => apply Set.subset_refl
    | step cd2 suffix subset next next_eq =>
      apply Set.subset_trans subset
      rw [cd2.facts_next next_eq]
      apply Set.subset_union_of_subset_left
      apply Set.subset_refl

  theorem facts_node_subset_of_prec {cd : ChaseDerivation obs rules} {node1 node2 : cd.Node} : node1 ≼ node2 -> node1.val.facts ⊆ node2.val.facts := by
    rintro ⟨cd2, suffix, head_eq, mem⟩
    rw [← head_eq]
    apply facts_node_subset_every_mem
    exact mem

  theorem facts_node_subset_result {cd : ChaseDerivation obs rules} : ∀ node ∈ cd, node.facts ⊆ cd.result := by intro node _ _ _; exists node

  theorem head_not_mem_tail {cd : ChaseDerivation obs rules} : ∀ h, ¬ cd.head ∈ cd.tail h := by
    intro h contra
    rw [mem_tail_iff] at contra
    rcases contra with ⟨cd2, suffix, contra⟩
    apply (cd2.active_trigger_origin_next contra).right
    apply obs.contains_trg_result_implies_cond
    have := cd.head.facts_contain_origin_result
    rw [Option.is_none_or_iff] at this
    specialize this (cd.head.origin.get (cd2.isSome_origin_next contra)) (by simp)
    apply Set.subset_trans this
    apply cd.facts_node_subset_every_mem
    apply mem_of_mem_suffix suffix
    exact cd2.head_mem

  theorem eq_of_suffix_of_head_mem {cd1 cd2 : ChaseDerivation obs rules} (suffix : cd1 <:+ cd2) (head_mem : cd2.head ∈ cd1) : cd1 = cd2 := by
    rw [suffix_iff_eq_or_suffix_tail] at suffix
    cases suffix with
    | inl suffix => exact suffix
    | inr suffix => rcases suffix with ⟨h, suffix⟩; apply False.elim; apply head_not_mem_tail h; apply mem_of_mem_suffix suffix; exact head_mem

  theorem predecessor_trans {cd : ChaseDerivation obs rules} {n1 n2 n3 : Node cd} : n1 ≼ n2 -> n2 ≼ n3 -> n1 ≼ n3 := by
    rintro ⟨cd1, suffix1, head_eq1, prec1⟩ ⟨cd2, suffix2, head_eq2, prec2⟩
    exists cd1; simp only [suffix1, head_eq1, true_and]
    apply mem_of_mem_suffix _ _ prec2
    cases PossiblyInfiniteList.suffix_or_suffix_of_suffix suffix1 suffix2 with
    | inr suffix => exact suffix
    | inl suffix => rw [eq_of_suffix_of_head_mem suffix]; exact PossiblyInfiniteList.IsSuffix_refl; rw [head_eq2]; exact prec1

  theorem predecessor_antisymm {cd : ChaseDerivation obs rules} {n1 n2 : Node cd} : n1 ≼ n2 -> n2 ≼ n1 -> n1 = n2 := by
    rintro ⟨cd1, suffix1, head_eq1, prec1⟩ ⟨cd2, suffix2, head_eq2, prec2⟩
    have : cd1 = cd2 := by
      cases PossiblyInfiniteList.suffix_or_suffix_of_suffix suffix1 suffix2 with
      | inl suffix => rw [eq_of_suffix_of_head_mem suffix]; rw [head_eq2]; exact prec1
      | inr suffix => rw [eq_of_suffix_of_head_mem suffix]; rw [head_eq1]; exact prec2
    apply Subtype.ext
    rw [← head_eq1, ← head_eq2, this]

  theorem mem_suffix_of_mem {cd1 cd2 : ChaseDerivation obs rules} (suffix : cd1 <:+ cd2) : ∀ node ∈ cd2, node.facts ⊆ cd1.head.facts ∨ node ∈ cd1 := by
    intro node node_mem
    rcases subderivation_of_node_mem node_mem with ⟨cd3, cd3_head, suffix'⟩
    cases PossiblyInfiniteList.suffix_or_suffix_of_suffix suffix suffix' with
    | inl suffix => apply Or.inl; rw [← cd3_head]; apply cd3.facts_node_subset_every_mem; apply mem_of_mem_suffix suffix; apply cd1.head_mem
    | inr suffix => apply Or.inr; rw [← cd3_head]; apply mem_of_mem_suffix suffix; apply cd3.head_mem

  theorem result_suffix {cd1 cd2 : ChaseDerivation obs rules} (suffix : cd1 <:+ cd2) : cd1.result = cd2.result := by
    apply Set.ext
    intro f
    constructor
    . rintro ⟨node, node_mem, f_mem⟩; apply cd2.facts_node_subset_result; exact mem_of_mem_suffix suffix _ node_mem; exact f_mem
    . rintro ⟨node, node_mem, f_mem⟩
      cases mem_suffix_of_mem suffix _ node_mem with
      | inl mem_suffix => apply cd1.facts_node_subset_result; exact cd1.head_mem; apply mem_suffix; exact f_mem
      | inr mem_suffix => apply cd1.facts_node_subset_result; exact mem_suffix; exact f_mem

  theorem constants_node_subset_constants_fs_union_constants_rules {cd : ChaseDerivation obs rules} {node : ChaseNode obs rules} (node_mem : node ∈ cd) :
      node.facts.constants ⊆ (cd.head.facts.constants ∪ rules.head_constants) := by
    let node' : cd.Node := ⟨node, node_mem⟩
    show node'.val.facts.constants ⊆ (cd.head.facts.constants ∪ rules.head_constants)
    induction node' using mem_rec with
    | head =>
      apply Set.subset_union_of_subset_left
      apply Set.subset_refl
    | step cd2 suffix ih next next_eq =>
      rw [facts_next next_eq]
      intro c c_mem
      rw [FactSet.constants_union] at c_mem
      cases c_mem with
      | inl c_mem => apply ih; exact c_mem
      | inr c_mem =>
        let origin := next.origin.get (cd2.isSome_origin_next next_eq)
        apply Set.subset_trans (origin.fst.val.mapped_head_constants_subset origin.snd)
        . intro c c_mem
          rw [List.mem_toSet, List.mem_append] at c_mem
          cases c_mem with
          | inl c_mem =>
            apply ih
            rw [List.mem_flatMap] at c_mem
            rcases c_mem with ⟨t, t_mem, c_mem⟩
            rw [List.mem_map] at t_mem
            rcases t_mem with ⟨v, v_mem, t_mem⟩
            rcases FunctionFreeConjunction.mem_vars.mp (origin.fst.val.rule.frontier_subset_vars_body v_mem) with ⟨a, a_mem, v_mem'⟩
            exists origin.fst.val.subs.apply_function_free_atom a
            constructor
            . have := cd2.active_trigger_origin_next next_eq
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
                unfold TermMapping.apply_generalized_atom
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

  theorem facts_mem_some_node_of_mem_result {cd : ChaseDerivation obs rules} : ∀ (l : List (Fact sig)), l.toSet ⊆ cd.result -> ∃ node ∈ cd, l.toSet ⊆ node.facts := by
    intro l
    induction l with
    | nil => intros; exists cd.head; constructor; exact cd.head_mem; intro _ contra; simp [List.mem_toSet] at contra
    | cons f l ih =>
      intro subset
      rcases subset f (by simp [List.mem_toSet]) with ⟨node_f, node_f_mem, f_mem⟩
      rcases ih (by intro f f_mem; apply subset; rw [List.mem_toSet] at f_mem; simp [List.mem_toSet, f_mem]) with ⟨node_ih, node_ih_mem, l_subset⟩
      rcases cd.subderivation_of_node_mem node_f_mem with ⟨cd_f, cd_f_head, cd_f_suffix⟩
      cases mem_suffix_of_mem cd_f_suffix _ node_ih_mem with
      | inl mem_suffix =>
        exists node_f
        constructor
        . exact node_f_mem
        . intro e e_mem
          rw [List.mem_toSet, List.mem_cons] at e_mem
          cases e_mem with
          | inl e_mem => rw [e_mem]; exact f_mem
          | inr e_mem => rw [← cd_f_head]; apply mem_suffix; apply l_subset; rw [List.mem_toSet]; exact e_mem
      | inr mem_suffix =>
        exists node_ih
        constructor
        . exact node_ih_mem
        . intro e e_mem
          rw [List.mem_toSet, List.mem_cons] at e_mem
          cases e_mem with
          | inr e_mem => apply l_subset; rw [List.mem_toSet]; exact e_mem
          | inl e_mem =>
            rw [e_mem]
            apply cd_f.facts_node_subset_every_mem _ mem_suffix
            rw [cd_f_head]; exact f_mem

  theorem trg_loaded_for_some_node_of_trg_loaded_for_result {cd : ChaseDerivation obs rules} : ∀ trg : Trigger obs, trg.loaded cd.result -> ∃ node ∈ cd, trg.loaded node.facts := by
    intro trg trg_loaded
    apply cd.facts_mem_some_node_of_mem_result
    exact trg_loaded

  theorem trg_active_for_some_node_of_trg_active_for_result {cd : ChaseDerivation obs rules} : ∀ trg : Trigger obs, trg.active cd.result -> ∃ node ∈ cd, trg.active node.facts := by
    intro trg trg_active
    rcases cd.trg_loaded_for_some_node_of_trg_loaded_for_result trg trg_active.left with ⟨node, node_mem, loaded_node⟩
    exists node; simp only [node_mem, true_and]
    constructor; exact loaded_node
    intro contra
    apply trg_active.right
    exact obs.monotone (cd.facts_node_subset_result _ node_mem) contra

  theorem result_models_rules {cd : ChaseDerivation obs rules} : cd.result.modelsRules rules := by
    intro r r_mem subs subs_loaded
    let trg : Trigger obs := ⟨r, subs⟩
    have trg_loaded : trg.loaded cd.result := subs_loaded
    apply obs.cond_implies_trg_is_satisfied (trg := trg)
    rcases cd.trg_loaded_for_some_node_of_trg_loaded_for_result trg trg_loaded with ⟨node_loaded, node_loaded_mem, trg_loaded⟩
    rcases cd.subderivation_of_node_mem node_loaded_mem with ⟨cd_loaded, cd_loaded_head, cd_loaded_suffix⟩
    rcases cd_loaded.fairness' ⟨trg, r_mem⟩ with ⟨cd_obs, cd_obs_suffix, fairness⟩
    specialize fairness cd_obs.head cd_obs.head_mem
    apply Classical.byContradiction
    intro contra_not_obs
    apply fairness
    constructor
    . apply Set.subset_trans trg_loaded
      rw [← cd_loaded_head]
      apply cd_loaded.facts_node_subset_every_mem
      apply cd_obs.mem_of_mem_suffix cd_obs_suffix
      apply cd_obs.head_mem
    . intro contra
      apply contra_not_obs
      rw [← result_suffix (PossiblyInfiniteList.IsSuffix_trans cd_obs_suffix cd_loaded_suffix)]
      apply obs.monotone
      . apply cd_obs.facts_node_subset_result; apply cd_obs.head_mem
      . exact contra

  theorem functional_term_originates_from_some_trigger
      {cd : ChaseDerivation obs rules}
      (node : Node cd)
      {t : GroundTerm sig}
      (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok)
      (t_mem : t ∈ node.val.facts.terms) :
      t ∈ cd.head.facts.terms ∨ ∃ node2, node2 ≼ node ∧ node2.val.origin.is_some_and (fun origin => t ∈ origin.fst.val.fresh_terms_for_head_disjunct origin.snd.val (by rw [← PreTrigger.length_mapped_head]; exact origin.snd.isLt)) := by
    induction node using mem_rec with
    | head => apply Or.inl; exact t_mem
    | step cd2 suffix ih next next_mem =>
      rw [cd2.facts_next next_mem, FactSet.terms_union] at t_mem

      have aux : t ∈ cd2.head.facts.terms -> t ∈ cd.head.facts.terms ∨ ∃ (node2 : cd.Node), node2 ≼ ⟨next, cd2.mem_of_mem_suffix suffix _ (cd2.next_mem_of_mem _ next_mem)⟩ ∧ node2.val.origin.is_some_and (fun origin => t ∈ origin.fst.val.fresh_terms_for_head_disjunct origin.snd.val (by rw [← PreTrigger.length_mapped_head]; exact origin.snd.isLt)) := by
        intro t_mem
        cases ih t_mem with
        | inl ih => apply Or.inl; exact ih
        | inr ih =>
          rcases ih with ⟨node2, prec, t_mem⟩
          apply Or.inr; exists node2; constructor;
          . apply predecessor_trans prec
            exact predecessor_of_suffix suffix (head_prec_next next_mem)
          . exact t_mem

      cases t_mem with
      | inl t_mem => exact aux t_mem
      | inr t_mem =>
        unfold ChaseNode.origin_result at t_mem
        rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_head_iff] at t_mem
        cases t_mem with
        | inl t_mem => rcases t_is_func with ⟨func, ts, arity, t_is_func⟩; rcases t_mem with ⟨c, _, t_mem⟩; rw [← t_mem] at t_is_func; simp [GroundTerm.const, GroundTerm.func] at t_is_func
        | inr t_mem =>
        cases t_mem with
        | inr t_mem =>
          apply Or.inr; exists ⟨next, cd2.mem_of_mem_suffix suffix _ (cd2.next_mem_of_mem _ next_mem)⟩; constructor
          . exact predecessor_refl
          . rw [Option.is_some_and_iff]
            exists next.origin.get (cd2.isSome_origin_next next_mem)
            simp only [Option.some_get, true_and]
            exact t_mem
        | inl t_mem =>
          apply aux
          apply FactSet.terms_subset_of_subset (cd2.active_trigger_origin_next next_mem).left
          rw [List.mem_map] at t_mem
          rcases t_mem with ⟨v, v_mem, t_mem⟩
          rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_body_iff]
          apply Or.inr
          exists v; simp only [t_mem, and_true]
          apply Rule.frontier_subset_vars_body; rw [Rule.mem_frontier_iff_mem_frontier_for_head]; exact ⟨_, v_mem⟩

  theorem trigger_introducing_functional_term_occurs_in_chase
      {cd : ChaseDerivation obs rules}
      (node : Node cd)
      {t : GroundTerm sig}
      (t_mem_node : t ∈ node.val.facts.terms)
      {trg : RTrigger obs rules}
      {disj_idx : Nat}
      {lt : disj_idx < trg.val.rule.head.length}
      (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
      t ∈ cd.head.facts.terms ∨ ∃ node2, node2 ≼ node ∧ node2.val.origin.is_some_and (fun origin => origin.fst.equiv trg ∧ origin.snd.val = disj_idx) := by
    cases functional_term_originates_from_some_trigger node (by
      cases eq : t with
      | const _ =>
        rw [eq] at t_mem_trg
        simp [PreTrigger.fresh_terms_for_head_disjunct, PreTrigger.functional_term_for_var, GroundTerm.func, GroundTerm.const] at t_mem_trg
      | func func ts arity_ok => exists func, ts, arity_ok
    ) t_mem_node with
    | inl t_mem => apply Or.inl; exact t_mem
    | inr t_mem =>
      apply Or.inr
      simp only [Option.is_some_and_iff] at t_mem
      rcases t_mem with ⟨node2, prec, origin, origin_eq, t_mem⟩
      simp only [Option.is_some_and_iff]
      exists node2; simp only [prec, true_and]
      exists origin; simp only [origin_eq, true_and]
      exact RTrigger.equiv_of_term_mem_fresh_terms_for_head_disjunct t_mem t_mem_trg

  theorem result_of_trigger_introducing_functional_term_occurs_in_chase
      {cd : ChaseDerivation obs rules}
      (node : Node cd)
      {t : GroundTerm sig}
      (t_mem_node : t ∈ node.val.facts.terms)
      {trg : RTrigger obs rules}
      {disj_idx : Nat}
      {lt : disj_idx < trg.val.rule.head.length}
      (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
      t ∈ cd.head.facts.terms ∨ (trg.val.mapped_head[disj_idx]'(by rw [PreTrigger.length_mapped_head]; exact lt)).toSet ⊆ node.val.facts := by
    cases trigger_introducing_functional_term_occurs_in_chase node t_mem_node t_mem_trg with
    | inl t_mem => apply Or.inl; exact t_mem
    | inr t_mem =>
      apply Or.inr
      simp only [Option.is_some_and_iff] at t_mem
      rcases t_mem with ⟨node2, prec, origin, origin_eq, equiv, index_eq⟩
      apply Set.subset_trans _ (cd.facts_node_subset_of_prec prec)
      have := node2.val.facts_contain_origin_result
      simp only [origin_eq, Option.is_none_or] at this
      simp only [← PreTrigger.result_eq_of_equiv equiv, ← index_eq]
      exact this

end ChaseDerivation

