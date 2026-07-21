/-
Copyright 2026 Henrik Tscherny, Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

import BasicLeanDatastructures.WellFounded

public import ExistentialRules.ChaseSequence.ChaseBranch
public import ExistentialRules.ChaseSequence.Termination.Basic

import ExistentialRules.ChaseSequence.CoreChase.Basic
public import ExistentialRules.ChaseSequence.CoreChase.CoreChaseNode

/-!
# Core Chase Derivations and Branches

Similar to `RegularChaseDerivation`s and `RegularChaseBranch`es, we define `CoreChaseDerivation`s and `CoreChaseBranch`es.
The main result of this file is that the result of a `CoreChaseBranch` models the underlying `KnowledgeBase`.
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]


abbrev CoreChaseDerivation (rules : RuleSet sig) := ChaseDerivation (CoreChaseNode rules) (RestrictedObsolescence sig) rules

namespace CoreChaseDerivation

variable {rules : RuleSet sig}

section FinitenessOfFactSets

/-!
## Finiteness of FactSets in the Core Chase

If we start a `CoreChaseDerivation` on a finite fact set, all other fact sets (and cores) also remain finite.
For regular chase derivations, we only show this for `ChaseBranch`es that start on a database. However, here we also require such a result on auxiliary results that we show for the `CoreChaseDerivation`.
-/

/-- If the initial facts are finite, then the facts of every node are finite. -/
theorem facts_finite_of_mem_of_head_finite {cd : CoreChaseDerivation rules} (head_fin : cd.head.facts.finite) (node : cd.Node) : node.val.facts.finite := by
  induction node using ChaseDerivation.mem_rec with
  | head => exact head_fin
  | step cd2 suffix ih next next_mem =>
    rw [← next.ingoingFacts_eq, cd2.facts_next next_mem, cd2.head.outgoingFacts_eq]
    apply Set.union_finite_of_both_finite (Set.finite_of_subset_finite ih cd2.head.homSubset.left)
    apply List.finite_toSet

/-- If the initial core is finite, then the cores of every node are finite. -/
theorem core_finite_of_mem_of_head_finite {cd : CoreChaseDerivation rules} (head_fin : cd.head.core.finite) (node : cd.Node) : node.val.core.finite := by
  have node_mem : node.val ∈ cd := node.property
  rw [cd.mem_iff_eq_head_or_mem_tail] at node_mem
  cases node_mem with
  | inl node_mem => rw [node_mem]; exact head_fin
  | inr node_mem =>
    rcases node_mem with ⟨h, node_mem⟩
    apply Set.finite_of_subset_finite (facts_finite_of_mem_of_head_finite (cd := (cd.tail h)) _ ⟨node.val, node_mem⟩) node.val.homSubset.left
    let next := cd.next.get h
    have next_eq : cd.next = some next := by simp [next]
    rw [cd.head_tail', ← next.ingoingFacts_eq, cd.facts_next next_eq, cd.head.outgoingFacts_eq]
    apply Set.union_finite_of_both_finite head_fin
    apply List.finite_toSet

end FinitenessOfFactSets

section HomomorphismsAlongChase

/-!
## Homomorphisms along the Chase

In the regular `ChaseDerivation`, each steps can only add facts, which makes consecutive nodes subsets of each other.
This is not true for the core chase. But at least, we can always find a homomorphism into the next fact set. (This trivially holds for the regular chase derivation as well since with the subset relation the id mapping always forms such a homomorphism.)
-/

/-- For each derivation, there is a homomorphism from its head into every node. -/
theorem exists_homomorphism_from_head_of_mem {cd : CoreChaseDerivation rules} :
    ∀ node ∈ cd, ∃ h : GroundTermMapping sig, h.isHomomorphism cd.head.core node.core := by
  intro node node_mem
  let node : cd.Node := ⟨node, node_mem⟩
  show ∃ h : GroundTermMapping sig, h.isHomomorphism cd.head.core node.val.core
  induction node using cd.mem_rec with
  | head => exact ⟨id, GroundTermMapping.isHomomorphism_id_of_subset Set.subset_refl⟩
  | step cd2 suffix ih next next_eq =>
    rcases ih with ⟨h_ih, h_ih_hom⟩
    rcases next.homSubset.right with ⟨h_next, h_next_hom⟩
    have id_hom_to_next : GroundTermMapping.isHomomorphism id cd2.head.core next.facts := by
      apply GroundTermMapping.isHomomorphism_id_of_subset
      rw [← next.ingoingFacts_eq, cd2.facts_next next_eq]
      rw [cd2.head.outgoingFacts_eq]
      exact Set.subset_union_of_subset_left Set.subset_refl
    exists h_next ∘ id ∘ h_ih
    apply GroundTermMapping.isHomomorphism_compose
    apply GroundTermMapping.isHomomorphism_compose
    . exact h_ih_hom
    . exact id_hom_to_next
    . exact h_next_hom

/-- The head's core cannot occur again in the tail. If this was the case and since we always find homomorphism from to successor cores, we can argue that then the triggers would have already been satisfied. The same theorem exists for regular `ChaseDerivation`s but the argument is easier for them. -/
theorem head_core_not_mem_tail_of_finite {cd : CoreChaseDerivation rules} (head_finite : cd.head.core.finite) : ∀ h,
    ∀ node ∈ cd.tail h, cd.head.core ≠ node.core := by
  intro h node node_mem contra
  let next := cd.next.get h
  have next_eq : cd.next = some next := by simp [next]
  let origin := next.origin.get (cd.isSome_origin_next next_eq)
  apply next.origin_trg_inactive_of_isWeakCore_of_homSubset_of_finite cd.head.isWeakCore _ head_finite origin (by simp [origin])
  . exact cd.active_trigger_origin_next next_eq
  . constructor
    . rw [← next.ingoingFacts_eq, cd.facts_next next_eq, cd.head.outgoingFacts_eq]
      exact Set.subset_union_of_subset_left Set.subset_refl
    . -- there exists a homomorphism from next to (the second occurrence of) cd.head
      rcases exists_homomorphism_from_head_of_mem _ node_mem with ⟨h, hom⟩
      rw [ChaseDerivation.head_tail'] at hom
      -- we also have a homomorphism from next.facts to next.core by definition
      rcases next.homSubset.right with ⟨h_core, h_core_hom⟩
      -- we can compose both homomorphisms into a homomorphism from next.facts to cd.head.core
      let h_facts_head : GroundTermMapping sig := h ∘ h_core
      have h_facts_head_hom : h_facts_head.isHomomorphism next.facts cd.head.core := by
        apply GroundTermMapping.isHomomorphism_compose; exact h_core_hom; rw [contra]; exact hom
      exists h_facts_head

/-- The `head` cannot occur in the `tail`. Otherwise, the same fact set would occur twice in the chase. But since we always find homomorphism from to successor fact sets, we can argue that then the triggers would have already been satisfied. The same theorem exists for regular `ChaseDerivation`s but the argument is easier for them. -/
theorem head_not_mem_tail_of_finite {cd : CoreChaseDerivation rules} (head_finite : cd.head.core.finite) : ∀ h, ¬ cd.head ∈ cd.tail h := by
  intro h contra
  exact cd.head_core_not_mem_tail_of_finite head_finite h _ contra rfl

/-- By `head_not_mem_tail_of_finite`, if we have a suffix but our head occurs in the suffix, then our suffix is equal to us. -/
@[grind ->]
theorem eq_of_suffix_of_head_mem_of_finite {cd1 cd2 : CoreChaseDerivation rules} (suffix : cd1 <:+ cd2) (head_mem : cd2.head ∈ cd1) (head_finite : cd2.head.core.finite) : cd1 = cd2 := by
  rw [ChaseDerivation.suffix_iff_eq_or_suffix_tail] at suffix
  cases suffix with
  | inl suffix => exact suffix
  | inr suffix => rcases suffix with ⟨h, suffix⟩; apply False.elim; apply head_not_mem_tail_of_finite head_finite h; apply ChaseDerivation.mem_of_mem_suffix suffix; exact head_mem

/-- And now by `eq_of_suffix_of_head_mem_of_finite`, if we have two suffixes $C$ and $D$, and the head of $D$ occurs in $C$, then $D$ is a suffix of $C$. This also holds for regular chase derivations but for different reasons (see the differences of `head_not_mem_tail_of_finite` and `ChaseDerivation.head_not_mem_tail`.) -/
@[grind ->]
theorem suffix_of_suffix_of_suffix_of_head_mem_of_finite {cd cd1 cd2 : CoreChaseDerivation rules} : cd1 <:+ cd -> cd2 <:+ cd -> cd2.head ∈ cd1 -> cd2.head.core.finite -> cd2 <:+ cd1 := by
  intro suffix1 suffix2 head_mem head_finite
  cases PossiblyInfiniteList.suffix_or_suffix_of_suffix suffix1 suffix2 with
  | inr suffix => exact suffix
  | inl suffix => rw [eq_of_suffix_of_head_mem_of_finite suffix head_mem head_finite]; exact PossiblyInfiniteList.IsSuffix_refl

end HomomorphismsAlongChase

section Predecessors

/-!
## Predecessor Relation

We port the predecessor results from the `ChaseDerivation` that are there only shown for derivations with `RegularChaseNode`s. But since we have `suffix_of_suffix_of_suffix_of_head_mem_of_finite`, we can also show these for `CoreChaseDerivation`s given that the cores are finite.

We also add a few results on top that are specific to the core chase such as `exists_homomorphism_of_prec` or `core_not_subset_of_strict_predecessor` (where the latter is a variant of `ChaseDerivation.facts_not_subset_of_strict_predecessor`.
-/

/-- The predecessor relation is antisymmetric. -/
@[grind ->]
theorem predecessor_antisymm_of_finite {cd : CoreChaseDerivation rules} {n1 n2 : cd.Node} (n1_fin : n1.val.core.finite) (n2_fin : n2.val.core.finite) :
    n1 ≼ n2 -> n2 ≼ n1 -> n1 = n2 := by
  simp only [cd.predecessor_iff]; grind

/-- The predecessor relation is transitive. -/
@[grind ->]
theorem predecessor_trans_of_finite {cd : CoreChaseDerivation rules} {n1 n2 n3 : cd.Node} (n2_fin : n2.val.core.finite) :
    n1 ≼ n2 -> n2 ≼ n3 -> n1 ≼ n3 := by
  simp only [cd.predecessor_iff]; grind

/-- We can express fairness in terms of the predecessor relation: For each trigger, there is a node such that the trigger is not active for each of the node's successors. -/
theorem fairness_prec_of_finite {cd : CoreChaseDerivation rules} (head_fin : cd.head.core.finite) : ∀ (trg : RTrigger (RestrictedObsolescence sig) rules), ∃ (node : cd.Node), ∀ node2, node ≼ node2 -> ¬ trg.val.active node2.val.core := by
  intro trg
  rcases cd.fairness' trg with ⟨cd2, suffix, fair⟩
  exists ⟨cd2.head, cd2.mem_of_mem_suffix suffix _ cd2.head_mem⟩
  intro node2 prec
  apply fair
  rw [cd.predecessor_iff] at prec
  rcases prec with ⟨cd3, suf3, head3, node2_mem_cd3⟩
  simp only at head3
  have : cd3 = cd2 := by
    have cd2_head_fin : cd2.head.core.finite := by
      let cd2_head_node : cd.Node := ⟨cd2.head, by apply ChaseDerivation.mem_of_mem_suffix suffix; exact cd2.head_mem⟩
      exact cd.core_finite_of_mem_of_head_finite head_fin cd2_head_node
    apply eq_of_suffix_of_head_mem_of_finite _ (by rw [← head3]; exact cd3.head_mem) cd2_head_fin
    apply suffix_of_suffix_of_suffix_of_head_mem_of_finite suffix suf3 _ (by rw [head3]; exact cd2_head_fin)
    rw [head3]; exact cd2.head_mem
  rw [← this]
  exact node2_mem_cd3

/-- For each node, there exists a homomorphism to each of its successors. -/
theorem exists_homomorphism_of_prec {cd : CoreChaseDerivation rules} {n1 n2 : cd.Node} :
    n1 ≼ n2 -> ∃ h : GroundTermMapping sig, h.isHomomorphism n1.val.core n2.val.core := by
  rw [cd.predecessor_iff]; intro ⟨cd2, suffix, head_eq, n2_mem⟩
  rw [← head_eq]
  exact exists_homomorphism_from_head_of_mem (cd := cd2) n2.val n2_mem


section StrictPredecessor

/-- The strict predecessor relation is asymmetric. -/
@[grind ->]
theorem strict_predecessor_asymmetric_of_finite {cd : CoreChaseDerivation rules} {n1 n2 : cd.Node}
    (n1_fin : n1.val.core.finite) (n2_fin : n2.val.core.finite) :
    n1 ≺ n2 -> ¬ n2 ≺ n1 := by
  intro prec contra; apply prec.right; apply predecessor_antisymm_of_finite n1_fin n2_fin prec.left contra.left

/-- The strict predecessor relation is transitive. -/
@[grind ->]
theorem strict_predecessor_trans_of_finite {cd : CoreChaseDerivation rules} {n1 n2 n3 : cd.Node}
    (n1_fin : n1.val.core.finite) (n2_fin : n2.val.core.finite) :
    n1 ≺ n2 -> n2 ≺ n3 -> n1 ≺ n3 := by
  intro prec1 prec2
  constructor
  . exact predecessor_trans_of_finite n2_fin prec1.left prec2.left
  . grind

/-- The `ChaseDerivationSkeleton.head` is a strict predecessor of `ChaseDerivationSkeleton.next`. -/
theorem head_strict_prec_next_of_finite {cd : CoreChaseDerivation rules} (head_fin : cd.head.core.finite) :
    ∀ {next}, (mem : next ∈ cd.next) -> ⟨cd.head, cd.head_mem⟩ ≺ ⟨next, cd.next_mem_of_mem _ mem⟩ := by
  intro next next_mem
  constructor
  . exact cd.head_prec_next next_mem
  . intro contra
    apply cd.head_not_mem_tail_of_finite head_fin (by rw [next_mem]; simp)
    grind

/-- The core of a strict successor cannot be a subset of our core. Otherwise, our current core would not be a core. -/
@[grind ->]
theorem core_not_subset_of_strict_predecessor_of_finite {cd : CoreChaseDerivation rules} {n1 n2 : cd.Node} (n1_fin : n1.val.core.finite) :
    n1 ≺ n2 -> ¬ n2.val.core ⊆ n1.val.core := by
  intro ⟨prec, ne⟩ contra
  have cores_eq : n2.val.core = n1.val.core := by
    apply FactSet.homSubset_eq_self_of_isWeakCore_of_finite _ n1.val.isWeakCore n1_fin
    exact ⟨contra, exists_homomorphism_of_prec prec⟩
  rw [cd.predecessor_iff] at prec
  rcases prec with ⟨cd2, suffix, head_eq, n2_mem⟩
  rw [cd2.mem_iff_eq_head_or_mem_tail] at n2_mem
  cases n2_mem with
  | inl n2_mem => apply ne; rw [Subtype.mk.injEq]; grind
  | inr n2_mem =>
    rcases n2_mem with ⟨next_some, n2_mem⟩
    apply head_core_not_mem_tail_of_finite (cd := cd2) (by rw [head_eq]; exact n1_fin) next_some _ n2_mem
    rw [head_eq, cores_eq]

end StrictPredecessor

end Predecessors

section TermsInChase

/-!
## Terms in the Chase

We make some general observations about certain terms that might occur in the chase.

1. Constants can only originate directly from rules or from the initial fact set. No other constants can be introduced.
2. Functional terms can either also originate from the initial fact set or they are introduced as fresh terms by a trigger.

The second observation entails that the precense of a functional term that does not occur in the initial fact set implies
that the trigger that introduces this term must have been applied in some `ChaseNode`.
-/


/-- Constants in the chase can only come from the initial fact set or from a constant in a rule. -/
theorem constants_node_subset_constants_fs_union_constants_rules
    {cd : CoreChaseDerivation rules}
    {next_some : cd.next.isSome}
    {node : CoreChaseNode rules} (node_mem : node ∈ cd.tail next_some) :
    node.facts.constants ⊆ cd.head.core.constants ∪ rules.head_constants :=
  ChaseDerivation.constants_node_subset_constants_fs_union_constants_rules CoreChaseNode.out_sub_in node_mem

/-- Each functional term in the chase originates as a fresh term from a trigger if it was not already part of the initial fact set. -/
theorem functional_term_originates_from_some_trigger
    {cd : CoreChaseDerivation rules}
    {next_some : cd.next.isSome}
    (start_finite : cd.head.core.finite)
    (node : (cd.tail next_some).Node)
    {t : GroundTerm sig}
    (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok)
    (t_mem : t ∈ node.val.facts.terms) :
    t ∈ cd.head.core.terms ∨ ∃ node2, node2 ≼ node ∧ ∃ orig ∈ node2.val.origin, t ∈ orig.fst.val.fresh_terms_for_head_disjunct orig.snd.val (by rw [← PreTrigger.length_mapped_head]; exact orig.snd.isLt) := by
  apply ChaseDerivation.functional_term_originates_from_some_trigger CoreChaseNode.out_sub_in _ node t_is_func t_mem
  intro n1 n2 n3; apply predecessor_trans_of_finite; apply core_finite_of_mem_of_head_finite; rw [ChaseDerivation.head_tail']; apply cd.core_finite_of_mem_of_head_finite _ ⟨cd.next.get next_some, by apply cd.next_mem_of_mem; simp⟩; exact start_finite

/-- If a functional term occurs in the chase, then the trigger that introduces this term must have been used in the chase, unless the term already occurs in the initial fact set. -/
theorem trigger_introducing_functional_term_occurs_in_chase
    {cd : CoreChaseDerivation rules}
    {next_some : cd.next.isSome}
    (start_finite : cd.head.core.finite)
    (node : (cd.tail next_some).Node)
    {t : GroundTerm sig}
    (t_mem_node : t ∈ node.val.facts.terms)
    {trg : RTrigger (RestrictedObsolescence sig) rules}
    {disj_idx : Nat}
    {lt : disj_idx < trg.val.rule.head.length}
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
    t ∈ cd.head.core.terms ∨ ∃ node2, node2 ≼ node ∧ ∃ orig ∈ node2.val.origin, orig.fst.equiv trg ∧ orig.snd.val = disj_idx := by
  apply ChaseDerivation.trigger_introducing_functional_term_occurs_in_chase CoreChaseNode.out_sub_in _ node t_mem_node t_mem_trg
  intro n1 n2 n3; apply predecessor_trans_of_finite; apply core_finite_of_mem_of_head_finite; rw [ChaseDerivation.head_tail']; apply cd.core_finite_of_mem_of_head_finite _ ⟨cd.next.get next_some, by apply cd.next_mem_of_mem; simp⟩; exact start_finite

end TermsInChase

section Result

/-!
## Core Chase Result

Oppossed to regular chase derivations, the result of a core chase derivation is only defined if the derivation terminates. Then it is simply the last element.
Just like for RegularChaseDerivations however, the result also models all rules.
-/

abbrev result (cd : CoreChaseDerivation rules) (term : cd.terminates) : FactSet sig := (cd.last term).core

/-- The result is a model of all rules. This is true because otherwise, there would be an active trigger on the result. But we already know that no trigger can be active on the last node of a terminating chase derivation. -/
@[grind <-]
theorem result_models_rules {cd : CoreChaseDerivation rules} (term : cd.terminates) : (cd.result term).modelsRules rules := by
  intro r r_mem subs subs_loaded
  let trg : Trigger (RestrictedObsolescence sig) := ⟨r, subs⟩
  have trg_loaded : trg.loaded (cd.result term) := subs_loaded
  apply (RestrictedObsolescence sig).cond_implies_trg_is_satisfied (trg := trg)
  apply Classical.byContradiction; intro contra
  apply cd.trg_inactive_for_last term ⟨trg, r_mem⟩
  constructor
  . rw [CoreChaseNode.outgoingFacts_eq]; exact trg_loaded
  . rw [CoreChaseNode.outgoingFacts_eq]; exact contra

end Result

end CoreChaseDerivation


abbrev CoreChaseBranch (kb : KnowledgeBase sig) := ChaseBranch (CoreChaseNode kb.rules) (RestrictedObsolescence sig) kb

namespace CoreChaseBranch

variable {kb : KnowledgeBase sig}

section FinitenessOfFactSets

/-!
## Finiteness of FactSets in the Core Chase

Just as in a regular `ChaseBranch`, every fact set (and every core) that occurs in the `CoreChaseBranch` is finite simply since the (initial) database is finite and since each step only adds finitely many facts.
-/

/- Each fact set in the chase is finite. -/
theorem facts_finite_of_mem {cb : CoreChaseBranch kb} (node : cb.Node) : node.val.facts.finite := by
  apply CoreChaseDerivation.facts_finite_of_mem_of_head_finite
  rw [← cb.head.ingoingFacts_eq, cb.database_first'.left]; exact kb.db.toFactSet.property.left

/- Each core in the chase is finite. -/
theorem core_finite_of_mem {cb : CoreChaseBranch kb} (node : cb.Node) : node.val.core.finite := by
  apply Set.finite_of_subset_finite (cb.facts_finite_of_mem node) node.val.homSubset.left

end FinitenessOfFactSets

section DatabaseContainment

/-!
## Database Containment

Even though we do not have fact set monotonicity in the core chase, it is still true that the database occurs in every fact set and core in the chase.
This is because the database only features constants and these can never be remapped by any homomorphism.
This result is essential for showing that the core chase result is a model, which we also show here.
-/

/-- The database is a subset of each node since the database only contains constants which can never be remapped by homomorphisms. -/
theorem db_mem_of_mem {cb : CoreChaseBranch kb} : ∀ (node : cb.Node), kb.db.toFactSet.val ⊆ node.val.core := by
  intro node
  rcases CoreChaseDerivation.exists_homomorphism_from_head_of_mem _ node.property with ⟨h, hom⟩
  intro f f_mem
  apply hom.right
  rw [← CoreChaseNode.outgoingFacts_eq, cb.database_first'.right.left]
  rw [GroundTermMapping.mem_applyFactSet]; exists f; constructor; exact f_mem
  apply Eq.symm; apply h.applyFact_eq_self_of_isIdOnConstants_of_isFunctionFree
  . exact hom.left
  . exact kb.db.toFactSet.property.right f f_mem

/-- The result of a `CoreChaseBranch` models the whole `KnowledgeBase`. -/
@[grind <-]
theorem result_models_kb {cb : CoreChaseBranch kb} (term : cb.terminates) : (CoreChaseDerivation.result cb.toChaseDerivation term).modelsKb kb := by
  constructor
  . exact cb.db_mem_of_mem ⟨cb.last term, cb.last_mem term⟩
  . exact CoreChaseDerivation.result_models_rules term

end DatabaseContainment

section Predecessors

/-!
## Predecessor Relation

Compared to the `CoreChaseDerivation`, we can now drop the explicit finiteness conditions.
-/

/-- The predecessor relation is antisymmetric. -/
@[grind ->]
theorem predecessor_antisymm {cb : CoreChaseBranch kb} {n1 n2 : cb.Node} : n1 ≼ n2 -> n2 ≼ n1 -> n1 = n2 := by
  apply CoreChaseDerivation.predecessor_antisymm_of_finite <;> apply core_finite_of_mem

/-- The predecessor relation is transitive. -/
@[grind ->]
theorem predecessor_trans {cb : CoreChaseBranch kb} {n1 n2 n3 : cb.Node} :
    n1 ≼ n2 -> n2 ≼ n3 -> n1 ≼ n3 := by
  apply CoreChaseDerivation.predecessor_trans_of_finite; apply core_finite_of_mem

/-- We can express fairness in terms of the predecessor relation: For each trigger, there is a node such that the trigger is not active for each of the node's successors. -/
theorem fairness_prec {cb : CoreChaseBranch kb} : ∀ (trg : RTrigger (RestrictedObsolescence sig) kb.rules), ∃ (node : cb.Node), ∀ node2, node ≼ node2 -> ¬ trg.val.active node2.val.core := by
  apply CoreChaseDerivation.fairness_prec_of_finite; exact core_finite_of_mem ⟨cb.head, cb.head_mem⟩


section StrictPredecessor

/-- The strict predecessor relation is asymmetric. -/
@[grind ->]
theorem strict_predecessor_asymmetric {cb : CoreChaseBranch kb} {n1 n2 : cb.Node} : n1 ≺ n2 -> ¬ n2 ≺ n1 := by
  apply CoreChaseDerivation.strict_predecessor_asymmetric_of_finite <;> apply core_finite_of_mem

/-- The strict predecessor relation is transitive. -/
@[grind ->]
theorem strict_predecessor_trans {cb : CoreChaseBranch kb} {n1 n2 n3 : cb.Node} : n1 ≺ n2 -> n2 ≺ n3 -> n1 ≺ n3 := by
  apply CoreChaseDerivation.strict_predecessor_trans_of_finite <;> apply core_finite_of_mem

/-- The `ChaseDerivationSkeleton.head` is a strict predecessor of `ChaseDerivationSkeleton.next`. -/
theorem head_strict_prec_next {cb : CoreChaseBranch kb} :
    ∀ {next}, (mem : next ∈ cb.next) -> ⟨cb.head, cb.head_mem⟩ ≺ ⟨next, cb.next_mem_of_mem _ mem⟩ := by
  apply CoreChaseDerivation.head_strict_prec_next_of_finite; exact core_finite_of_mem ⟨cb.head, cb.head_mem⟩

/-- The core of a strict successor cannot be a subset of our core. Otherwise, our current core would not be a core. -/
@[grind ->]
theorem core_not_subset_of_strict_predecessor {cb : CoreChaseBranch kb} {n1 n2 : cb.Node} : n1 ≺ n2 -> ¬ n2.val.core ⊆ n1.val.core := by
  apply CoreChaseDerivation.core_not_subset_of_strict_predecessor_of_finite; apply core_finite_of_mem

end StrictPredecessor

section WellFounded

/-- The `strict_predecessor` relation is `WellFounded`. -/
theorem wellFounded_pred {cb : CoreChaseBranch kb} : WellFounded cb.strict_predecessor := by
  constructor; intro node
  induction node using cb.mem_rec with
  | head =>
    constructor; intro node prec
    exfalso
    apply cb.core_not_subset_of_strict_predecessor prec
    rw [← cb.head.outgoingFacts_eq, cb.database_first'.right.left]
    apply cb.db_mem_of_mem
  | step cd2 suf ih next next_mem =>
    constructor
    intro n2 prec
    let cd2_head : cb.Node := ⟨cd2.head, cd2.mem_of_mem_suffix suf _ cd2.head_mem⟩
    suffices n2 = cd2_head ∨ n2 ≺ cd2_head by
      cases this with
      | inl eq => rw [eq]; exact ih
      | inr prec => rcases ih with ⟨_, ih⟩; apply ih; exact prec
    cases cb.predecessor_total n2 ⟨cd2.head, cd2.mem_of_mem_suffix suf _ cd2.head_mem⟩ with
    | inl prec' => apply cb.eq_or_strict_of_predecessor; exact prec'
    | inr prec' =>
      cases cb.eq_or_strict_of_predecessor prec' with
      | inl eq => apply Or.inl; exact Eq.symm eq
      | inr prec' =>
        exfalso
        suffices ⟨next, cd2.mem_of_mem_suffix suf _ (cd2.next_mem_of_mem _ next_mem)⟩ ≼ n2 by
          apply prec.right
          apply CoreChaseDerivation.predecessor_antisymm_of_finite
          . apply cb.core_finite_of_mem
          . apply cb.core_finite_of_mem
          . exact prec.left
          . exact this
        have ne := prec'.right
        have prec' := prec'.left
        rw [cb.predecessor_iff] at prec'; rcases prec' with ⟨cd2', suf2, head_eq, n2_mem⟩
        suffices cd2 = cd2' by
          let cd2_head' : cd2.Node := ⟨cd2.head, cd2.head_mem⟩
          let n2' : cd2.Node := ⟨n2.val, by rw [this]; exact n2_mem⟩
          have prec : cd2_head' ≺ n2' := by
            constructor
            . rw [cd2.predecessor_iff]; exists cd2; constructor; exact PossiblyInfiniteList.IsSuffix_refl; grind
            . grind
          exact ChaseDerivationSkeleton.predecessor_of_suffix suf (cd2.next_prec_of_head_strict_prec prec next_mem)
        apply CoreChaseDerivation.eq_of_suffix_of_head_mem_of_finite
        . apply CoreChaseDerivation.suffix_of_suffix_of_suffix_of_head_mem_of_finite suf2 suf
          . simp only at head_eq; rw [← head_eq]; exact cd2'.head_mem
          . exact cb.core_finite_of_mem cd2_head
        . rw [head_eq]; exact cd2.head_mem
        . rw [head_eq]; exact cb.core_finite_of_mem cd2_head

instance {cb : CoreChaseBranch kb} : WellFoundedRelation cb.Node where
  rel := cb.strict_predecessor
  wf := wellFounded_pred

end WellFounded

end Predecessors

section TermsInChase

/-!
## Terms in the Chase

We make some general observations about certain terms that might occur in the chase.

1. Constants can only originate directly from rules or from the initial fact set. No other constants can be introduced.
2. Functional terms can either also originate from the initial fact set or they are introduced as fresh terms by a trigger.

The second observation entails that the precense of a functional term that does not occur in the initial fact set implies
that the trigger that introduces this term must have been applied in some `ChaseNode`.
-/

/-- Constants in the chase must be in the database or in some rule. -/
theorem constants_node_subset_constants_db_union_constants_rules {cb : CoreChaseBranch kb} {node : cb.Node} :
    node.val.facts.constants ⊆ (kb.db.constants.val ∪ kb.rules.head_constants) := by
  cases ChaseDerivation.mem_iff_eq_head_or_mem_tail.mp node.property with
  | inl node_mem => apply Set.subset_union_of_subset_left; rw [node_mem, ← cb.head.ingoingFacts_eq, cb.database_first'.left, Database.toFactSet_constants_same]; exact Set.subset_refl
  | inr node_mem =>
    rcases node_mem with ⟨_, node_mem⟩
    rw [← Database.toFactSet_constants_same, ← cb.database_first'.right.left, cb.head.outgoingFacts_eq]
    exact CoreChaseDerivation.constants_node_subset_constants_fs_union_constants_rules node_mem

/-- Each functional term in the chase originates as a fresh term from a trigger. -/
theorem functional_term_originates_from_some_trigger
    {cb : CoreChaseBranch kb}
    (node : cb.Node)
    {t : GroundTerm sig}
    (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok)
    (t_mem : t ∈ node.val.facts.terms) :
    ∃ node2, node2 ≼ node ∧ ∃ orig ∈ node2.val.origin,
      t ∈ orig.fst.val.fresh_terms_for_head_disjunct orig.snd.val (by rw [← PreTrigger.length_mapped_head]; exact orig.snd.isLt) := by
  have t_nmem_head : t ∉ cb.head.core.terms := by
    intro t_mem
    exact cb.func_term_not_mem_head t_is_func t_mem
  cases ChaseDerivation.mem_iff_eq_head_or_mem_tail.mp node.property with
  | inl node_mem =>
    rw [node_mem, ← cb.head.ingoingFacts_eq, cb.database_first'.left, ← cb.database_first'.right.left] at t_mem
    apply False.elim; apply t_nmem_head; exact t_mem
  | inr node_mem =>
    have start_finite := (cb.core_finite_of_mem ⟨_, cb.head_mem⟩)
    rcases node_mem with ⟨next_some, node_mem⟩
    cases CoreChaseDerivation.functional_term_originates_from_some_trigger start_finite ⟨node.val, node_mem⟩ t_is_func t_mem with
    | inl t_mem => apply False.elim; exact t_nmem_head t_mem
    | inr t_mem =>
      rcases t_mem with ⟨node2, prec, t_mem⟩
      have suf : (cb.tail next_some) <:+ cb.toChaseDerivation := PossiblyInfiniteList.IsSuffix_tail
      exact ⟨_, ChaseDerivationSkeleton.predecessor_of_suffix suf prec, t_mem⟩

/-- If a functional term occurs in the chase, then the trigger that introduces this term must have been used in the chase. -/
theorem trigger_introducing_functional_term_occurs_in_chase
    {cb : CoreChaseBranch kb}
    (node : cb.Node)
    {t : GroundTerm sig}
    (t_mem_node : t ∈ node.val.facts.terms)
    {trg : RTrigger (RestrictedObsolescence sig) kb.rules}
    {disj_idx : Nat}
    {lt : disj_idx < trg.val.rule.head.length}
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
    ∃ node2, node2 ≼ node ∧ ∃ orig ∈ node2.val.origin, orig.fst.equiv trg ∧ orig.snd.val = disj_idx := by
  have t_nmem_head : t ∉ cb.head.core.terms := by
    intro t_mem
    exact cb.func_term_not_mem_head (PreTrigger.term_functional_of_mem_fresh_terms _ t_mem_trg) t_mem
  cases ChaseDerivation.mem_iff_eq_head_or_mem_tail.mp node.property with
  | inl node_mem =>
    rw [node_mem, ← cb.head.ingoingFacts_eq, cb.database_first'.left, ← cb.database_first'.right.left] at t_mem_node
    apply False.elim; apply t_nmem_head; exact t_mem_node
  | inr node_mem =>
    have start_finite := (cb.core_finite_of_mem ⟨_, cb.head_mem⟩)
    rcases node_mem with ⟨next_some, node_mem⟩
    cases CoreChaseDerivation.trigger_introducing_functional_term_occurs_in_chase start_finite ⟨node.val, node_mem⟩ t_mem_node t_mem_trg with
    | inl t_mem => apply False.elim; exact t_nmem_head t_mem
    | inr t_mem =>
      rcases t_mem with ⟨node2, prec, t_mem⟩
      have suf : (cb.tail next_some) <:+ cb.toChaseDerivation := PossiblyInfiniteList.IsSuffix_tail
      exact ⟨_, ChaseDerivationSkeleton.predecessor_of_suffix suf prec, t_mem⟩

end TermsInChase

section MinimalNodeWithProp

/-!
## Minimal Nodes with given Properties

If a property hold for a given node in the chase, then there must be a "first" node for which this property holds. That means that this node is minimal with respect to the `≺` relation.
The result follows by the well foundedness of the `≺` relation.
-/

theorem prop_for_node_has_minimal_such_node
    {cb : CoreChaseBranch kb} (prop : cb.Node -> Prop) :
    ∀ n, prop n -> ∃ n2, prop n2 ∧ ∀ n3, n3 ≺ n2 -> ¬ prop n3 := by
  intro n prop_n
  exact minimal_element_for_property_and_relation prop n prop_n

end MinimalNodeWithProp

section OriginTriggerRemainsInactive

/-!
## Used triggers remain inactive

Here we prove that triggers used in the core chase remain inactive from this point.
Not only that but also every equivalent trigger (producing the same result) is inactive from this point on.
For regular chase derivations this is trivial because of fact monotonicity but here it is not quite obvious (even though it's intuitive).
-/

theorem origin_trg_remains_inactive {cb : CoreChaseBranch kb} {n1 n2 : cb.Node} (prec : n1 ≼ n2) :
    ∀ orig ∈ n1.val.origin, ∀ trg, orig.fst.equiv trg -> ¬ trg.val.active n2.val.core := by
  -- part of this can be proven with CoreChaseNode.origin_trg_inactive_for_own_core_of_finite
  sorry

end OriginTriggerRemainsInactive

end CoreChaseBranch

