import ProofLibrary.KnowledgeBaseBasics
import ProofLibrary.SubstitutionAndHomomorphismBasics

structure PreTrigger where
  rule : Rule
  subs : GroundSubstitution

namespace PreTrigger
  def skolemize_var_or_const (trg : PreTrigger) (disjunctIndex : Nat) (var_or_const : VarOrConst) : SkolemTerm :=
    var_or_const.skolemize trg.rule.id disjunctIndex trg.rule.frontier

  def apply_to_skolemized_term (trg : PreTrigger) (skolem_term : SkolemTerm) : GroundTerm :=
    trg.subs.apply_skolem_term skolem_term

  def apply_to_var_or_const (trg : PreTrigger) (disjunctIndex : Nat) : VarOrConst -> GroundTerm :=
    (trg.apply_to_skolemized_term ∘ (trg.skolemize_var_or_const disjunctIndex))

  def apply_to_function_free_atom (trg : PreTrigger) (disjunctIndex : Nat) (atom : FunctionFreeAtom) : Fact :=
    {
      predicate := atom.predicate
      terms := atom.terms.map (trg.apply_to_var_or_const disjunctIndex)
    }

  theorem apply_to_function_free_atom_terms_same_length (trg : PreTrigger) (disjunctIndex : Nat) (atom : FunctionFreeAtom) : atom.terms.length = (trg.apply_to_function_free_atom disjunctIndex atom).terms.length := by
    unfold apply_to_function_free_atom
    simp

  def mapped_body (trg : PreTrigger) : List Fact := SubsTarget.apply trg.subs trg.rule.body
  def mapped_head (trg : PreTrigger) : List (List Fact) := trg.rule.head.enum.map (fun (i, h) => h.map (trg.apply_to_function_free_atom i))

  theorem head_length_eq_mapped_head_length (trg : PreTrigger) : trg.rule.head.length = trg.mapped_head.length := by
    unfold mapped_head
    rw [List.length_map, List.length_enum]

  def result (trg : PreTrigger) : List FactSet :=
    trg.mapped_head.map List.toSet

  theorem subs_application_is_injective_for_freshly_introduced_terms {t : Variable} (trg : PreTrigger) (disjunctIndex : Fin trg.rule.head.length) (t_not_in_frontier : ¬ t ∈ trg.rule.frontier) : ∀ s, (trg.apply_to_var_or_const disjunctIndex (VarOrConst.var t) = trg.apply_to_var_or_const disjunctIndex (VarOrConst.var s)) -> trg.skolemize_var_or_const disjunctIndex (VarOrConst.var t) = trg.skolemize_var_or_const disjunctIndex (VarOrConst.var s) := by
    intro s apply_eq_for_t_and_s

    cases Decidable.em (s ∈ trg.rule.frontier) with
    | inr hr =>
      simp [t_not_in_frontier, hr, apply_to_var_or_const, apply_to_skolemized_term, skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize] at apply_eq_for_t_and_s
      simp [t_not_in_frontier, hr, apply_to_var_or_const, apply_to_skolemized_term, skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize]
      injection apply_eq_for_t_and_s with tree_node_eq
      injection tree_node_eq
    | inl hl =>
      simp [t_not_in_frontier, hl, apply_to_var_or_const, apply_to_skolemized_term, skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize] at apply_eq_for_t_and_s
      apply False.elim
      let tree_for_s := trg.apply_to_var_or_const disjunctIndex (VarOrConst.var s)
      let ts := trg.rule.frontier.map (fun fv => trg.subs fv)
      let a : SkolemFS := { ruleId := trg.rule.id, disjunctIndex, var := t }
      apply FiniteTree.tree_eq_while_contained_is_impossible tree_for_s (FiniteTreeList.fromList ts) a
      simp [tree_for_s, apply_to_var_or_const, apply_to_skolemized_term, skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, hl]
      apply apply_eq_for_t_and_s
      simp [tree_for_s, apply_to_var_or_const, apply_to_skolemized_term, skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, hl]
      apply List.listToSetElementAlsoListElement
      rw [FiniteTreeList.fromListToListIsId]
      apply List.mappedElemInMappedList
      apply List.listElementAlsoToSetElement
      apply hl

  def idx_of_fact_in_result (trg : PreTrigger) (f : Fact) (disj_index : Fin trg.result.length) (f_in_res : f ∈ trg.result.get disj_index) : Fin (trg.rule.head.get ⟨disj_index.val, (by rw [head_length_eq_mapped_head_length]; have isLt := disj_index.isLt; unfold result at isLt; simp only [List.length_map] at isLt; exact isLt)⟩).length :=
    let disj_index_mapped_head : Fin trg.mapped_head.length := ⟨disj_index.val, (by have isLt := disj_index.isLt; unfold result at isLt; simp only [List.length_map] at isLt; exact isLt)⟩
    let fin_mapped := (trg.mapped_head.get disj_index_mapped_head).idx_of f ((trg.mapped_head.get disj_index_mapped_head).listToSetElementAlsoListElement f (by unfold result at f_in_res; simp at f_in_res; apply f_in_res))
    have fin_mapped_isLt := fin_mapped.isLt
    ⟨fin_mapped.val, by simp [mapped_head] at fin_mapped_isLt; exact fin_mapped_isLt⟩

  theorem apply_subs_to_atom_at_idx_same_as_fact_at_idx (trg : PreTrigger) (disj_index : Fin trg.rule.head.length) (idx : Fin (trg.rule.head.get disj_index).length) : trg.apply_to_function_free_atom disj_index ((trg.rule.head.get disj_index).get idx) = (trg.mapped_head.get ⟨disj_index.val, (by rw [← head_length_eq_mapped_head_length]; exact disj_index.isLt)⟩).get ⟨idx.val, (by unfold mapped_head; simp)⟩ := by
    unfold mapped_head
    simp

  def loaded (trg : PreTrigger) (F : FactSet) : Prop :=
    trg.mapped_body.toSet ⊆ F

  theorem term_mapping_preserves_loadedness (trg : PreTrigger) (F : FactSet) (h : GroundTermMapping) (hh : isIdOnConstants h) : trg.loaded F -> { rule := trg.rule, subs := h ∘ trg.subs : PreTrigger }.loaded (applyFactSet h F) := by
    simp [loaded, mapped_body]
    induction trg.rule.body with
    | nil => intro _ _ _; contradiction
    | cons head tail ih =>
      intro base f hf
      simp [Set.element, Set.union, List.toSet] at hf
      cases hf with
      | inl hl =>
        have := Set.element_mapping_preserves_membership (GroundSubstitution.apply_function_free_atom trg.subs head) F (applyFact h)
        have := this (base (GroundSubstitution.apply_function_free_atom trg.subs head) (by apply Or.inl; simp [Set.element]))
        simp [Set.element, applyFactSet]
        simp [Set.element] at this
        cases this with | intro e he =>
          exists e
          rw [hl]
          constructor
          exact he.left
          rw [← he.right]
          simp [applyFact, GroundSubstitution.apply_function_free_atom]
          induction head.terms with
          | nil => simp [List.map]
          | cons t_head t_tail t_ih =>
            simp [List.map]
            constructor
            . cases t_head with
              | var v => simp [GroundSubstitution.apply_var_or_const]
              | const c => simp [GroundSubstitution.apply_var_or_const]; apply hh (GroundTerm.const c)
            . apply t_ih
      | inr hr =>
        apply ih
        intro _ hf'; apply base; apply Or.inr; apply hf'
        exact hr

  def equiv (trg1 trg2 : PreTrigger) : Prop := trg1.rule = trg2.rule ∧ ∀ v, v ∈ trg1.rule.frontier.toSet -> trg1.subs v = trg2.subs v

  theorem result_eq_of_equiv (trg1 trg2 : PreTrigger) : trg1.equiv trg2 -> trg1.result = trg2.result := by
    unfold equiv
    intro h

    have : trg1.mapped_head = trg2.mapped_head := by
      unfold mapped_head
      rw [h.left]
      rw [List.map_eq_map_iff]
      intro _ _
      unfold PreTrigger.apply_to_function_free_atom
      simp
      intro a _ voc hvoc
      cases voc with
      | const c => simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize]
      | var v =>
        cases Decidable.em (v ∈ trg1.rule.frontier) with
        | inl v_in_frontier =>
          simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term]
          rw [← h.left]
          simp [VarOrConst.skolemize, v_in_frontier]
          apply h.right
          apply List.listElementAlsoToSetElement
          apply v_in_frontier
        | inr v_not_in_frontier =>
          simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term]
          rw [← h.left]
          simp [VarOrConst.skolemize, v_not_in_frontier]
          apply congrArg
          rw [← FiniteTreeList.eqIffFromListEq]
          apply List.map_eq_map_if_functions_eq
          intro w hw
          rw [← h.right w]
          exact hw

    unfold result
    rw [this]
end PreTrigger

structure ObsoletenessCondition where
  cond : PreTrigger -> FactSet -> Prop
  monotone : ∀ trg (A B : FactSet), A ⊆ B -> cond trg A -> cond trg B
  cond_implies_trg_is_satisfied : cond trg F ->
    ∃ (s : GroundSubstitution) (i : Fin trg.rule.head.length),
      (∀ v, v ∈ (Rule.frontier trg.rule) → s v = trg.subs v) ∧
      ((s.apply_function_free_conj (trg.rule.head.get i)).toSet ⊆ F)
  contains_trg_result_implies_cond : ∀ {trg : PreTrigger} {F} (disj_index : Fin trg.result.length), (trg.result.get disj_index) ⊆ F -> cond trg F

structure Trigger (obsolete : ObsoletenessCondition) extends PreTrigger

instance : CoeOut (Trigger obs) PreTrigger where
  coe trigger := { rule := trigger.rule, subs := trigger.subs }

namespace Trigger
  def active (trg : Trigger obs) (F : FactSet) : Prop :=
    trg.loaded F ∧ ¬ (obs.cond trg F)
end Trigger

def SkolemObsoleteness : ObsoletenessCondition := {
  cond := fun (trg : PreTrigger) (F : FactSet) => ∃ i : Fin trg.mapped_head.length, (trg.mapped_head.get i).toSet ⊆ F
  monotone := by
    intro trg A B A_sub_B
    simp
    intro i head_sub_A
    exists i
    apply Set.subsetTransitive
    constructor
    . apply head_sub_A
    . apply A_sub_B
  cond_implies_trg_is_satisfied := by
    intro trg F
    simp
    intro i h
    exists (fun v => trg.apply_to_var_or_const i (VarOrConst.var v))
    constructor
    . intro v v_in_frontier
      simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, GroundSubstitution.apply_skolem_term, PreTrigger.skolemize_var_or_const, VarOrConst.skolemize, v_in_frontier]
    . exists ⟨i, by rw [PreTrigger.head_length_eq_mapped_head_length]; exact i.isLt⟩
      have : trg.mapped_head[i.val] = (trg.rule.head[i]'(by rw [PreTrigger.head_length_eq_mapped_head_length]; exact i.isLt)).map (fun a => { predicate := a.predicate, terms := a.terms.map (trg.apply_to_var_or_const i)}) := by
        unfold PreTrigger.mapped_head
        unfold PreTrigger.apply_to_function_free_atom
        simp
        rfl
      rw [this] at h

      unfold GroundSubstitution.apply_function_free_conj
      unfold GroundSubstitution.apply_function_free_atom

      have : GroundSubstitution.apply_var_or_const (fun v => trg.apply_to_var_or_const i (VarOrConst.var v)) = trg.apply_to_var_or_const i := by
        unfold GroundSubstitution.apply_var_or_const
        apply funext
        intro x
        cases x with
        | var => rfl
        | const => simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, GroundSubstitution.apply_skolem_term, PreTrigger.skolemize_var_or_const, VarOrConst.skolemize]
      rw [this]

      apply h
  contains_trg_result_implies_cond := by
    intro trg F i result_in_F
    unfold PreTrigger.result at result_in_F
    simp at result_in_F
    exists ⟨i, by have isLt := i.isLt; unfold PreTrigger.result at isLt; simp [List.length_map] at isLt; exact isLt⟩
}

def SkolemTrigger := Trigger SkolemObsoleteness

def RestrictedObsoleteness : ObsoletenessCondition := {
  cond := fun (trg : PreTrigger) (F : FactSet) =>
    ∃ (s : GroundSubstitution) (i : Fin trg.rule.head.length),
      (∀ v, v ∈ (Rule.frontier trg.rule) → s v = trg.subs v) ∧
      ((s.apply_function_free_conj (trg.rule.head.get i)).toSet ⊆ F)
  monotone := by
    intro trg A B A_sub_B
    simp
    intro subs frontier_same_under_subs i applied_head_sub_A
    exists subs
    constructor
    . apply frontier_same_under_subs
    . exists i
      apply Set.subsetTransitive
      constructor
      . apply applied_head_sub_A
      . apply A_sub_B
  cond_implies_trg_is_satisfied := by intro _ _ h; exact h
  contains_trg_result_implies_cond := by
    intro trg F i result_in_F
    let adjusted_i : Fin trg.rule.head.length := ⟨i, by rw [PreTrigger.head_length_eq_mapped_head_length]; have isLt := i.isLt; unfold PreTrigger.result at isLt; simp [List.length_map] at isLt; exact isLt⟩
    let obs_subs := fun v : Variable => trg.apply_to_var_or_const adjusted_i (VarOrConst.var v)

    exists obs_subs
    exists adjusted_i
    constructor
    . intro _ v'_in_frontier
      simp [obs_subs, PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, v'_in_frontier]
    . simp [obs_subs, SubsTarget.apply, GroundSubstitution.apply_function_free_conj]
      unfold GroundSubstitution.apply_function_free_atom
      intro f' hf'
      apply result_in_F
      unfold PreTrigger.result
      unfold PreTrigger.mapped_head
      unfold PreTrigger.apply_to_function_free_atom

      have : ∀ a : FunctionFreeAtom, (List.map (GroundSubstitution.apply_var_or_const obs_subs) a.terms) = (List.map (trg.apply_to_var_or_const adjusted_i) a.terms) := by
        intro a
        induction a.terms with
        | nil => simp [List.map]
        | cons head tail ih =>
          simp [List.map, ih]
          simp [obs_subs, SubsTarget.apply, GroundSubstitution.apply_skolem_term, GroundSubstitution.apply_var_or_const, PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const]
          cases head with
          | var v => simp
          | const c => simp [VarOrConst.skolemize]

      simp
      simp only [adjusted_i] at this
      simp [← this]
      apply hf'
}

def RestrictedTrigger := Trigger RestrictedObsoleteness

namespace FactSet
  variable (obs : ObsoletenessCondition)
  def modelsDb (fs : FactSet) (db : Database) : Prop :=
    db.toFactSet ⊆ fs

  def modelsRule (fs : FactSet) (rule : Rule) : Prop :=
    ∀ (trg : Trigger obs),
      (trg.rule = rule ∧ trg.loaded fs)
      -> obs.cond trg fs

  def modelsRules (fs : FactSet) (rules : RuleSet) : Prop :=
    ∀ r, r ∈ rules.rules -> fs.modelsRule obs r

  def modelsKb (fs : FactSet) (kb : KnowledgeBase) : Prop :=
    fs.modelsDb kb.db ∧ fs.modelsRules obs kb.rules

  def universallyModelsKb (fs : FactSet) (kb : KnowledgeBase) : Prop :=
    fs.modelsKb obs kb ∧
    (∀ m : FactSet, m.modelsKb obs kb -> ∃ (h : GroundTermMapping), isHomomorphism h fs m)
end FactSet

def RTrigger (obs : ObsoletenessCondition)(r : RuleSet) := { trg : Trigger obs // trg.rule ∈ r.rules}

namespace RTrigger
  def equiv (trg1 trg2 : RTrigger obs rs) : Prop := trg1.val.equiv trg2.val

  theorem funcTermForExisVarInMultipleTriggersMeansTheyAreTheSame
    {rs : RuleSet}
    (trg1 trg2 : RTrigger obs rs)
    (disjIndex1 : Fin trg1.val.rule.head.length)
    (disjIndex2 : Fin trg2.val.rule.head.length)
    (var1 var2 : Variable)
    (var1_not_in_frontier : ¬ var1 ∈ trg1.val.rule.frontier)
    (var2_not_in_frontier : ¬ var2 ∈ trg2.val.rule.frontier)
    :
    (trg1.val.apply_to_var_or_const disjIndex1 (VarOrConst.var var1)) = (trg2.val.apply_to_var_or_const disjIndex2 (VarOrConst.var var2))
    ->
    trg1.equiv trg2 ∧ disjIndex1.val = disjIndex2.val := by
    intro applications_eq
    simp [PreTrigger.apply_to_var_or_const, PreTrigger.apply_to_skolemized_term, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, var1_not_in_frontier, var2_not_in_frontier] at applications_eq
    injection applications_eq with rule_ids_and_vars_eq arguments_eq
    simp at rule_ids_and_vars_eq
    have rules_eq : trg1.val.rule = trg2.val.rule := by
      apply rs.id_unique
      constructor
      exact trg1.property
      constructor
      exact trg2.property
      exact rule_ids_and_vars_eq.left
    constructor
    . unfold equiv
      unfold PreTrigger.equiv
      constructor
      . exact rules_eq
      . let right := arguments_eq
        rw [← FiniteTreeList.eqIffFromListEq _ _] at right
        have : trg1.val.rule.frontier = trg2.val.rule.frontier := by rw [rules_eq]
        rw [← this] at right
        rw [List.map_eq_map_iff] at right
        intro v
        rw [← List.inIffInToSet]
        apply right
    . exact rule_ids_and_vars_eq.right.left
end RTrigger

