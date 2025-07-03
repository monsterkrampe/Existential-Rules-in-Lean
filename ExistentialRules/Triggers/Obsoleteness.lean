import ExistentialRules.Triggers.Basic

structure LaxObsoletenessCondition (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
  cond : PreTrigger sig -> FactSet sig -> Prop
  monotone : ∀ trg (A B : FactSet sig), A ⊆ B -> cond trg A -> cond trg B

structure ObsoletenessCondition (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] extends LaxObsoletenessCondition sig where
  cond_implies_trg_is_satisfied : cond trg fs -> trg.satisfied fs
  contains_trg_result_implies_cond : ∀ {trg : PreTrigger sig} {fs} (disj_index : Fin trg.mapped_head.length),
    ((trg.mapped_head[disj_index.val]).toSet ⊆ fs) -> cond trg fs
  preserved_under_equiv : ∀ {trg trg2 : PreTrigger sig} {fs}, trg.equiv trg2 -> (cond trg fs ↔ cond trg2 fs)

instance {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] :
    Coe (ObsoletenessCondition sig) (LaxObsoletenessCondition sig) where
  coe obs := { cond := obs.cond, monotone := obs.monotone }

def SkolemObsoleteness (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] : ObsoletenessCondition sig := {
  cond := fun (trg : PreTrigger sig) (fs : FactSet sig) => ∃ i : Fin trg.mapped_head.length, (trg.mapped_head[i.val]).toSet ⊆ fs
  monotone := by
    intro trg A B A_sub_B
    simp
    intro i head_sub_A
    exists i
    apply Set.subset_trans
    . exact head_sub_A
    . exact A_sub_B
  cond_implies_trg_is_satisfied := by
    intro trg fs h
    rcases h with ⟨i, h⟩
    exists ⟨i, by rw [← PreTrigger.length_mapped_head]; exact i.isLt⟩
    apply trg.satisfied_for_disj_of_mapped_head_contained
    exact h
  contains_trg_result_implies_cond := by
    intro trg F i result_in_F
    exists i
  preserved_under_equiv := by
    intro trg trg2 fs equiv
    rw [PreTrigger.result_eq_of_equiv trg trg2 equiv]
}

def RestrictedObsoleteness (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] : ObsoletenessCondition sig := {
  cond := fun (trg : PreTrigger sig) (fs : FactSet sig) => trg.satisfied fs
  monotone := by
    intro trg A B A_sub_B
    simp [PreTrigger.satisfied, PreTrigger.satisfied_for_disj]
    intro i subs frontier_same_under_subs applied_head_sub_A
    exists i
    exists subs
    constructor
    . apply frontier_same_under_subs
    . apply Set.subset_trans
      . exact applied_head_sub_A
      . exact A_sub_B
  cond_implies_trg_is_satisfied := by intro _ _ h; exact h
  contains_trg_result_implies_cond := by
    intro trg fs i result_in_fs
    exists ⟨i.val, by rw [← PreTrigger.length_mapped_head]; exact i.isLt⟩
    apply trg.satisfied_for_disj_of_mapped_head_contained
    exact result_in_fs
  preserved_under_equiv := by
    intro trg trg2 fs equiv
    apply PreTrigger.satisfied_preserved_of_equiv
    exact equiv
}

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

structure Trigger (obsolete : LaxObsoletenessCondition sig) extends PreTrigger sig

def SkolemTrigger := Trigger (SkolemObsoleteness sig : LaxObsoletenessCondition sig)
def RestrictedTrigger := Trigger (RestrictedObsoleteness sig : LaxObsoletenessCondition sig)

variable {obs : LaxObsoletenessCondition sig}

instance : CoeOut (Trigger obs) (PreTrigger sig) where
  coe trigger := { rule := trigger.rule, subs := trigger.subs }

namespace Trigger
  def active (trg : Trigger obs) (F : FactSet sig) : Prop :=
    trg.loaded F ∧ ¬ (obs.cond trg F)
end Trigger

