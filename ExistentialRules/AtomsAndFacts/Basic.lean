import BasicLeanDatastructures.List.Basic
import BasicLeanDatastructures.List.EraseDupsKeepRight
import BasicLeanDatastructures.Set.Basic
import BasicLeanDatastructures.Set.Finite

import ExistentialRules.Terms.Basic
import ExistentialRules.Terms.ListsOfTerms

section StructuralDefs

  structure FunctionFreeFact (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] where
    predicate : sig.P
    terms : List sig.C
    arity_ok : terms.length = sig.arity predicate
    deriving DecidableEq

  structure Fact (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
    predicate : sig.P
    terms : List (GroundTerm sig)
    arity_ok : terms.length = sig.arity predicate
    deriving DecidableEq

  structure FunctionFreeAtom (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
    predicate : sig.P
    terms : List (VarOrConst sig)
    arity_ok : terms.length = sig.arity predicate
    deriving DecidableEq

  structure Atom (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
    predicate : sig.P
    terms : List (SkolemTerm sig)
    arity_ok : terms.length = sig.arity predicate
    deriving DecidableEq

  variable (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

  abbrev FunctionFreeConjunction := List (FunctionFreeAtom sig)

  -- normally, we would only allow variables in atoms in rules... does this break later?
  structure Rule where
    id : Nat
    body : FunctionFreeConjunction sig
    head : List (FunctionFreeConjunction sig)
    deriving DecidableEq

  structure RuleSet where
    rules : Set (Rule sig)
    id_unique : ∀ r1 r2, r1 ∈ rules ∧ r2 ∈ rules ∧ r1.id = r2.id -> r1 = r2

  abbrev FactSet := Set (Fact sig)

  abbrev Database := { X : Set (FunctionFreeFact sig) // X.finite }

  structure KnowledgeBase where
    db : Database sig
    rules : RuleSet sig

end StructuralDefs


variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace FunctionFreeAtom

  def variables (a : FunctionFreeAtom sig) : List sig.V := VarOrConst.filterVars a.terms

  def constants (a : FunctionFreeAtom sig) : List sig.C := VarOrConst.filterConsts a.terms

  def skolemize (ruleId : Nat) (disjunctIndex : Nat) (frontier : List sig.V) (a : FunctionFreeAtom sig) : Atom sig := {
    predicate := a.predicate,
    terms := a.terms.map (VarOrConst.skolemize ruleId disjunctIndex frontier),
    arity_ok := by rw [List.length_map, a.arity_ok]
  }

  theorem length_skolemize {ruleId : Nat} {disjunctIndex : Nat} {frontier : List sig.V} {a : FunctionFreeAtom sig} :
      (a.skolemize ruleId disjunctIndex frontier).terms.length = a.terms.length := by
    unfold skolemize
    rw [List.length_map]

  theorem mem_skolemize_of_mem {ruleId : Nat} {disjunctIndex : Nat} {frontier : List sig.V}
      {a : FunctionFreeAtom sig} {t : VarOrConst sig} :
      t ∈ a.terms -> (t.skolemize ruleId disjunctIndex frontier) ∈ (a.skolemize ruleId disjunctIndex frontier).terms := by
    intro t_mem
    unfold skolemize
    rw [List.mem_map]
    exists t

end FunctionFreeAtom

namespace FunctionFreeConjunction

  def vars (conj : FunctionFreeConjunction sig) : List sig.V := conj.flatMap FunctionFreeAtom.variables

  def consts (conj : FunctionFreeConjunction sig) : List sig.C := conj.flatMap FunctionFreeAtom.constants

  def predicates (conj : FunctionFreeConjunction sig) : List sig.P := conj.map FunctionFreeAtom.predicate

end FunctionFreeConjunction

namespace Rule

  def frontier_for_head (r : Rule sig) (i : Fin r.head.length) : List sig.V :=
    r.body.vars.filter (fun v => v ∈ r.head[i.val].vars)

  def frontier (r : Rule sig) : List sig.V :=
    List.filter (fun v => r.head.any (fun h => v ∈ h.vars)) (FunctionFreeConjunction.vars r.body)

  theorem frontier_occurs_in_body (r : Rule sig) : ∀ v, v ∈ r.frontier -> ∃ f, f ∈ r.body ∧ (VarOrConst.var v) ∈ f.terms := by
    unfold frontier
    cases r.body with
    | nil => intros; contradiction
    | cons head tail =>
      intro v vInFrontier
      rw [List.mem_filter] at vInFrontier
      have mem_body := vInFrontier.left
      unfold FunctionFreeConjunction.vars at mem_body
      rw [List.mem_flatMap] at mem_body
      rcases mem_body with ⟨a, a_mem, v_mem⟩
      exists a
      constructor
      . exact a_mem
      . unfold FunctionFreeAtom.variables at v_mem
        apply VarOrConst.filterVars_occur_in_original_list
        exact v_mem

  def isDatalog (r : Rule sig) : Bool :=
    r.head.all (fun h => h.vars.all (fun v => v ∈ r.body.vars))

  def isDeterministic (r : Rule sig) : Bool := r.head.length = 1

  def predicates (r : Rule sig) : List sig.P := r.body.predicates ++ (r.head.flatMap FunctionFreeConjunction.predicates)

  def constants (r : Rule sig) : List sig.C := r.body.consts ++ r.head.flatMap (fun conj => conj.consts)

  def head_constants (r : Rule sig) : List sig.C := r.head.flatMap (fun conj => conj.consts)

  theorem head_constants_subset_constants (r : Rule sig) : r.head_constants ⊆ r.constants := by apply List.subset_append_right

  def skolem_functions (r : Rule sig) : List (SkolemFS sig) := r.head.zipIdx.flatMap (fun (head, i) =>
    (head.vars.filter (fun v => !(v ∈ r.frontier))).map (fun v => { ruleId := r.id, disjunctIndex := i, var := v, arity := r.frontier.length })
  )

end Rule

namespace RuleSet

  def isDeterministic (rs : RuleSet sig) : Prop := ∀ (r : Rule sig), r ∈ rs.rules -> r.isDeterministic

  def predicates (rs : RuleSet sig) : Set sig.P := fun p => ∃ r, r ∈ rs.rules ∧ p ∈ r.predicates

  theorem predicates_finite_of_finite (rs : RuleSet sig) : rs.rules.finite -> rs.predicates.finite := by
    intro finite
    rcases finite with ⟨l, nodup, eq⟩
    exists (l.flatMap Rule.predicates).eraseDupsKeepRight
    constructor
    . apply List.nodup_eraseDupsKeepRight
    . intro p
      rw [List.mem_eraseDupsKeepRight]
      unfold predicates
      simp only [List.mem_flatMap]
      constructor <;> (intro h; rcases h with ⟨r, h⟩; exists r)
      . rw [← eq]; assumption
      . rw [eq]; assumption

  def constants (rs : RuleSet sig) : Set sig.C := fun c => ∃ r, r ∈ rs.rules ∧ c ∈ r.constants

  theorem constants_finite_of_finite (rs : RuleSet sig) : rs.rules.finite -> rs.constants.finite := by
    intro finite
    rcases finite with ⟨l, nodup, eq⟩
    exists (l.flatMap Rule.constants).eraseDupsKeepRight
    constructor
    . apply List.nodup_eraseDupsKeepRight
    . intro c
      rw [List.mem_eraseDupsKeepRight]
      unfold constants
      simp only [List.mem_flatMap]
      constructor <;> (intro h; rcases h with ⟨r, h⟩; exists r)
      . rw [← eq]; assumption
      . rw [eq]; assumption

  def head_constants (rs : RuleSet sig) : Set sig.C := fun c => ∃ r, r ∈ rs.rules ∧ c ∈ r.head_constants

  theorem head_constants_finite_of_finite (rs : RuleSet sig) : rs.rules.finite -> rs.head_constants.finite := by
    intro finite
    rcases finite with ⟨l, nodup, eq⟩
    exists (l.flatMap Rule.head_constants).eraseDupsKeepRight
    constructor
    . apply List.nodup_eraseDupsKeepRight
    . intro c
      rw [List.mem_eraseDupsKeepRight]
      unfold head_constants
      simp only [List.mem_flatMap]
      constructor <;> (intro h; rcases h with ⟨r, h⟩; exists r)
      . rw [← eq]; assumption
      . rw [eq]; assumption

  theorem head_constants_subset_constants (rs : RuleSet sig) : rs.head_constants ⊆ rs.constants := by
    intro c c_mem
    rcases c_mem with ⟨r, r_mem, c_mem⟩
    exists r
    constructor
    . exact r_mem
    . apply Rule.head_constants_subset_constants; exact c_mem

  def skolem_functions (rs : RuleSet sig) : Set (SkolemFS sig) := fun f => ∃ r, r ∈ rs.rules ∧ f ∈ r.skolem_functions

  theorem skolem_functions_finite_of_finite (rs : RuleSet sig) : rs.rules.finite -> rs.skolem_functions.finite := by
    intro finite
    rcases finite with ⟨l, nodup, eq⟩
    exists (l.flatMap Rule.skolem_functions).eraseDupsKeepRight
    constructor
    . apply List.nodup_eraseDupsKeepRight
    . intro c
      rw [List.mem_eraseDupsKeepRight]
      unfold skolem_functions
      simp only [List.mem_flatMap]
      constructor <;> (intro h; rcases h with ⟨r, h⟩; exists r)
      . rw [← eq]; assumption
      . rw [eq]; assumption

end RuleSet

namespace KnowledgeBase

  def isDeterministic (kb : KnowledgeBase sig) : Prop := kb.rules.isDeterministic

end KnowledgeBase

namespace Fact

  def constants (f : Fact sig) : List sig.C := f.terms.flatMap GroundTerm.constants

  def function_symbols (f : Fact sig) : List (SkolemFS sig) := f.terms.flatMap GroundTerm.functions

  def isFunctionFree (f : Fact sig) : Prop := ∀ t, t ∈ f.terms -> ∃ c, t = GroundTerm.const c

  def toFunctionFreeFact (f : Fact sig) (isFunctionFree : f.isFunctionFree) : FunctionFreeFact sig := {
    predicate := f.predicate
    terms := f.terms.attach.map (fun t => t.val.toConst (isFunctionFree t.val t.property))
    arity_ok := by rw [List.length_map, List.length_attach, f.arity_ok]
  }

end Fact

namespace FunctionFreeFact

  def toFact (f : FunctionFreeFact sig) : Fact sig := {
    predicate := f.predicate,
    terms := f.terms.map GroundTerm.const,
    arity_ok := by rw [List.length_map, f.arity_ok]
  }

  theorem toFact_isFunctionFree (f : FunctionFreeFact sig) : f.toFact.isFunctionFree := by
    intro t t_mem
    unfold toFact at t_mem
    simp at t_mem
    rcases t_mem with ⟨c, _, t_eq⟩
    exists c
    rw [t_eq]

  theorem toFunctionFreeFact_after_toFact_is_id (f : FunctionFreeFact sig) : f.toFact.toFunctionFreeFact (f.toFact_isFunctionFree) = f := by
    unfold toFact
    unfold Fact.toFunctionFreeFact
    simp only
    rw [FunctionFreeFact.mk.injEq]
    constructor
    . simp
    . rw [List.map_attach_eq_pmap, List.pmap_map]
      simp [GroundTerm.toConst, GroundTerm.const]

end FunctionFreeFact

theorem Fact.toFact_after_toFunctionFreeFact_is_id (f : Fact sig) (isFunctionFree : f.isFunctionFree) : (f.toFunctionFreeFact isFunctionFree).toFact = f := by
  unfold toFunctionFreeFact
  unfold FunctionFreeFact.toFact
  simp
  rw [Fact.mk.injEq]
  constructor
  . simp
  . simp only [List.map_attach_eq_pmap]
    apply List.ext_get
    . simp
    intro n _ _
    simp
    specialize isFunctionFree f.terms[n] (by simp)
    rcases isFunctionFree with ⟨c, isFunctionFree⟩
    simp only [isFunctionFree]
    unfold GroundTerm.const
    unfold GroundTerm.toConst
    simp

namespace FactSet

  def predicates (fs : FactSet sig) : Set sig.P := fun p => ∃ f, f ∈ fs ∧ f.predicate = p

  def terms (fs : FactSet sig) : Set (GroundTerm sig) := fun t => ∃ f, f ∈ fs ∧ t ∈ f.terms

  def constants (fs : FactSet sig) : Set sig.C := fun c => ∃ f, f ∈ fs ∧ c ∈ f.constants

  def function_symbols (fs : FactSet sig) : Set (SkolemFS sig) := fun func => ∃ f, f ∈ fs ∧ func ∈ f.function_symbols

  def isFunctionFree (fs : FactSet sig) : Prop := ∀ f, f ∈ fs -> f.isFunctionFree

  theorem terms_finite_of_finite (fs : FactSet sig) (finite : fs.finite) : fs.terms.finite := by
    rcases finite with ⟨l, nodup, finite⟩
    exists (l.map Fact.terms).flatten.eraseDupsKeepRight
    constructor
    . apply List.nodup_eraseDupsKeepRight
    . intro e
      constructor
      . intro in_l
        unfold FactSet.terms
        simp [List.mem_eraseDupsKeepRight, List.mem_flatten] at in_l
        rcases in_l with ⟨terms, ex_f, e_in_terms⟩
        rcases ex_f with ⟨f, f_in_l, terms_eq⟩
        exists f
        constructor
        . rw [← finite]; exact f_in_l
        . rw [terms_eq]; exact e_in_terms
      . intro in_fs
        unfold FactSet.terms at in_fs
        simp [List.mem_eraseDupsKeepRight, List.mem_flatten]
        rcases in_fs with ⟨f, f_in_fs, e_in_f⟩
        exists f.terms
        constructor
        . exists f
          constructor
          . rw [finite]; exact f_in_fs
          . rfl
        . exact e_in_f

  theorem constants_finite_of_finite (fs : FactSet sig) (fin : fs.finite) : fs.constants.finite := by
    rcases fin with ⟨l, _, l_eq⟩
    exists (l.flatMap Fact.constants).eraseDupsKeepRight
    constructor
    . apply List.nodup_eraseDupsKeepRight
    . intro c
      rw [List.mem_eraseDupsKeepRight]
      rw [List.mem_flatMap]
      unfold constants
      constructor
      . intro h
        rcases h with ⟨f, f_mem, c_mem⟩
        rw [l_eq] at f_mem
        exists f
      . intro h
        rcases h with ⟨f, f_mem, c_mem⟩
        rw [← l_eq] at f_mem
        exists f

  theorem finite_of_preds_finite_of_terms_finite (fs : FactSet sig) : fs.predicates.finite -> fs.terms.finite -> fs.finite := by
    intro preds_fin terms_fin
    rcases preds_fin with ⟨preds, _, preds_eq⟩
    rcases terms_fin with ⟨terms, _, terms_eq⟩

    let overapproximation : FactSet sig := fun f => f.predicate ∈ fs.predicates ∧ (∀ t, t ∈ f.terms -> t ∈ fs.terms)
    have overapproximation_fin : overapproximation.finite := by
      exists (preds.flatMap (fun p =>
        (all_lists_of_length terms (sig.arity p)).attach.map (fun ⟨ts, mem⟩ =>
          {
            predicate := p
            terms := ts
            arity_ok := ((mem_all_lists_of_length terms (sig.arity p) ts).mp mem).left
          }
        )
      )).eraseDupsKeepRight

      constructor
      . apply List.nodup_eraseDupsKeepRight
      . intro f
        rw [List.mem_eraseDupsKeepRight]
        simp only [List.mem_flatMap, List.mem_map, List.mem_attach, true_and, Subtype.exists]
        constructor
        . intro h
          rcases h with ⟨pred, pred_mem, ts, ts_mem, f_eq⟩
          rw [← f_eq]
          constructor
          . rw [preds_eq] at pred_mem
            exact pred_mem
          . rw [mem_all_lists_of_length] at ts_mem
            intro t t_mem
            rw [← terms_eq]
            apply ts_mem.right
            exact t_mem
        . intro h
          rcases h with ⟨pred_mem, ts_mem⟩
          exists f.predicate
          constructor
          . rw [preds_eq]; exact pred_mem
          . exists f.terms
            exists (by
              rw [mem_all_lists_of_length]
              constructor
              . exact f.arity_ok
              . intro t t_mem; rw [terms_eq]; apply ts_mem; exact t_mem
            )

    apply Set.finite_of_subset_finite overapproximation_fin
    intro f f_mem
    constructor
    . exists f
    . intro t t_mem
      exists f

end FactSet

namespace Database

  def constants (db : Database sig) : { C : Set sig.C // C.finite } := ⟨
    fun c => ∃ (f : FunctionFreeFact sig), f ∈ db ∧ c ∈ f.terms,
    by
      rcases db.property with ⟨l, _, l_eq⟩
      exists (l.flatMap (fun f => f.terms)).eraseDupsKeepRight
      constructor
      . apply List.nodup_eraseDupsKeepRight
      . intro c
        rw [List.mem_eraseDupsKeepRight, List.mem_flatMap]
        constructor
        . intro h
          rcases h with ⟨f, f_mem, c_mem⟩
          exists f
          constructor
          . rw [l_eq] at f_mem
            exact f_mem
          . exact c_mem
        . intro h
          rcases h with ⟨f, f_mem, c_mem⟩
          exists f
          constructor
          . rw [← l_eq] at f_mem
            exact f_mem
          . exact c_mem
  ⟩

  def toFactSet (db : Database sig) : { fs : FactSet sig // fs.finite ∧ fs.isFunctionFree } := ⟨
    (fun f => ∃ f', f' ∈ db.val ∧ f'.toFact = f),
    (by
      rcases db.property with ⟨l, _, l_eq⟩
      exists (l.map FunctionFreeFact.toFact).eraseDupsKeepRight
      constructor
      . apply List.nodup_eraseDupsKeepRight
      . intro f
        rw [List.mem_eraseDupsKeepRight]
        rw [List.mem_map]
        simp only [l_eq]
        simp [Set.element]
    ),
    (by
      intro f f_mem
      rcases f_mem with ⟨_, _, f_eq⟩
      rw [← f_eq]
      apply FunctionFreeFact.toFact_isFunctionFree
    ),
  ⟩

  theorem toFactSet_constants_same (db : Database sig) : db.toFactSet.val.constants = db.constants.val := by
    unfold toFactSet
    unfold constants
    unfold FactSet.constants
    simp only
    apply Set.ext
    intro c
    constructor
    . intro h
      rcases h with ⟨f, f_mem, c_mem⟩
      rcases f_mem with ⟨f', f'_mem, f_eq⟩
      exists f'
      constructor
      . exact f'_mem
      . unfold Fact.constants at c_mem
        rw [List.mem_flatMap] at c_mem
        rcases c_mem with ⟨t, t_mem, c_mem⟩
        rw [← f_eq] at t_mem
        unfold FunctionFreeFact.toFact at t_mem
        rw [List.mem_map] at t_mem
        rcases t_mem with ⟨d, d_mem, t_eq⟩
        rw [← t_eq] at c_mem
        rw [GroundTerm.constants_const, List.mem_singleton] at c_mem
        rw [c_mem]
        exact d_mem
    . intro h
      rcases h with ⟨f, f_mem, c_mem⟩
      exists f.toFact
      constructor
      . exists f
      . unfold FunctionFreeFact.toFact
        unfold Fact.constants
        rw [List.mem_flatMap]
        exists GroundTerm.const c
        constructor
        . rw [List.mem_map]
          exists c
        . simp [GroundTerm.constants_const]

end Database

