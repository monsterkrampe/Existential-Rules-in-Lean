/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import BasicLeanDatastructures.List.Basic
public import ExistentialRules.AtomsAndRules.Rule

/-!
# Skolem Terms

If you are familiar with existential rules, you may have expected (labelled) nulls to be part of the `Signature`.
These nulls would act as placeholders that are introduced during the chase to find fresh representatives for existentially quantified variables.
However, implementing this freshness is not really nice to model since it would require is to keep global state around to know
which nulls have already been used. Instead, we act as if the existentially quantified variables where Skolemized. By that, freshly
introduced terms simply become Skolem terms and we can show that these are indeed fresh by design. Some works on existential rules take this view,
first and foremost of course the ones considering the Skolem chase [SkolemChase].
-/

public section

/--  As a building block for Skolem terms, we introduce `SkolemFS` as a Skolem Function Symbol here. This structure captures the rule, disjunct, and (existential) variable for that the Skolem function was introduced. -/
structure SkolemFS (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
  rule : Rule sig
  headIdx : Nat
  headIdx_lt : headIdx < rule.head.length
  v : sig.V
  v_mem : v ∈ rule.existential_vars_for_head_disjunct headIdx headIdx_lt
deriving DecidableEq

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- The arity corresponds to the size of the frontier of the rule, i.e. the universal variables that occur in both body and head. -/
@[expose]
def SkolemFS.arity (sfs : SkolemFS sig) : Nat := sfs.rule.frontier.length

/-- The Skolem function symbols of a rule are all `SkolemFS` with the rule id, all possible head indices and the respective existential variables. -/
@[expose]
def Rule.skolem_functions (r : Rule sig) : List (SkolemFS sig) := r.head.zipIdx.attach.flatMap (fun pair =>
  (pair.val.fst.vars.filter (fun v => v ∉ r.frontier)).attach.map (fun v => {
    rule := r,
    headIdx := pair.val.snd,
    headIdx_lt := List.snd_lt_of_mem_zipIdx pair.property,
    v := v.val
    v_mem := by
      unfold Rule.existential_vars_for_head_disjunct
      have eq := List.fst_eq_of_mem_zipIdx pair.property; simp only [Nat.sub_zero] at eq
      have mem := v.property; rw [List.mem_filter] at mem
      rw [List.mem_filter, ← eq]
      exact mem
  })
)

/-- With `SkolemTerm` we mean the Skolemized version of an existential variable. That is, a `SkolemTerm` only consists of a function symbol (`SkolemFS`) and a list of universal variables. Beyond that, we allow this inductive structure also to be a plain variable or constant. Thereby, the `SkolemTerm` can represent any term occurring in a Skolemized rule. -/
inductive SkolemTerm (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
| var (v : sig.V) : SkolemTerm sig
| const (c : sig.C) : SkolemTerm sig
| func (fs : SkolemFS sig) (frontier : List sig.V) (arity_ok : frontier.length = fs.arity) : SkolemTerm sig
deriving DecidableEq

namespace SkolemTerm

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- We may obtain all variables from a `SkolemTerm` term as the list of all variables occurring in the functional term or, if the term is a plain variable, simply as the singleton list with this one variable. -/
def variables : SkolemTerm sig -> List sig.V
| .var v => List.cons v List.nil
| .const _ => List.nil
| .func _ vs _ => vs

end SkolemTerm


namespace VarOrConst

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- In the context of a rule and a disjunct (in that rule), we can turn a `VarOrConst` into a `SkolemTerm` using the frontier of the rule. This function is used for skolemizing existential variables in rules. -/
@[expose]
def skolemize (rule : Rule sig) (i : Nat) (lt : i < rule.head.length) : VarOrConst sig -> SkolemTerm sig
| .const c => SkolemTerm.const c
| .var v =>
  if mem : v ∈ rule.existential_vars_for_head_disjunct i lt
  then .func { rule, headIdx := i, headIdx_lt := lt, v, v_mem := mem } rule.frontier rfl
  else .var v

/-- The `skolemize` function is injective. That is, if the produced `SkolemTerm`s are the same, then they need to result from the same variable. This is important to ensure that introduced Skolem terms are indeed fresh (and unique) in the chase. -/
@[grind ->]
theorem skolemize_injective  (rule : Rule sig) (i : Nat) (lt : i < rule.head.length) (s t : VarOrConst sig) :
    s.skolemize rule i lt = t.skolemize rule i lt -> s = t := by
  fun_cases s.skolemize rule i lt <;> fun_cases t.skolemize rule i lt <;> simp

end VarOrConst

