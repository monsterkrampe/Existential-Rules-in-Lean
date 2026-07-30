/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.Terms.Basic

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

/--  As a building block for Skolem terms, we introduce `SkolemFS` as a Skolem Function Symbol here. This structure captures the rule, disjunct, and (existential) variable for that the Skolem function was introduced. The arity corresponds to the size of the frontier of the rule, i.e. the universal variables that occur in both body and head. -/
structure SkolemFS (sig : Signature) [DecidableEq sig.V] where
  ruleId : Nat
  disjunctIndex : Nat
  var : sig.V
  arity : Nat
  deriving DecidableEq

/-- With `SkolemTerm` we mean the Skolemized version of an existential variable. That is, a `SkolemTerm` only consists of a function symbol (`SkolemFS`) and a list of universal variables. Beyond that, we allow this inductive structure also to be a plain variable or constant. Thereby, the `SkolemTerm` can represent any term occurring in a Skolemized rule. -/
inductive SkolemTerm (sig : Signature) [DecidableEq sig.C] [DecidableEq sig.V] where
| var (v : sig.V) : SkolemTerm sig
| const (c : sig.C) : SkolemTerm sig
| func (fs : SkolemFS sig) (frontier : List sig.V) (arity_ok : frontier.length = fs.arity) : SkolemTerm sig
deriving DecidableEq

namespace SkolemTerm

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

/-- We may obtain all variables from a `SkolemTerm` term as the list of all variables occurring in the functional term or, if the term is a plain variable, simply as the singleton list with this one variable. -/
def variables : SkolemTerm sig -> List sig.V
| .var v => List.cons v List.nil
| .const _ => List.nil
| .func _ vs _ => vs

end SkolemTerm


namespace VarOrConst

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

/-- In the context of a rule and a disjunct (in that rule), we can turn a `VarOrConst` into a `SkolemTerm` using the frontier of the rule. This function is used for skolemizing existential variables in rules. -/
@[expose]
def skolemize (ruleId : Nat) (disjunctIndex : Nat) (frontier : List sig.V) : VarOrConst sig -> SkolemTerm sig
| .var v =>
  if (v ∈ frontier)
  then .var v
  else .func { ruleId, disjunctIndex, var := v, arity := frontier.length } frontier rfl
| .const c => SkolemTerm.const c

/-- The `skolemize` function is injective. That is, if the produced `SkolemTerm`s are the same, then bey need to result from the same variable. This is important to ensure that introduced Skolem terms are indeed fresh (and unique) in the chase. -/
@[grind ->]
theorem skolemize_injective (ruleId : Nat) (i : Nat) (frontier : List sig.V) (s t : VarOrConst sig) :
    s.skolemize ruleId i frontier = t.skolemize ruleId i frontier -> s = t := by
  fun_cases s.skolemize ruleId i frontier <;> fun_cases t.skolemize ruleId i frontier <;> simp

end VarOrConst

