import ExistentialRules.AtomsAndFacts.Basic
import ExistentialRules.AtomsAndFacts.SubstitutionsAndHomomorphisms

/--An `AtomPos` consists of a `GeneralizedAtom` and a natural Number i that refers to term at Position i in that Atom (if this position actually exists)-/
structure AtomPos (sig : Signature) (T : Type u) [DecidableEq sig.P] where
  a: GeneralizedAtom sig T
  i: Nat

namespace AtomPos

  variable {sig : Signature} [DecidableEq sig.P]

  /--Returns the term at the position referred by `AtomPos`-/
  def getTerm (pos: AtomPos sig T) (valid: pos.i < pos.a.terms.length) : T := pos.a.terms[pos.i]

  /--Returns the term at the position referred by `AtomPos` if that position actually exists. Otherwise returns `none`-/
  def getTerm? (pos: AtomPos sig T) : Option (T) := pos.a.terms[pos.i]?

  /--i is a valid index for a `GeneralizedAtom` a if it refers to an actual term of the atom a-/
  def idx_valid (a: GeneralizedAtom sig T)(i: Nat) : Bool :=
    if i < a.terms.length then true else false

  /--`getTerm?` of an `AtomPos` pos returns `Option.some` value iff the positions' index i is valid for the atom a -/
  theorem some_iff_idx_valid (pos: AtomPos sig T) :
      pos.getTerm?.isSome ↔ idx_valid pos.a pos.i := by
    unfold getTerm? idx_valid
    simp

  /--The existence of a real term behid an `AtomPos` is invariant to any `TermMapping`-/
  theorem some_iff_map_some (pos: AtomPos sig T) (h: TermMapping T S):
      let mapped_pos: AtomPos sig S := {a:= TermMapping.apply_generalized_atom h pos.a, i:= pos.i}
      pos.getTerm?.isSome ↔ mapped_pos.getTerm?.isSome := by
    unfold getTerm?
    simp only [isSome_getElem?]
    rw[TermMapping.length_terms_apply_generalized_atom]

  /--It doesn't matter if we first get the Term from a `AtomPos` and then apply a `TermMapping` or if we first apply the TermMapping on the whole atom and the retrieve the Term-/
  theorem getTerm_map_eq (pos: AtomPos sig T)(h: TermMapping T S):
      (posSome: pos.i < pos.a.terms.length) -> h (pos.getTerm posSome)
      = {pos with a:=(h.apply_generalized_atom pos.a)}.getTerm (by rw[TermMapping.length_terms_apply_generalized_atom]; exact posSome):= by
    intro posSome
    unfold TermMapping.apply_generalized_atom getTerm
    simp

  /--It doesn't matter if we first get the Term from a `AtomPos` and then apply a `TermMapping` or if we first apply the TermMapping on the whole atom and the retrieve the Term-/
  theorem getTerm?_map_eq (pos: AtomPos sig T)(h: TermMapping T S):
      (posSome: pos.getTerm?.isSome) -> h (pos.getTerm?.get posSome)
      = {pos with a:=(h.apply_generalized_atom pos.a)}.getTerm?.get (by simp[← some_iff_map_some]; exact posSome):= by
    intro posSome
    unfold TermMapping.apply_generalized_atom getTerm?
    simp

end AtomPos
