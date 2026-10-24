import AnthillModKbSpec.MillerCertificates

namespace AnthillModKbSpec.Archive.UnaryMatcher

open MillerCertificates

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Symbol]

def matchUnary? (hoApplySymbol : Symbol) (rigids : List Variable)
    (head query : Term Variable Literal Symbol) : Option (UnaryMatch hoApplySymbol rigids head query) :=
  match head, query with
  | .app h [.var p, .var x], .app f [.var a] =>
      if valid : h = hoApplySymbol ∧ p ≠ x ∧ p ∉ rigids ∧ x ∉ rigids ∧ a ∈ rigids ∧ f ≠ hoApplySymbol then
        some ⟨p, x, a, f, by simp only [Term.hoApply, valid.1], rfl,
          valid.2.1, valid.2.2.1, valid.2.2.2.1, valid.2.2.2.2.1, valid.2.2.2.2.2⟩
      else none
  | _, _ => none

/-- Compute both the head match and its capture-safe scoped body instance. -/
def expandUnary? (ha : Symbol) (rigids : List Variable) (head : Term Variable Literal Symbol)
    (body : List (Term Variable Literal Symbol)) (query : Term Variable Literal Symbol) :
    Option (Expansion ha rigids head body query) :=
  match matchUnary? ha rigids head query with
  | none => none
  | some matched =>
      match computed : (Term.conjunction body).instantiate? matched.substitution with
      | none => none
      | some result => some ⟨matched, result, computed⟩

end AnthillModKbSpec.Archive.UnaryMatcher
