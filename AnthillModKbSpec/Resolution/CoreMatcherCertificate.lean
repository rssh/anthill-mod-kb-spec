import AnthillModKbSpec.Resolution.MillerCertificates

namespace AnthillModKbSpec.CoreMatcherCertificate

open MillerCertificates

/-- Untrusted data proposed by any backend. No Lean expressions, metavariable
contexts, semantic model, or proof fields enter this interface. -/
structure UnaryCandidate (Variable Symbol : Type) where
  predicate : Symbol
  argument : Variable
  deriving Repr

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Symbol]

/-- Independently validate a backend's proposed symbol and rigid argument.
This checks the proposal rather than asking the handwritten matcher to find it.
Rejected data supplies no certificate and no evidence for NAF. -/
def checkUnary? (ha : Symbol) (rigids : List Variable) (head query : Term Variable Literal Symbol)
    (candidate : UnaryCandidate Variable Symbol) : Option (UnaryMatch ha rigids head query) :=
  match head, query with
  | .app h [.var p, .var x], .app f [.var a] =>
      if valid : h = ha ∧ p ≠ x ∧ p ∉ rigids ∧ x ∉ rigids ∧ a ∈ rigids ∧ f ≠ ha ∧
          candidate.predicate = f ∧ candidate.argument = a then
        some ⟨p, x, a, f, by simp only [Term.hoApply, valid.1], rfl,
          valid.2.1, valid.2.2.1, valid.2.2.2.1, valid.2.2.2.2.1, valid.2.2.2.2.2.1⟩
      else none
  | _, _ => none

/-- Convert accepted proposal data into the existing capture-safe expansion
certificate. Its toDerives theorem remains independent of the proposing backend. -/
def expandUnary? (ha : Symbol) (rigids : List Variable) (head : Term Variable Literal Symbol)
    (body : List (Term Variable Literal Symbol)) (query : Term Variable Literal Symbol)
    (candidate : UnaryCandidate Variable Symbol) : Option (Expansion ha rigids head body query) :=
  match checkUnary? ha rigids head query candidate with
  | none => none
  | some matched =>
      match computed : (Term.conjunction body).instantiate? matched.substitution with
      | none => none
      | some result => some ⟨matched, result, computed⟩

end AnthillModKbSpec.CoreMatcherCertificate
