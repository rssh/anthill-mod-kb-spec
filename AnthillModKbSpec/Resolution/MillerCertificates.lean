import AnthillModKbSpec.Resolution.Miller
import AnthillModKbSpec.Foundation.ClauseInstantiation
import AnthillModKbSpec.Foundation.Derivation

namespace AnthillModKbSpec.MillerCertificates

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Symbol]

/-- A supported Miller-pattern match: ho_apply(P,x) against f(a), where a is
a rigid parameter and P,x are distinct, standardized-apart clause variables.
This symbol-valued unary fragment needs no lambda syntax. It is not a complete
Miller unifier; unsupported patterns return none without certifying failure. -/
structure UnaryMatch (hoApplySymbol : Symbol) (rigids : List Variable)
    (head query : Term Variable Literal Symbol) where
  predicateName : Variable
  argumentName : Variable
  rigidName : Variable
  symbol : Symbol
  head_eq : head = .hoApply hoApplySymbol (.var predicateName) [.var argumentName]
  query_eq : query = .app symbol [.var rigidName]
  distinct : predicateName ≠ argumentName
  predicateFresh : predicateName ∉ rigids
  argumentFresh : argumentName ∉ rigids
  rigid : rigidName ∈ rigids
  ordinary : symbol ≠ hoApplySymbol

def UnaryMatch.substitution {ha : Symbol} {rigids : List Variable} {head query : Term Variable Literal Symbol}
    (matched : UnaryMatch ha rigids head query) : Substitution Variable Literal Symbol := fun name =>
  if name = matched.predicateName then .app matched.symbol []
  else if name = matched.argumentName then .var matched.rigidName else .var name

omit [DecidableEq Symbol] in
theorem UnaryMatch.rigids_fixed {ha : Symbol} {rigids : List Variable} {head query : Term Variable Literal Symbol}
    (matched : UnaryMatch ha rigids head query) (member : name ∈ rigids) : matched.substitution name = .var name := by
  have notP : name ≠ matched.predicateName := fun same => matched.predicateFresh (same ▸ member)
  have notX : name ≠ matched.argumentName := fun same => matched.argumentFresh (same ▸ member)
  simp [UnaryMatch.substitution, notP, notX]

omit [DecidableEq Symbol] in
theorem UnaryMatch.head_substitutes {ha : Symbol} {rigids : List Variable} {head query : Term Variable Literal Symbol}
    (matched : UnaryMatch ha rigids head query) :
    Substitutes matched.substitution head (.hoApply ha (.app matched.symbol []) [.var matched.rigidName]) := by
  simp only [matched.head_eq]
  apply Substitutes.app
  apply SubstitutesList.cons
  · simpa [UnaryMatch.substitution] using (Substitutes.var (σ := matched.substitution) (name := matched.predicateName))
  · apply SubstitutesList.cons
    · simpa [UnaryMatch.substitution, matched.distinct.symm] using
        (Substitutes.var (σ := matched.substitution) (name := matched.argumentName))
    · exact .nil

/-- These checks are the existing Miller restrictions, now consequences of an
accepted match rather than optional assertions unrelated to resolution. -/
theorem UnaryMatch.miller_pattern {ha : Symbol} {rigids : List Variable} {head query : Term Variable Literal Symbol}
    (matched : UnaryMatch ha rigids head query) : head.MillerHead ha [matched.argumentName] := by
  simp only [matched.head_eq]
  simp [Term.hoApply, Term.MillerHead, IsMillerArguments, Term.variableName?, matched.distinct]

omit [DecidableEq Variable] [DecidableEq Symbol] in
theorem UnaryMatch.miller_target {ha : Symbol} {rigids : List Variable} {head query : Term Variable Literal Symbol}
    (matched : UnaryMatch ha rigids head query) : IsMillerArguments rigids [(.var matched.rigidName : Term Variable Literal Symbol)] := by
  simp [IsMillerArguments, Term.variableName?, matched.rigid]

structure Expansion (ha : Symbol) (rigids : List Variable) (head : Term Variable Literal Symbol)
    (body : List (Term Variable Literal Symbol)) (query : Term Variable Literal Symbol) where
  matched : UnaryMatch ha rigids head query
  instantiatedBody : Term Variable Literal Symbol
  computed : (Term.conjunction body).instantiate? matched.substitution = some instantiatedBody

omit [DecidableEq Symbol] in
theorem Expansion.toDerives {ha : Symbol} {rigids : List Variable} {head query : Term Variable Literal Symbol}
    {body : List (Term Variable Literal Symbol)} (expanded : Expansion ha rigids head body query)
    {kb : LogicalKb Variable Literal Symbol} {context : ProofContext Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol}
    (member : HornClause.definite head body ∈ kb)
    (proof : Derives ha kb context expanded.instantiatedBody naf) : Derives ha kb context query naf := by
  rw [expanded.matched.query_eq]
  exact .hoApplyElim (.clause member expanded.matched.head_substitutes
    ((Term.conjunction body).instantiate?_sound expanded.computed) proof)

end AnthillModKbSpec.MillerCertificates
