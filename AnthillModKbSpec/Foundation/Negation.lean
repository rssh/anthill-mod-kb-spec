import AnthillModKbSpec.Foundation.Semantics

namespace AnthillModKbSpec.Semantics

variable {Literal Symbol Value : Type} {hoApplySymbol : Symbol}
variable (model : Model Literal Symbol Value hoApplySymbol)

/-- The closed-world choice used here: default negation is true exactly when
its operand is false. This is stronger than Model's coherence law. -/
def Model.ComplementNAF : Prop :=
  ∀ value, model.holds (model.defaultNegation value) ↔ ¬ model.holds value

end AnthillModKbSpec.Semantics
