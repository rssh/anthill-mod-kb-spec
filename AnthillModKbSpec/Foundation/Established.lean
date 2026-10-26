import AnthillModKbSpec.Foundation.Semantics

namespace AnthillModKbSpec.CertifiedRefutation

open Semantics

variable {Variable Literal Symbol Value : Type} [DecidableEq Variable] {hoApplySymbol : Symbol}

/-- Established truth under the original context. Clients can obtain this from
positive derivations, or from any independently proved adequate NAF provider.
It is not an assumption temporarily added while searching an implication. -/
def Established (model : Model Literal Symbol Value hoApplySymbol)
    (context : ProofContext Variable Literal Symbol) (goal : Term Variable Literal Symbol) : Prop :=
  ∀ environment, model.ContextHolds environment context → model.Satisfies environment goal

theorem Established.ofDerives (model : Model Literal Symbol Value hoApplySymbol)
    {kb : LogicalKb Variable Literal Symbol} {context : ProofContext Variable Literal Symbol}
    {goal : Term Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}
    (validKb : model.Models kb) (adequate : model.FailureAdequate kb naf)
    (proof : Derives hoApplySymbol kb context goal naf) : Established model context goal :=
  model.sound validKb adequate proof

theorem Established.ofPositive (model : Model Literal Symbol Value hoApplySymbol)
    {kb : LogicalKb Variable Literal Symbol} {context : ProofContext Variable Literal Symbol}
    {goal : Term Variable Literal Symbol} (validKb : model.Models kb)
    (proof : Derives hoApplySymbol kb context goal) : Established model context goal :=
  model.positive_sound validKb proof

end AnthillModKbSpec.CertifiedRefutation
