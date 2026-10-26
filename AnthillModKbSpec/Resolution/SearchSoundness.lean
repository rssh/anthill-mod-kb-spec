import AnthillModKbSpec.Foundation.Semantics
import AnthillModKbSpec.Resolution.ScopedSearch

namespace AnthillModKbSpec.Semantics

variable {Variable Literal Symbol Value : Type} [DecidableEq Variable] {hoApplySymbol : Symbol}
variable (model : Model Literal Symbol Value hoApplySymbol)

/-- Search soundness follows through the independently proved derivation
bridges. Adequacy of each concrete failure provider remains a separate task. -/
theorem Model.ground_success_sound {program : GroundSearch.Program Variable Literal Symbol hoApplySymbol}
    {context : GroundSearch.Context Variable Literal Symbol hoApplySymbol} {goal : Term Variable Literal Symbol}
    (validKb : model.Models program.toKb)
    (adequate : model.FailureAdequate program.toKb (GroundSearch.failureEvidence program context))
    (proof : GroundSearch.Succeeds program context goal) :
    ∀ environment, model.ContextHolds environment context.assumptions → model.Satisfies environment goal :=
  model.sound validKb adequate (GroundSearch.succeeds_toDerives proof)

theorem Model.variable_success_sound {program : VariableSearch.Program Variable Literal Symbol hoApplySymbol}
    {context : GroundSearch.Context Variable Literal Symbol hoApplySymbol} {goal : Term Variable Literal Symbol}
    (validKb : model.Models program.toKb)
    (adequate : model.FailureAdequate program.toKb (VariableSearch.failureEvidence program context))
    (proof : VariableSearch.Succeeds program context goal) :
    ∀ environment, model.ContextHolds environment context.assumptions → model.Satisfies environment goal :=
  model.sound validKb adequate (VariableSearch.succeeds_toDerives proof)

/-- Each reported answer denotes a true capture-avoiding query instance. -/
theorem Model.variable_answers_sound {program : VariableSearch.Program Variable Literal Symbol hoApplySymbol}
    {context : VariableSearch.Context Variable Literal Symbol hoApplySymbol}
    {query : Term Variable Literal Symbol} {σ : Substitution Variable Literal Symbol}
    (validKb : model.Models program.toKb)
    (adequate : model.FailureAdequate program.toKb (VariableSearch.failureEvidence program context))
    (answer : VariableSearch.Answers program context query σ) :
    ∃ instantiated, Substitutes σ query instantiated ∧
      ∀ environment, model.ContextHolds environment context.assumptions → model.Satisfies environment instantiated := by
  obtain ⟨instantiated, substitution, proof⟩ := VariableSearch.answers_toDerives answer
  exact ⟨instantiated, substitution, model.sound validKb adequate proof⟩

variable [FreshNames Variable]

theorem Model.scoped_success_sound {program : ScopedSearch.Program Variable Literal Symbol hoApplySymbol}
    {context : ScopedSearch.Context Variable Literal Symbol hoApplySymbol} {goal : Term Variable Literal Symbol}
    (validKb : model.Models program.toKb)
    (adequate : model.FailureAdequate program.toKb (ScopedSearch.failureEvidence program))
    (proof : ScopedSearch.Succeeds program context goal) :
    ∀ environment, model.ContextHolds environment context.assumptions → model.Satisfies environment goal :=
  model.sound validKb adequate (ScopedSearch.succeeds_toDerives proof)

theorem Model.scoped_answers_sound {program : ScopedSearch.Program Variable Literal Symbol hoApplySymbol}
    {context : ScopedSearch.Context Variable Literal Symbol hoApplySymbol}
    {query : Term Variable Literal Symbol} {σ : Substitution Variable Literal Symbol}
    (validKb : model.Models program.toKb)
    (adequate : model.FailureAdequate program.toKb (ScopedSearch.failureEvidence program))
    (answer : ScopedSearch.Answers program context query σ) :
    ∃ instantiated, Substitutes σ query instantiated ∧
      ∀ environment, model.ContextHolds environment context.assumptions → model.Satisfies environment instantiated := by
  obtain ⟨instantiated, substitution, proof⟩ := ScopedSearch.answers_toDerives answer
  exact ⟨instantiated, substitution, model.sound validKb adequate proof⟩

end AnthillModKbSpec.Semantics
