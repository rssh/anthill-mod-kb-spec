import AnthillModKbSpec.CompletedGround

namespace AnthillModKbSpec.Semantics

variable {Variable Literal Symbol Value : Type} [DecidableEq Variable] {hoApplySymbol : Symbol}
variable (model : Model Literal Symbol Value hoApplySymbol)

/-- Completion for one atom in one exact rigid scope. Its support consists of
local atomic assumptions or the instantiated bodies of BOTH global and local
clauses. The law is required only in environments satisfying the current local
assumptions. It is neither inherited by an extended context nor a claim that
all scopes admit one common completed model. -/
def Model.ScopedAtomCompleted (program : ScopedSearch.Program Variable Literal Symbol hoApplySymbol)
    (context : ScopedSearch.Context Variable Literal Symbol hoApplySymbol)
    (atom : Term Variable Literal Symbol) : Prop :=
  ∀ environment, model.ContextHolds environment context.assumptions →
    (model.Satisfies environment atom ↔ atom ∈ context.assumptions ∨
      ∃ body, ScopedSearch.Instance program context atom body ∧
        model.Satisfies environment (.conjunction body))

variable {model}
variable {program : ScopedSearch.Program Variable Literal Symbol hoApplySymbol}
variable {context : ScopedSearch.Context Variable Literal Symbol hoApplySymbol}
variable {atom : Term Variable Literal Symbol}

/-- Exhaustive instance coverage and semantic refutations of all bodies imply
semantic atom refutation. No arbitrary operational body failure is accepted. -/
theorem Model.scoped_atom_refuted (completed : model.ScopedAtomCompleted program context atom)
    (absent : atom ∉ context.assumptions)
    (generator : ScopedSearch.ExhaustedInstances program context atom)
    (bodiesRefuted : ∀ body ∈ generator.bodies, ∀ environment,
      model.ContextHolds environment context.assumptions →
        ¬ model.Satisfies environment (.conjunction body)) :
    ∀ environment, model.ContextHolds environment context.assumptions → ¬ model.Satisfies environment atom := by
  intro environment valid trueAtom
  rcases (completed environment valid).mp trueAtom with member | ⟨body, instanceProof, trueBody⟩
  · exact absent member
  · exact bodiesRefuted body (generator.complete body instanceProof) environment valid trueBody

/-- The positive direction can establish an atom from any applicable instance
with an established body, including a local definite clause. -/
theorem Model.scoped_atom_supported (completed : model.ScopedAtomCompleted program context atom)
    (instanceProof : ScopedSearch.Instance program context atom body)
    (bodyTrue : ∀ environment, model.ContextHolds environment context.assumptions →
      model.Satisfies environment (.conjunction body)) :
    ∀ environment, model.ContextHolds environment context.assumptions → model.Satisfies environment atom := by
  intro environment valid
  exact (completed environment valid).mpr (Or.inr ⟨body, instanceProof, bodyTrue environment valid⟩)

end AnthillModKbSpec.Semantics
