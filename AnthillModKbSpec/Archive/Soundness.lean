import AnthillModKbSpec.Archive.InductiveResolution
import AnthillModKbSpec.Resolution.InductiveSoundness

namespace AnthillModKbSpec.Archive.ExplicitInduction

open Semantics InductiveDomains InductiveSoundness

variable {Domain Variable Literal Symbol Value : Type} [DecidableEq Variable]
variable {hoApplySymbol : Symbol} {family : FiniteFamily Domain Symbol}
variable {kb : LogicalKb Variable Literal Symbol}

/-- Comparison experiment: resolution with explicit induction goals, constructor-case
search, and certified NAF preserves truth. InductiveProof denotes a universally
valid predicate family on the generated domains; formula goals retain their
ordinary compositional meaning. Every induction scheme is declared in the
program and exhaustively covers Sigma's constructors. -/
theorem sound [FreshNames Variable] (interpretation : Interpretation family kb Value hoApplySymbol)
    {program : InductiveResolution.Program family Variable Literal} (sameKb : program.clauses = kb)
    {context : ProofContext Variable Literal Symbol} {goal : InductionGoals.Goal Domain Variable Literal Symbol}
    (proof : InductiveResolution.Proves interpretation.model program interpretation.membershipSymbol context goal) :
    ∀ environment, interpretation.model.ContextHolds environment context →
      goal.Holds interpretation.model family environment := by
  apply proof.sound (realizes := interpretation.realizes) (negation := interpretation.negation)
  rw [sameKb]
  exact interpretation.validKb

/-- The chosen model witnesses consistency of the extended logic, including
constructor-case search, induction application to rigid values, and NAF. -/
theorem consistent [FreshNames Variable] (interpretation : Interpretation family kb Value hoApplySymbol)
    {program : InductiveResolution.Program family Variable Literal} (sameKb : program.clauses = kb) :
    ¬ InductiveResolution.Proves interpretation.model program interpretation.membershipSymbol [] (.formula .falsity) := by
  apply InductiveResolution.no_falsity (realizes := interpretation.realizes) (negation := interpretation.negation)
  rw [sameKb]
  exact interpretation.validKb

end AnthillModKbSpec.Archive.ExplicitInduction
