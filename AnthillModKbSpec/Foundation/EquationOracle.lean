import AnthillModKbSpec.Foundation.Semantics
import AnthillModKbSpec.Foundation.Opening

namespace AnthillModKbSpec.Semantics

/-- A positive oracle for conditional equations. Every accepted claim must be
valid under every environment satisfying its body. No completeness, decision
procedure, or interpretation of unanswered queries as negation is required. -/
structure EquationOracle {Literal Symbol Value : Type} {hoApplySymbol : Symbol}
    (model : Model Literal Symbol Value hoApplySymbol) (Variable : Type) [DecidableEq Variable] where
  certifies : List (Term Variable Literal Symbol) →
    Term Variable Literal Symbol → Term Variable Literal Symbol → Prop
  sound : ∀ {body left right}, certifies body left right →
    ∀ environment, model.Satisfies environment (.conjunction body) →
      model.eval environment left = model.eval environment right

variable {Variable Literal Symbol Value : Type} [DecidableEq Variable] {hoApplySymbol : Symbol}
  {model : Model Literal Symbol Value hoApplySymbol}

namespace EquationOracle

/-- Original clauses and oracle-certified equation clauses inhabit one KB set. -/
def extend (oracle : EquationOracle model Variable) (kb : LogicalKb Variable Literal Symbol) :
    LogicalKb Variable Literal Symbol := fun clause =>
  clause ∈ kb ∨ ∃ left right body,
    oracle.certifies body left right ∧ clause = HornClause.equation left right body

theorem base_mem (oracle : EquationOracle model Variable) {kb : LogicalKb Variable Literal Symbol}
    {clause : HornClause Variable Literal Symbol} (member : clause ∈ kb) :
    clause ∈ oracle.extend kb := Or.inl member

theorem equation_mem (oracle : EquationOracle model Variable) (kb : LogicalKb Variable Literal Symbol)
    {body : List (Term Variable Literal Symbol)} {left right : Term Variable Literal Symbol}
    (accepted : oracle.certifies body left right) :
    HornClause.equation left right body ∈ oracle.extend kb :=
  Or.inr ⟨left, right, body, accepted, rfl⟩

/-- Oracle soundness discharges validity of every added clause. -/
theorem models_extension (oracle : EquationOracle model Variable)
    {kb : LogicalKb Variable Literal Symbol} (validKb : model.Models kb) :
    model.Models (oracle.extend kb) := by
  intro clause member environment
  rcases member with original | ⟨left, right, body, accepted, rfl⟩
  · exact validKb _ original environment
  · exact (model.satisfies_equation environment left right body).mpr (oracle.sound accepted environment)

/-- Accepting a conditional equation does not discharge its body. The ordinary
clause rule still requires a proof of the condition in the actual context. -/
theorem derive (oracle : EquationOracle model Variable) (kb : LogicalKb Variable Literal Symbol)
    {context : ProofContext Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}
    {body : List (Term Variable Literal Symbol)} {left right : Term Variable Literal Symbol}
    (accepted : oracle.certifies body left right)
    (condition : Derives hoApplySymbol (oracle.extend kb) context (.conjunction body) naf) :
    Derives hoApplySymbol (oracle.extend kb) context (.equal left right) naf :=
  Derives.equation (oracle.equation_mem kb accepted)
    (Substitutes.identity _) (Substitutes.identity _) (Substitutes.identity _) condition

/-- A concrete semantic oracle specification for closed computations. Equality
is checked at one environment, and closedness makes that check valid at all
environments. This does not assume decidability of equality on the value carrier. -/
def closed (model : Model Literal Symbol Value hoApplySymbol) (Variable : Type) [DecidableEq Variable] :
    EquationOracle model Variable where
  certifies body left right := body = [] ∧ left.freeVars = [] ∧ right.freeVars = [] ∧
    model.eval (fun _ => model.inhabitant) left = model.eval (fun _ => model.inhabitant) right
  sound := by
    intro body left right accepted environment condition
    obtain ⟨_, closedLeft, closedRight, equal⟩ := accepted
    have leftSame : model.eval environment left = model.eval (fun _ => model.inhabitant) left := by
      apply model.eval_congr
      intro name member
      simp [closedLeft] at member
    have rightSame : model.eval environment right = model.eval (fun _ => model.inhabitant) right := by
      apply model.eval_congr
      intro name member
      simp [closedRight] at member
    exact leftSame.trans (equal.trans rightSame.symm)

end EquationOracle

/-- Soundness with positive equation-oracle assistance. NAF adequacy is required
for the extended KB, including all oracle-certified conditional equations. -/
theorem Model.sound_with_equation_oracle (model : Model Literal Symbol Value hoApplySymbol)
    (oracle : EquationOracle model Variable) {kb : LogicalKb Variable Literal Symbol}
    {context : ProofContext Variable Literal Symbol} {goal : Term Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol}
    (validKb : model.Models kb) (adequate : model.FailureAdequate (oracle.extend kb) naf)
    (proof : Derives hoApplySymbol (oracle.extend kb) context goal naf) :
    ∀ environment, model.ContextHolds environment context → model.Satisfies environment goal :=
  model.sound (oracle.models_extension validKb) adequate proof

theorem Model.consistent_with_equation_oracle (model : Model Literal Symbol Value hoApplySymbol)
    (oracle : EquationOracle model Variable) {kb : LogicalKb Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol}
    (validKb : model.Models kb) (adequate : model.FailureAdequate (oracle.extend kb) naf) :
    ¬ Derives hoApplySymbol (oracle.extend kb) [] .falsity naf :=
  model.consistent (oracle.models_extension validKb) adequate

end AnthillModKbSpec.Semantics
