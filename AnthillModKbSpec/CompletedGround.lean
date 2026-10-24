import AnthillModKbSpec.SearchSoundness

namespace AnthillModKbSpec.Semantics

variable {Variable Literal Symbol Value : Type} [DecidableEq Variable] {hoApplySymbol : Symbol}
variable (model : Model Literal Symbol Value hoApplySymbol)

/-- The closed-world choice used here: default negation is true exactly when
its operand is false. This is stronger than Model's coherence law. -/
def Model.ComplementNAF : Prop :=
  ∀ value, model.holds (model.defaultNegation value) ↔ ¬ model.holds value

/-- Ground completion relative to the fixed atomic context: an ordinary ground
atom holds iff it is a local fact or some defining clause has a true body.
Unlike Horn implication alone, this excludes unsupported true atoms. This is
a model condition, not an assertion that every program has such a model. -/
def Model.GroundCompleted (program : GroundSearch.Program Variable Literal Symbol hoApplySymbol)
    (context : GroundSearch.Context Variable Literal Symbol hoApplySymbol) : Prop :=
  ∀ atom, GroundSearch.IsAtom hoApplySymbol atom → ∀ environment,
    model.Satisfies environment atom ↔
      atom ∈ context.assumptions ∨
        ∃ body, HornClause.definite atom body ∈ program.clauses ∧
          model.Satisfies environment (.conjunction body)

variable {model}
variable {program : GroundSearch.Program Variable Literal Symbol hoApplySymbol}
variable {context : GroundSearch.Context Variable Literal Symbol hoApplySymbol}

/-- Finite certificates are sound in every completed model with complement NAF.
The mutual induction proves both directions needed by nested NAF. It neither
assumes total search nor equates absence of success with a failure certificate. -/
theorem Model.ground_certificates_sound
    (completed : model.GroundCompleted program context) (negation : model.ComplementNAF) :
    (∀ goal, GroundSearch.Succeeds program context goal → ∀ environment, model.Satisfies environment goal) ∧
    (∀ goal, GroundSearch.Fails program context goal → ∀ environment, ¬ model.Satisfies environment goal) := by
  have positive : ∀ goal (proof : GroundSearch.Succeeds program context goal),
      ∀ environment, model.Satisfies environment goal := by
    intro goal proof
    refine GroundSearch.Succeeds.rec
      (motive_1 := fun goal _ => ∀ environment, model.Satisfies environment goal)
      (motive_2 := fun goal _ => ∀ environment, ¬ model.Satisfies environment goal)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ proof
    · intro symbol args valid member environment
      exact (completed _ valid environment).mpr (Or.inl member)
    · intro symbol args body valid member proof ih environment
      exact (completed _ valid environment).mpr (Or.inr ⟨body, member, ih environment⟩)
    · intro environment; simpa only [Model.Satisfies, Model.eval] using model.holds_top
    · intro a b left right ihLeft ihRight environment
      simp only [Model.Satisfies, Model.eval]
      exact (model.holds_conjunction _ _).mpr ⟨ihLeft environment, ihRight environment⟩
    · intro goal refuted ih environment
      simp only [Model.Satisfies, Model.eval]
      exact (negation _).mpr (ih environment)
    · intro symbol args valid absent allClauses ih environment trueAtom
      rcases (completed _ valid environment).mp trueAtom with member | ⟨body, member, trueBody⟩
      · exact absent member
      · exact ih body member environment trueBody
    · intro environment proof
      exact model.holds_bottom (by simpa only [Model.Satisfies, Model.eval] using proof)
    · intro a b failed valid ih environment proof
      simp only [Model.Satisfies, Model.eval] at proof
      exact ih environment ((model.holds_conjunction _ _).mp proof).1
    · intro a b valid failed ih environment proof
      simp only [Model.Satisfies, Model.eval] at proof
      exact ih environment ((model.holds_conjunction _ _).mp proof).2
    · intro goal proof ih environment refuted
      apply model.defaultNegation_coherent (model.eval environment goal) _ (ih environment)
      simpa only [Model.Satisfies, Model.eval] using refuted
  refine ⟨positive, ?_⟩
  intro goal refuted environment trueGoal
  -- Reuse the positive proof's mutual induction by wrapping failure in NAF.
  have negative := positive (.defaultNeg goal) (.defaultNeg refuted) environment
  exact model.defaultNegation_coherent (model.eval environment goal)
    (by simpa only [Model.Satisfies, Model.eval] using negative) trueGoal

/-- Completion validates the original Horn clauses in addition to its converse. -/
theorem Model.ground_completed_models (completed : model.GroundCompleted program context) :
    model.Models program.toKb := by
  intro clause member environment
  change clause ∈ program.clauses at member
  cases program.wellFormed clause member with
  | definite headValid bodyValid =>
      simp only [Model.Satisfies, HornClause.toFormula, Model.eval]
      apply (model.holds_implication _ _).mpr
      intro bodyTrue
      exact (completed _ headValid environment).mpr (Or.inr ⟨_, member, bodyTrue⟩)

/-- The previously required adequacy condition now follows from completion;
it is not assumed. Evidence remains tied to the exact KB and context. -/
theorem Model.ground_failure_adequate (completed : model.GroundCompleted program context)
    (negation : model.ComplementNAF) :
    model.FailureAdequate program.toKb (GroundSearch.failureEvidence program context) := by
  intro actualContext goal closed evidence environment validContext
  rcases evidence with ⟨sameSymbol, sameKb, sameContext, refuted⟩
  simp only [Model.Satisfies, Model.eval]
  exact (negation _).mpr ((model.ground_certificates_sound completed negation).2 goal refuted environment)

/-- Full declarative soundness using this ground failure provider, with the
adequacy obligation discharged by the completed-model theorem. -/
theorem Model.ground_completed_sound (completed : model.GroundCompleted program context)
    (negation : model.ComplementNAF)
    {assumptions : ProofContext Variable Literal Symbol} {goal : Term Variable Literal Symbol}
    (proof : Derives hoApplySymbol program.toKb assumptions goal
      (GroundSearch.failureEvidence program context)) :
    ∀ environment, model.ContextHolds environment assumptions → model.Satisfies environment goal :=
  model.sound (model.ground_completed_models completed) (model.ground_failure_adequate completed negation) proof

end AnthillModKbSpec.Semantics
