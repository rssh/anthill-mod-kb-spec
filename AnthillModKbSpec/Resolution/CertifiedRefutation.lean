import AnthillModKbSpec.Foundation.InductiveDomains
import AnthillModKbSpec.Foundation.Established
import AnthillModKbSpec.Resolution.ScopedAtomSemantics

namespace AnthillModKbSpec.CertifiedRefutation

open Semantics

variable {Variable Literal Symbol Value : Type} [DecidableEq Variable] {hoApplySymbol : Symbol}

/-- A semantic refutation certificate, separate from operational search failure.
Ground leaves require a completed model of the exact program. Scoped atom
leaves require exact-scope completion and certified refutations of every
instantiated body in an exhaustive cover. Implication
requires established antecedent truth and consequent refutation in the SAME
original context. Guarded universals require actual generated counterexamples. -/
inductive Refutes (model : Model Literal Symbol Value hoApplySymbol)
    (kb : LogicalKb Variable Literal Symbol) : ProofContext Variable Literal Symbol →
    Term Variable Literal Symbol → Prop where
  | ground {program : GroundSearch.Program Variable Literal Symbol hoApplySymbol}
      {context : GroundSearch.Context Variable Literal Symbol hoApplySymbol}
      (sameKb : program.toKb = kb)
      (completed : model.GroundCompleted program context)
      (failed : GroundSearch.Fails program context goal) : Refutes model kb context.assumptions goal
  | scopedAtom {program : ScopedSearch.Program Variable Literal Symbol hoApplySymbol}
      {context : ScopedSearch.Context Variable Literal Symbol hoApplySymbol}
      (sameKb : program.toKb = kb)
      (valid : ScopedSearch.IsAtom hoApplySymbol context.parameters atom)
      (closed : atom.freeVars = []) (contextClosed : context.Closed)
      (completed : model.ScopedAtomCompleted program context atom)
      (absent : atom ∉ context.assumptions)
      (generator : ScopedSearch.ExhaustedInstances program context atom)
      (bodiesRefuted : ∀ body ∈ generator.bodies,
        Refutes model kb context.assumptions (.conjunction body)) :
      Refutes model kb context.assumptions atom
  | falsity : Refutes model kb context .falsity
  | imp (antecedent : Established model context a) (consequent : Refutes model kb context b) :
      Refutes model kb context (.imp a b)
  | conjLeft (left : Refutes model kb context a) : Refutes model kb context (.conj a b)
  | conjRight (right : Refutes model kb context b) : Refutes model kb context (.conj a b)
  | disj (left : Refutes model kb context a) (right : Refutes model kb context b) :
      Refutes model kb context (.disj a b)
  | defaultNeg (established : Established model context goal) : Refutes model kb context (.defaultNeg goal)
  | guarded {Domain : Type} {sigma : InductiveDomains.Definitions Domain Symbol}
      {membershipSymbol : Domain → Symbol}
      {goal : InductiveDomains.Universal Domain Variable Literal Symbol}
      (realizes : InductiveDomains.Realizes model sigma membershipSymbol)
      (counterexamples : ∀ environment, model.ContextHolds environment context →
        InductiveDomains.Refutes sigma goal.domains (fun tree => model.Satisfies
          (update environment goal.binder (InductiveDomains.denote model tree)) goal.body)) :
      Refutes model kb context (goal.toTerm membershipSymbol)

variable {model : Model Literal Symbol Value hoApplySymbol} {kb : LogicalKb Variable Literal Symbol}
variable {context : ProofContext Variable Literal Symbol} {goal : Term Variable Literal Symbol}

theorem Refutes.sound (negation : model.ComplementNAF) (refuted : Refutes model kb context goal) :
    ∀ environment, model.ContextHolds environment context → ¬ model.Satisfies environment goal := by
  induction refuted with
  | ground sameKb completed failed =>
      intro environment valid
      exact (model.ground_certificates_sound completed negation).2 _ failed environment
  | scopedAtom sameKb valid closed contextClosed completed absent generator bodiesRefuted ih =>
      exact model.scoped_atom_refuted completed absent generator ih
  | falsity =>
      intro environment valid proof
      exact model.holds_bottom (by simpa only [Model.Satisfies, Model.eval] using proof)
  | imp antecedent consequent ih =>
      intro environment valid proof
      simp only [Model.Satisfies, Model.eval] at proof
      exact ih environment valid ((model.holds_implication _ _).mp proof (antecedent environment valid))
  | conjLeft left ih =>
      intro environment valid proof
      simp only [Model.Satisfies, Model.eval] at proof
      exact ih environment valid ((model.holds_conjunction _ _).mp proof).1
  | conjRight right ih =>
      intro environment valid proof
      simp only [Model.Satisfies, Model.eval] at proof
      exact ih environment valid ((model.holds_conjunction _ _).mp proof).2
  | disj left right ihLeft ihRight =>
      intro environment valid proof
      simp only [Model.Satisfies, Model.eval] at proof
      exact ((model.holds_disjunction _ _).mp proof).elim (ihLeft environment valid) (ihRight environment valid)
  | defaultNeg established =>
      intro environment valid proof
      exact model.defaultNegation_coherent _
        (by simpa only [Model.Satisfies, Model.eval] using proof) (established environment valid)
  | @guarded context Domain sigma membershipSymbol universal realizes counterexamples =>
      intro environment valid
      exact universal.refutes_sound model realizes environment (counterexamples environment valid)

theorem Refutes.not_established (negation : model.ComplementNAF)
    (refuted : Refutes model kb context goal) (environment : Environment Variable Value)
    (valid : model.ContextHolds environment context) : ¬ Established model context goal :=
  fun established => refuted.sound negation environment valid (established environment valid)

theorem Refutes.naf (negation : model.ComplementNAF) (refuted : Refutes model kb context goal) :
    ∀ environment, model.ContextHolds environment context → model.Satisfies environment (.defaultNeg goal) := by
  intro environment valid
  simp only [Model.Satisfies, Model.eval]
  exact (negation _).mpr (refuted.sound negation environment valid)

/-- Adapt the atomic case of the old operational failure judgment only when
all applicable bodies have certified refutations. The old recursive Fails
premises alone do not supply those certificates. -/
theorem Refutes.ofScopedAtomFailure [FreshNames Variable]
    {program : ScopedSearch.Program Variable Literal Symbol hoApplySymbol}
    {scope : ScopedSearch.Context Variable Literal Symbol hoApplySymbol}
    {symbol : Symbol} {args : List (Term Variable Literal Symbol)}
    (sameKb : program.toKb = kb)
    (completed : model.ScopedAtomCompleted program scope (.app symbol args))
    (failed : ScopedSearch.Fails program scope (.app symbol args))
    (certify : ∀ body, ScopedSearch.Instance program scope (.app symbol args) body →
      Refutes model kb scope.assumptions (.conjunction body)) :
    Refutes model kb scope.assumptions (.app symbol args) := by
  cases failed with
  | atom valid closed contextClosed absent generator allBodies =>
      exact .scopedAtom sameKb valid closed contextClosed completed absent generator
        (fun body member => certify body (generator.sound body member))

/-- Scoped positive support can establish an implication antecedent without
using the legacy scoped NAF adapter. -/
theorem Established.ofScopedInstance (model : Model Literal Symbol Value hoApplySymbol)
    {program : ScopedSearch.Program Variable Literal Symbol hoApplySymbol}
    {scope : ScopedSearch.Context Variable Literal Symbol hoApplySymbol}
    {atom : Term Variable Literal Symbol} {body : List (Term Variable Literal Symbol)}
    (completed : model.ScopedAtomCompleted program scope atom)
    (instanceProof : ScopedSearch.Instance program scope atom body)
    (establishedBody : Established model scope.assumptions (.conjunction body)) :
    Established model scope.assumptions atom :=
  model.scoped_atom_supported completed instanceProof establishedBody

/-- Only refutation certificates supply evidence here. No rule accepts an
arbitrary ScopedSearch.Fails certificate. The KB and application symbol retain
the same identity guards as the other failure-evidence adapters. -/
def failureEvidence (model : Model Literal Symbol Value hoApplySymbol)
    (kb : LogicalKb Variable Literal Symbol) : NafFailure Variable Literal Symbol :=
  fun actualSymbol actualKb context goal =>
    actualSymbol = hoApplySymbol ∧ actualKb = kb ∧ Refutes model kb context goal

theorem failureAdequate (model : Model Literal Symbol Value hoApplySymbol)
    (negation : model.ComplementNAF) (kb : LogicalKb Variable Literal Symbol) :
    model.FailureAdequate kb (failureEvidence model kb) := by
  intro context goal closed evidence environment valid
  exact evidence.2.2.naf negation environment valid

/-- A closed operand with a certified refutation gives an actual declarative
NAF proof using the adequate provider. The existing free-variable gate remains. -/
theorem Refutes.toDerives (closed : goal.freeVars = []) (refuted : Refutes model kb context goal) :
    Derives hoApplySymbol kb context (.defaultNeg goal) (failureEvidence model kb) :=
  .defaultNegIntro closed ⟨rfl, rfl, refuted⟩

theorem sound (model : Model Literal Symbol Value hoApplySymbol)
    (validKb : model.Models kb) (negation : model.ComplementNAF)
    (proof : Derives hoApplySymbol kb context goal (failureEvidence model kb)) :
    ∀ environment, model.ContextHolds environment context → model.Satisfies environment goal :=
  model.sound validKb (failureAdequate model negation kb) proof

theorem consistent (model : Model Literal Symbol Value hoApplySymbol)
    (validKb : model.Models kb) (negation : model.ComplementNAF) :
    ¬ Derives hoApplySymbol kb [] .falsity (failureEvidence model kb) :=
  model.consistent validKb (failureAdequate model negation kb)

end AnthillModKbSpec.CertifiedRefutation
