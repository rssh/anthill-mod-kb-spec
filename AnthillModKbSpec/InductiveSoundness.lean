import AnthillModKbSpec.CounterexampleSearch
import AnthillModKbSpec.MillerResolution
import AnthillModKbSpec.EquationOracle

namespace AnthillModKbSpec.InductiveSoundness

open Semantics InductiveDomains

variable {Domain Variable Literal Symbol Value : Type} [DecidableEq Variable]
variable {hoApplySymbol : Symbol}

/-- The hypotheses of soundness over an inductively generated data universe.
Every KB clause, including any membership clauses, induction principles, and
predicate definitions, must hold in the same model. Exact domain realization
is stronger than merely satisfying constructor-closure clauses. No typed sort
system or assumption that the entire carrier consists of data is required. -/
structure Interpretation (family : FiniteFamily Domain Symbol)
    (kb : LogicalKb Variable Literal Symbol) (Value : Type) (hoApplySymbol : Symbol) where
  model : Model Literal Symbol Value hoApplySymbol
  membershipSymbol : Domain → Symbol
  realizes : Realizes model family.definitions membershipSymbol
  validKb : model.Models kb
  negation : model.ComplementNAF

variable {family : FiniteFamily Domain Symbol} {kb : LogicalKb Variable Literal Symbol}

/-- Soundness of the original declarative sublogic. -/
theorem declarative_sound (interpretation : Interpretation family kb Value hoApplySymbol)
    {context : ProofContext Variable Literal Symbol} {goal : Term Variable Literal Symbol}
    (proof : Derives hoApplySymbol kb context goal
      (CertifiedRefutation.failureEvidence interpretation.model kb)) :
    ∀ environment, interpretation.model.ContextHolds environment context →
      interpretation.model.Satisfies environment goal :=
  CertifiedRefutation.sound interpretation.model interpretation.validKb interpretation.negation proof

/-- Main theorem: formula-only backward resolution, including the supported
Miller-pattern match and certified NAF, preserves truth in an inductive KB
model. Induction is an ordinary validated KB clause; no separate induction
goal type or inference axiom is required. -/
theorem sound (interpretation : Interpretation family kb Value hoApplySymbol)
    {parameters : List Variable} {context : ProofContext Variable Literal Symbol}
    {goal : Term Variable Literal Symbol}
    (proof : MillerResolution.Proves interpretation.model kb parameters context goal) :
    ∀ environment, interpretation.model.ContextHolds environment context →
      interpretation.model.Satisfies environment goal :=
  MillerResolution.Proves.sound interpretation.validKb interpretation.negation proof

theorem consistent (interpretation : Interpretation family kb Value hoApplySymbol) {parameters : List Variable} :
    ¬ MillerResolution.Proves interpretation.model kb parameters [] .falsity :=
  MillerResolution.no_falsity interpretation.validKb interpretation.negation

/-- Consistency of the original KB-only declarative sublogic. -/
theorem declarative_consistent (interpretation : Interpretation family kb Value hoApplySymbol) :
    ¬ Derives hoApplySymbol kb [] .falsity
      (CertifiedRefutation.failureEvidence interpretation.model kb) :=
  CertifiedRefutation.consistent interpretation.model interpretation.validKb interpretation.negation

/-- A sound equation oracle preserves the same inductive model, membership
realization, and NAF interpretation while extending the ordinary KB set. -/
def Interpretation.withEquationOracle (interpretation : Interpretation family kb Value hoApplySymbol)
    (oracle : EquationOracle interpretation.model Variable) :
    Interpretation family (oracle.extend kb) Value hoApplySymbol where
  model := interpretation.model
  membershipSymbol := interpretation.membershipSymbol
  realizes := interpretation.realizes
  validKb := oracle.models_extension interpretation.validKb
  negation := interpretation.negation

theorem declarative_sound_with_equation_oracle
    (interpretation : Interpretation family kb Value hoApplySymbol)
    (oracle : EquationOracle interpretation.model Variable)
    {context : ProofContext Variable Literal Symbol} {goal : Term Variable Literal Symbol}
    (proof : Derives hoApplySymbol (oracle.extend kb) context goal
      (CertifiedRefutation.failureEvidence interpretation.model (oracle.extend kb))) :
    ∀ environment, interpretation.model.ContextHolds environment context →
      interpretation.model.Satisfies environment goal :=
  declarative_sound (interpretation.withEquationOracle oracle) proof

theorem sound_with_equation_oracle
    (interpretation : Interpretation family kb Value hoApplySymbol)
    (oracle : EquationOracle interpretation.model Variable)
    {parameters : List Variable} {context : ProofContext Variable Literal Symbol}
    {goal : Term Variable Literal Symbol}
    (proof : MillerResolution.Proves interpretation.model (oracle.extend kb) parameters context goal) :
    ∀ environment, interpretation.model.ContextHolds environment context →
      interpretation.model.Satisfies environment goal :=
  sound (interpretation.withEquationOracle oracle) proof

theorem declarative_consistent_with_equation_oracle
    (interpretation : Interpretation family kb Value hoApplySymbol)
    (oracle : EquationOracle interpretation.model Variable) :
    ¬ Derives hoApplySymbol (oracle.extend kb) [] .falsity
      (CertifiedRefutation.failureEvidence interpretation.model (oracle.extend kb)) :=
  declarative_consistent (interpretation.withEquationOracle oracle)

/-- Existence implies consistency of the positive logic, whose derivability
judgment does not itself depend on which model was chosen. -/
theorem positive_consistent_of_model_exists
    (existsModel : Nonempty (Interpretation family kb Value hoApplySymbol)) :
    ¬ Derives hoApplySymbol kb [] .falsity := by
  obtain ⟨interpretation⟩ := existsModel
  exact interpretation.model.positive_consistent interpretation.validKb

/-- D_all quantification ranges over precisely the family's generated data,
which may be a proper subset of the semantic carrier. -/
theorem forallAll_iff (interpretation : Interpretation family kb Value hoApplySymbol)
    (binder : Variable) (body : Term Variable Literal Symbol) (environment : Environment Variable Value) :
    interpretation.model.Satisfies environment
      ((family.forallAll binder body).toTerm interpretation.membershipSymbol) ↔
      ∀ value : family.Generated, interpretation.model.Satisfies
        (update environment binder (denote interpretation.model value.val)) body :=
  family.forallAll_satisfies_iff interpretation.model interpretation.realizes environment binder body

/-- The domain-certificate extension is sound in the same interpretation.
Its universal conclusion need not have a translation into KB-only Derives. -/
theorem forall_of_counterexample_failure (interpretation : Interpretation family kb Value hoApplySymbol)
    {context : ProofContext Variable Literal Symbol} (binder : Variable) (body : Term Variable Literal Symbol)
    (failed : CounterexampleSearch.Fails interpretation.model family.definitions context
      (family.forallAll binder body)) :
    ∀ environment, interpretation.model.ContextHolds environment context →
      interpretation.model.Satisfies environment
        ((family.forallAll binder body).toTerm interpretation.membershipSymbol) :=
  failed.sound interpretation.realizes

/-- The scoped certified success judgment is also sound whenever its program
represents this exact KB. This does not assert that every raw KB is representable
by the current scoped grammar (in particular, its ordinary atom restriction). -/
theorem scoped_sound [FreshNames Variable]
    (interpretation : Interpretation family kb Value hoApplySymbol)
    {program : ScopedSearch.Program Variable Literal Symbol hoApplySymbol}
    (sameKb : program.toKb = kb) {context : ScopedSearch.Context Variable Literal Symbol hoApplySymbol}
    {goal : Term Variable Literal Symbol}
    (proof : CertifiedScopedSearch.Succeeds interpretation.model program context goal) :
    ∀ environment, interpretation.model.ContextHolds environment context.assumptions →
      interpretation.model.Satisfies environment goal := by
  apply proof.sound (negation := interpretation.negation)
  rw [sameKb]
  exact interpretation.validKb

end AnthillModKbSpec.InductiveSoundness
