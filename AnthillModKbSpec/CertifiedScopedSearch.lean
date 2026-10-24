import AnthillModKbSpec.CertifiedRefutation

namespace AnthillModKbSpec.CertifiedScopedSearch

open Semantics

variable {Variable Literal Symbol Value : Type} [DecidableEq Variable] [FreshNames Variable]
variable {hoApplySymbol : Symbol}

/-- The certified scoped success path. Positive clause selection, hypothetical
contexts, and rigid opening follow ScopedSearch. NAF requires Refutes, never
raw operational Fails. Guarded universals additionally accept certified domain
proofs obtained by induction or exhaustive finite coverage. These are proof
certificates, not an executable search algorithm. -/
inductive Succeeds (model : Model Literal Symbol Value hoApplySymbol)
    (program : ScopedSearch.Program Variable Literal Symbol hoApplySymbol) :
    ScopedSearch.Context Variable Literal Symbol hoApplySymbol → Term Variable Literal Symbol → Prop where
  | assumption {context : ScopedSearch.Context Variable Literal Symbol hoApplySymbol}
      (valid : ScopedSearch.IsAtom hoApplySymbol context.parameters (.app symbol args))
      (member : Term.app symbol args ∈ context.assumptions) :
      Succeeds model program context (.app symbol args)
  | clause {context : ScopedSearch.Context Variable Literal Symbol hoApplySymbol}
      (valid : ScopedSearch.IsAtom hoApplySymbol context.parameters (.app symbol args))
      (instantiation : ScopedSearch.Instance program context (.app symbol args) body)
      (proof : Succeeds model program context (.conjunction body)) :
      Succeeds model program context (.app symbol args)
  | truth {context : ScopedSearch.Context Variable Literal Symbol hoApplySymbol} :
      Succeeds model program context .truth
  | conj {context : ScopedSearch.Context Variable Literal Symbol hoApplySymbol}
      (left : Succeeds model program context a) (right : Succeeds model program context b) :
      Succeeds model program context (.conj a b)
  | defaultNeg {context : ScopedSearch.Context Variable Literal Symbol hoApplySymbol}
      (closed : goal.freeVars = [])
      (refuted : CertifiedRefutation.Refutes model program.toKb context.assumptions goal) :
      Succeeds model program context (.defaultNeg goal)
  | forallVar {context : ScopedSearch.Context Variable Literal Symbol hoApplySymbol}
      (valid : ScopedSearch.IsGoal hoApplySymbol context.parameters (.forallVar binder body))
      (proof : Succeeds model program (context.extend (context.eigen binder body))
        (body.openFree binder (context.eigen binder body))) :
      Succeeds model program context (.forallVar binder body)
  | imp {context : ScopedSearch.Context Variable Literal Symbol hoApplySymbol}
      (premise : ScopedSearch.IsLocal hoApplySymbol context.parameters antecedent)
      (conclusion : ScopedSearch.IsGoal hoApplySymbol context.parameters consequent)
      (proof : Succeeds model program (context.assume antecedent premise) consequent) :
      Succeeds model program context (.imp antecedent consequent)
  | guarded {context : ScopedSearch.Context Variable Literal Symbol hoApplySymbol}
      {Domain : Type} {sigma : InductiveDomains.Definitions Domain Symbol}
      {membershipSymbol : Domain → Symbol}
      {goal : InductiveDomains.Universal Domain Variable Literal Symbol}
      (realizes : InductiveDomains.Realizes model sigma membershipSymbol)
      (proof : ∀ environment, model.ContextHolds environment context.assumptions →
        InductiveDomains.Holds sigma goal.domains (fun tree => model.Satisfies
          (update environment goal.binder (InductiveDomains.denote model tree)) goal.body)) :
      Succeeds model program context (goal.toTerm membershipSymbol)

variable {model : Model Literal Symbol Value hoApplySymbol}
variable {program : ScopedSearch.Program Variable Literal Symbol hoApplySymbol}
variable {context : ScopedSearch.Context Variable Literal Symbol hoApplySymbol}
variable {goal : Term Variable Literal Symbol}

/-- Query answers preserve active rigid parameters and validate their instance
in the original context, using certified success rather than legacy success. -/
inductive Answers (model : Model Literal Symbol Value hoApplySymbol)
    (program : ScopedSearch.Program Variable Literal Symbol hoApplySymbol)
    (context : ScopedSearch.Context Variable Literal Symbol hoApplySymbol)
    (query : Term Variable Literal Symbol) (σ : Substitution Variable Literal Symbol) : Prop where
  | intro (safe : ScopedSearch.SafeGoal hoApplySymbol context.parameters query known)
      (preserves : ∀ name ∈ context.parameters, σ name = .var name)
      (instantiation : Substitutes σ query instantiated)
      (valid : ScopedSearch.IsGoal hoApplySymbol context.parameters instantiated)
      (proof : Succeeds model program context instantiated) : Answers model program context query σ

omit [FreshNames Variable] in
private theorem conjunctionSubstitution {σ : Substitution Variable Literal Symbol}
    (proof : SubstitutesList σ before after) : Substitutes σ (.conjunction before) (.conjunction after) := by
  induction before generalizing after with
  | nil => cases proof; exact .truth
  | cons head tail ih => cases proof with | cons first rest => exact .conj first (ih rest)

omit [FreshNames Variable] in
/-- An instance is a positive implication from its body, using only the original
local assumptions. This avoids any dependence on legacy scoped NAF adequacy. -/
private theorem instanceImplication {atom : Term Variable Literal Symbol} {body : List (Term Variable Literal Symbol)}
    (instanceProof : ScopedSearch.Instance program context atom body) :
    Derives hoApplySymbol program.toKb context.assumptions (.imp (.conjunction body) atom) := by
  apply Derives.impIntro
  cases instanceProof with
  | intro member headSubst bodySubst valid =>
      exact .clause member headSubst (conjunctionSubstitution bodySubst) (.assumption (by simp))
  | hypothesis member backchain valid =>
      exact backchain.toDerives (.assumption (by simp [member])) (.conjLeft (b := .truth) (.assumption (by simp [Term.conjunction])))

/-- Soundness of the complete certified success judgment. The hypotheses are
KB validity and the chosen complement interpretation of NAF; adequacy of the
legacy ScopedSearch failure provider is never assumed. -/
theorem Succeeds.sound (validKb : model.Models program.toKb) (negation : model.ComplementNAF)
    (proof : Succeeds model program context goal) :
    ∀ environment, model.ContextHolds environment context.assumptions → model.Satisfies environment goal := by
  induction proof with
  | assumption valid member => intro environment assumptions; exact assumptions _ member
  | clause valid instanceProof bodyProof ih =>
      intro environment assumptions
      have rule := model.positive_sound validKb (instanceImplication instanceProof) environment assumptions
      simp only [Model.Satisfies, Model.eval] at rule
      simp only [Model.Satisfies, Model.eval]
      exact (model.holds_implication _ _).mp rule (ih environment assumptions)
  | truth =>
      intro environment assumptions
      simpa only [Model.Satisfies, Model.eval] using model.holds_top
  | conj left right ihLeft ihRight =>
      intro environment assumptions
      simp only [Model.Satisfies, Model.eval]
      exact (model.holds_conjunction _ _).mpr ⟨ihLeft environment assumptions, ihRight environment assumptions⟩
  | defaultNeg closed refuted => exact refuted.naf negation
  | @forallVar binder body scope valid proof ih =>
      intro environment assumptions
      simp only [Model.Satisfies, Model.eval]
      apply (model.holds_universal _).mpr
      intro value
      have result := ih (update environment (scope.eigen binder body) value)
        (model.context_fresh environment (scope.eigen_freshContext binder body) value assumptions)
      simp only [Model.Satisfies] at result
      rw [model.eval_open_fresh (scope.eigen_freshGoal binder body)
        (scope.opening binder body) environment value] at result
      exact result
  | imp premise conclusion proof ih =>
      intro environment assumptions
      simp only [Model.Satisfies, Model.eval]
      apply (model.holds_implication _ _).mpr
      intro antecedent
      exact ih environment (by
        intro assumption member
        simp only [ScopedSearch.Context.assume, List.mem_cons] at member
        rcases member with rfl | member
        · exact antecedent
        · exact assumptions _ member)
  | guarded realizes proof =>
      intro environment assumptions
      exact (InductiveDomains.Universal.satisfies_iff _ model realizes environment).mpr (proof environment assumptions)

/-- Success can now establish an antecedent for certified implication
refutation, including antecedents whose own proof uses certified NAF. -/
theorem Succeeds.established (validKb : model.Models program.toKb) (negation : model.ComplementNAF)
    (proof : Succeeds model program context goal) :
    CertifiedRefutation.Established model context.assumptions goal := proof.sound validKb negation

theorem Succeeds.refutes_imp (validKb : model.Models program.toKb) (negation : model.ComplementNAF)
    (antecedent : Succeeds model program context a)
    (consequent : CertifiedRefutation.Refutes model program.toKb context.assumptions b) :
    CertifiedRefutation.Refutes model program.toKb context.assumptions (.imp a b) :=
  .imp (antecedent.established validKb negation) consequent

/-- The negative and positive paths cannot certify the same goal in a context
that holds in the chosen model. Unsatisfiable contexts are explicitly excluded. -/
theorem Succeeds.not_refuted (validKb : model.Models program.toKb) (negation : model.ComplementNAF)
    (proof : Succeeds model program context goal) (environment : Environment Variable Value)
    (assumptions : model.ContextHolds environment context.assumptions) :
    ¬ CertifiedRefutation.Refutes model program.toKb context.assumptions goal :=
  fun refuted => refuted.sound negation environment assumptions (proof.sound validKb negation environment assumptions)

theorem Answers.sound {query : Term Variable Literal Symbol} {σ : Substitution Variable Literal Symbol}
    (validKb : model.Models program.toKb) (negation : model.ComplementNAF)
    (answer : Answers model program context query σ) :
    ∃ instantiated, Substitutes σ query instantiated ∧
      ∀ environment, model.ContextHolds environment context.assumptions → model.Satisfies environment instantiated := by
  cases answer with
  | intro safe preserves instantiation valid proof =>
      exact ⟨_, instantiation, proof.sound validKb negation⟩

theorem no_falsity (validKb : model.Models program.toKb) (negation : model.ComplementNAF) :
    ¬ Succeeds model program (⟨[], [], by simp⟩ : ScopedSearch.Context Variable Literal Symbol hoApplySymbol) .falsity := by
  intro proof
  have impossible := proof.sound validKb negation (fun _ => model.inhabitant)
    (by intro assumption member; cases member)
  exact model.holds_bottom (by simpa only [Model.Satisfies, Model.eval] using impossible)

end AnthillModKbSpec.CertifiedScopedSearch
