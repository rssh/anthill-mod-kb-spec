import AnthillModKbSpec.Resolution.MillerCertificates
import AnthillModKbSpec.Resolution.CertifiedRefutation

namespace AnthillModKbSpec.MillerResolution

open Semantics MillerCertificates

variable {Variable Literal Symbol Value : Type} [DecidableEq Variable]
variable {hoApplySymbol : Symbol}

/-- Formula-only resolution with a supported Miller-pattern clause step.
There is no InductiveProof goal, schema registry, or induction inference rule:
an induction principle is just a clause selected from the ordinary logical KB.
The rigid parameter list constrains matching; clause substitutions instantiate
templates and never rewrite the query or surrounding assumptions. -/
inductive Proves (model : Model Literal Symbol Value hoApplySymbol)
    (kb : LogicalKb Variable Literal Symbol) :
    List Variable → ProofContext Variable Literal Symbol → Term Variable Literal Symbol → Prop where
  | assumption (member : goal ∈ context) : Proves model kb parameters context goal
  | truth : Proves model kb parameters context .truth
  | conj (left : Proves model kb parameters context a) (right : Proves model kb parameters context b) :
      Proves model kb parameters context (.conj a b)
  | impIntro (proof : Proves model kb parameters (a :: context) b) : Proves model kb parameters context (.imp a b)
  | forallIntro (freshContext : FreshForContext eigen context)
      (freshGoal : eigen ∉ (Term.forallVar binder body).freeVars)
      (opening : Substitutes (Substitution.single binder (.var eigen)) body opened)
      (proof : Proves model kb (eigen :: parameters) context opened) :
      Proves model kb parameters context (.forallVar binder body)
  | clause (member : HornClause.definite head body ∈ kb)
      (headInstance : Substitutes substitution head instantiatedHead)
      (bodyInstance : Substitutes substitution (.conjunction body) instantiatedBody)
      (proof : Proves model kb parameters context instantiatedBody) :
      Proves model kb parameters context instantiatedHead
  | certifiedClause (member : HornClause.definite head body ∈ kb)
      (expanded : Expansion hoApplySymbol parameters head body query)
      (proof : Proves model kb parameters context expanded.instantiatedBody) :
      Proves model kb parameters context query
  | hoApplyIntro (proof : Proves model kb parameters context (.app predicate args)) :
      Proves model kb parameters context (.hoApply hoApplySymbol (.app predicate []) args)
  | hoApplyElim (proof : Proves model kb parameters context (.hoApply hoApplySymbol (.app predicate []) args)) :
      Proves model kb parameters context (.app predicate args)
  | defaultNeg (closed : goal.freeVars = []) (refuted : CertifiedRefutation.Refutes model kb context goal) :
      Proves model kb parameters context (.defaultNeg goal)
  | declarative (proof : Derives hoApplySymbol kb context goal (CertifiedRefutation.failureEvidence model kb)) :
      Proves model kb parameters context goal

variable {model : Model Literal Symbol Value hoApplySymbol} {kb : LogicalKb Variable Literal Symbol}
variable {parameters : List Variable} {context : ProofContext Variable Literal Symbol} {goal : Term Variable Literal Symbol}

/-- Every supported resolution step, including backward lifting of an ordinary
atomic goal into a ho_apply clause head, compiles to the original calculus. -/
theorem Proves.toDerives (proof : Proves model kb parameters context goal) :
    Derives hoApplySymbol kb context goal (CertifiedRefutation.failureEvidence model kb) := by
  induction proof with
  | assumption member => exact .assumption member
  | truth => exact .truth
  | conj left right ihLeft ihRight => exact .conjIntro ihLeft ihRight
  | impIntro proof ih => exact .impIntro ih
  | forallIntro freshContext freshGoal opening proof ih => exact .forallIntro freshContext freshGoal opening ih
  | clause member headInstance bodyInstance proof ih => exact .clause member headInstance bodyInstance ih
  | certifiedClause member expanded proof ih => exact expanded.toDerives member ih
  | hoApplyIntro proof ih => exact .hoApplyIntro ih
  | hoApplyElim proof ih => exact .hoApplyElim ih
  | defaultNeg closed refuted => exact refuted.toDerives closed
  | declarative proof => exact proof

theorem Proves.sound (validKb : model.Models kb) (negation : model.ComplementNAF)
    (proof : Proves model kb parameters context goal) :
    ∀ environment, model.ContextHolds environment context → model.Satisfies environment goal :=
  CertifiedRefutation.sound model validKb negation proof.toDerives

/-- An ordinary clause can also use executable, capture-safe instantiation. -/
theorem Proves.clauseComputed {head instantiatedHead instantiatedBody : Term Variable Literal Symbol}
    {body : List (Term Variable Literal Symbol)} {substitution : Substitution Variable Literal Symbol}
    (member : HornClause.definite head body ∈ kb)
    (computedHead : head.instantiate? substitution = some instantiatedHead)
    (computedBody : (Term.conjunction body).instantiate? substitution = some instantiatedBody)
    (proof : Proves model kb parameters context instantiatedBody) : Proves model kb parameters context instantiatedHead :=
  .clause member (head.instantiate?_sound computedHead) ((Term.conjunction body).instantiate?_sound computedBody) proof

theorem Proves.generalize (binder : Variable) (fresh : FreshForContext binder context)
    (proof : Proves model kb (binder :: parameters) context goal) :
    Proves model kb parameters context (.forallVar binder goal) := by
  apply Proves.forallIntro (eigen := binder) (opened := goal) fresh
  · simp [Term.freeVars]
  · have same : Substitution.single binder (.var binder) = (Term.var : Substitution Variable Literal Symbol) := by
      funext name
      by_cases same : name = binder <;> simp [Substitution.single, Substitution.bind, same]
    rw [same]
    exact Substitutes.identity _
  · exact proof

theorem no_falsity (validKb : model.Models kb) (negation : model.ComplementNAF) :
    ¬ Proves model kb parameters [] .falsity := fun proof =>
  CertifiedRefutation.consistent model validKb negation proof.toDerives

end AnthillModKbSpec.MillerResolution
