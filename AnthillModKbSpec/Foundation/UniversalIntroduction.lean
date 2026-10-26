import AnthillModKbSpec.Foundation.InductiveDomains
import AnthillModKbSpec.Foundation.Established
import AnthillModKbSpec.Foundation.Opening

namespace AnthillModKbSpec

open Semantics InductiveDomains

variable {Variable Literal Symbol Value Domain : Type} [DecidableEq Variable]
variable {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
variable {context : ProofContext Variable Literal Symbol} {goal : Term Variable Literal Symbol}
variable {naf : NafFailure Variable Literal Symbol}

/-- Universal introduction for a free parameter with the same name as the
binder. It must not occur freely in any undischarged local assumption.
This is derived from the existing eigenvariable rule, not a new axiom. -/
theorem Derives.generalize (proof : Derives hoApplySymbol kb context goal naf)
    (binder : Variable) (fresh : FreshForContext binder context) :
    Derives hoApplySymbol kb context (.forallVar binder goal) naf := by
  apply Derives.forallIntro (eigen := binder) (opened := goal) fresh
  · simp [Term.freeVars]
  · have same : Substitution.single binder (.var binder) = (Term.var : Substitution Variable Literal Symbol) := by
      funext name
      by_cases same : name = binder <;> simp [Substitution.single, Substitution.bind, same]
    rw [same]
    exact Substitutes.identity goal
  · exact proof

/-- Bounded forall introduction: prove the body for an arbitrary parameter
under its D_all membership assumption, then discharge that assumption. The
parameter must be fresh for the remaining local context. -/
theorem Derives.forallAll_intro (family : FiniteFamily Domain Symbol) (binder : Variable)
    (fresh : FreshForContext binder context)
    (proof : Derives hoApplySymbol kb
      (guard membershipSymbol family.domains (.var binder) :: context) goal naf) :
    Derives hoApplySymbol kb context ((family.forallAll binder goal).toTerm membershipSymbol) naf :=
  (Derives.impIntro proof).generalize binder fresh

/-- Read a KB clause as a universally quantified implication restricted to all
declared data domains. Clause variables are templates, so they may be
generalized here even if other clauses mention the same names. -/
theorem Derives.forallAll_of_clause (family : FiniteFamily Domain Symbol)
    (binder : Variable) {head : Term Variable Literal Symbol} {body : List (Term Variable Literal Symbol)}
    (member : HornClause.definite head body ∈ kb) :
    Derives hoApplySymbol kb []
      ((family.forallAll binder (.imp (.conjunction body) head)).toTerm membershipSymbol) := by
  apply Derives.forallAll_intro family binder (by intro assumption impossible; cases impossible)
  apply Derives.impIntro
  exact .clause (σ := Term.var) member (Substitutes.identity _) (Substitutes.identity _)
    (.assumption (by simp))

/-- The common one-premise clause has the exact g -> p goal shape, without
exposing the conjunction-with-True encoding of a singleton clause body. -/
theorem Derives.forallAll_of_single_clause (family : FiniteFamily Domain Symbol)
    (binder : Variable) {head antecedent : Term Variable Literal Symbol}
    (member : HornClause.definite head [antecedent] ∈ kb) :
    Derives hoApplySymbol kb []
      ((family.forallAll binder (.imp antecedent head)).toTerm membershipSymbol) := by
  apply Derives.forallAll_intro family binder (by intro assumption impossible; cases impossible)
  apply Derives.impIntro
  exact .clause (σ := Term.var) member (Substitutes.identity _) (Substitutes.identity _)
    (.conjIntro (.assumption (by simp)) .truth)

/-- Semantic generalization of any established formula, including a derived
implication rather than a clause literally present in the KB. Domain realization
and carrier coverage are unnecessary: restricting a universal preserves truth. -/
theorem Semantics.Model.forallAll_of_established (model : Model Literal Symbol Value hoApplySymbol)
    (family : FiniteFamily Domain Symbol) (binder : Variable)
    (fresh : FreshForContext binder context)
    (proof : CertifiedRefutation.Established model context goal)
    (environment : Environment Variable Value) (assumptions : model.ContextHolds environment context) :
    model.Satisfies environment ((family.forallAll binder goal).toTerm membershipSymbol) := by
  simp only [FiniteFamily.forallAll, Universal.toTerm, Model.Satisfies, Model.eval,
    model.holds_universal, model.holds_implication]
  intro value guardTrue
  exact proof (update environment binder value) (model.context_fresh environment fresh value assumptions)

theorem Semantics.Model.forallAll_of_derives (model : Model Literal Symbol Value hoApplySymbol)
    (family : FiniteFamily Domain Symbol) (binder : Variable)
    (validKb : model.Models kb) (adequate : model.FailureAdequate kb naf)
    (fresh : FreshForContext binder context) (proof : Derives hoApplySymbol kb context goal naf)
    (environment : Environment Variable Value) (assumptions : model.ContextHolds environment context) :
    model.Satisfies environment ((family.forallAll binder goal).toTerm membershipSymbol) :=
  model.forallAll_of_established family binder fresh (model.sound validKb adequate proof) environment assumptions

theorem Semantics.Model.forallAll_of_single_clause (model : Model Literal Symbol Value hoApplySymbol)
    (family : FiniteFamily Domain Symbol) (binder : Variable) (validKb : model.Models kb)
    {head antecedent : Term Variable Literal Symbol}
    (member : HornClause.definite head [antecedent] ∈ kb) (environment : Environment Variable Value) :
    model.Satisfies environment ((family.forallAll binder (.imp antecedent head)).toTerm membershipSymbol) :=
  model.positive_sound validKb (Derives.forallAll_of_single_clause family binder member) environment
    (by intro assumption impossible; cases impossible)

end AnthillModKbSpec
