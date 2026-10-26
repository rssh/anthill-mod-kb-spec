import AnthillModKbSpec.Foundation.LogicalKb
import AnthillModKbSpec.Foundation.Substitution

namespace AnthillModKbSpec

/-- Local assumptions are formulas with fixed free parameters, not implicitly
universally quantified clause templates. A list records nested context extension;
its order has no logical significance. -/
abbrev ProofContext (Variable Literal Symbol : Type) := List (Formula Variable Literal Symbol)

/-- A name is absent from all free variables of the local context. The KB is
not included: its clause variables are implicitly universally quantified and
are instantiated independently on each use. -/
def FreshForContext {Variable Literal Symbol : Type} [DecidableEq Variable]
    (name : Variable) (context : ProofContext Variable Literal Symbol) : Prop :=
  ∀ assumption ∈ context, name ∉ assumption.freeVars

/-- Evidence supplied by a separate search semantics: the given goal's search
under exactly this application symbol, KB, and local context completed with no
solution. Residual, floundered, open-world, or truncated searches must not supply
this evidence. This predicate is an interface, not an implemented search oracle.
Its correctness must be established when proving soundness of a concrete search
semantics; an arbitrary predicate is not automatically trustworthy. -/
abbrev NafFailure (Variable Literal Symbol : Type) :=
  Symbol → LogicalKb Variable Literal Symbol → ProofContext Variable Literal Symbol →
    Formula Variable Literal Symbol → Prop

/-- The positive calculus has no externally supplied failure evidence. -/
def NafFailure.disabled : NafFailure Variable Literal Symbol := fun _ _ _ _ => False

/-- Declarative derivability: `Derives hoApplySymbol kb context goal naf`.
The final failure-evidence argument defaults to `NafFailure.disabled`, recovering
the positive calculus. All premises of a rule use the same evidence relation.

This is a natural-deduction specification, not a search procedure. Clause
application chooses a capture-avoiding instance and proves its body. Goal-clause
instances derive falsity when their bodies are proved. `defaultNegIntro` requires
a ground operand and separate evidence of complete empty search under the same
KB and context. Lack of a proof by itself does not introduce default negation.
There is no explicit negation, predicate closure policy, indexing, unification algorithm,
termination assumption, or completeness claim about the Anthill resolver.

Free names in goals and local assumptions are fixed parameters: no rule
substitutes through the current sequent. Universal introduction opens a binder
with a fresh such parameter (an eigenvariable). The substitution relation also
permits alpha-renaming of nested binders to avoid capture.

The syntax is deliberately raw. A later well-formedness/signature layer must
restrict usable clause heads, goal forms, and the reserved application symbol.
Semantics.lean proves soundness relative to models of the KB and adequate
failure evidence. No consistency claim is made for arbitrary KBs. -/
inductive Derives {Variable Literal Symbol : Type} [DecidableEq Variable]
    (hoApplySymbol : Symbol) (kb : LogicalKb Variable Literal Symbol) :
    ProofContext Variable Literal Symbol → Formula Variable Literal Symbol →
    (naf : NafFailure Variable Literal Symbol := NafFailure.disabled) → Prop where
  | assumption (member : goal ∈ context) : Derives hoApplySymbol kb context goal naf
  | truth : Derives hoApplySymbol kb context .truth naf
  | conjIntro (left : Derives hoApplySymbol kb context a naf)
      (right : Derives hoApplySymbol kb context b naf) :
      Derives hoApplySymbol kb context (.conj a b) naf
  | conjLeft (proof : Derives hoApplySymbol kb context (.conj a b) naf) :
      Derives hoApplySymbol kb context a naf
  | conjRight (proof : Derives hoApplySymbol kb context (.conj a b) naf) :
      Derives hoApplySymbol kb context b naf
  | disjLeft (proof : Derives hoApplySymbol kb context a naf) :
      Derives hoApplySymbol kb context (.disj a b) naf
  | disjRight (proof : Derives hoApplySymbol kb context b naf) :
      Derives hoApplySymbol kb context (.disj a b) naf
  | disjElim (choice : Derives hoApplySymbol kb context (.disj a b) naf)
      (left : Derives hoApplySymbol kb (a :: context) goal naf)
      (right : Derives hoApplySymbol kb (b :: context) goal naf) :
      Derives hoApplySymbol kb context goal naf
  | impIntro (proof : Derives hoApplySymbol kb (premise :: context) conclusion naf) :
      Derives hoApplySymbol kb context (.imp premise conclusion) naf
  | impElim (rule : Derives hoApplySymbol kb context (.imp premise conclusion) naf)
      (argument : Derives hoApplySymbol kb context premise naf) :
      Derives hoApplySymbol kb context conclusion naf
  /-- Falsity has its usual logical meaning, rather than representing search
  failure. Contradictory KBs therefore invalidate a consistency guarantee. -/
  | falsityElim (proof : Derives hoApplySymbol kb context .falsity naf) :
      Derives hoApplySymbol kb context goal naf
  | forallIntro
      (freshContext : FreshForContext eigen context)
      (freshGoal : eigen ∉ (Term.forallVar binder body).freeVars)
      (opening : Substitutes (Substitution.single binder (.var eigen)) body opened)
      (proof : Derives hoApplySymbol kb context opened naf) :
      Derives hoApplySymbol kb context (.forallVar binder body) naf
  | forallElim (proof : Derives hoApplySymbol kb context (.forallVar binder body) naf)
      (instantiation : Substitutes (Substitution.single binder witness) body instantiated) :
      Derives hoApplySymbol kb context instantiated naf
  | existsIntro
      (instantiation : Substitutes (Substitution.single binder witness) body instantiated)
      (proof : Derives hoApplySymbol kb context instantiated naf) :
      Derives hoApplySymbol kb context (.existsVar binder body) naf
  | existsElim (existence : Derives hoApplySymbol kb context (.existsVar binder body) naf)
      (freshContext : FreshForContext eigen context)
      (freshBody : eigen ∉ (Term.existsVar binder body).freeVars)
      (freshGoal : eigen ∉ goal.freeVars)
      (opening : Substitutes (Substitution.single binder (.var eigen)) body opened)
      (proof : Derives hoApplySymbol kb (opened :: context) goal naf) :
      Derives hoApplySymbol kb context goal naf
  /-- The same simultaneous substitution instantiates head and body. It does
  not affect assumptions, goals, or any other use of the clause. -/
  | clause (member : HornClause.definite head body ∈ kb)
      (headInstance : Substitutes σ head instantiatedHead)
      (bodyInstance : Substitutes σ (.conjunction body) instantiatedBody)
      (proof : Derives hoApplySymbol kb context instantiatedBody naf) :
      Derives hoApplySymbol kb context instantiatedHead naf
  | goalClause (member : HornClause.goal body ∈ kb)
      (bodyInstance : Substitutes σ (.conjunction body) instantiatedBody)
      (proof : Derives hoApplySymbol kb context instantiatedBody naf) :
      Derives hoApplySymbol kb context .falsity naf
  /-- Ground negation as failure. Complete empty search is a separate positive
  premise, not `¬ Derives ... goal`. A failed, suspended, or bounded proof attempt
  cannot be substituted for this evidence. The context is part of the evidence,
  so failure in an outer context cannot simply be reused under new assumptions.
  Free goal names (including eigenvariables) conservatively block this rule. -/
  | defaultNegIntro (ground : goal.freeVars = [])
      (refuted : naf hoApplySymbol kb context goal) :
      Derives hoApplySymbol kb context (.defaultNeg goal) naf
  /-- A concrete symbol predicate and its explicit `ho_apply` form are
  interchangeable in proofs, including when obtained from local assumptions.
  No rule applies an unresolved variable, literal, or compound predicate. -/
  | hoApplyIntro (proof : Derives hoApplySymbol kb context (.app predicate args) naf) :
      Derives hoApplySymbol kb context (.hoApply hoApplySymbol (.app predicate []) args) naf
  | hoApplyElim
      (proof : Derives hoApplySymbol kb context (.hoApply hoApplySymbol (.app predicate []) args) naf) :
      Derives hoApplySymbol kb context (.app predicate args) naf
  | equalRefl : Derives hoApplySymbol kb context (.equal term term) naf
  | equalSymm (proof : Derives hoApplySymbol kb context (.equal a b) naf) :
      Derives hoApplySymbol kb context (.equal b a) naf
  | equalTrans (left : Derives hoApplySymbol kb context (.equal a b) naf)
      (right : Derives hoApplySymbol kb context (.equal b c) naf) :
      Derives hoApplySymbol kb context (.equal a c) naf
  /-- Replace equal values in a formula, with both context instances checked by
  capture-avoiding substitution. This also permits replacement inside operations. -/
  | equalSubst (equality : Derives hoApplySymbol kb context (.equal a b) naf)
      (leftInstance : Substitutes (Substitution.single name a) template before)
      (rightInstance : Substitutes (Substitution.single name b) template after)
      (proof : Derives hoApplySymbol kb context before naf) :
      Derives hoApplySymbol kb context after naf

/-- Conditional equations use the ordinary KB clause rule with one substitution
for the two sides and the condition body. -/
theorem Derives.equation {Variable Literal Symbol : Type} [DecidableEq Variable]
    {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
    {context : ProofContext Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}
    {left right left' right' condition : Term Variable Literal Symbol}
    {body : List (Term Variable Literal Symbol)} {σ : Substitution Variable Literal Symbol}
    (member : HornClause.equation left right body ∈ kb)
    (leftInstance : Substitutes σ left left') (rightInstance : Substitutes σ right right')
    (bodyInstance : Substitutes σ (.conjunction body) condition)
    (proof : Derives hoApplySymbol kb context condition naf) :
    Derives hoApplySymbol kb context (.equal left' right') naf :=
  .clause member (.equal leftInstance rightInstance) bodyInstance proof

end AnthillModKbSpec
