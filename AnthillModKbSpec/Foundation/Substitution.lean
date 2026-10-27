import AnthillModKbSpec.Foundation.Syntax

namespace AnthillModKbSpec

/-- Free variable names, with repetitions allowed. Binder names are removed only
from their own bodies; application arguments can themselves contain scopes. -/
def Term.freeVars {Variable Literal Symbol : Type} [DecidableEq Variable] :
    Term Variable Literal Symbol → List Variable
  | .var name => [name]
  | .lit _ | .truth | .falsity => []
  | .app _ args => args.flatMap Term.freeVars
  | .dictionaryCall dictionary _ _ args => dictionary.freeVars ++ args.flatMap Term.freeVars
  | .defaultNeg body => body.freeVars
  | .conj left right | .disj left right | .imp left right | .equal left right =>
      left.freeVars ++ right.freeVars
  | .forallVar name body | .existsVar name body => body.freeVars.filter (· != name)

/-- A simultaneous substitution for free variables. Its images are not
recursively substituted. Substitutions instantiate clause templates, never the
surrounding proof context or the rigid parameters of an existing goal. -/
abbrev Substitution (Variable Literal Symbol : Type) :=
  Variable → Term Variable Literal Symbol

/-- Override one name in a substitution. -/
def Substitution.bind {Variable Literal Symbol : Type} [DecidableEq Variable]
    (σ : Substitution Variable Literal Symbol) (name : Variable)
    (value : Term Variable Literal Symbol) : Substitution Variable Literal Symbol :=
  fun candidate => if candidate = name then value else σ candidate

/-- Replace one free variable and leave all other names unchanged. -/
def Substitution.single {Variable Literal Symbol : Type} [DecidableEq Variable]
    (name : Variable) (value : Term Variable Literal Symbol) : Substitution Variable Literal Symbol :=
  Substitution.bind Term.var name value

mutual
/-- Capture-avoiding simultaneous substitution, expressed as a relation.
At a binder `x`, choose an output binder `y` that cannot capture any substituted
free variable of the body. Override `x` by `y` while traversing that body. Thus
bound variables are preserved (possibly alpha-renamed) and inner binders shadow
outer bindings. No arbitrary fresh-name algorithm is built into the syntax. -/
inductive Substitutes {Variable Literal Symbol : Type} [DecidableEq Variable] :
    Substitution Variable Literal Symbol →
    Term Variable Literal Symbol → Term Variable Literal Symbol → Prop where
  | var : Substitutes σ (.var name) (σ name)
  | lit : Substitutes σ (.lit value) (.lit value)
  | truth : Substitutes σ .truth .truth
  | falsity : Substitutes σ .falsity .falsity
  | app (args : SubstitutesList σ before after) :
      Substitutes σ (.app symbol before) (.app symbol after)
  | conj (left : Substitutes σ a a') (right : Substitutes σ b b') :
      Substitutes σ (.conj a b) (.conj a' b')
  | disj (left : Substitutes σ a a') (right : Substitutes σ b b') :
      Substitutes σ (.disj a b) (.disj a' b')
  | imp (premise : Substitutes σ a a') (conclusion : Substitutes σ b b') :
      Substitutes σ (.imp a b) (.imp a' b')
  | defaultNeg (body : Substitutes σ before after) :
      Substitutes σ (.defaultNeg before) (.defaultNeg after)
  | forallVar
      (fresh : ∀ name ∈ body.freeVars, name ≠ binder → renamed ∉ (σ name).freeVars)
      (bodySubst : Substitutes (Substitution.bind σ binder (.var renamed)) body result) :
      Substitutes σ (.forallVar binder body) (.forallVar renamed result)
  | existsVar
      (fresh : ∀ name ∈ body.freeVars, name ≠ binder → renamed ∉ (σ name).freeVars)
      (bodySubst : Substitutes (Substitution.bind σ binder (.var renamed)) body result) :
      Substitutes σ (.existsVar binder body) (.existsVar renamed result)
  | dictionaryCall (dictionary : Substitutes σ beforeDictionary afterDictionary)
      (args : SubstitutesList σ before after) :
      Substitutes σ (.dictionaryCall beforeDictionary path operation before)
        (.dictionaryCall afterDictionary path operation after)
  | equal (left : Substitutes σ a a') (right : Substitutes σ b b') :
      Substitutes σ (.equal a b) (.equal a' b')

/-- The same substitution applied pointwise to argument lists. -/
inductive SubstitutesList {Variable Literal Symbol : Type} [DecidableEq Variable] :
    Substitution Variable Literal Symbol →
    List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) → Prop where
  | nil : SubstitutesList σ [] []
  | cons (head : Substitutes σ a b) (tail : SubstitutesList σ as bs) :
      SubstitutesList σ (a :: as) (b :: bs)
end

/-- A single substitution replaces the selected variable by its witness. -/
theorem Substitutes.singleVar {Variable Literal Symbol : Type} [DecidableEq Variable]
    (name : Variable) (witness : Term Variable Literal Symbol) :
    Substitutes (Substitution.single name witness) (.var name) witness := by
  simpa [Substitution.single, Substitution.bind] using
    (Substitutes.var (σ := Substitution.single name witness) (name := name) :
      Substitutes (Substitution.single name witness) (.var name)
        ((Substitution.single name witness) name))

/-- Substituting a goal list pointwise substitutes its conjunction. -/
theorem SubstitutesList.conjunction {Variable Literal Symbol : Type} [DecidableEq Variable]
    {σ : Substitution Variable Literal Symbol} {before after : List (Term Variable Literal Symbol)}
    (proof : SubstitutesList σ before after) : Substitutes σ (.conjunction before) (.conjunction after) := by
  induction before generalizing after with
  | nil => cases proof; exact .truth
  | cons head tail ih => cases proof with | cons first rest => exact .conj first (ih rest)

end AnthillModKbSpec
