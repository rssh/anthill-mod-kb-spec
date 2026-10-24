namespace AnthillModKbSpec

/-- A common carrier for data, goals, and scoped logical terms.
All variables share one namespace. A nullary application is a symbol value.
Logical constructors make binding, equality, and nested implication explicit; they do not
specify a resolver or assert that every raw term is a well-formed goal. -/
inductive Term (Variable Literal Symbol : Type) where
  | var (name : Variable)
  | lit (value : Literal)
  | app (symbol : Symbol) (args : List (Term Variable Literal Symbol))
  | truth
  | falsity
  | conj (left right : Term Variable Literal Symbol)
  | disj (left right : Term Variable Literal Symbol)
  /-- In goal position, prove the conclusion under local premise assumptions.
  The assumptions' scope is the conclusion, including its nested goals. -/
  | imp (premise conclusion : Term Variable Literal Symbol)
  /-- Negation as failure (`not body`), distinct from implication to falsity.
  This constructor does not identify failed proof search with a negative proof;
  introduction requires complete-failure evidence in the derivability relation.
  GroundSearch supplies a finite-failure fragment; full resolver soundness is
  a separate obligation. -/
  | defaultNeg (body : Term Variable Literal Symbol)
  /-- Bind every occurrence of this name in the body, including predicate-value
  positions and nested implications. The nearest binder shadows outer ones. -/
  | forallVar (name : Variable) (body : Term Variable Literal Symbol)
  | existsVar (name : Variable) (body : Term Variable Literal Symbol)
  /-- Call an operation in a dictionary, following required-model fields first.
  Dictionary and arguments are ordinary terms. Selectors use the symbol
  namespace and are not variable occurrences. -/
  | dictionaryCall (dictionary : Term Variable Literal Symbol) (path : List Symbol)
      (operation : Symbol) (args : List (Term Variable Literal Symbol))
  /-- Equality of returned values, including operation and dictionary calls. -/
  | equal (left right : Term Variable Literal Symbol)
  deriving Repr

/-- Terms used in atomic goal positions share the common carrier.
This alias does not enforce atomicity. -/
abbrev Atom := Term

/-- Formulas use the same syntax, so scoped formulas can also be term arguments. -/
abbrev Formula := Term

/-- Explicit KB predicate application, using an ordinary designated symbol. -/
def Term.hoApply {Variable Literal Symbol : Type} (hoApplySymbol : Symbol)
    (predicate : Term Variable Literal Symbol) (args : List (Term Variable Literal Symbol)) :
    Term Variable Literal Symbol :=
  .app hoApplySymbol (predicate :: args)

/-- Conjunction of a goal list; an empty list denotes truth. -/
def Term.conjunction {Variable Literal Symbol : Type}
    (goals : List (Term Variable Literal Symbol)) : Term Variable Literal Symbol :=
  goals.foldr .conj .truth

/-- Syntax for the scope of KB `forall_impl(binders, antecedents, consequents)`:
`∀ binders. (conjunction antecedents → conjunction consequents)`.
Binders scope both sides of the implication. This is a notation helper, not an
execution or lowering function. Opening binders with fresh rigid witnesses and
restoring local assumptions are obligations of future operational semantics. -/
def Term.forallImpl {Variable Literal Symbol : Type} (binders : List Variable)
    (antecedents consequents : List (Term Variable Literal Symbol)) :
    Term Variable Literal Symbol :=
  binders.foldr .forallVar (.imp (.conjunction antecedents) (.conjunction consequents))

/-- A clause has at most one positive head. Its body may contain scoped goals
and nested implications, extending ordinary first-order Horn syntax.
Free variables share one implicit universal closure. -/
inductive HornClause (Variable Literal Symbol : Type) where
  | definite (head : Atom Variable Literal Symbol) (body : List (Term Variable Literal Symbol))
  | goal (body : List (Term Variable Literal Symbol))
  deriving Repr

/-- Translate connectives without inserting implicit universal closure. -/
def HornClause.toFormula {Variable Literal Symbol : Type} :
    HornClause Variable Literal Symbol → Formula Variable Literal Symbol
  | .definite head body => .imp (.conjunction body) head
  | .goal body => .imp (.conjunction body) .falsity

/-- `left <=> right :- body`: a definite clause with a value-equality head.
The body and both sides share the clause's implicit universal closure. -/
def HornClause.equation {Variable Literal Symbol : Type}
    (left right : Term Variable Literal Symbol) (body : List (Term Variable Literal Symbol)) :
    HornClause Variable Literal Symbol := .definite (.equal left right) body

end AnthillModKbSpec
