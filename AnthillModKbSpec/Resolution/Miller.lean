import AnthillModKbSpec.Foundation.Syntax

namespace AnthillModKbSpec

/-- Extract a name only from a bare variable. -/
def Term.variableName? {Variable Literal Symbol : Type} : Term Variable Literal Symbol → Option Variable
  | .var name => some name
  | _ => none

/-- The local Miller argument restriction: distinct bare bound variables. -/
def IsMillerArguments {Variable Literal Symbol : Type} (bound : List Variable)
    (args : List (Term Variable Literal Symbol)) : Prop :=
  let names := args.filterMap Term.variableName?
  names.length = args.length ∧ names.Nodup ∧ ∀ name ∈ names, name ∈ bound

/-- Optional local restriction on an explicit `ho_apply` occurrence with a free
variable predicate. Bound predicate occurrences are treated as rigid here.
This is neither a callability/type/arity check nor a higher-order unification theorem. -/
def Term.MillerHead {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Symbol]
    (term : Term Variable Literal Symbol) (hoApplySymbol : Symbol) (bound : List Variable) : Prop :=
  match term with
  | .app symbol (.var name :: args) =>
      if symbol = hoApplySymbol ∧ name ∉ bound then IsMillerArguments bound args else True
  | _ => True

/-- Check every occurrence, including scoped terms stored inside applications.
Quantifiers extend the shared binding context; implications preserve it on both
sides. Replacing a binder by a flexible unknown requires checking again.
This syntactic experiment does not establish a full Miller pattern calculus. -/
def Term.IsMiller {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Symbol]
    (term : Term Variable Literal Symbol) (hoApplySymbol : Symbol)
    (bound : List Variable := []) : Prop :=
  match term with
  | .var _ | .lit _ | .truth | .falsity => True
  | .defaultNeg body => body.IsMiller hoApplySymbol bound
  | .dictionaryCall dictionary _ _ args =>
      dictionary.IsMiller hoApplySymbol bound ∧ ∀ arg ∈ args, arg.IsMiller hoApplySymbol bound
  | .app symbol args =>
      (Term.app symbol args).MillerHead hoApplySymbol bound ∧
        ∀ arg ∈ args, arg.IsMiller hoApplySymbol bound
  | .conj left right | .disj left right | .imp left right | .equal left right =>
      left.IsMiller hoApplySymbol bound ∧ right.IsMiller hoApplySymbol bound
  | .forallVar name body | .existsVar name body =>
      body.IsMiller hoApplySymbol (name :: bound)

end AnthillModKbSpec
