import AnthillModKbSpec.Foundation.Completion
import AnthillModKbSpec.Resolution.Machine.Unification

/-! # Open atoms (S22)

An open predicate's marked case `p(x̄) :- UNKNOWN` is syntax: the atoms a
formula depends on through it are found without search. The open atoms are the
marker atoms: the completion leaves them unconstrained, and every atom of `p`
the marked case covers holds exactly when its marker atom does. A marker with
arguments, `p(x̄) :- UNKNOWN(x̄)`, keeps each atom of `p` apart; the KB
generator chooses which form to emit.

`openAtomsOf` collects the marker atoms a formula reaches: the marker atoms
among its own atoms, and, for any other atom, those its covering clauses
reach, wherever their bodies mention them. A clause covers an atom when its
head may match it (`mayMatch`): no literal clash, and no clash of declared
free constructors, separates them. A defined operation may equal any value,
and a name matches anything. The result may over-approximate, since head
arguments are matched independently. It is a routing hint: an operand that
reaches an open atom is reported `opened` and no refutation is searched for
it at first, but the logical Unknown always needs checked witnesses. -/

namespace AnthillModKbSpec.Completion

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

attribute [local instance] Machine.termEq

mutual
/-- Two terms may denote the same value: no literal clash, and no clash of two
declared free constructors (`free symbol arity`), separates them. A name
matches anything, since a rigid parameter or an answer name may stand for any
value; so does an application of a symbol that is not a declared free
constructor, and a term of another kind. -/
def mayMatch (free : Symbol → Nat → Bool) : Term Variable Literal Symbol → Term Variable Literal Symbol → Bool
  | .var _, _ => true
  | _, .var _ => true
  | .lit first, .lit second => first == second
  | .lit _, .app symbol args => !free symbol args.length
  | .app symbol args, .lit _ => !free symbol args.length
  | .app first firstArgs, .app second secondArgs =>
      if free first firstArgs.length && free second secondArgs.length then
        first == second && mayMatchAll free firstArgs secondArgs
      else true
  | _, _ => true

/-- `mayMatch` argument by argument, for lists of the same length. -/
def mayMatchAll (free : Symbol → Nat → Bool) :
    List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) → Bool
  | [], [] => true
  | first :: firstRest, second :: secondRest => mayMatch free first second && mayMatchAll free firstRest secondRest
  | _, _ => false
end

/-- A marker atom: an application of a marker. -/
def markerAtom (marker : Symbol → Bool) : Term Variable Literal Symbol → Bool
  | .app symbol _ => marker symbol
  | _ => false

/-- The atoms of a formula in goal positions, through its connectives and
quantifiers; not the applications inside data. -/
def goalAtoms : Term Variable Literal Symbol → List (Term Variable Literal Symbol)
  | .app symbol args => [.app symbol args]
  | .conj left right | .disj left right | .imp left right => goalAtoms left ++ goalAtoms right
  | .defaultNeg body | .forallVar _ body | .existsVar _ body => goalAtoms body
  | _ => []

/-- The bodies of the clauses that may conclude an atom: an atomic head of its
predicate whose arguments may match. -/
def coveringBodies (free : Symbol → Nat → Bool) (clauses : List (HornClause Variable Literal Symbol))
    (symbol : Symbol) (args : List (Term Variable Literal Symbol)) : List (List (Term Variable Literal Symbol)) :=
  clauses.filterMap fun
    | .definite (.app head heads) body => if head = symbol ∧ mayMatchAll free heads args = true then some body else none
    | _ => none

/-- The marker atoms reachable from a worklist of atoms: a marker atom is
collected; any other atom, expanded once, adds the atoms of its covering
clauses' bodies. The fuel bounds the steps. -/
def openReach (marker : Symbol → Bool) (free : Symbol → Nat → Bool) (clauses : List (HornClause Variable Literal Symbol)) :
    Nat → List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol)
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | fuel + 1, atom :: rest, seen =>
      if markerAtom marker atom then atom :: openReach marker free clauses fuel rest seen
      else if seen.contains atom then openReach marker free clauses fuel rest seen
      else
        match atom with
        | .app symbol args =>
            openReach marker free clauses fuel
              (rest ++ (coveringBodies free clauses symbol args).flatMap (·.flatMap goalAtoms)) (atom :: seen)
        | _ => openReach marker free clauses fuel rest seen

/-- The open atoms a formula reaches through the clauses, each once. The fuel
covers every expansion: each distinct atom is expanded at most once, and each
expansion adds at most all the atoms of the clause bodies. -/
def openAtomsOf (marker : Symbol → Bool) (free : Symbol → Nat → Bool) (clauses : List (HornClause Variable Literal Symbol))
    (formula : Term Variable Literal Symbol) : List (Term Variable Literal Symbol) :=
  let atoms := goalAtoms formula
  let bodyAtoms := clauses.flatMap fun
    | .definite _ body | .goal body => body.flatMap goalAtoms
  (openReach marker free clauses ((atoms.length + bodyAtoms.length + 1) * (bodyAtoms.length + 1)) atoms []).eraseDups

/-- The free constructors of a completed program, by symbol and arity. -/
def Completed.free (completion : Completed Variable Literal Symbol) (symbol : Symbol) (arity : Nat) : Bool :=
  completion.constructors.contains (.application symbol arity)

end AnthillModKbSpec.Completion
