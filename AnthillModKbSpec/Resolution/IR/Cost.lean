import AnthillModKbSpec.Resolution.IR.Evaluate

/-! # Cost classes, before anything runs (S28)

Admission reports a query's cost class with its profile
([decision IR](../../../docs/decision-ir.md)):

| Class | When | Why |
| --- | --- | --- |
| Polynomial, of degree `k` | P0 or P1, and no NAF literal, denial, or condition reads a predicate whose dependency closure reaches a cycle or a marker | Every model then lies between two computable ones, the least fixpoint with the markers false and the greatest with them true |
| Exponential | P0 or P1 otherwise | Deciding the completion's models is NP-hard (supported models); the enumeration is exact |
| Budgeted | P2 | The derivation search bounded by the fuel; S24's iteration and witnesses run once |
| Blocked | Undecided before anything runs | Nothing runs |

The degree is S23's: the most names a rule of the query's dependency closure
joins, a denial (the denials join every query's relevant program), or the
query's goals other than its rigid parameters, and one more for each rigid
parameter the query splits. The class is read on the predicate graph
(`Program.edgesOf`), from the predicates the query, its conditions, and
the denials name. -/

namespace AnthillModKbSpec.IR

open Completion Tabled

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

/-- A query's cost class. -/
inductive Cost where
  | polynomial (degree : Nat)
  | exponential
  | budgeted
  | blocked
  deriving DecidableEq, Repr

namespace Program

variable (program : Program Variable Literal Symbol)

/-- The predicates a body names: its calls' and its NAF literals'. -/
def bodyPredicates (body : List (Goal Variable Literal Symbol)) : List Symbol :=
  body.filterMap fun
    | .call predicate _ | .naf predicate _ => some predicate
    | _ => none

/-- The predicates a body reads under NAF. -/
def nafPredicates (body : List (Goal Variable Literal Symbol)) : List Symbol :=
  body.filterMap fun
    | .naf predicate _ => some predicate
    | _ => none

/-- A body with a marker literal. -/
def hasMarker (body : List (Goal Variable Literal Symbol)) : Bool :=
  body.any fun
    | .marker _ _ => true
    | _ => false

/-- The predicates reachable from some, the starts included. -/
def closureOf (starts : List Symbol) : List Symbol :=
  let symbols := program.predicates.map (·.symbol)
  let edges := edgesOf program.rules
  (starts ++ starts.flatMap (Tabled.reach edges symbols)).eraseDups

/-- A predicate whose dependency closure reaches a cycle or a marker. -/
def hard (symbol : Symbol) : Bool :=
  let symbols := program.predicates.map (·.symbol)
  let edges := edgesOf program.rules
  (program.closureOf [symbol]).any fun reached =>
    (Tabled.reach edges symbols reached).contains reached ||
      (program.rules.any fun rule => rule.head == reached && hasMarker rule.body)

/-- The predicates the query's dependency closure holds: those its goals and
conditions name, the denials', and every one they reach. -/
def queryClosure (query : Query Variable Literal Symbol) : List Symbol :=
  program.closureOf (bodyPredicates query.goals ++ bodyPredicates query.conditions ++
    program.denials.flatMap bodyPredicates)

/-- The predicates read where the models' order matters: under NAF in the
closure's rules and in the goals, and anywhere in the denials and the
conditions. -/
def readers (query : Query Variable Literal Symbol) : List Symbol :=
  let closure := program.queryClosure query
  (program.rules.filter fun rule => closure.contains rule.head).flatMap (fun rule => nafPredicates rule.body) ++
    nafPredicates query.goals ++ bodyPredicates query.conditions ++ program.denials.flatMap bodyPredicates

/-- The degree: the rigid parameters the query splits, one per instance of
the split, and the most names a rule of the closure, a denial, or an
instance's goals join (the goals' names other than the parameters, which an
instance binds). -/
def degree (query : Query Variable Literal Symbol) : Nat :=
  let closure := program.queryClosure query
  query.parameters.length +
    (((program.rules.filter fun rule => closure.contains rule.head).map fun rule => rule.names.eraseDups.length) ++
      program.denials.map (fun body => (bodyNames body).eraseDups.length)).foldr max
      ((bodyNames query.goals).eraseDups.filter fun name => !query.parameters.contains name).length

/-- **The cost class**, before anything runs. -/
def cost (query : Query Variable Literal Symbol) : Cost :=
  match program.classify query with
  | .p0 | .p1 =>
      if (program.readers query).any program.hard || hasMarker query.conditions || program.denials.any hasMarker then
        .exponential
      else .polynomial (program.degree query)
  | .p2 _ => .budgeted
  | .undecided _ => .blocked

end Program

end AnthillModKbSpec.IR
