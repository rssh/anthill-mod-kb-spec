import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.IR AnthillModKbSpec.Answers
  AnthillModKbSpec.Admission AnthillModKbSpec.Completion

namespace IRBudgetedTests

attribute [local instance] AnthillModKbSpec.Machine.termEq

/-! Executable traces of S28's P2 within the fuel: No by S24's refutation, Unknown
by S24's witnesses, Yes by a checked derivation the search finds within the
fuel, Undecided naming the growing call; monotone in the fuel; a P0 or P1
query answered exactly whatever the fuel. Each `#guard` evaluates compiled
code. -/

inductive Sym where
  | path | edge | p | q | r | s | t | u | w | node | allData | a | b | c | zero | succ | ha
  deriving DecidableEq, Repr

abbrev T := Term Nat Nat Sym
abbrev G := Goal Nat Nat Sym

def k (symbol : Sym) : T := .app symbol []
def v (name : Nat) : T := .var name
def succ (term : T) : T := .app .succ [term]

def call (predicate : Sym) (args : List T) : G := .call predicate args
def naf (predicate : Sym) (args : List T) : G := .naf predicate args
def guard (symbol : Sym) (name : Nat) : G := .guard symbol (v name)
def rule (head : Sym) (args : List T) (body : List G) : Rule Nat Nat Sym := ⟨head, args, body⟩
def fact (head : Sym) (args : List T) : Rule Nat Nat Sym := ⟨head, args, []⟩

open Tabled.Mode in
/-- `p`, `q`, `r` unary with an input, `s`, `t`, `u`, `w` nullary; the graph's
`path` and `edge`; the guards `node` (finite) and `allData` (every ground data
term). -/
def declarations : List (Predicate Sym) :=
  [⟨.path, [input, output], .defined⟩, ⟨.edge, [input, output], .defined⟩,
   ⟨.p, [input], .defined⟩, ⟨.q, [input], .defined⟩, ⟨.r, [input], .defined⟩, ⟨.s, [], .defined⟩,
   ⟨.t, [], .defined⟩, ⟨.u, [], .defined⟩, ⟨.w, [], .defined⟩,
   ⟨.node, [input], .guard⟩, ⟨.allData, [input], .guard⟩]

open Tabled.Mode in
/-- S24's unguarded program's modes: `r` and `q` bind their argument, `p`
reads it. -/
def outputDeclarations : List (Predicate Sym) :=
  [⟨.p, [input], .defined⟩, ⟨.q, [output], .defined⟩, ⟨.r, [output], .defined⟩, ⟨.s, [], .defined⟩]

def constructors : List (Constructor Nat Sym) :=
  [.application .a 0, .application .b 0, .application .c 0, .application .zero 0, .application .succ 1]

def members : Sym → Option (List T)
  | .node => some [k .a, k .b, k .c]
  | _ => none

def program (rules : List (Rule Nat Nat Sym)) (denials : List (List G) := [])
    (predicates : List (Predicate Sym) := declarations) : Program Nat Nat Sym :=
  ⟨predicates, constructors, rules, [], denials, fun _ _ => true, members, fun _ _ => none, .ha⟩

def query (goals : List G) (answers : List Nat := []) (conditions : List G := []) : Query Nat Nat Sym :=
  ⟨conditions, goals, answers⟩

/-- The kind of a decision and its evidence. -/
def kind : Decision Nat Nat Sym → String
  | .yes (.relevant _) => "yes (relevant program)"
  | .yes (.derivation _ _) => "yes (derivation)"
  | .no (.relevant _) => "no (relevant program)"
  | .no (.refutation _) => "no (refutation)"
  | .unknown (.assignment _) (.assignment _) => "unknown (assignments)"
  | .unknown (.greatest _) (.least _) => "unknown (fixpoints)"
  | .unknown _ _ => "unknown"
  | .undecided _ => "undecided"

/-- The round a derivation needed. -/
def round : Decision Nat Nat Sym → Option Nat
  | .yes (.derivation round _) => some round
  | _ => none

/-- What an Undecided decision lacks. -/
def missing : Decision Nat Nat Sym → List String
  | .undecided blockers => blockers.map fun blocker =>
      match blocker.missing with
      | .consistency _ => "consistency"
      | .witnesses _ => "witnesses"
      | .termination => "termination"
      | _ => "other"
  | _ => []

/-- The sites and formulas of an Undecided decision's blockers. -/
def named : Decision Nat Nat Sym → List (Option Site × T)
  | .undecided blockers => blockers.map fun blocker =>
      (match blocker.place with
        | .site site => some site
        | .reached _ _ => none, blocker.formula)
  | _ => []

/-- A decision and its certificate's check. -/
def checks (program : Program Nat Nat Sym) (fuel : Nat) (query : Query Nat Nat Sym) : Bool :=
  program.checkDecision query (program.decideWithin fuel query)

/-! ## Growing recursion: Undecided by the fuel, naming the call -/

/-- `p(X) :- allData(X), p(succ(X))`: every call makes a larger one. -/
def growing : Program Nat Nat Sym := program [rule .p [v 0] [guard .allData 0, call .p [succ (v 0)]]]

/- `p(zero)` holds in the greatest fixpoint and fails in the least, but no
abstract witness shows it (the greatest reads the guard atom as false), no
refutation applies, and no derivation exists: Undecided, lacking a
termination argument, at the growing call `p(succ(X))`, the body literal 1 of
rule 0, whatever the fuel. -/
#guard missing (growing.decideWithin 0 (query [call .p [k .zero]])) == ["termination"]
#guard named (growing.decideWithin 20 (query [call .p [k .zero]])) == [(some (.body 0 1), .app .p [succ (v 0)])]

/-! ## Yes within the fuel, monotone -/

/-- The growing rule with the fact `p(succ(succ(zero)))`. -/
def reached : Program Nat Nat Sym :=
  program [rule .p [v 0] [guard .allData 0, call .p [succ (v 0)]], fact .p [succ (succ (k .zero))]]

/- `p(zero)` is derived once the saturation reaches `p(succ(succ(zero)))`:
the fact, then `p(succ(zero))`, then `p(zero)`. Undecided below that fuel;
Yes at it, with the derivation and its round; every larger fuel gives the same
decision. -/
#guard kind (reached.decideWithin 2 (query [call .p [k .zero]])) == "undecided"
#guard kind (reached.decideWithin 3 (query [call .p [k .zero]])) == "yes (derivation)"
#guard round (reached.decideWithin 3 (query [call .p [k .zero]])) == some 3
#guard round (reached.decideWithin 50 (query [call .p [k .zero]])) == some 3
#guard (match reached.decideWithin 3 (query [call .p [k .zero]]), reached.decideWithin 50 (query [call .p [k .zero]]) with
  | .yes (.derivation _ first), .yes (.derivation _ second) => first.steps == second.steps && first.goal == second.goal
  | _, _ => false)

/-! ## Unguarded names: outside the Herbrand reduction -/

/- `q(X) :- r(X).` with no rule for `r`: the name `X` has no guard, so the
query is P2. `q(a)` is not possibly true over the universe and ⋆: No, by S24's
refutation, with no fuel. -/
#guard kind ((program [rule .q [v 0] [call .r [v 0]]]).decideWithin 0 (query [call .q [k .a]])) == "no (refutation)"

/- `p(X). s :- p(a).`: `s` derived from the instance `p(a)`: Yes. With
`s :- p(a), ¬r(a)` and no rule for `r`, the NAF operand `r(a)` is refuted: Yes. -/
#guard kind ((program [fact .p [v 0], rule .s [] [call .p [k .a]]]).decideWithin 5 (query [call .s []])) == "yes (derivation)"
#guard kind ((program [fact .p [v 0], rule .s [] [call .p [k .a], naf .r [k .a]]]).decideWithin 5 (query [call .s []])) ==
  "yes (derivation)"

/- With `r(a).`, the operand is not refuted: no derivation, and `s` fails in
every model (it is refuted over the universe): No. -/
#guard kind ((program [fact .p [v 0], fact .r [k .a], rule .s [] [call .p [k .a], naf .r [k .a]]]).decideWithin 5
  (query [call .s []])) == "no (refutation)"

/-- S24's unguarded program: `r(X) :- r(X). q(X) :- r(X). p(X). s :- q(Y), p(Y).` -/
def unguarded : Program Nat Nat Sym :=
  program [rule .r [v 0] [call .r [v 0]], rule .q [v 0] [call .r [v 0]], fact .p [v 0],
    rule .s [] [call .q [v 1], call .p [v 1]]] [] outputDeclarations

/- `s` fails in the least fixpoint (no `r`) and holds in the greatest (`r(⋆)`
supports itself): Unknown, by S24's two witnesses, with no fuel. -/
#guard kind (unguarded.decideWithin 0 (query [call .s []])) == "unknown (fixpoints)"

/-! ## Left recursion with a free output -/

/-- `path(X, Y) :- node(X), path(X, Z), node(Z), edge(Z, Y), node(Y)`: the
recursive call leaves `Z` free on the cycle, so the query is P2. -/
def leftFree (edges : List (Sym × Sym)) : Program Nat Nat Sym :=
  program (edges.map (fun (from_, to) => fact .edge [k from_, k to]) ++
    [rule .path [v 0, v 1] [guard .node 0, call .edge [v 0, v 1], guard .node 1],
     rule .path [v 0, v 1] [guard .node 0, call .path [v 0, v 2], guard .node 2, call .edge [v 2, v 1], guard .node 1]])

/- Over the chain `a → b → c`, `path(a, c)` is derived through `path(a, b)`
once the saturation has the answers of `path(a, Z)`: Yes. `path(c, a)` has no
edge into `a`: No, by refutation. -/
#guard kind ((leftFree [(.a, .b), (.b, .c)]).decideWithin 10 (query [call .path [k .a, k .c]])) == "yes (derivation)"
#guard kind ((leftFree [(.a, .b), (.b, .c)]).decideWithin 10 (query [call .path [k .c, k .a]])) == "no (refutation)"

/-! ## P0 and P1: the exact answer, whatever the fuel -/

/- `p(a) :- ¬q(a). q(a) :- ¬p(a).`: Unknown by two assignments of the relevant
program, at fuel 0 and at fuel 100 alike; `p(a).`: Yes by its relevant
program; `s. ⊥ :- s.` is inconsistent: Undecided, the KB's consistency, at any
fuel. -/
#guard kind ((program [rule .p [k .a] [naf .q [k .a]], rule .q [k .a] [naf .p [k .a]]]).decideWithin 0
  (query [call .p [k .a]])) == "unknown (assignments)"
#guard kind ((program [rule .p [k .a] [naf .q [k .a]], rule .q [k .a] [naf .p [k .a]]]).decideWithin 100
  (query [call .p [k .a]])) == "unknown (assignments)"
#guard kind ((program [fact .p [k .a]]).decideWithin 0 (query [call .p [k .a]])) == "yes (relevant program)"
#guard kind ((program [fact .p [k .a]]).decideWithin 100 (query [call .p [k .a]])) == "yes (relevant program)"
#guard missing ((program [fact .s []] [[call .s []]]).decideWithin 100 (query [call .s []])) == ["consistency"]

/-! ## What P2 assumes of the KB -/

/- Every answer assumes a model. `q(X) :- r(X).` has an unguarded name, so
every query is P2, the KB-level ones included, and the KB-level check cannot
read the root `s` of `s :- ¬s.`: the gate checks it on its ground closure and
finds no model. `p(a)` answers Undecided, the KB's consistency, not Yes. -/
#guard missing ((program [rule .s [] [naf .s []], fact .p [k .a], rule .q [v 0] [call .r [v 0]]]).decideWithin 5
  (query [call .p [k .a]])) == ["consistency"]

/- A consistent ground cycle `t :- ¬u. u :- ¬t.` beside `p(X). s :- p(a).`:
its ground closure has a model, so `s` answers Yes. With `t :- ¬u, p(a)`, the
closure reaches the rule `p(X)`, which has a name: unsettled, Undecided. -/
#guard kind ((program [rule .t [] [naf .u []], rule .u [] [naf .t []], fact .p [v 0], rule .s [] [call .p [k .a]]]).decideWithin 5
  (query [call .s []])) == "yes (derivation)"
#guard missing ((program [rule .t [] [naf .u [], call .p [k .a]], rule .u [] [naf .t []], fact .p [v 0],
    rule .s [] [call .p [k .a]]]).decideWithin 5 (query [call .s []])) == ["consistency"]

/- The denials: with `p(X)` unguarded no P1 query reads them, so each must be
refuted. `⊥ :- r(a).` with no rule for `r`: refuted, `s` answers Yes. With
`r(a).` too, the denial holds of a fact: Undecided, the KB's consistency. -/
#guard kind ((program [fact .p [v 0], rule .s [] [call .p [k .a]]] [[call .r [k .a]]]).decideWithin 5
  (query [call .s []])) == "yes (derivation)"
#guard missing ((program [fact .p [v 0], fact .r [k .a], rule .s [] [call .p [k .a]]] [[call .r [k .a]]]).decideWithin 5
  (query [call .s []])) == ["consistency"]

/- The growing rule's KB with `u :- ¬w, p(zero). w :- ¬u. s. ⊥ :- s.`: the
roots reach the growing call, but the denials' own query is P1 and has no
model: every query Undecided, `p(zero)` included. -/
#guard missing ((program [rule .p [v 0] [guard .allData 0, call .p [succ (v 0)]], fact .p [succ (succ (k .zero))],
    rule .u [] [naf .w [], call .p [k .zero]], rule .w [] [naf .u []], fact .s []] [[call .s []]]).decideWithin 10
  (query [call .p [k .zero]])) == ["consistency"]

/-! ## Certificates and their checks -/

/- The certificates of five of the decisions above check: two derivations, a
refutation, S24's two witnesses, and a P1 relevant program. -/
#guard checks reached 3 (query [call .p [k .zero]])
#guard checks (program [rule .q [v 0] [call .r [v 0]]]) 0 (query [call .q [k .a]])
#guard checks unguarded 0 (query [call .s []])
#guard checks (leftFree [(.a, .b), (.b, .c)]) 10 (query [call .path [k .a, k .c]])
#guard checks (program [fact .p [k .a]]) 0 (query [call .p [k .a]])

/- A tampered derivation: its first step dropped, offered for another goal,
or for a larger atom: rejected. -/
#guard (match reached.decideWithin 3 (query [call .p [k .zero]]) with
  | .yes (.derivation _ derivation) => !reached.checkDerivation (query [call .p [k .zero]]) { derivation with steps := derivation.steps.tail }
  | _ => false)
#guard (match (program [fact .p [v 0], rule .s [] [call .p [k .a]]]).decideWithin 5 (query [call .s []]) with
  | .yes (.derivation _ derivation) =>
      (program [fact .p [v 0], rule .s [] [call .p [k .a]]]).checkDerivation (query [call .s []]) derivation &&
        !(program [fact .p [v 0], rule .s [] [call .p [k .a]]]).checkDerivation (query [call .p [k .b]]) derivation
  | _ => false)
#guard (match reached.decideWithin 3 (query [call .p [k .zero]]) with
  | .yes (.derivation _ derivation) => !reached.checkDerivation (query [call .p [succ (succ (succ (k .zero)))]]) derivation
  | _ => false)

/- A refutation offered for a query it does not refute, and S24's witnesses
swapped: rejected. -/
#guard !reached.checkDecision (query [call .p [k .zero]]) (.no (.refutation []))
#guard (match unguarded.decideWithin 0 (query [call .s []]) with
  | .unknown (.greatest high) (.least low) => !unguarded.checkDecision (query [call .s []]) (.unknown (.greatest low) (.least high))
  | _ => false)

/- A derivation's values must be its rules' names': `path(X, Y)`'s base rule
has the names `X, Y, X, X, Y, Y`, so changing a repeat, or giving the goal a
value it has no name for, is rejected. -/
#guard (match (leftFree [(.a, .b), (.b, .c)]).decideWithin 10 (query [call .path [k .a, k .c]]) with
  | .yes (.derivation _ derivation) =>
      !(leftFree [(.a, .b), (.b, .c)]).checkDerivation (query [call .path [k .a, k .c]])
        { derivation with steps := derivation.steps.map fun step => (step.1, step.2.set 2 (k .zero)) } &&
      !(leftFree [(.a, .b), (.b, .c)]).checkDerivation (query [call .path [k .a, k .c]]) { derivation with goal := [k .a] }
  | _ => false)

/- Certificates on an inconsistent KB, `s. ⊥ :- s.`: a derivation of `s` and a
refutation of `r(a)` check on their own, but the KB-level check fails:
rejected, as the evaluator answers Undecided. A refutation for a query the
checker rejects (`q(X)` with its input unbound): rejected. -/
#guard !(program [fact .s []] [[call .s []]]).checkDecision (query [call .s []]) (.yes (.derivation 0 ⟨[(0, [])], []⟩))
#guard !(program [fact .s []] [[call .s []]]).checkDecision (query [call .r [k .a]]) (.no (.refutation []))
#guard !(program [rule .q [v 0] [call .r [v 0]]]).checkDecision (query [call .q [v 0]] [0]) (.no (.refutation []))

end IRBudgetedTests
