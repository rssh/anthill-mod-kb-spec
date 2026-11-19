import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.IR AnthillModKbSpec.Answers
  AnthillModKbSpec.Admission AnthillModKbSpec.Completion

namespace IREvaluateTests

attribute [local instance] AnthillModKbSpec.Machine.termEq

/-! Executable traces of S28: the IR evaluator's exact P1 decisions. Each
`#guard` evaluates compiled code: the relevant program built without fuel, its
models by the Kripke–Kleene iteration and enumeration, and the answer. -/

inductive Sym where
  | path | edge | p | q | r | s | t | m | node | item | allData | a | b | c | zero | succ | ha
  deriving DecidableEq, Repr

abbrev T := Term Nat Nat Sym
abbrev G := Goal Nat Nat Sym

def k (symbol : Sym) : T := .app symbol []
def v (name : Nat) : T := .var name

def call (predicate : Sym) (args : List T) : G := .call predicate args
def naf (predicate : Sym) (args : List T) : G := .naf predicate args
def guard (symbol : Sym) (name : Nat) : G := .guard symbol (v name)
def rule (head : Sym) (args : List T) (body : List G) : Rule Nat Nat Sym := ⟨head, args, body⟩
def fact (head : Sym) (args : List T) : Rule Nat Nat Sym := ⟨head, args, []⟩

open Tabled.Mode in
def declarations : List (Predicate Sym) :=
  [⟨.path, [input, output], .defined⟩, ⟨.edge, [input, output], .defined⟩,
   ⟨.p, [], .defined⟩, ⟨.q, [], .defined⟩, ⟨.r, [], .defined⟩, ⟨.s, [], .defined⟩, ⟨.t, [], .defined⟩,
   ⟨.node, [input], .guard⟩, ⟨.item, [input], .guard⟩, ⟨.allData, [input], .guard⟩]

open Tabled.Mode in
/-- The same symbols at arity one, for the non-ground programs. -/
def unaryDeclarations : List (Predicate Sym) :=
  [⟨.p, [input], .defined⟩, ⟨.q, [input], .opened⟩, ⟨.r, [input], .defined⟩,
   ⟨.node, [input], .guard⟩, ⟨.allData, [input], .guard⟩]

def constructors : List (Constructor Nat Sym) :=
  [.application .a 0, .application .b 0, .application .c 0, .application .zero 0, .application .succ 1]

/-- `node` and `item` are finite domains, their members listed; `allData`
holds of every ground data term. -/
def members : Sym → Option (List T)
  | .node => some [k .a, k .b, k .c]
  | .item => some [k .a, k .b]
  | _ => none

def program (rules : List (Rule Nat Nat Sym)) (denials : List (List G) := [])
    (predicates : List (Predicate Sym) := declarations) : Program Nat Nat Sym :=
  ⟨predicates, constructors, rules, [], denials, fun _ _ => true, members, fun _ _ => none, .ha⟩

def query (goals : List G) (answers : List Nat := []) (conditions : List G := []) : Query Nat Nat Sym :=
  ⟨conditions, goals, answers⟩

/-- The kind of an answer. -/
def kind : IRAnswer Nat Nat Sym → String
  | .yes _ => "yes"
  | .no _ => "no"
  | .unknown _ _ => "unknown"
  | .undecided _ => "undecided"

/-- What an Undecided answer lacks. -/
def missing : IRAnswer Nat Nat Sym → List String
  | .undecided blockers => blockers.map fun blocker =>
      match blocker.missing with
      | .consistency _ => "consistency"
      | .witnesses _ => "witnesses"
      | .termination => "termination"
      | .mode => "mode"
      | _ => "other"
  | _ => []

/-- The sites of an Undecided answer's blockers. -/
def sites : IRAnswer Nat Nat Sym → List (Option Site)
  | .undecided blockers => blockers.map fun blocker =>
      match blocker.place with
      | .site site => some site
      | .reached _ _ => none
  | _ => []

/-! ## `path` over a cycle, lowered with its range guards first -/

/-- `edge(a, b). edge(b, a).` and
`path(X, Y) :- node(X), edge(X, Y), node(Y).`
`path(X, Y) :- node(X), edge(X, Z), node(Z), path(Z, Y), node(Y).` -/
def pathRules (guardSymbol : Sym) (edges : List (Sym × Sym)) : List (Rule Nat Nat Sym) :=
  edges.map (fun (from_, to) => fact .edge [k from_, k to]) ++
  [rule .path [v 0, v 1] [guard guardSymbol 0, call .edge [v 0, v 1], guard guardSymbol 1],
   rule .path [v 0, v 1]
     [guard guardSymbol 0, call .edge [v 0, v 2], guard guardSymbol 2, call .path [v 2, v 1], guard guardSymbol 1]]

def cycle : Program Nat Nat Sym := program (pathRules .node [(.a, .b), (.b, .a)])

/- `path(a, b)` holds by the edge: Yes. `path(a, c)` lies on the cycle
`path(a, c) ↔ path(b, c)` with no edge to `c`: false in the least fixpoint and
true in the greatest, both models of the completion: Unknown, where S24 gives
Undecided (its greatest witness reads a guard atom as false). -/
#guard kind (cycle.answer (query [call .path [k .a, k .b]])) == "yes"
#guard kind (cycle.answer (query [call .path [k .a, k .c]])) == "unknown"

/- The lowered program, its guards over `D_all`, an infinite domain decided
on bound names: the same answers. -/
#guard kind ((program (pathRules .allData [(.a, .b), (.b, .a)])).answer (query [call .path [k .a, k .b]])) == "yes"
#guard kind ((program (pathRules .allData [(.a, .b), (.b, .a)])).answer (query [call .path [k .a, k .c]])) == "unknown"

/-! ## `path` over a chain -/

def chain : Program Nat Nat Sym := program (pathRules .node [(.a, .b), (.b, .c)])

/- Over `a → b → c`, `path(a, c)` holds through `b`, and `path(c, a)` has no
instance whose body can hold: No. -/
#guard kind (chain.answer (query [call .path [k .a, k .c]])) == "yes"
#guard kind (chain.answer (query [call .path [k .c, k .a]])) == "no"

/-! ## Left recursion -/

/-- `path(X, Y) :- node(X), node(Z), path(X, Z), edge(Z, Y), node(Y)`: the
translator binds `Z` from the finite `node` first, so the recursive call has
both arguments bound. -/
def leftRules (edges : List (Sym × Sym)) : List (Rule Nat Nat Sym) :=
  edges.map (fun (from_, to) => fact .edge [k from_, k to]) ++
  [rule .path [v 0, v 1] [guard .node 0, call .edge [v 0, v 1], guard .node 1],
   rule .path [v 0, v 1] [guard .node 0, guard .node 2, call .path [v 0, v 2], call .edge [v 2, v 1], guard .node 1]]

/- Over the cycle, `path(a, a)` holds through `b`; `path(a, c)` has no
`edge(Z, c)` for any `Z`: No. Over the chain, `path(a, c)`: Yes. -/
#guard kind ((program (leftRules [(.a, .b), (.b, .a)])).answer (query [call .path [k .a, k .a]])) == "yes"
#guard kind ((program (leftRules [(.a, .b), (.b, .a)])).answer (query [call .path [k .a, k .c]])) == "no"
#guard kind ((program (leftRules [(.a, .b), (.b, .c)])).answer (query [call .path [k .a, k .c]])) == "yes"

/- With `Z` left free on the recursive call (`path(X, Z)` before any guard of
`Z`), the call leaves an output free on the cycle: P2, Undecided before
anything runs, lacking a termination argument. -/
#guard missing ((program
    [fact .edge [k .a, k .b], rule .path [v 0, v 1] [guard .node 0, call .edge [v 0, v 1], guard .node 1],
     rule .path [v 0, v 1] [guard .node 0, call .path [v 0, v 2], guard .node 2, call .edge [v 2, v 1], guard .node 1]]).answer
  (query [call .path [k .a, k .b]])) == ["termination"]

/-! ## NAF loops and the KB's consistency -/

/- `p :- ¬q. q :- ¬p.`: the models `{p}` and `{q}`: Unknown. -/
#guard kind ((program [rule .p [] [naf .q []], rule .q [] [naf .p []]]).answer (query [call .p []])) == "unknown"

/- `p :- ¬p.`: no model: Undecided, the KB's consistency. -/
#guard missing ((program [rule .p [] [naf .p []]]).answer (query [call .p []])) == ["consistency"]

/- `p :- q. p :- ¬q. q :- q.`: `p` holds in every model, whichever value `q`
takes, with no derivation: Yes. -/
#guard kind ((program [rule .p [] [call .q []], rule .p [] [naf .q []], rule .q [] [call .q []]]).answer
  (query [call .p []])) == "yes"

/- A denial rules out a model of the query's part on a consistent KB:
`p :- ¬q. q :- ¬p. ⊥ :- p.` makes `p` false: No. -/
#guard kind ((program [rule .p [] [naf .q []], rule .q [] [naf .p []]] [[call .p []]]).answer (query [call .p []])) == "no"

/- `p. ⊥ :- p.`: no model: Undecided, the KB's consistency. -/
#guard missing ((program [fact .p []] [[call .p []]]).answer (query [call .p []])) == ["consistency"]

/-! ## Rules outside the relevant program -/

/- The query `p` with `p :- ¬s. s :- ¬p.` has two models. An unreached rule
`r :- p, ¬r` forces `p` false (`r ↔ p ∧ ¬r`): it reads a relevant atom under
NAF on a cycle, so the evaluator does not answer Unknown, and names the rule:
Undecided at its head, the two witnesses not shown to be models. -/
#guard kind ((program [rule .p [] [naf .s []], rule .s [] [naf .p []]]).answer (query [call .p []])) == "unknown"
#guard missing ((program [rule .p [] [naf .s []], rule .s [] [naf .p []], rule .r [] [call .p [], naf .r []]]).answer
  (query [call .p []])) == ["witnesses"]
#guard sites ((program [rule .p [] [naf .s []], rule .s [] [naf .p []], rule .r [] [call .p [], naf .r []]]).answer
  (query [call .p []])) == [some (.head 2)]

/- A rule outside that reads relevant atoms positively, or under NAF with no
cycle in the predicate graph, keeps the witnesses: `t :- p, ¬q.` outside:
Unknown. -/
#guard kind ((program [rule .p [] [naf .s []], rule .s [] [naf .p []], rule .t [] [call .p [], naf .q []]]).answer
  (query [call .p []])) == "unknown"

/- The check names a rule on the cycle, not one that only reads it: with
`t :- r.` reading the cycle `r :- p, ¬r`, the blocker sits at the head of
`r :- p, ¬r`. -/
#guard sites ((program [rule .p [] [naf .s []], rule .s [] [naf .p []], rule .t [] [call .r []],
    rule .r [] [call .p [], naf .r []]]).answer (query [call .p []])) == [some (.head 3)]

/- A rule with a ground head and names only in its body is computed when its
head is relevant: `p :- node(X), ¬q. q :- node(Y), ¬p.` answers Unknown, as
`p :- ¬q. q :- ¬p.` does. -/
#guard kind ((program [rule .p [] [guard .node 0, naf .q []], rule .q [] [guard .node 1, naf .p []]]).answer
  (query [call .p []])) == "unknown"

/- Yes and No need no extension: with the same unreached rule, `p :- ¬s. s.`
answers No. -/
#guard kind ((program [rule .p [] [naf .s []], fact .s [], rule .r [] [call .p [], naf .r []]]).answer
  (query [call .p []])) == "no"

/-! ## The KB-level check, beside the queries -/

/- An unrelated `t :- ¬t.`: the KB has no model. The ground rules on NAF
cycles get a relevant program of their own, checked once per KB: every query
answers Undecided, the KB's consistency. -/
#guard missing ((program [fact .p [], rule .t [] [naf .t []]]).answer (query [call .p []])) == ["consistency"]

/- An unrelated consistent cycle `t :- ¬r. r :- ¬t.` passes the check: `p.`
answers Yes. It is outside `p :- q. q :- q.`'s relevant program and on a
cycle through NAF, so it still blocks Unknown, named at its first rule. -/
#guard kind ((program [fact .p [], rule .t [] [naf .r []], rule .r [] [naf .t []]]).answer (query [call .p []])) == "yes"
#guard missing ((program [rule .p [] [call .q []], rule .q [] [call .q []], rule .t [] [naf .r []], rule .r [] [naf .t []]]).answer
  (query [call .p []])) == ["witnesses"]
#guard sites ((program [rule .p [] [call .q []], rule .q [] [call .q []], rule .t [] [naf .r []], rule .r [] [naf .t []]]).answer
  (query [call .p []])) == [some (.head 2)]

/- A root whose own query is not P1 does not switch the check off: with
`t :- ¬r, q(zero). r :- ¬t. q(X) :- allData(X), q(succ(X)).` beside
`s :- ¬s.`, the joint KB-level query is P2, and each root is checked on its
own: `s` alone has no model. -/
open Tabled.Mode in
def mixedDeclarations : List (Predicate Sym) :=
  [⟨.p, [], .defined⟩, ⟨.s, [], .defined⟩, ⟨.t, [], .defined⟩, ⟨.r, [], .defined⟩, ⟨.q, [input], .defined⟩,
   ⟨.allData, [input], .guard⟩]

#guard missing ((program [fact .p [], rule .s [] [naf .s []], rule .t [] [naf .r [], call .q [k .zero]], rule .r [] [naf .t []],
    rule .q [v 0] [guard .allData 0, call .q [.app .succ [v 0]]]] [] mixedDeclarations).answer (query [call .p []])) ==
  ["consistency"]

/- The check names the piece with no model, not unrelated atoms: with the
consistent cycle `t :- ¬r. r :- ¬t.` beside `p. ⊥ :- p.`, the blocker names
`p`. -/
#guard (match (program [fact .p [], rule .t [] [naf .r []], rule .r [] [naf .t []]] [[call .p []]]).answer (query [call .p []]) with
  | .undecided [blocker] => match blocker.missing with
    | .consistency atoms => atoms == [.app .p []]
    | _ => false
  | _ => false)

/-! ## Non-ground NAF and an open predicate -/

/-- `q(X) :- node(X), unknown(X)` (`q` opened by its marker case) and
`p(X) :- node(X), naf q(X)`. -/
def openRules : List (Rule Nat Nat Sym) :=
  [rule .q [v 0] [guard .node 0, .marker .m [v 0]], rule .p [v 0] [guard .node 0, naf .q [v 0]]]

def openProgram : Program Nat Nat Sym := program openRules [] unaryDeclarations

/- `p(a)`: true when the marker atom `unknown(a)` is false, false when it is
true: Unknown. The rules' other instances (`p(b)`, `q(c)`) are outside the
relevant program and stratified (`naf q` below `p`). -/
#guard kind (openProgram.answer (query [call .p [k .a]])) == "unknown"
#guard kind (openProgram.answer (query [call .q [k .a]])) == "unknown"

/- An atom no rule concludes: `r(a)` fails in every model: No; its NAF holds
in every model: Yes. -/
#guard kind (openProgram.answer (query [call .r [k .a]])) == "no"
#guard kind (openProgram.answer (query [naf .r [k .a]])) == "yes"

/-! ## Conditions -/

/- Under the condition `q`, with `p :- q.` and `q :- q`: Yes; under `¬q`: No.
A condition no model satisfies (`r`, with no rule for `r`) makes both Yes and
No true: the evaluator answers Yes. -/
#guard kind ((program [rule .p [] [call .q []], rule .q [] [call .q []]]).answer
  (query [call .p []] [] [call .q []])) == "yes"
#guard kind ((program [rule .p [] [call .q []], rule .q [] [call .q []]]).answer
  (query [call .p []] [] [naf .q []])) == "no"
#guard kind ((program [rule .p [] [call .q []], rule .q [] [call .q []]]).answer
  (query [call .p []] [] [call .r []])) == "yes"

/-! ## Rigid parameters, split by a finite guard -/

/- `path(x, y)` with the parameter `x` guarded by `item` (members `a`, `b`):
one ground query per member, combined as S27's `meaning_split` states. Over
the cycle, `path(x, a)` holds for both members: Yes; `path(x, c)` is open for
both: Unknown. Over the chain, `path(x, c)` holds for both: Yes; `path(x, a)`
fails for both: No. -/
#guard kind (cycle.answer (query [call .path [v 7, k .a]] [] [guard .item 7])) == "yes"
#guard kind (cycle.answer (query [call .path [v 7, k .c]] [] [guard .item 7])) == "unknown"
#guard kind (chain.answer (query [call .path [v 7, k .c]] [] [guard .item 7])) == "yes"
#guard kind (chain.answer (query [call .path [v 7, k .a]] [] [guard .item 7])) == "no"

/- Over `node` (`a`, `b`, `c`) on the chain, `path(x, c)` holds for `a` and
`b` and fails for `c`: the goal depends on the parameter: Unknown, with a
witness from each kind of instance. -/
#guard kind (chain.answer (query [call .path [v 7, k .c]] [] [guard .node 7])) == "unknown"
#guard (match chain.answer (query [call .path [v 7, k .c]] [] [guard .node 7]) with
  | .unknown holds fails => (holds.1, fails.1)
  | _ => (9, 9)) == (0, 2)

/- The witnesses come from instances whose rules outside are stratified,
whatever the members' order: `p(b) :- ¬s. s :- ¬p(b).` with `p(x)` under
`item(x)`: the instance `a` leaves the `b` cycle outside, the instance `b`
holds it; Unknown with the members `a, b` and with `b, a`. -/
open Tabled.Mode in
def splitDeclarations : List (Predicate Sym) :=
  [⟨.p, [input], .defined⟩, ⟨.s, [], .defined⟩, ⟨.item, [input], .guard⟩]

def splitProgram (order : List T) : Program Nat Nat Sym :=
  { program [rule .p [k .b] [naf .s []], rule .s [] [naf .p [k .b]]] [] splitDeclarations with
    members := fun | .item => some order | other => members other }

#guard kind ((splitProgram [k .a, k .b]).answer (query [call .p [v 7]] [] [guard .item 7])) == "unknown"
#guard kind ((splitProgram [k .b, k .a]).answer (query [call .p [v 7]] [] [guard .item 7])) == "unknown"

/- A parameter no finite guard splits: P2, Undecided before anything runs. -/
#guard missing (chain.answer (query [call .path [v 7, k .c]])) == ["termination"]

/-! ## Certificates and their checks -/

/-- An answer and its certificate's check. -/
def checks (program : Program Nat Nat Sym) (query : Query Nat Nat Sym) : Bool :=
  program.checkAnswer query (program.answer query)

/- Every certificate the evaluator gives checks: Yes and No by recomputing the
relevant programs, Unknown by its two witnesses, each a model. -/
#guard checks cycle (query [call .path [k .a, k .b]])
#guard checks chain (query [call .path [k .c, k .a]])
#guard checks cycle (query [call .path [k .a, k .c]])
#guard checks chain (query [call .path [v 7, k .c]] [] [guard .node 7])
#guard checks openProgram (query [call .p [k .a]])

/- A tampered Unknown: the witnesses swapped, the goal no longer holds in the
first; the first witness with `path(b, c)` dropped, no longer a model. Both
rejected. -/
#guard (match cycle.answer (query [call .path [k .a, k .c]]) with
  | .unknown holds fails => !cycle.checkUnknown (query [call .path [k .a, k .c]]) fails holds
  | _ => false)
#guard (match cycle.answer (query [call .path [k .a, k .c]]) with
  | .unknown holds fails =>
      !cycle.checkUnknown (query [call .path [k .a, k .c]]) (holds.1, (holds.2.1.erase (.path, [k .b, k .c]), holds.2.2)) fails
  | _ => false)

/-- The recomputed instances of a P0 or P1 query. -/
def recomputed (program : Program Nat Nat Sym) (query : Query Nat Nat Sym) : List (GroundProgram Nat Nat Sym) :=
  if decided : (program.classify query).decides = true then program.instances query decided else []

/- On an inconsistent KB neither a Yes nor a No certifies, recomputed
programs and all: `p :- ¬p.` -/
#guard !(program [rule .p [] [naf .p []]]).checkAnswer (query [call .p []])
  (.yes (recomputed (program [rule .p [] [naf .p []]]) (query [call .p []])))
#guard !(program [rule .p [] [naf .p []]]).checkAnswer (query [call .p []])
  (.no (recomputed (program [rule .p [] [naf .p []]]) (query [call .p []])))

/- A Yes with no program at all, for a No query: rejected by the comparison
with the recomputed programs. -/
#guard !chain.checkAnswer (query [call .path [k .c, k .a]]) (.yes [])

/- An Unknown witness padded with an atom outside its relevant program:
rejected. -/
#guard (match cycle.answer (query [call .path [k .a, k .c]]) with
  | .unknown holds fails =>
      !cycle.checkUnknown (query [call .path [k .a, k .c]]) (holds.1, ((.edge, [k .c, k .c]) :: holds.2.1, holds.2.2)) fails
  | _ => false)

/- A Yes certificate offered for a No, and one whose relevant program is not
the recomputed one: rejected. -/
#guard (match chain.answer (query [call .path [k .c, k .a]]) with
  | .no grounds => !chain.checkByPrograms (query [call .path [k .c, k .a]]) true grounds
  | _ => false)
#guard (match cycle.answer (query [call .path [k .a, k .b]]) with
  | .yes grounds => !cycle.checkByPrograms (query [call .path [k .a, k .b]]) true
      (grounds.map fun ground => { ground with goals := [] })
  | _ => false)

/-! ## Cost classes, before anything runs -/

/- `path` over the cycle reads nothing under NAF: polynomial, of degree 3, the
names of its recursive rule. `p :- ¬q. q :- ¬p.` reads `q` under NAF on a
cycle, and the open program reads `q`, whose rule has a marker: exponential.
`p(a) :- q(a), ¬r(a). q(a).` reads `r`, which reaches neither a cycle nor a
marker: polynomial. A P2 query is budgeted; one Undecided before anything
runs is blocked. -/
#guard cycle.cost (query [call .path [k .a, k .c]]) == .polynomial 3

/- A denial joins every query's relevant program, so its names count: the
query `p` with the denial `⊥ :- node(X), node(Y), edge(X, Y)` has degree 2. -/
#guard (program [fact .p [], fact .edge [k .a, k .b]] [[guard .node 0, guard .node 1, call .edge [v 0, v 1]]]).cost
  (query [call .p []]) == .polynomial 2
#guard (program [rule .p [] [naf .q []], rule .q [] [naf .p []]]).cost (query [call .p []]) == .exponential
#guard openProgram.cost (query [call .p [k .a]]) == .exponential
#guard (program [rule .p [k .a] [call .q [k .a], naf .r [k .a]], fact .q [k .a]] [] unaryDeclarations).cost
  (query [call .p [k .a]]) == .polynomial 0
#guard (program [rule .p [] [call .q []], rule .p [] [naf .q []], rule .q [] [call .q []]]).cost (query [call .p []]) == .exponential
#guard chain.cost (query [call .path [v 7, k .c]]) == .budgeted
#guard (program [rule .p [] [call .m []]]).cost (query [call .p []]) == .blocked

/-! ## Before anything runs -/

/- A growing call, `p(X) :- allData(X), p(succ(X))`: P2, Undecided before
anything runs, at the call. -/
#guard missing ((program [rule .p [v 0] [guard .allData 0, call .p [.app .succ [v 0]]]] [] unaryDeclarations).answer
  (query [call .p [k .zero]])) == ["termination"]

/- An undeclared predicate: Undecided, the checker's blocker. -/
#guard kind ((program [rule .p [] [call .m []]]).answer (query [call .p []])) == "undecided"

end IREvaluateTests
