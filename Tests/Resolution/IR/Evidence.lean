import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.IR AnthillModKbSpec.Answers
  AnthillModKbSpec.Admission AnthillModKbSpec.Completion

namespace IREvidenceTests

/-! Executable traces of S27: the decision IR's checker and its evidence
classes. Each `#guard` evaluates compiled code: the profile of an IR program
and query (P0, P1, P2 with its reasons, or Undecided with its blockers),
before anything runs. -/

inductive Sym where
  | path | edge | append | count | grow | dup | top | p | q | r
  | node | allData | item | isList
  | nil | cons | pair | zero | succ | a | b | c | ha
  deriving DecidableEq, Repr

abbrev T := Term Nat Nat Sym
abbrev G := Goal Nat Nat Sym

def k (symbol : Sym) : T := .app symbol []
def v (name : Nat) : T := .var name
def cons (head tail : T) : T := .app .cons [head, tail]
def succ (term : T) : T := .app .succ [term]
def pair (left right : T) : T := .app .pair [left, right]

def call (predicate : Sym) (args : List T) : G := .call predicate args
def guard (symbol : Sym) (name : Nat) : G := .guard symbol (v name)
def rule (head : Sym) (args : List T) (body : List G) : Rule Nat Nat Sym := ⟨head, args, body⟩
def fact (head : Sym) (args : List T) : Rule Nat Nat Sym := ⟨head, args, []⟩

open Tabled.Mode in
def declarations : List (Predicate Sym) :=
  [⟨.path, [input, output], .defined⟩, ⟨.edge, [input, output], .defined⟩,
   ⟨.append, [input, input, output], .defined⟩, ⟨.count, [input, output], .defined⟩,
   ⟨.grow, [input], .defined⟩, ⟨.dup, [input, output], .defined⟩, ⟨.top, [input, output], .defined⟩,
   ⟨.p, [input], .defined⟩, ⟨.q, [input], .defined⟩, ⟨.r, [input], .defined⟩,
   ⟨.node, [input], .guard⟩, ⟨.allData, [input], .guard⟩, ⟨.item, [input], .guard⟩, ⟨.isList, [input], .guard⟩]

def constructors : List (Constructor Nat Sym) :=
  [.application .nil 0, .application .cons 2, .application .pair 2, .application .zero 0,
   .application .succ 1, .application .a 0, .application .b 0, .application .c 0]

/-- `node` is a finite domain, its members listed; the other guards are not. -/
def members : Sym → Option (List T)
  | .node => some [k .a, k .b, k .c]
  | _ => none

def program (rules : List (Rule Nat Nat Sym)) (denials : List (List G) := []) : Program Nat Nat Sym :=
  ⟨declarations, constructors, rules, [], denials, fun _ _ => true, members, fun _ _ => none, .ha⟩

def query (goals : List G) (answers : List Nat := []) (conditions : List G := []) : Query Nat Nat Sym :=
  ⟨conditions, goals, answers⟩

def isP0 : Profile Nat Nat Sym → Bool
  | .p0 => true
  | _ => false

def isP1 : Profile Nat Nat Sym → Bool
  | .p1 => true
  | _ => false

def reasons : Profile Nat Nat Sym → List Program.Reason
  | .p2 notes => notes.map (·.reason)
  | _ => []

def undecided : Profile Nat Nat Sym → Bool
  | .undecided _ => true
  | _ => false

/-! ## `path` over a cycle: a ground query P1, `∃Y. path(a, Y)` P2 -/

/-- `edge(a, b). edge(b, a).` and `path` with every name guarded:
`path(X, Y) :- node(X), edge(X, Y), node(Y).`
`path(X, Y) :- node(X), edge(X, Z), node(Z), path(Z, Y), node(Y).` -/
def pathRules (guardSymbol : Sym) : List (Rule Nat Nat Sym) :=
  [fact .edge [k .a, k .b], fact .edge [k .b, k .a],
   rule .path [v 0, v 1] [guard guardSymbol 0, call .edge [v 0, v 1], guard guardSymbol 1],
   rule .path [v 0, v 1]
     [guard guardSymbol 0, call .edge [v 0, v 2], guard guardSymbol 2, call .path [v 2, v 1], guard guardSymbol 1]]

def pathProgram : Program Nat Nat Sym := program (pathRules .node)

/- `path(a, c)`: both arguments bound, every call inside `path`'s component
has data-term arguments. -/
#guard isP1 (pathProgram.classify (query [call .path [k .a, k .c]]))

/- The vertices: `path` with both arguments bound, `edge` called with both
bound and with its output free. -/
#guard (pathProgram.vertices (query [call .path [k .a, k .c]])).length == 3
#guard pathProgram.closed (query [call .path [k .a, k .c]])
#guard pathProgram.levels (query [call .path [k .a, k .c]]) (.path, [true, true]) == 2

/- `∃Y. path(a, Y)`: the recursive call leaves `Y` free at its caller's level
and does not decrease; P2, naming that call. -/
#guard reasons (pathProgram.classify (query [call .path [k .a, v 1], guard .node 1] [1])) == [.freeOutput]

/- The lowered program, its guards over `D_all` (an infinite domain, decided
on bound names): P1 for the ground query too. -/
#guard isP1 ((program (pathRules .allData)).classify (query [call .path [k .a, k .c]]))

/-! ## `append(+, +, −)`: P1, decreasing -/

def appendRules : List (Rule Nat Nat Sym) :=
  [rule .append [k .nil, v 0, v 0] [guard .isList 0],
   rule .append [cons (v 1) (v 2), v 0, cons (v 1) (v 3)]
     [guard .item 1, guard .isList 2, guard .isList 0, call .append [v 2, v 0, v 3], guard .isList 3]]

def appendQuery : Query Nat Nat Sym :=
  query [call .append [cons (k .a) (k .nil), cons (k .b) (k .nil), v 4], guard .isList 4] [4]

#guard isP1 ((program appendRules).classify appendQuery)
#guard (program appendRules).levels appendQuery (.append, [true, true, false]) == 0

/-! ## Self-supporting cycles with a free output: P2 -/

/-- `count(X, zero) :- node(X). count(X, succ(Y)) :- node(X), count(X, Y), allData(Y).`
with mode (+, −): with its output free it makes one call and holds of
unboundedly many outputs. -/
def countRules : List (Rule Nat Nat Sym) :=
  [rule .count [v 0, k .zero] [guard .node 0],
   rule .count [v 0, succ (v 1)] [guard .node 0, call .count [v 0, v 1], guard .allData 1]]

#guard reasons ((program countRules).classify (query [call .count [k .a, v 1], guard .allData 1] [1])) == [.freeOutput]

/- The same predicate with its output bound is P1: `count(a, succ(zero))`. -/
#guard isP1 ((program countRules).classify (query [call .count [k .a, succ (k .zero)]]))

/- `grow(X) :- allData(X), grow(succ(X))`: a growing call. -/
#guard reasons ((program [rule .grow [v 0] [guard .allData 0, call .grow [succ (v 0)]]]).classify
  (query [call .grow [k .zero]])) == [.growingCall]

/-! ## Across components: constructed inputs and term growth by the bodies -/

/- `p(X) :- node(X), q(succ(X)). q(Y) :- allData(Y).`: the body constructs
the input of a lower component. P1. -/
#guard isP1 ((program [rule .p [v 0] [guard .node 0, call .q [succ (v 0)]], rule .q [v 0] [guard .allData 0]]).classify
  (query [call .p [k .a]]))

/-- `dup(X, Y) :- allData(X), Y = pair(X, X), allData(Y)` called thirteen
times in a row: each call has one answer; the bound is by the bodies. P1. -/
def dupChain : Rule Nat Nat Sym :=
  rule .top [v 0, v 13] ((guard .allData 0 :: (List.range 13).map fun i => call .dup [v i, v (i + 1)]) ++
    (List.range 13).map fun i => guard .allData (i + 1))

#guard isP1 ((program [rule .dup [v 0, v 1] [guard .allData 0, .equal (v 1) (pair (v 0) (v 0)), guard .allData 1],
    dupChain]).classify (query [call .top [k .a, v 20], guard .allData 20] [20]))

/-! ## Guards and parameters -/

/- An unguarded name ranges over the carrier: P2. -/
#guard reasons ((program [rule .q [v 0] [call .r [v 0]], rule .r [v 0] [guard .allData 0]]).classify
  (query [call .q [k .a]])) == [.unguarded]

/- A rigid parameter `x`: P2 unless a finite guard among the conditions
splits it; split, the query is P1 when each of its three instances,
`path(a, c)`, `path(b, c)`, `path(c, c)`, is. -/
#guard reasons (pathProgram.classify (query [call .path [v 7, k .c]])) == [.parameter]
#guard isP1 (pathProgram.classify (query [call .path [v 7, k .c]] [] [guard .node 7]))
#guard (pathProgram.splitValues (query [call .path [v 7, k .c]] [] [guard .node 7])).length == 3
#guard ((pathProgram.splitValues (query [call .path [v 7, k .c]] [] [guard .node 7])).map fun values =>
    isP1 (pathProgram.classifyClosed ((query [call .path [v 7, k .c]] [] [guard .node 7]).instantiate values))).all id

/- An instance of the split that is not P1 makes the query P2: with a free
output on the cycle, each instance `∃Y. path(x, Y)` is P2. -/
#guard reasons (pathProgram.classify (query [call .path [v 7, v 1], guard .node 1] [1] [guard .node 7])) ==
  [.freeOutput, .freeOutput, .freeOutput]

/- Guarded by an infinite domain, the parameter cannot be split. -/
#guard reasons (pathProgram.classify (query [call .path [v 7, k .c]] [] [guard .allData 7])) == [.parameter]

/-! ## P0 and blockers -/

/- `p(a) :- q(a), naf r(a). q(a).`, the query `p(a)`: ground and acyclic. -/
#guard isP0 ((program [rule .p [k .a] [call .q [k .a], .naf .r [k .a]], fact .q [k .a]]).classify
  (query [call .p [k .a]]))

/- A ground cycle is not P0: `p(a) :- q(a). q(a) :- p(a).` S07 ranks atoms:
`p(a) :- p(b). p(b).` is acyclic, P0, though `p` calls itself. -/
#guard isP1 ((program [rule .p [k .a] [call .q [k .a]], rule .q [k .a] [call .p [k .a]]]).classify
  (query [call .p [k .a]]))
#guard isP0 ((program [rule .p [k .a] [call .p [k .b]], fact .p [k .b]]).classify (query [call .p [k .a]]))

/- S07's ground fragment has no denials and no equations: `q(a). ⊥ :- q(a).`
and `p(a) :- a = a.` are P1, not P0. -/
#guard isP1 ((program [fact .q [k .a]] [[call .q [k .a]]]).classify (query [call .q [k .a]]))
#guard isP1 ((program [rule .p [k .a] [.equal (k .a) (k .a)]]).classify (query [call .p [k .a]]))

/-! ## Denials join the graph -/

/- `p(a) :- naf q(a). q(a) :- naf p(a). ⊥ :- p(a).`, the query `p(a)`: the
denial's call `p(a)` is a vertex of the query's graph, decided with it. -/
#guard isP1 ((program [rule .p [k .a] [.naf .q [k .a]], rule .q [k .a] [.naf .p [k .a]]] [[call .p [k .a]]]).classify
  (query [call .p [k .a]]))
#guard ((program [rule .p [k .a] [.naf .q [k .a]], rule .q [k .a] [.naf .p [k .a]]] [[call .q [k .a]]]).vertices
  (query [call .p [k .a]])).length == 2

/- A denial without the finiteness evidence makes the query P2: `⊥ :- path(a, Y),
node(Y)` leaves `Y` free on the cycle, so even `path(a, c)` is P2. -/
#guard reasons ((program (pathRules .node) [[call .path [k .a, v 1], guard .node 1]]).classify
  (query [call .path [k .a, k .c]])) == [.freeOutput]

/- An input unbound: `∃X. path(X, c)` with mode (+, −). -/
#guard undecided (pathProgram.classify (query [call .path [v 1, k .c], guard .node 1] [1]))

/- A guard over an infinite domain cannot bind its name. -/
#guard undecided ((program [rule .q [v 0] [guard .allData 1, call .path [v 0, v 1], guard .allData 0]]).classify
  (query [call .q [k .a]]))

/- Over a finite domain it binds: in `q(X) :- node(X), node(Y), path(Y, X)`,
with `q` at mode (+), `node(Y)` enumerates `Y`. -/
#guard !undecided ((program (pathRules .node ++ [rule .q [v 0] [guard .node 0, guard .node 1, call .path [v 1, v 0]]])).classify
  (query [call .q [k .a]]))

/- An undeclared predicate, a non-data argument (a formula inside data), a
predicate declared twice, a predicate named by the reserved `ho_apply`. -/
#guard undecided ((program [rule .q [v 0] [guard .allData 0, call .nil [v 0]]]).classify
  (query [call .q [k .a]]))
#guard undecided ((program [fact .q [.truth]]).classify (query [call .q [k .a]]))
#guard undecided ({ program [] with predicates := declarations ++ [(⟨.q, [.input], .guard⟩ : Predicate Sym)] }.classify
  (query [call .p [k .a]]))
#guard undecided ({ program [] with hoApply := .q }.classify (query [call .p [k .a]]))

attribute [local instance] AnthillModKbSpec.Machine.termEq

/-- The blockers' sites, paths, and formulas. -/
def blockersOf : Profile Nat Nat Sym → List (Option Site × List Nat × Term Nat Nat Sym)
  | .undecided blockers => blockers.map fun blocker =>
      match blocker.place with
      | .site site => (some site, blocker.path, blocker.formula)
      | .reached _ _ => (none, blocker.path, blocker.formula)
  | _ => []

/- A duplicated symbol is named; a goal is reported at its position; a
defined operation inside data at its argument's path. -/
#guard blockersOf ({ program [] with predicates := declarations ++ [(⟨.q, [.input], .guard⟩ : Predicate Sym)] }.classify
  (query [call .p [k .a]])) == [(some .goal, [], k .q)]
#guard blockersOf (pathProgram.classify (query [call .path [k .a, k .c], call .path [v 1, k .c], guard .node 1] [1])) ==
  [(some .goal, [1], .app .path [v 1, k .c])]
#guard blockersOf ((program [rule .q [v 0] [guard .allData 0, call .r [.app .grow [v 0]]], rule .r [v 0] [guard .allData 0]]).classify
  (query [call .q [k .a]])) == [(some (.body 0 1), [0], .app .grow [v 0])]

/- A finite guard's listed member must be a ground data term. -/
#guard undecided ({ program [] with members := fun | .node => some [v 3] | _ => none }.classify (query [call .p [k .a]]))

end IREvidenceTests
