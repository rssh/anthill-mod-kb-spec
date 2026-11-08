import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Tabled AnthillModKbSpec.Machine AnthillModKbSpec.Completion
  AnthillModKbSpec.Answers AnthillModKbSpec.AdmissionSignature AnthillModKbSpec.InductiveDomains

namespace TabledEvaluationTests

/-! Executable traces of S24: tabled backtracking on the shared machine and the
fast fragment's answers over the completion. Each `#guard` evaluates compiled
code: a Yes is a run's proof exported as an S08 term and checked, a No a
refutation over the universe, an Unknown two witnesses that check, and an
Undecided its blockers. -/

attribute [local instance] termEq

inductive Sym where
  | path | edge | a | b | c | d | p | q | r | s | t | u | succ | zero
  | top | left | right | mid | ha | tab | unknown
  | isUnit | allData | isPred (arity : Nat) | tag (tag : P1.Tag)
  deriving DecidableEq, Repr

def vocab : P1.Vocabulary Sym := ⟨Sym.tag, fun _ _ same => by cases same; rfl⟩

abbrev T := Term Nat Nat Sym
abbrev Clause := HornClause Nat Nat Sym

def k (symbol : Sym) : T := .app symbol []
def atom (symbol : Sym) (args : List T) : T := .app symbol args
def v (name : Nat) : T := .var name
def fact (head : T) : Clause := .definite head []
def rule (head : T) (body : List T) : Clause := .definite head body
def naf (goal : T) : T := .defaultNeg goal
def succ (term : T) : T := atom .succ [term]

/-- The admission signature: one domain without constructors, no registered
predicate; its guard symbols have one role each. -/
def family : FiniteFamily Unit Sym := ⟨fun _ => False, [()], fun domain => by cases domain; simp⟩
def admission : SignatureSnapshot Unit Sym := ⟨0, ⟨family, fun _ => .isUnit, .allData, .isPred, []⟩⟩

def isGuard : Sym → Bool
  | .isUnit | .allData | .isPred _ => true
  | _ => false

theorem isGuard_iff (symbol : Sym) : isGuard symbol = true ↔ Open.IsGuard admission.naming symbol := by
  cases symbol <;> simp [isGuard, Open.IsGuard, admission, SignatureSnapshot.naming, Signature.naming]

theorem separated : Open.Separated admission.naming Sym.ha where
  membership _ _ _ := rfl
  predicate _ _ same := by cases same; rfl
  dataMembership _ same := by cases same
  predicateMembership _ _ same := by cases same
  predicateData _ same := by cases same
  hoApply := by simp [Open.IsGuard, admission, SignatureSnapshot.naming, Signature.naming]

def unknownMarker (symbol : Sym) : Bool := symbol == .unknown

theorem markers : ∀ symbol, unknownMarker symbol = true → isGuard symbol = false := by
  intro symbol marker; cases symbol <;> simp_all [unknownMarker, isGuard]

/-- The declared free constructors. -/
def free : Sym → Nat → Bool
  | .a, 0 | .b, 0 | .c, 0 | .d, 0 | .zero, 0 | .succ, 1 => true
  | _, _ => false

open Mode in
/-- The mode declarations. -/
def modes : Modes Sym
  | .path | .edge => some [input, output]
  | .p | .q | .r | .s | .t | .u => some [input]
  | .top | .left | .right => some []
  | .mid => some [input]
  | _ => none

open Mode in
/-- Propositional predicates. -/
def nullary : Modes Sym
  | .p | .q | .r | .s => some []
  | _ => none

def fragmentOf (clauses : List Clause) (declared : Modes Sym) : Tabled.Program Nat Nat Sym :=
  ⟨clauses.zipIdx.map fun (clause, index) => (index, clause), free, isGuard, unknownMarker, .ha, declared⟩

def setupOf (clauses : List Clause) (goal : T) (declared : Modes Sym := modes) : Tabled.Setup Unit Nat Nat Sym :=
  Tabled.Setup.ofProgram vocab (fragmentOf clauses declared) admission isGuard isGuard_iff separated markers
    (fun symbol => free symbol 0 || free symbol 1) [goal] .tab

def answerOf (clauses : List Clause) (goal : T) (answers : List Nat := []) (fuel : Nat := 3000)
    (declared : Modes Sym := modes) : TabledAnswer Nat Nat Sym :=
  (setupOf clauses goal declared).answer fuel ⟨[], goal, answers⟩

def kindOf : TabledAnswer Nat Nat Sym → String
  | .yes _ => "yes"
  | .no _ => "no"
  | .unknown _ _ => "unknown"
  | .undecided _ => "undecided"

def witnessKinds : TabledAnswer Nat Nat Sym → List String
  | .unknown holds fails => [holds, fails].map fun
      | .greatest _ => "greatest"
      | .least _ => "least"
      | .assignment _ => "assignment"
  | _ => []

def missingKinds : TabledAnswer Nat Nat Sym → List String
  | .undecided blockers => blockers.map fun blocker => match blocker.missing with
      | .proof => "proof" | .mode => "mode" | .termination => "termination"
      | .construct _ => "construct" | .witnesses _ => "witnesses" | .consistency _ => "consistency"
  | _ => []

/-- The formulas an Undecided answer's blockers name. -/
def blockerFormulas : TabledAnswer Nat Nat Sym → List T
  | .undecided blockers => blockers.map (·.formula)
  | _ => []

/-! ## Path over a graph -/

def rightRecursive : List Clause :=
  [rule (atom .path [v 0, v 1]) [atom .edge [v 0, v 1]],
   rule (atom .path [v 0, v 1]) [atom .edge [v 0, v 2], atom .path [v 2, v 1]]]

def leftRecursive : List Clause :=
  [rule (atom .path [v 0, v 1]) [atom .path [v 0, v 2], atom .edge [v 2, v 1]],
   rule (atom .path [v 0, v 1]) [atom .edge [v 0, v 1]]]

/-- A cycle `a ↔ b`; `c` is unreachable. -/
def cyclic : List Clause := [fact (atom .edge [k .a, k .b]), fact (atom .edge [k .b, k .a])]

/-- `a → b → c`. -/
def acyclic : List Clause := [fact (atom .edge [k .a, k .b]), fact (atom .edge [k .b, k .c])]

-- Over the cycle: `path(a, b)` is Yes, its proof exported and checked.
#guard kindOf (answerOf (cyclic ++ rightRecursive) (atom .path [k .a, k .b])) == "yes"
-- `path(a, c)` is Unknown: the cycle supports it in the greatest fixpoint, not
-- in the least, the two fixpoints its witnesses.
#guard kindOf (answerOf (cyclic ++ rightRecursive) (atom .path [k .a, k .c])) == "unknown"
#guard witnessKinds (answerOf (cyclic ++ rightRecursive) (atom .path [k .a, k .c])) == ["greatest", "least"]
-- Over the acyclic graph: `path(a, c)` is Yes, `path(a, d)` No, its failure
-- passing no cycle.
#guard kindOf (answerOf (acyclic ++ rightRecursive) (atom .path [k .a, k .c])) == "yes"
#guard kindOf (answerOf (acyclic ++ rightRecursive) (atom .path [k .a, k .d])) == "no"
-- An answer name: `∃Y. path(a, Y)` is Yes.
#guard kindOf (answerOf (cyclic ++ rightRecursive) (atom .path [k .a, v 7]) [7]) == "yes"

-- Left recursion terminates: the recursive call waits on its own table.
#guard kindOf (answerOf (cyclic ++ leftRecursive) (atom .path [k .a, k .a])) == "yes"
#guard kindOf (answerOf (acyclic ++ leftRecursive) (atom .path [k .a, k .c])) == "yes"
-- Over the cycle, `path(a, c)` fails at `edge(Z, c)` for every `Z`: No, though
-- the call `path(a, Z)` is on a cycle.
#guard kindOf (answerOf (cyclic ++ leftRecursive) (atom .path [k .a, k .c])) == "no"

/-! ## Each distinct call is evaluated once -/

def engineOf (clauses : List Clause) (goal : T) : Engine Nat Nat Sym :=
  (setupOf clauses goal).engine ((setupOf clauses goal).space [] goal)

def tablesOf (clauses : List Clause) (goal : T) : List (Sym × List T × Nat) :=
  match (engineOf clauses goal).run 3000 (Engine.start [] goal) with
  | .success _ resume => resume.tables.map fun table => (table.call.predicate, table.call.inputs, table.answers.length)
  | .interrupted run => run.tables.map fun table => (table.call.predicate, table.call.inputs, table.answers.length)
  | .finished _ => []

/-- `top :- left, right.  left :- mid(a).  right :- mid(a).  mid(a).`: the call
`mid(a)` is reached twice and has one table. -/
def diamond : List Clause :=
  [rule (k .top) [k .left, k .right], rule (k .left) [atom .mid [k .a]], rule (k .right) [atom .mid [k .a]],
   fact (atom .mid [k .a])]

#guard (tablesOf diamond (k .top)).map (·.1) == [.top, .left, .mid, .right]
#guard kindOf (answerOf diamond (k .top)) == "yes"

-- `∃Y. path(a, Y)` over the cycle: one table per call, `path(a)` with both answers.
#guard tablesOf (cyclic ++ rightRecursive) (.existsVar 7 (atom .path [k .a, v 7])) ==
  [(.path, [k .a], 2), (.edge, [k .a], 1), (.path, [k .b], 2), (.edge, [k .b], 1)]

/-! ## Loops through NAF -/

-- `p :- ¬q.  q :- ¬p.`: Unknown, the two ground fixpoints `{p}` and `{q}` its witnesses.
#guard kindOf (answerOf [rule (k .p) [naf (k .q)], rule (k .q) [naf (k .p)]] (k .p) (declared := nullary)) == "unknown"
#guard witnessKinds (answerOf [rule (k .p) [naf (k .q)], rule (k .q) [naf (k .p)]] (k .p) (declared := nullary)) ==
  ["assignment", "assignment"]
-- `p :- ¬p.`: no assignment is a fixpoint; the completion is inconsistent: Undecided.
#guard missingKinds (answerOf [rule (k .p) [naf (k .p)]] (k .p) (declared := nullary)) == ["consistency"]
-- NAF with evidence: `p :- ¬q` with no clause for `q` is Yes, the refutation of
-- `q` checked again by S08; with the fact `q` it is No.
#guard kindOf (answerOf [rule (k .p) [naf (k .q)]] (k .p) (declared := nullary)) == "yes"
#guard kindOf (answerOf [rule (k .p) [naf (k .q)], fact (k .q)] (k .p) (declared := nullary)) == "no"

/-! ## Growing calls and fuel -/

/-- `p(X) :- p(succ(X))`: every call is new. -/
def grow : List Clause := [rule (atom .p [v 0]) [atom .p [succ (v 0)]]]

-- Undecided by fuel, lacking a termination argument, naming the growing call.
#guard missingKinds (answerOf grow (atom .p [k .zero]) (fuel := 300)) == ["termination"]
#guard (blockerFormulas (answerOf grow (atom .p [k .zero]) (fuel := 300))).any fun formula =>
  match formula with
  | .app .p [.app .succ _] => true
  | _ => false

/-- A query's profile. -/
def profileKind (clauses : List Clause) (goal : T) (answers : List Nat := []) (declared : Modes Sym := modes) : String :=
  match (fragmentOf clauses declared).admit ⟨[], goal, answers⟩ with
  | .undecided _ => "undecided"
  | .p1 => "p1"
  | .p2 _ => "p2"

-- A P1 query needs no fuel: its run is bounded and ends, the same answer with
-- no fuel and with plenty.
#guard profileKind (cyclic ++ rightRecursive) (atom .path [k .a, k .b]) == "p1"
#guard kindOf (answerOf (cyclic ++ rightRecursive) (atom .path [k .a, k .b]) (fuel := 0)) == "yes"
#guard kindOf (answerOf (cyclic ++ rightRecursive) (atom .path [k .a, k .b]) (fuel := 9000)) == "yes"

/-- `p :- ¬q.  q :- ¬p.`: NAF through a cycle, P2. -/
def loopNaf : List Clause := [rule (k .p) [naf (k .q)], rule (k .q) [naf (k .p)]]

-- A P2 query is bounded by the fuel, and monotone in it: too little fuel is
-- Undecided, a decided answer stays.
#guard profileKind loopNaf (k .p) (declared := nullary) == "p2"
#guard kindOf (answerOf loopNaf (k .p) (fuel := 5) (declared := nullary)) == "undecided"
#guard kindOf (answerOf loopNaf (k .p) (fuel := 300) (declared := nullary)) == "unknown"
#guard kindOf (answerOf loopNaf (k .p) (fuel := 9000) (declared := nullary)) == "unknown"

/-! ## Bounded runs end without fuel -/

/-- The outcome of a query's bounded run. -/
def decidedKind (clauses : List Clause) (goal : T) : String :=
  match (setupOf clauses goal).decided [] goal with
  | .success _ _ => "success"
  | .interrupted _ => "interrupted"
  | .finished .exhausted => "exhausted"
  | .finished (.opened _) => "opened"
  | .finished (.abandoned _) => "abandoned"
  | .finished _ => "finished"

/-- The tables a bounded run opens, and the calls its bounds allow. -/
def decidedTables (clauses : List Clause) (goal : T) : Nat :=
  match (setupOf clauses goal).decided [] goal with
  | .success _ resume => resume.tables.length
  | _ => 0

def boundCalls (clauses : List Clause) (goal : T) : Nat := ((setupOf clauses goal).bounds [] goal).calls.length

-- A bounded run ends for any program: the growing call `p(succ(…))` leaves the
-- bounds and is abandoned, where the fuelled run is interrupted.
#guard decidedKind grow (atom .p [k .zero]) == "abandoned"
-- `∃Y. path(a, Y)` opens four tables, among the bounds' calls.
#guard decidedTables (cyclic ++ rightRecursive) (.existsVar 7 (atom .path [k .a, v 7])) == 4
#guard decidedTables (cyclic ++ rightRecursive) (.existsVar 7 (atom .path [k .a, v 7])) ≤
  boundCalls (cyclic ++ rightRecursive) (.existsVar 7 (atom .path [k .a, v 7]))

/-! ## Rigid parameters -/

-- `path(X, c)` with `X` a rigid parameter of the query: its call is tabled, so
-- left recursion over the cycle ends (plain SLD on it looped): No, since
-- `edge(Z, c)` holds for no `Z`.
#guard profileKind (cyclic ++ leftRecursive) (atom .path [v 9, k .c]) == "p1"
#guard decidedKind (cyclic ++ leftRecursive) (atom .path [v 9, k .c]) == "exhausted"
#guard kindOf (answerOf (cyclic ++ leftRecursive) (atom .path [v 9, k .c])) == "no"
-- `path(X, a)` neither holds for every `X` nor is refuted, and witnesses with
-- parameters are S26's: Undecided, after a run that ended.
#guard decidedKind (cyclic ++ leftRecursive) (atom .path [v 9, k .a]) == "exhausted"
#guard kindOf (answerOf (cyclic ++ leftRecursive) (atom .path [v 9, k .a])) == "undecided"

/-! ## Open predicates, the fresh value, denials, admission -/

-- `q(a) :- unknown`: Unknown, the marker false in the least fixpoint and true in
-- the greatest, with no refutation run; `¬q(a)` is Unknown too.
#guard kindOf (answerOf [rule (atom .q [k .a]) [k .unknown]] (atom .q [k .a])) == "unknown"
#guard kindOf (answerOf [rule (atom .q [k .a]) [k .unknown]] (naf (atom .q [k .a]))) == "unknown"

open Mode in
def freshModes : Modes Sym
  | .r | .q => some [output]
  | .p => some [input]
  | .s => some []
  | _ => none

/-- `r(X) :- r(X).  q(X) :- r(X).  p(X).  s :- q(Y), p(Y).`: over no data term
the greatest fixpoint gives `r` nothing; the fresh value supports `s`. -/
def freshKb : List Clause :=
  [rule (atom .r [v 0]) [atom .r [v 0]], rule (atom .q [v 0]) [atom .r [v 0]], fact (atom .p [v 0]),
   rule (k .s) [atom .q [v 1], atom .p [v 1]]]

#guard kindOf (answerOf freshKb (k .s) (declared := freshModes)) == "unknown"

-- A denial whose body is proved makes every answer Undecided.
#guard missingKinds (answerOf [fact (k .p), .goal [k .p], fact (k .q)] (k .q) (declared := nullary)) == ["consistency"]
-- A denial whose body fails constrains nothing.
#guard kindOf (answerOf [fact (k .q), .goal [k .p]] (k .q) (declared := nullary)) == "yes"

-- A predicate without a mode is Undecided before anything runs: the goal and
-- the clause each lack a mode.
#guard missingKinds (answerOf [fact (atom .d [k .a])] (atom .d [k .a])) == ["mode", "mode"]

end TabledEvaluationTests
