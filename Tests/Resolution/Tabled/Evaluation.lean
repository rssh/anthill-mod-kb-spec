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
    (fun symbol => free symbol 0 || free symbol 1) [goal] .tab id [] (by simp)

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

/-- What each blocker lacks. -/
def blockerKinds (blockers : List (Blocker Nat Nat Sym)) : List String :=
  blockers.map fun blocker => match blocker.missing with
    | .proof => "proof" | .mode => "mode" | .termination => "termination"
    | .construct _ => "construct" | .witnesses _ => "witnesses" | .consistency _ => "consistency"

def missingKinds : TabledAnswer Nat Nat Sym → List String
  | .undecided blockers => blockerKinds blockers
  | _ => []

/-- The formulas an Undecided answer's blockers name. -/
def blockerFormulas : TabledAnswer Nat Nat Sym → List T
  | .undecided blockers => blockers.map (·.formula)
  | _ => []

/-- A signature with one domain of nodes `a`, `b`, `c`: its guards `isUnit`
and `allData` hold of them. -/
def nodeRules : List (InductiveDomains.Rule Unit Sym) := [⟨(), .a, []⟩, ⟨(), .b, []⟩, ⟨(), .c, []⟩]
def nodes : FiniteFamily Unit Sym := ⟨fun rule => rule ∈ nodeRules, [()], fun domain => by cases domain; simp⟩
def guarded : SignatureSnapshot Unit Sym := ⟨0, ⟨nodes, fun _ => .isUnit, .allData, .isPred, []⟩⟩

theorem guarded_isGuard_iff (symbol : Sym) : isGuard symbol = true ↔ Open.IsGuard guarded.naming symbol := by
  cases symbol <;> simp [isGuard, Open.IsGuard, guarded, SignatureSnapshot.naming, Signature.naming]

theorem guarded_separated : Open.Separated guarded.naming Sym.ha where
  membership _ _ _ := rfl
  predicate _ _ same := by cases same; rfl
  dataMembership _ same := by cases same
  predicateMembership _ _ same := by cases same
  predicateData _ same := by cases same
  hoApply := by simp [Open.IsGuard, guarded, SignatureSnapshot.naming, Signature.naming]

def guardedSetupOf (clauses : List Clause) (goal : T) : Tabled.Setup Unit Nat Nat Sym :=
  Tabled.Setup.ofProgram vocab (fragmentOf clauses modes) guarded isGuard guarded_isGuard_iff guarded_separated markers
    (fun symbol => free symbol 0 || free symbol 1) [goal] .tab id nodeRules (fun _ member => member)

def guardedAnswerOf (clauses : List Clause) (goal : T) : TabledAnswer Nat Nat Sym :=
  (guardedSetupOf clauses goal).answer 3000 ⟨[], goal, []⟩

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

/-- A query's bounded run with its data terms cut at `size` nodes: the setup's
own limit is generous, so that a P1 run never meets it; a growing program
reaches any limit, and these traces use a small one. -/
def smallRun (clauses : List Clause) (goal : T) (size : Nat) (declared : Modes Sym := modes) : Engine.Outcome Nat Nat Sym :=
  let setup := setupOf clauses goal declared
  let engine : Engine Nat Nat Sym := { setup.engine (setup.space [] goal) with bounds := some { setup.bounds [] goal with size } }
  engine.runToEnd (bounds := { setup.bounds [] goal with size }) rfl (Engine.start [] goal)

def outcomeKind : Engine.Outcome Nat Nat Sym → String
  | .success _ _ => "success"
  | .interrupted _ => "interrupted"
  | .finished .exhausted => "exhausted"
  | .finished (.opened _) => "opened"
  | .finished (.abandoned _) => "abandoned"
  | .finished _ => "finished"

/-- The outcome of a query's bounded run. -/
def decidedKind (clauses : List Clause) (goal : T) : String :=
  outcomeKind ((setupOf clauses goal).decided [] goal)

/-- The tables a bounded run opens. -/
def decidedTables (clauses : List Clause) (goal : T) : Nat :=
  match (setupOf clauses goal).decided [] goal with
  | .success _ resume => resume.tables.length
  | _ => 0

-- A bounded run ends for any program: the growing call `p(succ(…))` leaves the
-- bounds and is abandoned, where the fuelled run is interrupted.
#guard outcomeKind (smallRun grow (atom .p [k .zero]) 6) == "abandoned"
-- `∃Y. path(a, Y)` opens four tables, one per distinct call (the bounds'
-- calls, `Bounds.calls`, are for the proof, never computed).
#guard decidedTables (cyclic ++ rightRecursive) (.existsVar 7 (atom .path [k .a, v 7])) == 4

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

/-! ## Guards -/

/-- `path` lowered with its range guards first, as lowering emits it. -/
def lowered : List Clause :=
  [rule (atom .path [v 0, v 1]) [atom .allData [v 0], atom .allData [v 1], atom .edge [v 0, v 1]],
   rule (atom .path [v 0, v 1]) [atom .allData [v 0], atom .allData [v 1], atom .edge [v 0, v 2], atom .path [v 2, v 1]]]

-- The guards are tabled calls, decided by the signature's generated clauses,
-- which the checker reads too: the lowered `path` answers Yes, its proof
-- checked, and No for an unreachable target.
#guard profileKind (acyclic ++ lowered) (atom .path [k .a, k .c]) == "p1"
#guard kindOf (guardedAnswerOf (acyclic ++ lowered) (atom .path [k .a, k .b])) == "yes"
#guard kindOf (guardedAnswerOf (acyclic ++ lowered) (atom .path [k .a, k .c])) == "yes"
#guard kindOf (guardedAnswerOf (acyclic ++ lowered) (atom .path [k .a, k .d])) == "no"

/-! ## Calls with computed inputs -/

-- `p(X) :- q(succ(X)).  q(Y).`: the call `q(succ(a))` takes a constructed
-- input, within the bounds' size: Yes.
open Mode in
def oneInput : Modes Sym
  | .p | .q | .s => some [input]
  | _ => none

#guard profileKind [rule (atom .p [v 0]) [atom .q [succ (v 0)]], fact (atom .q [v 1])] (atom .p [k .a]) (declared := oneInput) == "p1"
#guard kindOf (answerOf [rule (atom .p [v 0]) [atom .q [succ (v 0)]], fact (atom .q [v 1])] (atom .p [k .a])
  (declared := oneInput)) == "yes"

/-! ## Consistency -/

open Mode in
def outputs : Modes Sym
  | .p | .q => some [output]
  | .r => some []
  | _ => none

-- `p(a). q(a). ⊥ :- p(X), q(X).`: the denial is violated by an instance, its
-- body closed existentially: every answer is Undecided, the KB's consistency.
#guard missingKinds (answerOf [fact (atom .p [k .a]), fact (atom .q [k .a]), .goal [atom .p [v 0], atom .q [v 0]], fact (k .r)]
  (k .r) (declared := outputs)) == ["consistency"]
-- `false :- p.` is a denial too.
#guard missingKinds (answerOf [fact (k .p), .definite .falsity [k .p], fact (k .q)] (k .q) (declared := nullary)) ==
  ["consistency"]
-- A denial whose body needs a constructed input: proved, so the KB is inconsistent.
#guard missingKinds (answerOf [rule (atom .p [v 0]) [atom .q [succ (v 0)]], fact (atom .q [v 1]), .goal [atom .p [k .a]],
  fact (atom .s [k .a])] (atom .s [k .a]) (declared := oneInput)) == ["consistency"]

/-- Five independent loops through NAF: thirty-two models. -/
def fiveLoops : List Clause :=
  [Sym.a, Sym.b, Sym.c, Sym.d, Sym.zero].flatMap fun constant =>
    [rule (atom .p [k constant]) [naf (atom .q [k constant])], rule (atom .q [k constant]) [naf (atom .p [k constant])]]

-- Ten undecided atoms: not every assignment is tried, so no candidate model is
-- no evidence of inconsistency.
#guard !(missingKinds (answerOf fiveLoops (atom .p [k .a]) (declared := oneInput))).contains "consistency"

/-! ## A bounded run's cut names its bound -/

def smallBlockers (clauses : List Clause) (goal : T) (size : Nat) (declared : Modes Sym := modes) : List String :=
  match smallRun clauses goal size declared with
  | .finished outcome => blockerKinds (Tabled.Setup.blockersOf outcome goal)
  | _ => []

-- The growing call `p(succ(…))` leaves the bounds: the blocker is a
-- termination limit, not a construct.
#guard (smallBlockers grow (atom .p [k .zero]) 6).contains "termination"
#guard !(smallBlockers grow (atom .p [k .zero]) 6).contains "construct"

-- A NAF cut by the bounds names the bound too.
#guard (smallBlockers [rule (atom .p [v 0]) [naf (atom .q [succ (succ (succ (succ (succ (succ (v 0))))))])],
  fact (atom .q [v 1])] (atom .p [k .zero]) 6 (declared := oneInput)).contains "termination"
#guard !(smallBlockers [rule (atom .p [v 0]) [naf (atom .q [succ (succ (succ (succ (succ (succ (v 0))))))])],
  fact (atom .q [v 1])] (atom .p [k .zero]) 6 (declared := oneInput)).contains "construct"

/-! ## Denials beside a P1 query -/

open Mode in
def denialModes : Modes Sym
  | .p | .q => some [input]
  | .r | .s | .t => some []
  | _ => none

-- A denial whose body is not P1 is checked with the fuel, not bounded: a
-- growing denial body ends with the fuel, naming its growing call.
#guard profileKind [rule (atom .p [v 0]) [atom .p [succ (v 0)]], .goal [atom .p [k .zero]], fact (k .r)] (k .r)
  (declared := denialModes) == "p1"
#guard missingKinds (answerOf [rule (atom .p [v 0]) [atom .p [succ (v 0)]], .goal [atom .p [k .zero]], fact (k .r)] (k .r)
  (fuel := 300) (declared := denialModes)) == ["termination"]
-- `⊥ :- (∀X. q(X)), t.` with `q(Y)`: the universal makes the body P2, run with
-- the fuel; `t` fails, so the KB is consistent and `r` is Yes.
#guard kindOf (answerOf [.goal [.forallVar 3 (atom .q [v 3]), k .t], fact (atom .q [v 4]), fact (k .r)] (k .r)
  (declared := denialModes)) == "yes"
-- `⊥ :- (s → (s → s)), t.`: the call `s` in the context `[s, s]` is outside
-- the bounds but answered by its assumption, so nothing is cut: `r` is Yes.
#guard kindOf (answerOf [.goal [.imp (k .s) (.imp (k .s) (k .s)), k .t], fact (k .r)] (k .r) (declared := denialModes)) == "yes"

-- A cut inside a response already incomplete is recorded too: the call
-- `q(succ⁶(zero))` leaves the bounds, the `ho_apply` datum in a head is an
-- unsupported match, and both are named.
#guard (smallBlockers [rule (atom .p [v 0]) [atom .q [succ (succ (succ (succ (succ (succ (v 0))))))]],
  rule (atom .q [succ (v 1)]) [atom .q [v 1]], fact (atom .q [atom .ha [v 2, v 3]])] (atom .p [k .zero]) 6
  (declared := oneInput)).contains "termination"

open Mode in
def countModes : Modes Sym
  | .q => some [output]
  | _ => none

-- An answer outside the bounds is recorded, not scheduled: the consumer
-- waiting on the table is a gap of the bound's.
#guard (smallBlockers [fact (atom .q [k .zero]), rule (atom .q [succ (v 1)]) [atom .q [v 1]]]
  (.existsVar 0 (.conj (atom .q [v 0]) (.equal (v 0) (k .c)))) 3 (declared := countModes)).contains "termination"

-- `naf unknown` meets an open atom: a witness is what is missing, not a construct.
#guard (smallBlockers [rule (k .p) [naf (k .unknown)]] (k .p) 50 (declared := nullary)).contains "witnesses"
#guard !(smallBlockers [rule (k .p) [naf (k .unknown)]] (k .p) 50 (declared := nullary)).contains "construct"

-- Denials whose bodies meet open atoms, checked one at a time, can miss a joint
-- inconsistency: `p :- ¬q. q :- ¬p. ⊥ :- ¬p. ⊥ :- ¬q.` has no model, and no
-- assignment shows one, so every answer is Undecided, the KB's consistency.
#guard missingKinds (answerOf [rule (k .p) [naf (k .q)], rule (k .q) [naf (k .p)], .goal [naf (k .p)], .goal [naf (k .q)],
  fact (k .r)] (k .r) (declared := nullary)) == ["consistency"]
-- `q(a) :- unknown. ⊥ :- q(a).`: the denial's run meets the open atom, and the
-- assignment with `unknown` false is a model in which the body fails: `r` is Yes.
#guard kindOf (answerOf [rule (atom .q [k .a]) [k .unknown], .goal [atom .q [k .a]], fact (k .r)] (k .r)
  (declared := denialModes)) == "yes"

end TabledEvaluationTests
