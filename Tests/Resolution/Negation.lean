import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Machine AnthillModKbSpec.P1 AnthillModKbSpec.Completion

namespace NegationTests

/-! Executable traces of S10: NAF evidence as refutations in the completed
program, checked by the S08 checker. Each `#guard` evaluates compiled code. -/

inductive Sym where
  | p | q | r | nat | zero | succ | one | two | plus | unknown | registry | ha
  | tag (tag : Tag)
  deriving DecidableEq, Repr

def vocab : Vocabulary Sym := ⟨Sym.tag, fun _ _ same => by cases same; rfl⟩

abbrev T := Term Nat Nat Sym
abbrev Clause := HornClause Nat Nat Sym
abbrev P := Proof Nat Nat Sym

def k (symbol : Sym) : T := .app symbol []
def atom (symbol : Sym) (args : List T) : T := .app symbol args
def fact (head : T) : Clause := .definite head []
def x (name : Nat) : T := .var name
def node (rule : Rule Nat Nat Sym) (conclusion : T) (premises : List P := []) : P := .node rule conclusion premises
def naf (goal : T) : T := .defaultNeg goal

/-- The declared free constructors: data constants and `succ`, and the
predicate names a registry lists. `plus` is a defined operation. -/
def free (symbol : Sym) : Bool := [Sym.zero, .succ, .one, .two, .p, .q].contains symbol

/-- The signature of `clauses` and `formulas`, with `unknown` the open marker. -/
def signatureOf (clauses : List Clause) (formulas : List T := []) : Signature Nat Sym :=
  Signature.of (· == .unknown) .ha free clauses formulas

/-- The completed program of `clauses`, closing their predicates and those of
`formulas`. -/
def completionOf (clauses : List Clause) (formulas : List T := []) : Completed Nat Nat Sym :=
  completion clauses (signatureOf clauses formulas)

def completedOf (clauses : List Clause) (formulas : List T := []) : List Clause :=
  (completionOf clauses formulas).clauses

def snapshotOf (clauses : List Clause) (formulas : List T := []) : Snapshot Nat Nat Sym :=
  ⟨.ha, completedOf clauses formulas⟩

/-- Check a tree whose NAF nodes carry refutations in the completed program. -/
def verdict (clauses : List Clause) (formulas : List T) (context : List T) (goal : T) (proof : P) : Verdict Sym :=
  checkProof vocab (refutationChecker vocab (snapshotOf clauses formulas)) [] context goal (encode vocab proof)

/-- The NAF node for `operand`, with the refutation as its evidence. -/
def nafNode (operand : T) (refutation : P) : P := node (.defaultNegIntro (encode vocab refutation)) (naf operand)

/-- The head name of a generated only-if clause. -/
def headName : Clause → Nat
  | .definite _ [.app _ [.var name]] => name
  | _ => 0

/-- `p(t) ∧ true` from the assumption `p(t)`: the body of an only-if clause. -/
def bodyOf (assumed : T) : P := node .conjIntro (.conj assumed .truth) [node .assumption assumed, node .truth .truth]

/-! ### No clauses: `p` is false everywhere, also at a rigid name -/

-- With no clause for p, its completion is `false :- p(x)`. The refutation of
-- p(a): assume p(a), and the only-if clause derives false from it.
def noP : Clause := onlyIf ([] : List Clause) Sym.p 1
def refuteNoP (argument : T) : P :=
  node .impIntro (.imp (atom .p [argument]) .falsity)
    [node (.clause noP [(headName noP, argument)]) .falsity [bodyOf (atom .p [argument])]]
-- NAF on the rigid parameter 5: no closed operand is needed.
#guard verdict [] [atom .p [x 0]] [] (naf (atom .p [x 5])) (nafNode (atom .p [x 5]) (refuteNoP (x 5))) = .accept
-- ∀x. naf p(x): open the binder, then NAF at the eigenvariable.
#guard verdict [] [atom .p [x 0]] [] (.forallVar 1 (naf (atom .p [x 1])))
  (node (.forallIntro 7) (.forallVar 1 (naf (atom .p [x 1]))) [nafNode (atom .p [x 7]) (refuteNoP (x 7))]) = .accept
-- Without the completion there is no refutation: the program alone is not
-- closed.
#guard checkProof vocab (refutationChecker vocab ⟨.ha, []⟩) [] [] (naf (atom .p [x 5]))
  (encode vocab (nafNode (atom .p [x 5]) (refuteNoP (x 5)))) = .reject

/-! ### A fact: a clash refutes other constants, never a rigid name -/

def pOne : List Clause := [fact (atom .p [k .one])]
def onlyP : Clause := onlyIf pOne Sym.p 1
/-- The cases of `p(t)`: `(t = one ∧ true) ∨ false`. -/
def pCases (argument : T) : T := .disj (.conj (.equal argument (k .one)) .truth) .falsity
/-- Refute `p(argument)` by its cases: the first by a clash of `argument` with
`one`, the second by the assumed `false`. -/
def refuteByClash (argument : T) (clash : Clause) : P :=
  node .impIntro (.imp (atom .p [argument]) .falsity)
    [node .disjElim .falsity
      [node (.clause onlyP [(headName onlyP, argument)]) (pCases argument) [bodyOf (atom .p [argument])],
        node (.goalClause clash []) .falsity
          [node .conjIntro (.conj (.equal argument (k .one)) .truth)
            [node .conjLeft (.equal argument (k .one)) [node .assumption (.conj (.equal argument (k .one)) .truth)],
              node .truth .truth]],
        node .assumption .falsity]]
def twoOne : Clause := clash (.application Sym.two 0) (.application Sym.one 0)
-- p(two) is refuted: two and one are distinct constructors.
#guard verdict pOne [atom .p [k .two]] [] (naf (atom .p [k .two])) (nafNode (atom .p [k .two]) (refuteByClash (k .two) twoOne))
  = .accept
-- The same tree for a rigid name is rejected: `a = one` is no clash, and
-- indeed p(a) holds when a is one.
#guard verdict pOne [atom .p [k .two]] [] (naf (atom .p [x 5])) (nafNode (atom .p [x 5]) (refuteByClash (x 5) twoOne))
  = .reject
-- Without the clash in the equality theory (two unknown to the signature),
-- p(two) is not refuted either.
#guard verdict pOne [] [] (naf (atom .p [k .two])) (nafNode (atom .p [k .two]) (refuteByClash (k .two) twoOne)) = .reject

/-! ### Open predicates -/

-- q(X) :- unknown keeps q open: its completion has a case `unknown`, and
-- `unknown` has no completion, so the case is never refuted.
def openQ : List Clause := [.definite (atom .q [x 0]) [k .unknown]]
#guard ((signatureOf openQ).predicates.map Prod.fst) = [.q]
#guard match onlyIf openQ Sym.q 1 with
  | .definite (.disj (.existsVar _ (.conj _ (.conj (.app .unknown []) .truth))) .falsity) _ => true
  | _ => false

-- The marker has no clauses of its own: a KB clause concluding it is invalid,
-- reported by its position.
def invalidAt (clauses : List Clause) : Option Nat :=
  match complete? (· == .unknown) .ha free clauses [] with
  | .error index => some index
  | .ok _ => none
#guard invalidAt (openQ ++ [fact (k .unknown)]) = some 1
#guard invalidAt [.definite (k .unknown) [atom .q [x 0]]] = some 0
#guard invalidAt openQ = none
#guard match complete? (· == .unknown) .ha free openQ [] with
  | .ok result => result.clauses.length == (completedOf openQ).length
  | .error _ => false

-- A head mentioning the marker anywhere is invalid: through a compound head or
-- as the predicate a ho_apply head applies.
#guard invalidAt [.definite (.conj (k .unknown) (k .q)) []] = some 0
#guard invalidAt [.definite (atom .ha [k .unknown, x 0]) []] = some 0
-- A head that may conclude any predicate may conclude the marker: invalid once
-- the marker is used, harmless otherwise.
#guard invalidAt [.definite (atom .ha [x 1, x 0]) [], .definite (atom .q [x 0]) [k .unknown]] = some 0
#guard invalidAt [.definite (x 9) [], .definite (atom .q [x 0]) [k .unknown]] = some 0
#guard invalidAt [.definite (x 9) [], fact (atom .q [k .one])] = none

/-! ### Machine runs: evidence first, then refutation -/

abbrev Run := Outcome Nat Nat Sym T Unit

/-- The evidence-first NAF strategy over the completion of `clauses`, with
`unknown` the open marker. -/
def strategy (clauses : List Clause) (formulas : List T := []) (select : Selection Nat Nat Sym := fun _ _ _ _ => []) :
    Strategy Nat Nat Sym T :=
  nafByRefutation vocab .ha (completionOf clauses formulas) (fun _ => false) select 200 (· == .unknown)

def runOf (clauses : List Clause) (formulas : List T) (flexibles : List Nat) (context : List T) (goal : T) : Run :=
  run (strategy clauses formulas) 2000 (State.init () flexibles context goal)

/-- Run, export, and check the export against the completed snapshot. -/
def checkedRun (clauses : List Clause) (formulas : List T) (context : List T) (goal : T) : Option (Verdict Sym) :=
  match runOf clauses formulas [] context goal with
  | .success proof _ => (exportProof vocab id proof).map fun term =>
      checkProof vocab (refutationChecker vocab (snapshotOf clauses formulas)) [] context goal term
  | _ => none

/-- The rule of the root node of a run's proof. -/
def rootRule (outcome : Run) : Option RuleId :=
  outcome.proof?.bind fun proof => match proof.tree with
    | .node rule _ _ _ => some rule.id
    | .deferred _ _ => none

-- No p clauses: naf p(5) at the rigid parameter 5 is refuted by the completion,
-- and the export checks.
#guard (runOf [] [atom .p [x 0]] [] [] (naf (atom .p [x 5]))).kind = .success
#guard checkedRun [] [atom .p [x 0]] [] (naf (atom .p [x 5])) = some .accept
-- ∀x. naf p(x): the eigenvariable is rigid, so the same refutation applies.
#guard checkedRun [] [atom .p [x 0]] [] (.forallVar 1 (naf (atom .p [x 1]))) = some .accept
-- Evidence first: an assumed naf p(5) closes the goal by identity, and no
-- refutation is searched (the root is no NAF node).
#guard rootRule (runOf [] [atom .p [x 0]] [] [naf (atom .p [x 5])] (naf (atom .p [x 5]))) ≠ some .defaultNegIntro
#guard (runOf [] [atom .p [x 0]] [] [naf (atom .p [x 5])] (naf (atom .p [x 5]))).kind = .success
-- A fact p(one) defeats the universal negative: p(a) is not refuted for a
-- rigid a, since a may be one.
#guard (runOf pOne [] [] [] (.forallVar 1 (naf (atom .p [x 1])))).kind = .abandoned
-- ... but naf p(two) is refuted by the clash of two with one.
#guard checkedRun pOne [atom .p [k .two]] [] (naf (atom .p [k .two])) = some .accept

/-! ### What the completion leaves open -/

-- A compound head may conclude p and q, so neither is closed: naf p(one) is
-- never refuted, and a tree through a closing clause for p does not check.
def compound : List Clause := [.definite (.conj (atom .p [k .one]) (atom .q [k .one])) []]
#guard (signatureOf compound).predicates.isEmpty
#guard (runOf compound [] [] [] (naf (atom .p [k .one]))).kind = .abandoned
#guard verdict compound [] [] (naf (atom .p [k .one])) (nafNode (atom .p [k .one]) (refuteNoP (k .one))) = .reject
-- A ho_apply head names the predicate it concludes: p is left open. A head
-- applying a predicate variable may conclude any predicate: none is closed.
#guard !((signatureOf [.definite (atom .ha [k .p, x 0]) [atom .q [x 0]]]).predicates.any (·.1 == .p))
#guard (signatureOf [.definite (atom .ha [x 1, x 0]) [], fact (atom .q [k .one])]).predicates.isEmpty
-- So does a formula-variable head, alone or in a compound head: X :- true may
-- conclude p(two).
#guard (signatureOf [.definite (x 9) [], fact (atom .p [k .one])]).predicates.isEmpty
#guard (signatureOf [.definite (.conj (x 9) (atom .q [k .one])) [], fact (atom .p [k .one])]).predicates.isEmpty
#guard (runOf [.definite (x 9) [], fact (atom .p [k .one])] [naf (atom .p [k .two])] [] []
  (naf (atom .p [k .two]))).kind = .abandoned
-- ho_apply itself is never closed: ho_apply(p, one) holds by p(one).
def applied : T := atom .ha [k .p, k .one]
#guard !((signatureOf pOne [applied]).predicates.any (·.1 == .ha))
#guard (runOf pOne [applied] [] [] (naf applied)).kind = .abandoned
-- plus is a defined operation, not a declared constructor: plus(zero) = zero
-- adds no clash for it. Declared free, it would: the completion then
-- contradicts the equation and refutes anything.
def plusZero : T := .equal (atom .plus [k .zero]) (k .zero)
def plusEquation : Clause := HornClause.equation (atom .plus [k .zero]) (k .zero) []
def withPlus : List Clause := [plusEquation, fact (atom .p [k .one])]
def plusClash : Clause := clash (.application Sym.plus 1) (.application Sym.zero 0)
def refuteByPlus (operand : T) : P :=
  node .impIntro (.imp operand .falsity)
    [node (.goalClause plusClash [((freshNames ([] : List Nat) 1).headD 0, k .zero)]) .falsity
      [node .conjIntro (.conj plusZero .truth) [node (.clause plusEquation []) plusZero [node .truth .truth],
        node .truth .truth]]]
#guard !((signatureOf withPlus).constructors.contains (.application .plus 1))
#guard verdict withPlus [] [] (naf (atom .p [k .one])) (nafNode (atom .p [k .one]) (refuteByPlus (atom .p [k .one])))
  = .reject
#guard checkProof vocab (refutationChecker vocab
    ⟨.ha, completed withPlus (Signature.of (· == .unknown) .ha (fun symbol => symbol == .plus || free symbol) withPlus [])⟩)
    [] [] (naf (atom .p [k .one])) (encode vocab (nafNode (atom .p [k .one]) (refuteByPlus (atom .p [k .one])))) = .accept

/-! ### Flexible operands: delay first, then the closing phase -/

/-- Run, export, and check the export for the root read through the final answers. -/
def checkedAnswer (clauses : List Clause) (formulas : List T) (flexibles : List Nat) (context : List T) (goal : T) :
    Option (Verdict Sym) :=
  match runOf clauses formulas flexibles context goal with
  | .success proof _ => (exportProof vocab id proof).map fun term =>
      checkProof vocab (refutationChecker vocab (snapshotOf clauses formulas)) []
        (context.map proof.store.resolve) (proof.store.resolve goal) term
  | _ => none

def answerOf (clauses : List Clause) (formulas : List T) (flexibles : List Nat) (goal : T) (name : Nat) : Option T :=
  (runOf clauses formulas flexibles [] goal).proof?.map fun proof => proof.store.resolve (x name)

-- naf p(X), X an answer name, no p clauses: the NAF waits for X; no goal binds
-- it, so the branch closes and p(X) is refuted for every X. The answer leaves
-- X unbound, and the export checks.
def nafX : T := naf (atom .p [x 3])
#guard checkedAnswer [] [atom .p [x 0]] [3] [] nafX = some .accept
#guard (answerOf [] [atom .p [x 0]] [3] nafX 3).map (identical (x 3)) = some true
-- With p(one) the generic refutation fails, X may be one: a gap.
#guard (runOf pOne [] [3] [] nafX).kind = .abandoned
-- Delay first: in naf p(X) ∧ r(X) with r(two), r binds X to two, the NAF wakes
-- and refutes p(two). Refuting at once, generically, would have failed.
def nafThenR : T := .conj nafX (atom .r [x 3])
def rTwo : List Clause := pOne ++ [fact (atom .r [k .two])]
#guard checkedAnswer rTwo [] [3] [] nafThenR = some .accept
#guard (answerOf rTwo [] [3] nafThenR 3).map (identical (k .two)) = some true
-- With r(one) the woken NAF reads naf p(one): a gap.
#guard (runOf (pOne ++ [fact (atom .r [k .one])]) [] [3] [] nafThenR).kind = .abandoned
-- An open predicate: naf q(5) meets q's marked case `q(X) :- unknown`. It is
-- reported opened, not abandoned as a gap, and no refutation is searched (S22).
#guard (runOf openQ [] [] [] (naf (atom .q [x 5]))).kind = .opened
#guard match runOf openQ [] [] [] (naf (atom .q [x 5])) with
  | .opened [gap] => identical gap.obligation.goal (naf (atom .q [x 5]))
  | _ => false
-- The open atom it meets is the marker atom.
#guard identicalArgs (openAtomsOf (· == Sym.unknown) (fun _ _ => true) openQ (naf (atom .q [x 5]))) [k .unknown]
-- The marker itself as a goal is open too; a clause body reaching it as well.
#guard (runOf openQ [] [] [] (atom .q [k .one])).kind = .opened
-- Without the marker, the same NAF is a gap, as before S22.
#guard (run (nafByRefutation vocab .ha (completionOf openQ) (fun _ => false) (fun _ _ _ _ => []) 200) 2000
  (State.init () [] [] (naf (atom .q [x 5])))).kind = .abandoned
-- A head that cannot match the operand covers nothing: q(one) :- unknown says
-- nothing about q(two), which is refuted by the clash of two and one.
#guard (openAtomsOf (· == Sym.unknown) (fun _ _ => true) [.definite (atom .q [k .one]) [k .unknown]]
  (atom .q [k .two])).isEmpty
#guard (runOf [.definite (atom .q [k .one]) [k .unknown]] [atom .q [k .two]] [] [] (naf (atom .q [k .two]))).kind
  = .success

/-! ### Guarded universal negatives and positive witnesses first -/

/-- `∀x. r(x) → naf p(x)`: no p over the domain r. -/
def guarded : T := .forallVar 1 (.imp (atom .r [x 1]) (naf (atom .p [x 1])))

-- The domain r = {two}, with p(one): the cases x = two of r(x) and x = one of
-- p(x) join to two = one, a clash. The export checks.
def overTwo : List Clause := pOne ++ [fact (atom .r [k .two])]
#guard checkedRun overTwo [] [] guarded = some .accept

/-- Evidence-first NAF with positive witnesses asked first. -/
def witnessFirst (clauses : List Clause) (select : Selection Nat Nat Sym := fun _ _ _ _ => []) :
    Strategy Nat Nat Sym T :=
  Strategy.withWitness
    (witnessSearch vocab (snapshotOf clauses) (Program.ofClauses (completedOf clauses) fun _ => false) (fun _ _ _ _ => []) 200)
    (strategy clauses [] select)

def witnessRun (clauses : List Clause) (goal : T) : Run :=
  run (witnessFirst clauses) 2000 (State.init () [] [] goal)

-- The domain r = {one}, with p(one): the witness one defeats the negative
-- before x is opened, and the run fails. Without the witness query the opened
-- goal is only a gap: the rigid x may be one.
def overOne : List Clause := pOne ++ [fact (atom .r [k .one])]
#guard (witnessRun overOne guarded).kind = .exhausted
#guard (runOf overOne [] [] [] guarded).kind = .abandoned
-- The same for the unguarded ∀x. naf p(x).
#guard (witnessRun pOne (.forallVar 1 (naf (atom .p [x 1])))).kind = .exhausted
-- No witness over r = {two}: the negative is opened and refuted as before.
#guard (witnessRun overTwo guarded).kind = .success
-- Evidence first, also before the witness: an assumed ∀x. naf p(x), or an
-- assumed falsity, closes the goal although p(one) is a witness.
def universalNaf : T := .forallVar 1 (naf (atom .p [x 1]))
def witnessRunUnder (clauses : List Clause) (context : List T) (goal : T) : Run :=
  run (witnessFirst clauses) 2000 (State.init () [] context goal)
#guard (witnessRunUnder pOne [universalNaf] universalNaf).kind = .success
#guard (witnessRunUnder pOne [.falsity] universalNaf).kind = .success
-- A left rule on an unrelated assumption is no evidence for the goal: with a
-- selection splitting q(one) ∧ q(two), the witness p(one) still defeats it.
def splitConjunctions : Selection Nat Nat Sym := fun _ _ _ context =>
  context.filterMap fun (assumption, read) => match read with
    | .conj _ _ => some (.conjUse assumption)
    | _ => none
#guard (run (witnessFirst pOne splitConjunctions) 2000
  (State.init () [] [.conj (atom .q [k .one]) (atom .q [k .two])] universalNaf)).kind = .exhausted

/-! ### Boundaries of the search -/

def nafP5 : T := naf (atom .p [x 5])

-- A clash under a constructor argument: succ(one) = one.
def nafSuccOne : T := naf (atom .p [atom .succ [k .one]])
#guard checkedRun pOne [nafSuccOne] [] nafSuccOne = some .accept
-- Injectivity is not searched: succ(two) = succ(one) is not split into
-- two = one, so the run is a gap ...
def pSuccOne : List Clause := [fact (atom .p [atom .succ [k .one]])]
def succTwo : T := atom .succ [k .two]
def nafSuccTwo : T := naf (atom .p [succTwo])
#guard (runOf pSuccOne [nafSuccTwo] [] [] nafSuccTwo).kind = .abandoned
-- ... but a supplied refutation using the injectivity clause checks.
def injSucc : Clause := (injective Sym.succ 1).headD (fact (k .p))
def injNames : Clause → List Nat
  | .definite (.equal (.var first) (.var second)) _ => [first, second]
  | _ => []
def onlyPS : Clause := onlyIf pSuccOne Sym.p 1
def succEq : T := .equal succTwo (atom .succ [k .one])
def refuteByInjection : P :=
  node .impIntro (.imp (atom .p [succTwo]) .falsity)
    [node .disjElim .falsity
      [node (.clause onlyPS [(headName onlyPS, succTwo)]) (.disj (.conj succEq .truth) .falsity) [bodyOf (atom .p [succTwo])],
        node (.goalClause twoOne []) .falsity
          [node .conjIntro (.conj (.equal (k .two) (k .one)) .truth)
            [node (.clause injSucc ((injNames injSucc).zip [k .two, k .one])) (.equal (k .two) (k .one))
                [node .conjIntro (.conj succEq .truth)
                  [node .conjLeft succEq [node .assumption (.conj succEq .truth)], node .truth .truth]],
              node .truth .truth]],
        node .assumption .falsity]]
#guard verdict pSuccOne [nafSuccTwo] [] nafSuccTwo (nafNode (atom .p [succTwo]) refuteByInjection) = .accept
-- A refutation that needs induction, p(succ(X)) :- p(X) with no base case,
-- unfolds without end: the bounded run finds none, and the NAF is a gap.
def pRec : List Clause := [.definite (atom .p [atom .succ [x 0]]) [atom .p [x 0]]]
#guard (runOf pRec [] [] [] nafP5).kind = .abandoned

-- Unrelated disjunctions are split only when no other step is left: with five
-- assumed q(i) ∨ r(i), false :- p(x) still refutes p(5) at once.
def unrelated : List T := (List.range 5).map fun index => .disj (atom .q [x (20 + index)]) (atom .r [x (20 + index)])
#guard (runOf [] [atom .p [x 0], atom .q [x 0], atom .r [x 0]] [] unrelated nafP5).kind = .success
-- Clash clauses are tried only for an assumed equation with their pair: five
-- unrelated literals do not slow the refutation of p(two).
def literals : List T := (List.range 5).map fun value => atom .r [.lit value]
#guard checkedRun pOne (naf (atom .p [k .two]) :: literals) [] (naf (atom .p [k .two])) = some .accept

-- The clash candidates at false: one per constructor pair an assumed equation
-- has, so succ(a) = zero and succ(b) = zero share one; none for a variable side
-- or a constructor the completion does not declare; a reversed equation is its
-- own pair.
def clashCount (constructors : List (Constructor Nat Sym)) (context : List T) : Nat :=
  let state : State Nat Nat Sym Unit Unit := State.init () [] context .falsity
  (clashAttempts (Certificate := Unit) Sym.ha constructors state.root state.store
    (state.store.readContext state.root)).length
def succZero : List (Constructor Nat Sym) := [.application .succ 1, .application .zero 0]
#guard clashCount succZero [.equal (atom .succ [x 1]) (k .zero), .equal (atom .succ [x 2]) (k .zero)] = 1
#guard clashCount succZero [.equal (x 1) (k .zero)] = 0
#guard clashCount [.application .zero 0] [.equal (atom .succ [x 1]) (k .zero)] = 0
#guard clashCount succZero [.equal (atom .succ [x 1]) (k .zero), .equal (k .zero) (atom .succ [x 2])] = 2

/-! ### Exact snapshots and contexts

Evidence is checked against the snapshot and the context it is given. -/

/-- The exported proof of a run on the completion of `clauses`. -/
def exported (clauses : List Clause) (formulas : List T) (context : List T) (goal : T) : Option T :=
  match runOf clauses formulas [] context goal with
  | .success proof _ => exportProof vocab id proof
  | _ => none

def checkIn (snapshot : Snapshot Nat Nat Sym) (context : List T) (goal : T) : Option T → Option (Verdict Sym) :=
  Option.map (checkProof vocab (refutationChecker vocab snapshot) [] context goal)

-- Adding a clause: the evidence of naf p(5) with no p clauses is rejected once
-- p(one) is a clause, whose completion has the case x = one.
#guard checkIn (snapshotOf pOne [atom .p [x 0]]) [] nafP5 (exported [] [atom .p [x 0]] [] nafP5) = some .reject
-- Registering a predicate adds its registry fact: naf registry(q) is refuted
-- while only p is registered, and that evidence is rejected once q is.
def registered (symbols : List Sym) : List Clause := symbols.map fun symbol => fact (atom .registry [k symbol])
def nafQ : T := naf (atom .registry [k .q])
#guard checkIn (snapshotOf (registered [.p]) [nafQ]) [] nafQ (exported (registered [.p]) [nafQ] [] nafQ) = some .accept
#guard checkIn (snapshotOf (registered [.p, .q]) [nafQ]) [] nafQ (exported (registered [.p]) [nafQ] [] nafQ) = some .reject
#guard (runOf (registered [.p, .q]) [nafQ] [] [] nafQ).kind = .abandoned
-- Adding a domain member: the guarded refutation over r = {two} is rejected
-- over r = {two, zero}, whose completion of r has another case; a new run
-- refutes again, since zero is not one either.
def overTwoZero : List Clause := overTwo ++ [fact (atom .r [k .zero])]
#guard checkIn (snapshotOf overTwoZero) [] guarded (exported overTwo [] [] guarded) = some .reject
#guard checkedRun overTwoZero [] [] guarded = some .accept
-- The context: refuting p(5) under r(5) uses r(5); the same evidence under no
-- assumption is rejected.
def underR5 : Option T := exported overTwo [] [atom .r [x 5]] nafP5
#guard checkIn (snapshotOf overTwo) [atom .r [x 5]] nafP5 underR5 = some .accept
#guard checkIn (snapshotOf overTwo) [] nafP5 underR5 = some .reject
-- Lemma imports: with q(X) :- p(X), the lemma q(one) is derivable. Completed
-- with the program it would add the case x = one to q's completion, and the
-- evidence of naf q(two) is rejected there; imported after the completion it
-- adds a clause and leaves the evidence checking.
def qOfP : List Clause := pOne ++ [.definite (atom .q [x 0]) [atom .p [x 0]]]
def nafQTwo : T := naf (atom .q [k .two])
def lemmaQ : Clause := fact (atom .q [k .one])
#guard checkIn ⟨.ha, completedOf qOfP [nafQTwo] ++ [lemmaQ]⟩ [] nafQTwo (exported qOfP [nafQTwo] [] nafQTwo) = some .accept
#guard checkIn (snapshotOf (qOfP ++ [lemmaQ]) [nafQTwo]) [] nafQTwo (exported qOfP [nafQTwo] [] nafQTwo) = some .reject

end NegationTests
