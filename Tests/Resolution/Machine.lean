import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Machine

namespace MachineTests

/-! Executable traces of the S04 machine. The command below is a test driver for
logical connectives and atomic assumptions: S05 supplies the real matcher and
S06 the real commands. `#guard` evaluates each run; the generic theorems
(`step_valid`, `run_success`, `Frame.feed_exact`, `run_exhausted`,
`Store.commit_no_escape`) hold for any command. -/

inductive Sym where
  | p | q | r | a | b
  deriving DecidableEq, Repr

abbrev T := Term Nat Nat Sym

/-- A toy complete-failure certificate: the operand and the context it is absent
from. The test KB has no clauses, so absence is complete failure here; S07
defines real certificates and S08 checks them. -/
structure Absent where
  operand : T
  context : List T

abbrev Tree := ProofTree Nat Nat Sym Absent

def k (symbol : Sym) : T := .app symbol []
def atom (symbol : Sym) (args : List T) : T := .app symbol args

/-! ### Test driver -/

mutual
/-- Structural equality for the shapes used here. -/
def same : T → T → Bool
  | .var x, .var y => x == y
  | .lit x, .lit y => x == y
  | .app s xs, .app t ys => s == t && sameArgs xs ys
  | .truth, .truth => true
  | .falsity, .falsity => true
  | .conj a b, .conj c d => same a c && same b d
  | .disj a b, .disj c d => same a c && same b d
  | .imp a b, .imp c d => same a c && same b d
  | .equal a b, .equal c d => same a c && same b d
  | .existsVar x a, .existsVar y b => x == y && same a b
  | .forallVar x a, .forallVar y b => x == y && same a b
  | _, _ => false

def sameArgs : List T → List T → Bool
  | [], [] => true
  | x :: xs, y :: ys => same x y && sameArgs xs ys
  | _, _ => false
end

mutual
/-- `candidate` is `body` with the binder replaced by some name. -/
def instanceOf (binder : Nat) : T → T → Bool
  | .var x, .var _ => x == binder || same (.var x) (.var x)
  | .app s xs, .app t ys => s == t && instancesOf binder xs ys
  | body, candidate => same body candidate

def instancesOf (binder : Nat) : List T → List T → Bool
  | [], [] => true
  | x :: xs, y :: ys => instanceOf binder x y && instancesOf binder xs ys
  | _, _ => false
end

def flexibleUnbound (store : Store Nat Nat Sym) (name : Nat) : Bool :=
  match store.info? name with
  | some (.flexible _) => (store.binding? name).isNone
  | _ => false

mutual
/-- One-way matching: binds unbound flexible names of the pattern only. -/
def matchTerm (store : Store Nat Nat Sym) : T → T → List (Nat × T) → Option (List (Nat × T))
  | .var x, target, acc =>
      if same (.var x) target then some acc
      else if flexibleUnbound store x then
        match OperationDictionaries.lookup acc x with
        | some value => if same value target then some acc else none
        | none => some ((x, target) :: acc)
      else none
  | .app s xs, .app t ys, acc => if s == t then matchArgs store xs ys acc else none
  | pattern, target, acc => if same pattern target then some acc else none

def matchArgs (store : Store Nat Nat Sym) : List T → List T → List (Nat × T) → Option (List (Nat × T))
  | [], [], acc => some acc
  | x :: xs, y :: ys, acc =>
      match matchTerm store x y acc with
      | some next => matchArgs store xs ys next
      | none => none
  | _, _, _ => none
end

/-- Identity candidates, or `none` when an assumption cannot be resolved
(a capture hazard asks for alpha-renaming; it is not a miss). -/
def identityCandidates (store : Store Nat Nat Sym) (scope : Scope Nat Nat Sym) (goal : T) :
    Option (List (Expansion Nat Nat Sym Absent)) :=
  (scope.assumptions.mapM store.resolve?).map fun resolved =>
    resolved.filterMap fun assumption =>
      (matchTerm store goal assumption []).map (fun bindings => Expansion.assumption bindings)

/-- Case analysis on `a or b` is offered only while neither case is assumed, so
it is not repeated inside its own cases. -/
def caseCandidates (scope : Scope Nat Nat Sym) (goal : T) : List (Expansion Nat Nat Sym Absent) :=
  scope.assumptions.filterMap fun
    | .disj left right =>
        if scope.assumptions.any (fun other => same other left || same other right) then none
        else some (Expansion.disjElim left right goal)
    | _ => none

/-- Opening an existential assumption is offered only while no instance of its
body is assumed. -/
def openCandidates (store : Store Nat Nat Sym) (obligation : Obligation Nat Nat Sym) (goal : T) :
    List (Expansion Nat Nat Sym Absent) :=
  obligation.scope.assumptions.filterMap fun
    | .existsVar binder body =>
        if obligation.scope.assumptions.any (instanceOf binder body) then none
        else some (Expansion.existsElim binder body (store.freshFor obligation) goal)
    | _ => none

def equalityCandidates (store : Store Nat Nat Sym) (left right : T) : List (Expansion Nat Nat Sym Absent) :=
  match matchTerm store left right [] with
  | some bindings => [{ rule := .equalRefl, bindings := bindings }]
  | none =>
      match matchTerm store right left [] with
      | some bindings => [{ rule := .equalRefl, bindings := bindings }]
      | none => []

/-- Identity is preferred whenever it applies; otherwise case analysis and
existential opening come before the goal's introduction rule. -/
def logical : Command Nat Nat Sym Absent := fun obligation store =>
  match store.resolve? obligation.goal with
  | none => .unsupported
  | some goal =>
      match identityCandidates store obligation.scope goal with
      | none => .unsupported
      | some (first :: rest) => .candidates (first :: rest)
      | some [] =>
          let left := caseCandidates obligation.scope goal ++ openCandidates store obligation goal
          match goal with
          | .truth => .candidates [.truth]
          | .conj a b => .candidates (left ++ [.conjIntro a b])
          | .disj a b => .candidates (left ++ [.disjLeft a, .disjRight b])
          | .imp a b => .candidates (left ++ [.impIntro a b])
          | .forallVar x body => .candidates [.forallIntro x body (store.freshFor obligation)]
          | .existsVar x body => .candidates (left ++ [.existsIntro x body (store.freshFor obligation)])
          | .equal l r => .candidates (equalityCandidates store l r)
          | .app _ _ => .candidates left
          | _ => .unsupported

def query (flexibles : List Nat) (context : List T) (goal : T) : State Nat Nat Sym Absent Nat :=
  State.init 0 flexibles context goal

def solve (state : State Nat Nat Sym Absent Nat) (fuel : Nat := 200) : Outcome Nat Nat Sym Absent Nat :=
  run logical fuel state

def rulesOf (outcome : Outcome Nat Nat Sym Absent Nat) : Option (List RuleId) :=
  outcome.proof?.map (·.tree.rules)

def answerIs (outcome : Outcome Nat Nat Sym Absent Nat) (name : Nat) (expected : T) : Bool :=
  match outcome.proof?.bind (·.answer? name) with
  | some value => same value expected
  | none => false

def resume : Outcome Nat Nat Sym Absent Nat → Outcome Nat Nat Sym Absent Nat
  | .success _ state => solve state
  | other => other

mutual
/-- Leaves in order, with the context each was proved under. -/
def leaves : Tree → List (RuleId × List T)
  | .node rule obligation _ [] => [(rule.id, obligation.context)]
  | .node _ _ _ subproofs => leavesOf subproofs

def leavesOf : List Tree → List (RuleId × List T)
  | [] => []
  | tree :: trees => leaves tree ++ leavesOf trees
end

def leavesAre (outcome : Outcome Nat Nat Sym Absent Nat) (expected : List (RuleId × List T)) : Bool :=
  match outcome.proof? with
  | some proof =>
      let actual := leaves proof.tree
      actual.length == expected.length &&
        (actual.zip expected).all (fun (found, wanted) => found.1 == wanted.1 && sameArgs found.2 wanted.2)
  | none => false

def X : Nat := 0

/-! ### Conjunction: one AND node, completed once after both children -/

-- solve p∧q → push frame(conjIntro; current p, pending [q]) → p by assumption →
-- frame waits, focus q → q by assumption → frame completes → success.
def conjunction := solve (query [] [k .p, k .q] (.conj (k .p) (k .q)))
#guard conjunction.kind = .success
#guard rulesOf conjunction = some [.conjIntro, .assumption, .assumption]
#guard leavesAre conjunction [(.assumption, [k .p, k .q]), (.assumption, [k .p, k .q])]

/-! ### Disjunction: OR alternatives with rollback -/

-- solve p∨q → choice point [disjRight] → disjLeft: p has no candidate → failed →
-- restore and try disjRight → q by assumption.
def disjunction := solve (query [] [k .q] (.disj (k .p) (k .q)))
#guard disjunction.kind = .success
#guard rulesOf disjunction = some [.disjRight, .assumption]

-- p(X) offers X:=a and X:=b. X:=a fails at q(a); backtracking restores the store
-- without that binding, and X:=b succeeds. No further answers remain.
def rollback := solve (query [X] [atom .p [k .a], atom .p [k .b], atom .q [k .b]]
  (.conj (atom .p [.var X]) (atom .q [.var X])))
#guard rollback.kind = .success
#guard answerIs rollback X (k .b)
#guard (resume rollback).kind = .exhausted

-- Several answers are enumerated by resuming after success.
def answers := solve (query [X] [atom .p [k .a], atom .p [k .b]] (atom .p [.var X]))
#guard answerIs answers X (k .a)
#guard answerIs (resume answers) X (k .b)
#guard (resume (resume answers)).kind = .exhausted

/-! ### Nested implication and local assumptions -/

-- p → (q → p∧q): each impIntro premise extends only its own scope.
def nested := solve (query [] [] (.imp (k .p) (.imp (k .q) (.conj (k .p) (k .q)))))
#guard nested.kind = .success
#guard rulesOf nested = some [.impIntro, .impIntro, .conjIntro, .assumption, .assumption]
#guard leavesAre nested [(.assumption, [k .q, k .p]), (.assumption, [k .q, k .p])]

-- (p → p) ∧ p: the assumption p of the first conjunct does not reach the second.
def isolated := solve (query [] [] (.conj (.imp (k .p) (k .p)) (k .p)))
#guard isolated.kind = .exhausted
#guard isolated.proof?.isNone

-- With p assumed outside, both conjuncts see it.
def shared := solve (query [] [] (.imp (k .p) (.conj (.imp (k .p) (k .p)) (k .p))))
#guard shared.kind = .success

/-! ### Case analysis: two AND cases with separate assumptions -/

-- From p∨q prove q∨p: disjElim's cases are proved under p and under q respectively.
def cases := solve (query [] [.disj (k .p) (k .q)] (.disj (k .q) (k .p)))
#guard cases.kind = .success
#guard rulesOf cases =
  some [.disjElim, .assumption, .disjRight, .assumption, .disjLeft, .assumption]
#guard leavesAre cases
  [(.assumption, [.disj (k .p) (k .q)]),
   (.assumption, [k .p, .disj (k .p) (k .q)]),
   (.assumption, [k .q, .disj (k .p) (k .q)])]

/-! ### Shared answers across AND siblings -/

-- p(X) binds X:=a; the sibling sees q(a), which q(b) does not match. The
-- incompatible answer X:=b is never committed and no proof tree is produced.
def incompatible := solve (query [X] [atom .p [k .a], atom .q [k .b]]
  (.conj (atom .p [.var X]) (atom .q [.var X])))
#guard incompatible.kind = .exhausted
#guard incompatible.proof?.isNone

def compatible := solve (query [X] [atom .p [k .a], atom .q [k .a]]
  (.conj (atom .p [.var X]) (atom .q [.var X])))
#guard compatible.kind = .success
#guard answerIs compatible X (k .a)

-- The machine itself refuses to rebind X, even for a command that does not
-- resolve the goal first: binding X:=b after X:=a is a contract violation.
def rebind : Command Nat Nat Sym Absent := fun obligation _ =>
  match obligation.goal with
  | .conj a b => .candidates [.conjIntro a b]
  | .app .p _ => .candidates [.assumption [(X, k .a)]]
  | .app .q _ => .candidates [.assumption [(X, k .b)]]
  | _ => .unsupported

def rebound := run rebind 50 (query [X] [] (.conj (atom .p [.var X]) (atom .q [.var X])))
#guard rebound.kind = .unknown

-- Binding a name to itself is no change, not an occurs-check failure.
def selfIdentity := solve (query [] [] (.existsVar 11 (.imp (atom .p [.var 11]) (atom .p [.var 11]))))
#guard selfIdentity.kind = .success
#guard (solve (query [X] [] (.equal (.var X) (.var X)))).kind = .success

def selfBinding : Command Nat Nat Sym Absent := fun _ _ => .candidates [.assumption [(X, .var X)]]
#guard (run selfBinding 10 (query [X] [] (atom .p [.var X]))).kind = .success

/-! ### Dependencies: rigid names and opened witnesses do not escape -/

-- ∀x. ∃y. y = x: y is created inside x's scope, so it depends on x.
def forallExists := solve (query [] [] (.forallVar 10 (.existsVar 11 (.equal (.var 11) (.var 10)))))
#guard forallExists.kind = .success
#guard rulesOf forallExists = some [.forallIntro, .existsIntro, .equalRefl]

-- ∃y. ∀x. y = x: y does not depend on x, so y := x is rejected.
def existsForall := solve (query [] [] (.existsVar 11 (.forallVar 10 (.equal (.var 11) (.var 10)))))
#guard existsForall.kind = .exhausted

-- A root answer cannot be bound to a rigid name opened during search.
def escape := solve (query [X] [] (.forallVar 10 (.equal (.var X) (.var 10))))
#guard escape.kind = .exhausted

-- (∃x. p(x)) → ∃y. p(y): the witness opened by existsElim is in scope when y is
-- created, so y may take it.
def openThenWitness := solve (query [] [] (.imp (.existsVar 10 (atom .p [.var 10])) (.existsVar 11 (atom .p [.var 11]))))
#guard openThenWitness.kind = .success
#guard rulesOf openThenWitness = some [.impIntro, .existsElim, .assumption, .existsIntro, .assumption]

-- ∃y. ((∃x. p(x)) → p(y)): y exists before the witness is opened, so the witness
-- cannot become y's answer.
def witnessEscape := solve (query [] [] (.existsVar 11 (.imp (.existsVar 10 (atom .p [.var 10])) (atom .p [.var 11]))))
#guard witnessEscape.kind = .exhausted

-- (∀x. ∃y. true) ∧ (∀z. true): y is created under x. A command that tries to bind
-- y to z, an eigenvariable of the sibling branch at the same depth, is refused;
-- a numeric level would not separate the two scopes.
def crossBranch : Command Nat Nat Sym Absent := fun obligation store =>
  match obligation.goal, obligation.scope.rigids with
  | .truth, rigid :: _ =>
      let escaping := store.names.filterMap fun
        | (name, .flexible dependencies) =>
            if flexibleUnbound store name && !dependencies.contains rigid then some name else none
        | _ => none
      .candidates (escaping.map (fun name => Expansion.assumption [(name, .var rigid)]) ++ [.truth])
  | _, _ => logical obligation store

def siblingEscape := run crossBranch 100
  (query [] [] (.conj (.forallVar 20 (.existsVar 21 .truth)) (.forallVar 30 .truth)))
#guard siblingEscape.kind = .success
#guard siblingEscape.proof?.map (·.store.bindings.isEmpty) = some true

-- A name free in the query is one of its rigid parameters: opening ∀x does not
-- reuse it, so p(1) does not prove p(x).
def capture := solve (query [] [] (.imp (atom .p [.var 1]) (.forallVar 10 (atom .p [.var 10]))))
#guard capture.kind = .exhausted

/-! ### Unsupported, interrupted, and contract-violating paths -/

-- An unsupported focus is a gap, not failure: the outcome is unknown.
def unsupported := solve (query [] [] (.defaultNeg (k .p)))
#guard unsupported.kind = .unknown

-- A gap on one alternative does not block success on another, and it is still
-- reported once the remaining alternatives are exhausted.
def gapThenSuccess := solve (query [] [k .p] (.disj (.defaultNeg (k .q)) (k .p)))
#guard gapThenSuccess.kind = .success
#guard rulesOf gapThenSuccess = some [.disjRight, .assumption]
#guard (resume gapThenSuccess).kind = .unknown

-- Running out of budget is an interruption.
#guard (solve (query [] [k .p, k .q] (.conj (k .p) (k .q))) 3).kind = .interrupted

-- Binding a rigid parameter breaks the contract and is recorded as a gap.
def bindRigid : Command Nat Nat Sym Absent := fun _ _ => .candidates [.assumption [(7, k .a)]]
#guard (run bindRigid 10 (query [] [] (atom .p [.var 7]))).kind = .unknown

-- Opening a name already free in the obligation breaks the contract.
def staleName : Command Nat Nat Sym Absent := fun _ _ => .candidates [.existsIntro 0 (atom .p [.var 7]) 7]
#guard (run staleName 10 (query [] [] (.existsVar 0 (atom .p [.var 7])))).kind = .unknown

/-! ### Closed-world evidence is retained -/

-- Closes `naf A` when A is absent from the context, keeping the certificate.
def withNaf : Command Nat Nat Sym Absent := fun obligation store =>
  match store.resolve? obligation.goal with
  | some (.defaultNeg operand) =>
      if obligation.context.any (same operand) then .candidates []
      else .candidates [{ rule := .defaultNegIntro ⟨operand, obligation.context⟩ }]
  | _ => logical obligation store

-- p ∧ naf q under p: the NAF node keeps its certificate, so the exported proof
-- needs no new failure search, and the tree is snapshot-indexed.
def negation := run withNaf 100 (query [] [k .p] (.conj (k .p) (.defaultNeg (k .q))))
#guard negation.kind = .success
#guard rulesOf negation = some [.conjIntro, .assumption, .defaultNegIntro]
#guard match negation.proof? with
  | some proof =>
      match proof.tree.closedWorld with
      | [⟨.completeFailure, certificate⟩] => same certificate.operand (k .q) && sameArgs certificate.context [k .p]
      | _ => false
  | none => false
#guard (run withNaf 100 (query [] [k .p] (.defaultNeg (k .p)))).kind = .exhausted

/-! ### Formal properties used by the traces -/

def parent : Obligation Nat Nat Sym := Obligation.root [] [k .p, k .q] (.conj (k .p) (k .q))
def left : Premise Nat Nat Sym := { goal := k .p }
def right : Premise Nat Nat Sym := { goal := k .q }
def leftTree : Tree := .node .assumption (parent.premise left) [] []
def rightTree : Tree := .node .assumption (parent.premise right) [] []

-- One subproof per premise completes the AND node, exactly once.
example : (Frame.start parent .conjIntro left [right]).feed [leftTree, rightTree] =
    .complete (.node .conjIntro parent [left, right] [leftTree, rightTree]) :=
  Frame.feed_exact _ _ rfl

example : ∃ next, (Frame.start parent .conjIntro left [right]).feed [leftTree] = .waiting next :=
  let ⟨next, fed, _⟩ := Frame.feed_partial _ _ (by decide)
  ⟨next, fed⟩

example : (Frame.start parent .conjIntro left [right]).feed [leftTree, rightTree, leftTree] = .overfull :=
  Frame.feed_overfull _ _ (by decide)

-- The completed node is scope-coherent.
example : (ProofTree.node .conjIntro parent [left, right] [leftTree, rightTree]).Coherent :=
  .node (.cons rfl (.node .nil) (.cons rfl (.node .nil) .nil))

-- Every reachable state of any command keeps the invariant; a success proves the
-- root with a coherent tree and scoped answers.
example (command : Command Nat Nat Sym Absent) (fuel : Nat) (proof : CompletedProof Nat Nat Sym Absent Nat)
    (next : State Nat Nat Sym Absent Nat) (ran : run command fuel (query [X] [k .p] (atom .p [.var X])) = .success proof next) :
    proof.tree.obligation = (query [X] [k .p] (atom .p [.var X])).root ∧ proof.tree.Coherent ∧ proof.store.Scoped :=
  let ⟨_, root, coherent, answers, _⟩ := run_success command fuel (State.init_valid _ _ _ _) ran
  ⟨root, coherent, answers⟩

-- Clause and logical evidence is monotonic; closed-world evidence is not.
example {kb grown : LogicalKb Nat Nat Sym} (larger : ∀ clause, clause ∈ kb → clause ∈ grown)
    {context : ProofContext Nat Nat Sym} {goal : T} (proof : Derives Sym.r kb context goal) :
    Derives Sym.r grown context goal :=
  proof.positive_mono larger

example : (RuleApp.defaultNegIntro ⟨k .q, []⟩ : RuleApp Nat Nat Sym Absent).evidenceClass = .snapshotIndexed := rfl
example : (RuleApp.clause (.definite (k .p) []) [] : RuleApp Nat Nat Sym Absent).evidenceClass = .monotonic := rfl

end MachineTests
