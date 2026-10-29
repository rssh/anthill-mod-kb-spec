import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Machine

namespace DelayTests

/-! Executable traces of delayed goals (S18). The command below is a test driver:
`r(t, ...)` is a check that delays while `t` reads as an unbound flexible name
and otherwise holds by an assumption; so does `naf r(t, ...)`, which otherwise
closes when its operand is not assumed; `s(t, u)` delays on both names while
both are unbound and otherwise holds; `e(t, u)` binds `t := u`; `c(t)` is a
test-driver clause `c(t) :- r(t), true` (S06 supplies clause selection). `#guard`
evaluates each run; the generic theorems (`step_valid`, `run_success`,
`Store.commit_wakes`, `CompletedProof.Valid`, `run_not_exhausted`) hold
for any command. -/

inductive Sym where
  | p | q | r | s | e | c | a | b
  deriving DecidableEq, Repr

abbrev T := Term Nat Nat Sym
abbrev E := Expansion Nat Nat Sym Unit
abbrev Tree := ProofTree Nat Nat Sym Unit
abbrev Run := Outcome Nat Nat Sym Unit Nat

def k (symbol : Sym) : T := .app symbol []
def atom (symbol : Sym) (args : List T) : T := .app symbol args

def same : T → T → Bool := identical
def sameArgs : List T → List T → Bool := identicalArgs

-- Matching and the candidate builders repeat the driver of
-- Tests/Resolution/Machine.lean: each test file runs on its own and cannot
-- import another.
mutual
/-- One-way matching: binds unbound flexible names of the pattern only. -/
def matchTerm (store : Store Nat Nat Sym) : T → T → List (Nat × T) → Option (List (Nat × T))
  | .var x, target, acc =>
      if same (.var x) target then some acc
      else if store.assignable x then
        match OperationDictionaries.lookup acc x with
        | some value => if same value target then some acc else none
        | none => some ((x, target) :: acc)
      else none
  | .app head xs, .app other ys, acc => if head == other then matchArgs store xs ys acc else none
  | pattern, target, acc => if same pattern target then some acc else none

def matchArgs (store : Store Nat Nat Sym) : List T → List T → List (Nat × T) → Option (List (Nat × T))
  | [], [], acc => some acc
  | x :: xs, y :: ys, acc =>
      match matchTerm store x y acc with
      | some next => matchArgs store xs ys next
      | none => none
  | _, _, _ => none
end

/-- The name a term reads as, when it is an unbound flexible name. -/
def unbound? (store : Store Nat Nat Sym) : T → Option Nat := assignableName? store

/-- The name `r(t, ...)`, or NAF of it, waits on. -/
def waitsOn? (store : Store Nat Nat Sym) : T → Option Nat
  | .app .r (arg :: _) => unbound? store arg
  | .defaultNeg operand => waitsOn? store operand
  | _ => none

def identityCandidates (store : Store Nat Nat Sym) (scope : Scope Nat Nat Sym) (goal : T) : List E :=
  (scope.assumptions.map store.resolve).filterMap fun assumption =>
    (matchTerm store goal assumption []).map (fun bindings => Expansion.assumption bindings)

def equalityCandidates (store : Store Nat Nat Sym) (left right : T) : List E :=
  match matchTerm store left right [] with
  | some bindings => [{ rule := .equalRefl, bindings := bindings }]
  | none =>
      match matchTerm store right left [] with
      | some bindings => [{ rule := .equalRefl, bindings := bindings }]
      | none => []

/-- The driver's answer for a goal that `waitsOn?` does not delay: the `s` check
still delays on both of its names, the other goals give candidates. -/
def respond (obligation : Obligation Nat Nat Sym) (store : Store Nat Nat Sym) (goal : T) :
    Response Nat Nat Sym Unit :=
  let fresh := store.freshFor (store.readBinders obligation)
  match goal with
  | .defaultNeg operand =>
      if (obligation.context.map store.resolve).any (same operand) then .candidates []
      else .candidates [{ rule := .defaultNegIntro () }]
  | .app .s [left, right] =>
      match unbound? store left, unbound? store right with
      | some first, some second => .delay [first, second]
      | _, _ => .candidates [{ rule := .extension .s [left, right] none }]
  | .app .e [left, right] =>
      match unbound? store left with
      | some name => .candidates [{ rule := .extension .e [left, right] none, bindings := [(name, right)] }]
      | none => .candidates []
  | .app .c [arg] =>
      .candidates [{ rule := .extension .c [arg] none, premises := [{ goal := atom .r [arg] }, { goal := .truth }] }]
  | .truth => .candidates [.truth]
  | .conj left right => .candidates [.conjIntro left right]
  | .imp premise conclusion => .candidates [.impIntro premise conclusion]
  | .forallVar binder body => .candidates [.forallIntro binder body fresh]
  | .existsVar binder body => .candidates [.existsIntro binder body fresh]
  | .equal left right => .candidates (equalityCandidates store left right)
  | .app _ _ => .candidates (identityCandidates store obligation.scope goal)
  | _ => .unsupported

def delaying : Command Nat Nat Sym Unit := fun obligation store =>
  let goal := store.resolve obligation.goal
  match waitsOn? store goal with
  | some name => .delay [name]
  | none => respond obligation store goal

def query (flexibles : List Nat) (context : List T) (goal : T) : State Nat Nat Sym Unit Nat :=
  State.init 0 flexibles context goal

def solve (state : State Nat Nat Sym Unit Nat) (command : Command Nat Nat Sym Unit := delaying) (fuel : Nat := 300) :
    Run :=
  run command fuel state

/-- Resume after a success with the command that produced it. -/
def resume (outcome : Run) (command : Command Nat Nat Sym Unit := delaying) : Run :=
  match outcome with
  | .success _ state => solve state command
  | other => other

def X : Nat := 0
def Y : Nat := 1

def answerIs (outcome : Run) (name : Nat) (expected : T) : Bool :=
  match outcome.proof? with
  | some proof => same (proof.answer name) expected
  | none => false

/-- The deferred proofs, newest first: id and the delayed goal read through the
final answers. -/
def records (outcome : Run) : List (Nat × T) :=
  match outcome.proof? with
  | some proof => proof.deferred.map fun record => (record.id, proof.store.resolve record.obligation.goal)
  | none => []

def recordsAre (outcome : Run) (expected : List (Nat × T)) : Bool :=
  let actual := records outcome
  actual.length == expected.length &&
    (actual.zip expected).all fun (found, wanted) => found.1 == wanted.1 && same found.2 wanted.2

/-- The rules of a completed proof's tree. The success step fills each reference
with its deferred proof, so a woken goal's rules appear where it delayed. -/
def rulesOf (outcome : Run) : Option (List RuleId) := outcome.proof?.map (·.tree.rules)

def settled (outcome : Run) : Bool :=
  match outcome.proof? with
  | some proof => proof.store.wakeups.isEmpty && proof.store.constraints.isEmpty
  | none => false

def gapReasons : Run → List GapReason
  | .unknown gaps => gaps.map (·.reason)
  | _ => []

/-! ### Wake on binding -/

-- r(X) delays (id 0); p(X) binds X := a and wakes it; r(a) holds. Its proof is
-- recorded under id 0 and filled into the tree at success, where it delayed.
def wake := solve (query [X] [atom .p [k .a], atom .r [k .a]] (.conj (atom .r [.var X]) (atom .p [.var X])))
#guard wake.kind = .success
#guard answerIs wake X (k .a)
#guard recordsAre wake [(0, atom .r [k .a])]
#guard rulesOf wake = some [.conjIntro, .assumption, .assumption]
#guard settled wake

/-! ### Rollback -/

-- X := b wakes r(b), which fails; rollback restores the suspension and X := a
-- wakes it again.
def restore := solve (query [X] [atom .p [k .b], atom .p [k .a], atom .r [k .a]]
  (.conj (atom .r [.var X]) (atom .p [.var X])))
#guard restore.kind = .success
#guard answerIs restore X (k .a)
#guard recordsAre restore [(0, atom .r [k .a])]
#guard (resume restore).kind = .exhausted

-- X := a wakes r(a), whose proof is recorded; q(a) fails; rollback discards that
-- record with the store. X := b succeeds with exactly one deferred proof.
def discardRecord := solve (query [X] [atom .p [k .a], atom .p [k .b], atom .r [k .a], atom .r [k .b], atom .q [k .b]]
  (.conj (atom .r [.var X]) (.conj (atom .p [.var X]) (atom .q [.var X]))))
#guard discardRecord.kind = .success
#guard answerIs discardRecord X (k .b)
#guard recordsAre discardRecord [(0, atom .r [k .b])]
#guard rulesOf discardRecord = some [.conjIntro, .assumption, .conjIntro, .assumption, .assumption]

-- The woken r(a, Y) has two candidates: Y := b, then Y := c. q(b) fails after
-- its proof was recorded; backtracking resumes the woken goal's own choice
-- point, with the woken entry on the stack and without that record.
def wokenAlternatives := solve (query [X, Y] [atom .p [k .a], atom .r [k .a, k .b], atom .r [k .a, k .c], atom .q [k .c]]
  (.conj (atom .r [.var X, .var Y]) (.conj (atom .p [.var X]) (atom .q [.var Y]))))
#guard wokenAlternatives.kind = .success
#guard answerIs wokenAlternatives Y (k .c)
#guard recordsAre wokenAlternatives [(0, atom .r [k .a, k .c])]
#guard rulesOf wokenAlternatives = some [.conjIntro, .assumption, .conjIntro, .assumption, .assumption]
#guard (resume wokenAlternatives).kind = .exhausted

/-! ### Several wakeups -/

-- Both checks delay (ids 0 and 1); q binds X and Y in one commit and wakes both,
-- the oldest first: records are newest first.
def twoWakeups := solve (query [X, Y] [atom .q [k .a, k .b], atom .r [k .a], atom .r [k .b]]
  (.conj (atom .r [.var X]) (.conj (atom .r [.var Y]) (atom .q [.var X, .var Y]))))
#guard twoWakeups.kind = .success
#guard recordsAre twoWakeups [(1, atom .r [k .b]), (0, atom .r [k .a])]
#guard rulesOf twoWakeups = some [.conjIntro, .assumption, .conjIntro, .assumption, .assumption]

-- A check delaying on [X, Y], then a goal binding X only: woken once, no stale
-- attachment on Y, success without floundering, and Y stays unbound.
def oneOfTwo := solve (query [X, Y] [atom .p [k .a]] (.conj (atom .s [.var X, .var Y]) (atom .p [.var X])))
#guard oneOfTwo.kind = .success
#guard recordsAre oneOfTwo [(0, atom .s [k .a, .var Y])]
#guard answerIs oneOfTwo Y (.var Y)
#guard settled oneOfTwo

-- The same check, then a goal binding X and Y in one commit: woken once.
def bothOfTwo := solve (query [X, Y] [atom .q [k .a, k .b]] (.conj (atom .s [.var X, .var Y]) (atom .q [.var X, .var Y])))
#guard bothOfTwo.kind = .success
#guard recordsAre bothOfTwo [(0, atom .s [k .a, k .b])]
#guard settled bothOfTwo

-- Exactly once, at the store: a commit binding both names a suspension waits on
-- returns it once and removes it; a suspension on another name stays.
def waitingStore : Store Nat Nat Sym :=
  { names := [(0, .flexible []), (1, .flexible []), (2, .flexible [])], bindings := []
    wakeups := [⟨1, Obligation.root [] [] (atom .r [.var 2]), [2]⟩,
      ⟨0, Obligation.root [] [] (atom .s [.var 0, .var 1]), [0, 1]⟩]
    constraints := [] }
#guard match waitingStore.commit (Obligation.root [] [] .truth) [] [] [] [(0, k .a), (1, k .b)] with
  | .committed next woken => woken.map (·.id) == [0] && next.wakeups.map (·.id) == [1]
  | _ => false
#guard match waitingStore.commit (Obligation.root [] [] .truth) [] [] [] [(0, k .a)] with
  | .committed next woken => woken.map (·.id) == [0] && next.wakeups.map (·.id) == [1]
  | _ => false
#guard match waitingStore.commit (Obligation.root [] [] .truth) [] [] [] [] with
  | .committed next woken => woken.isEmpty && next.wakeups.map (·.id) == [1, 0]
  | _ => false

/-! ### Aliases, callers, and scopes -/

-- e binds X := Y, which wakes r(X); it reads as r(Y) and delays again under id
-- 1. p(Y) binds Y := a and wakes it. Record 0 references record 1, and filling
-- follows the chain: r(a)'s assumption stands where r(X) delayed.
def alias := solve (query [X, Y] [atom .p [k .a], atom .r [k .a]]
  (.conj (atom .r [.var X]) (.conj (atom .e [.var X, .var Y]) (atom .p [.var Y]))))
#guard alias.kind = .success
#guard answerIs alias X (k .a)
#guard recordsAre alias [(1, atom .r [k .a]), (0, atom .r [k .a])]
#guard match alias.proof? with
  | some proof => (proof.deferred.find? (·.id == 0)).map (·.tree.refs.map Prod.fst) == some [1]
  | none => false
#guard rulesOf alias = some [.conjIntro, .assumption, .conjIntro, .extension, .assumption]

-- The callee c(X) completes with r(X) suspended; the caller's p(X) binds X := a
-- after the callee returned and wakes r(a).
def callee := solve (query [X] [atom .p [k .a], atom .r [k .a]] (.conj (atom .c [.var X]) (atom .p [.var X])))
#guard callee.kind = .success
#guard recordsAre callee [(0, atom .r [k .a])]
#guard rulesOf callee = some [.conjIntro, .extension, .assumption, .truth, .assumption]

-- r(X) delays under the local assumption r(a). After the implication is
-- discharged, p(X) wakes it, and r(a) holds by the assumption of its own scope.
def ownScope := solve (query [X] [atom .p [k .a]] (.conj (.imp (atom .r [k .a]) (atom .r [.var X])) (atom .p [.var X])))
#guard ownScope.kind = .success
#guard recordsAre ownScope [(0, atom .r [k .a])]
#guard match ownScope.proof? with
  | some proof => proof.deferred.all fun record => sameArgs record.obligation.context [atom .r [k .a], atom .p [k .a]]
  | none => false

-- The woken goal used r(a) from its own scope; the caller's last goal cannot.
def callerScope := solve (query [X] [atom .p [k .a]]
  (.conj (.imp (atom .r [k .a]) (atom .r [.var X])) (.conj (atom .p [.var X]) (atom .r [k .a]))))
#guard callerScope.kind = .exhausted

/-! ### Floundering and discarded suspensions -/

-- Still delayed at the end: unknown with a floundered gap, never success or
-- exhaustion.
def flounder := solve (query [X] [] (atom .r [.var X]))
#guard flounder.kind = .unknown
#guard gapReasons flounder = [.floundered]

-- A floundered branch does not block another branch's success, and its gap is
-- still reported once the alternatives are exhausted.
def splitting : Command Nat Nat Sym Unit := fun obligation store =>
  match store.resolve obligation.goal with
  | .disj left right => .candidates [.disjLeft left, .disjRight right]
  | _ => delaying obligation store

def flounderThenSuccess := solve (query [X] [atom .p [k .a], atom .r [k .a]]
  (.disj (atom .r [.var X]) (.conj (atom .r [.var X]) (atom .p [.var X])))) splitting
#guard flounderThenSuccess.kind = .success
#guard (resume flounderThenSuccess splitting).kind = .unknown

-- An unresolved constraint left at the end flounders too. S18 adds the slot and
-- no solver, so this state is built by hand.
def constrained : State Nat Nat Sym Unit Nat :=
  let state := query [X] [] .truth
  { state with store := { state.store with constraints := [⟨state.root, [X]⟩] } }
#guard (solve constrained).kind = .unknown
#guard gapReasons (solve constrained) = [.floundered]

-- No goal binds X: the branch fails and the suspension is discarded with it.
def discarded := solve (query [X] [] (.conj (atom .r [.var X]) (atom .p [.var X])))
#guard discarded.kind = .exhausted

/-! ### Evidence of delayed obligations -/

-- naf r(X) delays; p(X) binds X := a and wakes it, and its NAF node keeps the
-- certificate in the deferred proof. The success step fills that proof into the
-- tree, so the completed tree retains the certificate and is not monotonic.
def delayedNaf := solve (query [X] [atom .p [k .a]] (.conj (.defaultNeg (atom .r [.var X])) (atom .p [.var X])))
#guard delayedNaf.kind = .success
#guard delayedNaf.proof?.map (·.tree.closedWorld.length) = some 1
#guard delayedNaf.proof?.map (fun proof => (proof.deferred.flatMap (·.tree.closedWorld)).length) = some 1
#guard rulesOf delayedNaf = some [.conjIntro, .defaultNegIntro, .assumption]

/-! ### Restrictions never flounder -/

-- ∀x. (r(x) → ∃y. (r(y) ∧ y = x)): r(y) delays; y := x wakes it, and r(x) holds
-- by the assumption of its own scope. y keeps its dependency set [x] after
-- binding: a restriction, not a residual constraint.
def restricted := solve (query [] [] (.forallVar 10 (.imp (atom .r [.var 10])
  (.existsVar 11 (.conj (atom .r [.var 11]) (.equal (.var 11) (.var 10)))))))
#guard restricted.kind = .success
#guard settled restricted
#guard match restricted.proof? with
  | some proof => proof.store.names.any fun
      | (name, .flexible (_ :: _)) => (proof.store.binding? name).isSome
      | _ => false
  | none => false

/-! ### Invalid delays -/

-- A delay on no name, a rigid name, a bound name, or an undeclared name is a
-- contract gap on the delayed obligation.
def contractGap (outcome : Run) (goal : T) : Bool :=
  match outcome with
  | .unknown [⟨.contract, obligation⟩] => same obligation.goal goal
  | _ => false

#guard contractGap (solve (query [X] [] (atom .r [.var X])) (fun _ _ => .delay [])) (atom .r [.var X])
#guard contractGap (solve (query [] [] (atom .r [.var 7])) (fun _ _ => .delay [7])) (atom .r [.var 7])
#guard contractGap (solve (query [X] [] (atom .r [.var X])) (fun _ _ => .delay [9])) (atom .r [.var X])

def delayOnBound : Command Nat Nat Sym Unit := fun obligation store =>
  match obligation.goal with
  | .app .r _ => .delay [X]
  | _ => delaying obligation store
#guard contractGap (solve (query [X] [atom .p [k .a]] (.conj (atom .p [.var X]) (atom .r [.var X]))) delayOnBound)
  (atom .r [.var X])

/-! ### Formal properties used by the traces -/

-- Exactly-once wakeup holds for every commit of a scoped, waiting store.
example {store next : Store Nat Nat Sym} (valid : store.Scoped) (waiting : store.Waiting)
    {obligation : Obligation Nat Nat Sym} {bindings : List (Nat × T)} {woken : List (Suspension Nat Nat Sym)}
    (committed : store.commit obligation [] [] [] bindings = .committed next woken) :
    ((woken ++ next.wakeups).map Suspension.id).Nodup ∧ (woken.map Suspension.id).Pairwise (· > ·) ∧
      next.Waiting :=
  let ⟨_, once, _, _, waits, _⟩ := Store.commit_wakes valid waiting committed
  ⟨once, (Store.commit_woken valid committed).2, waits⟩

-- Every success of any command proves the root coherently with no goal still
-- delayed and no reference left in its tree.
example (command : Command Nat Nat Sym Unit) (fuel : Nat) (proof : CompletedProof Nat Nat Sym Unit Nat)
    (next : State Nat Nat Sym Unit Nat)
    (ran : run command fuel (query [X] [atom .p [k .a]] (atom .r [.var X])) = .success proof next) :
    proof.store.wakeups = [] ∧ proof.tree.obligation = (query [X] [atom .p [k .a]] (atom .r [.var X])).root ∧
      proof.tree.Coherent ∧ proof.tree.refs = [] :=
  let ⟨valid, _⟩ := run_success command fuel (State.init_valid _ _ _ _) ran
  ⟨valid.settled.1, valid.proves, valid.coherent, valid.complete⟩

-- A tree with a reference is never monotonic: the reference may stand for a
-- proof with closed-world evidence.
example (obligation : Obligation Nat Nat Sym) : ¬ (ProofTree.deferred (Certificate := Unit) 0 obligation).Monotonic :=
  fun monotonic => List.cons_ne_nil _ _ monotonic.1

-- A run's success is monotonic exactly when its tree retains no closed-world
-- evidence.
example (command : Command Nat Nat Sym Unit) (fuel : Nat) (proof : CompletedProof Nat Nat Sym Unit Nat)
    (next : State Nat Nat Sym Unit Nat)
    (ran : run command fuel (query [X] [atom .p [k .a]] (atom .r [.var X])) = .success proof next) :
    proof.tree.Monotonic ↔ proof.tree.closedWorld = [] :=
  (run_success command fuel (State.init_valid _ _ _ _) ran).1.monotonic_iff

-- Once a branch floundered, the run never reports exhaustion.
example (command : Command Nat Nat Sym Unit) (fuel : Nat) {state : State Nat Nat Sym Unit Nat}
    {tree : Tree} (focused : state.focus = .proved tree) (framesEq : state.frames = [])
    (residual : state.store.residual ≠ []) {next : State Nat Nat Sym Unit Nat}
    (stepped : step command state = .running next) : run command fuel next ≠ .exhausted := by
  rw [step_flounder command focused framesEq residual] at stepped
  cases stepped
  obtain ⟨pending, more, residualEq⟩ := List.exists_cons_of_ne_nil residual
  exact run_not_exhausted command fuel (by simp [residualEq])

end DelayTests
