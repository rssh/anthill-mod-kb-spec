import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Machine AnthillModKbSpec.InductiveDomains AnthillModKbSpec.AdmissionSignature

namespace PositiveTests

/-! Executable traces of S06: the `positive` command over an effective program.
Each trace runs the machine from `State.init` and is checked by `#guard`, which
evaluates compiled code. The theorems at the end hold for every program and
query: a successful run reconstructs `Derives` for its answer instance. -/

inductive Sym where
  | p | q | r | s | t | u | v | w | e | num | a | b | c | zero | succ | isNat | allData | isPred | natDomain | ha
  deriving DecidableEq, Repr

abbrev T := Term Nat Nat Sym
abbrev Clause := HornClause Nat Nat Sym
abbrev Run := Outcome Nat Nat Sym Unit Nat

def k (symbol : Sym) : T := .app symbol []
def atom (symbol : Sym) (args : List T) : T := .app symbol args
def same : T → T → Bool := identical
def fact (head : T) : Clause := .definite head []
def rule (head : T) (body : List T) : Clause := .definite head body

/-- A program of KB clauses with no guard symbols. -/
def plain (clauses : List Clause) : Program Nat Nat Sym :=
  ⟨clauses.mapIdx fun index clause => ⟨.lowered index, clause⟩, fun _ => false⟩

def query (flexibles : List Nat) (context : List T) (goal : T) : State Nat Nat Sym Unit Nat :=
  State.init 0 flexibles context goal

def solve (program : Program Nat Nat Sym) (state : State Nat Nat Sym Unit Nat) (fuel : Nat := 400) : Run :=
  run (positive .ha program) fuel state

def resume (program : Program Nat Nat Sym) : Run → Run
  | .success _ state => solve program state
  | other => other

def rulesOf (outcome : Run) : Option (List RuleId) := outcome.proof?.map (·.tree.rules)

def answerIs (outcome : Run) (name : Nat) (expected : T) : Bool :=
  match outcome.proof? with
  | some proof => same (proof.answer name) expected
  | none => false

def floundered : Run → Bool
  | .unknown gaps => gaps.any (·.reason == .floundered)
  | _ => false

mutual
/-- Clause applications in preorder, with the goal each one proves. -/
def clauseNodes : ProofTree Nat Nat Sym Unit → List (Clause × T)
  | .node (.clause clause _) obligation _ subproofs => (clause, obligation.goal) :: clauseNodesOf subproofs
  | .node _ _ _ subproofs => clauseNodesOf subproofs
  | .deferred _ _ => []

def clauseNodesOf : List (ProofTree Nat Nat Sym Unit) → List (Clause × T)
  | [] => []
  | tree :: trees => clauseNodes tree ++ clauseNodesOf trees
end

def clausesOf (outcome : Run) : List (Clause × T) := (outcome.proof?.map (clauseNodes ·.tree)).getD []

mutual
/-- Witnesses of existential introductions in preorder. -/
def witnesses : ProofTree Nat Nat Sym Unit → List T
  | .node (.existsIntro witness) _ _ subproofs => witness :: witnessesOf subproofs
  | .node _ _ _ subproofs => witnessesOf subproofs
  | .deferred _ _ => []

def witnessesOf : List (ProofTree Nat Nat Sym Unit) → List T
  | [] => []
  | tree :: trees => witnesses tree ++ witnessesOf trees
end

mutual
/-- Witnesses of universal eliminations in preorder. -/
def eliminations : ProofTree Nat Nat Sym Unit → List T
  | .node (.forallElim witness) _ _ subproofs => witness :: eliminationsOf subproofs
  | .node _ _ _ subproofs => eliminationsOf subproofs
  | .deferred _ _ => []

def eliminationsOf : List (ProofTree Nat Nat Sym Unit) → List T
  | [] => []
  | tree :: trees => eliminations tree ++ eliminationsOf trees
end

/-- Every universal-elimination witness names only names the final store declares. -/
def witnessesDeclared (outcome : Run) : Bool :=
  match outcome.proof? with
  | some proof => (eliminations proof.tree).all fun witness => witness.freeVars.all fun name => (proof.store.info? name).isSome
  | none => false

/-- The first existential witness, read through the final answers. -/
def witnessIs (outcome : Run) (expected : T) : Bool :=
  match outcome.proof? with
  | some proof =>
      match witnesses proof.tree with
      | witness :: _ => same (proof.store.resolve witness) expected
      | [] => false
  | none => false

/-! ### Clause selection replaces the goal by the instantiated body -/

-- R01: p(a) :- q(a) and the fact q(a). The first step selects the clause: the
-- focus is its renamed body under the same scope, so no head is assumed, and
-- the frame above it is the FinishClause continuation, waiting on that body.
def r01 : Program Nat Nat Sym := plain [rule (atom .p [k .a]) [atom .q [k .a]], fact (atom .q [k .a])]
#guard match step (positive .ha r01) (query [] [] (atom .p [k .a])) with
  | .running state =>
      match state.focus, state.frames with
      | .solve obligation, [.frame frame] =>
          same obligation.goal (.conj (atom .q [k .a]) .truth) && obligation.scope.assumptions.isEmpty &&
            frame.pending.isEmpty && frame.done.isEmpty && (match frame.rule with | .clause _ _ => true | _ => false)
      | _, _ => false
  | .finished _ => false
-- Its clause node is built once, on the body's proof.
#guard rulesOf (solve r01 (query [] [] (atom .p [k .a]))) = some [.clause, .conjIntro, .clause, .truth, .truth]

/-! ### Connectives -/

-- p ∨ q under q: the left disjunct misses; rollback tries the right one.
#guard rulesOf (solve (plain []) (query [] [k .q] (.disj (k .p) (k .q)))) = some [.disjRight, .assumption]
-- (p → p) ∧ p: the first conjunct's assumption is scoped to it, so the second
-- conjunct has no proof.
#guard (solve (plain []) (query [] [] (.conj (.imp (k .p) (k .p)) (k .p)))).kind = .exhausted
-- ∀1. (q(1) → q(1)): universal introduction opens a fresh rigid name.
#guard rulesOf (solve (plain []) (query [] [] (.forallVar 1 (.imp (atom .q [.var 1]) (atom .q [.var 1])))))
  = some [.forallIntro, .impIntro, .assumption]

/-! ### Candidate backtracking and single completion -/

-- R02: p :- q, p :- r, and r. The first clause's body has no proof; exhausting
-- that candidate does not declare p false: the second clause succeeds. The root
-- p is completed once, by the second clause; resuming is exhausted.
def r02 : Program Nat Nat Sym := plain [rule (k .p) [k .q], rule (k .p) [k .r], fact (k .r)]
def r02Run := solve r02 (query [] [] (k .p))
#guard r02Run.kind = .success
#guard match clausesOf r02Run with
  | [(.definite (.app .p []) [.app .r []], .app .p []), (.definite (.app .r []) [], .app .r [])] => true
  | _ => false
#guard (resume r02 r02Run).kind = .exhausted

-- Nested goals: p :- q, r with both as facts. Each frame completes once, so the
-- tree has exactly one node per clause use.
def nestedRun := solve (plain [rule (k .p) [k .q, k .r], fact (k .q), fact (k .r)]) (query [] [] (k .p))
#guard rulesOf nestedRun = some [.clause, .conjIntro, .clause, .truth, .conjIntro, .clause, .truth, .truth]
#guard (clausesOf nestedRun).length = 3

-- r(X) :- s(X) and r(X) :- t(X) under s(a), t(b), u(b), for r(Y) ∧ u(Y): the
-- first clause binds Y to a and fails at u(a); rollback discards its fresh
-- names and bindings, and the second clause answers b. Resuming is exhausted.
def rProgram : Program Nat Nat Sym :=
  plain [rule (atom .r [.var 50]) [atom .s [.var 50]], rule (atom .r [.var 50]) [atom .t [.var 50]]]
def rRun := solve rProgram
  (query [0] [atom .s [k .a], atom .t [k .b], atom .u [k .b]] (.conj (atom .r [.var 0]) (atom .u [.var 0])))
#guard rRun.kind = .success
#guard answerIs rRun 0 (k .b)
#guard rulesOf rRun = some [.conjIntro, .clause, .conjIntro, .assumption, .truth, .assumption]
#guard (resume rProgram rRun).kind = .exhausted

-- Answers enumerate on resume: p(X) from the facts p(a), p(b).
def pFacts : Program Nat Nat Sym := plain [fact (atom .p [k .a]), fact (atom .p [k .b])]
#guard answerIs (solve pFacts (query [0] [] (atom .p [.var 0]))) 0 (k .a)
#guard answerIs (resume pFacts (solve pFacts (query [0] [] (atom .p [.var 0])))) 0 (k .b)
#guard (resume pFacts (resume pFacts (solve pFacts (query [0] [] (atom .p [.var 0]))))).kind = .exhausted

/-! ### Existential answers -/

-- ∃y. p(y) over p(a), p(b): the witness is a fresh flexible name, answered a,
-- then b; then exhausted.
def existsRun := solve pFacts (query [] [] (.existsVar 9 (atom .p [.var 9])))
#guard rulesOf existsRun = some [.existsIntro, .clause, .truth]
#guard witnessIs existsRun (k .a)
#guard witnessIs (resume pFacts existsRun) (k .b)
#guard (resume pFacts (resume pFacts existsRun)).kind = .exhausted

-- Quantifier order (R16), with s(Y, Y) as a clause: under ∀x the witness may
-- take x; created before x, it may not, and the run is exhausted, not unknown.
def sameProgram : Program Nat Nat Sym := plain [fact (atom .s [.var 50, .var 50])]
#guard (solve sameProgram (query [] [] (.forallVar 10 (.existsVar 11 (atom .s [.var 11, .var 10]))))).kind = .success
#guard (solve sameProgram (query [] [] (.existsVar 11 (.forallVar 10 (atom .s [.var 11, .var 10]))))).kind = .exhausted

/-! ### Local rules -/

-- q(a) → ((∀x. (q(x) → p(x))) → p(a)): the rule is assumed, then used for p(a)
-- by implication elimination with a fresh witness a'. Its instance
-- q(a') → p(a) is proved from the assumption by an exact universal elimination,
-- never reopened by implication introduction; q(a') binds a' := a.
def localRule : T := .forallVar 1 (.imp (atom .q [.var 1]) (atom .p [.var 1]))
def useLocal := solve (plain []) (query [] [] (.imp (atom .q [k .a]) (.imp localRule (atom .p [k .a]))))
#guard rulesOf useLocal = some [.impIntro, .impIntro, .impElim, .forallElim, .assumption, .assumption]
#guard (resume (plain []) useLocal).kind = .exhausted

-- A goal that is itself an instance of the rule, q(a) → p(a), is closed by the
-- rule alone: one exact universal elimination.
#guard rulesOf (solve (plain []) (query [] [] (.imp localRule (.imp (atom .q [k .a]) (atom .p [k .a])))))
  = some [.impIntro, .forallElim, .assumption]

-- Lifetime: the rule is discharged with its implication. The sibling conjunct
-- cannot use it, so the run is exhausted.
#guard (solve (plain []) (query [] []
  (.conj (.imp localRule (.imp (atom .q [k .a]) (atom .p [k .a]))) (.imp (atom .q [k .a]) (atom .p [k .a]))))).kind
  = .exhausted

-- Captured names are kept: ∀1. (q(1, 7) → p(1)) keeps the parameter 7, so q(a, 7)
-- proves p(a) and q(a, 8) does not.
def captured : T := .forallVar 1 (.imp (atom .q [.var 1, .var 7]) (atom .p [.var 1]))
#guard (solve (plain []) (query [] [captured, atom .q [k .a, .var 7]] (atom .p [k .a]))).kind = .success
#guard (solve (plain []) (query [] [captured, atom .q [k .a, .var 8]] (atom .p [k .a]))).kind = .exhausted

-- Explicit binders are instantiated in order: ∀1. ∀2. (q(1, 2) → p(2, 1)) under
-- q(a, b) proves p(b, a), not p(a, b). Its instance is proved by two universal
-- eliminations: the last binder with the fresh witness matched against the goal,
-- then the first with the witness read off the intermediate instance.
def twoBinders : T := .forallVar 1 (.forallVar 2 (.imp (atom .q [.var 1, .var 2]) (atom .p [.var 2, .var 1])))
def swapped := solve (plain []) (query [] [twoBinders, atom .q [k .a, k .b]] (atom .p [k .b, k .a]))
#guard rulesOf swapped = some [.impElim, .forallElim, .forallElim, .assumption, .assumption]
#guard (solve (plain []) (query [] [twoBinders, atom .q [k .a, k .b]] (atom .p [k .a, k .b]))).kind = .exhausted

-- A universal fact ∀1. ∀2. r(1, 2, 1) instantiates the same way.
def universalFact : T := .forallVar 1 (.forallVar 2 (atom .r [.var 1, .var 2, .var 1]))
#guard rulesOf (solve (plain []) (query [] [universalFact] (atom .r [k .a, k .b, k .a])))
  = some [.forallElim, .forallElim, .assumption]
#guard (solve (plain []) (query [] [universalFact] (atom .r [k .a, k .b, k .b]))).kind = .exhausted

-- A binder that does not occur in the rule's matrix gets a closed witness: no
-- undeclared name enters the tree.
def vacuous := solve (plain []) (query [] [.forallVar 1 (.forallVar 2 (atom .p [.var 2]))] (atom .p [k .a]))
#guard rulesOf vacuous = some [.forallElim, .forallElim, .assumption]
#guard witnessesDeclared vacuous

-- An operation call inside a rule: its instance is still found exactly.
def call (argument : T) : T := .dictionaryCall (k .c) [] .s [argument]
#guard rulesOf (solve (plain []) (query [] [.forallVar 1 (.imp (atom .q [call (.var 1)]) (atom .p [.var 1])),
  atom .q [call (k .a)]] (atom .p [k .a]))) = some [.impElim, .forallElim, .assumption, .assumption]

-- A rigid name equal to the rule's inner binder name: reading the instance's
-- premise renames that binder, but the instance itself is built and closed as
-- written, so the run still succeeds.
#guard (solve (plain []) (query [] [.forallVar 1 (.imp (.forallVar 2 (atom .r [.var 1, .var 2])) (atom .p [.var 1])),
  .forallVar 3 (atom .r [.var 2, .var 3])] (atom .p [.var 2]))).kind = .success

-- A curried rule whose final conclusion fits the goal is a gap: this slice
-- eliminates one implication.
#guard (solve (plain []) (query [] [.forallVar 1 (.imp (atom .q [.var 1]) (.imp (atom .r [.var 1]) (atom .p [.var 1]))),
  atom .q [k .c], atom .r [k .c]] (atom .p [k .c]))).kind = .unknown

-- The rule's own instance with a parameter equal to its inner binder name: an
-- exact step whose premise reading would rename that binder is not offered, so
-- the goal is opened and the rule used as for an atom. No loop.
#guard (solve (plain []) (query [] [.forallVar 1 (.forallVar 2 (.imp (atom .q [.var 1, .var 2]) (atom .p [.var 1, .var 2]))),
  atom .q [.var 2, .var 7]] (.imp (atom .q [.var 2, .var 7]) (atom .p [.var 2, .var 7])))).kind = .success

-- A goal the store cannot conclude without left rules or compound conclusions
-- is a gap, not a miss: a rule concluding a universal, a conjunctive
-- assumption, a rule whose conclusion is its own binder.
#guard (solve (plain []) (query [] [.forallVar 1 (.imp (atom .q [.var 1]) (.forallVar 2 (atom .p [.var 1, .var 2]))),
  atom .q [k .a]] (atom .p [k .a, k .b]))).kind = .unknown
#guard (solve (plain []) (query [] [.conj (k .p) (k .q)] (k .p))).kind = .unknown
#guard (solve (plain []) (query [] [.forallVar 1 (.var 1)] (atom .p [k .a]))).kind = .unknown
-- An assumed false proves any goal (ex falso).
#guard rulesOf (solve (plain []) (query [] [.falsity] (atom .p [k .a]))) = some [.falsityElim, .assumption]
#guard rulesOf (solve (plain []) (query [] [.falsity] (.conj (k .p) (k .q)))) = some [.falsityElim, .assumption]

-- A local rule's answer binds a root name through a fresh witness.
#guard answerIs (solve (plain []) (query [0] [localRule, atom .q [k .c]] (atom .p [.var 0]))) 0 (k .c)

-- A goal that is an assumption is closed by it, without introduction.
#guard rulesOf (solve (plain []) (query [] [universalFact] universalFact)) = some [.assumption]

/-! ### Guards from the signature delay -/

inductive Dom where
  | nat
  deriving DecidableEq, Repr

def zeroRule : Rule Dom Sym := ⟨.nat, .zero, []⟩
def succRule : Rule Dom Sym := ⟨.nat, .succ, [.nat]⟩
def family : FiniteFamily Dom Sym := ⟨fun rule => rule = zeroRule ∨ rule = succRule, [.nat], fun domain => by cases domain; simp⟩

/-- isNat is Nat's membership symbol, allData is D_all, isPred names every P_n;
p is registered at arity 1. -/
def snapshot : SignatureSnapshot Dom Sym := ⟨0, ⟨family, fun _ => .isNat, .allData, fun _ => .isPred, [⟨.p, 1⟩]⟩⟩
def names : Nat → Nat := fun index => 100 + index
def rules : List (Rule Dom Sym) := [zeroRule, succRule]

theorem listed : ∀ rule ∈ rules, snapshot.signature.data.definitions rule := by
  intro rule member
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at member
  exact member

def zero : T := k .zero
def succ (n : T) : T := atom .succ [n]

/-- KB clauses with generated ranges: unannotated variables range over D_all;
the generator relation natDomain ranges over the carrier. -/
def data (clause : Clause) : SourceClause Dom Nat Nat Sym := ⟨clause, Elaboration.defaultRanges, fun _ => .allData⟩
def carrier (clause : Clause) : SourceClause Dom Nat Nat Sym := ⟨clause, Elaboration.defaultRanges, fun _ => .carrier⟩

def sources : List (SourceClause Dom Nat Nat Sym) :=
  [ data (rule (atom .v [.var 50]) []),                                -- v(X) :- true, guarded
    data (rule (atom .num [.var 50]) [atom .natDomain [.var 50]]),     -- a typed head: member goal appended
    carrier (fact (atom .natDomain [zero])),
    carrier (rule (atom .natDomain [succ (.var 50)]) [atom .natDomain [.var 50]]) ]

def built : Except LoweringError (Program Nat Nat Sym) := Program.build .ha snapshot names rules sources
def guarded : Program Nat Nat Sym :=
  match built with
  | .ok program => program
  | .error _ => ⟨[], fun _ => false⟩

#guard match built with | .ok _ => true | .error _ => false
-- The guard symbols are the naming's membership symbols, not the generator's.
#guard guardSymbol snapshot .allData && guardSymbol snapshot .isNat && guardSymbol snapshot .isPred &&
  !guardSymbol snapshot .natDomain
-- Lowered bodies begin with their guards: v(X) :- D_all(X).
#guard match guarded.clauses with
  | ⟨.lowered 0, .definite (.app .v [.var 50]) [.app .allData [.var 50]]⟩ :: _ => true
  | _ => false
-- The generated signature clauses follow: two membership clauses, one D_all
-- clause, one predicate fact.
#guard (guarded.clauses.filter (·.source == .signature)).length = 4

-- v(Y) alone: the guard on the unbound Y delays and nothing binds Y, so the run
-- flounders: unknown, never exhausted.
def vAlone := solve guarded (query [0] [] (atom .v [.var 0]))
#guard floundered vAlone

-- v(Y) ∧ q(Y) under q(succ(zero)): the guard delays inside v's clause, v's frame
-- completes, and the caller's q(Y) binds Y and wakes it. The woken guard is
-- proved from the generated clauses D_all(x) :- isNat(x) and isNat(succ(x)) :- isNat(x).
def vCaller := solve guarded (query [0] [atom .q [succ zero]] (.conj (atom .v [.var 0]) (atom .q [.var 0])))
#guard vCaller.kind = .success
#guard answerIs vCaller 0 (succ zero)
#guard match vCaller.proof? with
  | some proof => proof.deferred.length == 1 && proof.tree.refs.isEmpty
  | none => false
-- A binding outside the range refutes the woken guard: exhausted.
#guard (solve guarded (query [0] [atom .q [k .b]] (.conj (atom .v [.var 0]) (atom .q [.var 0])))).kind = .exhausted

-- An explicit domain list guards with the disjunction isNat(X) ∨ false. It
-- delays as a whole; once bound, a value outside the domain refutes it, and the
-- trailing false is a miss, not a gap: exhausted, also on resume.
def explicitProgram : Program Nat Nat Sym :=
  match Program.build .ha snapshot names rules [⟨rule (atom .w [.var 50]) [], Elaboration.defaultRanges,
      fun _ => .data [.nat]⟩] with
  | .ok program => program
  | .error _ => ⟨[], fun _ => false⟩
#guard match explicitProgram.clauses with
  | ⟨.lowered 0, .definite (.app .w [.var 50]) [.disj (.app .isNat [.var 50]) .falsity]⟩ :: _ => true
  | _ => false
def explicitCaller (value : T) := solve explicitProgram (query [0] [atom .q [value]]
  (.conj (atom .w [.var 0]) (atom .q [.var 0])))
#guard (explicitCaller (k .b)).kind = .exhausted
#guard answerIs (explicitCaller (succ zero)) 0 (succ zero)
#guard (resume explicitProgram (explicitCaller (succ zero))).kind = .exhausted
#guard floundered (solve explicitProgram (query [0] [] (atom .w [.var 0])))

-- A predicate range guards with isPred(P), proved from the registered fact.
def predicateProgram : Program Nat Nat Sym :=
  match Program.build .ha snapshot names rules [⟨rule (atom .w [.var 50]) [], Elaboration.defaultRanges,
      fun _ => .predicate 1⟩] with
  | .ok program => program
  | .error _ => ⟨[], fun _ => false⟩
#guard (solve predicateProgram (query [0] [atom .e [k .p]] (.conj (atom .w [.var 0]) (atom .e [.var 0])))).kind
  = .success
#guard (solve predicateProgram (query [0] [atom .e [k .q]] (.conj (atom .w [.var 0]) (atom .e [.var 0])))).kind
  = .exhausted

-- A query goal over an explicit domain: ∃x:nat. q(x) lowers to
-- ∃x. ((isNat(x) ∨ false) ∧ q(x)). The guard waits for q(x) to bind x.
def explicitQuery : T :=
  match lowerQuery (Literal := Nat) .ha snapshot.naming (fun path => if path = [] then .data [.nat] else .allData)
      Elaboration.defaultRanges [] (.existsVar 70 (atom .q [.var 70])) with
  | .ok (_, goal) => goal
  | .error _ => .truth
#guard (solve guarded (query [] [atom .q [succ zero]] explicitQuery)).kind = .success
#guard (solve guarded (query [] [atom .q [k .b]] explicitQuery)).kind = .exhausted

-- A guard or formula-variable goal identical to an assumption closes by it
-- instead of waiting.
#guard rulesOf (solve guarded (query [0] [atom .allData [.var 0]] (atom .allData [.var 0]))) = some [.assumption]
#guard rulesOf (solve guarded (query [0] [.var 0] (.var 0))) = some [.assumption]

-- The trailing false of an explicit domain guard is never tried, even with a
-- denial clause in the KB that would loop: the out-of-domain value is a miss.
def denialGuard : Program Nat Nat Sym :=
  match Program.build .ha snapshot names rules [⟨rule (atom .w [.var 50]) [], Elaboration.defaultRanges,
      fun _ => .data [.nat]⟩, carrier (.goal [k .r]), carrier (rule (k .r) [k .r])] with
  | .ok program => program
  | .error _ => ⟨[], fun _ => false⟩
#guard (solve denialGuard (query [0] [atom .q [k .b]] (.conj (atom .w [.var 0]) (atom .q [.var 0])))).kind = .exhausted

-- num(X) :- natDomain(X): the guard waits, and the member goal appended after
-- the body is an ordinary goal that enumerates the domain by its clauses.
def numRun := solve guarded (query [0] [] (atom .num [.var 0]))
#guard answerIs numRun 0 zero
#guard answerIs (resume guarded numRun) 0 (succ zero)
#guard answerIs (resume guarded (resume guarded numRun)) 0 (succ (succ zero))

-- A predicate binder left at the data default is rejected and reported, never
-- lowered with a default range: P applied by ho_apply needs `.predicate 1`.
def callClause : Clause := rule (atom .u [.var 60]) [.hoApply .ha (.var 60) [zero]]
#guard match Program.build (Literal := Nat) .ha snapshot names rules (sources ++ [data callClause]) with
  | .error (.clause 4) => true
  | _ => false
#guard match Program.build (Literal := Nat) .ha snapshot names rules
    (sources ++ [⟨callClause, Elaboration.defaultRanges, fun _ => .predicate 1⟩]) with
  | .ok program => program.clauses.length == 9
  | .error _ => false
-- So is a query goal: ∀P. ho_apply(P, zero) under the data default.
#guard match lowerQuery (Literal := Nat) .ha snapshot.naming Elaboration.defaultRanges Elaboration.defaultRanges []
    (.forallVar 60 (.hoApply .ha (.var 60) [zero])) with
  | .error .goal => true
  | _ => false

/-! ### Loops and gaps -/

-- R04: p :- p before the fact p. Depth-first selection keeps re-entering the
-- first clause; the budget runs out. An interrupted run is no result about p.
#guard (solve (plain [rule (k .p) [k .p], fact (k .p)]) (query [] [] (k .p))).kind = .interrupted
-- With the fact first, every resume finds another proof, through one more use
-- of p :- p; the search never reports exhaustion.
def loopProgram : Program Nat Nat Sym := plain [fact (k .p), rule (k .p) [k .p]]
def loopFirst := solve loopProgram (query [] [] (k .p))
#guard rulesOf loopFirst = some [.clause, .truth]
#guard rulesOf (resume loopProgram loopFirst) = some [.clause, .conjIntro, .clause, .truth, .truth]
#guard (resume loopProgram (resume loopProgram loopFirst)).kind = .success

-- A gap among the candidates keeps the others: p(op(b)) cannot be compared with
-- p(a), but the fact p(a) still answers; the gap is recorded, so resuming is
-- unknown, never exhausted.
def withCall : Program Nat Nat Sym := plain [fact (atom .p [k .a]), fact (atom .p [call (k .b)])]
#guard (solve withCall (query [] [] (atom .p [k .a]))).kind = .success
#guard (resume withCall (solve withCall (query [] [] (atom .p [k .a])))).kind = .unknown

-- ho_apply against a direct application needs conversion (S11): a gap, both for
-- a ho_apply goal facing a direct fact and for a flexible head facing a direct goal.
#guard (solve (plain [fact (atom .p [k .a]), fact (atom .q [k .p])]) (query [0] []
  (.conj (atom .q [.var 0]) (.hoApply .ha (.var 0) [k .a])))).kind = .unknown
def flexibleHead : Program Nat Nat Sym := plain [fact (atom .p [k .a]), fact (.hoApply .ha (.var 50) [k .a])]
#guard (solve flexibleHead (query [] [] (atom .p [k .a]))).kind = .success
#guard (resume flexibleHead (solve flexibleHead (query [] [] (atom .p [k .a])))).kind = .unknown

-- An alpha-variant match is an unsupported capability: a gap, not failure. A
-- plain clash is a miss.
#guard (solve (plain [fact (atom .p [.forallVar 1 (atom .q [.var 1])])]) (query [] []
  (atom .p [.forallVar 2 (atom .q [.var 2])]))).kind = .unknown
#guard (solve (plain [fact (atom .p [k .b])]) (query [] [] (atom .p [k .a]))).kind = .exhausted

-- Falsity is an ordinary goal: an assumed false, a local rule concluding false
-- (a negation), or a denial clause proves it. With none of them it is a miss.
#guard rulesOf (solve (plain []) (query [] [.falsity] .falsity)) = some [.assumption]
#guard rulesOf (solve (plain []) (query [] [.forallVar 1 (.imp (atom .p [.var 1]) .falsity), atom .p [k .a]] .falsity))
  = some [.impElim, .forallElim, .assumption, .assumption]
def denial : Program Nat Nat Sym :=
  plain [.goal [atom .p [.var 50], atom .q [.var 50]], fact (atom .p [k .a]), fact (atom .p [k .b]), fact (atom .q [k .b])]
#guard rulesOf (solve denial (query [] [] .falsity))
  = some [.goalClause, .conjIntro, .clause, .truth, .conjIntro, .clause, .truth, .truth]
#guard (resume denial (solve denial (query [] [] .falsity))).kind = .exhausted
#guard (solve (plain []) (query [] [] .falsity)).kind = .exhausted

-- NAF is outside this slice: a gap.
#guard (solve (plain []) (query [] [] (.defaultNeg (k .p)))).kind = .unknown

/-! ### Reconstruction -/

-- Every successful run reconstructs `Derives` for its answer instance, in the
-- program's KB and, for a built program, in E(KB).
example {fuel : Nat} {proof : CompletedProof Nat Nat Sym Unit Nat} {resume : State Nat Nat Sym Unit Nat}
    (ran : run (positive .ha rProgram) fuel
      (query [0] [atom .s [k .a], atom .t [k .b], atom .u [k .b]] (.conj (atom .r [.var 0]) (atom .u [.var 0]))) =
        .success proof resume) :
    Derives Sym.ha rProgram.kb ([atom .s [k .a], atom .t [k .b], atom .u [k .b]].map proof.store.resolve)
      (proof.store.resolve (.conj (atom .r [.var 0]) (atom .u [.var 0]))) :=
  positive_reconstructs (naf := NafFailure.disabled) rProgram fuel 0 [0] _ _ ran

example {program : Program Nat Nat Sym} (built : Program.build .ha snapshot names rules sources = .ok program)
    {fuel : Nat} {proof : CompletedProof Nat Nat Sym Unit Nat} {resume : State Nat Nat Sym Unit Nat}
    (ran : run (positive .ha program) fuel (query [0] [atom .q [succ zero]]
      (.conj (atom .v [.var 0]) (atom .q [.var 0]))) = .success proof resume) :
    Derives Sym.ha (elaboratedKb snapshot names sources) ([atom .q [succ zero]].map proof.store.resolve)
      (proof.store.resolve (.conj (atom .v [.var 0]) (atom .q [.var 0]))) :=
  positive_reconstructs_elaborated built listed fuel 0 [0] _ _ ran

-- Resuming keeps the state valid and sound, so every further answer is
-- reconstructed too.
example {fuel : Nat} {state resume : State Nat Nat Sym Unit Nat} {proof : CompletedProof Nat Nat Sym Unit Nat}
    (valid : state.Valid) (sound : state.Sound Sym.ha pFacts.kb NafFailure.disabled)
    (ran : run (positive .ha pFacts) fuel state = .success proof resume) :
    ReadDerives Sym.ha pFacts.kb NafFailure.disabled proof.store proof.root ∧ resume.Valid ∧
      resume.Sound Sym.ha pFacts.kb NafFailure.disabled :=
  run_reconstructs _ (positive_sound pFacts) fuel valid sound ran

-- A guard on an unbound flexible name delays, validly, unless an assumption it
-- reads as closes it.
example {obligation : Obligation Nat Nat Sym} {store : Store Nat Nat Sym}
    (reads : store.resolve obligation.goal = (.app .allData [.var 0] : T)) (unbound : store.assignable 0 = true)
    (unassumed : identities (Certificate := Unit) (.app .allData [.var 0]) (store.readContext obligation) = []) :
    positive (Certificate := Unit) .ha guarded obligation store = .delay [0] ∧ store.delayable [0] = true :=
  positive_guard reads (by decide) unbound unassumed

end PositiveTests
