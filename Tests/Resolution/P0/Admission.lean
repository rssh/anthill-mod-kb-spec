import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Machine AnthillModKbSpec.Admission AnthillModKbSpec.InductiveDomains
  AnthillModKbSpec.AdmissionSignature

namespace P0AdmissionTests

/-! Executable traces of S07: P0 admission and total evaluation on the shared
machine. Each `#guard` evaluates compiled code: `check` decides admission
before any rule runs, and `Plan.run` runs a Ready plan with the P0 command
set. The examples at the end instantiate the run theorems. -/

inductive Sym where
  | p | q | r | s | w | a | b | c | zero | succ | isNat | allData | isPred | call | ha
  deriving DecidableEq, Repr

abbrev T := Term Nat Nat Sym
abbrev Clause := HornClause Nat Nat Sym

def k (symbol : Sym) : T := .app symbol []
def atom (symbol : Sym) (args : List T) : T := .app symbol args
def fact (head : T) : Clause := .definite head []
def rule (head : T) (body : List T) : Clause := .definite head body
def naf (goal : T) : T := .defaultNeg goal

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

/-- The listed rules are exactly the declared ones, and the generated clauses
name arguments distinctly: the input contract `check` relies on. -/
theorem listed : ∀ rule ∈ rules, snapshot.signature.data.definitions rule := by
  intro rule member
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at member
  exact member

theorem complete : ∀ rule, snapshot.signature.data.definitions rule → rule ∈ rules := by
  intro rule declared
  rcases declared with rfl | rfl <;> simp [rules]

theorem distinct : DistinctNames snapshot.signature.data.definitions names :=
  DistinctNames.of_injective fun first second same => by simpa [names] using same

def zero : T := k .zero
def succ (n : T) : T := atom .succ [n]

/-- The effective program of ground KB clauses: the clauses as lowering gives
them, then the generated signature clauses, as `Program.build` lays them out. -/
def kb (clauses : List Clause) : Program Nat Nat Sym :=
  ⟨clauses.mapIdx (fun index clause => ⟨.lowered index, clause⟩) ++
    (signatureClauses snapshot names rules).map (⟨.signature, ·⟩), guardSymbol snapshot⟩

def input (clauses : List Clause) (context : List T) (goal : T) : Input Dom Nat Nat Sym :=
  ⟨snapshot, names, rules, listed, complete, distinct, kb clauses, fun _ => guardSymbol_iff, context, goal⟩

abbrev Admitted := Result Dom Nat Nat Sym .ha
abbrev Run := Outcome Nat Nat Sym (P0.Certificate Nat Nat Sym) (Input Dom Nat Nat Sym)

def admission (query : Input Dom Nat Nat Sym) : Admitted := check .ha query

def ready : Admitted → Bool
  | .ready _ => true
  | _ => false

/-- The requests of a NeedsEvidence answer: site, term path, capability. -/
def requested : Admitted → List (Site × List Nat × Capability)
  | .needsEvidence request more => (request :: more).map fun request => (request.site, request.path, request.capability)
  | _ => []

def invalid : Admitted → Option Diagnostic
  | .invalid diagnostic => some diagnostic
  | _ => none

/-- Run a Ready plan; `none` if admission did not answer Ready. -/
def solve (query : Input Dom Nat Nat Sym) (fuel : Nat := 500) : Option Run :=
  match admission query with
  | .ready plan => some (plan.run fuel)
  | _ => none

def kindOf (outcome : Option Run) : Option OutcomeKind := outcome.map Outcome.kind

def rulesOf (outcome : Option Run) : Option (List RuleId) := outcome.bind fun run => run.proof?.map (·.tree.rules)

/-- The certificates the success tree's NAF nodes retain. -/
def certificates (outcome : Option Run) : List (P0.Certificate Nat Nat Sym) :=
  match outcome.bind Outcome.proof? with
  | some proof => proof.tree.closedWorld.map (·.certificate)
  | none => []

mutual
def nodes : ProofTree Nat Nat Sym (P0.Certificate Nat Nat Sym) →
    List (RuleApp Nat Nat Sym (P0.Certificate Nat Nat Sym) × Obligation Nat Nat Sym)
  | .node rule obligation _ subproofs => (rule, obligation) :: nodesOf subproofs
  | .deferred _ _ => []

def nodesOf : List (ProofTree Nat Nat Sym (P0.Certificate Nat Nat Sym)) →
    List (RuleApp Nat Nat Sym (P0.Certificate Nat Nat Sym) × Obligation Nat Nat Sym)
  | [] => []
  | tree :: trees => nodes tree ++ nodesOf trees
end

/-- Clause applications of the success tree in preorder, with the goals they prove. -/
def clauseGoals (outcome : Option Run) : List T :=
  match outcome.bind Outcome.proof? with
  | some proof => (nodes proof.tree).filterMap fun | (.clause _ _, obligation) => some obligation.goal | _ => none
  | none => []

def same (left right : List T) : Bool := left.length == right.length && (left.zip right).all fun (l, r) => identical l r

/-! ### R01: clause and fact evidence -/

-- p(a) :- q(a) and the fact q(a): Ready, and the run succeeds with one clause
-- node per use; the body's fact closes by its own clause.
def r01 := input [rule (atom .p [k .a]) [atom .q [k .a]], fact (atom .q [k .a])] [] (atom .p [k .a])
#guard ready (admission r01)
#guard kindOf (solve r01) = some .success
#guard rulesOf (solve r01) = some [.clause, .conjIntro, .clause, .truth, .truth]
-- The same atom as a local fact closes by assumption instead.
#guard rulesOf (solve (input [rule (atom .p [k .a]) [atom .q [k .a]]] [atom .q [k .a]] (atom .p [k .a])))
  = some [.clause, .conjIntro, .assumption, .truth]

/-! ### R02: success after a failed candidate -/

-- p :- q, p :- r, and r: the first candidate fails at q, which has no
-- candidate; the second succeeds; p completes once.
def r02 := input [rule (k .p) [k .q], rule (k .p) [k .r], fact (k .r)] [] (k .p)
#guard kindOf (solve r02) = some .success
#guard same (clauseGoals (solve r02)) [k .p, k .r]

/-! ### All-candidate failure -/

-- Both candidates for p fail: the run is exhausted, and `run_correct_of_p0`
-- gives a complete-failure certificate.
def allFail := input [rule (k .p) [k .q], rule (k .p) [k .r]] [] (k .p)
#guard ready (admission allFail)
#guard kindOf (solve allFail) = some .exhausted
-- The run is total: a smaller budget may interrupt it, a large one never does.
#guard kindOf (solve allFail 2) = some .interrupted

/-! ### R03: NAF with no defining clause -/

-- p :- naf q with no clause for q: Ready, and the success tree holds one NAF
-- node whose certificate names the exact clauses, context, and operand.
def r03 := input [rule (k .p) [naf (k .q)]] [] (k .p)
#guard ready (admission r03)
#guard kindOf (solve r03) = some .success
#guard rulesOf (solve r03) = some [.clause, .conjIntro, .defaultNegIntro, .truth]
#guard match certificates (solve r03) with
  | [certificate] => identical certificate.operand (k .q) && certificate.context.isEmpty &&
      certificate.clauses.length == 1
  | _ => false
-- The certificate carries a finite failure witness that checks on the
-- certificate's own clauses and context, with no search: q has no clause.
#guard match certificates (solve r03) with
  | [certificate] => certificate.check .ha && (match certificate.witness.get with
      | some (.atom .nil) => true
      | _ => false)
  | _ => false

/-! ### Nested NAF -/

-- naf naf q with the fact q: the inner operand q succeeds, so the inner NAF
-- fails and its barrier is cut; the outer operand is then exhausted, so the
-- outer NAF succeeds. Only the outer node is in the tree.
#guard rulesOf (solve (input [rule (k .p) [naf (naf (k .q))], fact (k .q)] [] (k .p)))
  = some [.clause, .conjIntro, .defaultNegIntro, .truth]
#guard match certificates (solve (input [rule (k .p) [naf (naf (k .q))], fact (k .q)] [] (k .p))) with
  | [certificate] => identical certificate.operand (naf (k .q)) && certificate.check .ha
  | _ => false
-- The witness for naf q fails by q's success, which names q's fact.
#guard match certificates (solve (input [rule (k .p) [naf (naf (k .q))], fact (k .q)] [] (k .p))) with
  | [certificate] => match certificate.witness.get with
      | some (.negation (.clause [] .truth)) => true
      | _ => false
  | _ => false
-- A deeper witness: p fails because both its clauses fail, and it checks.
#guard match certificates (solve (input [rule (k .p) [k .q], rule (k .p) [k .r, k .s], fact (k .r),
    rule (k .w) [naf (k .p)]] [] (k .w))) with
  | [certificate] => certificate.check .ha && (match certificate.witness.get with
      | some (.atom (.cons _ (.cons _ .nil))) => true
      | _ => false)
  | _ => false
-- Without q, the inner NAF succeeds, so the outer fails: exhausted.
#guard kindOf (solve (input [rule (k .p) [naf (naf (k .q))]] [] (k .p))) = some .exhausted
-- A NAF goal in a conjunction after a candidate choice: p(X)-like choice over
-- ground clauses, then naf: r :- s(a), naf q(a); r :- s(b), naf q(b) with q(a).
def choiceThenNaf := input
  [rule (k .r) [atom .s [k .a], naf (atom .q [k .a])], rule (k .r) [atom .s [k .b], naf (atom .q [k .b])],
    fact (atom .s [k .a]), fact (atom .s [k .b]), fact (atom .q [k .a])] [] (k .r)
#guard kindOf (solve choiceThenNaf) = some .success
#guard same (clauseGoals (solve choiceThenNaf)) [k .r, atom .s [k .b]]

/-! ### R04, R05: cycles are rejected before execution -/

-- p :- p beside the fact p: NeedsEvidence, an acyclic strategy for clause 0,
-- even though selecting the fact would prove p. P3 may admit that strategy.
#guard requested (admission (input [rule (k .p) [k .p], fact (k .p)] [] (k .p))) = [(.head 0, [], .acyclicStrategy)]
-- p :- naf p: the cycle through NAF is rejected; no two-valued model is built.
#guard requested (admission (input [rule (k .p) [naf (k .p)]] [] (k .p))) = [(.head 0, [], .acyclicStrategy)]
-- A positive-negative cycle across two clauses names both.
#guard requested (admission (input [rule (k .p) [naf (k .q)], rule (k .q) [k .p]] [] (k .p)))
  = [(.head 0, [], .acyclicStrategy), (.head 1, [], .acyclicStrategy)]
-- An acyclic program with a cycle elsewhere in it is still rejected: the whole
-- program is checked, not one successful branch.
#guard requested (admission (input [fact (k .p), rule (k .q) [k .q]] [] (k .p))) = [(.head 1, [], .acyclicStrategy)]
-- Only the clauses on the cycle are named: s :- p depends on the cycle p, q
-- but is not on it, and needs no strategy of its own.
#guard requested (admission (input [rule (k .s) [k .p], rule (k .p) [k .q], rule (k .q) [k .p]] [] (k .s)))
  = [(.head 1, [], .acyclicStrategy), (.head 2, [], .acyclicStrategy)]

/-! ### R06: stale context evidence -/

-- naf q established in the empty context; its certificate names that context.
def nafEmpty := input [] [] (naf (k .q))
#guard match certificates (solve nafEmpty) with
  | [certificate] => certificate.context.isEmpty
  | _ => false
-- Add q to the context: a new check and run, and the NAF goal now fails. The
-- old certificate names the empty context, so it is not valid for the new one
-- (`P0.NegativeCertificate.stale`).
#guard kindOf (solve (input [] [k .q] (naf (k .q)))) = some .exhausted

/-! ### Formulas outside P0 get actionable requests -/

-- An answer variable: a ground instance is needed.
#guard requested (admission (input [] [] (atom .p [.var 0]))) = [(.goal, [0], .groundInstance)]
-- An implication goal and a disjunction under a conjunction: scoped proof.
#guard requested (admission (input [] [] (.imp (k .q) (k .p)))) = [(.goal, [], .scopedProof)]
#guard requested (admission (input [] [] (.conj (k .p) (.disj (k .q) (k .r))))) = [(.goal, [1], .scopedProof)]
-- An equality goal, a dictionary call inside data, an application by ho_apply
-- inside data: their capabilities, at their term paths.
#guard requested (admission (input [] [] (.equal (k .a) (k .a)))) = [(.goal, [], .equality)]
#guard requested (admission (input [] [] (atom .p [k .a, .dictionaryCall (k .b) [] .call []])))
  = [(.goal, [1], .dictionaryLaw)]
#guard requested (admission (input [] [] (atom .p [atom .ha [k .q, k .a]]))) = [(.goal, [0], .hoApplyConversion)]
-- A non-atomic assumption needs left rules; a denial clause, contradiction
-- search; a compound head, its own matching; a KB clause defining a guard
-- symbol would change what the guard means.
#guard requested (admission (input [] [.conj (k .p) (k .q)] (k .p))) = [(.assumption 0, [], .scopedProof)]
#guard requested (admission (input [.goal [k .p]] [] (k .p))) = [(.head 0, [], .contradiction)]
#guard requested (admission (input [rule (.forallVar 1 (atom .p [.var 1])) []] [] (k .p))) = [(.head 0, [], .compoundHead)]
#guard requested (admission (input [fact (atom .isNat [k .a])] [] (k .p))) = [(.head 0, [], .guardDefinition)]
-- Calls, equalities, and literals get their own capability at every site.
#guard requested (admission (input [fact (.dictionaryCall (k .b) [] .call [])] [] (k .p)))
  = [(.head 0, [], .dictionaryLaw)]
#guard requested (admission (input [] [.equal (k .a) (k .a)] (k .p))) = [(.assumption 0, [], .equality)]
#guard requested (admission (input [] [.lit 3] (k .p))) = [(.assumption 0, [], .termKind)]
-- Every request is listed, not just the first.
#guard (requested (admission (input [rule (k .p) [atom .q [.var 3]]] [.var 1] (.imp (k .p) (k .q))))).length = 3

/-! ### Guards are decided, not searched -/

/-- A built effective program: its generated signature clauses are non-ground
and recursive (`isNat(succ(X)) :- isNat(X)`), and P0 does not reject it for that. -/
def carrier (clause : Clause) : SourceClause Dom Nat Nat Sym := ⟨clause, Elaboration.defaultRanges, fun _ => .carrier⟩

def builtInput (sources : List (SourceClause Dom Nat Nat Sym)) (context : List T) (goal : T) : Input Dom Nat Nat Sym :=
  match built : Program.build .ha snapshot names rules sources with
  | .ok program => ⟨snapshot, names, rules, listed, complete, distinct, program, Program.build_guard built, context, goal⟩
  | .error _ => input [] [] .falsity

def guarded := [carrier (rule (k .w) [atom .isNat [succ zero]]), carrier (rule (k .s) [atom .isNat [k .b]])]
#guard ready (admission (builtInput guarded [] (k .w)))
-- The member guard has its fact, decided structurally; the non-member has none.
#guard kindOf (solve (builtInput guarded [] (k .w))) = some .success
#guard kindOf (solve (builtInput guarded [] (k .s))) = some .exhausted
-- D_all through a declared domain; P_1 for the registered reference p only.
#guard kindOf (solve (builtInput [] [] (atom .allData [succ (succ zero)]))) = some .success
#guard kindOf (solve (builtInput [] [] (atom .isPred [k .p]))) = some .success
#guard kindOf (solve (builtInput [] [] (atom .isPred [k .q]))) = some .exhausted
-- A guard used as a NAF operand: naf isNat(b) holds.
#guard kindOf (solve (builtInput [] [] (naf (atom .isNat [k .b])))) = some .success
-- Guards follow the generated clauses through assumptions too: under the
-- assumption isNat(b), isNat(succ(b)) holds by succ's membership clause, and
-- its NAF fails, as in the original program.
#guard kindOf (solve (builtInput [] [atom .isNat [k .b]] (atom .isNat [succ (k .b)]))) = some .success
#guard kindOf (solve (builtInput [] [atom .isNat [k .b]] (naf (atom .isNat [succ (k .b)])))) = some .exhausted
-- D_all through an assumed membership; a membership assumed of another term
-- does not leak.
#guard kindOf (solve (builtInput [] [atom .isNat [k .b]] (atom .allData [succ (k .b)]))) = some .success
#guard kindOf (solve (builtInput [] [atom .isNat [k .c]] (atom .isNat [succ (k .b)]))) = some .exhausted

-- A rule list missing a declared rule, or listing an undeclared one, cannot
-- form an input: the contract asks for exactly the declared rules.
example : ¬ ∀ rule, snapshot.signature.data.definitions rule → rule ∈ [succRule] := fun complete => by
  have missing := complete zeroRule (.inl rfl)
  simp [zeroRule, succRule] at missing
example : ¬ ∀ rule ∈ [zeroRule, succRule, ⟨.nat, .b, []⟩], snapshot.signature.data.definitions rule := fun listed => by
  have undeclared := listed ⟨.nat, .b, []⟩ (by simp)
  simp [snapshot, family, zeroRule, succRule] at undeclared

/-! ### Invalid declarations -/

-- A clause marked as generated from the signature that it does not generate.
def forged : Input Dom Nat Nat Sym :=
  ⟨snapshot, names, rules, listed, complete, distinct, ⟨[⟨.signature, fact (atom .isNat [k .a])⟩], guardSymbol snapshot⟩,
    fun _ => guardSymbol_iff, [], k .p⟩
#guard invalid (admission forged) = some (.signatureClause 0)
-- A program missing a generated clause is not the snapshot's effective
-- program: `w :- isNat(succ(zero))` alone would decide its guard from the
-- signature although the program cannot derive it.
def bare : Input Dom Nat Nat Sym :=
  ⟨snapshot, names, rules, listed, complete, distinct,
    ⟨[⟨.lowered 0, rule (k .w) [atom .isNat [succ zero]]⟩], guardSymbol snapshot⟩, fun _ => guardSymbol_iff, [], k .w⟩
#guard invalid (admission bare) = some (.missingSignatureClause 0)
#guard ready (admission (input [rule (k .w) [atom .isNat [succ zero]]] [] (k .w)))
-- Being outside P0 is never invalid.
#guard invalid (admission (input [] [] (.imp (k .q) (k .p)))) = none

/-! ### Ground NAF over `positive`, beyond P0

`Strategy.withNegation` on the shared S06 strategy, outside a plan: a non-ground
program, a context with answer names, delayed guards. -/

abbrev Machine := Outcome Nat Nat Sym Unit Nat

def program (clauses : List Clause) (guard : Sym → Bool := fun _ => false) : Program Nat Nat Sym :=
  ⟨clauses.mapIdx fun index clause => ⟨.lowered index, clause⟩, guard⟩

def negating (program : Program Nat Nat Sym) : Strategy Nat Nat Sym Unit :=
  (positive .ha program).withNegation fun _ _ => ()

def runNegating (program : Program Nat Nat Sym) (flexibles : List Nat) (context : List T) (goal : T) : Machine :=
  run (negating program) 400 (State.init 0 flexibles context goal)

-- The base strategy's exact candidates come first: ex falso under an assumed
-- falsity, and an assumed `naf q`, prove `naf q` although q is a fact.
#guard (runNegating (program [fact (k .q)]) [] [.falsity] (naf (k .q))).kind = .success
#guard (runNegating (program [fact (k .q)]) [] [naf (k .q)] (naf (k .q))).kind = .success
-- NAF under an assumption with an unbound answer name is not ground: the
-- operand's search could bind X. It is a gap, never an exhaustion.
#guard (runNegating (program []) [] [] (.existsVar 9 (.imp (atom .p [.var 9]) (naf (atom .p [k .a]))))).kind
  = .unknown
-- An answer name bound before the NAF is read through its binding: r(a)
-- binds X, so naf q(X) is the ground naf q(a), decided either way however
-- the conjunction nests. An operand naming X while X is unbound is a gap.
#guard (runNegating (program [fact (atom .r [k .a])]) [7] [] (.conj (atom .r [.var 7]) (naf (atom .q [.var 7])))).kind
  = .success
#guard (runNegating (program [fact (atom .r [k .a]), fact (atom .q [k .a])]) [7] []
  (.conj (atom .r [.var 7]) (naf (atom .q [.var 7])))).kind = .exhausted
#guard (runNegating (program [fact (atom .r [k .a])]) [] [] (.existsVar 7 (.conj (atom .r [.var 7]) (naf (atom .q [.var 7]))))).kind
  = .success
#guard (runNegating (program [fact (atom .r [k .a])]) [7] [] (.conj (naf (atom .q [.var 7])) (atom .r [.var 7]))).kind
  = .unknown
-- A rigid parameter is not ground either: it stands for every value. With the
-- fact p(a), p(X) fails for the eigenvariable X, but that does not show
-- ∀X. naf p(X): it is a gap, not a success. The same for a rigid name in an
-- assumption: under p(X), q(a) :- p(c) fails for the eigenvariable, but not
-- for X = c. A free name of the query is a rigid parameter too.
#guard (runNegating (program [fact (atom .p [k .a])]) [] [] (.forallVar 9 (naf (atom .p [.var 9])))).kind = .unknown
#guard (runNegating (program [rule (atom .q [k .a]) [atom .p [k .c]]]) [] []
  (.forallVar 9 (.imp (atom .p [.var 9]) (naf (atom .q [k .a]))))).kind = .unknown
#guard (runNegating (program [fact (atom .p [k .a])]) [] [] (naf (atom .p [.var 9]))).kind = .unknown
-- Ground NAF decides no operand whose search delays a goal. Here the guard
-- isNat(Y) delays inside the operand and is proved after r binds Y: q is
-- proved, so naf q fails, but the NAF is recorded as a gap and the run is
-- unknown, not exhausted.
def wokenGuard := program [rule (k .q) [atom .isNat [.var 7], atom .r [.var 7]], fact (atom .r [zero]),
  fact (atom .isNat [zero])] (· == .isNat)
#guard (runNegating wokenGuard [] [] (k .q)).kind = .success
#guard (runNegating wokenGuard [] [] (naf (k .q))).kind = .unknown
-- The same when the operand fails after its delayed guard woke: s has no
-- clause, so q is exhausted, but naf q is not proved: unknown.
def wokenThenFails := program [rule (k .q) [atom .isNat [.var 7], atom .r [.var 7], k .s], fact (atom .r [zero]),
  fact (atom .isNat [zero])] (· == .isNat)
#guard (runNegating wokenThenFails [] [] (k .q)).kind = .exhausted
#guard (runNegating wokenThenFails [] [] (naf (k .q))).kind = .unknown
-- Without a delay, the same operand is decided: naf q holds.
#guard (runNegating (program [rule (k .q) [atom .r [.var 7], k .s], fact (atom .r [zero])]) [] [] (naf (k .q))).kind
  = .success

/-! ### Deciding queries, and every query of a program -/

/-- The answer of a Ready plan; `none` if admission did not answer Ready. -/
def decided (query : Input Dom Nat Nat Sym) : Option Bool :=
  match admission query with
  | .ready plan => some plan.answer
  | _ => none

#guard decided r01 = some true
#guard decided (input [rule (k .p) [k .q], rule (k .p) [k .r]] [] (k .p)) = some false
#guard decided r03 = some true
#guard decided (input [rule (k .p) [naf (k .q)], fact (k .q)] [] (k .p)) = some false

def decides : ProgramResult Nat Nat Sym → Bool
  | .decides => true
  | _ => false

theorem decides_iff {result : ProgramResult Nat Nat Sym} : decides result = true ↔ result = .decides := by
  cases result <;> simp [decides]

def programInvalid : ProgramResult Nat Nat Sym → Option Diagnostic
  | .invalid diagnostic => some diagnostic
  | _ => none

def programRequested : ProgramResult Nat Nat Sym → List (Site × List Nat × Capability)
  | .needsEvidence request more => (request :: more).map fun request => (request.site, request.path, request.capability)
  | _ => []

/-- A program of KB clauses, without a query. -/
def base (clauses : List Clause) : ProgramInput Dom Nat Nat Sym := (input clauses [] .truth).base

/-- The answer to a query on a program, if the query is Ready. -/
def asked (program : ProgramInput Dom Nat Nat Sym) (context : List T) (goal : T) : Option Bool :=
  match check .ha (program.ask context goal) with
  | .ready plan => some plan.answer
  | _ => none

-- A ground acyclic program decides every P0 query; the check takes no query.
def chain := base [rule (k .p) [k .q], fact (k .q)]
#guard decides (checkProgram .ha chain)
#guard decides (checkProgram .ha (base [rule (k .p) [naf (k .q)], rule (k .w) [atom .isNat [succ zero]]]))
-- A cycle, or a clause outside P0, is reported, and the check covers no query
-- of that program. That does not make the queries undecidable: with `p :- p`
-- beside the fact `p`, `p` holds.
#guard programRequested (checkProgram .ha (base [rule (k .p) [k .p], fact (k .p)]))
  = [(.head 0, [], .acyclicStrategy)]
#guard programRequested (checkProgram .ha (base [rule (k .p) [naf (k .p)]]))
  = [(.head 0, [], .acyclicStrategy)]
#guard programRequested (checkProgram .ha (base [rule (atom .p [.var 1]) [atom .q [.var 1]]]))
  = [(.head 0, [0], .groundInstance), (.body 0 0, [0], .groundInstance)]
-- The program's declarations are checked as `check` checks them.
#guard programInvalid (checkProgram .ha forged.base) = some (.signatureClause 0)
#guard programInvalid (checkProgram .ha bare.base) = some (.missingSignatureClause 0)
-- Queries on an accepted program are Ready, and decided, also those asking for
-- guard facts the empty query does not: a guard goal, a guard under an assumed
-- membership, and NAF of a guard.
#guard asked chain [k .r] (.conj (k .p) (naf (k .r))) = some false
#guard asked chain [] (.conj (k .p) (naf (k .r))) = some true
#guard asked chain [] (atom .isNat [succ zero]) = some true
#guard asked chain [atom .isNat [k .b]] (atom .isNat [succ (k .b)]) = some true
#guard asked chain [] (naf (atom .isNat [k .b])) = some true
#guard asked chain [] (atom .allData [k .b]) = some false
-- A query outside P0 still asks for evidence on an accepted program.
#guard asked chain [.var 1] (.imp (k .p) (k .q)) = none

/-! ### The theorems, instantiated -/

-- Every plan's run finishes with a success or an exhaustion: a plan carries
-- its admission, so it is a Ready one.
example (plan : Plan Dom Nat Nat Sym .ha) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      (∃ proof resume, plan.run fuel = .success proof resume) ∨ plan.run fuel = .exhausted :=
  run_total_of_p0 plan

-- Success carries a success certificate for the original goal and a `Derives`
-- proof with the exact ground failure provider; exhaustion, a failure certificate.
example {plan : Plan Dom Nat Nat Sym .ha} (admitted : admission r03 = .ready plan) (fuel : Nat) :
    (plan.run fuel = .exhausted → GroundSearch.Fails plan.ground.program plan.ground.context (k .p)) ∧
      ∀ gaps, plan.run fuel ≠ .unknown gaps :=
  ⟨(run_correct_of_p0 admitted fuel).2.1, (run_correct_of_p0 admitted fuel).2.2⟩

-- A plan never asks for a capability during its run.
example (plan : Plan Dom Nat Nat Sym .ha)
    {state : State Nat Nat Sym (P0.Certificate Nat Nat Sym) (Input Dom Nat Nat Sym)}
    (reached : Reaches plan.ground.strategy (plan.ground.init plan.input) state) : state.gaps = [] :=
  (ready_no_missing_capability plan reached).1

-- On a program the check accepts, every P0 query is decided; the kernel
-- evaluates the check.
example :
    ∃ plan, check .ha (chain.ask [] (k .w)) = .ready plan ∧
      (plan.answer = true ↔ GroundSearch.Succeeds plan.ground.program plan.ground.context (k .w)) ∧
      (plan.answer = false ↔ GroundSearch.Fails plan.ground.program plan.ground.context (k .w)) :=
  checkProgram_decides (decides_iff.mp (by decide))
    ⟨.atom (.app (by decide) fun _ member => by cases member), .app (by decide) fun _ member => by cases member⟩
    (fun _ member => by cases member)

end P0AdmissionTests
