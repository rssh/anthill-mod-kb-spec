import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Machine AnthillModKbSpec.Admission AnthillModKbSpec.P1
  AnthillModKbSpec.InductiveDomains AnthillModKbSpec.AdmissionSignature

namespace P1CheckTests

/-! Executable traces of S08: supplied proof trees encoded as `Term`, checked
against the shared rules. Each `#guard` runs the checker; the examples at the
end instantiate the theorems. -/

inductive Sym where
  | p | q | r | w | a | b | c | zero | succ | even | isNat | allData | isPred | ha | lem | loop | custom
  | tag (tag : Tag)
  deriving DecidableEq, Repr

/-- The encoding's symbols: one per tag, distinct by construction. -/
def vocab : Vocabulary Sym := ⟨Sym.tag, fun _ _ same => by cases same; rfl⟩

abbrev T := Term Nat Nat Sym
abbrev Clause := HornClause Nat Nat Sym
abbrev P := Proof Nat Nat Sym

def k (symbol : Sym) : T := .app symbol []
def atom (symbol : Sym) (args : List T) : T := .app symbol args
def fact (head : T) : Clause := .definite head []
def rule (head : T) (body : List T) : Clause := .definite head body
def naf (goal : T) : T := .defaultNeg goal
def succ (n : T) : T := atom .succ [n]
def zero : T := k .zero

def node (rule : Rule Nat Nat Sym) (conclusion : T) (premises : List P := []) : P := .node rule conclusion premises

/-- A checker over a clause list: no NAF evidence check, no derived rule. -/
def plain (clauses : List Clause) : Checker Nat Nat Sym := ⟨⟨.ha, clauses⟩, NafFailure.disabled, none, []⟩

def verdict (checker : Checker Nat Nat Sym) (context : List T) (goal : T) (proof : P)
    (imports : List (Import Nat Nat Sym) := []) : Verdict Sym :=
  checkProof vocab checker imports context goal (encode vocab proof)

/-- The proof of a clause body: a conjunction node per goal, ending in truth. -/
def body : List P → P
  | [] => node .truth .truth
  | proof :: rest => node .conjIntro (.conj proof.conclusion (body rest).conclusion) [proof, body rest]

/-- A clause step: the clause, its instantiation, its conclusion, and proofs of
the instantiated body goals. -/
def step (clause : Clause) (instantiation : List (Nat × T)) (goal : T) (goals : List P) : P :=
  node (.clause clause instantiation) goal [body goals]

/-! ### R25, R29: a valid proof of a formula outside automatic discovery -/

-- ∀1. (p(1) → p(1)): forallIntro with eigenvariable 5, impIntro discharging
-- p(5), and the assumption. P0 has no discovery plan for it.
def identity : T := .forallVar 1 (.imp (atom .p [.var 1]) (atom .p [.var 1]))
def identityProof (eigen : Nat := 5) : P :=
  node (.forallIntro eigen) identity
    [node .impIntro (.imp (atom .p [.var eigen]) (atom .p [.var eigen])) [node .assumption (atom .p [.var eigen])]]
#guard verdict (plain []) [] identity (identityProof) = .accept

/-! ### R26: a rejected proof is no evidence about the goal -/

-- The opened body names another eigenvariable: rejected, although the goal is
-- derivable (the proof above is accepted).
def badOpening : P :=
  node (.forallIntro 5) identity
    [node .impIntro (.imp (atom .p [.var 6]) (atom .p [.var 6])) [node .assumption (atom .p [.var 6])]]
#guard verdict (plain []) [] identity badOpening = .reject
-- A term that is no proof tree at all is rejected for every goal.
#guard checkProof vocab (plain []) [] [] identity .truth = .reject
-- A tree for another goal is rejected for this one.
#guard verdict (plain []) [] (.forallVar 2 (.imp (atom .p [.var 2]) (atom .p [.var 2]))) (identityProof) = .reject

/-! ### R27: assuming the goal, and scope escape -/

-- Closing q by assumption needs q in the context.
#guard verdict (plain []) [] (k .q) (node .assumption (k .q)) = .reject
#guard verdict (plain []) [k .q] (k .q) (node .assumption (k .q)) = .accept
-- The eigenvariable must be fresh for the context: 5 is free in q(5).
#guard verdict (plain []) [atom .q [.var 5]] identity (identityProof 5) = .reject
#guard verdict (plain []) [atom .q [.var 5]] identity (identityProof 6) = .accept
-- A proof under the assumption q, imported as `lem`, re-checks where it is
-- used: it does not hold under the empty context.
def underQ : Import Nat Nat Sym := ⟨.lem, [k .q], k .q, encode vocab (node .assumption (k .q))⟩
#guard verdict (plain []) [] (k .q) (node (.reference .lem) (k .q)) [underQ] = .reject
#guard verdict (plain []) [k .q] (k .q) (node (.reference .lem) (k .q)) [underQ] = .accept

/-! ### R30: explicit rule applications with their parameters -/

-- p(X) :- q(X) instantiated with X := a, and the fact q(a).
def kb : List Clause := [rule (atom .p [.var 0]) [atom .q [.var 0]], fact (atom .q [k .a])]
def qa : P := step (fact (atom .q [k .a])) [] (atom .q [k .a]) []
def pa (value : T := k .a) : P :=
  step (rule (atom .p [.var 0]) [atom .q [.var 0]]) [(0, value)] (atom .p [k .a]) [qa]
#guard verdict (plain kb) [] (atom .p [k .a]) (pa) = .accept
-- The instantiation is part of the node: X := b does not give p(a).
#guard verdict (plain kb) [] (atom .p [k .a]) (pa (k .b)) = .reject
-- A clause the snapshot does not hold is not usable.
#guard verdict (plain [fact (atom .q [k .a])]) [] (atom .p [k .a]) (pa) = .reject
-- A universal assumption used at a witness.
#guard verdict (plain []) [.forallVar 1 (atom .p [.var 1])] (atom .p [k .a])
  (node (.forallElim (k .a)) (atom .p [k .a]) [node .assumption (.forallVar 1 (atom .p [.var 1]))]) = .accept
-- Disjunction elimination needs both cases, each under its own assumption.
#guard verdict (plain []) [.disj (k .p) (k .q)] (.disj (k .q) (k .p))
  (node .disjElim (.disj (k .q) (k .p)) [node .assumption (.disj (k .p) (k .q)),
    node .disjRight (.disj (k .q) (k .p)) [node .assumption (k .p)],
    node .disjLeft (.disj (k .q) (k .p)) [node .assumption (k .q)]]) = .accept
#guard verdict (plain []) [.disj (k .p) (k .q)] (.disj (k .q) (k .p))
  (node .disjElim (.disj (k .q) (k .p)) [node .assumption (.disj (k .p) (k .q)),
    node .disjRight (.disj (k .q) (k .p)) [node .assumption (k .p)],
    node .disjRight (.disj (k .q) (k .p)) [node .assumption (k .q)]]) = .reject

/-! ### Lemma imports -/

-- q(a) is proved once, as `lem`, and referenced in a proof of p(a).
def lemma : Import Nat Nat Sym := ⟨.lem, [], atom .q [k .a], encode vocab qa⟩
def paByLemma : P :=
  step (rule (atom .p [.var 0]) [atom .q [.var 0]]) [(0, k .a)] (atom .p [k .a]) [node (.reference .lem) (atom .q [k .a])]
#guard checkImports vocab (plain kb) [lemma]
#guard verdict (plain kb) [] (atom .p [k .a]) paByLemma [lemma] = .accept
-- Without the lemma the reference needs evidence: the proof is not decided.
#guard verdict (plain kb) [] (atom .p [k .a]) paByLemma = .needsEvidence [.lemma .lem]
-- An unproved claim: the import's term proves something else. A reference
-- stands for the import's statement, so it cannot be used for what the term
-- proves instead.
def claim : Import Nat Nat Sym := ⟨.lem, [], atom .q [k .a], encode vocab (node .truth .truth)⟩
#guard !checkImports vocab (plain kb) [claim]
#guard verdict (plain kb) [] (atom .p [k .a]) paByLemma [claim] = .reject
#guard verdict (plain kb) [] .truth (node (.reference .lem) .truth) [claim] = .reject
-- What a referenced proof needs counts as the reference's: a lemma that uses
-- NAF needs a NAF evidence check.
def negated : Import Nat Nat Sym := ⟨.lem, [], naf (k .q), encode vocab (node (.defaultNegIntro .truth) (naf (k .q)))⟩
#guard verdict (plain kb) [] (naf (k .q)) (node (.reference .lem) (naf (k .q))) [negated] = .needsEvidence [.negation]
-- Each missing capability is listed once.
#guard verdict (plain []) [] (.conj (naf (k .q)) (naf (k .r)))
  (node .conjIntro (.conj (naf (k .q)) (naf (k .r)))
    [node (.defaultNegIntro .truth) (naf (k .q)), node (.defaultNegIntro .truth) (naf (k .r))]) = .needsEvidence [.negation]
-- A proof referencing itself is checked against the older imports only: its
-- own reference needs a proof of `loop` before it, so it is never accepted.
def loop : Import Nat Nat Sym := ⟨.loop, [], k .q, encode vocab (node (.reference .loop) (k .q))⟩
#guard !checkImports vocab (plain kb) [loop]
#guard verdict (plain kb) [] (k .q) (node (.reference .loop) (k .q)) [loop] = .needsEvidence [.lemma .loop]

/-! ### A true recursive theorem whose direct execution is not admitted -/

def two : T := succ (succ zero)
def four : T := succ (succ two)
def evenStep : Clause := rule (atom .even [succ (succ (.var 0))]) [atom .even [.var 0]]
def evenKb : List Clause := [fact (atom .even [zero]), evenStep]
def evenFour : P :=
  step evenStep [(0, two)] (atom .even [four])
    [step evenStep [(0, zero)] (atom .even [two]) [step (fact (atom .even [zero])) [] (atom .even [zero]) []]]
#guard verdict (plain evenKb) [] (atom .even [four]) evenFour = .accept

/-! ### Admission: P0 inputs, supplied proofs, and imported facts -/

inductive Dom where
  | nat
  deriving DecidableEq, Repr

def zeroRule : Rule Dom Sym := ⟨.nat, .zero, []⟩
def succRule : Rule Dom Sym := ⟨.nat, .succ, [.nat]⟩
def family : FiniteFamily Dom Sym := ⟨fun rule => rule = zeroRule ∨ rule = succRule, [.nat], fun domain => by cases domain; simp⟩
def snapshot : SignatureSnapshot Dom Sym := ⟨0, ⟨family, fun _ => .isNat, .allData, fun _ => .isPred, [⟨.p, 1⟩]⟩⟩
def names : Nat → Nat := fun index => 100 + index
def rules : List (Rule Dom Sym) := [zeroRule, succRule]

theorem listed : ∀ rule ∈ rules, snapshot.signature.data.definitions rule := by
  intro rule member
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at member
  exact member

theorem complete : ∀ rule, snapshot.signature.data.definitions rule → rule ∈ rules := by
  intro rule declared
  rcases declared with rfl | rfl <;> simp [rules]

theorem distinct : DistinctNames snapshot.signature.data.definitions names :=
  DistinctNames.of_injective fun first second same => by simpa [names] using same

def generated : List Clause := signatureClauses snapshot names rules

def program (clauses : List Clause) : Program Nat Nat Sym :=
  ⟨clauses.mapIdx (fun index clause => ⟨.lowered index, clause⟩) ++ generated.map (⟨.signature, ·⟩), guardSymbol snapshot⟩

def input (clauses : List Clause) (context : List T) (goal : T) : Input Dom Nat Nat Sym :=
  ⟨snapshot, names, rules, listed, complete, distinct, program clauses, fun _ => guardSymbol_iff, context, goal⟩

def ready : Result Dom Nat Nat Sym .ha → Bool
  | .ready _ => true
  | _ => false

def needsEvidence : Result Dom Nat Nat Sym .ha → Bool
  | .needsEvidence _ _ => true
  | _ => false

/-- The checker for an input's own effective program. -/
def own (query : Input Dom Nat Nat Sym) : Checker Nat Nat Sym := plain (query.program.clauses.map ProgramClause.clause)

-- The identity is outside P0, which asks for evidence; with the supplied proof
-- the same admission check answers it, by checking only.
#guard needsEvidence (check .ha (input [] [] identity))
def admitted (proofs : List T) (checker : Checker Nat Nat Sym := own (input [] [] identity)) : Admitted Dom Nat Nat Sym .ha :=
  admit vocab checker .ha [] (input [] [] identity) proofs
#guard match admitted [] with | .needsEvidence _ [] => true | _ => false
#guard match admitted [encode vocab badOpening, encode vocab identityProof] with | .proved _ => true | _ => false
-- A proof checked against another KB does not answer the query.
#guard match admitted [encode vocab identityProof] (plain []) with | .needsEvidence _ _ => true | _ => false
-- What a supplied proof lacks is reported beside P0's requests.
#guard match admitted [encode vocab (node (.extension .custom []) identity)] with
  | .needsEvidence _ [.rule .custom] => true
  | _ => false

-- even's recursive clause is outside P0. Its theorem even(4) is checked in a
-- proof layer whose KB is the executable program with the recursive clause,
-- and imported as a fact: the run then answers for that KB.
#guard needsEvidence (check .ha (input evenKb [] (atom .even [four])))
def executable : Input Dom Nat Nat Sym := input [rule (k .w) [atom .even [four]], fact (atom .even [zero])] [] (k .w)
def proofLayer : Checker Nat Nat Sym := plain (executable.program.clauses.map ProgramClause.clause ++ [evenStep])
def evenTheorem : Import Nat Nat Sym := ⟨.lem, [], atom .even [four], encode vocab evenFour⟩
#guard (importedClauses vocab proofLayer (fun _ => true) [evenTheorem]).length == 1
def outcome (result : Result Dom Nat Nat Sym .ha) : Option OutcomeKind :=
  match result with
  | .ready plan => some (plan.run 500).kind
  | _ => none
#guard outcome (check .ha executable) = some .exhausted
#guard (admitImports vocab proofLayer .ha executable [evenTheorem]).bind outcome = some .success
-- A KB that does not contain the executable program is refused.
#guard (admitImports vocab (plain evenKb) .ha executable [evenTheorem]).isNone
-- An import outside the P0 classes stays in the proof layer: a NAF fact is not
-- added, and the program is admitted as before.
def nafFact : Import Nat Nat Sym := ⟨.loop, [], naf (k .r), encode vocab (node (.defaultNegIntro .truth) (naf (k .r)))⟩
#guard (admitImports vocab proofLayer .ha executable [nafFact, evenTheorem]).bind outcome = some .success
-- A local proof is never a global fact: an import under assumptions adds no clause.
#guard (importedClauses vocab (plain []) (fun _ => true) [underQ]).isEmpty

/-! ### Guard premises against the generated signature clauses -/

-- isNat(succ(zero)) by the membership clauses, with the generated names.
def natSucc : P :=
  step (rule (atom .isNat [succ (.var 100)]) [atom .isNat [.var 100]]) [(100, zero)] (atom .isNat [succ zero])
    [step (fact (atom .isNat [zero])) [] (atom .isNat [zero]) []]
#guard verdict (plain generated) [] (atom .isNat [succ zero]) natSucc = .accept
-- allData through Nat, and isPred(p) by its generated fact.
#guard verdict (plain generated) [] (atom .allData [succ zero])
  (step (rule (atom .allData [.var 100]) [atom .isNat [.var 100]]) [(100, succ zero)] (atom .allData [succ zero])
    [natSucc]) = .accept
#guard verdict (plain generated) [] (atom .isPred [k .p]) (step (fact (atom .isPred [k .p])) [] (atom .isPred [k .p]) [])
  = .accept
#guard verdict (plain generated) [] (atom .isPred [k .q]) (step (fact (atom .isPred [k .q])) [] (atom .isPred [k .q]) [])
  = .reject

/-! ### R28: exported P0 runs, NAF evidence, and checked membership -/

/-- Run a Ready plan, export its success, and check the export with the plan's
checker under a context. -/
def exported (query : Input Dom Nat Nat Sym) : Option (Plan Dom Nat Nat Sym .ha × T) :=
  match check .ha query with
  | .ready plan =>
      match plan.run 500 with
      | .success proof _ => (plan.exportProof vocab proof).map (plan, ·)
      | _ => none
  | _ => none

def checkExport (query : Input Dom Nat Nat Sym) (context : List T := query.context) : Option (Verdict Sym) :=
  (exported query).map fun (plan, term) => checkProof vocab (plan.checker vocab) [] context query.goal term

-- p :- q and q: the machine's tree is exactly the tree built by hand.
def chain := input [rule (k .p) [k .q], fact (k .q)] [] (k .p)
#guard checkExport chain = some .accept
def byHand : P := step (rule (k .p) [k .q]) [] (k .p) [step (fact (k .q)) [] (k .q) []]
#guard (exported chain).any fun (_, term) => identical term (encode vocab byHand)
#guard verdict (plain (chain.program.clauses.map ProgramClause.clause)) [] (k .p) byHand = .accept
-- A guard fact of the plan exports as a checked membership node.
#guard checkExport (input [rule (k .w) [atom .isNat [succ zero]]] [] (k .w)) = some .accept
#guard checkExport (input [rule (k .w) [atom .allData [succ (k .b)]]] [atom .isNat [k .b]] (k .w)) = some .accept
-- NAF: the certificate's failure witness is the node's evidence.
def negation := input [rule (k .p) [naf (k .q)]] [] (k .p)
#guard checkExport negation = some .accept
-- Stale evidence: under another context the same term is rejected.
#guard checkExport negation [k .r] = some .reject
-- Forged evidence: a witness that does not check is rejected.
def forged : Option (Verdict Sym) :=
  (exported negation).map fun (plan, _) =>
    checkProof vocab (plan.checker vocab) [] [] (k .p) (encode vocab
      (step (rule (k .p) [naf (k .q)]) [] (k .p)
        [node (.defaultNegIntro (encodeFailure vocab (.negation .truth))) (naf (k .q))]))
#guard forged = some .reject
-- Without a NAF evidence check, the proof needs that capability.
#guard (exported negation).map (fun (plan, term) =>
  checkProof vocab { plan.checker vocab with negation := none } [] [] (k .p) term) = some (.needsEvidence [.negation])

/-! ### Capabilities and holes -/

-- A derived rule nobody registered needs evidence, before the tree is checked;
-- a tree for another goal is rejected first.
#guard verdict (plain []) [] (k .p) (node (.extension .custom []) (k .p)) = .needsEvidence [.rule .custom]
#guard verdict (plain []) [] (k .q) (node (.extension .custom []) (k .p)) = .reject
-- A tree still holding a reference to a delayed goal exports nothing.
#guard (exportTree (Certificate := Unit) (fun _ => .truth) Store.empty (fun _ _ => none)
  (.deferred 0 ⟨⟨[], []⟩, k .p⟩)).isNone
#guard (exportTree (Certificate := Unit) (fun _ => .truth) Store.empty (fun _ _ => none)
  (.node .conjIntro ⟨⟨[], []⟩, .conj (k .p) .truth⟩ [{ goal := k .p }, { goal := .truth }]
    [.deferred 0 ⟨⟨[], []⟩, k .p⟩, .node .truth ⟨⟨[], []⟩, .truth⟩ [] []])).isNone

-- A malformed existential elimination exports nothing.
#guard (exportTree (Certificate := Unit) (fun _ => .truth) Store.empty (fun _ _ => none)
  (.node (.existsElim 5) ⟨⟨[], []⟩, k .p⟩ [{ goal := .existsVar 1 (k .q) }, { goal := k .p }] [])).isNone
-- A derived rule's closed-world evidence is its last parameter.
#guard (exportTree (Certificate := Unit) (fun _ => k .b) Store.empty (fun _ _ => none)
  (.node (.extension .custom [k .a] (some ⟨.completeFailure, ()⟩)) ⟨⟨[], []⟩, k .p⟩ [] [])).any
    fun proof => identical (encode vocab proof) (encode vocab (node (.extension .custom [k .a, k .b]) (k .p)))
-- A replacement template is read through the store, like every parameter.
def bound : Store Nat Nat Sym := ⟨[], [(7, k .a)], [], []⟩
#guard (exportTree (Certificate := Unit) (fun _ => .truth) bound (fun _ _ => none)
  (.node (.equalSubst 1 (atom .p [.var 7, .var 1])) ⟨⟨[], []⟩, k .p⟩ [] [])).any
    fun proof => identical (encode vocab proof) (encode vocab (node (.equalSubst 1 (atom .p [k .a, .var 1])) (k .p)))

/-! ### The theorems, instantiated -/

-- An accepted term reconstructs `Derives` for its goal, with the checker's KB
-- and NAF provider.
example (accepted : verdict (plain kb) [] (atom .p [k .a]) (pa) = .accept) :
    Derives Sym.ha (plain kb).snapshot.kb [] (atom .p [k .a]) NafFailure.disabled :=
  checked_toDerives vocab (plain kb) ((checkProof_accept_iff vocab (plain kb)).mp accepted)

-- Every successful run of a Ready plan exports an accepted term.
example (plan : Plan Dom Nat Nat Sym .ha) {fuel : Nat} {proof resume}
    (ran : plan.run fuel = .success proof resume) :
    ∃ term, plan.exportProof vocab proof = some term ∧
      checkProof vocab (plan.checker vocab) [] plan.input.context plan.input.goal term = .accept :=
  Plan.exportProof_checked ran

-- Rejection says nothing about the goal.
example (goal : T) : checkProof vocab (plain []) [] [] goal .truth = .reject := reject_says_nothing vocab _ [] [] goal

end P1CheckTests
