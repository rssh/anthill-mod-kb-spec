import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Machine AnthillModKbSpec.P1 AnthillModKbSpec.Admission
  AnthillModKbSpec.InductiveDomains AnthillModKbSpec.AdmissionSignature

namespace ConversionTests

attribute [local instance] termEq clauseEq

/-! Executable traces of S11: `ho_apply` conversion on the shared machine and
whole-formula induction-head selection. Goals reading as concrete indirect
calls are normalized (`ho_goal`); candidates applying a predicate by
`ho_apply` meet direct goals through the goal's indirect view and are
converted; the explicit `headMatch` choice selects a clause by its whole head.
Each run's export is checked by the S08 checker. Each `#guard` evaluates
compiled code; the examples at the end instantiate the theorems. -/

inductive Sym where
  | p | q | r | s | a | b | zero | succ | isNat | isBool | isPred1 | isPred2 | reachable | r2 | allData | isPred | ha
  | tag (tag : Tag)
  deriving DecidableEq, Repr

def vocab : Vocabulary Sym := ⟨Sym.tag, fun _ _ same => by cases same; rfl⟩

abbrev T := Term Nat Nat Sym
abbrev Clause := HornClause Nat Nat Sym
abbrev Run := Outcome Nat Nat Sym Unit Nat
abbrev P := Proof Nat Nat Sym

def k (symbol : Sym) : T := .app symbol []
def atom (symbol : Sym) (args : List T) : T := .app symbol args
def x (name : Nat) : T := .var name
def fact (head : T) : Clause := .definite head []
def rule (head : T) (body : List T) : Clause := .definite head body
def same : T → T → Bool := identical
def applyP (predicate : T) (args : List T) : T := .hoApply .ha predicate args

def plain (clauses : List Clause) : Program Nat Nat Sym :=
  ⟨clauses.mapIdx fun index clause => ⟨.lowered index, clause⟩, fun _ => false⟩

def query (flexibles : List Nat) (context : List T) (goal : T) : State Nat Nat Sym Unit Nat :=
  State.init 0 flexibles context goal

/-- No command is chosen: the left strategy is `positive` with its own
handling of compound assumptions. -/
def noChoice : Selection Nat Nat Sym := fun _ _ _ _ => []

def solve (clauses : List Clause) (state : State Nat Nat Sym Unit Nat) (select : Selection Nat Nat Sym := noChoice)
    (fuel : Nat := 2000) : Run :=
  run (left .ha (plain clauses) select) fuel state

def resume (clauses : List Clause) (outcome : Run) (select : Selection Nat Nat Sym := noChoice) : Run :=
  match outcome with
  | .success _ state => run (left .ha (plain clauses) select) 2000 state
  | other => other

def rulesOf (outcome : Run) : Option (List RuleId) := outcome.proof?.map (·.tree.rules)

def answerIs (outcome : Run) (name : Nat) (expected : T) : Bool :=
  match outcome.proof? with
  | some proof => same (proof.answer name) expected
  | none => false

def checker (clauses : List Clause) : Checker Nat Nat Sym := ⟨⟨.ha, clauses⟩, NafFailure.disabled, none, []⟩

/-- The run's proof as a supplied tree, read through its final store. -/
def exported (outcome : Run) : Option P :=
  outcome.proof?.bind fun proof => exportTree (Certificate := Unit) (fun _ => .truth) proof.store (fun _ _ => none) proof.tree

/-- The exported term is accepted for the answer instance. -/
def checks (clauses : List Clause) (context : List T) (goal : T) (outcome : Run) : Bool :=
  match outcome.proof? with
  | some proof =>
      match exportProof vocab (fun _ => .truth) proof with
      | some term =>
          decide (checkProof vocab (checker clauses) [] (context.map proof.store.resolve) (proof.store.resolve goal) term
            = .accept)
      | none => false
  | none => false

def verdict (clauses : List Clause) (context : List T) (goal : T) (proof : P) : Verdict Sym :=
  checkProof vocab (checker clauses) [] context goal (encode vocab proof)

/-- The rules of a supplied tree in preorder, by their encoding tags. -/
partial def tags : P → List Tag
  | .node rule _ premises =>
      (match encodeRule vocab rule with | .app (.tag tag) _ => [tag] | _ => []) ++ premises.flatMap tags

def exportedTags (outcome : Run) : Option (List Tag) := (exported outcome).map tags

mutual
def nodes : ProofTree Nat Nat Sym Unit → List (ProofTree Nat Nat Sym Unit)
  | .node rule obligation premises subproofs => .node rule obligation premises subproofs :: nodesOf subproofs
  | .deferred _ _ => []

def nodesOf : List (ProofTree Nat Nat Sym Unit) → List (ProofTree Nat Nat Sym Unit)
  | [] => []
  | tree :: trees => nodes tree ++ nodesOf trees
end

/-- Every node of a run's tree with its rule and goal read through the final store. -/
def readNodes (outcome : Run) : List (RuleApp Nat Nat Sym Unit × T) :=
  match outcome.proof? with
  | some proof =>
      (nodes proof.tree).filterMap fun
        | .node rule obligation _ _ => some (rule, proof.store.resolve obligation.goal)
        | .deferred _ _ => Option.none
  | Option.none => []

/-! ### `ho_goal`: indirect goals are answered as their direct form -/

-- ho_apply(p, a) with the fact p(a): one normalization, then the fact.
def hoGoalRun := solve [fact (atom .p [k .a])] (query [] [] (applyP (k .p) [k .a]))
#guard rulesOf hoGoalRun = some [.hoApplyIntro, .clause, .truth]
#guard checks [fact (atom .p [k .a])] [] (applyP (k .p) [k .a]) hoGoalRun
#guard exportedTags hoGoalRun = some [.hoApplyIntro, .clause, .truth]
-- A direct assumption for an indirect goal: normalized, then identity.
#guard rulesOf (solve [] (query [] [atom .p [k .a]] (applyP (k .p) [k .a]))) = some [.hoApplyIntro, .assumption]
-- No rewrite loop: with no evidence the indirect goal is exhausted, not interrupted.
#guard (solve [] (query [] [] (applyP (k .p) [k .a]))).kind = .exhausted
#guard (solve [] (query [] [] (atom .p [k .a]))).kind = .exhausted

-- The strategy's chosen commands are kept beside `ho_goal`: a disjunction split
-- chosen at the indirect goal proves it in both cases.
def chooseCases : Selection Nat Nat Sym := fun _ _ goal _ =>
  if (goal.call? Sym.ha).isSome then [.disjCases (.disj (applyP (k .p) [k .a]) (applyP (k .p) [k .a]))] else []
def casesRun := solve [] (query [] [.disj (applyP (k .p) [k .a]) (applyP (k .p) [k .a])] (applyP (k .p) [k .a])) chooseCases
#guard casesRun.kind = .success
#guard checks [] [.disj (applyP (k .p) [k .a]) (applyP (k .p) [k .a])] (applyP (k .p) [k .a]) casesRun

/-! ### Indirect evidence for direct goals: `ho_elim` through the indirect view -/

-- An assumption ho_apply(p, a) proves p(a), converted by elimination.
def indirectAssumed := solve [] (query [] [applyP (k .p) [k .a]] (atom .p [k .a]))
#guard rulesOf indirectAssumed = some [.converted]
#guard checks [] [applyP (k .p) [k .a]] (atom .p [k .a]) indirectAssumed
#guard exportedTags indirectAssumed = some [.hoApplyElim, .assumption]
#guard (resume [] indirectAssumed).kind = .exhausted
-- Another predicate's indirect assumption is a miss.
#guard (solve [] (query [] [applyP (k .q) [k .a]] (atom .p [k .a]))).kind = .exhausted

-- A concrete indirect head `ho_apply(q, x) :- r(x)` concludes q(a) by the clause
-- node, converted; for p(a) it is a miss.
def concreteHead : List Clause := [rule (applyP (k .q) [x 1]) [atom .r [x 1]], fact (atom .r [k .a])]
def concreteRun := solve concreteHead (query [] [] (atom .q [k .a]))
#guard rulesOf concreteRun = some [.converted, .conjIntro, .clause, .truth, .truth]
#guard checks concreteHead [] (atom .q [k .a]) concreteRun
#guard (solve concreteHead (query [] [] (atom .p [k .a]))).kind = .exhausted

-- A flexible head `ho_apply(P, x) :- q(x)` for r(a): matching the view binds the
-- clause's P to the reference r; the clause node records that instantiation.
def flexibleHead : List Clause := [fact (atom .q [k .a]), rule (applyP (x 1) [x 2]) [atom .q [x 2]]]
def flexibleRun := solve flexibleHead (query [] [] (atom .r [k .a]))
#guard rulesOf flexibleRun = some [.converted, .conjIntro, .clause, .truth, .truth]
#guard checks flexibleHead [] (atom .r [k .a]) flexibleRun
#guard (readNodes flexibleRun).any fun
  | (.converted view (.clause _ _), goal) => same view (applyP (k .r) [k .a]) && same goal (atom .r [k .a])
  | _ => false
-- Such a head concludes every unary call, its own body included: selected before
-- the fact, it is re-entered on q(a) until the budget runs out. Nothing claims
-- termination; admitting a flexible head is S12's.
#guard (solve flexibleHead.reverse (query [] [] (atom .r [k .a]))).kind = .interrupted

/-! ### Direct evidence for a flexible predicate: introduction through the view -/

-- ∃-style answer name X0 applied by ho_apply, under q(a): identity binds X0 := q.
def flexibleGoal := solve [] (query [0] [atom .q [k .a]] (applyP (x 0) [k .a]))
#guard rulesOf flexibleGoal = some [.converted]
#guard answerIs flexibleGoal 0 (k .q)
#guard checks [] [atom .q [k .a]] (applyP (x 0) [k .a]) flexibleGoal
#guard exportedTags flexibleGoal = some [.hoApplyIntro, .assumption]
-- A direct clause is never matched against a flexible predicate: choosing among
-- the program's predicates needs an admitted candidate set, so it is a gap.
#guard (solve [fact (atom .q [k .a])] (query [0] [] (applyP (x 0) [k .a]))).kind = .unknown

/-! ### Rigid predicates are never assigned -/

-- ∀P. ho_apply(P, a) under q(a): the opened P is rigid, so q(a) is no evidence.
#guard (solve [] (query [] [atom .q [k .a]] (.forallVar 5 (applyP (x 5) [k .a])))).kind = .exhausted
-- A rigid query parameter P: an assumption ho_apply(P, a) proves the identical goal.
#guard rulesOf (solve [] (query [] [applyP (x 5) [k .a]] (applyP (x 5) [k .a]))) = some [.assumption]
-- ...and is no evidence for q(a): P is not assigned.
#guard (solve [] (query [] [applyP (x 5) [k .a]] (atom .q [k .a]))).kind = .exhausted
-- A flexible clause predicate may be bound to a rigid parameter, by the S05 match.
#guard rulesOf (solve [fact (applyP (x 1) [k .a])] (query [] [] (applyP (x 5) [k .a]))) = some [.clause, .truth]

/-! ### Static classification: structural reference matching, not lambdas -/

-- Reading conclusions against goals; P (1) may be bound, the rigid 5 not.
def binds : Nat → Bool := (· == 1)
#guard compareAtom .ha binds (atom .p [k .a]) (atom .p [x 2]) = .direct
#guard compareAtom .ha binds (atom .p [k .a]) (applyP (x 1) [x 2]) = .elim
#guard compareAtom .ha binds (applyP (x 1) [k .a]) (atom .q [x 2]) = .intro
-- A call of another arity: only a lambda could match.
#guard compareAtom .ha binds (atom .p [k .a, k .b]) (applyP (x 1) [x 2]) = .lambda
-- A goal that is no call, falsity included, is never an application's instance.
#guard compareAtom .ha binds (.conj (k .p) (k .q)) (applyP (x 1) [x 2]) = .apart
#guard compareAtom .ha binds .falsity (applyP (x 1) [x 2]) = .apart
-- A rigid predicate name or a concrete reference of another arity is apart.
#guard compareAtom .ha binds (atom .p [k .a, k .b]) (applyP (x 5) [x 2]) = .apart
#guard compareAtom .ha binds (atom .p [k .a, k .b]) (applyP (k .q) [x 2]) = .apart
-- Whole formulas compare through their implications.
#guard compare .ha binds (.imp (k .s) (atom .p [k .a])) (.imp (k .r) (applyP (x 1) [x 2])) = .elim
#guard compare .ha binds (.imp (k .s) (atom .p [k .a])) (applyP (x 1) [x 2]) = .apart
-- Whole formulas of the same kind, binders included, go to the matcher as they are.
#guard compare .ha binds (.forallVar 7 (atom .p [x 7])) (.forallVar 7 (atom .p [x 7])) = .direct
#guard compare .ha binds (.forallVar 7 (atom .p [x 7])) (.existsVar 7 (atom .p [x 7])) = .apart

-- In a run, a lambda comparison is a gap: unknown, never exhausted.
#guard (solve [fact (applyP (x 1) [k .a])] (query [] [] (atom .p [k .a, k .b]))).kind = .unknown
-- A concrete reference of another arity is a plain miss.
#guard (solve [fact (applyP (k .q) [k .a])] (query [] [] (atom .p [k .a, k .b]))).kind = .exhausted
-- A flexible head never concludes falsity: contradiction search stays exhaustive.
#guard (solve [rule (applyP (x 1) [x 2]) [atom .q [x 2]]] (query [] [] .falsity)).kind = .exhausted
-- A goal applying a rigid name or a term is no introduction: a direct clause is a
-- miss there, not a gap.
#guard (solve [fact (atom .q [k .b])] (query [] [] (.forallVar 5 (applyP (x 5) [k .a])))).kind = .exhausted
#guard (solve [fact (atom .q [k .a])] (query [] [] (applyP (atom .r [k .b]) [k .a]))).kind = .exhausted

-- The matcher itself is unchanged: ho_apply against a direct call is unsupported.
#guard match (Store.empty : Store Nat Nat Sym).unify ⟨[], []⟩ .ha (applyP (k .p) [k .a]) (atom .p [k .a]) with
  | .unsupported => true
  | _ => false

/-! ### Whole-formula induction-head selection

The induction principle is a clause with a compound head, its predicate guarded
by `P_1`: `(isNat(x) → ho_apply(P, x)) :- isPred1(P), ho_apply(P, zero), step(P)`.
The step's binder `n` is its own. The focus `isNat(a) → reachable(a)` is
matched against the whole head through its indirect view: `x := a`, and
`P := reachable`, the registered unary reference. -/

def isNat (term : T) : T := atom .isNat [term]
def reachable (term : T) : T := atom .reachable [term]
def zero : T := k .zero
def succ (term : T) : T := atom .succ [term]

/-- Template names: P is 1, x is 2; the step binder n is 3. -/
def step (predicate : T) : T :=
  .forallVar 3 (.imp (isNat (x 3)) (.imp (applyP predicate [x 3]) (applyP predicate [succ (x 3)])))
def induction : Clause :=
  rule (.imp (isNat (x 2)) (applyP (x 1) [x 2])) [atom .isPred1 [x 1], applyP (x 1) [zero], step (x 1)]
def nat : List Clause := [fact (isNat zero), rule (isNat (succ (x 2))) [isNat (x 2)]]
def reach : List Clause := [fact (reachable zero), rule (reachable (succ (x 2))) [reachable (x 2)]]
/-- The generated registry facts: reachable at arity 1, r2 only at arity 2. -/
def registry : List Clause := [fact (atom .isPred1 [k .reachable]), fact (atom .isPred2 [k .r2])]
def kb : List Clause := nat ++ reach ++ [induction] ++ registry

/-- Choose the principle by its whole head at the root focus only. -/
def atRoot : Selection Nat Nat Sym := fun obligation _ _ _ =>
  if obligation.scope.assumptions.isEmpty then [.headMatch induction] else []

-- The focus with a rigid parameter a (9).
def focus : T := .imp (isNat (x 9)) (reachable (x 9))
def inductionRun := solve kb (query [] [] focus) atRoot

#guard rulesOf inductionRun = some [.converted, .conjIntro, .clause, .truth, .conjIntro, .hoApplyIntro, .clause, .truth,
  .conjIntro, .forallIntro, .impIntro, .impIntro, .hoApplyIntro, .clause, .conjIntro, .converted, .truth, .truth]
-- The export is accepted: S08's own rules check every node, the conversion
-- under the implication included; no matcher search is replayed.
#guard checks kb [] focus inductionRun
#guard (exportedTags inductionRun).map (·.take 6) = some [.impElim, .impIntro, .impIntro, .hoApplyElim, .impElim, .assumption]
-- The principle's node: x := a and P := reachable, read through the final
-- answers; the rigid a is a value, never assigned.
#guard match inductionRun.proof? with
  | some proof =>
      (nodes proof.tree).any fun
        | .node (.converted _ (.clause clause instantiation)) _ _ _ =>
            decide (clause = induction) &&
              (instantiation.map fun pair => (pair.1, proof.store.resolve pair.2)).all fun
                | (1, value) => same value (k .reachable)
                | (2, value) => same value (x 9)
                | _ => false
        | _ => false
  | Option.none => false
-- The exported tree states that instantiation explicitly in its clause node, so
-- the checker verifies it by substitution, without a matcher search.
partial def clauseRules : P → List (Clause × List (Nat × T))
  | .node rule _ premises =>
      (match rule with | .clause clause instantiation => [(clause, instantiation)] | _ => []) ++
        premises.flatMap clauseRules
#guard match exported inductionRun with
  | some tree => (clauseRules tree).any fun (clause, instantiation) =>
      decide (clause = induction) && instantiation.all fun
        | (1, value) => same value (k .reachable)
        | (2, value) => same value (x 9)
        | _ => false
  | Option.none => false
-- The original formula is finished exactly once, by that node.
#guard ((readNodes inductionRun).filter fun (_, goal) => same goal focus).length = 1
-- The predicate guard is kept and discharged by the generated fact for reachable.
#guard (readNodes inductionRun).any fun
  | (.clause clause _, goal) =>
      decide (clause = fact (atom .isPred1 [k .reachable])) && same goal (atom .isPred1 [k .reachable])
  | _ => false
-- The step keeps its own binder: the universally quantified step obligation is
-- opened by forallIntro at a fresh rigid name, independent of a.
#guard (readNodes inductionRun).any fun
  | (.forallIntro eigen, goal) => same goal (step (k .reachable)) && eigen != 9
  | _ => false
-- Inside the step, the hypothesis ho_apply(reachable, n) proves reachable(n) by
-- elimination through the view.
#guard (readNodes inductionRun).any fun
  | (.converted view .assumption, .app .reachable [.var name]) =>
      same view (applyP (k .reachable) [x name]) && name != 9
  | _ => false
-- Instantiating the head's names never captures the step binder: x := n renames it.
#guard match (step (x 1)).instantiate (Substitution.single 1 (x 3)) with
  | .forallVar binder _ => binder != 3
  | _ => false

-- The atomic path cannot select a principle with a compound head: without the
-- choice, the focus is exhausted.
#guard (solve kb (query [] [] focus)).kind = .exhausted
-- The guarded universal itself, opened first.
#guard (solve kb (query [] [] (.forallVar 2 (.imp (isNat (x 2)) (reachable (x 2))))) atRoot).kind = .success

/-! ### Rejections: wrong domain, wrong range, arity -/

-- A guard of another domain: the whole head does not match.
#guard (solve kb (query [] [] (.imp (atom .isBool [x 9]) (reachable (x 9)))) atRoot).kind = .exhausted
-- A predicate outside the unary range: r2 is registered at arity 2 only, so
-- isPred1(r2) has no generated fact; zero is no predicate reference at all.
#guard (solve kb (query [] [] (.imp (isNat (x 9)) (atom .r2 [x 9]))) atRoot).kind = .exhausted
#guard (solve kb (query [] [] (.imp (isNat (x 9)) (atom .zero [x 9]))) atRoot).kind = .exhausted
-- Arity mismatch: only a lambda answer could make the unary head conclude
-- reachable(a, b): unsupported, a gap.
#guard (solve kb (query [] [] (.imp (isNat (x 9)) (atom .reachable [x 9, k .b]))) atRoot).kind = .unknown

-- Other compound heads are matched as whole formulas, without conversion.
def conjClause : Clause := rule (.conj (atom .p [x 1]) (atom .q [x 1])) [atom .r [x 1]]
def conjRun := solve [conjClause, fact (atom .r [k .a])] (query [] [] (.conj (atom .p [k .a]) (atom .q [k .a])))
  (fun obligation _ _ _ => if obligation.scope.assumptions.isEmpty then [.headMatch conjClause] else [])
#guard rulesOf conjRun = some [.clause, .conjIntro, .clause, .truth, .truth]
#guard checks [conjClause, fact (atom .r [k .a])] [] (.conj (atom .p [k .a]) (atom .q [k .a])) conjRun

-- A quantified head is matched as a whole, as the matcher compares binders.
def quantified : Clause := fact (.forallVar 7 (atom .p [x 7]))
#guard rulesOf (solve [quantified] (query [] [] (.forallVar 7 (atom .p [x 7]))) (fun _ _ _ _ => [.headMatch quantified]))
  = some [.clause, .truth]

-- A projected conjunct is compared like any conclusion: `ho_apply(P, x)` from the
-- head `ho_apply(P, x) ∧ q(x)` concludes p(a) through the view, converted.
def projected : Clause := rule (.conj (applyP (x 1) [x 2]) (atom .q [x 2])) [atom .r [x 2]]
def projectRun := solve [projected, fact (atom .r [k .a])] (query [] [] (atom .p [k .a]))
  (fun _ _ _ _ => [.headProject projected [false]])
#guard rulesOf projectRun = some [.converted, .conjIntro, .clause, .truth, .truth]
#guard checks [projected, fact (atom .r [k .a])] [] (atom .p [k .a]) projectRun
-- Chosen explicitly, a direct conjunct or head may bind a goal's flexible
-- predicate: the selection, not the strategy, chose the clause.
def directConj : Clause := rule (.conj (atom .p [x 2]) (atom .q [x 2])) [atom .r [x 2]]
def directRun := solve [directConj, fact (atom .r [k .a])] (query [0] [] (applyP (x 0) [k .a]))
  (fun _ _ _ _ => [.headProject directConj [false]])
#guard rulesOf directRun = some [.converted, .conjIntro, .clause, .truth, .truth]
#guard answerIs directRun 0 (k .p)
#guard checks [directConj, fact (atom .r [k .a])] [] (applyP (x 0) [k .a]) directRun
#guard answerIs (solve [fact (atom .q [k .a])] (query [0] [] (applyP (x 0) [k .a]))
  (fun _ _ _ _ => [.headMatch (fact (atom .q [k .a]))])) 0 (k .q)

/-! ### Hand-built conversions -/

def viewTree : P := Unfold.convert (applyP (k .p) [k .a]) (atom .p [k .a]) (Unfold.hypothesis (applyP (k .p) [k .a]))
#guard verdict [] [applyP (k .p) [k .a]] (atom .p [k .a]) viewTree = .accept
-- Another predicate's indirect call does not convert to p(a).
#guard verdict [] [applyP (k .q) [k .a]] (atom .p [k .a])
  (Unfold.convert (applyP (k .q) [k .a]) (atom .p [k .a]) (Unfold.hypothesis (applyP (k .q) [k .a]))) = .reject
-- Under an implication, the cut keeps the premise as it is.
def impTree : P := Unfold.convert (.imp (k .s) (applyP (k .p) [k .a])) (.imp (k .s) (atom .p [k .a]))
  (Unfold.hypothesis (.imp (k .s) (applyP (k .p) [k .a])))
#guard verdict [] [.imp (k .s) (applyP (k .p) [k .a])] (.imp (k .s) (atom .p [k .a])) impTree = .accept
#guard verdict [] [.imp (k .r) (applyP (k .p) [k .a])] (.imp (k .s) (atom .p [k .a]))
  (Unfold.convert (.imp (k .r) (applyP (k .p) [k .a])) (.imp (k .s) (atom .p [k .a]))
    (Unfold.hypothesis (.imp (k .r) (applyP (k .p) [k .a])))) = .reject

/-! ### Proof-layer capabilities beside P0

P0 asks evidence for every application by `ho_apply`; the diagnosis names the
S11 commands that use it. Inside data nothing converts. -/

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

def program (clauses : List Clause) : Program Nat Nat Sym :=
  ⟨clauses.mapIdx (fun index clause => ⟨.lowered index, clause⟩) ++
    (signatureClauses snapshot names rules).map (⟨.signature, ·⟩), guardSymbol snapshot⟩

def input (clauses : List Clause) (context : List T) (goal : T) : Input Dom Nat Nat Sym :=
  ⟨snapshot, names, rules, listed, complete, distinct, program clauses, fun _ => guardSymbol_iff, context, goal⟩

def diagnosed (clauses : List Clause) (context : List T) (goal : T) : List (Site × ProofLayer) :=
  (diagnose .ha (input clauses context goal)).map fun (request, layer) => (request.site, layer)

-- An indirect goal: ho_goal and converted candidates.
#guard diagnosed [] [] (applyP (k .p) [k .a]) = [(.goal, .commands [.hoApplyIntro, .converted])]
-- An indirect assumption and an indirect head: converted candidates.
#guard diagnosed [] [applyP (k .p) [k .a]] (atom .p [k .a]) = [(.assumption 0, .commands [.converted])]
#guard diagnosed [rule (applyP (k .q) [k .a]) [atom .r [k .a]]] [] (atom .q [k .a]) = [(.head 0, .commands [.converted])]
-- Inside data nothing converts: truth, not values, is preserved by ho_apply.
#guard diagnosed [] [] (atom .q [applyP (k .p) [k .a]]) = [(.goal, .none)]
-- Nor inside a NAF operand: conversion gives no failure evidence.
#guard diagnosed [] [] (.defaultNeg (applyP (k .p) [k .a])) = [(.goal, .none)]
-- An induction principle's compound head: S09's use, and the whole head converted.
#guard (diagnosed [induction] [] (atom .q [k .a])).head? = some (.head 0, .commands [.headUse, .converted])

/-! ### The theorems, instantiated -/

/-- A successful run with conversions and the whole-formula choice
reconstructs `Derives` for its answer instance. -/
example {proof : CompletedProof Nat Nat Sym Unit Nat} {resume : State Nat Nat Sym Unit Nat}
    (ran : run (left .ha (plain kb) atRoot) 2000 (query [] [] focus) = .success proof resume) :
    Derives Sym.ha (plain kb).kb ([].map proof.store.resolve) (proof.store.resolve focus) :=
  left_reconstructs (naf := NafFailure.disabled) _ _ 2000 0 [] [] focus ran

/-- Conversion under an implication, by the foundation rules. -/
example {context : ProofContext Nat Nat Sym}
    (proof : Derives Sym.ha (plain kb).kb context (.imp (k .s) (applyP (k .p) [k .a])) NafFailure.disabled) :
    Derives Sym.ha (plain kb).kb context (.imp (k .s) (atom .p [k .a])) NafFailure.disabled :=
  Derives.ofIndirect (.imp (.call (by decide))) proof

/-- A lambda comparison: no instance of the conclusion is the goal or its view. -/
example (σ : Substitution Nat Nat Sym) : (applyP (x 1) [x 2]).instantiate σ ≠ atom .p [k .a, k .b] :=
  (compareAtom_lambda (hoApplySymbol := Sym.ha) (binds := binds) (by decide) σ).1

/-- The conversion's nodes are checked given a checked tree of the view. -/
example {context : ProofContext Nat Nat Sym} {proof : P}
    (proves : Proves (checker []) (fun _ _ _ => False) context (applyP (k .p) [k .a]) proof) :
    Proves (checker []) (fun _ _ _ => False) context (atom .p [k .a])
      (Unfold.convert (applyP (k .p) [k .a]) (atom .p [k .a]) proof) :=
  Unfold.convert_proves (.inl (.call (by decide))) proves

/-- The guard of a registered reference holds by its generated fact. -/
example {built : Program Nat Nat Sym} (ok : Program.build .ha snapshot names rules [] = .ok built) :
    Derives Sym.ha built.kb [] (Elaboration.rangeGuard snapshot.naming (.predicate 1) (k .p)) NafFailure.disabled :=
  Program.predicateGuard_derives ok complete (by decide)

end ConversionTests
