import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Machine AnthillModKbSpec.P1 AnthillModKbSpec.Answers
  AnthillModKbSpec.InductiveDomains AnthillModKbSpec.DictionaryRegistry AnthillModKbSpec.OrderDictionaries
  AnthillModKbSpec.OrderRegistry AnthillModKbSpec.OrderEvaluation

namespace DictionaryEvaluationTests

attribute [local instance] termEq

/-! Executable traces of S14 over the Nat and Bool order registry
(`OrderRegistry`, `OrderEvaluation`): operations evaluated by registered total
evaluators where their value is demanded, the P1 decision of
`call = result`, laws used only as checked lemmas, and what is Undecided.
Each `#guard` evaluates compiled code. The examples at the end instantiate the
theorems. -/

/-- The proof encoding's symbols: one tag symbol of the order model per tag. -/
def vocab : Vocabulary Symbol :=
  ⟨fun tag => .tag tag.ctorIdx, fun first second same => by
    have read := congrArg Tag.ofNat (Symbol.tag.inj same)
    simpa [Tag.ofNat_ctorIdx] using read⟩

abbrev Clause := HornClause String Data Symbol
abbrev L := Lemma Domain String Data Symbol

def rules : List (Rule Domain Symbol) := [zeroRule, succRule, trueRule, falseRule]

theorem listed : ∀ rule ∈ rules, snapshot.signature.signature.data.definitions rule := by
  intro rule member
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

def noChoice : Selection String Data Symbol := fun _ _ _ _ => []
def noCut : LemmaSelection String Data Symbol := fun _ _ _ _ => []

/-- The route over the order registry with the KB's own clauses and the lemmas. -/
def route (clauses : List Clause := []) (lemmas : List L := []) (fuel : Nat := 3000)
    (registered : List (Evaluation String Data Symbol) := evaluations) : Route Domain String Data Symbol :=
  ⟨snapshot, registered, .hoApply, vocab, .evaluation, names, rules, clauses, lemmas, noChoice, noCut, fuel⟩

def natOrdT : T := .app .natOrd []
def natDescT : T := .app .natDesc []
def boolOrdT : T := .app .boolOrd []
def aliasT : T := .app .aliasOrd []
def num (n : Nat) : T := (natTree n).toTerm
def a : T := .var "a"
def b : T := .var "b"
def isNat (term : T) : T := .app .isNat [term]
def less (dict x y : T) : T := lessTerm dict x y
def eq (left right : T) : T := .equal left right

/-- The answer's shape, its blockers by what they lack. -/
def shape : Route.DictionaryAnswer String Data Symbol → String
  | .yes _ => "yes"
  | .no _ => "no"
  | .unknown _ _ => "unknown"
  | .undecided _ => "undecided"

def missing : Route.DictionaryAnswer String Data Symbol → List (Missing String Data Symbol)
  | .undecided blockers => blockers.map Blocker.missing
  | _ => []

instance : BEq (Missing String Data Symbol) where
  beq
    | .proof, .proof | .mode, .mode | .termination, .termination => true
    | .construct first, .construct second => first == second
    | .lemma first, .lemma second => first == second
    | _, _ => false

/-- A raw run of the route's strategy, with flexible names. -/
def solve (route : Route Domain String Data Symbol) (flexibles : List String) (context : List T) (goal : T) :
    Outcome String Data Symbol Unit Unit :=
  Machine.run route.strategy route.fuel (State.init () flexibles context goal)

/-- The run's export, checked by the route's checker for the answer instance. -/
def verdict (route : Route Domain String Data Symbol) (context : List T) (goal : T)
    (outcome : Outcome String Data Symbol Unit Unit) : Option (Verdict Symbol) :=
  outcome.proof?.bind fun proof =>
    (exportProof vocab (fun _ => .truth) proof).map fun term =>
      checkProof vocab route.checker route.table (context.map proof.store.resolve) (proof.store.resolve goal) term

/-- The rules of a supplied tree in preorder, by their encoding tags. -/
partial def tags : Proof String Data Symbol → List Tag
  | .node rule _ premises =>
      (match encodeRule vocab rule with | .app (.tag index) _ => [Tag.ofNat index] | _ => []) ++ premises.flatMap tags

def exportedTags (outcome : Outcome String Data Symbol Unit Unit) : List Tag :=
  ((outcome.proof?.bind fun proof => exportTree (Certificate := Unit) (fun _ => .truth) proof.store (fun _ _ => none)
    proof.tree).map tags).getD []

mutual
def nodes : ProofTree String Data Symbol Unit → List (ProofTree String Data Symbol Unit)
  | .node rule obligation premises subproofs => .node rule obligation premises subproofs :: nodesOf subproofs
  | .deferred _ _ => []

def nodesOf : List (ProofTree String Data Symbol Unit) → List (ProofTree String Data Symbol Unit)
  | [] => []
  | tree :: trees => nodes tree ++ nodesOf trees
end

/-- The lemma commands of a run's tree, with their witnesses read through the
final store. -/
def lemmaNodes (outcome : Outcome String Data Symbol Unit Unit) : List (Symbol × List T) :=
  match outcome.proof? with
  | some proof =>
      (nodes proof.tree).filterMap fun
        | .node (.derived (.lemmaRule name _ witnesses)) _ _ _ => some (name, witnesses.map proof.store.resolve)
        | _ => none
  | none => []

/-- The goals of a run's tree in preorder, read through the final store. -/
def goals (outcome : Outcome String Data Symbol Unit Unit) : List T :=
  match outcome.proof? with
  | some proof => (nodes proof.tree).filterMap fun
      | .node _ obligation _ _ => some (proof.store.resolve obligation.goal)
      | _ => none
  | none => []

/-! ### The Nat ordering example: evaluation and the decision

`less` and `equal` carry primitive contracts and evaluations; a call is
evaluated to a Bool constructor term. The equation `call = result` with
member-tree arguments and result is decided without a run. -/

#guard snapshot.evaluate evaluations (less natOrdT (num 2) (num 3)) = some trueB
#guard snapshot.evaluate evaluations (less natOrdT (num 9) (num 2)) = some falseB
-- The descending dictionary on the same domain, by its own evaluation.
#guard snapshot.evaluate evaluations (less natDescT (num 2) (num 3)) = some falseB
#guard snapshot.evaluate evaluations (less boolOrdT falseB trueB) = some trueB
-- A nested path: `equal` under `weakOrd.eqModel`.
#guard snapshot.evaluate evaluations (equalTerm natOrdT (num 4) (num 4)) = some trueB
#guard snapshot.evaluate evaluations (equalTerm boolOrdT trueB falseB) = some falseB

#guard shape ((route).answer [] (eq (less natOrdT (num 2) (num 3)) trueB)) = "yes"
#guard shape ((route).answer [] (eq (less natOrdT (num 2) (num 3)) falseB)) = "no"
#guard shape ((route).answer [] (eq (equalTerm natOrdT (num 4) (num 5)) falseB)) = "yes"
#guard shape ((route).answer [] (eq (less natDescT (num 2) (num 3)) trueB)) = "no"
-- With the call on the right, decided the same way.
#guard shape ((route).answer [] (eq falseB (less natOrdT (num 3) (num 2)))) = "yes"
#guard shape ((route).answer [] (eq trueB (less natOrdT (num 3) (num 2)))) = "no"
-- The decision checks the evaluator's value at run time: an evaluation that
-- does not answer leaves the equation undecided, never No.
def gappy : List (Evaluation String Data Symbol) :=
  [{ natLess with run := fun args => if args = [num 0, num 0] then none else lessRun false args }]
#guard shape ((route (registered := gappy)).answer [] (eq (less natOrdT (num 0) (num 0)) falseB)) = "undecided"
#guard shape ((route (registered := gappy)).answer [] (eq (less natOrdT (num 0) (num 1)) falseB)) = "no"
-- A contract is found by its argument count among several for one operation,
-- and so is its evaluation: one registered for three arguments, listed first,
-- is not run on a call with two.
#guard ({ natRegistration with primitives := [⟨[], .less, [.nat, .nat, .nat], .bool⟩, ⟨[], .less, [.nat, .nat], .bool⟩] } :
  Registration Domain Symbol).primitive? [] .less 2 = some ⟨[], .less, [.nat, .nat], .bool⟩
#guard snapshot.evaluate ({ natLess with arity := 3, run := fun _ => none } :: evaluations) (less natOrdT (num 2) (num 3)) =
  some trueB
-- The decision is the contract's on the equations it admits.
#guard snapshot.check? evaluations rules ⟨less natOrdT (num 2) (num 3), falseB⟩ =
  some (snapshot.decide evaluations ⟨less natOrdT (num 2) (num 3), falseB⟩)
-- A goal the context assumes is proved from it, never refuted: the decision's
-- No waits for a run under the context. A context that does not prove the goal
-- keeps the No.
def assumed : T := eq (less natOrdT (num 2) (num 3)) falseB
#guard shape ((route).answer [assumed] assumed) = "yes"
#guard match (route).answer [assumed] assumed with
  | .yes term => checkProof vocab (route).checker [] [assumed] assumed term == .accept
  | _ => false
#guard shape ((route).answer [isNat a] assumed) = "no"
-- The Yes of the decision is the evaluation node, accepted by the checker.
#guard match (route).answer [] (eq (less natOrdT (num 2) (num 3)) trueB) with
  | .yes term => checkProof vocab (route).checker [] [] (eq (less natOrdT (num 2) (num 3)) trueB) term == .accept
  | _ => false

/-! ### Evaluation on value demand in runs -/

-- A flexible result is bound to the value.
def bound := solve (route) ["R"] [] (eq (less natOrdT (num 2) (num 3)) (.var "R"))
#guard bound.kind = .success
#guard (bound.proof?.map fun proof => proof.store.resolve (.var "R")) = some trueB
#guard verdict (route) [] (eq (less natOrdT (num 2) (num 3)) (.var "R")) bound = some .accept
-- A call on the right is turned around by `equalSymm`, then evaluated.
def turned := solve (route) [] [] (eq trueB (less natOrdT (num 2) (num 3)))
#guard turned.kind = .success
#guard exportedTags turned = [.equalSymm, .extension]
#guard verdict (route) [] (eq trueB (less natOrdT (num 2) (num 3))) turned = some .accept
-- An evaluated goal keeps its exact candidates: an assumption it reads as, ex
-- falso. With `c` rigid the evaluation misses, and the assumption closes it.
def c : T := .var "c"
#guard shape ((route).answer [eq (less natOrdT (num 2) (num 3)) c] (eq (less natOrdT (num 2) (num 3)) c)) = "yes"
#guard shape ((route).answer [.falsity] (eq (less natOrdT (num 2) (num 3)) c)) = "yes"
-- A wrong value is a miss: exhausted, which a run never reads as No.
#guard (solve (route) [] [] (eq (less natOrdT (num 3) (num 2)) trueB)).kind = .exhausted

-- Rollback: `OrdDictionary(D)` binds D to natOrd, whose
-- `less(natOrd, 3, 2) = true` misses; the binding is undone, and natDesc,
-- the descending order, succeeds.
def backtracked := solve (route) ["D"] [] (.conj (ordGuard (.var "D")) (eq (less (.var "D") (num 3) (num 2)) trueB))
#guard backtracked.kind = .success
#guard (backtracked.proof?.map fun proof => proof.store.resolve (.var "D")) = some natDescT
#guard verdict (route) [] (.conj (ordGuard (.var "D")) (eq (less (.var "D") (num 3) (num 2)) trueB)) backtracked =
  some .accept

-- The exported evaluation node is checked by re-running the snapshot's
-- evaluators. Without the evaluation rule the checker needs it; a node with a
-- wrong value is rejected.
#guard (bound.proof?.bind fun proof => (exportProof vocab (fun _ => .truth) proof).map fun term =>
  checkProof vocab ⟨(route).checkSnapshot, NafFailure.disabled, none, []⟩ [] []
    (eq (less natOrdT (num 2) (num 3)) trueB) term) = some (.needsEvidence [.rule .evaluation])
#guard checkProof vocab (route).checker [] [] (eq (less natOrdT (num 2) (num 3)) falseB)
  (encode vocab (Unfold.evaluation .evaluation (less natOrdT (num 2) (num 3)) falseB)) = .reject

/-! ### Unmet domain guards

Outside its domain an operation is not evaluated, and nothing is refuted:
Bool arguments to the Nat order, Nat arguments to the Bool order. -/

#guard snapshot.evaluate evaluations (less natOrdT trueB (num 3)) = none
#guard snapshot.evaluate evaluations (less boolOrdT (num 2) (num 3)) = none
#guard shape ((route).answer [] (eq (less natOrdT trueB (num 3)) falseB)) = "undecided"
-- The call is outside its contract: `true` is a member tree of Bool, not of
-- Nat. The blocker says so first; asymmetry is named as a law that may conclude
-- the goal (over-approximated, its guards unchecked).
#guard missing ((route).answer [] (eq (less natOrdT trueB (num 3)) falseB)) ==
  [.construct (.dictionary .domain), .lemma .asymmetric]
-- A rigid name may be a member: not outside, only the law is named.
#guard missing ((route).answer [] (eq (less natOrdT a (num 3)) falseB)) == [.lemma .asymmetric]
-- The decision admits arguments in the contract's domains only: an evaluation
-- that also answers outside them decides nothing there.
def loose : List (Evaluation String Data Symbol) :=
  [{ natLess with run := fun args => if args = [trueB, num 3] then some falseB else lessRun false args }]
#guard snapshot.check? loose rules ⟨less natOrdT trueB (num 3), trueB⟩ = none
#guard shape ((route (registered := loose)).answer [] (eq (less natOrdT trueB (num 3)) trueB)) = "undecided"
-- The decision needs a result in the result domain: `less(natOrd, 2, 3) = 2`
-- is not decided.
#guard (snapshot.admits? evaluations rules ⟨less natOrdT (num 2) (num 3), num 2⟩) = false
-- `DomainMember(natOrd, true)` is not derivable from the generated clauses.
#guard (solve (route) [] [] (.app .domainMember [natOrdT, trueB])).kind = .exhausted
#guard (solve (route) [] [] (.app .domainMember [natOrdT, num 2])).kind = .success

/-! ### Missing evaluator evidence

`compare` has no primitive contract, so no evaluation: Undecided, naming the
missing evaluator and the law that may conclude it. An evaluation for another
version of the registration is not used either. -/

def compareGoal : T := eq (compareTerm natOrdT (num 2) (num 3)) ltT
#guard snapshot.evaluate evaluations (compareTerm natOrdT (num 2) (num 3)) = none
#guard missing ((route).answer [] compareGoal) == [.construct (.dictionary .evaluator), .lemma .lessCompare]
def stale : List (Evaluation String Data Symbol) := [{ natLess with version := 0 }]
#guard missing ((route (registered := stale)).answer [] (eq (less natOrdT (num 2) (num 3)) trueB)) ==
  [.construct (.dictionary .evaluator), .lemma .lessCompare]
-- An unknown name is no route, never No. No law is named: every view's first
-- premise is the interface guard, which no unregistered name meets.
#guard missing ((route).answer [] (eq (less aliasT (num 2) (num 3)) trueB)) ==
  [.construct (.dictionary .unknown)]

/-! ### Laws as checked lemmas

Asymmetry has one view, a conditional rule over the dictionary and two
members, proved from the law's fact in the proof layer and checked there. -/

def asymmetryLemmas : List L := asymmetry.lemmas vocab ordDeclaration fun index => .view .asymmetric index
def lessCompareLemmas : List L := lessCompare.lemmas vocab ordDeclaration fun index => .view .lessCompare index

#guard (asymmetry.views ordDeclaration).map (·.binders) = [["d", "x", "y"]]
#guard (asymmetry.views ordDeclaration).map (·.premises.length) = [4]
#guard (lessCompare.views ordDeclaration).length = 2
#guard checkImports vocab (route [] asymmetryLemmas).checker ((asymmetryLemmas ++ lessCompareLemmas).map ProofImport.entry)

-- The goal `less(natOrd, b, a) = false` with `a`, `b` rigid: the evaluator does
-- not answer. The asymmetry view is matched structurally (d := natOrd, y := b,
-- x := a), and its premises are the run's obligations in order:
-- OrdDictionary(natOrd), DomainMember(natOrd, a), DomainMember(natOrd, b),
-- less(natOrd, a, b) = true. They all succeed before the goal closes.
def lawContext : List T := [isNat a, isNat b, eq (less natOrdT a b) trueB]
def lawGoal : T := eq (less natOrdT b a) falseB
def byLaw := solve (route [] asymmetryLemmas) [] lawContext lawGoal
#guard byLaw.kind = .success
#guard lemmaNodes byLaw = [(.view .asymmetric 0, [natOrdT, a, b])]
#guard ((goals byLaw).filter fun goal => match goal with | .app _ _ | .equal _ _ => true | _ => false).take 5 =
  [lawGoal, ordGuard natOrdT, domainMember natOrdT a, isNat a, domainMember natOrdT b]
#guard (goals byLaw).contains (eq (less natOrdT a b) trueB)
#guard verdict (route [] asymmetryLemmas) lawContext lawGoal byLaw = some .accept
#guard shape ((route [] asymmetryLemmas).answer lawContext lawGoal) = "yes"
-- Without the lemma, the goal is Undecided, naming the law.
#guard missing ((route).answer lawContext lawGoal) == [.lemma .asymmetric]
-- With the call on the right the goal is turned around first: the same law.
def turnedGoal : T := eq falseB (less natOrdT b a)
#guard shape ((route [] asymmetryLemmas).answer lawContext turnedGoal) = "yes"
#guard missing ((route).answer lawContext turnedGoal) == [.lemma .asymmetric]
-- A dictionary bound by the run is not reported as a missing binding: the gap
-- keeps the goal as written, and the law is named once, though each of the
-- three candidate dictionaries reached it.
def boundGoal : T := .existsVar "D" (.conj (ordGuard (.var "D")) (eq (less (.var "D") b a) falseB))
#guard missing ((route).answer [isNat a, isNat b] boundGoal) == [.lemma .asymmetric]
#guard match (route).answer [isNat a, isNat b] boundGoal with
  | .undecided blockers => blockers.length == 1
  | _ => false
-- A use that fails its guards: `true` is no member of natOrd's domain. The
-- call is outside its contract.
#guard shape ((route [] asymmetryLemmas).answer [isNat a, eq (less natOrdT a trueB) trueB]
  (eq (less natOrdT trueB a) falseB)) = "undecided"
#guard missing ((route [] asymmetryLemmas).answer [isNat a, eq (less natOrdT a trueB) trueB]
  (eq (less natOrdT trueB a) falseB)) == [.construct (.dictionary .domain)]

-- Rollback restores rejected candidates: with the dictionary a flexible name,
-- OrdDictionary(D) first selects natOrd, whose `less(natOrd, a, b) = true` is
-- not assumed; the binding is undone, and natDesc succeeds.
def flexibleContext : List T := [isNat a, isNat b, eq (less natDescT a b) trueB]
def flexibleGoal : T := eq (less (.var "D") b a) falseB
def rolledBack := solve (route [] asymmetryLemmas) ["D"] flexibleContext flexibleGoal
#guard rolledBack.kind = .success
#guard (rolledBack.proof?.map fun proof => proof.store.resolve (.var "D")) = some natDescT
#guard verdict (route [] asymmetryLemmas) flexibleContext flexibleGoal rolledBack = some .accept

-- `compare` has no evaluator, but the view `compare(d,x,y) = lt :- …,
-- less(d,x,y) = true` concludes it, and its premise is evaluated.
def lessCompareTo : List L := lessCompareLemmas.take 1
#guard ((lessCompare.views ordDeclaration).take 1).map View.conclusion = [eq (compareTerm (.var "d") (.var "x") (.var "y")) ltT]
-- Offering only the other direction leaves this one missing: still named.
#guard missing ((route [] (lessCompareLemmas.drop 1)).answer [] compareGoal) ==
  [.construct (.dictionary .evaluator), .lemma .lessCompare]
def compared := solve (route [] lessCompareTo) [] [] compareGoal
#guard compared.kind = .success
#guard exportedTags compared |>.contains .extension
#guard verdict (route [] lessCompareTo) [] compareGoal compared = some .accept

-- A view binder its conclusion does not mention gets a fresh flexible witness.
def chain : T := .forallVar "d" (.forallVar "x" (.forallVar "y" (.forallVar "z"
  (.imp (.conj (eq (less (.var "d") (.var "x") (.var "y")) trueB)
      (.conj (eq (less (.var "d") (.var "y") (.var "z")) trueB) .truth))
    (eq (less (.var "d") (.var "x") (.var "z")) trueB)))))
#guard ((lawInstance? ["F0", "F1", "F2", "F3"] chain (eq (less natOrdT a (.var "e")) trueB)).map
  fun found => (found.1, found.2.2)) = some ([natOrdT, a, .var "F2", .var "e"], ["F2"])

-- A symmetric law does not become rewriting: with both views of lessCompare
-- offered, `less(natOrd, a, b) = true` backchains from one to the other until
-- the fuel runs out. Undecided, never Yes.
def looping := solve (route [] lessCompareLemmas 400) [] [isNat a, isNat b] (eq (less natOrdT a b) trueB)
#guard looping.kind = .interrupted
#guard missing ((route [] lessCompareLemmas 400).answer [isNat a, isNat b] (eq (less natOrdT a b) trueB)) ==
  [.termination]

/-! ### The theorems, instantiated -/

example : snapshot.Models evaluations interp := models

example : snapshot.Complete evaluations := complete

/-- Every rule of the order signature is listed. -/
theorem covering : ∀ rule, snapshot.signature.signature.data.definitions rule → rule ∈ rules := by
  intro rule declared
  rcases declared with rfl | rfl | rfl | rfl <;> simp [rules]

-- The decision contract in the order model: a Yes is equality of values, a
-- No their difference, under every environment.
#guard snapshot.admits? evaluations rules ⟨less natOrdT (num 2) (num 3), falseB⟩
#guard !snapshot.decide evaluations ⟨less natOrdT (num 2) (num 3), falseB⟩
example (admitted : snapshot.admits? evaluations rules ⟨less natOrdT (num 2) (num 3), falseB⟩ = true)
    (decided : snapshot.decide evaluations ⟨less natOrdT (num 2) (num 3), falseB⟩ = false)
    (environment : Semantics.Environment String Value) :
    model.eval environment (less natOrdT (num 2) (num 3)) ≠ model.eval environment falseB :=
  (snapshot.decision evaluations complete interp models).no _ (Snapshot.admits?_decides listed admitted) decided
    environment
example (decided : snapshot.decide evaluations ⟨less natOrdT (num 2) (num 3), trueB⟩ = true)
    (environment : Semantics.Environment String Value) :
    model.Satisfies environment (eq (less natOrdT (num 2) (num 3)) trueB) :=
  (model.satisfies_equal _ _ _).mpr (Snapshot.decide_sound decided evaluated environment)

-- Every answer of the route means what it says.
example (clauses : List Clause) (lemmas : List L) (context : List T) (goal : T) :
    ((route clauses lemmas).answer context goal).Sound ((route clauses lemmas).meaning context goal) :=
  (route clauses lemmas).answer_sound wellFormed listed context goal

-- Every equation the decision contract decides, the call on either side, is
-- answered Yes or No.
example (clauses : List Clause) (lemmas : List L) (context : List T) (left right : T)
    (decides : snapshot.Decides evaluations ⟨left, right⟩ ∨ snapshot.Decides evaluations ⟨right, left⟩) :
    ((route clauses lemmas).answer context (eq left right)).definite = true :=
  (route clauses lemmas).answer_definite complete covering context decides

-- Every Yes is a term the route's checker accepts.
example (clauses : List Clause) (lemmas : List L) (context : List T) (goal : T) (term : T)
    (answered : (route clauses lemmas).answer context goal = .yes term) :
    checkProof vocab (route clauses lemmas).checker (route clauses lemmas).table context goal term = .accept :=
  (route clauses lemmas).answer_accepted answered

-- The strategy is sound for the checker's KB, and a successful run
-- reconstructs `Derives` there.
example (clauses : List Clause) (lemmas : List L) :
    Strategy.Sound .hoApply (route clauses lemmas).checkSnapshot.kb NafFailure.disabled (route clauses lemmas).strategy :=
  (route clauses lemmas).strategy_sound

example {proof : CompletedProof String Data Symbol Unit Unit} {resume : State String Data Symbol Unit Unit}
    (ran : (route [] asymmetryLemmas).run lawContext lawGoal = .success proof resume) :
    Derives .hoApply (route [] asymmetryLemmas).checkSnapshot.kb (lawContext.map proof.store.resolve)
      (proof.store.resolve lawGoal) NafFailure.disabled :=
  run_init_reconstructs _ (route [] asymmetryLemmas).strategy_sound _ () [] lawContext lawGoal ran

end DictionaryEvaluationTests
