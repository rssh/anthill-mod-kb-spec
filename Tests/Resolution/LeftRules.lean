import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Machine AnthillModKbSpec.P1 AnthillModKbSpec.Admission
  AnthillModKbSpec.InductiveDomains AnthillModKbSpec.AdmissionSignature

namespace LeftRulesTests

/-! Executable traces of S09: left rules on selected assumptions and compound
clause heads, run on the shared machine by the left strategy, exported as S08
logical nodes, and checked. Each `#guard` evaluates compiled code. The
examples at the end instantiate the theorems. -/

inductive Sym where
  | p | q | r | s | t | a | b | c | zero | succ | isNat | allData | isPred | ha
  | tag (tag : Tag)
  deriving DecidableEq, Repr

def vocab : Vocabulary Sym := ⟨Sym.tag, fun _ _ same => by cases same; rfl⟩

abbrev T := Term Nat Nat Sym
abbrev Clause := HornClause Nat Nat Sym
abbrev Run := Outcome Nat Nat Sym Unit Nat
abbrev P := Proof Nat Nat Sym

def k (symbol : Sym) : T := .app symbol []
def atom (symbol : Sym) (args : List T) : T := .app symbol args
def fact (head : T) : Clause := .definite head []
def rule (head : T) (body : List T) : Clause := .definite head body
def same : T → T → Bool := identical
def X : T := .var 0
def x (name : Nat) : T := .var name

def plain (clauses : List Clause) : Program Nat Nat Sym :=
  ⟨clauses.mapIdx fun index clause => ⟨.lowered index, clause⟩, fun _ => false⟩

def query (flexibles : List Nat) (context : List T) (goal : T) : State Nat Nat Sym Unit Nat :=
  State.init 0 flexibles context goal

/-! ### A heuristic selection for the traces

The library takes the selection as a parameter. These traces use a heuristic
one, `relevant`, and add explicit choices where it has none. It splits a
compound assumption once per branch, and uses universal and implication
assumptions and compound heads whose conclusion might conclude the goal, at
fresh flexible witnesses. It has no termination or completeness argument. -/

section Heuristic

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal]
  [FreshNames Variable]


/-- Some reading already holds an instance of `pattern` over `binders`. -/
def holdsInstance (binders : List Variable) (pattern : Term Variable Literal Symbol)
    (reads : List (Term Variable Literal Symbol)) : Bool :=
  reads.any fun read => (extract binders pattern read []).isSome

/-- The leaves of a nested conjunction with their paths. -/
def conjuncts : Term Variable Literal Symbol → List (List Bool × Term Variable Literal Symbol)
  | .conj left right => (conjuncts left).map (fun (path, leaf) => (false :: path, leaf)) ++
      (conjuncts right).map (fun (path, leaf) => (true :: path, leaf))
  | term => [([], term)]

/-- The commands for one assumption, as written and as read. A conjunction is
split unless both components are present, a disjunction unless a disjunct is,
an existential unless an instance of its body is. A universal or implication
assumption whose conclusion is not an atom, and might conclude the goal, is
used at fresh flexible witnesses unless an instance of its conclusion is
present; an atomic conclusion is `positive`'s local rule. -/
def assumptionChoices (hoApplySymbol : Symbol) (goal : Term Variable Literal Symbol)
    (reads : List (Term Variable Literal Symbol)) (assumption read : Term Variable Literal Symbol) :
    List (Choice Variable Literal Symbol) :=
  let present := fun formula => reads.any (identical formula)
  match read with
  | .conj left right => if present left && present right then [] else [.conjUse assumption]
  | .disj left right => if present left || present right then [] else [.disjCases assumption]
  | .existsVar binder body => if holdsInstance [binder] body reads then [] else [.existsOpen assumption]
  | _ =>
      let binders := leadingBinders read
      match stripLeading binders.length read with
      | .imp _ conclusion =>
          if !isFact conclusion && mayConclude hoApplySymbol goal binders conclusion &&
              !holdsInstance binders conclusion reads then [.impUse assumption (binders.map fun _ => none)]
          else []
      | .app _ _ | .falsity => []
      | matrix =>
          if !binders.isEmpty && mayConclude hoApplySymbol goal binders matrix && !holdsInstance binders matrix reads then
            [.forallUse assumption (binders.map fun _ => none)]
          else []

/-- The commands for one program clause with a compound head that might
conclude the goal: a conjunct that might match it, by splitting the head; a
head `A → false`, as a denial, for falsity; any other compound head by
assuming it once its body is proved, unless an instance of the head is
present. -/
def headChoices (hoApplySymbol : Symbol) (goal : Term Variable Literal Symbol)
    (reads : List (Term Variable Literal Symbol)) (clause : HornClause Variable Literal Symbol) :
    List (Choice Variable Literal Symbol) :=
  match clause with
  | .definite head _ =>
      match head with
      | .conj _ _ =>
          (conjuncts head).filterMap fun (path, leaf) =>
            if mayMatch hoApplySymbol goal leaf then some (.headProject clause path) else none
      | .imp _ .falsity => match goal with | .falsity => [.headDenial clause] | _ => []
      | .disj _ _ | .imp _ _ | .forallVar _ _ | .existsVar _ _ =>
          if mayConclude hoApplySymbol goal clause.templates head && !holdsInstance clause.templates head reads then
            [.headUse clause]
          else []
      | _ => []
  | .goal _ => []

/-- A heuristic selection for proof attempts: the commands of every
assumption and of every compound head that might conclude the goal. A truth
or conjunction goal gets none: its introduction rule loses nothing, since
case analysis distributes over the conjuncts. Falsity elimination is not
offered: it is an explicit choice, since a contradiction whose premise again
needs one would recurse. No termination is claimed. -/
def relevant (hoApplySymbol : Symbol) (program : Program Variable Literal Symbol) : Selection Variable Literal Symbol :=
  fun _ _ goal context =>
    match goal with
    | .truth | .conj _ _ => []
    | _ =>
        let reads := context.map Prod.snd
        context.flatMap (fun (assumption, read) => assumptionChoices hoApplySymbol goal reads assumption read) ++
          program.clauses.flatMap (fun entry => headChoices hoApplySymbol goal reads entry.clause)

end Heuristic

/-- Run the left strategy, with the heuristic selection unless another is given. -/
def solve (clauses : List Clause) (state : State Nat Nat Sym Unit Nat)
    (select : Selection Nat Nat Sym := relevant .ha (plain clauses)) (fuel : Nat := 2000) : Run :=
  run (left .ha (plain clauses) select) fuel state

def resume (clauses : List Clause) (outcome : Run) (select : Selection Nat Nat Sym := relevant .ha (plain clauses)) :
    Run :=
  match outcome with
  | .success _ state => run (left .ha (plain clauses) select) 2000 state
  | other => other

def rulesOf (outcome : Run) : Option (List RuleId) := outcome.proof?.map (·.tree.rules)

def answerIs (outcome : Run) (name : Nat) (expected : T) : Bool :=
  match outcome.proof? with
  | some proof => same (proof.answer name) expected
  | none => false

/-- The checker of a run's export: the program's clauses, with no NAF evidence
check and no derived rule. -/
def checker (clauses : List Clause) : Checker Nat Nat Sym := ⟨⟨.ha, clauses⟩, NafFailure.disabled, none, []⟩

def verdict (clauses : List Clause) (context : List T) (goal : T) (proof : P) : Verdict Sym :=
  checkProof vocab (checker clauses) [] context goal (encode vocab proof)

/-- The run's proof as a supplied tree, read through its final store. -/
def exported (outcome : Run) : Option P :=
  outcome.proof?.bind fun proof => exportTree (Certificate := Unit) (fun _ => .truth) proof.store (fun _ _ => none) proof.tree

/-- The exported term is accepted for the answer instance: the context and
goal read through the final answers. -/
def checks (clauses : List Clause) (context : List T) (goal : T) (outcome : Run) : Bool :=
  match outcome.proof? with
  | some proof =>
      match exportProof vocab (fun _ => .truth) proof with
      | some term =>
          decide (checkProof vocab (checker clauses) [] (context.map proof.store.resolve) (proof.store.resolve goal) term
            = .accept)
      | none => false
  | none => false

/-- The rules of a supplied tree in preorder, by their encoding tags. -/
partial def tags : P → List Tag
  | .node rule _ premises =>
      (match encodeRule vocab rule with | .app (.tag tag) _ => [tag] | _ => []) ++ premises.flatMap tags

def exportedTags (outcome : Run) : Option (List Tag) := (exported outcome).map tags

/-- The exported tree needs nothing beyond the shared rules: no derived rule,
NAF evidence check, or reference. -/
def logicalOnly (outcome : Run) : Bool :=
  match exported outcome with
  | some tree => tree.requires.isEmpty
  | none => false

mutual
def nodes : ProofTree Nat Nat Sym Unit → List (ProofTree Nat Nat Sym Unit)
  | .node rule obligation premises subproofs => .node rule obligation premises subproofs :: nodesOf subproofs
  | .deferred _ _ => []

def nodesOf : List (ProofTree Nat Nat Sym Unit) → List (ProofTree Nat Nat Sym Unit)
  | [] => []
  | tree :: trees => nodes tree ++ nodesOf trees
end

/-- The S09 command nodes of a run's tree, in preorder. -/
def commandNodes (outcome : Run) : List (ProofTree Nat Nat Sym Unit) :=
  match outcome.proof? with
  | some proof => (nodes proof.tree).filter fun | .node (.derived _) _ _ _ => true | _ => false
  | none => []

/-- The assumptions each subproof of a node adds to its parent's, read through
the final store. -/
def addedBy (outcome : Run) : ProofTree Nat Nat Sym Unit → List (List T)
  | .node _ parent _ subproofs =>
      match outcome.proof? with
      | some proof => subproofs.map fun tree =>
          (tree.obligation.scope.assumptions.take
            (tree.obligation.scope.assumptions.length - parent.scope.assumptions.length)).map proof.store.resolve
      | none => []
  | .deferred _ _ => []

/-- A selection offering no S09 command. -/
def never : Selection Nat Nat Sym := fun _ _ _ _ => []

/-- The heuristic selection, then explicit choices for a goal as read. -/
def also (clauses : List Clause) (extra : T → List T → List (Choice Nat Nat Sym)) : Selection Nat Nat Sym :=
  fun obligation store goal context =>
    relevant .ha (plain clauses) obligation store goal context ++ extra goal (context.map Prod.snd)

/-! ### Implication selection: prove A, then B is available for C -/

-- q → (p ∧ s) assumed, the fact q, goal s. The implication is selected for
-- s: its premise q is the first focus, under the original scope, and only
-- then does p ∧ s join the context, where it is split and closes s.
def impContext : List T := [.imp (k .q) (.conj (k .p) (k .s))]
def impRun := solve [fact (k .q)] (query [] impContext (k .s))
#guard match step (left (Certificate := Unit) .ha (plain [fact (k .q)]) (relevant .ha (plain [fact (k .q)])))
    (query [] impContext (k .s)) with
  | .running state =>
      match state.focus with
      | .solve obligation => same obligation.goal (k .q) && obligation.scope.assumptions.length == 1
      | _ => false
  | .finished _ => false
#guard rulesOf impRun = some [.impUse, .clause, .truth, .conjUse, .assumption]
-- The export spells the selection out in the original context: B by impElim,
-- B discharged from the continuation by impIntro, C by impElim. The split of
-- p ∧ s is two more cuts by projection.
#guard exportedTags impRun = some [.impElim, .impIntro, .impElim, .impIntro, .impElim, .impIntro, .assumption,
  .conjLeft, .assumption, .conjRight, .assumption, .impElim, .assumption, .clause, .truth]
#guard checks [fact (k .q)] impContext (k .s) impRun
#guard logicalOnly impRun

-- Selected for s, its premise q has no proof here: exhausted, and nothing
-- about s or q follows.
#guard (solve [] (query [] impContext (k .s))).kind = .exhausted

-- Assuming q → p does not run q: with the looping clause q :- q, the goal
-- (q → p) → r is exhausted without ever focusing q.
#guard (solve [rule (k .q) [k .q]] (query [] [] (.imp (.imp (k .q) (k .p)) (k .r)))).kind = .exhausted

-- A compound conclusion at a fresh flexible witness, bound by the premise:
-- ∀1. (q(1) → (p(1) ∨ s(1))), q(a), ∀2. (s(2) → p(2)) prove p(a).
def witnessContext : List T :=
  [.forallVar 1 (.imp (atom .q [x 1]) (.disj (atom .p [x 1]) (atom .s [x 1]))), atom .q [k .a],
    .forallVar 2 (.imp (atom .s [x 2]) (atom .p [x 2]))]
def witnessRun := solve [] (query [] witnessContext (atom .p [k .a]))
#guard witnessRun.kind = .success
#guard match commandNodes witnessRun, witnessRun.proof? with
  | .node (.derived (.impUse _ [witness])) _ _ _ :: _, some proof => same (proof.store.resolve witness) (k .a)
  | _, _ => false
#guard checks [] witnessContext (atom .p [k .a]) witnessRun

-- R12: goal p under q and q → (s ∨ p). Implication-left proves q, then p is
-- proved in both cases; s and p are never asserted together, so the case s
-- fails without s → p.
def r12Context (bridge : Bool) : List T :=
  [k .q, .imp (k .q) (.disj (k .s) (k .p))] ++ if bridge then [.imp (k .s) (k .p)] else []
#guard (solve [] (query [] (r12Context false) (k .p))).kind = .exhausted
def r12Run := solve [] (query [] (r12Context true) (k .p))
#guard rulesOf r12Run = some [.impUse, .assumption, .disjCases, .impElim, .assumption, .assumption, .assumption]
#guard checks [] (r12Context true) (k .p) r12Run

-- A matcher gap stays a gap: a local rule whose head differs from the goal
-- only by `ho_apply` needs S11's conversion, so the run is unknown, never
-- exhausted, as for `positive`.
#guard (solve [] (query [] [.imp (k .q) (Term.hoApply .ha (k .p) [k .a]), k .q] (atom .p [k .a]))).kind = .unknown

-- A conjunction is split once per branch: under p ∧ q, r has no proof.
#guard (solve [] (query [] [.conj (k .p) (k .q)] (k .r))).kind = .exhausted

/-! ### Disjunctive assumptions: two AND contexts -/

-- q ∨ p under p ∨ q: case analysis, each case proving the goal by a
-- different disjunct.
def swapRun := solve [] (query [] [.disj (k .p) (k .q)] (.disj (k .q) (k .p)))
#guard rulesOf swapRun = some [.disjCases, .disjRight, .assumption, .disjLeft, .assumption]
#guard exportedTags swapRun = some [.disjElim, .assumption, .disjRight, .assumption, .disjLeft, .assumption]
#guard checks [] [.disj (k .p) (k .q)] (.disj (k .q) (k .p)) swapRun
-- Each case's subproof adds exactly its own disjunct.
#guard match commandNodes swapRun with
  | node :: _ =>
      match addedBy swapRun node with
      | [[first], [second]] => same first (k .p) && same second (k .q)
      | _ => false
  | [] => false

-- Incompatible answers: p(X) under p(a) ∨ p(b). The first case binds X := a,
-- which the second case cannot prove: exhausted, no answer.
#guard (solve [] (query [0] [.disj (atom .p [k .a]) (atom .p [k .b])] (atom .p [X]))).kind = .exhausted
-- Compatible answers: under p(a) ∨ q(a) and ∀1. (q(1) → p(1)) both cases
-- prove p(a); the answer is a, and resuming is exhausted.
def sharedContext : List T := [.disj (atom .p [k .a]) (atom .q [k .a]), .forallVar 1 (.imp (atom .q [x 1]) (atom .p [x 1]))]
def sharedRun := solve [] (query [0] sharedContext (atom .p [X]))
#guard answerIs sharedRun 0 (k .a)
#guard (resume [] sharedRun).kind = .exhausted
#guard checks [] sharedContext (atom .p [X]) sharedRun

-- Branch-local assumptions do not leak: in (q ∨ p) ∧ p under p ∨ q, the case
-- p of the first conjunct does not reach the second conjunct, nor the case q.
#guard (solve [] (query [] [.disj (k .p) (k .q)] (.conj (.disj (k .q) (k .p)) (k .p)))).kind = .exhausted
-- Disjunctive syllogism: p ∨ q and p → false prove q, the first case by
-- contradiction.
def syllogismRun := solve [] (query [] [.disj (k .p) (k .q), .imp (k .p) .falsity] (k .q)) (also [] fun goal reads =>
  if same goal (k .q) && reads.any (same (k .p)) then [.contradiction] else [])
#guard rulesOf syllogismRun = some [.disjCases, .falsityElim, .impElim, .assumption, .assumption, .assumption]
#guard checks [] [.disj (k .p) (k .q), .imp (k .p) .falsity] (k .q) syllogismRun

-- A failed command attempt proves nothing about the goal: with no command
-- selected the same goal is exhausted, while the run above and the checked
-- tree below prove it.
#guard (solve [] (query [] [.disj (k .p) (k .q)] (.disj (k .q) (k .p))) never).kind = .exhausted

/-! ### Existential assumptions: a fresh local rigid witness -/

-- ∃2. p(2) under ∃1. p(1): the assumption is opened first, and the goal's
-- witness is created inside its scope.
def existsRun := solve [] (query [] [.existsVar 1 (atom .p [x 1])] (.existsVar 2 (atom .p [x 2])))
#guard rulesOf existsRun = some [.existsOpen, .existsIntro, .assumption]
#guard exportedTags existsRun = some [.existsElim, .assumption, .existsIntro, .assumption]
#guard checks [] [.existsVar 1 (atom .p [x 1])] (.existsVar 2 (atom .p [x 2])) existsRun
-- The opened witness is fresh for the context, the existential, and the goal.
#guard match commandNodes existsRun with
  | .node (.derived (.existsOpen _ eigen)) obligation _ _ :: _ =>
      !(obligation.freeVars.contains eigen) && eigen != 1 && eigen != 2
  | _ => false
-- The witness does not escape through an answer: p(X) with X a root answer
-- would need X := the opened witness.
#guard (solve [] (query [9] [.existsVar 1 (atom .p [x 1])] (atom .p [x 9]))).kind = .exhausted
-- Nor through a name created outside its scope: ∃2. ((∃1. p(1)) → p(2)).
#guard (solve [] (query [] [] (.existsVar 2 (.imp (.existsVar 1 (atom .p [x 1])) (atom .p [x 2]))))).kind = .exhausted

-- R11: ∃1. naf p(1) assumed. It is opened at a local rigid witness, and its
-- negative assumption closes ∃2. naf p(2) by identity: the proof has no NAF
-- node, so no failure search runs.
def r11Run := solve [] (query [] [.existsVar 1 (.defaultNeg (atom .p [x 1]))] (.existsVar 2 (.defaultNeg (atom .p [x 2]))))
#guard rulesOf r11Run = some [.existsOpen, .existsIntro, .assumption]
#guard checks [] [.existsVar 1 (.defaultNeg (atom .p [x 1]))] (.existsVar 2 (.defaultNeg (atom .p [x 2]))) r11Run

/-! ### Universal assumptions: explicit, capture-safe instances -/

-- ∀1. ∀2. (p(1, 2) ∨ q(1, 2)) instantiated at 1 := 2, a parameter, and
-- 2 := c. The inner binder 2 is renamed, so the instance is about the
-- parameter: p(2, c) ∨ q(2, c), and r(2) follows by cases.
def captureContext : List T :=
  [.forallVar 1 (.forallVar 2 (.disj (atom .p [x 1, x 2]) (atom .q [x 1, x 2]))),
    .forallVar 3 (.forallVar 4 (.imp (atom .p [x 3, x 4]) (atom .r [x 3]))),
    .forallVar 5 (.forallVar 6 (.imp (atom .q [x 5, x 6]) (atom .r [x 5])))]
def captureRule : T := .forallVar 1 (.forallVar 2 (.disj (atom .p [x 1, x 2]) (atom .q [x 1, x 2])))
/-- Use the rule at 1 := 2 and 2 := c for `goal`, once per branch. -/
def captureChoice (goal : T) : T → List T → List (Choice Nat Nat Sym) := fun focus reads =>
  if reads.any fun read => same read (.disj (atom .p [x 2, k .c]) (atom .q [x 2, k .c])) then []
  else if same focus goal then [.forallUse captureRule [some (x 2), some (k .c)]] else []
def captureRun := solve [] (query [] captureContext (atom .r [x 2])) (also [] (captureChoice (atom .r [x 2])))
#guard captureRun.kind = .success
#guard match commandNodes captureRun with
  | node :: _ =>
      match addedBy captureRun node with
      | [[added]] => same added (.disj (atom .p [x 2, k .c]) (atom .q [x 2, k .c]))
      | _ => false
  | [] => false
#guard checks [] captureContext (atom .r [x 2]) captureRun
-- The instance is about the parameter 2, not c: with 2 declared by s(2),
-- r(c) does not follow from it.
#guard (solve [] (query [] (captureContext ++ [atom .s [x 2]]) (atom .r [k .c]))
  (also [] (captureChoice (atom .r [k .c])))).kind = .exhausted
-- A witness must name declared names in scope: where 2 is no parameter of the
-- query, the commit refuses the instance, a contract gap and no answer.
#guard match solve [] (query [] captureContext (atom .r [k .c])) (also [] (captureChoice (atom .r [k .c]))) with
  | .unknown gaps => gaps.any (·.reason == .contract)
  | _ => false

-- A captured parameter is kept: ∀1. (p(1) ∨ q(7)) at 1 := a gives p(a) ∨ q(7),
-- with 7 still free; s follows from p(a) → s and q(7) → s, not from q(8) → s.
def keptChoice : T → List T → List (Choice Nat Nat Sym) := fun goal reads =>
  if reads.any fun read => same read (.disj (atom .p [k .a]) (atom .q [x 7])) then []
  else if same goal (k .s) then [.forallUse (.forallVar 1 (.disj (atom .p [x 1]) (atom .q [x 7]))) [some (k .a)]] else []
def keptContext (other : Nat) : List T :=
  [.forallVar 1 (.disj (atom .p [x 1]) (atom .q [x 7])), .imp (atom .p [k .a]) (k .s), .imp (atom .q [x other]) (k .s)]
#guard (solve [] (query [] (keptContext 7) (k .s)) (also [] keptChoice)).kind = .success
#guard (solve [] (query [] (keptContext 8) (k .s)) (also [] keptChoice)).kind = .exhausted

-- Only explicit binders are instantiated: ∀1. ∀2. (p(1) ∨ q(2)) at 1 := a
-- adds ∀2. (p(a) ∨ q(2)), still universal, for the goal unchanged.
def partialRule : T := .forallVar 1 (.forallVar 2 (.disj (atom .p [x 1]) (atom .q [x 2])))
#guard match (Choice.forallUse partialRule [some (k .a)]).attempt (Certificate := Unit) .ha (plain [])
    (Obligation.root [] [partialRule] (k .r)) Store.empty [] with
  | some (some expansion) =>
      match expansion.premises with
      | [premise] =>
          match premise.discharge.assumptions with
          | [added] => same added (.forallVar 2 (.disj (atom .p [k .a]) (atom .q [x 2]))) && same premise.goal (k .r) &&
              expansion.flexibles.isEmpty
          | _ => false
      | _ => false
  | _ => false
-- An assumption that is not the obligation's own is no choice: a miss.
#guard match (Choice.forallUse partialRule [some (k .a)]).attempt (Certificate := Unit) .ha (plain [])
    (Obligation.root [] [] (k .r)) Store.empty [] with
  | some none => true
  | _ => false

-- Repeated use with different witnesses: ∀1. (p(1) ∨ q(1)) at a for r(a) and
-- at b for r(b), with ∀2. (p(2) → r(2)) and ∀3. (q(3) → r(3)).
def repeatContext : List T :=
  [.forallVar 1 (.disj (atom .p [x 1]) (atom .q [x 1])), .forallVar 2 (.imp (atom .p [x 2]) (atom .r [x 2])),
    .forallVar 3 (.imp (atom .q [x 3]) (atom .r [x 3]))]
def repeatChoice : T → List T → List (Choice Nat Nat Sym) := fun goal reads =>
  [k .a, k .b].filterMap fun witness =>
    if same goal (atom .r [witness]) && !(reads.any fun read => same read (.disj (atom .p [witness]) (atom .q [witness])))
    then some (.forallUse (.forallVar 1 (.disj (atom .p [x 1]) (atom .q [x 1]))) [some witness]) else none
def repeatRun := solve [] (query [] repeatContext (.conj (atom .r [k .a]) (atom .r [k .b]))) (also [] repeatChoice)
#guard repeatRun.kind = .success
def usedWitnesses (outcome : Run) : List T :=
  (commandNodes outcome).filterMap fun
    | .node (.derived (.forallUse _ [witness])) _ _ _ => some witness
    | _ => none
#guard match usedWitnesses repeatRun with
  | [first, second] => same first (k .a) && same second (k .b)
  | _ => false
#guard checks [] repeatContext (.conj (atom .r [k .a]) (atom .r [k .b])) repeatRun

/-! ### Compound clause heads -/

-- A conjunctive head splits: p(X) ∧ q(X) :- r(X) concludes q(a) and p(a)
-- from r(a), by projection.
def conjKb : List Clause := [rule (.conj (atom .p [X]) (atom .q [X])) [atom .r [X]], fact (atom .r [k .a])]
def splitRun := solve conjKb (query [] [] (atom .q [k .a]))
#guard rulesOf splitRun = some [.headProject, .conjIntro, .clause, .truth, .truth]
#guard exportedTags splitRun = some [.conjRight, .clause, .conjIntro, .clause, .truth, .truth]
#guard checks conjKb [] (atom .q [k .a]) splitRun
#guard checks conjKb [] (atom .p [k .a]) (solve conjKb (query [] [] (atom .p [k .a])))
#guard (solve conjKb (query [] [] (atom .q [k .b]))).kind = .exhausted

-- A disjunctive head is used by case analysis once its body is proved:
-- p ∨ q :- r, the fact r, and p → s, q → s prove s.
def disjKb : List Clause := [rule (.disj (k .p) (k .q)) [k .r], fact (k .r)]
/-- Use the disjunctive head for s, once per branch: it does not conclude s by
itself, so the heuristic selection does not choose it. -/
def disjChoice (clauses : List Clause) : Selection Nat Nat Sym :=
  also clauses fun goal reads =>
    if same goal (k .s) && !(reads.any (same (.disj (k .p) (k .q)))) then [.headUse (rule (.disj (k .p) (k .q)) [k .r])]
    else []
def headRun := solve disjKb (query [] [.imp (k .p) (k .s), .imp (k .q) (k .s)] (k .s)) (disjChoice disjKb)
#guard rulesOf headRun = some [.headUse, .conjIntro, .clause, .truth, .truth, .disjCases, .impElim, .assumption,
  .assumption, .impElim, .assumption, .assumption]
#guard checks disjKb [.imp (k .p) (k .s), .imp (k .q) (k .s)] (k .s) headRun
-- A disjunct is never taken as established: without q → s, the case q fails.
#guard (solve disjKb (query [] [.imp (k .p) (k .s)] (k .s)) (disjChoice disjKb)).kind = .exhausted
-- No head before its body: without the fact r, nothing follows.
#guard (solve [rule (.disj (k .p) (k .q)) [k .r]] (query [] [.imp (k .p) (k .s), .imp (k .q) (k .s)] (k .s))
  (disjChoice [rule (.disj (k .p) (k .q)) [k .r]])).kind = .exhausted

-- A head p → q stays a local rule once its body is proved: with r and p, q.
def ruleKb : List Clause := [rule (.imp (k .p) (k .q)) [k .r], fact (k .r), fact (k .p)]
#guard rulesOf (solve ruleKb (query [] [] (k .q))) =
  some [.headUse, .conjIntro, .clause, .truth, .truth, .impElim, .assumption, .clause, .truth]
#guard checks ruleKb [] (k .q) (solve ruleKb (query [] [] (k .q)))
#guard (solve [rule (.imp (k .p) (k .q)) [k .r], fact (k .p)] (query [] [] (k .q))).kind = .exhausted

-- A logical-not head is conditional falsity: ¬p(X) :- r(X), as false :- r(X), p(X).
def negationKb (pFact : Bool) : List Clause :=
  [rule (.imp (atom .p [X]) .falsity) [atom .r [X]], fact (atom .r [k .a])] ++ if pFact then [fact (atom .p [k .a])] else []
def denialRun := solve (negationKb true) (query [] [] .falsity)
#guard rulesOf denialRun = some [.headDenial, .conjIntro, .clause, .truth, .truth, .clause, .truth]
#guard exportedTags denialRun = some [.impElim, .clause, .conjIntro, .clause, .truth, .truth, .clause, .truth]
#guard checks (negationKb true) [] .falsity denialRun
/-- Falsity elimination for `goal`, an explicit choice. -/
def refute (clauses : List Clause) (goal : T) : Selection Nat Nat Sym :=
  also clauses fun focus _ => if same focus goal then [.contradiction] else []
-- Another goal follows by falsity elimination.
#guard rulesOf (solve (negationKb true) (query [] [] (k .t)) (refute (negationKb true) (k .t))) =
  some [.falsityElim, .headDenial, .conjIntro, .clause, .truth, .truth, .clause, .truth]
#guard (solve (negationKb false) (query [] [] .falsity)).kind = .exhausted

-- An existential head introduces a local witness when used: ∃1. p(1) :- r.
def existsKb : List Clause := [rule (.existsVar 1 (atom .p [x 1])) [k .r], fact (k .r)]
def existsHeadRun := solve existsKb (query [] [] (.existsVar 2 (atom .p [x 2]))) (also existsKb fun goal reads =>
  if same goal (.existsVar 2 (atom .p [x 2])) && !(reads.any (same (.existsVar 1 (atom .p [x 1])))) then
    [.headUse (rule (.existsVar 1 (atom .p [x 1])) [k .r])]
  else [])
#guard rulesOf existsHeadRun = some [.headUse, .conjIntro, .clause, .truth, .truth, .existsOpen, .existsIntro, .assumption]
#guard checks existsKb [] (.existsVar 2 (atom .p [x 2])) existsHeadRun

/-! ### Falsity -/

-- p → false and p prove any goal by falsity elimination. Positive execution,
-- which only uses an assumed false, is exhausted.
#guard rulesOf (solve [] (query [] [.imp (k .p) .falsity, k .p] (k .q)) (refute [] (k .q))) =
  some [.falsityElim, .impElim, .assumption, .assumption]
#guard (run (positive (Certificate := Unit) .ha (plain [])) 2000 (query [] [.imp (k .p) .falsity, k .p] (k .q))).kind
  = .exhausted

/-! ### Checking the constructions directly

The S08 checker decides each construction's nodes; a construction whose
premise trees are checked under other contexts than the command gives them is
rejected. -/

-- Implication: q is proved in the original context. An argument that uses
-- the conclusion p, available only to the continuation, is rejected.
def impTree (argument : P) : P :=
  Unfold.impUse (.imp (k .q) (k .p)) [] (k .p) (k .s) argument
    (Unfold.impUse (.imp (k .p) (k .s)) [] (k .s) (k .s) (Unfold.hypothesis (k .p)) (Unfold.hypothesis (k .s)))
#guard verdict [] [.imp (k .q) (k .p), k .q, .imp (k .p) (k .s)] (k .s) (impTree (Unfold.hypothesis (k .q))) = .accept
#guard verdict [] [.imp (k .q) (k .p), .imp (k .p) (k .s)] (k .s) (impTree (Unfold.hypothesis (k .p))) = .reject

-- Disjunction: each case under its own assumption; a second case that uses
-- the first case's assumption is rejected.
#guard verdict [] [.disj (k .p) (k .q)] (.disj (k .q) (k .p))
  (Unfold.disjCases (k .p) (k .q) (.disj (k .q) (k .p))
    (.node .disjRight (.disj (k .q) (k .p)) [Unfold.hypothesis (k .p)])
    (.node .disjLeft (.disj (k .q) (k .p)) [Unfold.hypothesis (k .q)])) = .accept
#guard verdict [] [.disj (k .p) (k .q)] (.disj (k .q) (k .p))
  (Unfold.disjCases (k .p) (k .q) (.disj (k .q) (k .p))
    (.node .disjRight (.disj (k .q) (k .p)) [Unfold.hypothesis (k .p)])
    (.node .disjRight (.disj (k .q) (k .p)) [Unfold.hypothesis (k .p)])) = .reject

-- Existential: the eigenvariable is fresh for the context, the existential,
-- and the goal.
def openTree (eigen : Nat) (goal : T) : P :=
  Unfold.existsOpen (.existsVar 1 (atom .p [x 1])) eigen (atom .p [x eigen]) goal
    (.node (.existsIntro (x eigen)) goal [Unfold.hypothesis (atom .p [x eigen])])
#guard verdict [] [.existsVar 1 (atom .p [x 1])] (.existsVar 2 (atom .p [x 2])) (openTree 5 (.existsVar 2 (atom .p [x 2])))
  = .accept
#guard verdict [] [.existsVar 1 (atom .p [x 1]), atom .q [x 5]] (.existsVar 2 (atom .p [x 2]))
  (openTree 5 (.existsVar 2 (atom .p [x 2]))) = .reject
#guard verdict [] [.existsVar 1 (atom .p [x 1, x 5])] (.existsVar 2 (atom .p [x 2]))
  (Unfold.existsOpen (.existsVar 1 (atom .p [x 1, x 5])) 5 (atom .p [x 5, x 5]) (.existsVar 2 (atom .p [x 2]))
    (.node (.existsIntro (x 5)) (.existsVar 2 (atom .p [x 2])) [Unfold.hypothesis (atom .p [x 5])])) = .reject
#guard verdict [] [.existsVar 1 (atom .p [x 1])] (atom .p [x 5])
  (Unfold.existsOpen (.existsVar 1 (atom .p [x 1])) 5 (atom .p [x 5]) (atom .p [x 5]) (Unfold.hypothesis (atom .p [x 5])))
  = .reject

-- Universal: each step's instance is decided by capture-avoiding
-- substitution; the capturing instance ∀2. p(2, 2) is rejected.
def chainTree (instantiated : T) : P :=
  Unfold.forallUse (.forallVar 1 (.forallVar 2 (atom .p [x 1, x 2]))) [(x 2, instantiated)] instantiated instantiated
    (Unfold.hypothesis instantiated)
#guard verdict [] [.forallVar 1 (.forallVar 2 (atom .p [x 1, x 2]))] (.forallVar 3 (atom .p [x 2, x 3]))
  (chainTree (.forallVar 3 (atom .p [x 2, x 3]))) = .accept
#guard verdict [] [.forallVar 1 (.forallVar 2 (atom .p [x 1, x 2]))] (.forallVar 2 (atom .p [x 2, x 2]))
  (chainTree (.forallVar 2 (atom .p [x 2, x 2]))) = .reject

/-! ### Static diagnostics: proof-layer capabilities beside P0

P0 admission asks for evidence for these formulas; the diagnosis names the S09
commands that use each one in the proof layer. The input is still not
admitted for automatic execution. -/

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

def kb (clauses : List Clause) : Program Nat Nat Sym :=
  ⟨clauses.mapIdx (fun index clause => ⟨.lowered index, clause⟩) ++
    (signatureClauses snapshot names rules).map (⟨.signature, ·⟩), guardSymbol snapshot⟩

def input (clauses : List Clause) (context : List T) (goal : T) : Input Dom Nat Nat Sym :=
  ⟨snapshot, names, rules, listed, complete, distinct, kb clauses, fun _ => guardSymbol_iff, context, goal⟩

def diagnosed (clauses : List Clause) (context : List T) (goal : T) : List (Site × ProofLayer) :=
  (diagnose .ha (input clauses context goal)).map fun (request, layer) => (request.site, layer)

#guard diagnosed [] [.disj (k .p) (k .q)] (k .q) = [(.assumption 0, .commands [.disjCases])]
#guard diagnosed [] [.imp (k .q) (.conj (k .p) (k .s))] (k .s) = [(.assumption 0, .commands [.impUse])]
#guard diagnosed [] [.existsVar 1 (atom .p [x 1])] (k .q) = [(.assumption 0, .commands [.existsOpen])]
#guard diagnosed [rule (.conj (k .p) (k .q)) [k .r], fact (k .r)] [] (k .q) =
  [(.head 0, .commands [.headProject, .headUse])]
#guard diagnosed [rule (.imp (k .p) .falsity) [k .r]] [] (k .q) = [(.head 0, .commands [.headDenial, .headUse])]
#guard diagnosed [.goal [k .r]] [] (k .q) = [(.head 0, .commands [.goalClause, .falsityElim])]
#guard diagnosed [] [] (.imp (k .p) (k .p)) = [(.goal, .introduction)]
-- A name inside a NAF operand has S10's refutation route: at a rigid query
-- parameter, and at a clause variable of a body goal.
#guard diagnosed [] [] (.defaultNeg (atom .p [x 5])) = [(.goal, .refutation)]
-- A formula variable as the operand is not refuted.
#guard diagnosed [] [] (.defaultNeg (x 5)) = [(.goal, .none)]
#guard diagnosed [rule (atom .q [X]) [atom .r [X], .defaultNeg (atom .p [X])]] [] (k .s) =
  [(.head 0, .none), (.body 0 0, .none), (.body 0 1, .refutation)]
-- A P0 input has nothing to diagnose.
#guard diagnosed [fact (k .q)] [] (k .q) = []

/-! ### The theorems, instantiated -/

/-- A successful left run reconstructs `Derives` for its answer instance. -/
example {proof : CompletedProof Nat Nat Sym Unit Nat} {resume : State Nat Nat Sym Unit Nat}
    (ran : run (left .ha (plain [fact (k .q)]) (relevant .ha (plain [fact (k .q)]))) 2000 (query [] impContext (k .s)) =
      .success proof resume) :
    Derives Sym.ha (plain [fact (k .q)]).kb (impContext.map proof.store.resolve) (proof.store.resolve (k .s)) :=
  left_reconstructs (naf := NafFailure.disabled) _ _ 2000 0 [] impContext (k .s) ran

/-- The implication construction is valid whenever its premise trees are, the
premise in the original context and the continuation under the conclusion. -/
example {context : List T} {argument continuation : P} (member : .imp (k .q) (k .p) ∈ context)
    (argues : Proves (checker []) (fun _ _ _ => False) context (k .q) argument)
    (continues : Proves (checker []) (fun _ _ _ => False) (k .p :: context) (k .s) continuation) :
    Proves (checker []) (fun _ _ _ => False) context (k .s)
      (Unfold.impUse (.imp (k .q) (k .p)) [] (k .p) (k .s) argument continuation) :=
  Unfold.impUse_proves member .nil argues continues

/-- A diagnosed input is never Ready. -/
example {entry : Request Nat Nat Sym × ProofLayer} (member : entry ∈ diagnose .ha (input [] [.disj (k .p) (k .q)] (k .q)))
    (plan : Plan Dom Nat Nat Sym .ha) : check .ha (input [] [.disj (k .p) (k .q)] (k .q)) ≠ .ready plan :=
  diagnose_not_ready member plan

end LeftRulesTests
