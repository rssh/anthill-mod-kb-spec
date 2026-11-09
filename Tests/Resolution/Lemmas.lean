import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Machine AnthillModKbSpec.P1 AnthillModKbSpec.Admission
  AnthillModKbSpec.InductiveDomains AnthillModKbSpec.AdmissionSignature

namespace LemmaTests

attribute [local instance] termEq

/-! Executable traces of S20: checked lemmas used inside machine runs by the
left strategy with lemmas, exported with references, and checked. Each
`#guard` evaluates compiled code. The examples at the end instantiate the
theorems. -/

inductive Sym where
  | p | q | r | s | t | u | v | w | a | b | c | f | zero | succ | isNat | allData | isPred | ha
  | univ | ctx | negated | self | cases | law | pa
  | tag (tag : Tag)
  deriving DecidableEq, Repr

def vocab : Vocabulary Sym := ⟨Sym.tag, fun _ _ same => by cases same; rfl⟩

abbrev T := Term Nat Nat Sym
abbrev Clause := HornClause Nat Nat Sym
abbrev Run := Outcome Nat Nat Sym Unit Nat
abbrev P := Proof Nat Nat Sym
abbrev L := Lemma Unit Nat Nat Sym

def k (symbol : Sym) : T := .app symbol []
def atom (symbol : Sym) (args : List T) : T := .app symbol args
def fact (head : T) : Clause := .definite head []
def rule (head : T) (body : List T) : Clause := .definite head body
def naf (goal : T) : T := .defaultNeg goal
def node (rule : Rule Nat Nat Sym) (conclusion : T) (premises : List P := []) : P := .node rule conclusion premises

/-- The proof of a clause body: a conjunction node per goal, ending in truth. -/
def body : List P → P
  | [] => node .truth .truth
  | proof :: rest => node .conjIntro (.conj proof.conclusion (body rest).conclusion) [proof, body rest]

/-- A clause step with its instantiation, conclusion, and body proofs. -/
def step (clause : Clause) (instantiation : List (Nat × T)) (goal : T) (goals : List P) : P :=
  node (.clause clause instantiation) goal [body goals]

def plain (clauses : List Clause) : Program Nat Nat Sym :=
  ⟨clauses.mapIdx fun index clause => ⟨.lowered index, clause⟩, fun _ => false⟩

def query (flexibles : List Nat) (context : List T) (goal : T) : State Nat Nat Sym Unit Nat :=
  State.init 0 flexibles context goal

/-- A lemma entry: its name, context, statement, and proof term, with no
binder ranges of interest. -/
def lemma (name : Sym) (context : List T) (statement : T) (proof : P) : L :=
  ⟨⟨name, context, statement, encode vocab proof⟩, fun _ => .allData⟩

def table (lemmas : List L) : List (Import Nat Nat Sym) := lemmas.map ProofImport.entry

/-! ### The proof layer's checker

NAF evidence for `naf v` is accepted only in the empty context: evidence
indexed by the context it was computed under, as P0's and S10's are. -/

def emptyFailure : NafFailure Nat Nat Sym := fun _ _ context operand => context = [] ∧ operand = k .v

def onlyEmpty (snapshot : P1.Snapshot Nat Nat Sym) : NafCheck snapshot emptyFailure :=
  ⟨fun context operand _ => context.isEmpty && identical operand (k .v), fun context operand _ accepted => by
    simp only [Bool.and_eq_true, List.isEmpty_iff, identical_iff] at accepted
    exact accepted⟩

/-- A checker over a KB, with that NAF evidence check and no derived rule. -/
def layer (clauses : List Clause) : Checker Nat Nat Sym := ⟨⟨.ha, clauses⟩, emptyFailure, some (onlyEmpty _), []⟩

/-! ### Runs -/

def noChoice : Selection Nat Nat Sym := fun _ _ _ _ => []
def noCut : LemmaSelection Nat Nat Sym := fun _ _ _ _ => []

/-- Split a disjunctive assumption once per branch: unless a disjunct is
already present. -/
def splits : Selection Nat Nat Sym := fun _ _ _ context =>
  let reads := context.map Prod.snd
  context.filterMap fun (assumption, read) =>
    match read with
    | .disj left right => if reads.any (identical left) || reads.any (identical right) then none else some (.disjCases assumption)
    | _ => none

/-- Cut on a lemma, at no witness, unless its statement is already assumed. -/
def cutOnce (name : Sym) (statement : T) : LemmaSelection Nat Nat Sym := fun _ _ _ context =>
  if context.any fun pair => identical pair.2 statement then [] else [(name, [])]

/-- Run the left strategy with the lemmas the program sees under the checker. -/
def solve (checker : Checker Nat Nat Sym) (clauses : List Clause) (lemmas : List L) (state : State Nat Nat Sym Unit Nat)
    (select : Selection Nat Nat Sym := noChoice) (cuts : LemmaSelection Nat Nat Sym := noCut) : Run :=
  run (withLemmas .ha (plain clauses) (lemmasFor vocab checker .ha (plain clauses) lemmas) select cuts) 2000 state

def offeredNames (checker : Checker Nat Nat Sym) (clauses : List Clause) (lemmas : List L) : List Sym :=
  (lemmasFor vocab checker .ha (plain clauses) lemmas).statements.map Prod.fst

def kind (outcome : Run) : OutcomeKind := outcome.kind

mutual
def nodes : ProofTree Nat Nat Sym Unit → List (ProofTree Nat Nat Sym Unit)
  | .node rule obligation premises subproofs => .node rule obligation premises subproofs :: nodesOf subproofs
  | .deferred _ _ => []

def nodesOf : List (ProofTree Nat Nat Sym Unit) → List (ProofTree Nat Nat Sym Unit)
  | [] => []
  | tree :: trees => nodes tree ++ nodesOf trees
end

/-- The lemma commands of a run's tree, in preorder, with their witnesses read
through the final store. -/
def lemmaNodes (outcome : Run) : List (RuleId × Sym × List T) :=
  match outcome.proof? with
  | some proof =>
      (nodes proof.tree).filterMap fun
        | .node (.derived (.lemmaUse name _ witnesses)) _ _ _ => some (.lemmaUse, name, witnesses.map proof.store.resolve)
        | .node (.derived (.lemmaRule name _ witnesses)) _ _ _ => some (.lemmaRule, name, witnesses.map proof.store.resolve)
        | .node (.derived (.lemmaCut name _ witnesses)) _ _ _ => some (.lemmaCut, name, witnesses.map proof.store.resolve)
        | _ => none
  | none => []

/-- The run's export, checked against the checker with the lemma table as its
import table, for the answer instance. -/
def verdict (checker : Checker Nat Nat Sym) (lemmas : List L) (context : List T) (goal : T) (outcome : Run) :
    Option (Verdict Sym) :=
  outcome.proof?.bind fun proof =>
    (exportProof vocab (fun _ => .truth) proof).map fun term =>
      checkProof vocab checker (table lemmas) (context.map proof.store.resolve) (proof.store.resolve goal) term

/-- The rules of a supplied tree in preorder, by their encoding tags. -/
partial def tags : P → List Tag
  | .node rule _ premises =>
      (match encodeRule vocab rule with | .app (.tag tag) _ => [tag] | _ => []) ++ premises.flatMap tags

def exportedTags (outcome : Run) : List Tag :=
  ((outcome.proof?.bind fun proof => exportTree (Certificate := Unit) (fun _ => .truth) proof.store (fun _ _ => none)
    proof.tree).map tags).getD []

/-! ### A universal lemma, used twice with different witnesses

`univ : ∀1. (q(1) → p(1))` is proved in a proof layer whose KB is the
executable program, the facts `q(a)` and `q(b)`, with `p(X) :- q(X)`. The
program alone does not prove `p(a)`. -/

def pq : Clause := rule (atom .p [.var 0]) [atom .q [.var 0]]
def facts : List Clause := [fact (atom .q [k .a]), fact (atom .q [k .b])]
def proofLayer : Checker Nat Nat Sym := layer (facts ++ [pq])

def universal : T := .forallVar 1 (.imp (atom .q [.var 1]) (atom .p [.var 1]))
def univ : L :=
  lemma .univ [] universal
    (node (.forallIntro 5) universal
      [node .impIntro (.imp (atom .q [.var 5]) (atom .p [.var 5]))
        [step pq [(0, .var 5)] (atom .p [.var 5]) [node .assumption (atom .q [.var 5])]]])

#guard checkImports vocab proofLayer (table [univ])
#guard offeredNames proofLayer facts [univ] = [.univ]

def both : T := .conj (atom .p [k .a]) (atom .p [k .b])
#guard kind (solve proofLayer facts [] (query [] [] both)) = .exhausted
def twice := solve proofLayer facts [univ] (query [] [] both)
#guard kind twice = .success
-- Two lemmaRule nodes, at fresh flexible witnesses matched to a and to b; the
-- premise q(a), then q(b), is a goal of the run.
#guard lemmaNodes twice = [(.lemmaRule, .univ, [k .a]), (.lemmaRule, .univ, [k .b])]
-- Exported as a reference with the eliminations of its instance, accepted.
#guard verdict proofLayer [univ] [] both twice = some .accept
#guard (exportedTags twice).count .reference = 2
#guard (exportedTags twice).count .forallElim = 2
-- Without the lemma table, the reference is a missing capability.
#guard (twice.proof?.bind fun proof => (exportProof vocab (fun _ => .truth) proof).map fun term =>
  checkProof vocab proofLayer [] [] both term) = some (.needsEvidence [.lemma .univ])
-- A goal reading as the whole statement is closed by the lemma itself.
def whole := solve proofLayer facts [univ] (query [] [] universal)
#guard kind whole = .success
#guard verdict proofLayer [univ] [] universal whole = some .accept

/-! ### A lemma proved under assumptions

`ctx : t` under the context `[s]`, by `t :- s`. It is not a global fact: where
`s` is not assumed it does not hold, and the reference is rejected. -/

def ts : Clause := rule (k .t) [k .s]
def ctxLemma : L := lemma .ctx [k .s] (k .t) (step ts [] (k .t) [node .assumption (k .s)])
def ctxLayer : Checker Nat Nat Sym := layer [ts]

#guard checkImports vocab ctxLayer (table [ctxLemma])
-- Offered, but in the empty context it does not hold: a miss, so exhausted.
#guard kind (solve ctxLayer [] [ctxLemma] (query [] [] (k .t))) = .exhausted
-- Under `s`, opened by the implication's introduction, it holds.
def underS := solve ctxLayer [] [ctxLemma] (query [] [] (.imp (k .s) (k .t)))
#guard kind underS = .success
#guard lemmaNodes underS = [(.lemmaUse, .ctx, [])]
#guard verdict ctxLayer [ctxLemma] [] (.imp (k .s) (k .t)) underS = some .accept
#guard kind (solve ctxLayer [] [ctxLemma] (query [] [k .s] (k .t))) = .success
-- The reference itself is rejected by S08 where `s` is absent.
#guard checkProof vocab ctxLayer (table [ctxLemma]) [] (k .t) (encode vocab (node (.reference .ctx) (k .t))) = .reject

/-! ### Context-indexed NAF evidence, checked again at the use site

`negated : w`, by `w :- naf v`, its NAF evidence accepted in the empty context
only. The lemma's own context is empty, so it is checked and offered; at a use
site under `s` its proof is checked again there and its evidence rejected. -/

def wv : Clause := rule (k .w) [naf (k .v)]
def negatedLemma : L :=
  lemma .negated [] (k .w) (step wv [] (k .w) [node (.defaultNegIntro .truth) (naf (k .v))])
def negLayer : Checker Nat Nat Sym := layer [wv]

#guard checkImports vocab negLayer (table [negatedLemma])
def plainW := solve negLayer [] [negatedLemma] (query [] [] (k .w))
#guard kind plainW = .success
#guard verdict negLayer [negatedLemma] [] (k .w) plainW = some .accept
-- Under `s` the evidence does not hold: the lemma is rejected at the use site.
-- Its own context is there, so the rejection is a gap, not a miss: the lemma
-- applies, and its proof failing to check here says nothing about `w`.
def underSW := solve negLayer [] [negatedLemma] (query [] [] (.imp (k .s) (k .w)))
#guard match underSW with
  | .abandoned gaps => gaps.map (fun gap => (gap.reason, gap.obligation.goal)) == [(.unsupported, k .w)]
  | _ => false
#guard checkProof vocab negLayer (table [negatedLemma]) [k .s] (k .w)
  (encode vocab (node (.reference .negated) (k .w))) = .reject

/-! ### An eigenvariable of the lemma's proof, named by the use site

S08 checks a referenced proof as written. `univ`'s proof opens its universal at
the eigenvariable 5; where the use site's context names 5, the proof does not
check there. The lemma's context is there, so the use is a gap. -/

-- Under `r(4)`, the run opens `∀2` at 5: the context is `[q(5), r(4)]`.
def clash := solve proofLayer facts [univ] (query [] [atom .r [.var 4]] (.forallVar 2 (.imp (atom .q [.var 2]) (atom .p [.var 2]))))
#guard match clash with
  | .abandoned gaps => gaps.map (fun gap => (gap.reason, gap.obligation.goal)) == [(.unsupported, atom .p [.var 5])]
  | _ => false
-- Under `r(7)`, it opens at 8: the proof checks, and the run succeeds.
#guard kind (solve proofLayer facts [univ] (query [] [atom .r [.var 7]]
  (.forallVar 2 (.imp (atom .q [.var 2]) (atom .p [.var 2]))))) = .success

/-! ### A conclusion applying a predicate by `ho_apply`

`indirect : ho_apply(p, a)`, by `hoApplyIntro` from the fact `p(a)`. The goal
`p(a)` is compared through its indirect view and the node converted (S11). -/

def hoP : T := .app .ha [k .p, k .a]
def indirectLemma : L := lemma .pa [] hoP (node .hoApplyIntro hoP [step (fact (atom .p [k .a])) [] (atom .p [k .a]) []])
def hoLayer : Checker Nat Nat Sym := layer [fact (atom .p [k .a])]
#guard checkImports vocab hoLayer (table [indirectLemma])
def converted := solve hoLayer [] [indirectLemma] (query [] [] (atom .p [k .a]))
#guard kind converted = .success
#guard (exportedTags converted).count .hoApplyElim = 1
#guard verdict hoLayer [indirectLemma] [] (atom .p [k .a]) converted = some .accept

/-! ### Lemmas that are never offered -/

-- A lemma referencing itself is checked against the older lemmas only, where
-- its name is missing: never checked, never offered.
def selfLemma : L := lemma .self [] (k .r) (node (.reference .self) (k .r))
#guard !checkImports vocab proofLayer (table [selfLemma])
#guard offeredNames proofLayer facts [selfLemma] = []
#guard kind (solve proofLayer facts [selfLemma] (query [] [] (k .r))) = .exhausted
#guard checkProof vocab proofLayer (table [selfLemma]) [] (k .r) (encode vocab (node (.reference .self) (k .r)))
  = .needsEvidence [.lemma .self]
-- The other lemmas of the table are still offered.
#guard offeredNames proofLayer facts [selfLemma, univ] = [.univ]
-- An unchecked claim: its term proves something else.
def claim : L := lemma .pa [] (atom .p [k .a]) (node .truth .truth)
#guard offeredNames proofLayer facts [claim] = []
-- Stale: the KB changed, and `p(X) :- q(X)` is gone. Checked against the run's
-- checker, the lemma no longer checks and is not offered.
#guard offeredNames (layer facts) facts [univ] = []
#guard kind (solve (layer facts) facts [univ] (query [] [] both)) = .exhausted
-- Another snapshot: a checker whose KB does not contain the program offers
-- nothing; nor does one for another application symbol.
#guard offeredNames (layer [pq]) facts [univ] = []
#guard offeredNames ⟨⟨.isPred, facts ++ [pq]⟩, emptyFailure, none, []⟩ facts [univ] = []

/-! ### A use site that may still change is a gap

Under `q(X)`, with `X` an unbound flexible name, the context could still read
otherwise, and the lemma may hold under one reading and not another: a gap,
never a miss. -/

def open' := solve proofLayer facts [univ] (query [0] [] (.imp (atom .q [.var 0]) (atom .p [.var 0])))
#guard kind open' = .abandoned
#guard match open' with
  | .abandoned gaps => gaps.map (fun gap => (gap.reason, gap.obligation.goal)) == [(.unsupported, atom .p [.var 0])]
  | _ => false
-- With `X` bound first, by `q(X)` as a goal, the context is fixed by the time
-- the lemma is used: success.
#guard kind (solve proofLayer facts [univ]
  (query [0] [] (.conj (atom .q [.var 0]) (.imp (atom .q [.var 0]) (atom .p [.var 0]))))) = .success

/-! ### A compound conclusion, used through a cut

`cases : p ∨ s`, by the clause `p ∨ s :- q` with a disjunctive head. The cut
assumes it for the continuation, where `disjCases` splits it (S09). -/

def disjunction : T := .disj (k .p) (k .s)
def headClause : Clause := rule disjunction [k .q]
def casesLemma : L := lemma .cases [] disjunction (step headClause [] disjunction [step (fact (k .q)) [] (k .q) []])
def program : List Clause := [rule (k .u) [k .p], rule (k .u) [k .s]]
def casesLayer : Checker Nat Nat Sym := layer (program ++ [headClause, fact (k .q)])

#guard checkImports vocab casesLayer (table [casesLemma])
-- Backchaining does not use a compound conclusion; without a cut, exhausted.
#guard kind (solve casesLayer program [casesLemma] (query [] [] (k .u)) splits) = .exhausted
def split := solve casesLayer program [casesLemma] (query [] [] (k .u)) splits (cutOnce .cases disjunction)
#guard kind split = .success
#guard (lemmaNodes split).map (·.1) = [.lemmaCut]
#guard verdict casesLayer [casesLemma] [] (k .u) split = some .accept
#guard (exportedTags split).count .disjElim = 1

/-! ### An equation as a conclusion

`law : ∀1. (q(1) → f(1) = c)`, the shape of S14's dictionary laws: an equation
goal is backchained on its conclusion, the premise a goal of the run. -/

def fc : Clause := rule (.equal (atom .f [.var 0]) (k .c)) [atom .q [.var 0]]
def equation : T := .forallVar 1 (.imp (atom .q [.var 1]) (.equal (atom .f [.var 1]) (k .c)))
def lawLemma : L :=
  lemma .law [] equation
    (node (.forallIntro 5) equation
      [node .impIntro (.imp (atom .q [.var 5]) (.equal (atom .f [.var 5]) (k .c)))
        [step fc [(0, .var 5)] (.equal (atom .f [.var 5]) (k .c)) [node .assumption (atom .q [.var 5])]]])
def lawLayer : Checker Nat Nat Sym := layer (facts ++ [fc])
def byLaw := solve lawLayer facts [lawLemma] (query [] [] (.equal (atom .f [k .b]) (k .c)))
#guard kind byLaw = .success
#guard lemmaNodes byLaw = [(.lemmaRule, .law, [k .b])]
#guard verdict lawLayer [lawLemma] [] (.equal (atom .f [k .b]) (k .c)) byLaw = some .accept
-- Without `q(r)` the premise fails. An equation goal has no introduction rule,
-- which the left strategy records as a gap: abandoned, not exhausted.
#guard kind (solve lawLayer facts [lawLemma] (query [] [] (.equal (atom .f [k .r]) (k .c)))) = .abandoned

/-! ### Static diagnostics beside P0

A formula a checked lemma may conclude is a proof-layer capability: P0 still
asks for evidence, or admits the input without the lemma. A lemma enters a P0
program only through `admitImports`. -/

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

def effective (clauses : List Clause) : Program Nat Nat Sym :=
  ⟨clauses.mapIdx (fun index clause => ⟨.lowered index, clause⟩) ++ generated.map (⟨.signature, ·⟩), guardSymbol snapshot⟩

def input (clauses : List Clause) (context : List T) (goal : T) : Input Dom Nat Nat Sym :=
  ⟨snapshot, names, rules, listed, complete, distinct, effective clauses, fun _ => guardSymbol_iff, context, goal⟩

/-- The proof layer over an input's effective program, with `p(X) :- q(X)`. -/
def over (query : Input Dom Nat Nat Sym) : Checker Nat Nat Sym :=
  layer (query.program.clauses.map ProgramClause.clause ++ [pq])

def univD : Lemma Dom Nat Nat Sym := ⟨univ.entry, fun _ => .allData⟩

-- The universal is a scoped goal P0 asks evidence for; `univ` may conclude it.
def scopedGoal := input facts [] universal
#guard (P1.diagnose vocab (over scopedGoal) .ha scopedGoal [univD]).map (fun entry => (entry.1.capability, entry.2))
  = [(.scopedProof, [(.univ, .lemmaUse)])]
-- With no lemma, nothing is diagnosed beyond P0's own requests.
#guard (P1.diagnose vocab (over scopedGoal) .ha scopedGoal []).isEmpty
-- An instance of the universal, as the machine proves it: introduction, then
-- `lemmaRule`.
def instanceGoal := input facts [] (.imp (atom .q [k .a]) (atom .p [k .a]))
#guard (P1.diagnose vocab (over instanceGoal) .ha instanceGoal [univD]).map (·.2) = [[(.univ, .lemmaRule)]]
#guard kind (solve proofLayer facts [univ] (query [] [] (.imp (atom .q [k .a]) (atom .p [k .a])))) = .success
-- Inside a NAF operand a lemma could only refute the goal: nothing diagnosed.
def negatedGoal := input facts [] (naf universal)
#guard (P1.diagnose vocab (over negatedGoal) .ha negatedGoal [univD]).isEmpty
-- A compound universal's instance, through a cut; an existential's body at a
-- particular value, never.
#guard lemmaCommand .ha (.disj (atom .p [k .a]) (atom .s [k .a]))
  (.forallVar 1 (.disj (atom .p [.var 1]) (atom .s [.var 1]))) = some .lemmaCut
#guard lemmaCommand .ha (atom .p [k .a]) (.existsVar 1 (atom .p [.var 1])) = none
#guard lemmaCommand .ha (atom .p [k .a]) (.existsVar 1 (.conj (atom .q [.var 1]) (atom .p [k .a]))) = some .lemmaCut
-- `p(a)` is in P0's classes: P0 admits it whatever the lemmas, and its run is
-- exhausted, while the proof layer proves it with `univ`. No lemma is
-- diagnosed for a Ready input.
def atomic := input facts [] (atom .p [k .a])
#guard match check .ha atomic with | .ready plan => (plan.run 500).kind = .exhausted | _ => false
#guard (P1.diagnose vocab (over atomic) .ha atomic [univD]).isEmpty
-- The universal is no P0 clause: `admitImports` adds nothing for it. A closed
-- lemma in the P0 classes, `p(a)` proved under no assumptions, is added, and
-- P0 then answers.
def paLemma : Lemma Dom Nat Nat Sym :=
  ⟨⟨.pa, [], atom .p [k .a], encode vocab (step pq [(0, k .a)] (atom .p [k .a])
    [step (fact (atom .q [k .a])) [] (atom .q [k .a]) []])⟩, fun _ => .allData⟩
def answer (result : Option (Result Dom Nat Nat Sym .ha)) : Option OutcomeKind :=
  result.bind fun | .ready plan => some (plan.run 500).kind | _ => none
#guard answer (admitImports vocab (over atomic) .ha atomic (table [univ])) = some .exhausted
#guard answer (admitImports vocab (over atomic) .ha atomic [paLemma.entry]) = some .success

/-! ### The theorems, instantiated -/

example : (lemmasFor vocab proofLayer .ha (plain facts) [univ]).Sound .ha proofLayer.snapshot.kb emptyFailure :=
  lemmasFor_sound vocab proofLayer .ha (plain facts) [univ]

example : Strategy.Sound .ha proofLayer.snapshot.kb emptyFailure
    (withLemmas (Certificate := Unit) .ha (plain facts) (lemmasFor vocab proofLayer .ha (plain facts) [univ]) noChoice
      noCut) :=
  withLemmas_sound vocab proofLayer (by decide) [univ] noChoice noCut

example {proof : CompletedProof Nat Nat Sym Unit Nat} {resume : State Nat Nat Sym Unit Nat}
    (ran : run (withLemmas .ha (plain facts) (lemmasFor vocab proofLayer .ha (plain facts) [univ]) noChoice noCut) 2000
      (query [] [] both) = .success proof resume) :
    Derives .ha proofLayer.snapshot.kb [] (proof.store.resolve both) emptyFailure :=
  withLemmas_derives vocab proofLayer (by decide) [univ] noChoice noCut 2000 0 [] [] both ran

end LemmaTests
