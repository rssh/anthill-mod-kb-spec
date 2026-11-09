import AnthillModKbSpec.Resolution.Tabled.Termination
import AnthillModKbSpec.Resolution.Tabled.Calls
import AnthillModKbSpec.Resolution.P1.Answer

/-! # The fast fragment's answers (S24)

`Setup.answer` answers a query of the fast fragment against the Clark
completion of its program:

1. **Admission** (S23): a blocker gives Undecided before anything runs.
2. **The tabled run** (`Engine.run`), with the setup's fuel. Running out of
   fuel is Undecided, naming the call being evaluated: the growing call.
3. **Yes**: a success, exported as an S08 term with every table answer
   expanded from its own proof (`exportWith`), and checked (`checks`). A NAF
   node carries the universe its refutation was computed over; the checker
   computes the refutation again (`nafCheck`).
4. **No**: after a completed run, a goal refuted by the Kripke–Kleene
   iteration over the universe (`refutesIn`), false in every model of the
   completion.
5. **Unknown**: after a completed run, two witnesses (`witnesses`): for a
   positive covered program, the greatest fixpoint, where the goal holds over
   a post-fixpoint of the universe and one fresh value, and the least, where it
   fails over a closed abstract least fixpoint; for a ground program, two
   assignments that are fixpoints, NAF included. Every denial body fails in
   both.
6. Otherwise **Undecided**, with the run's gaps, or the consistency of the KB
   when no assignment of a ground program's open atoms is a fixpoint.

Every answer is sound for the models of the completion with complement NAF that
realize the admission signature (`answer_sound`), and only Undecided changes
with more fuel (`answer_mono`). -/

namespace AnthillModKbSpec.Tabled

open Machine Semantics Completion Answers P1

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  [FreshNames Variable]

attribute [local instance] termEq

/-- A witness of an open goal: the greatest fixpoint, bounded below by these
atoms; the least fixpoint, bounded above by these abstract atoms; or a ground
fixpoint, these atoms true. -/
inductive Witness (Variable Literal Symbol : Type) where
  | greatest (atoms : List (AAtom Variable Literal Symbol))
  | least (atoms : List (AAtom Variable Literal Symbol))
  | assignment (atoms : List (GAtom Variable Literal Symbol))

/-- The answers of the fast fragment: Yes and No carry terms (a checked proof,
the refutation's universe), Unknown two witnesses. -/
abbrev TabledAnswer (Variable Literal Symbol : Type) :=
  Answer (Term Variable Literal Symbol) (Term Variable Literal Symbol) (Witness Variable Literal Symbol)
    (Blocker Variable Literal Symbol)

/-! ## What a query's bounds collect -/

mutual
/-- The symbols applied in a term, at any depth. -/
def appliedSymbols : Term Variable Literal Symbol → List Symbol
  | .app symbol args => symbol :: appliedSymbolsAll args
  | .conj left right | .disj left right | .imp left right | .equal left right =>
      appliedSymbols left ++ appliedSymbols right
  | .defaultNeg body | .forallVar _ body | .existsVar _ body => appliedSymbols body
  | .dictionaryCall dictionary _ _ args => appliedSymbols dictionary ++ appliedSymbolsAll args
  | _ => []

def appliedSymbolsAll : List (Term Variable Literal Symbol) → List Symbol
  | [] => []
  | term :: rest => appliedSymbols term ++ appliedSymbolsAll rest
end

mutual
/-- The most arguments an application in a term has. -/
def widest : Term Variable Literal Symbol → Nat
  | .app _ args => max args.length (widestAll args)
  | .conj left right | .disj left right | .imp left right | .equal left right => max (widest left) (widest right)
  | .defaultNeg body | .forallVar _ body | .existsVar _ body => widest body
  | .dictionaryCall dictionary _ _ args => max (widest dictionary) (widestAll args)
  | _ => 0

def widestAll : List (Term Variable Literal Symbol) → Nat
  | [] => 0
  | term :: rest => max (widest term) (widestAll rest)
end

mutual
/-- The literals of a term, at any depth. -/
def literalsOf : Term Variable Literal Symbol → List Literal
  | .lit value => [value]
  | .app _ args => literalsAll args
  | .conj left right | .disj left right | .imp left right | .equal left right => literalsOf left ++ literalsOf right
  | .defaultNeg body | .forallVar _ body | .existsVar _ body => literalsOf body
  | .dictionaryCall dictionary _ _ args => literalsOf dictionary ++ literalsAll args
  | _ => []

def literalsAll : List (Term Variable Literal Symbol) → List Literal
  | [] => []
  | term :: rest => literalsOf term ++ literalsAll rest
end

/-- The arguments of a goal's atoms and their subterms. -/
def argumentTerms : Term Variable Literal Symbol → List (Term Variable Literal Symbol)
  | .app _ args => subtermsAll args
  | .conj left right | .disj left right | .imp left right => argumentTerms left ++ argumentTerms right
  | .defaultNeg body | .forallVar _ body | .existsVar _ body => argumentTerms body
  | .equal left right => subterms left ++ subterms right
  | _ => []

/-- The antecedents a goal assumes. -/
def antecedents : Term Variable Literal Symbol → List (Term Variable Literal Symbol)
  | .imp premise conclusion => premise :: antecedents conclusion
  | .conj left right | .disj left right => antecedents left ++ antecedents right
  | .defaultNeg body | .forallVar _ body | .existsVar _ body => antecedents body
  | _ => []

/-- A P1 profile. -/
def Profile.isP1 : Profile Variable Literal Symbol → Bool
  | .p1 => true
  | _ => false

/-- A program of the fast fragment with what its answers need: the S08
vocabulary, the unknown marker, the admission signature with its guard symbols
decided and separated, the signature the completion closes, the rule name of
table answers, and the fuel of a run. -/
structure Setup (Domain Variable Literal Symbol : Type) [DecidableEq Variable] [DecidableEq Literal]
    [DecidableEq Symbol] [FreshNames Variable] where
  vocab : Vocabulary Symbol
  fragment : Tabled.Program Variable Literal Symbol
  admission : AdmissionSignature.SignatureSnapshot Domain Symbol
  isGuard : Symbol → Bool
  isGuard_iff : ∀ symbol, isGuard symbol = true ↔ Open.IsGuard admission.naming symbol
  separated : Open.Separated admission.naming fragment.hoApply
  markers : ∀ symbol, fragment.unknownMarker symbol = true → isGuard symbol = false
  signature : Signature Literal Symbol
  closed : ∀ key ∈ signature.predicates, fragment.unknownMarker key.1 = false ∧ key.1 ≠ fragment.hoApply ∧
    isGuard key.1 = false
  tableSymbol : Symbol
  /-- The naming of the generated clauses' variables, and the declared
  constructor rules, listed: the guards' clauses (`generated`). -/
  names : Nat → Variable
  rules : List (InductiveDomains.Rule Domain Symbol)
  listed : ∀ rule ∈ rules, admission.signature.data.definitions rule

namespace Setup

variable {Domain : Type} (setup : Setup Domain Variable Literal Symbol)

def hoApplySymbol : Symbol := setup.fragment.hoApply

def clauses : List (HornClause Variable Literal Symbol) := setup.fragment.clauses.map Prod.snd

def completion : Completed Variable Literal Symbol := Completion.completion setup.clauses setup.signature

/-- The completed snapshot answers are about. -/
def snapshot : P1.Snapshot Variable Literal Symbol := ⟨setup.hoApplySymbol, setup.completion.clauses⟩

/-- The clauses the signature generates for its guards: domain membership,
`D_all` from each domain, and the registered predicates' facts. Every model
realizing the admission signature satisfies them (`models_signatureKb`). -/
def generated : List (HornClause Variable Literal Symbol) :=
  signatureClauses setup.admission setup.names setup.rules

/-- The snapshot exported proofs are checked against: the completion and the
guards' generated clauses, which prove guard atoms. -/
def checkSnapshot : P1.Snapshot Variable Literal Symbol :=
  ⟨setup.hoApplySymbol, setup.completion.clauses ++ setup.generated⟩

/-- The universe of a query: the ground data subterms of the program and the query. -/
def space (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    List (Term Variable Literal Symbol) :=
  universeOf setup.signature.constructors setup.clauses (goal :: context)

/-- The Kripke–Kleene iteration over a universe: definitely and possibly true
atoms, stopped once a round changes nothing (`untilStable`), at most `rounds`
rounds. Every round is sound, so the round it stops at is (`kleene_round`). -/
def kleene (space : List (Term Variable Literal Symbol)) :
    List (GAtom Variable Literal Symbol) × List (AAtom Variable Literal Symbol) :=
  untilStable (fun next current => decide (next.1 = current.1) && decide (next.2 = current.2))
    (kkStep setup.signature space setup.clauses) (rounds setup.signature space) (kk setup.signature space setup.clauses 0)

theorem kleene_round (space : List (Term Variable Literal Symbol)) :
    ∃ round, setup.kleene space = kk setup.signature space setup.clauses round :=
  untilStable_round _ _ _ (kk_succ _ _ _) _ 0

/-- A ground operand refuted over a universe, the iteration's result given. -/
def refutesInWith (space : List (Term Variable Literal Symbol))
    (fixed : List (GAtom Variable Literal Symbol) × List (AAtom Variable Literal Symbol))
    (operand : Term Variable Literal Symbol) : Bool :=
  validUniverse setup.signature.constructors space && refutesWith setup.signature space fixed operand

/-- A ground operand refuted over a universe. -/
def refutesIn (space : List (Term Variable Literal Symbol)) (operand : Term Variable Literal Symbol) : Bool :=
  setup.refutesInWith space (setup.kleene space) operand

/-- The engine of a query, its refutations over the query's universe. -/
def engine (space : List (Term Variable Literal Symbol)) : Engine Variable Literal Symbol where
  hoApplySymbol := setup.hoApplySymbol
  fragment := setup.fragment
  resolution := Machine.Program.ofClauses (setup.clauses ++ setup.generated) setup.fragment.guard
  unknownMarker := setup.fragment.unknownMarker
  tableSymbol := setup.tableSymbol
  refutes :=
    let fixed : Thunk _ := Thunk.mk fun _ => setup.kleene space
    fun operand => setup.refutesInWith space fixed.get operand
  evidence := fun _ => .app setup.tableSymbol space

variable {setup}

/-- A refutation is false in every model of the completed program. -/
theorem refutesIn_sound {space : List (Term Variable Literal Symbol)} {operand : Term Variable Literal Symbol}
    (refuted : setup.refutesIn space operand = true) {Value : Type} {model : Model Literal Symbol Value setup.hoApplySymbol}
    (models : model.Models setup.snapshot.kb) (negation : model.ComplementNAF) (environment : Environment Variable Value) :
    ¬ model.Satisfies environment operand := by
  simp only [refutesIn, refutesInWith, Bool.and_eq_true] at refuted
  obtain ⟨round, roundEq⟩ := setup.kleene_round space
  rw [roundEq] at refuted
  exact refutes_sound (count := round) (Completes.of_models (signature := setup.signature) (clauses := setup.clauses) models)
    refuted.1 negation refuted.2 environment

/-- NAF evidence by refutation: the operand fails in every model. -/
theorem refutesIn_naf {space : List (Term Variable Literal Symbol)} {operand : Term Variable Literal Symbol}
    (refuted : setup.refutesIn space operand = true) (context : ProofContext Variable Literal Symbol) :
    semanticNaf setup.hoApplySymbol setup.checkSnapshot.kb context operand := by
  intro Value model models negation environment _
  rw [sat_neg model environment negation]
  exact refutesIn_sound refuted (fun clause member => models clause (List.mem_append_left _ member)) negation environment

variable (setup)

/-- The check of NAF evidence: a universe over which the operand is refuted. -/
def nafCheck (space : List (Term Variable Literal Symbol)) : NafCheck setup.checkSnapshot semanticNaf where
  check :=
    let cached : Thunk _ := Thunk.mk fun _ => setup.kleene space
    fun _ operand evidence =>
      match evidence with
      | .app symbol evidenceSpace =>
          decide (symbol = setup.tableSymbol) &&
            (if evidenceSpace = space then setup.refutesInWith space cached.get operand else setup.refutesIn evidenceSpace operand)
      | _ => false
  sound := by
    intro context operand evidence accepted
    dsimp only at accepted
    split at accepted
    · simp only [Bool.and_eq_true] at accepted
      split at accepted
      · rename_i same
        subst same
        exact refutesIn_naf accepted.2 context
      · exact refutesIn_naf accepted.2 context
    · cases accepted

/-- The checker of the fast fragment's proofs: NAF evidence by refutation, the
iteration over the query's universe run once for all its NAF nodes. -/
def checker (space : List (Term Variable Literal Symbol)) : Checker Variable Literal Symbol :=
  ⟨setup.checkSnapshot, semanticNaf, some (setup.nafCheck space), []⟩

/-- A proof term of the goal under the context, checked. -/
def checks (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol)
    (proof : Term Variable Literal Symbol) : Bool :=
  decide (checkProof setup.vocab (setup.checker (setup.space context goal)) [] context goal proof = .accept)

/-- The answer of a table with an atom in a context. -/
def findAnswer (tables : List (Table Variable Literal Symbol)) (atom : Term Variable Literal Symbol)
    (context : ProofContext Variable Literal Symbol) : Option (TableAnswer Variable Literal Symbol) :=
  tables.findSome? fun table =>
    if decide (table.call.context = context) then table.answers.find? fun answer => decide (answer.atom = atom) else none

/-- Export a completed proof, each table answer expanded from its own proof. -/
def exportWith (tables : List (Table Variable Literal Symbol)) :
    Nat → CompletedProof Variable Literal Symbol (Term Variable Literal Symbol) Unit → Option (Proof Variable Literal Symbol)
  | 0, proof => exportTree id proof.store (fun _ _ => none) proof.tree
  | depth + 1, proof =>
      exportTree id proof.store (fun rule _ =>
        match rule with
        | .extension symbol (atom :: context) none =>
            if symbol = setup.tableSymbol then
              (findAnswer tables atom context).bind fun answer => exportWith tables depth answer.proof
            else none
        | _ => none) proof.tree

/-- A run's success, exported and checked. -/
def proved (proof : CompletedProof Variable Literal Symbol (Term Variable Literal Symbol) Unit) (resume : Run Variable Literal Symbol)
    (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) : Option (Term Variable Literal Symbol) :=
  ((setup.exportWith resume.tables ((resume.tables.map fun table => table.answers.length).sum + 1) proof).map
    (encode setup.vocab)).filter (setup.checks context goal)

/-! ## Witnesses -/

/-- The denials' bodies. -/
def denials : List (List (Term Variable Literal Symbol)) :=
  setup.clauses.filterMap fun
    | .goal body => some body
    | _ => none

/-- The bodies of the clauses that conclude falsity, `⊥ :- body` and
`false :- body`: what the runtime consistency check runs. -/
def constraints : List (List (Term Variable Literal Symbol)) :=
  setup.clauses.filterMap fun
    | .goal body => some body
    | .definite .falsity body => some body
    | _ => none

/-- A denial body with its free names closed existentially: it is violated
when some instance holds. -/
def violation (body : List (Term Variable Literal Symbol)) : Formula Variable Literal Symbol :=
  (Term.conjunction body).freeVars.eraseDups.foldr Term.existsVar (.conjunction body)

/-- The covered programs, decided. -/
def covered : Bool :=
  setup.clauses.all (fun
    | .definite (.app symbol args) _ => decide ((symbol, args.length) ∈ setup.signature.predicates)
    | .goal _ => true
    | _ => false) &&
  setup.signature.predicates.all fun key => decide (key.1 ≠ setup.hoApplySymbol)

/-- The positive programs, decided. -/
def positive : Bool :=
  setup.clauses.all fun
    | .definite (.app _ args) body => dataArgs args && body.all (positiveGoal setup.hoApplySymbol)
    | _ => true

/-- The two witnesses of a positive covered program: a post-fixpoint in which
the goal holds and a closed abstract least fixpoint in which it fails, every
denial body failing in both. -/
def positiveWitnesses (space : List (Term Variable Literal Symbol)) (goal : Formula Variable Literal Symbol) :
    Option (Witness Variable Literal Symbol × Witness Variable Literal Symbol) :=
  let count := rounds setup.signature space
  let fixed := setup.kleene space
  let low := untilStable (fun next current => decide (next = current)) (leastStep setup.signature space setup.clauses) count
    (leastOver setup.signature space setup.clauses 0)
  let high := untilStable (fun next current => decide (next = current))
    (greatestStep setup.signature space setup.clauses setup.fragment.unknownMarker) count
    (greatestOver setup.signature space setup.clauses setup.fragment.unknownMarker 0)
  if !setup.fragment.unknownMarker setup.hoApplySymbol && setup.covered && setup.positive &&
      positiveGoal setup.hoApplySymbol goal &&
      closedLeast setup.signature space setup.clauses low && failsLeast setup.signature space low goal &&
      setup.denials.all (fun body => failsLeast setup.signature space low (.conjunction body)) &&
      postGreatest setup.signature space setup.clauses setup.fragment.unknownMarker high &&
      vtrue setup.signature space setup.fragment.unknownMarker high (fun _ => none) goal &&
      setup.denials.all (fun body => refutesWith setup.signature space fixed (.conjunction body)) then
    some (.greatest high, .least low)
  else none

/-- Every sublist of a list. -/
def subsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | item :: rest => (subsets rest).flatMap fun subset => [item :: subset, subset]

/-- The ground atoms of a program and a goal: closed atoms and unknown markers. -/
def groundAtoms (goal : Formula Variable Literal Symbol) : List (GAtom Variable Literal Symbol) :=
  let rec atomsOf : Term Variable Literal Symbol → List (GAtom Variable Literal Symbol)
    | .app symbol args => [(symbol, args)]
    | .conj left right | .disj left right | .imp left right => atomsOf left ++ atomsOf right
    | .defaultNeg body => atomsOf body
    | _ => []
  ((goal :: setup.clauses.flatMap HornClause.terms).flatMap atomsOf).eraseDups

/-- The ground atoms an iteration's result leaves undecided: neither
definitely true nor refuted, or unknown markers. -/
def undecidedWith (kleene : List (GAtom Variable Literal Symbol) × List (AAtom Variable Literal Symbol))
    (goal : Formula Variable Literal Symbol) : List (GAtom Variable Literal Symbol) :=
  (setup.groundAtoms goal).filter fun atom =>
    !decide (atom ∈ kleene.1) &&
      (setup.fragment.unknownMarker atom.1 || decide ((atom.1, atom.2.map some) ∈ kleene.2))

/-- The ground atoms the Kripke–Kleene iteration leaves undecided. -/
def undecidedAtoms (space : List (Term Variable Literal Symbol)) (goal : Formula Variable Literal Symbol) :
    List (GAtom Variable Literal Symbol) :=
  setup.undecidedWith (setup.kleene space) goal

/-- Assignments of a ground program's open atoms, the iteration's result
given: the definitely true ones with the others, every way when there are few,
otherwise all, none, or one. -/
def assignmentsWith (kleene : List (GAtom Variable Literal Symbol) × List (AAtom Variable Literal Symbol))
    (goal : Formula Variable Literal Symbol) : List (List (GAtom Variable Literal Symbol)) :=
  let atoms := setup.groundAtoms goal
  let definitely := atoms.filter fun atom => decide (atom ∈ kleene.1)
  let undecided := setup.undecidedWith kleene goal
  let choices := if undecided.length ≤ 8 then subsets undecided
    else [undecided, []] ++ undecided.map (fun atom => [atom]) ++ undecided.map (fun atom => undecided.erase atom)
  choices.map (definitely ++ ·)

/-- Assignments of a ground program's open atoms over a universe. -/
def assignments (space : List (Term Variable Literal Symbol)) (goal : Formula Variable Literal Symbol) :
    List (List (GAtom Variable Literal Symbol)) :=
  setup.assignmentsWith (setup.kleene space) goal

/-- An assignment of a ground program that is a fixpoint with every denial
body false. -/
def groundModel (assignment : List (GAtom Variable Literal Symbol)) : Bool :=
  groundFixpoint setup.signature setup.clauses assignment &&
    assignment.all (fun atom => groundInAll setup.signature.constructors atom.2) &&
    setup.denials.all fun body => !gtrue setup.signature assignment (.conjunction body)

/-- Two ground fixpoints, one making the goal true and one false. -/
def groundWitnesses (space : List (Term Variable Literal Symbol)) (goal : Formula Variable Literal Symbol) :
    Option (Witness Variable Literal Symbol × Witness Variable Literal Symbol) :=
  if groundProgram setup.hoApplySymbol setup.signature setup.fragment.unknownMarker setup.clauses &&
      knownGoal setup.hoApplySymbol setup.signature setup.fragment.unknownMarker goal then
    let models := (setup.assignments space goal).filter setup.groundModel
    match models.find? (gtrue setup.signature · goal), models.find? (!gtrue setup.signature · goal) with
    | some holds, some fails => some (.assignment holds, .assignment fails)
    | _, _ => none
  else none

/-- The two witnesses of a closed goal with no assumptions. -/
def witnesses (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    Option (Witness Variable Literal Symbol × Witness Variable Literal Symbol) :=
  let space := setup.space context goal
  if context.isEmpty && closedTerm goal && validUniverse setup.signature.constructors space then
    (setup.positiveWitnesses space goal).or (setup.groundWitnesses space goal)
  else none

/-- A ground program none of whose assignments of the undecided atoms is a
model, every assignment tried (at most eight undecided atoms): its completion
may be inconsistent (`p :- ¬p`). -/
def inconsistentWith (kleene : List (GAtom Variable Literal Symbol) × List (AAtom Variable Literal Symbol))
    (goal : Formula Variable Literal Symbol) : Bool :=
  groundProgram setup.hoApplySymbol setup.signature setup.fragment.unknownMarker setup.clauses &&
    decide ((setup.undecidedWith kleene goal).length ≤ 8) && !(setup.assignmentsWith kleene goal).any setup.groundModel

/-- A checked model of the KB in which every denial body fails: an
assignment of a ground program that is a fixpoint of its clauses
(`groundModel`), or the closed abstract least fixpoint of a positive covered
one (the `least` witness's check). Only for denials written `⊥ :- body`, which
these checks read. -/
def modelShown : Bool :=
  let space := setup.space [] .truth
  let low := untilStable (fun next current => decide (next = current)) (leastStep setup.signature space setup.clauses)
    (rounds setup.signature space) (leastOver setup.signature space setup.clauses 0)
  decide (setup.constraints.length = setup.denials.length) && validUniverse setup.signature.constructors space &&
    ((groundProgram setup.hoApplySymbol setup.signature setup.fragment.unknownMarker setup.clauses &&
        (setup.assignmentsWith (setup.kleene space) .truth).any setup.groundModel) ||
      (!setup.fragment.unknownMarker setup.hoApplySymbol && setup.covered && setup.positive &&
        closedLeast setup.signature space setup.clauses low &&
        setup.denials.all fun body => failsLeast setup.signature space low (.conjunction body)))

/-! ## The answer -/

/-- The blocker of an interrupted run: the call of the generator it was
stepping, the newest with something left. -/
def growing (run : Run Variable Literal Symbol) (context : ProofContext Variable Literal Symbol)
    (goal : Formula Variable Literal Symbol) : Blocker Variable Literal Symbol :=
  match run.stack.find? (fun generator => !State.done generator.state) with
  | some generator => ⟨.reached generator.state.root.context [], [], generator.state.root.goal, .termination⟩
  | none => Blocker.interrupted context goal

/-- The blockers of a completed run that answered nothing. -/
def blockersOf (outcome : Machine.Outcome Variable Literal Symbol (Term Variable Literal Symbol) Unit)
    (goal : Formula Variable Literal Symbol) : List (Blocker Variable Literal Symbol) :=
  match outcome with
  | .opened gaps | .abandoned gaps => gaps.map (Blocker.ofGap fun formula => [formula])
  | _ => [Blocker.unproved goal]

/-- The answer after the tabled run, from its outcome. -/
def answerFrom (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    Engine.Outcome Variable Literal Symbol → TabledAnswer Variable Literal Symbol
  | .interrupted run => .undecided [growing run context goal]
  | .success proof resume =>
      match setup.proved proof resume context goal with
      | some term => .yes term
      | none => .undecided [Blocker.unproved goal]
  | .finished outcome =>
      if setup.refutesInWith (setup.space context goal) (setup.kleene (setup.space context goal)) goal then
        .no (.app setup.tableSymbol (setup.space context goal))
      else
        match setup.witnesses context goal with
        | some (holds, fails) => .unknown holds fails
        | none =>
            if context.isEmpty && setup.inconsistentWith (setup.kleene (setup.space context goal)) goal then
              .undecided [⟨.site .goal, [], goal,
                .consistency ((setup.undecidedWith (setup.kleene (setup.space context goal)) goal).map
                  fun atom => .app atom.1 atom.2)⟩]
            else .undecided (blockersOf outcome goal)

/-- The tabled run of a query's goal, with fuel. -/
def runOf (fuel : Nat) (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    Engine.Outcome Variable Literal Symbol :=
  (setup.engine (setup.space context goal)).run fuel (Engine.start context goal)

/-- What a denial's run says about the KB, its body closed existentially
(`violation`): a proved body makes it inconsistent, whether or not its export
checks; a run out of fuel, or one that abandoned a path, leaves its
consistency open, and so does one that met open atoms, unless a checked model
of the KB shows it consistent (`modelShown`; decided with the user,
2026-11-09): denials checked one at a time miss a joint inconsistency through
open atoms. -/
def denialBlocker (fuel : Nat) (body : List (Term Variable Literal Symbol)) : Option (Blocker Variable Literal Symbol) :=
  match setup.runOf fuel [] (violation body) with
  | .success _ _ => some ⟨.site .goal, [], .conjunction body, .consistency body⟩
  | .interrupted run => some (growing run [] (violation body))
  | .finished (.abandoned _) => some ⟨.site .goal, [], .conjunction body, .consistency body⟩
  | .finished (.opened _) => if setup.modelShown then none else some ⟨.site .goal, [], .conjunction body, .consistency body⟩
  | .finished _ => none

/-- The runtime consistency check (S23's boundary): every answer assumes a
model, so a denial whose body is proved, or not settled within the fuel,
blocks every answer. -/
def denialCheck (fuel : Nat) : Option (Blocker Variable Literal Symbol) :=
  setup.constraints.findSome? (setup.denialBlocker fuel)

/-! ## Bounded runs: P1 without fuel -/

/-- The bounds of a query's run. Its calls are of the symbols the program and
the query apply; its data terms are built from those symbols, the literals,
and the query's free names (its rigid parameters), with at most the most
arguments an application has, and at most `(s + 1) ^ (p + 1)` nodes, for `s`
the largest argument of the program and the query and `p` the symbols: each
call made from a lower component's entry can grow its inputs by a body's
terms. That this limit covers every call of a P1 run is S15's. Its contexts
are drawn from the query's and every antecedent the program or the query
assumes. -/
def bounds (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    Bounds Variable Literal Symbol :=
  let terms := (setup.clauses ++ setup.generated).flatMap HornClause.terms ++ goal :: context
  let symbols := (appliedSymbolsAll terms).eraseDups
  let largest := ((terms.flatMap argumentTerms).map Tabled.size).foldr max 0
  { predicates := symbols
    constructors := symbols
    literals := (literalsAll terms).eraseDups
    names := ((goal :: context).flatMap Term.freeVars).eraseDups
    size := (largest + 1) ^ (symbols.length + 1)
    arity := (terms.map widest).foldr max 0
    assumptions := (context ++ terms.flatMap antecedents).eraseDups }

/-- The bounded engine of a query. -/
def boundedEngine (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    Engine Variable Literal Symbol :=
  { setup.engine (setup.space context goal) with bounds := some (setup.bounds context goal) }

/-- The tabled run of a query's goal, bounded and without fuel: it always ends
(`Engine.runToEnd`). -/
def decided (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    Engine.Outcome Variable Literal Symbol :=
  (setup.boundedEngine context goal).runToEnd (bounds := setup.bounds context goal) rfl (Engine.start context goal)

/-- What a denial's bounded run says about the KB, its body closed
existentially: a proved body makes it inconsistent; a run that abandoned a
path, its bounds among the reasons, leaves its consistency open, and so does
one that met open atoms unless a checked model shows the KB consistent. -/
def denialBounded (body : List (Term Variable Literal Symbol)) : Option (Blocker Variable Literal Symbol) :=
  match setup.decided [] (violation body) with
  | .success _ _ | .finished (.abandoned _) => some ⟨.site .goal, [], .conjunction body, .consistency body⟩
  | .finished (.opened _) => if setup.modelShown then none else some ⟨.site .goal, [], .conjunction body, .consistency body⟩
  | _ => none

/-- A denial body admitted as a query of its own: its body closed
existentially, no assumption. -/
def denialQuery (body : List (Term Variable Literal Symbol)) : Tabled.Query Variable Literal Symbol :=
  ⟨[], violation body, []⟩

/-- A denial's check beside a P1 query (decided with the user, 2026-11-09):
bounded and without fuel when its body is P1 itself, with the fuel otherwise.
A bounded run is only ever given a P1 goal. -/
def denialFor (fuel : Nat) (body : List (Term Variable Literal Symbol)) : Option (Blocker Variable Literal Symbol) :=
  if (setup.fragment.admit (denialQuery body)).isP1 then setup.denialBounded body else setup.denialBlocker fuel body

/-- The goal a query answers: its answer names existentially closed. -/
def goalOf (query : Tabled.Query Variable Literal Symbol) : Formula Variable Literal Symbol :=
  query.answers.foldr Term.existsVar query.goal

/-- The tabled run of a query: bounded and without fuel for a P1 query, with
the fuel otherwise. -/
def runFor (fuel : Nat) (query : Tabled.Query Variable Literal Symbol) : Engine.Outcome Variable Literal Symbol :=
  if (setup.fragment.admit query).isP1 then setup.decided query.context (goalOf query)
  else setup.runOf fuel query.context (goalOf query)

/-- The consistency check of a query's KB: bounded for a P1 query, with the
fuel otherwise. -/
def denialsFor (fuel : Nat) (query : Tabled.Query Variable Literal Symbol) : Option (Blocker Variable Literal Symbol) :=
  if (setup.fragment.admit query).isP1 then setup.constraints.findSome? (setup.denialFor fuel) else setup.denialCheck fuel

/-- The module's answer to a query of the fast fragment: its admission's
blockers, the KB's consistency, or the answer of its run, for its goal with
the answer names existentially closed. A P1 query runs bounded, without
fuel; a P2 query with the fuel. -/
def answer (fuel : Nat) (query : Tabled.Query Variable Literal Symbol) : TabledAnswer Variable Literal Symbol :=
  match setup.fragment.answer? query with
  | some blocked => blocked
  | none =>
      match setup.denialsFor fuel query with
      | some blocker => .undecided [blocker]
      | none => setup.answerFrom query.context (goalOf query) (setup.runFor fuel query)

end Setup

/-- The setup of a fragment program, closing the predicates its clauses and
the given formulas use, guards and unknown markers aside, and separating its
declared constructors. -/
def Setup.ofProgram {Domain : Type} (vocab : Vocabulary Symbol) (fragment : Tabled.Program Variable Literal Symbol)
    (admission : AdmissionSignature.SignatureSnapshot Domain Symbol) (isGuard : Symbol → Bool)
    (isGuard_iff : ∀ symbol, isGuard symbol = true ↔ Open.IsGuard admission.naming symbol)
    (separated : Open.Separated admission.naming fragment.hoApply)
    (markers : ∀ symbol, fragment.unknownMarker symbol = true → isGuard symbol = false)
    (free : Symbol → Bool) (formulas : List (Term Variable Literal Symbol)) (tableSymbol : Symbol)
    (names : Nat → Variable) (rules : List (InductiveDomains.Rule Domain Symbol))
    (listed : ∀ rule ∈ rules, admission.signature.data.definitions rule) :
    Setup Domain Variable Literal Symbol :=
  let opened := Signature.of fragment.unknownMarker fragment.hoApply free (fragment.clauses.map Prod.snd) formulas
  { vocab, fragment, admission, isGuard, isGuard_iff, separated, markers
    signature := ⟨opened.predicates.filter (fun key => !isGuard key.1), opened.constructors⟩
    closed := fun key member => by
      have inside := (List.mem_filter.mp member)
      obtain ⟨notMarker, ordinary⟩ := Signature.of_open inside.1
      exact ⟨notMarker, ordinary, by simpa using inside.2⟩
    tableSymbol, names, rules, listed }

namespace Setup

variable {Domain : Type} (setup : Setup Domain Variable Literal Symbol)

/-- What the answers are about: the models of the completed program with
complement NAF that realize the admission signature, under the query's
context, for its goal with the answer names closed. -/
def meaning (query : Tabled.Query Variable Literal Symbol) : Meaning :=
  Meaning.ofModels (Variable := Variable) (hoApplySymbol := setup.hoApplySymbol)
    (fun _ model => model.Models setup.snapshot.kb ∧ model.ComplementNAF ∧ AdmissionSignature.Realizes setup.admission model)
    query.context (goalOf query)

variable {setup}

/-- A model of the completion realizing the admission signature satisfies the
guards' generated clauses too. -/
theorem models_checkSnapshot {Value : Type} {model : Model Literal Symbol Value setup.hoApplySymbol}
    (models : model.Models setup.snapshot.kb) (realizes : AdmissionSignature.Realizes setup.admission model) :
    model.Models setup.checkSnapshot.kb := by
  intro clause member environment
  rcases List.mem_append.mp member with inCompletion | inGenerated
  · exact models clause inCompletion environment
  · exact Elaboration.models_signatureKb setup.admission model realizes setup.names clause
      (mem_signatureClauses setup.listed inGenerated) environment

theorem checks_sound {context : ProofContext Variable Literal Symbol} {goal : Formula Variable Literal Symbol}
    {proof : Term Variable Literal Symbol} (checked : setup.checks context goal proof = true) {Value : Type}
    {model : Model Literal Symbol Value setup.hoApplySymbol} (models : model.Models setup.checkSnapshot.kb)
    (negation : model.ComplementNAF) : ∀ environment, model.ContextHolds environment context → model.Satisfies environment goal :=
  model.sound models (semanticNaf_adequate model models negation)
    (checked_toDerives setup.vocab (setup.checker (setup.space context goal))
      ((checkProof_accept_iff setup.vocab (setup.checker (setup.space context goal))).mp (of_decide_eq_true checked)))

theorem proved_sound {proof : CompletedProof Variable Literal Symbol (Term Variable Literal Symbol) Unit}
    {resume : Run Variable Literal Symbol} {context : ProofContext Variable Literal Symbol} {goal : Formula Variable Literal Symbol}
    {term : Term Variable Literal Symbol} (found : setup.proved proof resume context goal = some term) {Value : Type}
    {model : Model Literal Symbol Value setup.hoApplySymbol} (models : model.Models setup.checkSnapshot.kb)
    (negation : model.ComplementNAF) : ∀ environment, model.ContextHolds environment context → model.Satisfies environment goal :=
  checks_sound (Option.filter_eq_some_iff.mp found).2 models negation

/-- A key model interpreting the guards exactly realizes the admission signature. -/
theorem realizes {base interp : Interp Literal Symbol}
    (guards : ∀ symbol keys, setup.isGuard symbol = true → (base symbol keys ↔ Open.guardTruth setup.admission setup.hoApplySymbol symbol keys)) :
    AdmissionSignature.Realizes setup.admission (keyModel setup.hoApplySymbol setup.signature base interp) := by
  apply Open.realizes_guards setup.separated
  intro symbol guard keys
  have isGuard := (setup.isGuard_iff symbol).mpr guard
  have notClosed : (symbol, keys.length) ∉ setup.signature.predicates := fun closed => by
    have := (setup.closed _ closed).2.2; simp only at this; rw [isGuard] at this; cases this
  rw [join_open notClosed]
  exact guards symbol keys isGuard

/-- The base of the least witness: guards exact, everything else false. -/
def lowBase : Interp Literal Symbol := fun symbol keys =>
  setup.isGuard symbol = true ∧ Open.guardTruth setup.admission setup.hoApplySymbol symbol keys

/-- The base of the greatest witness: guards exact, unknown markers true. -/
def highBase : Interp Literal Symbol := fun symbol keys =>
  (setup.isGuard symbol = true ∧ Open.guardTruth setup.admission setup.hoApplySymbol symbol keys) ∨
    (setup.isGuard symbol = false ∧ setup.fragment.unknownMarker symbol = true)

theorem covered_spec (found : setup.covered = true) : Covered setup.hoApplySymbol setup.signature setup.clauses := by
  simp only [covered, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at found
  refine ⟨fun clause member => ?_, found.2⟩
  have shape := found.1 clause member
  match clause, shape with
  | .definite (.app symbol args) body, shape => exact .inl ⟨symbol, args, body, rfl, by simpa using shape⟩
  | .goal body, _ => exact .inr ⟨body, rfl⟩

theorem positive_spec (found : setup.positive = true) : PositiveProgram setup.hoApplySymbol setup.clauses := by
  intro symbol args body member
  simp only [positive, List.all_eq_true] at found
  have shape := found _ member
  simp only [Bool.and_eq_true, List.all_eq_true] at shape
  exact shape

theorem mem_denials {body : List (Term Variable Literal Symbol)} (member : HornClause.goal body ∈ setup.clauses) :
    body ∈ setup.denials :=
  List.mem_filterMap.mpr ⟨_, member, rfl⟩

/-- Two witnesses are two models of the completion, one where the goal holds
and one where it fails. -/
theorem witnesses_sound {query : Tabled.Query Variable Literal Symbol}
    {holds fails : Witness Variable Literal Symbol} (found : setup.witnesses query.context (goalOf query) = some (holds, fails)) :
    (setup.meaning query).independence := by
  unfold witnesses at found
  dsimp only at found
  split at found
  · rename_i conditions
    simp only [Bool.and_eq_true, List.isEmpty_iff] at conditions
    obtain ⟨⟨empty, closedGoal⟩, valid⟩ := conditions
    have contextHolds : ∀ {Value : Type} {model : Model Literal Symbol Value setup.hoApplySymbol} environment,
        model.ContextHolds environment query.context := fun _ => by rw [empty]; intro _ inside; cases inside
    rcases positiveFound : setup.positiveWitnesses (setup.space query.context (goalOf query)) (goalOf query) with _ | pair
    · -- Ground witnesses.
      rw [positiveFound, Option.none_or] at found
      unfold groundWitnesses at found
      split at found
      · rename_i groundConditions
        simp only [Bool.and_eq_true] at groundConditions
        dsimp only at found
        split at found
        · rename_i holding failing holdsFound failsFound
          cases found
          have holdsMember := List.mem_of_find?_eq_some holdsFound
          have failsMember := List.mem_of_find?_eq_some failsFound
          have holdsValue := List.find?_some holdsFound
          have failsValue := List.find?_some failsFound
          have modelOf : ∀ assignment, assignment ∈ (setup.assignments (setup.space query.context (goalOf query)) (goalOf query)).filter
              setup.groundModel → ∃ model : Model Literal Symbol (Key Literal Symbol) setup.hoApplySymbol,
                (model.Models setup.snapshot.kb ∧ model.ComplementNAF ∧ AdmissionSignature.Realizes setup.admission model) ∧
                ∀ environment, (model.Satisfies environment (goalOf query) ↔ gtrue setup.signature assignment (goalOf query) = true) := by
            intro assignment member
            have checked := (List.mem_filter.mp member).2
            simp only [groundModel, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at checked
            obtain ⟨⟨fixed, groundAtoms⟩, denied⟩ := checked
            obtain ⟨models, valued⟩ := ground_witness groundConditions.1 fixed groundAtoms
              (fun body member => denied body (mem_denials member))
              (Open.guardTruth setup.admission setup.hoApplySymbol) groundConditions.2
            refine ⟨_, ⟨models, Model.keys_complement _, realizes fun symbol keys isGuard => ?_⟩, valued⟩
            have notMarker : setup.fragment.unknownMarker symbol = false := by
              cases marker : setup.fragment.unknownMarker symbol
              · rfl
              · have := setup.markers symbol marker; rw [isGuard] at this; cases this
            simp [groundBase, notMarker]
          obtain ⟨holdsModel, holdsHolds, holdsValued⟩ := modelOf holding holdsMember
          obtain ⟨failsModel, failsHolds, failsValued⟩ := modelOf failing failsMember
          let environment : Environment Variable (Key Literal Symbol) := fun _ => .truth False
          refine ⟨⟨_, holdsModel, holdsHolds, environment, contextHolds environment, (holdsValued environment).mpr holdsValue⟩,
            ⟨_, failsModel, failsHolds, environment, contextHolds environment, fun satisfied => ?_⟩⟩
          have := (failsValued environment).mp satisfied
          simp [this] at failsValue
        · cases found
      · cases found
    · -- The least and the greatest fixpoint.
      rw [positiveFound] at found
      simp only [Option.some_or, Option.some.injEq] at found
      subst found
      unfold positiveWitnesses at positiveFound
      dsimp only at positiveFound
      split at positiveFound
      · rename_i conditions
        cases positiveFound
        simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at conditions
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨notMarker, coveredB⟩, positiveB⟩, goalPositive⟩, closedL⟩, failsL⟩, denialsL⟩, post⟩, holdsG⟩, denialsG⟩ :=
          conditions
        have covered := covered_spec coveredB
        have positive := positive_spec positiveB
        have markedTrue : ∀ symbol keys, setup.fragment.unknownMarker symbol = true → setup.highBase symbol keys := by
          intro symbol keys marker
          exact .inr ⟨setup.markers symbol marker, marker⟩
        obtain ⟨highRound, highEq⟩ := untilStable_round _ _ _
          (greatestOver_succ setup.signature (setup.space query.context (goalOf query)) setup.clauses setup.fragment.unknownMarker)
          (rounds setup.signature (setup.space query.context (goalOf query))) 0
        obtain ⟨fixedRound, fixedEq⟩ := setup.kleene_round (setup.space query.context (goalOf query))
        obtain ⟨highModels, highHolds⟩ := greatest_witness (base := setup.highBase) covered positive valid notMarker markedTrue
          post (by rw [highEq]; exact greatestOver_atoms _) (count := fixedRound)
          (fun body member => by
            show refutesWith _ _ _ _ = true
            rw [← fixedEq]; exact denialsG body (mem_denials member)) goalPositive holdsG
        obtain ⟨lowModels, lowFails⟩ := least_witness (base := setup.lowBase) covered positive valid closedL
          (fun body member => denialsL body (mem_denials member)) failsL
        refine ⟨⟨_, _, ⟨highModels, Model.keys_complement _, realizes fun symbol keys isGuard => ?_⟩, _, contextHolds _, highHolds⟩,
          ⟨_, _, ⟨lowModels, Model.keys_complement _, realizes fun symbol keys isGuard => ?_⟩, fun _ => .truth False,
            contextHolds _, lowFails _⟩⟩
        · simp [highBase, isGuard]
        · simp [lowBase, isGuard]
      · cases positiveFound
  · cases found

theorem answerFrom_sound (query : Tabled.Query Variable Literal Symbol) (outcome : Engine.Outcome Variable Literal Symbol) :
    (setup.answerFrom query.context (goalOf query) outcome).Sound (setup.meaning query) := by
  unfold answerFrom
  split
  · trivial
  · split
    · rename_i term found
      intro Value model ⟨models, negation, realizes⟩ environment holds
      exact proved_sound found (models_checkSnapshot models realizes) negation environment holds
    · trivial
  · split
    · rename_i refuted
      intro Value model ⟨models, negation, _⟩ environment _ satisfied
      exact refutesIn_sound refuted models negation environment satisfied
    · split
      · rename_i holds fails found
        exact witnesses_sound found
      · split <;> trivial

/-- **The answers are sound**: Yes holds in every model of the completion,
No fails in every one, Unknown holds in one and fails in another, Undecided
claims nothing. -/
theorem answer_sound (fuel : Nat) (query : Tabled.Query Variable Literal Symbol) :
    (setup.answer fuel query).Sound (setup.meaning query) := by
  unfold answer
  split
  · rename_i blocked found
    unfold Program.answer? at found
    split at found
    · cases found; trivial
    · cases found
  · split
    · trivial
    · exact answerFrom_sound query _

/-- **Unknown never comes from an operational outcome**: only after the run
completed with no answer, and two witnesses. -/
theorem answer_unknown {fuel : Nat} {query : Tabled.Query Variable Literal Symbol} {holds fails : Witness Variable Literal Symbol}
    (answered : setup.answer fuel query = .unknown holds fails) :
    ∃ outcome, setup.runFor fuel query = .finished outcome := by
  unfold answer at answered
  split at answered
  · rename_i blocked found
    unfold Program.answer? at found
    split at found
    · cases found; cases answered
    · cases found
  · split at answered
    · cases answered
    cases ran : setup.runFor fuel query with
    | interrupted run => rw [ran] at answered; simp [answerFrom] at answered
    | success proof resume =>
        rw [ran] at answered; simp only [answerFrom] at answered; split at answered <;> cases answered
    | finished outcome => exact ⟨outcome, rfl⟩

end Setup

/-! ## More fuel -/

namespace Engine

variable (engine : Engine Variable Literal Symbol)

/-- A run that ended within its fuel ends the same with more. -/
theorem run_more : ∀ (fuel extra : Nat) (run : Run Variable Literal Symbol),
    (∀ final, engine.run fuel run ≠ .interrupted final) → engine.run (fuel + extra) run = engine.run fuel run
  | 0, _, run, ended => absurd rfl (ended run)
  | fuel + 1, extra, run, ended => by
      rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega]
      unfold Engine.run
      split
      · rename_i next stepped
        rw [run_more fuel extra next fun final same => ended final (by unfold Engine.run; rw [stepped]; exact same)]
      · rfl
      · rfl

end Engine

namespace Setup

variable {Domain : Type} (setup : Setup Domain Variable Literal Symbol)

theorem denialBlocker_more {fuel : Nat} {body : List (Term Variable Literal Symbol)}
    (none_ : setup.denialBlocker fuel body = none) (extra : Nat) : setup.denialBlocker (fuel + extra) body = none := by
  have ended : ∀ final, setup.runOf fuel [] (violation body) ≠ .interrupted final := by
    intro final ran
    unfold denialBlocker at none_; rw [ran] at none_; cases none_
  have more := (setup.engine (setup.space [] (violation body))).run_more fuel extra (Engine.start [] (violation body)) ended
  unfold denialBlocker runOf at none_ ⊢
  rw [more]; exact none_

theorem denialCheck_more {fuel : Nat} (none_ : setup.denialCheck fuel = none) (extra : Nat) :
    setup.denialCheck (fuel + extra) = none := by
  unfold denialCheck at none_ ⊢
  rw [List.findSome?_eq_none_iff] at none_ ⊢
  exact fun body member => setup.denialBlocker_more (none_ body member) extra

theorem findSome?_congr {α β : Type} {items : List α} {first second : α → Option β}
    (same : ∀ item ∈ items, first item = second item) : items.findSome? first = items.findSome? second := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.findSome?_cons, same item List.mem_cons_self,
        ih fun other member => same other (List.mem_cons_of_mem _ member)]

theorem denialFor_more {fuel : Nat} {body : List (Term Variable Literal Symbol)}
    (none_ : setup.denialFor fuel body = none) (extra : Nat) : setup.denialFor (fuel + extra) body = none := by
  unfold denialFor at none_ ⊢
  split
  · rename_i p1; simp only [p1, ↓reduceIte] at none_; exact none_
  · rename_i notP1; simp only [notP1, Bool.false_eq_true, ↓reduceIte] at none_; exact setup.denialBlocker_more none_ extra

theorem denialsFor_more {fuel : Nat} (none_ : setup.constraints.findSome? (setup.denialFor fuel) = none) (extra : Nat) :
    setup.constraints.findSome? (setup.denialFor (fuel + extra)) = none := by
  rw [List.findSome?_eq_none_iff] at none_ ⊢
  exact fun body member => setup.denialFor_more (none_ body member) extra

/-- **Answers are monotone in the fuel**: Yes, No, and Unknown never change
with more fuel; only Undecided can. -/
theorem answer_mono {fuel : Nat} {query : Tabled.Query Variable Literal Symbol}
    (decided : (setup.answer fuel query).decided = true) (extra : Nat) :
    setup.answer (fuel + extra) query = setup.answer fuel query := by
  unfold answer at decided ⊢
  split
  · rfl
  · rename_i notBlocked
    rw [notBlocked] at decided
    dsimp only at decided ⊢
    cases p1 : (setup.fragment.admit query).isP1 with
    | true =>
        simp only [denialsFor, runFor, p1, ↓reduceIte] at decided ⊢
        cases checked : setup.constraints.findSome? (setup.denialFor fuel) with
        | some blocker => rw [checked] at decided; simp [Answer.decided] at decided
        | none => rw [setup.denialsFor_more checked extra]
    | false =>
        simp only [denialsFor, runFor, p1, Bool.false_eq_true, ↓reduceIte] at decided ⊢
        cases checked : setup.denialCheck fuel with
        | some blocker => rw [checked] at decided; simp [Answer.decided] at decided
        | none =>
            rw [checked] at decided
            rw [setup.denialCheck_more checked extra]
            dsimp only at decided ⊢
            have ended : ∀ final, setup.runOf fuel query.context (goalOf query) ≠ .interrupted final := by
              intro final ran
              rw [ran] at decided
              simp [answerFrom, Answer.decided] at decided
            have more := (setup.engine (setup.space query.context (goalOf query))).run_more fuel extra
              (Engine.start query.context (goalOf query)) ended
            unfold runOf
            rw [more]

/-- **A P1 query needs no fuel**: its run is bounded and never interrupted
(`decided_ended`), and, when its KB's denials are P1 too, its answer is the
same whatever the fuel. A denial that is not P1 is checked with the fuel. -/
theorem answer_p1 {query : Tabled.Query Variable Literal Symbol} (p1 : (setup.fragment.admit query).isP1 = true)
    (denials : ∀ body ∈ setup.constraints, (setup.fragment.admit (denialQuery body)).isP1 = true)
    (fuel other : Nat) : setup.answer fuel query = setup.answer other query := by
  unfold answer
  simp only [denialsFor, runFor, p1, ↓reduceIte]
  rw [findSome?_congr fun body member => show setup.denialFor fuel body = setup.denialFor other body by
    simp only [denialFor, denials body member, ↓reduceIte]]

theorem decided_ended (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    ∀ final, setup.decided context goal ≠ .interrupted final :=
  (setup.boundedEngine context goal).runToEnd_ended (bounds := setup.bounds context goal) rfl _

end Setup

end AnthillModKbSpec.Tabled
