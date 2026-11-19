import AnthillModKbSpec.Resolution.IR.Cost
import AnthillModKbSpec.Resolution.Tabled.Witness

/-! # P2 within the fuel (S28)

A query of P2 lacks the finiteness evidence: its relevant program may be
infinite, or its names unguarded, outside the Herbrand reduction. It is not
decided exactly. The evaluator answers it soundly, by S24's methods on the
IR's rendering and a derivation within the fuel
([decision IR](../../../docs/decision-ir.md)):

- **Scopes.** S24's Kripke–Kleene iteration runs on a **scope**: the rules of
  the predicates a formula reads and of every predicate they reach
  (`Program.readClosure`), with the signature restricted to them
  (`Program.scopeSignature`). The only-if half of a predicate reads only its
  own rules (`definitions_scope`), so every model of the completion has on a
  scope what the iteration needs (`completes_scope`): the rest of the KB costs
  nothing. Predicates outside the scope are read as open: possibly true, never
  definitely.
- **No** by S24's refutation (`Program.refutedIn`) on the goals' scope, over
  the universe of its ground data terms and one abstract value ⋆ for every
  other value: a formula not possibly true under any abstract value of its
  names is false in every model of the completion (`refutedIn_sound`).
- **Unknown** by S24's witnesses (`Program.witnessesOver`), for a positive
  program and a positive goal with no condition: the least fixpoint with the
  markers false, over which a closed abstract least fixpoint shows the goal
  false, and the greatest with them true, below which a post-fixpoint over the
  universe and ⋆ shows it true; every denial body failing in the first and
  refuted once per KB for the second (`Program.denialsRefuted`). Both are key
  fixpoints of the whole completion, so models the answers are about
  (`witnessesOver_independence`). The cheap tests run first, the least
  fixpoint only for a positive program and goal, the greatest only once the
  least shows the goal false. The greatest witness reads guard, primitive,
  and declared atoms outside the closed predicates as false, so it shows a goal
  true only through closed predicates and markers.
- **Yes** by a derivation (`Derivation`): rule instances in order, each by its
  rule's index and its names' values, and an instance of the goals. A step is
  derived when its values are its rule's names' (`Rule.names`' repeats
  agreeing), its names hold ground terms, its calls are at atoms derived
  before it, its NAF operands are refuted, its fixed literals are true, and it
  has no marker literal (`Program.stepHead`). The checker
  (`Program.checkDerivation`) needs only the program and the query; a checked
  derivation's goal holds in every model of the completion realizing the
  signature (`checkDerivation_sound`). The search (`Program.searchFrom`) runs
  S27's saturation from the goals one round at a time, up to the fuel, and at
  each table takes the checked instances at its calls round by round, the
  calls found last first, until a round takes none; the first table that
  derives an instance of the goals gives the derivation, with its round, and
  the evaluator checks it before answering Yes.
- **What P2 assumes of the KB.** Every answer assumes a model (S24's policy,
  decided with the user, 2026-11-09). P1 answers on the KB-level check
  (`kbCheck`) alone; a P2 Yes or No also needs the check to have settled the
  KB (`Program.kbUnsettled`): when the KB-level query is not P1, the
  NAF-cycle roots whose own query is not P1 checked together on their ground
  closure (`Program.groundClosure`, when every rule they reach is ground), and
  the denials no P1 query read refuted. Otherwise Undecided, the KB's
  consistency, naming what is unsettled or the piece with no model. An
  Unknown needs nothing: its witnesses are models.
- **Undecided** otherwise, with the profile's notes: the growing call, the
  call with a free output, the unguarded name, or the unsplit parameter, each
  lacking a termination argument.

The decision (`Program.decideWithin`) runs the KB-level check, decides a P0 or
P1 query exactly with no fuel (S28's combination of its instances), and a P2
query by the steps above (`Program.budgeted`): the witnesses, then the
consistency gate, the refutation, and the first derivation the search finds
within the fuel. So every decision is sound (`decideWithin_sound`); a P0 or P1
query gets its exact answer whatever the fuel (`decideWithin_evidence`); and
once a decision is not Undecided, more fuel gives the same one
(`decideWithin_mono`). Every decision's certificate is checked by
`Program.checkDecision` (`checkDecision_sound`), on the same conditions as the
evaluator's: P0's and P1's as before, a derivation by its checker, a
refutation and S24's witnesses by computing them again. A derivation's round
is the search's, not checked. -/

namespace AnthillModKbSpec.IR

open Semantics Completion Tabled Answers

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

attribute [local instance] Machine.termEq

/-- A derivation of a closed query: rule instances in order, each by its
rule's index and the values of its names (in the order of `Rule.names`), and
an instance of the query's goals by the values of their names (in the order of
`bodyNames`). Each instance derives its head from the heads before it, its NAF
operands refuted, no marker literal read. -/
structure Derivation (Variable Literal Symbol : Type) where
  steps : List (Nat × List (Term Variable Literal Symbol))
  goal : List (Term Variable Literal Symbol)

/-- A ground atom holds in a model: the model's atom at its terms' values. -/
def AtomHolds {Value : Type} {hoApplySymbol : Symbol} (model : Model Literal Symbol Value hoApplySymbol)
    (atom : GAtom Variable Literal Symbol) : Prop :=
  model.holds (model.application atom.1 (atom.2.map (den model)))

namespace Program

variable (program : Program Variable Literal Symbol)

/-! ## Scopes: S24's iteration on the rules a formula reads -/

/-- The predicates some bodies read, and every one they reach in the
predicate graph. -/
def readClosure (bodies : List (List (Goal Variable Literal Symbol))) : List Symbol :=
  program.closureOf (bodies.flatMap bodyPredicates)

/-- A scope's clauses: the rules of its predicates. -/
def scopeClauses (symbols : List Symbol) : List (HornClause Variable Literal Symbol) :=
  (program.rules.filter fun rule => symbols.contains rule.head).map Rule.toClause

/-- A scope's signature: the closed predicates among its predicates, and the
declared constructors. -/
def scopeSignature (symbols : List Symbol) : Signature Literal Symbol :=
  ⟨program.closedKeys.filter fun key => symbols.contains key.1, program.constructors⟩

/-- A scope's universe for some formulas: the ground data subterms of its
clauses and of the formulas (S24's `universeOf`). -/
def universeIn (symbols : List Symbol) (formulas : List (Term Variable Literal Symbol)) : List (Term Variable Literal Symbol) :=
  universeOf program.constructors (program.scopeClauses symbols) formulas

/-- S24's Kripke–Kleene iteration over a universe, on a scope, stopped once a
round changes nothing. -/
def kleeneIn (symbols : List Symbol) (space : List (Term Variable Literal Symbol)) :
    List (GAtom Variable Literal Symbol) × List (AAtom Variable Literal Symbol) :=
  untilStable (fun next current => decide (next.1 = current.1) && decide (next.2 = current.2))
    (kkStep (program.scopeSignature symbols) space (program.scopeClauses symbols)) (rounds (program.scopeSignature symbols) space)
    (kk (program.scopeSignature symbols) space (program.scopeClauses symbols) 0)

theorem kleeneIn_round (symbols : List Symbol) (space : List (Term Variable Literal Symbol)) :
    ∃ round, program.kleeneIn symbols space = kk (program.scopeSignature symbols) space (program.scopeClauses symbols) round :=
  untilStable_round _ _ _ (kk_succ _ _ _) _ 0

/-- A formula refuted over a universe on a scope, the universe's validity and
the iteration's result given. -/
def refutedIn (symbols : List Symbol) (valid : Bool) (space : List (Term Variable Literal Symbol))
    (fixed : List (GAtom Variable Literal Symbol) × List (AAtom Variable Literal Symbol)) (formula : Term Variable Literal Symbol) :
    Bool :=
  valid && refutesWith (program.scopeSignature symbols) space fixed formula

variable {program}

omit [DecidableEq Variable] [DecidableEq Literal] in
/-- A scope's predicate has the program's definitions: its rules are all in
the scope, and the denials define nothing. -/
theorem definitions_scope {symbols : List Symbol} {symbol : Symbol} (inside : symbols.contains symbol = true) (arity : Nat) :
    definitions (program.scopeClauses symbols) symbol arity = definitions program.clauses symbol arity := by
  have rulesSame : ∀ rules : List (Rule Variable Literal Symbol),
      definitions ((rules.filter fun rule => symbols.contains rule.head).map Rule.toClause) symbol arity =
        definitions (rules.map Rule.toClause) symbol arity := by
    intro rules
    induction rules with
    | nil => rfl
    | cons rule rest ih =>
        by_cases kept : symbols.contains rule.head = true
        · simp only [List.filter_cons, kept, ite_true, List.map_cons, definitions, List.filterMap_cons, Rule.toClause] at ih ⊢
          rw [ih]
        · simp only [List.filter_cons, kept, Bool.false_eq_true, ite_false, List.map_cons, definitions, List.filterMap_cons,
            Rule.toClause] at ih ⊢
          have different : rule.head ≠ symbol := fun same => kept (same ▸ inside)
          simp only [different, false_and, ite_false]
          exact ih
  have denialsNone : definitions (program.denials.map denialClause) symbol arity = [] := by
    simp only [definitions, List.filterMap_map]
    exact List.filterMap_eq_nil_iff.mpr fun _ _ => rfl
  unfold scopeClauses Program.clauses
  rw [rulesSame]
  simp only [definitions, List.filterMap_append] at denialsNone ⊢
  rw [denialsNone, List.append_nil]

omit [DecidableEq Literal] in
/-- **A scope completes as the program does**: a model with what S24's
iteration needs of the program has it of every scope. -/
theorem completes_scope [FreshNames Variable] {Value : Type} {model : Model Literal Symbol Value program.hoApply}
    (completes : Completes model program.signature program.clauses) (symbols : List Symbol) :
    Completes model (program.scopeSignature symbols) (program.scopeClauses symbols) where
  program symbol args body member environment := by
    obtain ⟨rule, ruleMember, same⟩ := List.mem_map.mp member
    exact completes.program symbol args body
      (List.mem_append_left _ (List.mem_map.mpr ⟨rule, (List.mem_filter.mp ruleMember).1, same⟩)) environment
  onlyIf key member environment := by
    obtain ⟨closed, inside⟩ := List.mem_filter.mp member
    have same : onlyIf (program.scopeClauses symbols) key.1 key.2 = onlyIf program.clauses key.1 key.2 := by
      unfold onlyIf
      rw [definitions_scope inside]
    rw [same]
    exact completes.onlyIf key closed environment
  free := completes.free

/-- **A refuted formula is false** in every model with what S24's iteration
needs, under every environment. -/
theorem refutedIn_sound [FreshNames Variable] {symbols : List Symbol} {space : List (Term Variable Literal Symbol)}
    {formula : Term Variable Literal Symbol}
    (refuted : program.refutedIn symbols (validUniverse program.constructors space) space (program.kleeneIn symbols space) formula = true)
    {Value : Type} {model : Model Literal Symbol Value program.hoApply} (completes : Completes model program.signature program.clauses)
    (negation : model.ComplementNAF) (environment : Environment Variable Value) : ¬ model.Satisfies environment formula := by
  simp only [refutedIn, Bool.and_eq_true] at refuted
  obtain ⟨round, roundEq⟩ := program.kleeneIn_round symbols space
  rw [roundEq] at refuted
  exact refutes_sound (count := round) (completes_scope completes symbols) refuted.1 negation refuted.2 environment

/-- A model of the completion has what S24's iteration needs. -/
theorem completes_of_models [FreshNames Variable] {Value : Type} {model : Model Literal Symbol Value program.hoApply}
    (models : program.Models model) : Completes model program.signature program.clauses :=
  Completes.of_models (signature := program.signature) (clauses := program.clauses) models.1

/-- **No**: a query refuted on a scope fails in every model satisfying its
context. -/
theorem refutedIn_falsity [FreshNames Variable] {symbols : List Symbol} {space : List (Term Variable Literal Symbol)}
    {query : Query Variable Literal Symbol}
    (refuted : program.refutedIn symbols (validUniverse program.constructors space) space (program.kleeneIn symbols space)
      query.formula = true) :
    (program.meaning query).falsity :=
  fun _ _ models environment _ => refutedIn_sound refuted (completes_of_models models) models.2.1 environment

/-! ## The denials, once per KB -/

variable (program)

/-- The denials' scope: the predicates they read and every one those reach. -/
def denialScope : List Symbol := program.readClosure program.denials

/-- The first denial body not refuted (S24) on the denials' scope, over the
universe of its clauses and the bodies. Computed once per KB. -/
def unrefutedDenial : Option (List (Goal Variable Literal Symbol)) :=
  if program.denials.isEmpty then none
  else
    let symbols := program.denialScope
    let space := program.universeIn symbols (program.denials.map bodyTerm)
    let fixed := program.kleeneIn symbols space
    let valid := validUniverse program.constructors space
    program.denials.find? fun body => !program.refutedIn symbols valid space fixed (bodyTerm body)

/-- Every denial body refuted: no model of the program's clauses violates a
denial. -/
def denialsRefuted : Bool := program.unrefutedDenial.isNone

variable {program}

theorem denialsRefuted_sound [FreshNames Variable] (refuted : program.denialsRefuted = true) {Value : Type}
    {model : Model Literal Symbol Value program.hoApply} (completes : Completes model program.signature program.clauses)
    (negation : model.ComplementNAF) :
    ∀ body ∈ program.denials, ∀ environment, ¬ model.Satisfies environment (bodyTerm body) := by
  intro body member environment
  unfold denialsRefuted unrefutedDenial at refuted
  split at refuted
  · rename_i empty
    rw [List.isEmpty_iff.mp empty] at member
    cases member
  · simp only [Option.isNone_iff_eq_none, List.find?_eq_none, Bool.not_eq_true', Bool.not_eq_false] at refuted
    exact refutedIn_sound (refuted body member) completes negation environment

/-! ## Unknown: the least and the greatest fixpoint (S24) -/

variable (program)

/-- The marker atoms: the symbols no declaration names, other than `ho_apply`. -/
def marked (symbol : Symbol) : Bool := (program.predicate? symbol).isNone && symbol != program.hoApply

/-- The positive programs, decided: every rule's arguments data and its body
positive (S24's `PositiveProgram`). -/
def positive : Bool :=
  program.clauses.all fun
    | .definite (.app _ args) body => dataArgs args && body.all (positiveGoal program.hoApply)
    | _ => true

/-- The universe of S24's witnesses: the ground data subterms of the whole
rendering and of the query. -/
def witnessUniverse (query : Query Variable Literal Symbol) : List (Term Variable Literal Symbol) :=
  universeOf program.constructors program.clauses (query.formula :: query.context)

/-- **S24's two witnesses**, for a positive program and a positive goal with
no condition: a post-fixpoint in which the goal holds (the greatest fixpoint
lies above it), and a closed abstract least fixpoint in which it fails, every
denial body failing in it and refuted once per KB. The cheap tests run first;
the least fixpoint only for a positive program and goal, the greatest only
once the least shows the goal false. -/
def witnessesOver (query : Query Variable Literal Symbol) :
    Option (List (AAtom Variable Literal Symbol) × List (AAtom Variable Literal Symbol)) :=
  let space := program.witnessUniverse query
  if query.conditions.isEmpty && validUniverse program.constructors space && program.positive &&
      positiveGoal program.hoApply query.formula then
    let count := rounds program.signature space
    let low := untilStable (fun next current => decide (next = current)) (leastStep program.signature space program.clauses) count
      (leastOver program.signature space program.clauses 0)
    if closedLeast program.signature space program.clauses low && failsLeast program.signature space low query.formula &&
        program.denials.all (fun body => failsLeast program.signature space low (bodyTerm body)) then
      let high := untilStable (fun next current => decide (next = current))
        (greatestStep program.signature space program.clauses program.marked) count
        (greatestOver program.signature space program.clauses program.marked 0)
      if postGreatest program.signature space program.clauses program.marked high &&
          vtrue program.signature space program.marked high (fun _ => none) query.formula && program.denialsRefuted then
        some (high, low)
      else none
    else none
  else none

variable {program}

omit [DecidableEq Variable] [DecidableEq Literal] in
theorem positive_spec (found : program.positive = true) : PositiveProgram program.hoApply program.clauses := by
  intro symbol args body member
  simp only [positive, List.all_eq_true] at found
  have shape := found _ member
  simp only [Bool.and_eq_true, List.all_eq_true] at shape
  exact shape

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem goal_of_mem_clauses {body : List (Term Variable Literal Symbol)} (member : HornClause.goal body ∈ program.clauses) :
    ∃ denial ∈ program.denials, body = denial.map Goal.toTerm := by
  rcases List.mem_append.mp member with inRules | inDenials
  · obtain ⟨_, _, same⟩ := List.mem_map.mp inRules
    cases same
  · obtain ⟨denial, denialMember, same⟩ := List.mem_map.mp inDenials
    simp only [denialClause, HornClause.goal.injEq] at same
    exact ⟨denial, denialMember, same.symm⟩

/-- **S24's witnesses are an Unknown's**: two models of the completion
realizing the signature, one where the query holds and one where it fails, its
context empty. The greatest fixpoint's denials are false by the KB-level
refutation (`denialsRefuted_sound`). -/
theorem witnessesOver_independence [FreshNames Variable] (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    {high low : List (AAtom Variable Literal Symbol)} (found : program.witnessesOver query = some (high, low)) :
    (program.meaning query).independence := by
  unfold witnessesOver at found
  dsimp only at found
  split at found
  · rename_i first
    split at found
    · rename_i second
      split at found
      · rename_i third
        simp only [Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, rfl⟩ := found
        simp only [Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at first second third
        obtain ⟨⟨⟨noConditions, valid⟩, positive⟩, goalPositive⟩ := first
        obtain ⟨⟨closedL, fails⟩, denialsFail⟩ := second
        obtain ⟨⟨post, holds⟩, refuted⟩ := third
        have covered := program.covered wellFormed
        have positiveProgram := positive_spec positive
        have contextHolds : ∀ {Value : Type} {model : Model Literal Symbol Value program.hoApply} environment,
            model.ContextHolds environment query.context := fun _ => by
          simp only [Query.context, noConditions, List.map_nil]
          intro _ inside
          cases inside
        -- The least fixpoint, the markers false: the query fails.
        obtain ⟨lowModels, lowFails⟩ := least_witness covered positiveProgram valid closedL (program.base fun _ _ => False)
          (fun body member => by
            obtain ⟨denial, denialMember, rfl⟩ := goal_of_mem_clauses member
            exact denialsFail denial denialMember) fails
        -- The greatest fixpoint, the markers true: the query holds (S24's
        -- `greatest_witness`, its denials false by the KB-level refutation).
        obtain ⟨highRound, highEq⟩ := untilStable_round _ _ _
          (greatestOver_succ program.signature (program.witnessUniverse query) program.clauses program.marked)
          (rounds program.signature (program.witnessUniverse query)) 0
        have markedOrdinary : program.marked program.hoApply = false := by simp [marked]
        have markedTrue : ∀ symbol keys, program.marked symbol = true → program.base (fun _ _ => True) symbol keys := by
          intro symbol keys isMarked
          simp only [marked, Bool.and_eq_true, Option.isNone_iff_eq_none] at isMarked
          simp [Program.base, isMarked.1]
        have mono := consequence_mono program.signature positiveProgram (program.base fun _ _ => True)
        have fixpoint := fixpoint_of_monotone (gfp_pre mono) (gfp_post mono)
        have below := le_gfp (highInterp_post covered.ordinary markedOrdinary markedTrue post
          (by rw [highEq]; exact greatestOver_atoms _))
        have highModels := models_of_fixpoint covered fixpoint fun body member environment => by
          obtain ⟨denial, denialMember, rfl⟩ := goal_of_mem_clauses member
          exact denialsRefuted_sound refuted (Completes.of_fixpoint covered fixpoint) (Model.keys_complement _) denial
            denialMember environment
        have highHolds := satisfies_mono (join_mono program.signature _ below) query.formula _ goalPositive
          (vtrue_sound covered.ordinary markedOrdinary markedTrue query.formula (fun _ => none) holds)
        exact ⟨⟨_, _, program.keyFixpoint_models wellFormed ((program.keyModel_models_iff wellFormed).mp highModels), _,
            contextHolds _, highHolds⟩,
          ⟨_, _, program.keyFixpoint_models wellFormed ((program.keyModel_models_iff wellFormed).mp lowModels),
            fun _ => .truth False, contextHolds _, lowFails _⟩⟩
      · cases found
    · cases found
  · cases found

/-! ## Yes: a derivation, checked -/

variable (program)

/-- A literal derived at an instance from atoms: a call at one of them, a NAF
literal whose operand is refuted, a fixed literal true. A marker literal is
never derived: the markers are unknown. -/
def literalDerived (refuted : Term Variable Literal Symbol → Bool) (derived : List (GAtom Variable Literal Symbol))
    (σ : Variable → Term Variable Literal Symbol) : Goal Variable Literal Symbol → Bool
  | .call predicate args => derived.contains (predicate, args.map (subst σ))
  | .naf predicate args => refuted (.app predicate (args.map (subst σ)))
  | .marker _ _ => false
  | goal => program.fixedB σ goal

/-- A body derived at an instance: the names hold ground terms and each
literal is derived. -/
def bodyDerived (refuted : Term Variable Literal Symbol → Bool) (derived : List (GAtom Variable Literal Symbol))
    (names : List Variable) (σ : Variable → Term Variable Literal Symbol) (body : List (Goal Variable Literal Symbol)) : Bool :=
  names.all (fun name => groundIn program.constructors (σ name)) && body.all (program.literalDerived refuted derived σ)

/-- The head a step derives from atoms: its rule's head at its values, when
the values are its rule's names' (`Rule.names`' repeats agreeing) and its
body is derived. -/
def stepHead (refuted : Term Variable Literal Symbol → Bool) (derived : List (GAtom Variable Literal Symbol))
    (step : Nat × List (Term Variable Literal Symbol)) : Option (GAtom Variable Literal Symbol) :=
  match program.rules[step.1]? with
  | some rule =>
      if rule.names.map (substOf rule.names step.2) == step.2 &&
          program.bodyDerived refuted derived rule.names (substOf rule.names step.2) rule.body then
        some (rule.head, rule.args.map (subst (substOf rule.names step.2)))
      else none
  | none => none

/-- The atoms a derivation's steps derive, from atoms given: each step's head
from the atoms before it; none when a step is not derived. -/
def derivedAtoms (refuted : Term Variable Literal Symbol → Bool) :
    List (GAtom Variable Literal Symbol) → List (Nat × List (Term Variable Literal Symbol)) →
      Option (List (GAtom Variable Literal Symbol))
  | derived, [] => some derived
  | derived, step :: rest =>
      match program.stepHead refuted derived step with
      | some head => derivedAtoms refuted (head :: derived) rest
      | none => none

/-- A derivation of a closed query, the refutations given: its goal's values
are the goals' names' (their repeats agreeing), its steps derive atoms, and
the goals' instance is derived from them. -/
def derivationHolds (refuted : Term Variable Literal Symbol → Bool) (query : Query Variable Literal Symbol)
    (derivation : Derivation Variable Literal Symbol) : Bool :=
  query.parameters.isEmpty &&
    (bodyNames query.goals).map (substOf (bodyNames query.goals) derivation.goal) == derivation.goal &&
    match program.derivedAtoms refuted [] derivation.steps with
    | some derived =>
        program.bodyDerived refuted derived (bodyNames query.goals) (substOf (bodyNames query.goals) derivation.goal) query.goals
    | none => false

/-- **A derivation, checked**: the query passes S27's checker and is closed,
each step is derived from the atoms before it, and the goal's instance from
them all, NAF operands refuted on the goals' scope (S24). -/
def checkDerivation (query : Query Variable Literal Symbol) (derivation : Derivation Variable Literal Symbol) : Bool :=
  (program.check query).isEmpty &&
    let symbols := program.readClosure [query.goals]
    let space := program.universeIn symbols [query.formula]
    program.derivationHolds (program.refutedIn symbols (validUniverse program.constructors space) space
      (program.kleeneIn symbols space)) query derivation

variable {program}

section Derivations

variable [FreshNames Variable] {Value : Type} {model : Model Literal Symbol Value program.hoApply}

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
/-- A closed query's goals have only answer names. -/
theorem names_answers_of {query : Query Variable Literal Symbol} (none : query.parameters = []) {name : Variable}
    (occurs : name ∈ bodyNames query.goals) : name ∈ query.answers := by
  by_cases answer : name ∈ query.answers
  · exact answer
  · have inside : name ∈ (bodyNames query.conditions ++ bodyNames query.goals).eraseDups.filter
        (fun name => !query.answers.contains name) :=
      List.mem_filter.mpr ⟨List.mem_eraseDups.mpr (List.mem_append_right _ occurs), by simp [answer]⟩
    unfold Query.parameters at none
    rw [none] at inside
    cases inside

/-- **A derived literal holds** in every model of the completion realizing
the signature, under the values of the instance: a call at an atom that holds,
a NAF literal at a refuted operand, a fixed literal by the realized guards
and primitives and the free constructors. -/
theorem literal_holds (models : program.Models model) {refuted : Term Variable Literal Symbol → Bool}
    (refutedSound : ∀ formula, refuted formula = true → ∀ environment, ¬ model.Satisfies environment formula)
    {derived : List (GAtom Variable Literal Symbol)} (holds : ∀ atom ∈ derived, AtomHolds model atom)
    {σ : Variable → Term Variable Literal Symbol} {goal : Goal Variable Literal Symbol}
    (declared : program.declares goal = true) (data : program.data goal = true)
    (ground : ∀ name ∈ goal.names, groundIn program.constructors (σ name) = true)
    (derives : program.literalDerived refuted derived σ goal = true) :
    model.Satisfies (fun name => den model (σ name)) goal.toTerm := by
  have allData : ∀ arg ∈ goal.args, dataIn program.constructors arg = true := List.all_eq_true.mp data
  have valuesEq : ∀ {args : List (Term Variable Literal Symbol)}, (∀ arg ∈ args, dataIn program.constructors arg = true) →
      args.map (model.eval fun name => den model (σ name)) = (args.map (subst σ)).map (den model) := by
    intro args argsData
    rw [evalAll_subst model σ args (dataInAll_of argsData), List.map_map]
  have groundOf : ∀ {term : Term Variable Literal Symbol}, term ∈ goal.args → groundIn program.constructors (subst σ term) = true :=
    fun member => groundIn_subst _ (allData _ member) fun name occurs => ground name (names_args_sub member occurs)
  cases goal with
  | call predicate args =>
      simp only [literalDerived, List.contains_iff_mem] at derives
      show model.Satisfies _ (.app predicate args)
      rw [sat_app, valuesEq (args := args) allData]
      exact holds _ derives
  | naf predicate args =>
      simp only [literalDerived] at derives
      show model.Satisfies _ (.defaultNeg (.app predicate args))
      rw [sat_neg _ _ models.2.1, sat_app, valuesEq (args := args) allData]
      intro atomHolds
      apply refutedSound _ derives (fun name => den model (σ name))
      rw [sat_app, eval_grounds _ _ ((groundInAll_iff program.constructors).mpr fun term member => by
        obtain ⟨arg, argMember, rfl⟩ := List.mem_map.mp member
        exact groundOf argMember)]
      exact atomHolds
  | equal left right =>
      simp only [literalDerived, fixedB, decide_eq_true_eq] at derives
      show model.Satisfies _ (.equal left right)
      rw [Model.satisfies_equal, eval_subst model σ left (allData left (by simp [Goal.args])),
        eval_subst model σ right (allData right (by simp [Goal.args])), derives]
  | differ left right =>
      simp only [literalDerived, fixedB, Bool.not_eq_true', decide_eq_false_iff_not] at derives
      show model.Satisfies _ (.defaultNeg (.equal left right))
      rw [sat_neg _ _ models.2.1, Model.satisfies_equal, eval_subst model σ left (allData left (by simp [Goal.args])),
        eval_subst model σ right (allData right (by simp [Goal.args]))]
      exact fun same => derives (den_injective (free_of_models models) _ _ (groundOf (by simp [Goal.args]))
        (groundOf (by simp [Goal.args])) same)
  | guard symbol arg =>
      simp only [literalDerived, fixedB] at derives
      obtain ⟨found, foundEq, kind, _⟩ := kindAt_declared declared
      show model.Satisfies _ (.app symbol [arg])
      rw [sat_app]
      simp only [List.map_cons, List.map_nil, eval_subst model σ arg (allData arg (by simp [Goal.args]))]
      exact (models.2.2.guards symbol ⟨found, foundEq, kind⟩ _).mpr ⟨_, groundOf (by simp [Goal.args]), derives, rfl⟩
  | primitive symbol inputs output =>
      simp only [literalDerived, fixedB, decide_eq_true_eq] at derives
      obtain ⟨found, foundEq, kind, _⟩ := kindAt_declared declared
      show model.Satisfies _ (.app symbol (inputs ++ [output]))
      rw [sat_app, valuesEq (args := inputs ++ [output]) allData]
      refine (models.2.2.primitives symbol ⟨found, foundEq, kind⟩ _).mpr
        ⟨inputs.map (subst σ), subst σ output, ?_, groundOf (by simp [Goal.args]), derives, by simp⟩
      intro input member
      obtain ⟨arg, argMember, rfl⟩ := List.mem_map.mp member
      exact groundOf (List.mem_append_left _ argMember)
  | marker symbol args => simp [literalDerived] at derives

/-- A derived body holds, literal by literal. -/
theorem body_holds (models : program.Models model) {refuted : Term Variable Literal Symbol → Bool}
    (refutedSound : ∀ formula, refuted formula = true → ∀ environment, ¬ model.Satisfies environment formula)
    {derived : List (GAtom Variable Literal Symbol)} (holds : ∀ atom ∈ derived, AtomHolds model atom)
    {names : List Variable} {σ : Variable → Term Variable Literal Symbol} {body : List (Goal Variable Literal Symbol)}
    (ok : ∀ goal ∈ body, program.declares goal = true ∧ program.data goal = true)
    (covers : ∀ name ∈ bodyNames body, name ∈ names) (derives : program.bodyDerived refuted derived names σ body = true) :
    model.Satisfies (fun name => den model (σ name)) (bodyTerm body) := by
  simp only [bodyDerived, Bool.and_eq_true, List.all_eq_true] at derives
  unfold bodyTerm
  rw [Model.satisfies_conjunction]
  intro term member
  obtain ⟨goal, goalMember, rfl⟩ := List.mem_map.mp member
  exact literal_holds models refutedSound holds (ok goal goalMember).1 (ok goal goalMember).2
    (fun name occurs => derives.1 name (covers name (List.mem_flatMap.mpr ⟨goal, goalMember, occurs⟩))) (derives.2 goal goalMember)

/-- **A derived step's head holds** in every model of the completion
realizing the signature, when the atoms it reads do: its body holds, so its
rule's clause gives its head. -/
theorem stepHead_holds (wellFormed : program.WellFormed) (models : program.Models model)
    {refuted : Term Variable Literal Symbol → Bool}
    (refutedSound : ∀ formula, refuted formula = true → ∀ environment, ¬ model.Satisfies environment formula)
    {derived : List (GAtom Variable Literal Symbol)} (holds : ∀ atom ∈ derived, AtomHolds model atom)
    {step : Nat × List (Term Variable Literal Symbol)} {head : GAtom Variable Literal Symbol}
    (found : program.stepHead refuted derived step = some head) : AtomHolds model head := by
  unfold stepHead at found
  split at found
  · rename_i rule ruleFound
    split at found
    · rename_i checks
      simp only [Option.some.injEq] at found
      subst found
      simp only [Bool.and_eq_true] at checks
      have ruleMember := List.mem_of_getElem? ruleFound
      have bodyHolds := body_holds models refutedSound holds (goals_ok wellFormed ruleMember)
        (fun name inside => List.mem_append_right _ inside) checks.2
      have clause := (completes_of_models models).program rule.head rule.args (rule.body.map Goal.toTerm)
        (List.mem_append_left _ (List.mem_map.mpr ⟨rule, ruleMember, rfl⟩))
        (fun name => den model (substOf rule.names step.2 name))
      rw [sat_imp] at clause
      have headHolds := clause bodyHolds
      rw [sat_app, evalAll_subst model _ rule.args (dataInAll_of (wellFormed.rules rule ruleMember).data)] at headHolds
      show model.holds (model.application rule.head ((rule.args.map (subst (substOf rule.names step.2))).map (den model)))
      rw [List.map_map]
      exact headHolds
    · cases found
  · cases found

/-- **The atoms a derivation derives hold** in every model of the completion
realizing the signature, by induction on its steps. -/
theorem derivedAtoms_holds (wellFormed : program.WellFormed) (models : program.Models model)
    {refuted : Term Variable Literal Symbol → Bool}
    (refutedSound : ∀ formula, refuted formula = true → ∀ environment, ¬ model.Satisfies environment formula) :
    ∀ {derived : List (GAtom Variable Literal Symbol)} {steps : List (Nat × List (Term Variable Literal Symbol))}
      {result : List (GAtom Variable Literal Symbol)}, program.derivedAtoms refuted derived steps = some result →
        (∀ atom ∈ derived, AtomHolds model atom) → ∀ atom ∈ result, AtomHolds model atom
  | derived, [], result, found, holds => by
      simp only [derivedAtoms, Option.some.injEq] at found
      subst found
      exact holds
  | derived, step :: rest, result, found, holds => by
      simp only [derivedAtoms] at found
      split at found
      · rename_i head headFound
        apply derivedAtoms_holds wellFormed models refutedSound found
        intro atom member
        rcases List.mem_cons.mp member with rfl | earlier
        · exact stepHead_holds wellFormed models refutedSound holds headFound
        · exact holds atom earlier
      · cases found

/-- **A derivation shows Yes**, the refutations sound, for a well-formed
program and a query whose goals scan: the goal's instance holds in every
model, so its existential closure does. -/
theorem derivationHolds_truth (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (goalsOk : ∀ goal ∈ query.goals, program.declares goal = true ∧ program.data goal = true)
    {refuted : Term Variable Literal Symbol → Bool}
    (refutedSound : ∀ {Value : Type} {model : Model Literal Symbol Value program.hoApply}, program.Models model →
      ∀ formula, refuted formula = true → ∀ environment, ¬ model.Satisfies environment formula)
    {derivation : Derivation Variable Literal Symbol} (checked : program.derivationHolds refuted query derivation = true) :
    (program.meaning query).truth := by
  unfold derivationHolds at checked
  simp only [Bool.and_eq_true, List.isEmpty_iff] at checked
  obtain ⟨⟨none, _⟩, rest⟩ := checked
  split at rest
  · rename_i derived found
    intro Value model models environment _
    have holds := derivedAtoms_holds wellFormed models (refutedSound models) found fun _ member => by cases member
    have bodyHolds := body_holds models (refutedSound models) holds goalsOk (fun _ inside => inside) rest
    unfold Query.formula
    apply satisfies_exists_of model _ query.answers environment
      (fun name => den model (substOf (bodyNames query.goals) derivation.goal name))
    unfold Model.Satisfies
    rw [Model.eval_congr model _ (right := fun name => den model (substOf (bodyNames query.goals) derivation.goal name))
      fun name occurs => by simp [override, names_answers_of none (bodyNames_of_freeVars occurs)]]
    exact bodyHolds
  · cases rest

/-- **A checked derivation is a Yes**: the query holds in every model of the
completion realizing the signature. -/
theorem checkDerivation_sound {query : Query Variable Literal Symbol} {derivation : Derivation Variable Literal Symbol}
    (checked : program.checkDerivation query derivation = true) : (program.meaning query).truth := by
  unfold checkDerivation at checked
  simp only [Bool.and_eq_true, List.isEmpty_iff] at checked
  exact derivationHolds_truth (program.wellFormed_of_check checked.1) (Scans.goals (program.queryOk_of_check checked.1).goals)
    (fun models _ refuted environment => refutedIn_sound refuted (completes_of_models models) models.2.1 environment) checked.2

end Derivations

/-! ## The search within the fuel -/

variable (program)

/-- The candidate steps of a saturation table: the checked passing instances
at its calls, read from its answers. -/
def tableSteps (table : CallTable Variable Literal Symbol) : List (Nat × List (Term Variable Literal Symbol)) :=
  let answers := tableAnswers table
  (table.flatMap fun entry => program.instancesAt answers entry.1.1 entry.1.2).eraseDups

/-- One round of the derivation: each pending candidate whose body the atoms
derive is taken and its head derived at once; the others stay pending. The
steps are kept newest first. -/
def deriveRound (refuted : Term Variable Literal Symbol → Bool)
    (state : List (Nat × List (Term Variable Literal Symbol)) × List (GAtom Variable Literal Symbol) ×
      List (Nat × List (Term Variable Literal Symbol))) :
    List (Nat × List (Term Variable Literal Symbol)) × List (GAtom Variable Literal Symbol) ×
      List (Nat × List (Term Variable Literal Symbol)) :=
  state.2.2.foldl (fun current step =>
    match program.stepHead refuted current.2.1 step with
    | some head => (step :: current.1, head :: current.2.1, current.2.2)
    | none => (current.1, current.2.1, step :: current.2.2)) (state.1, state.2.1, [])

/-- A derivation from a saturation table: its candidates taken round by round,
the calls found last first, until a round takes none, and the first instance
of the query's goals they derive. Checked before it is used. -/
def derivationIn (refuted : Term Variable Literal Symbol → Bool) (query : Query Variable Literal Symbol)
    (table : CallTable Variable Literal Symbol) : Option (Derivation Variable Literal Symbol) :=
  let candidates := program.tableSteps table
  let state := untilStable (fun next current => next.2.2.length == current.2.2.length) (program.deriveRound refuted)
    (candidates.length + 1) ([], [], candidates.reverse)
  ((program.bodyInstances (tableAnswers table) query.parameters (fun _ => none) query.goals).find? fun values =>
      program.bodyDerived refuted state.2.1 (bodyNames query.goals) (substOf (bodyNames query.goals) values) query.goals).map
    fun values => ⟨state.1.reverse, values⟩

/-- **The search within the fuel**: S27's saturation from the goals alone (no
condition and no denial: a derivation reads neither), one round at a time,
stopping once a round adds nothing; a derivation sought at each table; the
first one found, with its round. -/
def searchFrom (refuted : Term Variable Literal Symbol → Bool) (query : Query Variable Literal Symbol) :
    Nat → Nat → CallTable Variable Literal Symbol → Option (Nat × Derivation Variable Literal Symbol)
  | 0, n, table => (program.derivationIn refuted query table).map (n, ·)
  | fuel + 1, n, table =>
      match program.derivationIn refuted query table with
      | some derivation => some (n, derivation)
      | none =>
          let next := ({ program with denials := [] } : Program Variable Literal Symbol).round { query with conditions := [] } table
          if tableSize next = tableSize table then none else searchFrom refuted query fuel (n + 1) next

variable {program}

/-- **More fuel finds the same derivation**: the search stops at the first. -/
theorem searchFrom_mono {refuted : Term Variable Literal Symbol → Bool} {query : Query Variable Literal Symbol}
    {found : Nat × Derivation Variable Literal Symbol} :
    ∀ {fuel n : Nat} {table : CallTable Variable Literal Symbol} (extra : Nat),
      program.searchFrom refuted query fuel n table = some found →
        program.searchFrom refuted query (fuel + extra) n table = some found
  | 0, n, table, 0, search => search
  | 0, n, table, extra + 1, search => by
      simp only [searchFrom, Option.map_eq_some_iff] at search
      obtain ⟨derivation, derived, rfl⟩ := search
      rw [Nat.zero_add]
      simp only [searchFrom, derived]
  | fuel + 1, n, table, extra, search => by
      rw [Nat.add_right_comm]
      simp only [searchFrom] at search ⊢
      split at search
      · exact search
      · split at search
        · cases search
        · rename_i grows
          simp only [grows, ite_false]
          exact searchFrom_mono extra search

variable (program) in
/-- A P2 query passed S27's checker. -/
theorem check_of_p2 {query : Query Variable Literal Symbol} {notes : List (Note Variable Literal Symbol)}
    (classified : program.classify query = .p2 notes) : program.check query = [] := by
  cases clean : program.check query with
  | nil => rfl
  | cons blocker rest =>
      exfalso
      unfold classify classifyClosed at classified
      rw [clean] at classified
      split at classified <;> simp at classified

end Program

/-! ## The decision within the fuel -/

/-- A Yes's evidence: the relevant programs of the query's instances (P0, P1),
or a derivation the search found within the fuel, with its round (P2). -/
inductive YesEvidence (Variable Literal Symbol : Type) where
  | relevant (grounds : List (GroundProgram Variable Literal Symbol))
  | derivation (round : Nat) (derivation : Derivation Variable Literal Symbol)

/-- A No's evidence: the relevant programs (P0, P1), or S24's refutation over
a universe (P2). -/
inductive NoEvidence (Variable Literal Symbol : Type) where
  | relevant (grounds : List (GroundProgram Variable Literal Symbol))
  | refutation (space : List (Term Variable Literal Symbol))

/-- One witness of an Unknown: a model of an instance's relevant program, with
the instance's position (P0, P1), or one of S24's fixpoints, the greatest by
its post-fixpoint and the least by its closed abstract least fixpoint (P2). -/
inductive WitnessEvidence (Variable Literal Symbol : Type) where
  | assignment (witness : Nat × Assignment Variable Literal Symbol)
  | greatest (atoms : List (AAtom Variable Literal Symbol))
  | least (atoms : List (AAtom Variable Literal Symbol))

/-- The decisions within the fuel: S22's answers with each evidence. -/
abbrev Decision (Variable Literal Symbol : Type) :=
  Answer (YesEvidence Variable Literal Symbol) (NoEvidence Variable Literal Symbol) (WitnessEvidence Variable Literal Symbol)
    (Blocker Variable Literal Symbol)

/-- An exact answer as a decision. -/
def toDecision : IRAnswer Variable Literal Symbol → Decision Variable Literal Symbol
  | .yes grounds => .yes (.relevant grounds)
  | .no grounds => .no (.relevant grounds)
  | .unknown holds fails => .unknown (.assignment holds) (.assignment fails)
  | .undecided blockers => .undecided blockers

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem toDecision_sound {meaning : Meaning} {answer : IRAnswer Variable Literal Symbol} :
    (toDecision answer).Sound meaning ↔ answer.Sound meaning := by
  cases answer <;> exact Iff.rfl

namespace Program

variable (program : Program Variable Literal Symbol)

/-- The ground program of some atoms' dependency closure, when every rule of
every predicate it reaches is ground: its atoms, and its rules as heads and
ground bodies, a rule with a fixed literal false dropped. Then it is the atoms'
relevant program, whatever the rest of the KB is. None when one of those rules
has a name. -/
def groundClosure (roots : List (Goal Variable Literal Symbol)) : Option (GroundProgram Variable Literal Symbol) :=
  let symbols := program.readClosure [roots]
  let rules := program.rules.filter fun rule => symbols.contains rule.head
  if rules.all (fun rule => rule.names.isEmpty) then
    let bodies := rules.map fun rule => ((rule.head, rule.args), groundBody noNames rule.body, rule.body.all (program.fixedB noNames))
    some ⟨(bodies.flatMap fun entry => entry.1 :: entry.2.1.1 ++ entry.2.1.2.1).eraseDups,
      (bodies.filter (·.2.2)).map (fun entry => (entry.1, entry.2.1)), [], [], ([], [], []), true⟩
  else none

/-- **What P2's Yes and No assume of the KB, unsettled** (every answer
assumes a model: S24's policy, decided with the user, 2026-11-09). Nothing
when the KB-level query is P1: `kbCheck` decided it. Otherwise:

- the NAF-cycle roots whose own query is not P1, which `kbCheck` left
  unchecked, are checked together on their ground closure (`groundClosure`)
  when every rule they reach is ground: a piece with no model is the KB's
  inconsistency, named; when one of those rules has a name, they are
  unsettled, named;
- the denials, when no P1 query read them (none of the roots' own queries,
  and not the denials' own), must each be refuted by S24's refutation; the
  first that is not is unsettled, named.

Computed once per KB. Undecided is always sound, so the gate needs no proof:
it only keeps P2 from a Yes or a No the KB-level check did not cover. -/
def kbUnsettled : Option (Blocker Variable Literal Symbol) :=
  if (program.classifyClosed program.consistencyQuery).decides then none
  else
    let classified := program.cycleRoots.map fun root => (root, (program.classifyClosed (rootQuery root)).decides)
    let unchecked := (classified.filter fun entry => !entry.2).map (·.1)
    let denialBlocker : Option (Blocker Variable Literal Symbol) :=
      if classified.any (·.2) || (program.classifyClosed ⟨[], [], []⟩).decides then none
      else program.unrefutedDenial.map fun body => ⟨.site .goal, [], bodyTerm body, .consistency []⟩
    match unchecked with
    | [] => denialBlocker
    | root :: _ =>
        match program.groundClosure unchecked with
        | some ground => (inconsistencyOf (bodyTerm unchecked) ground).or denialBlocker
        | none => some ⟨.site .goal, [], root.toTerm, .consistency (unchecked.map Goal.toTerm)⟩

/-- **A P2 query within the fuel**: Unknown by S24's witnesses, with no fuel
and nothing assumed of the KB; otherwise, the KB settled (`unsettled` none),
No by S24's refutation on the goals' scope, with no fuel, then Yes by the
first derivation the search finds within the fuel, checked; otherwise
Undecided with the profile's notes, naming the growing call, the free output,
the unguarded name, or the unsplit parameter. The search runs only for a
closed query, the only kind a derivation shows. -/
def budgeted (fuel : Nat) (query : Query Variable Literal Symbol) (notes : List (Note Variable Literal Symbol))
    (unsettled : Option (Blocker Variable Literal Symbol)) : Decision Variable Literal Symbol :=
  match program.witnessesOver query with
  | some (high, low) => .unknown (.greatest high) (.least low)
  | none =>
      match unsettled with
      | some blocker => .undecided [blocker]
      | none =>
          let symbols := program.readClosure [query.goals]
          let space := program.universeIn symbols [query.formula]
          let valid := validUniverse program.constructors space
          let refuted := program.refutedIn symbols valid space (program.kleeneIn symbols space)
          if refuted query.formula then .no (.refutation space)
          else if query.parameters.isEmpty then
            match program.searchFrom refuted query fuel 0 [] with
            | some (round, derivation) =>
                if program.derivationHolds refuted query derivation then .yes (.derivation round derivation)
                else .undecided (notes.map Note.blocker)
            | none => .undecided (notes.map Note.blocker)
          else .undecided (notes.map Note.blocker)

/-- A query neither P0 nor P1: P2 within the fuel, or Undecided with the
checker's blockers. -/
def beyondP1 (fuel : Nat) (query : Query Variable Literal Symbol) : Profile Variable Literal Symbol → Decision Variable Literal Symbol
  | .p2 notes => program.budgeted fuel query notes program.kbUnsettled
  | other => .undecided other.blockers

/-- **The decision within the fuel**: Undecided when the KB-level check finds
the KB inconsistent; a query of P0 or P1 decided exactly with no fuel, as
`decideQuery` decides it; a P2 query within the fuel (`budgeted`); any other
query Undecided with the checker's blockers. The profile is read once. -/
def decideWithin (fuel : Nat) (query : Query Variable Literal Symbol) : Decision Variable Literal Symbol :=
  match program.kbCheck with
  | some blocker => .undecided [blocker]
  | none =>
      let profile := program.classify query
      if decided : profile.decides = true then toDecision (program.combine query.formula (program.instances query decided))
      else program.beyondP1 fuel query profile

/-- **A decision's certificate, checked**, on the evaluator's conditions:
P0's and P1's as `checkAnswer` checks them; a derivation by its checker and a
refutation computed again, each with the KB-level check passing and nothing
unsettled; S24's two witnesses computed again. -/
def checkDecision (query : Query Variable Literal Symbol) : Decision Variable Literal Symbol → Bool
  | .yes (.relevant grounds) => program.checkByPrograms query true grounds
  | .yes (.derivation _ derivation) =>
      program.checkDerivation query derivation && program.kbCheck.isNone && program.kbUnsettled.isNone
  | .no (.relevant grounds) => program.checkByPrograms query false grounds
  | .no (.refutation space) =>
      (program.check query).isEmpty && program.kbCheck.isNone && program.kbUnsettled.isNone &&
        let symbols := program.readClosure [query.goals]
        program.refutedIn symbols (validUniverse program.constructors space) space (program.kleeneIn symbols space) query.formula
  | .unknown (.assignment holds) (.assignment fails) => program.checkUnknown query holds fails
  | .unknown (.greatest high) (.least low) =>
      (program.check query).isEmpty &&
        match program.witnessesOver query with
        | some (found, foundLow) => decide (found = high) && decide (foundLow = low)
        | none => false
  | _ => false

section Guarantees

variable {program} [FreshNames Variable]

/-- **A P2 query's answers are sound**, whatever the KB-level gate says. -/
theorem budgeted_sound {fuel : Nat} {query : Query Variable Literal Symbol} {notes : List (Note Variable Literal Symbol)}
    {unsettled : Option (Blocker Variable Literal Symbol)} (classified : program.classify query = .p2 notes) :
    (program.budgeted fuel query notes unsettled).Sound (program.meaning query) := by
  have clean := program.check_of_p2 classified
  have wellFormed := program.wellFormed_of_check clean
  have queryOk := program.queryOk_of_check clean
  unfold budgeted
  split
  · rename_i found
    exact witnessesOver_independence wellFormed found
  · split
    · trivial
    · dsimp only
      split
      · rename_i refuted
        exact refutedIn_falsity refuted
      · split
        · split
          · split
            · rename_i checked
              exact derivationHolds_truth wellFormed (Scans.goals queryOk.goals)
                (fun models _ refuted environment => refutedIn_sound refuted (completes_of_models models) models.2.1 environment)
                checked
            · trivial
          · trivial
        · trivial

/-- **Every decision is sound**: Yes holds in every model of the completion
realizing the signature, No fails in each, Unknown holds in one and fails in
another, Undecided claims nothing. -/
theorem decideWithin_sound (fuel : Nat) (query : Query Variable Literal Symbol) :
    (program.decideWithin fuel query).Sound (program.meaning query) := by
  unfold decideWithin
  cases program.kbCheck with
  | some blocker => trivial
  | none =>
      dsimp only
      by_cases decided : (program.classify query).decides = true
      · simp only [decided, dite_true]
        have sound := decideQuery_sound (program := program) query
        simp only [decideQuery, decided, dite_true] at sound
        exact toDecision_sound.mpr sound
      · simp only [decided, Bool.false_eq_true, dite_false]
        cases classified : program.classify query with
        | p2 notes => exact budgeted_sound classified
        | p0 => trivial
        | p1 => trivial
        | undecided blockers => trivial

omit [FreshNames Variable] in
/-- **With the evidence, the P1 answer**: a query of P0 or P1 is decided
exactly, whatever the fuel. -/
theorem decideWithin_evidence {query : Query Variable Literal Symbol} (decided : (program.classify query).decides = true)
    (fuel : Nat) : program.decideWithin fuel query = toDecision (program.answer query) := by
  unfold decideWithin answer
  cases program.kbCheck with
  | some blocker => rfl
  | none => simp only [decideQuery, decided, dite_true]

omit [FreshNames Variable] in
theorem budgeted_mono {fuel fuel' : Nat} {query : Query Variable Literal Symbol} {notes : List (Note Variable Literal Symbol)}
    {unsettled : Option (Blocker Variable Literal Symbol)} (le : fuel ≤ fuel')
    (decided : (program.budgeted fuel query notes unsettled).decided = true) :
    program.budgeted fuel' query notes unsettled = program.budgeted fuel query notes unsettled := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
  unfold budgeted at decided ⊢
  cases witnesses : program.witnessesOver query with
  | some pair => rfl
  | none =>
      simp only [witnesses] at decided ⊢
      cases unsettled with
      | some blocker => rfl
      | none =>
          dsimp only at decided ⊢
          by_cases refuted : program.refutedIn (program.readClosure [query.goals])
              (validUniverse program.constructors (program.universeIn (program.readClosure [query.goals]) [query.formula]))
              (program.universeIn (program.readClosure [query.goals]) [query.formula])
              (program.kleeneIn (program.readClosure [query.goals])
                (program.universeIn (program.readClosure [query.goals]) [query.formula])) query.formula = true
          · simp only [refuted, ite_true]
          · simp only [refuted, Bool.false_eq_true, ite_false] at decided ⊢
            by_cases closed : query.parameters.isEmpty = true
            · simp only [closed, ite_true] at decided ⊢
              cases search : program.searchFrom (program.refutedIn (program.readClosure [query.goals])
                  (validUniverse program.constructors (program.universeIn (program.readClosure [query.goals]) [query.formula]))
                  (program.universeIn (program.readClosure [query.goals]) [query.formula])
                  (program.kleeneIn (program.readClosure [query.goals])
                    (program.universeIn (program.readClosure [query.goals]) [query.formula]))) query fuel 0 [] with
              | none => simp [search, Answer.decided] at decided
              | some found => rw [searchFrom_mono extra search]
            · simp only [closed, Bool.false_eq_true, ite_false] at decided
              simp [Answer.decided] at decided

omit [FreshNames Variable] in
/-- **Monotone in the fuel**: once decided, more fuel gives the same decision.
Only Undecided changes. -/
theorem decideWithin_mono {fuel fuel' : Nat} {query : Query Variable Literal Symbol} (le : fuel ≤ fuel')
    (decided : (program.decideWithin fuel query).decided = true) :
    program.decideWithin fuel' query = program.decideWithin fuel query := by
  unfold decideWithin at decided ⊢
  cases check : program.kbCheck with
  | some blocker => rfl
  | none =>
      simp only [check] at decided ⊢
      by_cases decides : (program.classify query).decides = true
      · simp only [decides, dite_true]
      · simp only [decides, Bool.false_eq_true, dite_false] at decided ⊢
        cases classified : program.classify query with
        | p2 notes =>
            simp only [classified, beyondP1] at decided ⊢
            exact budgeted_mono le decided
        | p0 => rfl
        | p1 => rfl
        | undecided blockers => rfl

/-- **A checked certificate is sound**: the decision it certifies means what
it says. -/
theorem checkDecision_sound {query : Query Variable Literal Symbol} {decision : Decision Variable Literal Symbol}
    (checked : program.checkDecision query decision = true) : decision.Sound (program.meaning query) := by
  cases decision with
  | yes evidence =>
      cases evidence with
      | relevant grounds => exact (checkByPrograms_sound checked).1 rfl
      | derivation _ derivation =>
          simp only [checkDecision, Bool.and_eq_true] at checked
          exact checkDerivation_sound checked.1.1
  | no evidence =>
      cases evidence with
      | relevant grounds => exact (checkByPrograms_sound checked).2 rfl
      | refutation space =>
          simp only [checkDecision, Bool.and_eq_true] at checked
          exact refutedIn_falsity checked.2
  | unknown holds fails =>
      cases holds <;> cases fails <;> simp only [checkDecision, Bool.false_eq_true] at checked
      · exact checkUnknown_sound checked
      · simp only [Bool.and_eq_true, List.isEmpty_iff] at checked
        obtain ⟨clean, same⟩ := checked
        split at same
        · rename_i found foundLow witnesses
          simp only [Bool.and_eq_true, decide_eq_true_eq] at same
          obtain ⟨rfl, rfl⟩ := same
          exact witnessesOver_independence (program.wellFormed_of_check clean) witnesses
        · cases same
  | undecided _ => trivial

end Guarantees

end Program

end AnthillModKbSpec.IR
