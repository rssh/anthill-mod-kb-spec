import AnthillModKbSpec.Resolution.P2.Principle
import AnthillModKbSpec.Resolution.P1.Export

/-! # Admitted induction (S12)

The induction path for a lowered guarded universal `∀x:D. p(x)` over a
declared inductive domain `D`, by its structural principle (`P2/Principle`).
`check` decides, before anything runs, whether the path is Ready:

- the goal is the lowered `∀x. G_D(x) → p(x)` over one declared domain
  (`target?`);
- `p` is registered at arity 1, so the principle's guard `P_1(p)` has its
  generated fact;
- the program carries the principle for `D`'s listed rules as a clause, lowering
  its source gives exactly that clause, and the signature's generated clauses,
  which discharge its guard, are carried;
- neither the query's context nor a clause a case may select holds a formula
  the cases cannot run (`contextGaps`, `casesGaps`): NAF, which the plan's run
  has no route for; a formula variable as a goal; a range guard on a name no
  other goal of its clause mentions; and P0's other requests, apart from ground
  instances and range guards. The clauses are those concluding a symbol
  reachable from what the premises ask, `p` and the guard `P_1`, and every head
  applying a predicate by `ho_apply` (`dependencies`), so an atomic induction
  clause, which positive search would select again on every call, is reported.
  Each gap is a `Need`, reported before anything runs.

The plan's strategy is one run of the left strategy on the program. Its
selection chooses the principle by its whole head (`headMatch`) exactly at a
focus `G_D(e) → p(e)` (`Plan.selection_focus`). The principle's premises are
never such a focus, nor are their instances (`Plan.body_unfocused`), and
`positive` never selects a compound head for an atomic goal, so the principle
cannot be selected again on its own subgoals. The run is bounded by its fuel:
an interrupted run is Unknown, never failure. Induction search is P2: failure
of a case for this predicate does not refute the universal.

A successful run reconstructs `Derives` for the guarded universal
(`Plan.reconstructs`), and the universal is true in every model realizing the
signature that satisfies the program's other clauses (`Plan.sound`): the
principle's validity is `principle_valid`, a theorem, not a registry fact. The
proof exports as S08 nodes: the clause node of the principle with its explicit
instantiation, converted, its guards, and one scoped subtree per case. The
checker decides an exported tree per run; that every successful run exports an
accepted tree is S15/S16's. The universal itself has no P0 plan
(`Plan.not_p0`). -/

namespace AnthillModKbSpec.Induction

open Machine Semantics InductiveDomains AdmissionSignature Elaboration

variable {Domain Variable Literal Symbol : Type}

/-- A lowered guarded universal over one domain, `∀x:D. p(x)`. -/
structure Target (Domain Variable Symbol : Type) where
  binder : Variable
  domain : Domain
  predicate : Symbol
  deriving Repr

section Goals

variable [DecidableEq Variable]

/-- The lowered goal `∀x. G_D(x) → p(x)`. -/
def Target.goal (naming : Naming Domain Symbol) (target : Target Domain Variable Symbol) :
    Formula Variable Literal Symbol :=
  forallRange naming (.data [target.domain]) target.binder (.app target.predicate [.var target.binder])

variable [DecidableEq Literal] [DecidableEq Symbol]

/-- The target of a lowered guarded universal over one of `domains`. -/
def target? (naming : Naming Domain Symbol) (domains : List Domain) :
    Formula Variable Literal Symbol → Option (Target Domain Variable Symbol)
  | .forallVar binder (.imp guarded (.app predicate [.var argument])) =>
      if argument = binder then
        (domains.find? fun domain => identical guarded (rangeGuard naming (.data [domain]) (.var binder))).map
          fun domain => ⟨binder, domain, predicate⟩
      else none
  | _ => none

theorem target?_spec {naming : Naming Domain Symbol} {domains : List Domain} {goal : Formula Variable Literal Symbol}
    {target : Target Domain Variable Symbol} (found : target? naming domains goal = some target) :
    goal = target.goal naming ∧ target.domain ∈ domains := by
  unfold target? at found
  split at found
  · rename_i binder guarded predicate argument
    split at found
    · rename_i same
      subst same
      simp only [Option.map_eq_some_iff] at found
      obtain ⟨domain, located, rfl⟩ := found
      have guardEq := identical_eq _ _
        (List.find?_some (p := fun domain => identical guarded (rangeGuard naming (.data [domain]) (.var argument)))
          located)
      exact ⟨by rw [guardEq]; rfl, List.mem_of_find?_eq_some located⟩
    · cases found
  · cases found

/-- The focus the principle is chosen at: `G_D(e) → p(e)` for a name `e`. -/
def focus? (naming : Naming Domain Symbol) (target : Target Domain Variable Symbol) :
    Term Variable Literal Symbol → Bool
  | .imp guarded (.app symbol [.var name]) =>
      decide (symbol = target.predicate) && identical guarded (rangeGuard naming (.data [target.domain]) (.var name))
  | _ => false

end Goals

/-! ## Admission -/

/-- What a case's search lacks at a formula. -/
inductive Missing where
  /-- A capability P0 names, other than a ground instance: an extension the
  case search lacks. -/
  | capability (capability : Admission.Capability)
  /-- NAF: the plan's run has no NAF route. -/
  | negation
  /-- A formula variable as a goal: it waits on its binding and flounders. -/
  | goalVariable
  /-- A range guard on a name its clause's head does not bind: it waits on the
  name and flounders. -/
  | waitingGuard
  deriving DecidableEq, Repr

/-- One formula a case's search cannot run, at its site and path. -/
structure CaseGap (Variable Literal Symbol : Type) where
  site : Admission.Site
  path : List Nat
  formula : Term Variable Literal Symbol
  missing : Missing

/-- What the induction path needs before it is Ready. -/
inductive Need (Variable Literal Symbol : Type) where
  /-- The goal is not a lowered guarded universal `∀x:D. p(x)` over one declared domain. -/
  | shape
  /-- The predicate is not registered at arity 1: the principle's guard has no generated fact. -/
  | registration (predicate : Symbol)
  /-- The program does not carry the lowered principle, or lowering its source
  does not give it. -/
  | principle
  /-- The principle's names are not admissible: a case's fields not distinct or
  naming the predicate, the target naming the predicate, or a constructor that
  is `ho_apply`. -/
  | names
  /-- The query's context holds a formula the cases cannot use. -/
  | context (gap : CaseGap Variable Literal Symbol)
  /-- A clause a case may select, the base cases and the others alike, holds a
  formula the cases cannot run. -/
  | clause (gap : CaseGap Variable Literal Symbol)

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

attribute [local instance] termEq clauseEq

/-- The predicate symbols a goal formula asks for, outside data. -/
def goalSymbols : Term Variable Literal Symbol → List Symbol
  | .app symbol _ => [symbol]
  | .conj left right | .disj left right | .imp left right => goalSymbols left ++ goalSymbols right
  | .defaultNeg body | .forallVar _ body | .existsVar _ body => goalSymbols body
  | _ => []

/-- The symbol a clause concludes, for an atomic head. -/
def headSymbol? : HornClause Variable Literal Symbol → Option Symbol
  | .definite (.app symbol _) _ => some symbol
  | _ => none

/-- The KB clauses a case may select, the principle excepted: those concluding
a symbol reachable through clause bodies from what the principle's premises ask
(`p` and the guard `P_1`), and every clause whose head applies a predicate by
`ho_apply`, which meets any call through its indirect view (S11). -/
def dependencies (hoApplySymbol : Symbol) (clauses : List (Nat × HornClause Variable Literal Symbol))
    (asked : List Symbol) : List (Nat × HornClause Variable Literal Symbol) :=
  let edges := clauses.flatMap fun (_, clause) =>
    match clause, headSymbol? clause with
    | .definite _ body, some symbol => (body.flatMap goalSymbols).map (symbol, ·)
    | _, _ => []
  let reached := GroundSearch.reach edges (edges.length + 1) asked
  clauses.filter fun (_, clause) =>
    match headSymbol? clause with
    | some symbol => decide (symbol ∈ reached) || decide (symbol = hoApplySymbol)
    | none => false

/-- The names a clause's goals other than its range guards mention: its head's
and its other body goals'. A range guard waits until a goal binds its name
(`waiting?`); a guard on another name has no goal to bind it and flounders. -/
def bindable (program : Machine.Program Variable Literal Symbol) (head : Term Variable Literal Symbol)
    (body : List (Term Variable Literal Symbol)) : List Variable :=
  head.freeVars ++ (body.filter fun goal => (guardSubject? program goal).isNone).flatMap Term.freeVars

/-- The formulas of a body goal the case search cannot run: NAF, which the
plan's run has no route for; a formula variable; and a range guard on a name
outside `bound`. The rest is P0's to report. -/
def goalGaps (program : Machine.Program Variable Literal Symbol) (bound : List Variable) (site : Admission.Site) :
    List Nat → Term Variable Literal Symbol → List (CaseGap Variable Literal Symbol)
  | path, .conj left right =>
      goalGaps program bound site (path ++ [0]) left ++ goalGaps program bound site (path ++ [1]) right
  | path, .defaultNeg operand => [⟨site, path, .defaultNeg operand, .negation⟩]
  | path, .var name => [⟨site, path, .var name, .goalVariable⟩]
  | path, goal =>
      match guardSubject? program goal with
      | some name => if name ∈ bound then [] else [⟨site, path, goal, .waitingGuard⟩]
      | none => []

/-- P0's requests as gaps, except ground instances, which a P2 search does not
need, and range guards, which positive search decides by their atoms (S06). -/
def requestGaps (program : Machine.Program Variable Literal Symbol)
    (requests : List (Admission.Request Variable Literal Symbol)) : List (CaseGap Variable Literal Symbol) :=
  (requests.filter fun request => request.capability != .groundInstance &&
      !(request.capability == .scopedProof && (guardSubject? program request.formula).isSome)).map
    fun request => ⟨request.site, request.path, request.formula, .capability request.capability⟩

/-- The gaps of one clause a case may select. -/
def clauseGaps (hoApplySymbol : Symbol) (program : Machine.Program Variable Literal Symbol) (guard : Symbol → Bool)
    (index : Nat) (clause : HornClause Variable Literal Symbol) : List (CaseGap Variable Literal Symbol) :=
  requestGaps program (Admission.clauseRequests hoApplySymbol guard index clause) ++
    match clause with
    | .definite head body =>
        body.zipIdx.flatMap fun (goal, position) =>
          goalGaps program (bindable program head body) (.body index position) [] goal
    | .goal body =>
        body.zipIdx.flatMap fun (goal, position) =>
          goalGaps program (bindable program .truth body) (.body index position) [] goal

/-- The gaps of the query's context. -/
def contextGaps (hoApplySymbol : Symbol) (input : Admission.Input Domain Variable Literal Symbol) :
    List (CaseGap Variable Literal Symbol) :=
  requestGaps input.program (Admission.contextRequests hoApplySymbol 0 input.context)

/-- The gaps of the clauses the cases may select, the principle excepted. -/
def casesGaps (hoApplySymbol : Symbol) (input : Admission.Input Domain Variable Literal Symbol)
    (target : Target Domain Variable Symbol) (clause : HornClause Variable Literal Symbol) :
    List (CaseGap Variable Literal Symbol) :=
  (dependencies hoApplySymbol (input.kbClauses.filter fun pair => !decide (pair.2 = clause))
      [target.predicate, input.signature.naming.predicateSymbol 1]).flatMap fun pair =>
    clauseGaps hoApplySymbol input.program input.guard pair.1 pair.2

/-- A Ready induction plan: the input, the target, the principle's names, the
lowered principle the program carries, and what admission established: lowering
the source gives it, the signature's generated clauses are carried, and
neither the query's context nor a clause the cases may select has a gap. It
says nothing about whether the goal holds. -/
structure Plan (Domain Variable Literal Symbol : Type) [DecidableEq Domain] [DecidableEq Variable]
    [DecidableEq Literal] [DecidableEq Symbol] (hoApplySymbol : Symbol) where
  input : Admission.Input Domain Variable Literal Symbol
  names : Names Variable
  target : Target Domain Variable Symbol
  admissible : Admissible hoApplySymbol (rulesOf input.rules target.domain) names
  goal_eq : input.goal = target.goal input.signature.naming
  registered : input.signature.Registered target.predicate 1
  lowered : elaborateClause? hoApplySymbol input.signature.naming (ranges target.domain input.rules) (rangeOf names)
    (source (Literal := Literal) hoApplySymbol input.signature.naming target.domain input.rules names) =
    some (principle hoApplySymbol input.signature.naming target.domain input.rules names)
  carried : input.program.has (principle hoApplySymbol input.signature.naming target.domain input.rules names) = true
  consistent : input.forged = []
  generated : input.unlisted = []
  context_clear : contextGaps hoApplySymbol input = []
  cases_clear : casesGaps hoApplySymbol input target
    (principle hoApplySymbol input.signature.naming target.domain input.rules names) = []

inductive Result (Domain Variable Literal Symbol : Type) [DecidableEq Domain] [DecidableEq Variable]
    [DecidableEq Literal] [DecidableEq Symbol] (hoApplySymbol : Symbol) where
  | ready (plan : Plan Domain Variable Literal Symbol hoApplySymbol)
  | needsEvidence (needs : List (Need Variable Literal Symbol))
  | invalid (diagnostic : Admission.Diagnostic)

/-- Admission of the induction path, before anything runs. The input's own
declarations are checked first, as P0 checks them; every other shortfall is a
`Need`. -/
def check [DecidableEq Domain] (hoApplySymbol : Symbol) (input : Admission.Input Domain Variable Literal Symbol)
    (names : Names Variable) : Result Domain Variable Literal Symbol hoApplySymbol :=
  match consistent : input.forged with
  | position :: _ => .invalid (.signatureClause position)
  | [] =>
  match generated : input.unlisted with
  | clause :: _ =>
      .invalid (.missingSignatureClause ((signatureClauses input.signature input.names input.rules).idxOf clause))
  | [] =>
  match found : target? input.signature.naming input.signature.signature.data.domains input.goal with
  | none => .needsEvidence [.shape]
  | some target =>
      let clause := principle hoApplySymbol input.signature.naming target.domain input.rules names
      let registered := input.signature.registered? target.predicate 1
      let lowers := decide (elaborateClause? hoApplySymbol input.signature.naming (ranges target.domain input.rules)
        (rangeOf names) (source hoApplySymbol input.signature.naming target.domain input.rules names) = some clause)
      let carried := input.program.has clause
      let admissible := admissible? hoApplySymbol (rulesOf input.rules target.domain) names
      let context := contextGaps hoApplySymbol input
      let cases := casesGaps hoApplySymbol input target clause
      if ok : registered = true ∧ lowers = true ∧ carried = true ∧ admissible = true ∧ context = [] ∧ cases = [] then
        .ready ⟨input, names, target, admissible?_spec ok.2.2.2.1, (target?_spec found).1,
          (SignatureSnapshot.registered?_eq_true _ _ _).mp ok.1, of_decide_eq_true ok.2.1, ok.2.2.1, consistent,
          generated, ok.2.2.2.2.1, ok.2.2.2.2.2⟩
      else
        .needsEvidence ((if registered then [] else [.registration target.predicate]) ++
          (if lowers && carried then [] else [.principle]) ++ (if admissible then [] else [.names]) ++
          context.map .context ++ cases.map .clause)

/-- A Ready plan is for exactly the input checked. -/
theorem check_input [DecidableEq Domain] {hoApplySymbol : Symbol} {input : Admission.Input Domain Variable Literal Symbol}
    {names : Names Variable} {plan : Plan Domain Variable Literal Symbol hoApplySymbol}
    (ready : check hoApplySymbol input names = .ready plan) : plan.input = input ∧ plan.names = names := by
  unfold check at ready
  split at ready
  · cases ready
  split at ready
  · cases ready
  split at ready
  · cases ready
  dsimp only at ready
  split at ready
  · cases ready; exact ⟨rfl, rfl⟩
  · cases ready

/-! ## The plan's strategy -/

namespace Plan

variable [DecidableEq Domain] {hoApplySymbol : Symbol} (plan : Plan Domain Variable Literal Symbol hoApplySymbol)

/-- The lowered principle the plan applies. -/
def principle : HornClause Variable Literal Symbol :=
  Induction.principle hoApplySymbol plan.input.signature.naming plan.target.domain plan.input.rules plan.names

/-- Choose the principle by its whole head exactly at a focus `G_D(e) → p(e)`. -/
def selection : Selection Variable Literal Symbol := fun _ _ goal _ =>
  if focus? plan.input.signature.naming plan.target goal then [.headMatch plan.principle] else []

/-- One run of the left strategy with the plan's selection, from the query. -/
def run [FreshNames Variable] (fuel : Nat) : Outcome Variable Literal Symbol Unit Unit :=
  Machine.run (left hoApplySymbol plan.input.program plan.selection) fuel
    (State.init () [] plan.input.context plan.input.goal)

theorem selection_focus {obligation : Obligation Variable Literal Symbol} {store : Store Variable Literal Symbol}
    {goal : Term Variable Literal Symbol} {context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)}
    {choice : Choice Variable Literal Symbol} (chosen : choice ∈ plan.selection obligation store goal context) :
    focus? plan.input.signature.naming plan.target goal = true ∧ choice = .headMatch plan.principle := by
  unfold selection at chosen
  split at chosen
  · rename_i focused
    simp only [List.mem_singleton] at chosen
    exact ⟨focused, chosen⟩
  · cases chosen

omit [DecidableEq Domain] in
private theorem not_focus_of {naming : Naming Domain Symbol} {target : Target Domain Variable Symbol}
    {term : Term Variable Literal Symbol} (notImp : ∀ premise conclusion, term ≠ .imp premise conclusion) :
    focus? naming target term = false := by
  cases term <;> first | rfl | exact absurd rfl (notImp _ _)

/-- No premise of the principle, under any substitution, is a focus: its
guards are atoms or truth, a case without fields an atom, any other case a
universal. So the selection does not choose the principle at one of its own
premises. Goals a case opens are not covered here; a clause a case selects
may ask a focus again, a nested induction. -/
theorem body_unfocused [FreshNames Variable] {premise : Term Variable Literal Symbol}
    (inside : ∀ head body, plan.principle = .definite head body → premise ∈ body)
    (σ : Substitution Variable Literal Symbol) :
    focus? plan.input.signature.naming plan.target (premise.instantiate σ) = false := by
  obtain ⟨head, body, same⟩ : ∃ head body, plan.principle = .definite head body := ⟨_, _, rfl⟩
  have member := inside head body same
  simp only [Plan.principle, Induction.principle, HornClause.definite.injEq] at same
  obtain ⟨_, rfl⟩ := same
  apply not_focus_of
  intro premiseTerm conclusion equal
  simp only [List.mem_append, clauseGuards, List.mem_map] at member
  rcases member with ⟨name, _, rfl⟩ | ⟨rule, _, rfl⟩
  · unfold rangeOf at equal
    split at equal <;> simp [rangeGuard, Term.instantiate] at equal
  · cases fields : rule.fields with
    | nil => simp [fields, guardFields, matrix, hypotheses, applied, Term.hoApply, Term.instantiate] at equal
    | cons _ _ => simp [fields, guardFields, forallRange, Term.instantiate] at equal

/-! ## What a successful run establishes -/

variable [FreshNames Variable]

omit [DecidableEq Domain] [DecidableEq Literal] [DecidableEq Symbol] in
/-- The lowered goal is closed, so every store reads it as it is. -/
theorem goal_closed {naming : Naming Domain Symbol} (target : Target Domain Variable Symbol)
    (store : Store Variable Literal Symbol) :
    store.resolve (target.goal (Literal := Literal) naming) = target.goal naming := by
  apply resolveWith_unbound
  intro name member
  simp [Target.goal, forallRange, rangeGuard, InductiveDomains.guard, Term.freeVars] at member

/-- A successful run reconstructs `Derives` for the guarded universal, under
the query's context read through the final answers. -/
theorem reconstructs {fuel : Nat} {proof : CompletedProof Variable Literal Symbol Unit Unit}
    {resume : State Variable Literal Symbol Unit Unit} (ran : plan.run fuel = .success proof resume)
    (naf : NafFailure Variable Literal Symbol) :
    Derives hoApplySymbol plan.input.program.kb (plan.input.context.map proof.store.resolve)
      (plan.target.goal plan.input.signature.naming) naf := by
  have derived := left_reconstructs (naf := naf) plan.input.program plan.selection fuel () [] plan.input.context
    plan.input.goal ran
  rwa [plan.goal_eq, goal_closed] at derived

omit [FreshNames Variable] in
/-- The program's KB is valid in a model realizing the signature once its
clauses other than the principle are: the principle is valid by
`principle_valid`, from the domain's exact realization. -/
theorem models {Value : Type} {model : Model Literal Symbol Value hoApplySymbol}
    (realizes : AdmissionSignature.Realizes plan.input.signature model)
    (others : ∀ clause ∈ plan.input.program.kb, clause ≠ plan.principle →
      ∀ environment : Environment Variable Value, model.Satisfies environment clause.toFormula) :
    model.Models plan.input.program.kb := by
  intro clause member environment
  by_cases same : clause = plan.principle
  · subst same
    exact principle_valid plan.input.signature model realizes plan.input.complete plan.admissible environment
  · exact others clause member same environment

/-- A successful run makes the guarded universal true in every model realizing
the signature and satisfying the program's other clauses, under every
environment satisfying the query's context. -/
theorem sound {Value : Type} {model : Model Literal Symbol Value hoApplySymbol}
    (realizes : AdmissionSignature.Realizes plan.input.signature model)
    (others : ∀ clause ∈ plan.input.program.kb, clause ≠ plan.principle →
      ∀ environment : Environment Variable Value, model.Satisfies environment clause.toFormula)
    {fuel : Nat} {proof : CompletedProof Variable Literal Symbol Unit Unit}
    {resume : State Variable Literal Symbol Unit Unit} (ran : plan.run fuel = .success proof resume) :
    ∀ environment, model.ContextHolds environment (plan.input.context.map proof.store.resolve) →
      model.Satisfies environment (plan.target.goal plan.input.signature.naming) :=
  model.sound (plan.models realizes others) (model.disabled_adequate _) (plan.reconstructs ran NafFailure.disabled)

omit [FreshNames Variable] in
/-- The universal has no P0 plan: P0 asks scoped-proof evidence for it. The
induction proof is nonetheless checked by S08's rules. -/
theorem not_p0 (other : Admission.Plan Domain Variable Literal Symbol hoApplySymbol) :
    Admission.check hoApplySymbol plan.input ≠ .ready other := by
  have asked : plan.input.requests hoApplySymbol ≠ [] := by
    simp [Admission.Input.requests, plan.goal_eq, Target.goal, forallRange, Admission.goalRequests]
  unfold Admission.check
  split
  · intro same; cases same
  · split
    · intro same; cases same
    · split
      · intro same; cases same
      · rename_i noRequests; exact absurd noRequests asked

end Plan

end AnthillModKbSpec.Induction
