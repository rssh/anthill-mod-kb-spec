import AnthillModKbSpec.Resolution.P3.Principle
import AnthillModKbSpec.Resolution.P1.Export

/-! # Admitted induction (S12)

The induction path for a lowered guarded universal `∀x:D. p(x)` over a
declared inductive domain `D`, by its structural principle (`P3/Principle`).
`check` decides, before anything runs, whether the path is Ready:

- the goal is the lowered `∀x. G_D(x) → p(x)` over one declared domain
  (`target?`);
- `p` is registered at arity 1, so the principle's guard `P_1(p)` has its
  generated fact;
- the program carries the principle for `D`'s listed rules as a clause, found
  with its names whatever names the generator chose (`carried?`); for
  admissible names, lowering its source gives exactly that clause
  (`lower_principle`);
- neither the query's context nor a clause a case may select holds a formula
  the cases cannot run (`contextGaps`, `casesGaps`): NAF as a goal, which the
  plan's run has no route for; a range guard on a name no other goal of its
  clause mentions; and P0's other requests, apart from ground instances of
  data and range guards. The clauses are those concluding a symbol reachable
  from what the premises ask, `p` and the guard `P_1`, every head applying a
  predicate by `ho_apply` or that is a formula variable, and every denial
  (`dependencies`), so an atomic induction clause, which positive search would
  select again on every call, is reported. Each gap is a `Need`, reported
  before anything runs.

The plan's strategy is one run of the left strategy committed to the plan's
selection (`leftCommitted`): where it chooses commands, they are the only ones
offered. It chooses the principle by its whole head (`headMatch`) exactly at a
focus `G_D(e) → p(e)` (`Plan.selection_focus`), not raced against the
implication's introduction, and splits a guard assumption at a guard goal on
its term (`guardSplits`), as a case's field guards need. The principle's
premises are never such a focus, nor are their instances
(`Plan.body_unfocused`), and `positive` never selects a compound head for an
atomic goal. The run is bounded by its fuel: an interrupted run is Unknown,
never failure. Induction search is P3: failure of a case for this predicate
does not refute the universal.

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
  /-- A capability P0 names, other than a ground instance of data: an extension
  the case search lacks. -/
  | capability (capability : Admission.Capability)
  /-- NAF as a goal: the plan's run has no NAF route. -/
  | negation
  /-- A range guard on a name no other goal of its clause mentions: positive
  search delays it until a goal binds the name, and none can. -/
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
  /-- The program carries no principle for the domain: no clause whose names,
  read off it, generate it. -/
  | principle
  /-- The carried principle's names are not admissible: a case's fields not
  distinct or naming the predicate, the target naming the predicate, or a
  constructor that is `ho_apply`. -/
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

/-- The KB clauses a case may select, the principle excepted: those concluding
a symbol reachable through clause bodies from what the principle's premises
ask (`p` and the guard `P_1`) or a denial's body asks; every clause whose head
applies a predicate by `ho_apply`, which meets any call through its indirect
view (S11); every clause whose head is a formula variable, which may meet any
goal; and every denial `⊥ :- body`, which serves any `false` subgoal, as ex
falso under an assumed `false` asks. A compound head, the principle's among
them, is never selected for an atomic goal. -/
def dependencies (hoApplySymbol : Symbol) (clauses : List (Nat × HornClause Variable Literal Symbol))
    (asked : List Symbol) : List (Nat × HornClause Variable Literal Symbol) :=
  let edges := clauses.flatMap fun (_, clause) =>
    match clause with
    | .definite (.app symbol _) body => (body.flatMap goalSymbols).map (symbol, ·)
    | _ => []
  let denied := clauses.flatMap fun (_, clause) =>
    match clause with
    | .goal body => body.flatMap goalSymbols
    | _ => []
  let reached := GroundSearch.reach edges (edges.length + 1) (asked ++ denied)
  clauses.filter fun (_, clause) =>
    match clause with
    | .definite (.app symbol _) _ => decide (symbol ∈ reached) || decide (symbol = hoApplySymbol)
    | .definite (.var _) _ | .goal _ => true
    | _ => false

/-- The names a clause's goals other than its range guards mention: its head's
and its other body goals'. A range guard waits until a goal binds its name
(`waiting?`); a guard on another name has no goal to bind it and flounders. -/
def bindable (program : Machine.Program Variable Literal Symbol) (head : Term Variable Literal Symbol)
    (body : List (Term Variable Literal Symbol)) : List Variable :=
  head.freeVars ++ (body.filter fun goal => (guardSubject? program goal).isNone).flatMap Term.freeVars

/-- The formulas of a body goal the case search cannot run, beyond P0's
requests: NAF, which the plan's run has no route for, and a range guard on a
name outside `bound`. -/
def goalGaps (program : Machine.Program Variable Literal Symbol) (bound : List Variable) (site : Admission.Site) :
    List Nat → Term Variable Literal Symbol → List (CaseGap Variable Literal Symbol)
  | path, .conj left right =>
      goalGaps program bound site (path ++ [0]) left ++ goalGaps program bound site (path ++ [1]) right
  | path, .defaultNeg operand => [⟨site, path, .defaultNeg operand, .negation⟩]
  | path, goal =>
      match guardSubject? program goal with
      | some name => if name ∈ bound then [] else [⟨site, path, goal, .waitingGuard⟩]
      | none => []

/-- A range guard as lowering builds it, on any term: guard atoms `m(t)` in a
disjunction ending in `false`. -/
def guardForm (program : Machine.Program Variable Literal Symbol) : Term Variable Literal Symbol → Bool
  | .disj (.app member [_]) rest =>
      program.guard member &&
        match rest with
        | .falsity => true
        | other => guardForm program other
  | _ => false

/-- P0's requests as gaps, except ground instances of data, which a P3 search
does not need, and range guards: positive search decides a guard goal by its
atoms (S06), and the plan's selection splits a guard assumption at a guard
goal on the same term (`guardSplits`). -/
def requestGaps (program : Machine.Program Variable Literal Symbol)
    (requests : List (Admission.Request Variable Literal Symbol)) : List (CaseGap Variable Literal Symbol) :=
  (requests.filter fun request => request.capability != .groundInstance &&
      !(request.capability == .scopedProof && guardForm program request.formula)).map
    fun request => ⟨request.site, request.path, request.formula, .capability request.capability⟩

/-- The gaps of the body goals of KB clause `index`, with `bound` its bindable names. -/
def bodyGaps (program : Machine.Program Variable Literal Symbol) (bound : List Variable) (index : Nat)
    (body : List (Term Variable Literal Symbol)) : List (CaseGap Variable Literal Symbol) :=
  body.zipIdx.flatMap fun (goal, position) => goalGaps program bound (.body index position) [] goal

/-- The gaps of one clause a case may select. A denial is run as a clause for
`false`, so only its body is checked. -/
def clauseGaps (hoApplySymbol : Symbol) (program : Machine.Program Variable Literal Symbol) (guard : Symbol → Bool)
    (index : Nat) : HornClause Variable Literal Symbol → List (CaseGap Variable Literal Symbol)
  | .definite head body =>
      requestGaps program (Admission.clauseRequests hoApplySymbol guard index (.definite head body)) ++
        bodyGaps program (bindable program head body) index body
  | .goal body =>
      requestGaps program (Admission.bodyRequests hoApplySymbol index 0 body) ++
        bodyGaps program (bindable program .truth body) index body

/-- The gaps of the query's context. A guard assumption is used through
`guardSplits`; any other non-atomic assumption, NAF included, is P0's
`scopedProof` request: the plan's selection chooses no other left rule. -/
def contextGaps (hoApplySymbol : Symbol) (input : Admission.Input Domain Variable Literal Symbol) :
    List (CaseGap Variable Literal Symbol) :=
  requestGaps input.program (Admission.contextRequests hoApplySymbol 0 input.context)

/-- The gaps of the clauses the cases may select. -/
def casesGaps (hoApplySymbol : Symbol) (input : Admission.Input Domain Variable Literal Symbol)
    (target : Target Domain Variable Symbol) : List (CaseGap Variable Literal Symbol) :=
  (dependencies hoApplySymbol input.kbClauses [target.predicate, input.signature.naming.predicateSymbol 1]).flatMap
    fun pair => clauseGaps hoApplySymbol input.program input.guard pair.1 pair.2

/-- The leading guarded binders of a case, `∀y. (G(y) → …)`. -/
def caseBinders : Term Variable Literal Symbol → List Variable
  | .forallVar binder (.imp _ body) => binder :: caseBinders body
  | _ => []

/-- The names of a clause shaped as a principle: `P` and the target from its
head `G(x) → ho_apply(P, x)`, the fields from its longest case's binders. -/
def namesOf? (hoApplySymbol : Symbol) : HornClause Variable Literal Symbol → Option (Names Variable)
  | .definite (.imp _ (.app symbol [.var predicate, .var target])) body =>
      if symbol = hoApplySymbol then
        let fields := body.foldl (fun longest premise =>
          let binders := caseBinders premise
          if longest.length < binders.length then binders else longest) []
        some ⟨predicate, target, fun index => fields.getD index target⟩
      else none
  | _ => none

/-- The principle the program carries for the target's domain, with its names:
a clause whose names, read off it, generate exactly it. Any names the
generator chose are found. -/
def carried? [DecidableEq Domain] (hoApplySymbol : Symbol) (input : Admission.Input Domain Variable Literal Symbol)
    (target : Target Domain Variable Symbol) : Option (HornClause Variable Literal Symbol × Names Variable) :=
  input.program.clauses.findSome? fun entry =>
    (namesOf? hoApplySymbol entry.clause).bind fun names =>
      if entry.clause = principle hoApplySymbol input.signature.naming target.domain input.rules names then
        some (entry.clause, names)
      else none

theorem carried?_spec [DecidableEq Domain] {hoApplySymbol : Symbol} {input : Admission.Input Domain Variable Literal Symbol}
    {target : Target Domain Variable Symbol} {clause : HornClause Variable Literal Symbol} {names : Names Variable}
    (found : carried? hoApplySymbol input target = some (clause, names)) :
    clause = principle hoApplySymbol input.signature.naming target.domain input.rules names ∧
      input.program.has clause = true := by
  obtain ⟨entry, member, produced⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨read, _, produced⟩ := Option.bind_eq_some_iff.mp produced
  split at produced
  · rename_i same
    cases produced
    exact ⟨same, List.any_eq_true.mpr ⟨entry, member, decide_eq_true rfl⟩⟩
  · cases produced

/-- A Ready induction plan: the input, the target, the principle the program
carries with its names, and what admission established: the names are
admissible, so lowering the source gives the principle (`Plan.lowered`), and
neither the query's context nor a clause the cases may select has a gap. It
says nothing about whether the goal holds. -/
structure Plan (Domain Variable Literal Symbol : Type) [DecidableEq Domain] [DecidableEq Variable]
    [DecidableEq Literal] [DecidableEq Symbol] (hoApplySymbol : Symbol) where
  input : Admission.Input Domain Variable Literal Symbol
  target : Target Domain Variable Symbol
  names : Names Variable
  clause : HornClause Variable Literal Symbol
  clause_eq : clause = principle hoApplySymbol input.signature.naming target.domain input.rules names
  admissible : Admissible hoApplySymbol (rulesOf input.rules target.domain) names
  goal_eq : input.goal = target.goal input.signature.naming
  registered : input.signature.Registered target.predicate 1
  carried : input.program.has clause = true
  consistent : input.forged = []
  generated : input.unlisted = []
  context_clear : contextGaps hoApplySymbol input = []
  cases_clear : casesGaps hoApplySymbol input target = []

inductive Result (Domain Variable Literal Symbol : Type) [DecidableEq Domain] [DecidableEq Variable]
    [DecidableEq Literal] [DecidableEq Symbol] (hoApplySymbol : Symbol) where
  | ready (plan : Plan Domain Variable Literal Symbol hoApplySymbol)
  | needsEvidence (needs : List (Need Variable Literal Symbol))
  | invalid (diagnostic : Admission.Diagnostic)

/-- Admission of the induction path, before anything runs. The input's own
declarations are checked first, as P0 checks them; every other shortfall is a
`Need`. The principle and its names are found in the program. -/
def check [DecidableEq Domain] (hoApplySymbol : Symbol) (input : Admission.Input Domain Variable Literal Symbol) :
    Result Domain Variable Literal Symbol hoApplySymbol :=
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
      let registered := input.signature.registered? target.predicate 1
      let registration : List (Need Variable Literal Symbol) :=
        if registered then [] else [.registration target.predicate]
      let context := contextGaps hoApplySymbol input
      let cases := casesGaps hoApplySymbol input target
      match carrying : carried? hoApplySymbol input target with
      | none => .needsEvidence (registration ++ [.principle] ++ context.map .context ++ cases.map .clause)
      | some (clause, names) =>
          let admissible := admissible? hoApplySymbol (rulesOf input.rules target.domain) names
          if ok : registered = true ∧ admissible = true ∧ context = [] ∧ cases = [] then
            .ready ⟨input, target, names, clause, (carried?_spec carrying).1, admissible?_spec ok.2.1,
              (target?_spec found).1, (SignatureSnapshot.registered?_eq_true _ _ _).mp ok.1,
              (carried?_spec carrying).2, consistent, generated, ok.2.2.1, ok.2.2.2⟩
          else
            .needsEvidence (registration ++ (if admissible then [] else [.names]) ++ context.map .context ++
              cases.map .clause)

/-- A Ready plan is for exactly the input checked. -/
theorem check_input [DecidableEq Domain] {hoApplySymbol : Symbol} {input : Admission.Input Domain Variable Literal Symbol}
    {plan : Plan Domain Variable Literal Symbol hoApplySymbol} (ready : check hoApplySymbol input = .ready plan) :
    plan.input = input := by
  unfold check at ready
  split at ready
  · cases ready
  split at ready
  · cases ready
  split at ready
  · cases ready
  dsimp only at ready
  split at ready
  · cases ready
  split at ready
  · cases ready; rfl
  · cases ready

/-- A guard assumption to split at a guard goal on `subject`: one reading as
`m(subject) ∨ rest`, `m` a guard symbol, neither side assumed yet. -/
def splittable (program : Machine.Program Variable Literal Symbol) (subject : Term Variable Literal Symbol)
    (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    Term Variable Literal Symbol → Bool
  | .disj (.app member [term]) rest =>
      program.guard member && identical term subject &&
        !(context.any fun (_, other) => identical other (.app member [term]) || identical other rest)
  | _ => false

/-- The guard assumptions to split at a guard goal on the same term. The split
is invertible: one case adds `m(t)`, which closes the goal or its membership
subgoals, and a `false` case closes by ex falso. A case assumes each field's
guard as `m(y) ∨ false`, and a guard atom on a field needs it. -/
def guardSplits (program : Machine.Program Variable Literal Symbol) (goal : Term Variable Literal Symbol)
    (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    List (Choice Variable Literal Symbol) :=
  match goal with
  | .app symbol [subject] =>
      if program.guard symbol then
        (context.filter fun (_, read) => splittable program subject context read).map
          fun (assumption, _) => .disjCases assumption
      else []
  | _ => []

theorem guardSplits_cases {program : Machine.Program Variable Literal Symbol} {goal : Term Variable Literal Symbol}
    {context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)} {choice : Choice Variable Literal Symbol}
    (member : choice ∈ guardSplits program goal context) : ∃ assumption, choice = .disjCases assumption := by
  unfold guardSplits at member
  split at member
  · split at member
    · obtain ⟨⟨assumption, _⟩, _, rfl⟩ := List.mem_map.mp member
      exact ⟨assumption, rfl⟩
    · cases member
  · cases member

/-! ## The plan's strategy -/

namespace Plan

variable [DecidableEq Domain] {hoApplySymbol : Symbol} (plan : Plan Domain Variable Literal Symbol hoApplySymbol)

/-- The lowered principle the plan applies, as the program carries it. -/
def principle : HornClause Variable Literal Symbol := plan.clause

/-- Lowering the source with `P` at `.predicate 1` gives the principle the plan
applies: its names are admissible (`lower_principle`). -/
theorem lowered :
    elaborateClause? hoApplySymbol plan.input.signature.naming (ranges plan.target.domain plan.input.rules)
      (rangeOf plan.names) (source (Literal := Literal) hoApplySymbol plan.input.signature.naming plan.target.domain
        plan.input.rules plan.names) = some plan.principle := by
  rw [Plan.principle, plan.clause_eq]
  exact lower_principle _ _ _ _ _ plan.admissible

/-- Choose the principle by its whole head exactly at a focus `G_D(e) → p(e)`,
and split a guard assumption at a guard goal on its term (`guardSplits`). -/
def selection : Selection Variable Literal Symbol := fun _ _ goal context =>
  if focus? plan.input.signature.naming plan.target goal then [.headMatch plan.principle]
  else (guardSplits plan.input.program goal context).take 1

/-- One run of the left strategy committed to the plan's selection, from the
query: at a focus the principle is the one command, not raced against the
implication's introduction. -/
def run [FreshNames Variable] (fuel : Nat) : Outcome Variable Literal Symbol Unit Unit :=
  Machine.run (leftCommitted hoApplySymbol plan.input.program plan.selection) fuel
    (State.init () [] plan.input.context plan.input.goal)

/-- The principle is chosen only at a focus. -/
theorem selection_focus {obligation : Obligation Variable Literal Symbol} {store : Store Variable Literal Symbol}
    {goal : Term Variable Literal Symbol} {context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)}
    {clause : HornClause Variable Literal Symbol}
    (chosen : .headMatch clause ∈ plan.selection obligation store goal context) :
    focus? plan.input.signature.naming plan.target goal = true ∧ clause = plan.principle := by
  unfold selection at chosen
  split at chosen
  · rename_i focused
    simp only [List.mem_singleton, Choice.headMatch.injEq] at chosen
    exact ⟨focused, chosen⟩
  · obtain ⟨_, impossible⟩ := guardSplits_cases (List.mem_of_mem_take chosen)
    cases impossible

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
  obtain ⟨head, body, same⟩ : ∃ head body, plan.principle = .definite head body :=
    ⟨_, _, by rw [Plan.principle, plan.clause_eq]; rfl⟩
  have member := inside head body same
  rw [Plan.principle, plan.clause_eq] at same
  simp only [Induction.principle, HornClause.definite.injEq] at same
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
  have derived := leftCommitted_reconstructs (naf := naf) plan.input.program plan.selection fuel () [] plan.input.context
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
  · rw [same, Plan.principle, plan.clause_eq]
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
