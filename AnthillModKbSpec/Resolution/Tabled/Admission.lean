import AnthillModKbSpec.Resolution.Tabled.Fragment

/-! # The fast fragment's admission: profiles, cost classes, blockers (S23)

Before anything runs, every predicate of a KB program is classified for
S24's tabled evaluation ([fast evaluation](../../../docs/fast-decision-routes.md)):

- **Blockers.** A construct outside the fragment, a predicate without a mode,
  or a safety violation is an Undecided blocker (S22) at its site and path.
- **Cost class.** A predicate is *complete* when every recursive call's inputs
  are data terms and its component either gives data-term outputs (`path`
  over facts: its answers are data terms) or decreases on every recursive
  call (`append`, `reachable`: no call repeats). Otherwise it is *budgeted*,
  with notes naming the growing call or answer. Decided with the user,
  2026-11-07: a call bound alone does not bound the answers
  (`count(x, succ(Y)) :- count(x, Y)` makes one call and has infinitely many
  answers), so `count(+, −)` is budgeted.
- **Profile.** P1 for a complete predicate with no NAF or denial over a
  predicate on a cycle, no generic universal goal, and no undecided
  hypothesis; P2 for the rest of the fragment, with its notes; Undecided
  with blockers otherwise.
- **Locality.** A predicate's class follows from its own clauses, the denials
  over it, and the classes of the predicates it calls (`mem_blockers`,
  `mem_notes`, `complete_iff`); a query's from the predicates it uses.

The degree of a complete predicate is the most free names a clause joins in
its dependency closure; over n data terms its clauses have at most nᵏ
instances. Determinism is reported for non-overlapping input patterns
(`deterministic_unique`). -/

namespace AnthillModKbSpec.Tabled

open Admission Answers

variable {Variable Literal Symbol : Type}

namespace Program

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] (program : Program Variable Literal Symbol)

/-! ## The dependency graph -/

/-- A head defining a predicate: an atom of a symbol that is not `ho_apply`,
a guard, or a marker. -/
def headOf? : Term Variable Literal Symbol → Option (Symbol × List (Term Variable Literal Symbol))
  | .app symbol args =>
      if symbol = program.hoApply ∨ program.guard symbol = true ∨ program.marker symbol = true then none
      else some (symbol, args)
  | _ => none

/-- The defining clauses of a predicate: index, head arguments, and body. -/
def definitions (predicate : Symbol) :
    List (Nat × List (Term Variable Literal Symbol) × List (Term Variable Literal Symbol)) :=
  program.clauses.filterMap fun (index, clause) =>
    match clause with
    | .definite head body =>
        match program.headOf? head with
        | some (symbol, args) => if symbol = predicate then some (index, args, body) else none
        | none => none
    | .goal _ => none

/-- The denials, `⊥ :- body` or `false :- body`, with their indices. -/
def denials : List (Nat × List (Term Variable Literal Symbol)) :=
  program.clauses.filterMap fun (index, clause) =>
    match clause with
    | .goal body | .definite .falsity body => some (index, body)
    | .definite _ _ => none

/-- The predicates the KB clauses define. -/
def heads : List Symbol :=
  program.clauses.filterMap fun (_, clause) =>
    match clause with
    | .definite head _ => (program.headOf? head).map Prod.fst
    | .goal _ => none

/-- An edge from each defined predicate to every predicate its bodies may call. -/
def edges : List (Symbol × Symbol) :=
  program.clauses.flatMap fun (_, clause) =>
    match clause with
    | .definite head body =>
        match program.headOf? head with
        | some (symbol, _) => (body.flatMap program.calls).map (symbol, ·)
        | none => []
    | .goal _ => []

/-- The predicates of the graph. -/
def vertices : List Symbol := (program.heads ++ program.edges.flatMap fun edge => [edge.1, edge.2]).eraseDups

/-- The predicates a predicate reaches along at least one edge. -/
def reach (predicate : Symbol) : List Symbol := Tabled.reach program.edges program.vertices predicate

/-- A predicate on a cycle of the dependency graph. -/
def cyclic (predicate : Symbol) : Bool := (program.reach predicate).contains predicate

/-- A call is recursive when its callee reaches its caller. -/
def recursive (caller callee : Symbol) : Bool := (program.reach callee).contains caller

/-- The predicates of a predicate's strongly connected component. -/
def component (predicate : Symbol) : List Symbol :=
  predicate :: (program.reach predicate).filter fun other => program.recursive predicate other

/-- A predicate with what it reaches: its dependency closure, each once. -/
def closure (predicate : Symbol) : List Symbol := predicate :: (program.reach predicate).filter (· != predicate)

/-! ## Data-term outputs and call sites -/

/-- The analysis frame of a defining clause: its head inputs. -/
def frameOf (predicate : Symbol) (args : List (Term Variable Literal Symbol)) : Option (Frame Variable Literal Symbol) :=
  (program.io? predicate args).map fun io => ⟨io.1, []⟩

/-- A defining clause gives data-term outputs, given which predicates do: every
head output is a data term at the end of the body. A clause without a mode at
its arity is a blocker and gives nothing here. -/
def clauseOutputs (info : Symbol → Bool) (predicate : Symbol) (args body : List (Term Variable Literal Symbol)) : Bool :=
  match program.io? predicate args with
  | some (inputs, outputs) =>
      let frame : Frame Variable Literal Symbol := ⟨inputs, []⟩
      outputs.all (frame.small (program.flowBody info frame [] body))
  | none => true

/-- Every defining clause gives data-term outputs, given the set of predicates that do. -/
def outputsOk (set : List Symbol) (predicate : Symbol) : Bool :=
  (program.definitions predicate).all fun clause => program.clauseOutputs (set.contains ·) predicate clause.2.1 clause.2.2

/-- The predicates with data-term outputs: the greatest post-fixpoint. -/
def dataOutputs : List Symbol := greatest program.outputsOk program.vertices

def dataInfo (predicate : Symbol) : Bool := program.dataOutputs.contains predicate

/-- The call sites of a predicate's defining clauses. -/
def callSites (predicate : Symbol) : List (Site × CallSite Variable Literal Symbol) :=
  (program.definitions predicate).flatMap fun (index, args, body) =>
    match program.frameOf predicate args with
    | some frame => program.sitesBody program.dataInfo frame index 0 [] body
    | none => []

/-- The recursive call sites of a predicate. -/
def recursiveSites (predicate : Symbol) : List (Site × CallSite Variable Literal Symbol) :=
  (program.callSites predicate).filter fun pair => program.recursive predicate pair.2.callee

/-- A component whose answers stay finite: every member gives data-term
outputs, or every recursive call in it decreases. -/
def settles (predicate : Symbol) : Bool :=
  (program.component predicate).all program.dataInfo ||
    (program.component predicate).all fun member => (program.recursiveSites member).all (·.2.decreasing)

/-! ## Scanning clauses -/

/-- What a defining clause gives: its head's data blockers or mode blocker,
the scan of its body from the head's input names, the guards still waiting
at its end, and the head outputs not bound by then. -/
def clauseFound (predicate : Symbol) (index : Nat) (args body : List (Term Variable Literal Symbol)) :
    Found Variable Literal Symbol :=
  let head := Term.app predicate args
  match program.modes predicate with
  | some modes =>
      if modes.length = args.length then
        let inputs := select .input modes args
        let scanned := program.scanBody index [] 0 (inputs.flatMap Term.freeVars) body
        let unbound := (args.zipIdx.zip modes).filterMap fun ((arg, position), mode) =>
          if mode = .output && !available [] scanned.bound arg.freeVars then some (blocker (.head index) [position] arg .mode)
          else none
        .ofBlockers (program.argsBlockers (.head index) [] 0 args) ++ scanned.found ++ .ofBlockers (scanned.close [] ++ unbound)
      else .ofBlockers [blocker (.head index) [] head .mode]
  | none => .ofBlockers [blocker (.head index) [] head .mode]

/-- What a denial gives: the scan of its body from no bound name. -/
def denialFound (index : Nat) (body : List (Term Variable Literal Symbol)) : Found Variable Literal Symbol :=
  let scanned := program.scanBody index [] 0 [] body
  scanned.found ++ .ofBlockers (scanned.close [])

/-- The capability of a head that may conclude any predicate. -/
def openCapability : Term Variable Literal Symbol → Capability
  | .var _ => .formulaVariable
  | .app _ _ => .hoApplyConversion
  | _ => .compoundHead

/-- Blockers that hold for every predicate: a head that may conclude any
predicate (a formula variable, or `ho_apply` of a predicate variable), as the
completion closes none then (`Completion.headOpens`); a KB clause concluding
a guard atom or an open marker; a head that is no formula (a literal, a
dictionary call). -/
def globalBlockers : List (Blocker Variable Literal Symbol) :=
  program.clauses.flatMap fun (index, clause) =>
    match clause with
    | .definite head _ =>
        match head with
        | .app symbol args =>
            if symbol = program.hoApply then
              match Completion.headOpens program.hoApply head with
              | none => [outside (.head index) [] head .hoApplyConversion]
              | some _ => []
            else if program.guard symbol then [outside (.head index) [] (.app symbol args) .guardDefinition]
            else if program.marker symbol then [blocker (.head index) [] (.app symbol args) (.construct .markerDefinition)]
            else []
        | .equal _ _ => []
        | .lit value => [outside (.head index) [] (.lit value) .termKind]
        | .dictionaryCall dictionary selectors operation args =>
            [outside (.head index) [] (.dictionaryCall dictionary selectors operation args) .dictionaryLaw]
        | _ =>
            match Completion.headOpens program.hoApply head with
            | none => [outside (.head index) [] head (openCapability head)]
            | some _ => []
    | .goal _ => []

/-- Blockers of the non-atomic heads that may conclude a predicate (an S09
compound head, a concrete `ho_apply` head): the completion leaves it open. -/
def openedBlockers (predicate : Symbol) : List (Blocker Variable Literal Symbol) :=
  program.clauses.flatMap fun (index, clause) =>
    match clause with
    | .definite head _ =>
        match head with
        | .equal _ _ => []
        | _ =>
            match program.headOf? head with
            | some _ => []
            | none =>
                match Completion.headOpens program.hoApply head with
                | some opened =>
                    if opened.contains predicate then [outside (.head index) [] head (openCapability head)] else []
                | none => []
    | .goal _ => []

/-- KB clauses that conclude no predicate: equations, kept as statements (S08,
S20). They block no predicate here: a defined operation is blocked where it
occurs in data. -/
def statements : List (Blocker Variable Literal Symbol) :=
  program.clauses.flatMap fun (index, clause) =>
    match clause with
    | .definite (.equal left right) _ => [outside (.head index) [] (.equal left right) .equality]
    | _ => []

/-- The predicates a denial constrains: those its body calls and what they reach. -/
def denialScope (body : List (Term Variable Literal Symbol)) : List Symbol :=
  (body.flatMap program.calls).flatMap program.closure

/-- A denial over a predicate on a cycle. -/
def denialCyclic (body : List (Term Variable Literal Symbol)) : Bool :=
  (program.denialScope body).any program.cyclic

/-- What the defining clauses of a predicate give. -/
def found (predicate : Symbol) : Found Variable Literal Symbol :=
  (program.definitions predicate).foldr (fun (index, args, body) rest => program.clauseFound predicate index args body ++ rest) .empty

/-! ## Local classes -/

/-- A predicate's own part of the complete class: its recursive calls have
data-term inputs, its component settles, and it has no undecided hypothesis. -/
def localComplete (predicate : Symbol) : Bool :=
  (program.recursiveSites predicate).all (·.2.small) && program.settles predicate &&
    (program.found predicate).notes.all fun note => note.reason != .hypothesis

/-- Complete: every predicate of the dependency closure is locally complete. -/
def complete (predicate : Symbol) : Bool := (program.closure predicate).all program.localComplete

/-- A predicate whose operand may call is on a cycle, or reaches one. -/
def reachesCycle (callees : List Symbol) : Bool := (callees.flatMap program.closure).any program.cyclic

/-- The notes on term growth at a predicate's own clauses: its recursive calls
whose inputs are not data terms, and, when its component does not settle, its
head outputs that are not data terms. -/
def growthNotes (predicate : Symbol) : List (Note Variable Literal Symbol) :=
  ((program.recursiveSites predicate).filter (!·.2.small)).map (fun (site, call) => ⟨site, call.path, call.formula, .growingCall⟩) ++
    if program.settles predicate then []
    else (program.definitions predicate).flatMap fun (index, args, body) =>
      match program.modes predicate with
      | some modes =>
          if modes.length = args.length then
            let frame : Frame Variable Literal Symbol := ⟨select .input modes args, []⟩
            let small := program.flowBody program.dataInfo frame [] body
            (args.zipIdx.zip modes).filterMap fun ((arg, position), mode) =>
              if mode = .output && !frame.small small arg then some ⟨.head index, [position], arg, .growingAnswer⟩ else none
          else []
      | none => []

/-- The notes of NAF goals: over a predicate on a cycle. -/
def negationNotes (negations : List (Negation Variable Literal Symbol)) : List (Note Variable Literal Symbol) :=
  negations.filterMap fun negation =>
    if program.reachesCycle negation.callees then some ⟨negation.site, negation.path, negation.formula, .cyclicNegation⟩
    else none

/-- The blockers of NAF goals needing constructive negation whose operand is
not complete: its answers may be infinite. -/
def negationBlockers (negations : List (Negation Variable Literal Symbol)) : List (Blocker Variable Literal Symbol) :=
  negations.filterMap fun negation =>
    if negation.constructive && !negation.callees.all program.complete then
      some (blocker negation.site negation.path negation.formula .termination)
    else none

/-- The denials over some of the predicates: those whose scope meets them. -/
def denialsOver (members : List Symbol) : List (Nat × List (Term Variable Literal Symbol)) :=
  program.denials.filter fun denial => (program.denialScope denial.2).any members.contains

/-- A denial's blockers: its own scan's and its NAF goals'. -/
def denialBlockers (index : Nat) (body : List (Term Variable Literal Symbol)) : List (Blocker Variable Literal Symbol) :=
  let found := program.denialFound index body
  found.blockers ++ program.negationBlockers found.negations

/-- A denial's notes: its own scan's, its NAF goals', and whether it is over a
predicate on a cycle. -/
def denialNotes (index : Nat) (body : List (Term Variable Literal Symbol)) : List (Note Variable Literal Symbol) :=
  let found := program.denialFound index body
  found.notes ++ program.negationNotes found.negations ++
    if program.denialCyclic body then [⟨.head index, [], (HornClause.goal body).toFormula, .cyclicDenial⟩] else []

/-- Blockers every predicate and query shares: the global ones and every
denial's. A denial the module cannot check leaves the KB's consistency open,
and every answer assumes it. -/
def sharedBlockers : List (Blocker Variable Literal Symbol) :=
  program.globalBlockers ++ program.denials.flatMap fun denial => program.denialBlockers denial.1 denial.2

/-- A predicate's own blockers: its clauses', its NAF goals', and those of the
heads that may conclude it. -/
def ownBlockers (predicate : Symbol) : List (Blocker Variable Literal Symbol) :=
  let found := program.found predicate
  found.blockers ++ program.negationBlockers found.negations ++ program.openedBlockers predicate

/-- A predicate's own notes: term growth, its clauses' universal goals and
hypotheses, and NAF over a cycle. -/
def ownNotes (predicate : Symbol) : List (Note Variable Literal Symbol) :=
  let found := program.found predicate
  program.growthNotes predicate ++ found.notes ++ program.negationNotes found.negations

/-- The names a goal's quantifiers bind. -/
def binders : Term Variable Literal Symbol → List Variable
  | .conj left right | .disj left right | .imp left right => binders left ++ binders right
  | .defaultNeg body => binders body
  | .forallVar name body | .existsVar name body => name :: binders body
  | _ => []

/-- The most names a defining clause of a predicate joins: its free names and
those its quantifiers bind. -/
def width (predicate : Symbol) : Nat :=
  (program.definitions predicate).foldr (fun (_, args, body) bound =>
    max ((Term.conjunction (args ++ body)).freeVars ++ body.flatMap binders).eraseDups.length bound) 0

/-- Two defining clauses' input patterns cannot match the same call: at some
input position, a literal or declared constructor clash separates them. -/
def apart (predicate : Symbol) (first second : List (Term Variable Literal Symbol)) : Bool :=
  match program.io? predicate first, program.io? predicate second with
  | some (firstInputs, _), some (secondInputs, _) =>
      (firstInputs.zip secondInputs).any fun pair => !Completion.mayMatch program.free pair.1 pair.2
  | _, _ => false

/-- Pairs of distinct positions of a list, in order. -/
def pairs {α : Type} : List α → List (α × α)
  | [] => []
  | first :: rest => rest.map (first, ·) ++ pairs rest

/-- At most one defining clause applies to each call. -/
def deterministic (predicate : Symbol) : Bool :=
  (pairs (program.definitions predicate)).all fun pair => program.apart predicate pair.1.2.1 pair.2.2.1

/-! ## Classes and profiles -/

end Program

/-- A predicate's class. A query's class reads the same fields over the
predicates it uses: they all have data-term outputs, they are complete and the
query has no growth note of its own, they are deterministic; a query is on no
cycle. -/
structure Class (Variable Literal Symbol : Type) where
  /-- Its answers' outputs are data terms. -/
  dataOutputs : Bool
  /-- The predicates it reaches. -/
  reach : List Symbol
  cyclic : Bool
  /-- The complete cost class; budgeted otherwise. -/
  complete : Bool
  /-- The most names a clause of its dependency closure joins. -/
  degree : Nat
  /-- At most one of its clauses applies to each call. -/
  deterministic : Bool
  /-- The blockers of its dependency closure. -/
  blockers : List (Blocker Variable Literal Symbol)
  /-- The P2 reasons of its dependency closure. -/
  notes : List (Note Variable Literal Symbol)

/-- A profile: P1, P2 with its reasons, or Undecided with its blockers. -/
inductive Profile (Variable Literal Symbol : Type) where
  | p1
  | p2 (notes : List (Note Variable Literal Symbol))
  | undecided (blockers : List (Blocker Variable Literal Symbol))

def Class.profile (found : Class Variable Literal Symbol) : Profile Variable Literal Symbol :=
  match found.blockers, found.notes with
  | [], [] => .p1
  | [], notes => .p2 notes
  | blockers, _ => .undecided blockers

namespace Program

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] (program : Program Variable Literal Symbol)

/-- The blockers of some predicates: their own and the shared ones. -/
def blockersOf (members : List Symbol) : List (Blocker Variable Literal Symbol) :=
  members.flatMap program.ownBlockers ++ program.sharedBlockers

/-- The notes of some predicates: their own and those of the denials over them. -/
def notesOf (members : List Symbol) : List (Note Variable Literal Symbol) :=
  members.flatMap program.ownNotes ++
    (program.denialsOver members).flatMap fun denial => program.denialNotes denial.1 denial.2

/-- The blockers of a predicate's dependency closure. -/
def blockers (predicate : Symbol) : List (Blocker Variable Literal Symbol) := program.blockersOf (program.closure predicate)

/-- The notes of a predicate's dependency closure. -/
def notes (predicate : Symbol) : List (Note Variable Literal Symbol) := program.notesOf (program.closure predicate)

/-- The degree: the widest clause of the dependency closure. -/
def degree (predicate : Symbol) : Nat :=
  (program.closure predicate).foldr (fun member bound => max (program.width member) bound) 0

/-- A predicate's class. -/
def classOf (predicate : Symbol) : Class Variable Literal Symbol :=
  ⟨program.dataInfo predicate, program.reach predicate, program.cyclic predicate, program.complete predicate,
    program.degree predicate, program.deterministic predicate, program.blockers predicate, program.notes predicate⟩

/-- Every predicate of the graph with its class. -/
def classify : List (Symbol × Class Variable Literal Symbol) :=
  program.vertices.map fun predicate => (predicate, program.classOf predicate)

end Program

/-! ## From S07's program input -/

namespace Program

/-- The fragment's program of an S07 program input: the effective program's
KB clauses, as lowering gave them with their range guards, and the
signature's guard symbols, with the declared free constructors, the open
markers, and the mode declarations. -/
def ofInput {Domain : Type} [DecidableEq Symbol] (input : Admission.ProgramInput Domain Variable Literal Symbol)
    (hoApply : Symbol) (free : Symbol → Nat → Bool) (marker : Symbol → Bool) (modes : Modes Symbol) :
    Program Variable Literal Symbol :=
  ⟨(input.ask [] .truth).kbClauses, free, Machine.guardSymbol input.signature, marker, hoApply, modes⟩

end Program

/-! ## The graph's facts -/

namespace Program

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] (program : Program Variable Literal Symbol)

omit [DecidableEq Variable] [DecidableEq Literal] in
theorem edges_targets : ∀ edge ∈ program.edges, edge.2 ∈ program.vertices := by
  intro edge member
  simp only [vertices, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
  exact .inr ⟨edge, member, by simp⟩

omit [DecidableEq Variable] [DecidableEq Literal] in
/-- `reach` is the transitive closure of the dependency edges. -/
theorem reach_iff {predicate other : Symbol} :
    other ∈ program.reach predicate ↔ Relation.TransGen (Edge program.edges) predicate other :=
  Tabled.reach_iff program.edges_targets

omit [DecidableEq Variable] [DecidableEq Literal] in
theorem reach_trans {first middle last : Symbol} (left : middle ∈ program.reach first)
    (right : last ∈ program.reach middle) : last ∈ program.reach first :=
  Tabled.reach_trans program.edges_targets left right

omit [DecidableEq Variable] [DecidableEq Literal] in
theorem reach_edge {first last : Symbol} (edge : (first, last) ∈ program.edges) : last ∈ program.reach first :=
  Tabled.reach_edge program.edges_targets edge

omit [DecidableEq Variable] [DecidableEq Literal] in
/-- What a predicate reaches: its callees and what they reach. -/
theorem reach_step {predicate other : Symbol} :
    other ∈ program.reach predicate ↔ ∃ callee, (predicate, callee) ∈ program.edges ∧
      (callee = other ∨ other ∈ program.reach callee) :=
  Tabled.reach_step program.edges_targets

omit [DecidableEq Variable] [DecidableEq Literal] in
theorem mem_definitions {predicate : Symbol}
    {entry : Nat × List (Term Variable Literal Symbol) × List (Term Variable Literal Symbol)} :
    entry ∈ program.definitions predicate ↔
      ∃ head, (entry.1, .definite head entry.2.2) ∈ program.clauses ∧ program.headOf? head = some (predicate, entry.2.1) := by
  obtain ⟨index, args, body⟩ := entry
  simp only [definitions, List.mem_filterMap]
  constructor
  · rintro ⟨⟨found, clause⟩, member, produced⟩
    cases clause with
    | definite head clauseBody =>
        dsimp only at produced
        cases headEq : program.headOf? head with
        | none => rw [headEq] at produced; cases produced
        | some pair =>
            obtain ⟨symbol, headArgs⟩ := pair
            rw [headEq] at produced
            dsimp only at produced
            split at produced
            · rename_i same
              cases produced
              subst same
              exact ⟨head, member, headEq⟩
            · cases produced
    | goal _ => cases produced
  · rintro ⟨head, member, headEq⟩
    exact ⟨(index, .definite head body), member, by simp [headEq]⟩

omit [DecidableEq Variable] [DecidableEq Literal] in
/-- A defining clause's body calls are edges from its predicate. -/
theorem edge_of_definition {predicate callee : Symbol} {index : Nat}
    {args body : List (Term Variable Literal Symbol)} (member : (index, args, body) ∈ program.definitions predicate)
    (calls : callee ∈ body.flatMap program.calls) : (predicate, callee) ∈ program.edges := by
  obtain ⟨head, clause, headEq⟩ := program.mem_definitions.mp member
  simp only [edges, List.mem_flatMap]
  exact ⟨(index, .definite head body), clause, by simp only [headEq, List.mem_map]; exact ⟨callee, calls, rfl⟩⟩

omit [DecidableEq Variable] [DecidableEq Literal] in
theorem mem_closure {predicate other : Symbol} :
    other ∈ program.closure predicate ↔ other = predicate ∨ other ∈ program.reach predicate := by
  simp only [closure, List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq]
  constructor
  · rintro (same | ⟨inside, _⟩)
    · exact .inl same
    · exact .inr inside
  · rintro (same | inside)
    · exact .inl same
    · by_cases same : other = predicate
      · exact .inl same
      · exact .inr ⟨inside, same⟩

omit [DecidableEq Variable] [DecidableEq Literal] in
theorem mem_component {predicate other : Symbol} :
    other ∈ program.component predicate ↔
      other = predicate ∨ (other ∈ program.reach predicate ∧ predicate ∈ program.reach other) := by
  simp [component, recursive]

omit [DecidableEq Variable] [DecidableEq Literal] in
theorem component_closure {predicate other : Symbol} (member : other ∈ program.component predicate) :
    other ∈ program.closure predicate := by
  rcases program.mem_component.mp member with same | ⟨inside, _⟩
  · exact program.mem_closure.mpr (.inl same)
  · exact program.mem_closure.mpr (.inr inside)

omit [DecidableEq Variable] [DecidableEq Literal] in
/-- Within a component, a call is recursive. -/
theorem recursive_of_component {predicate caller callee : Symbol} (callerMember : caller ∈ program.component predicate)
    (calleeMember : callee ∈ program.component predicate) (edge : (caller, callee) ∈ program.edges) :
    program.recursive caller callee = true := by
  simp only [recursive, List.contains_eq_mem, decide_eq_true_eq]
  rcases program.mem_component.mp callerMember with rfl | ⟨callerInside, callerBack⟩ <;>
    rcases program.mem_component.mp calleeMember with rfl | ⟨calleeInside, calleeBack⟩
  · exact program.reach_edge edge
  · exact calleeBack
  · exact callerInside
  · exact program.reach_trans calleeBack callerInside

omit [DecidableEq Variable] [DecidableEq Literal] in
/-- Every predicate of the closure's closure is in the closure. -/
theorem closure_trans {first middle last : Symbol} (left : middle ∈ program.closure first)
    (right : last ∈ program.closure middle) : last ∈ program.closure first := by
  rcases program.mem_closure.mp left with rfl | leftInside
  · exact right
  · rcases program.mem_closure.mp right with rfl | rightInside
    · exact left
    · exact program.mem_closure.mpr (.inr (program.reach_trans leftInside rightInside))

mutual
/-- A call site's callee is a call of its goal. -/
theorem sites_callee {info : Symbol → Bool} :
    ∀ {frame : Frame Variable Literal Symbol} {small : List Variable} {path : List Nat}
      {goal : Term Variable Literal Symbol} {site : CallSite Variable Literal Symbol},
      site ∈ program.sites info frame small path goal → site.callee ∈ program.calls goal
  | frame, small, path, .conj left right, site, member => by
      simp only [sites, List.mem_append] at member
      simp only [calls, List.mem_append]
      rcases member with here | there
      · exact .inl (sites_callee here)
      · exact .inr (sites_callee there)
  | frame, small, path, .disj left right, site, member => by
      simp only [sites, List.mem_append] at member
      simp only [calls, List.mem_append]
      rcases member with here | there
      · exact .inl (sites_callee here)
      · exact .inr (sites_callee there)
  | frame, small, path, .defaultNeg operand, site, member => by
      simp only [sites] at member; simp only [calls]; exact sites_callee member
  | frame, small, path, .existsVar _ body, site, member => by
      simp only [sites] at member; simp only [calls]; exact sites_callee member
  | frame, small, path, .forallVar _ body, site, member => by
      simp only [sites] at member; simp only [calls]; exact sites_callee member
  | frame, small, path, .imp _ conclusion, site, member => by
      simp only [sites] at member; simp only [calls, List.mem_append]; exact .inr (sites_callee member)
  | frame, small, path, .app symbol args, site, member => by
      simp only [sites] at member
      simp only [calls]
      split at member
      · rename_i predicate callArgs callEq
        split at member
        · simp only [List.mem_singleton] at member; subst member; simp
        · cases member
      · cases member
  | _, _, _, .var _, _, member | _, _, _, .lit _, _, member | _, _, _, .truth, _, member
  | _, _, _, .falsity, _, member | _, _, _, .dictionaryCall _ _ _ _, _, member
  | _, _, _, .equal _ _, _, member => by simp [sites, callOf?] at member
end

theorem sitesBody_callee {info : Symbol → Bool} {frame : Frame Variable Literal Symbol} {index : Nat} :
    ∀ {position : Nat} {small : List Variable} {body : List (Term Variable Literal Symbol)}
      {pair : Site × CallSite Variable Literal Symbol},
      pair ∈ program.sitesBody info frame index position small body → pair.2.callee ∈ body.flatMap program.calls
  | _, _, [], _, member => by cases member
  | position, small, goal :: rest, pair, member => by
      simp only [sitesBody, List.mem_append, List.mem_map] at member
      simp only [List.flatMap_cons, List.mem_append]
      rcases member with ⟨site, inside, rfl⟩ | there
      · exact .inl (program.sites_callee inside)
      · exact .inr (sitesBody_callee there)

end Program

/-! ## Queries -/

/-- A query: the context, the goal, and the answer names, flexible; the
query's other free names are rigid parameters. Answer names are declared,
never inferred. -/
structure Query (Variable Literal Symbol : Type) where
  context : ProofContext Variable Literal Symbol
  goal : Formula Variable Literal Symbol
  answers : List Variable

namespace Program

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] (program : Program Variable Literal Symbol)

/-- An assumption of the query's context: atoms are facts, conjunctions and
existentials are opened, disjunctions are split eagerly (S26), and a Harrop
rule is a scoped local clause, P2 (`localRule`). Any other assumption is
outside the fragment. -/
def assumptionFound (index : Nat) (path : List Nat) : Term Variable Literal Symbol → Found Variable Literal Symbol
  | .truth | .falsity => .empty
  | .conj left right | .disj left right =>
      assumptionFound index (path ++ [0]) left ++ assumptionFound index (path ++ [1]) right
  | .existsVar _ body => assumptionFound index (path ++ [0]) body
  | .app symbol args =>
      if symbol = program.hoApply then .ofBlockers [outside (.assumption index) path (.app symbol args) .hoApplyConversion]
      else if program.guard symbol then .empty
      else .ofBlockers (program.argsBlockers (.assumption index) path 0 args)
  | .equal left right => .ofBlockers [outside (.assumption index) path (.equal left right) .equality]
  | .var name => .ofBlockers [outside (.assumption index) path (.var name) .formulaVariable]
  | formula =>
      if harrop formula then
        ⟨program.antecedentBlockers (.assumption index) path formula, [⟨.assumption index, path, formula, .localRule⟩], []⟩
      else .ofBlockers [outside (.assumption index) path formula .scopedProof]

/-- The predicates a query uses: those its goal and its context's rules call. -/
def used (query : Query Variable Literal Symbol) : List Symbol :=
  program.calls query.goal ++ query.context.flatMap program.ruleCalls

/-- The query's rigid parameters: its free names other than the answer names. -/
def Query.rigid (query : Query Variable Literal Symbol) : List Variable :=
  ((query.context.flatMap Term.freeVars) ++ query.goal.freeVars).filter fun name => !query.answers.contains name

/-- What the query itself gives: the scan of its goal (the answer names must
be bound by its end), its context, and its NAF goals. -/
def queryFound (query : Query Variable Literal Symbol) : Found Variable Literal Symbol :=
  let rigid := Program.Query.rigid query
  let goal := program.scan .goal rigid [] [] query.goal
  let unbound := query.answers.filterMap fun name =>
    if goal.bound.contains name then none else some (blocker .goal [] (.var name) .mode)
  let context := query.context.zipIdx.foldr (fun (assumption, index) rest => program.assumptionFound index [] assumption ++ rest) .empty
  goal.found ++ .ofBlockers (goal.close rigid ++ unbound) ++ context

/-- A query's class: its own blockers and notes with those of the predicates it uses. -/
def queryClass (query : Query Variable Literal Symbol) : Class Variable Literal Symbol :=
  let found := program.queryFound query
  let used := program.used query
  let members := (used.flatMap program.closure).eraseDups
  ⟨used.all program.dataInfo, members, false,
    used.all program.complete && found.notes.all fun note => !note.reason.growth,
    used.foldr (fun member bound => max (program.degree member) bound) 0, used.all program.deterministic,
    found.blockers ++ program.negationBlockers found.negations ++ program.blockersOf members,
    found.notes ++ program.negationNotes found.negations ++ program.notesOf members⟩

/-- A query's admission: P1, P2 with its reasons, or Undecided with its
blockers, before anything runs. -/
def admit (query : Query Variable Literal Symbol) : Profile Variable Literal Symbol :=
  (program.queryClass query).profile

/-- A query outside the fragment answers Undecided with its blockers before
anything runs (S22); an admitted query is answered by its run (S24). -/
def answer? {Proof Refutation Witness : Type} (query : Query Variable Literal Symbol) :
    Option (Answer Proof Refutation Witness (Blocker Variable Literal Symbol)) :=
  match program.admit query with
  | .undecided blockers => some (.undecided blockers)
  | _ => none

end Program

end AnthillModKbSpec.Tabled
