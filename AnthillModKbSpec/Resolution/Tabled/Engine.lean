import AnthillModKbSpec.Resolution.Tabled.Witness
import AnthillModKbSpec.Resolution.Tabled.Admission
import AnthillModKbSpec.Resolution.Tabled.Weight
import AnthillModKbSpec.Resolution.P1.Negation

/-! # Tabled backtracking on the shared machine (S24)

SLG resolution as an extension of the shared machine. The run's state
(`Run`) holds the tables and a completion stack of generators, each one
ordinary machine state (`Machine.State`) whose transitions are the machine's
`step` with the engine's strategy:

- **Tables.** One per distinct call: a predicate, its input values as read,
  with no flexible name (rigid parameters are fixed for the run), and the
  closed context (`Call`). A table holds its answers, each with the
  generator's completed proof, and the branches waiting on it.
- **A new call** creates a table and pushes its generator: a machine state
  for the call with its outputs as fresh answer names, which resolves the call
  against the program's clauses (`Engine.rootStrategy`). The caller waits,
  focused on the call, until the table completes.
- **A repeated call** consumes its table (`Engine.strategy`): every answer is a
  candidate, its node a leaf naming the answer (`tableRule`).
- **A recursive call** consumes the answers so far and leaves a consumer: its
  branch (obligation, store, continuations, deferred proofs). Each later answer
  of the table is scheduled to every consumer as a choice point of the
  consumer's own machine state.
- **Completion per component.** When the generators on top of the stack have
  no alternative left, and none depends on a table below them, their tables
  are complete: they are one strongly connected component, popped together.
- **NAF.** `naf A` with `A` ground: refuted in the completion
  (`Engine.refutes`), it is proved by a node carrying the refutation's
  evidence; with an answer `A` in its table it fails. A table not yet complete
  makes the NAF wait: a loop through NAF is delayed, and resolved when its
  component completes, where the NAF is an open atom (`GapReason.opened`)
  unless an answer made it fail.
- **Fuel** bounds the transitions of a P2 run; running out is `interrupted`,
  never an answer.
- **Bounds.** A bounded run (P1) tables only calls drawn from its bounds,
  schedules only answers drawn from them, and keeps only the alternatives
  lighter than their focus (`fit`); it ends without fuel
  (`Tabled/Termination`).

The machine's invariants and reconstruction carry over to every generator,
and the tables' answers are derivable (`Tabled/EngineSound`). -/

namespace AnthillModKbSpec.Tabled

open Machine

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  [FreshNames Variable]

attribute [local instance] termEq

/-! ## Calls, tables, and the run -/

/-- A tabled call: a predicate, its input values as read, and the context,
all closed. -/
structure Call (Variable Literal Symbol : Type) where
  predicate : Symbol
  inputs : List (Term Variable Literal Symbol)
  context : ProofContext Variable Literal Symbol

/-- The same call: a variant, as read. -/
def Call.same (first second : Call Variable Literal Symbol) : Bool :=
  decide (first.predicate = second.predicate) && decide (first.inputs = second.inputs) &&
    decide (first.context = second.context)

/-- An answer of a table: the call's atom with its outputs, and the
generator's completed proof of it. -/
structure TableAnswer (Variable Literal Symbol : Type) where
  atom : Term Variable Literal Symbol
  proof : CompletedProof Variable Literal Symbol (Term Variable Literal Symbol) Unit

/-- A branch waiting on a table: a consumer of its answers, or a NAF waiting
for its completion. It belongs to the machine state of its owner: the
generator of a table, or the query (`none`). -/
structure Waiter (Variable Literal Symbol : Type) where
  owner : Option Nat
  negative : Bool
  obligation : Obligation Variable Literal Symbol
  store : Store Variable Literal Symbol
  frames : List (Continuation Variable Literal Symbol (Term Variable Literal Symbol))
  deferred : List (DeferredProof Variable Literal Symbol (Term Variable Literal Symbol))

structure Table (Variable Literal Symbol : Type) where
  call : Call Variable Literal Symbol
  root : Obligation Variable Literal Symbol
  answers : List (TableAnswer Variable Literal Symbol)
  waiters : List (Waiter Variable Literal Symbol)
  complete : Bool

/-- One machine state on the completion stack: the generator of a table, or
the query (`table = none`), with the oldest table it depends on. -/
structure Generator (Variable Literal Symbol : Type) where
  table : Option Nat
  state : State Variable Literal Symbol (Term Variable Literal Symbol) Unit
  dep : Nat
  /-- The root has been resolved against the clauses. -/
  started : Bool := true

/-- The tabled run: tables by index, the completion stack (top first), and the
gaps of the generators already popped. -/
structure Run (Variable Literal Symbol : Type) where
  tables : List (Table Variable Literal Symbol)
  stack : List (Generator Variable Literal Symbol)
  gaps : List (Gap Variable Literal Symbol)

/-- The bounds of a bounded run (P1): the predicates, data terms, and
assumptions its calls are drawn from, and the most arguments an atom has. A
call outside them is a gap, and only answers within them are scheduled to
consumers, so the run's tables and the answers it schedules are finitely many
(`Tabled/Termination`). -/
structure Bounds (Variable Literal Symbol : Type) where
  predicates : List Symbol
  data : List (Term Variable Literal Symbol)
  arity : Nat
  assumptions : List (Term Variable Literal Symbol)

/-- What the engine needs: the `ho_apply` symbol, the fragment's program with
its modes, the clauses calls are resolved against, the unknown markers, the
rule name of table answers, the refutation of ground NAF operands with its
evidence, and, for a bounded run, its bounds. -/
structure Engine (Variable Literal Symbol : Type) where
  hoApplySymbol : Symbol
  fragment : Tabled.Program Variable Literal Symbol
  resolution : Machine.Program Variable Literal Symbol
  unknownMarker : Symbol → Bool
  tableSymbol : Symbol
  refutes : Term Variable Literal Symbol → Bool
  evidence : Term Variable Literal Symbol → Term Variable Literal Symbol
  bounds : Option (Bounds Variable Literal Symbol) := none

/-- A machine state with nothing left to try. -/
def State.done (state : State Variable Literal Symbol (Term Variable Literal Symbol) Unit) : Bool :=
  match state.focus, state.choices with
  | .failed, [] => true
  | _, _ => false

/-- A closed term: no free name. -/
def closedTerm (term : Term Variable Literal Symbol) : Bool := term.freeVars.isEmpty

/-- A term with no flexible name as read: every free name a rigid parameter
of the store. -/
def rigidTerm (store : Store Variable Literal Symbol) (term : Term Variable Literal Symbol) : Bool :=
  term.freeVars.all fun name => decide (store.info? name = some .rigid)

/-- The free names of a call: its inputs' and its context's. -/
def Call.names (call : Call Variable Literal Symbol) : List Variable :=
  (call.inputs ++ call.context).flatMap Term.freeVars

namespace Engine

variable (engine : Engine Variable Literal Symbol)

/-! ## The strategy -/

/-- A bounded run's check of a call: its predicate, inputs, and context drawn
from the bounds, the context without repeats. An unbounded run admits every
call. -/
def admits (symbol : Symbol) (inputs : List (Term Variable Literal Symbol)) (context : ProofContext Variable Literal Symbol) :
    Bool :=
  match engine.bounds with
  | none => true
  | some bounds =>
      bounds.predicates.contains symbol && decide (inputs.length ≤ bounds.arity) && inputs.all (· ∈ bounds.data) &&
        context.all (· ∈ bounds.assumptions) && decide context.Nodup

/-- The call an atom makes in a context, when it is tabled: a predicate with
a declared mode at its arity, its inputs with no flexible name as read (rigid
parameters are fixed for the run), the context closed, within the bounds of a
bounded run. -/
def callOfAtom (store : Store Variable Literal Symbol) (symbol : Symbol) (args : List (Term Variable Literal Symbol))
    (context : ProofContext Variable Literal Symbol) : Option (Call Variable Literal Symbol) :=
  if symbol = engine.hoApplySymbol ∨ engine.fragment.guard symbol = true ∨ engine.unknownMarker symbol = true then none
  else
    match engine.fragment.io? symbol args with
    | some (inputs, _) =>
        if inputs.all (rigidTerm store) && context.all closedTerm && engine.admits symbol inputs context then
          some ⟨symbol, inputs, context⟩
        else none
    | none => none

/-- The call a focused obligation makes, as read. -/
def call? (obligation : Obligation Variable Literal Symbol) (store : Store Variable Literal Symbol) :
    Option (Call Variable Literal Symbol) :=
  match store.resolve obligation.goal with
  | .app symbol args => engine.callOfAtom store symbol args obligation.scope.assumptions
  | _ => none

/-- An answer a bounded run schedules to consumers: an atom of the bounds'
predicates over its data terms. -/
def inSpace (atom : Term Variable Literal Symbol) : Bool :=
  match engine.bounds with
  | none => true
  | some bounds =>
      match atom with
      | .app symbol args => bounds.predicates.contains symbol && decide (args.length ≤ bounds.arity) && args.all (· ∈ bounds.data)
      | _ => false

/-- The table of a call. -/
def findTable (tables : List (Table Variable Literal Symbol)) (call : Call Variable Literal Symbol) :
    Option (Nat × Table Variable Literal Symbol) :=
  (tables.zipIdx.find? fun entry => entry.1.call.same call).map fun entry => (entry.2, entry.1)

/-- A table answer as a candidate: the goal matched against the answer's atom,
its node a leaf naming the answer and its context. -/
def consume (obligation : Obligation Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (call : Call Variable Literal Symbol) (atom : Term Variable Literal Symbol) :
    Attempt Variable Literal Symbol (Term Variable Literal Symbol) :=
  attempt ((store.prepare obligation [] []).unify obligation.scope engine.hoApplySymbol obligation.goal atom)
    fun bindings => { rule := .extension engine.tableSymbol (atom :: call.context) none, bindings }

/-- A data equation, by matching its sides. -/
def equation (obligation : Obligation Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (left right : Term Variable Literal Symbol) : Attempt Variable Literal Symbol (Term Variable Literal Symbol) :=
  attempt ((store.prepare obligation [] []).unify obligation.scope engine.hoApplySymbol left right)
    fun bindings => { rule := .equalRefl, bindings }

/-- The positive strategy over the resolution clauses, unknown markers open. -/
def base : Strategy Variable Literal Symbol (Term Variable Literal Symbol) :=
  Strategy.withOpenGoals engine.unknownMarker (positive engine.hoApplySymbol engine.resolution)

/-- The alternatives of a response that fit a focus of weight `top`; a
response that loses any is incomplete (`Tabled/Weight`). -/
def fitTo (top : Nat) : Response Variable Literal Symbol (Term Variable Literal Symbol) →
    Response Variable Literal Symbol (Term Variable Literal Symbol)
  | .candidates alternatives =>
      if alternatives.all (fun expansion => decide (Fits engine.hoApplySymbol top expansion)) then .candidates alternatives
      else .incomplete (alternatives.filter fun expansion => decide (Fits engine.hoApplySymbol top expansion))
  | .incomplete alternatives => .incomplete (alternatives.filter fun expansion => decide (Fits engine.hoApplySymbol top expansion))
  | response => response

/-- A bounded run keeps only the alternatives lighter than the focus, so that
every machine step lowers the branches' weights (`step_lower`); an unbounded
run keeps every one. -/
def fit (top : Nat) (response : Response Variable Literal Symbol (Term Variable Literal Symbol)) :
    Response Variable Literal Symbol (Term Variable Literal Symbol) :=
  match engine.bounds with
  | none => response
  | some _ => engine.fitTo top response

/-- The weight of a generator's root, which resolves a call against the
clauses: more than any clause body's. -/
def rootWeight : Nat :=
  (engine.resolution.clauses.map fun entry =>
    match entry.clause with
    | .definite _ body => goalSize engine.hoApplySymbol (Term.conjunction body)
    | .goal _ => 0).foldr max 0 + 3

/-- A generator's root: the call resolved against the clauses. -/
def rootStrategy : Strategy Variable Literal Symbol (Term Variable Literal Symbol) :=
  fun obligation store => engine.fit engine.rootWeight (engine.base obligation store)

/-- What the engine answers for a focus inside a generator or the query: a
tabled call's answers, a ground NAF by its refutation or its table, a data
equation, otherwise the positive strategy. -/
def strategyCore (tables : List (Table Variable Literal Symbol)) : Strategy Variable Literal Symbol (Term Variable Literal Symbol) :=
  fun obligation store =>
    match engine.call? obligation store with
    | some call =>
        match findTable tables call with
        | some (_, table) => respond (table.answers.map fun answer => engine.consume obligation store call answer.atom)
        | none => .candidates []
    | none =>
        match store.resolve obligation.goal, obligation.goal with
        | .defaultNeg operand, _ =>
            if closedTerm operand then
              if engine.refutes operand then .candidates [Expansion.negation (engine.evidence operand)]
              else
                match operand with
                | .app symbol args =>
                    match engine.callOfAtom store symbol args obligation.scope.assumptions with
                    | some call =>
                        match findTable tables call with
                        | some (_, table) =>
                            if table.answers.any (fun answer => decide (answer.atom = operand)) then .candidates []
                            else if table.complete then .opened
                            else .candidates []
                        | none => .candidates []
                    | none => .unsupported
                | _ => .unsupported
            else engine.base obligation store
        | _, .equal left right => respond [engine.equation obligation store left right]
        | _, _ => engine.base obligation store

/-- The engine's strategy, fitted to the focused goal's size in a bounded run. -/
def strategy (tables : List (Table Variable Literal Symbol)) : Strategy Variable Literal Symbol (Term Variable Literal Symbol) :=
  fun obligation store => engine.fit (goalSize engine.hoApplySymbol obligation.goal) (engine.strategyCore tables obligation store)

/-! ## Run transitions -/

/-- Put the output positions' fresh names into a call's arguments. -/
def withOutputs : List Mode → List (Term Variable Literal Symbol) → List Variable → List (Term Variable Literal Symbol)
  | .input :: modes, arg :: args, names => arg :: withOutputs modes args names
  | .output :: modes, _ :: args, name :: names => .var name :: withOutputs modes args names
  | _, args, _ => args

/-- The generator of a new call: a machine state for the atom with its outputs
as fresh answer names. -/
def generator (symbol : Symbol) (args : List (Term Variable Literal Symbol)) (call : Call Variable Literal Symbol) :
    State Variable Literal Symbol (Term Variable Literal Symbol) Unit :=
  let modes := (engine.fragment.modes symbol).getD []
  let names := freshNames call.names (modes.filter (· = .output)).length
  State.init () names call.context (.app symbol (withOutputs modes args names))

/-- Create the table of a call and push its generator. -/
def open_ (run : Run Variable Literal Symbol) (symbol : Symbol) (args : List (Term Variable Literal Symbol))
    (call : Call Variable Literal Symbol) : Run Variable Literal Symbol :=
  let state := engine.generator symbol args call
  { run with
    tables := run.tables ++ [⟨call, state.root, [], [], false⟩]
    stack := ⟨some run.tables.length, state, run.tables.length, false⟩ :: run.stack }

/-- Update the entry at a position. -/
def updateAt {α : Type} : List α → Nat → (α → α) → List α
  | [], _, _ => []
  | entry :: rest, 0, change => change entry :: rest
  | entry :: rest, position + 1, change => entry :: updateAt rest position change

/-- Update the table at an index. -/
def updateTable (tables : List (Table Variable Literal Symbol)) (index : Nat)
    (change : Table Variable Literal Symbol → Table Variable Literal Symbol) : List (Table Variable Literal Symbol) :=
  updateAt tables index change

/-- Leave a branch waiting on a table, and record the dependence. -/
def wait (run : Run Variable Literal Symbol) (position index : Nat) (negative : Bool) : Run Variable Literal Symbol :=
  match run.stack[position]? with
  | some generator =>
      match generator.state.focus with
      | .solve obligation =>
          let waiter : Waiter Variable Literal Symbol :=
            ⟨generator.table, negative, obligation, generator.state.store, generator.state.frames, generator.state.deferred⟩
          { run with
            tables := updateTable run.tables index fun table => { table with waiters := table.waiters ++ [waiter] }
            stack := updateAt run.stack position fun generator => { generator with dep := min generator.dep index } }
      | _ => run
  | none => run

/-- Schedule an answer to one consumer: a choice point in its owner's machine
state, or a gap when the match is unsupported. -/
def schedule (stack : List (Generator Variable Literal Symbol)) (call : Call Variable Literal Symbol)
    (atom : Term Variable Literal Symbol) (waiter : Waiter Variable Literal Symbol) :
    List (Generator Variable Literal Symbol) × List (Gap Variable Literal Symbol) :=
  if waiter.negative then (stack, [])
  else
    match engine.consume waiter.obligation waiter.store call atom with
    | some (some expansion) =>
        (stack.map fun generator =>
          if generator.table = waiter.owner then
            { generator with state := { generator.state with choices :=
                ⟨waiter.obligation, [expansion], waiter.store, waiter.frames, waiter.deferred, none⟩ :: generator.state.choices } }
          else generator, [])
    | some none => (stack, [])
    | none => (stack, [⟨.unsupported, waiter.obligation, trailOf waiter.frames⟩])

/-- Record a generator's answer, if new, and schedule it to the table's
consumers. A bounded run schedules only answers within its bounds; another one
is recorded, for consumers still to come, and each consumer waiting is a gap. -/
def answer (run : Run Variable Literal Symbol) (index : Nat) (atom : Term Variable Literal Symbol)
    (proof : CompletedProof Variable Literal Symbol (Term Variable Literal Symbol) Unit) : Run Variable Literal Symbol :=
  match run.tables[index]? with
  | some table =>
      if table.answers.any (fun found => decide (found.atom = atom)) then run
      else
        let scheduled := if engine.inSpace atom then
            table.waiters.foldl (fun (acc : List (Generator Variable Literal Symbol) × List (Gap Variable Literal Symbol)) waiter =>
              let next := engine.schedule acc.1 table.call atom waiter
              (next.1, next.2 ++ acc.2)) (run.stack, [])
          else (run.stack, table.waiters.filterMap fun waiter =>
            if waiter.negative then none else some ⟨.unsupported, waiter.obligation, trailOf waiter.frames⟩)
        { tables := updateTable run.tables index fun table => { table with answers := table.answers ++ [⟨atom, proof⟩] }
          stack := scheduled.1
          gaps := scheduled.2 ++ run.gaps }
  | none => run

/-- The NAF waiters of a completed table that no answer made fail: open atoms. -/
def openedNegations (table : Table Variable Literal Symbol) : List (Gap Variable Literal Symbol) :=
  table.waiters.filterMap fun waiter =>
    if waiter.negative then
      match waiter.store.resolve waiter.obligation.goal with
      | .defaultNeg operand =>
          if table.answers.any (fun answer => decide (answer.atom = operand)) then none
          else some ⟨.opened, waiter.obligation, trailOf waiter.frames⟩
      | _ => none
    else none

/-- Complete the top `count` generators' tables and pop them, when they form a
component: none depends on a table below the lowest of theirs. -/
def complete? (run : Run Variable Literal Symbol) (count : Nat) : Option (Run Variable Literal Symbol) :=
  let segment := run.stack.take count
  let ids := segment.filterMap Generator.table
  match ids.getLast? with
  | some lowest =>
      if ids.length = segment.length && segment.all (fun generator => decide (lowest ≤ generator.dep)) then
        let completed := ids.foldl (fun tables index => updateAt tables index fun table =>
          { table with complete := true, waiters := [] }) run.tables
        let opened := (run.tables.zipIdx.filter fun entry => entry.2 ∈ ids).flatMap fun entry => openedNegations entry.1
        some { tables := completed, stack := run.stack.drop count
               gaps := opened ++ segment.flatMap (fun generator => generator.state.gaps) ++ run.gaps }
      else none
  | none => none

/-- An answer's free names are among its call's: rigid parameters of every
consumer. -/
def withinCall (tables : List (Table Variable Literal Symbol)) (index : Nat) (atom : Term Variable Literal Symbol) : Bool :=
  match tables[index]? with
  | some table => atom.freeVars.all (· ∈ table.call.names)
  | none => false

/-- The outcome of a run whose query has nothing left: its gaps, as the
machine reports them. -/
def outcomeOf (gaps : List (Gap Variable Literal Symbol)) :
    Outcome Variable Literal Symbol (Term Variable Literal Symbol) Unit :=
  if gaps.isEmpty then .exhausted else if gaps.all Gap.isOpened then .opened gaps else .abandoned gaps

/-- What a run's step gives. -/
inductive Status (Variable Literal Symbol : Type) where
  | running (run : Run Variable Literal Symbol)
  | success (proof : CompletedProof Variable Literal Symbol (Term Variable Literal Symbol) Unit) (resume : Run Variable Literal Symbol)
  | finished (outcome : Outcome Variable Literal Symbol (Term Variable Literal Symbol) Unit)

/-- One machine transition of the generator at a stack position, with a strategy. -/
def advance (run : Run Variable Literal Symbol) (position : Nat) (generator : Generator Variable Literal Symbol)
    (strategy : Strategy Variable Literal Symbol (Term Variable Literal Symbol)) : Status Variable Literal Symbol :=
  match Machine.step strategy generator.state with
  | .running next => .running { run with stack := updateAt run.stack position fun generator => { generator with state := next } }
  | .finished (.success proof resume) =>
      let resumed := { run with stack := updateAt run.stack position fun generator => { generator with state := resume } }
      match generator.table with
      | none => .success proof resumed
      | some index =>
          let atom := proof.store.resolve proof.root.goal
          if withinCall run.tables index atom then .running (engine.answer resumed index atom proof)
          else .running { resumed with gaps := ⟨.unsupported, proof.root, []⟩ :: resumed.gaps }
  | .finished _ => .running run

/-- Step the generator at a stack position: its first step resolves its root
against the clauses; later ones open a table for a new call, leave a recursive
call or a NAF on an incomplete table waiting, and make the machine
transition. -/
def stepAt (run : Run Variable Literal Symbol) (position : Nat) (generator : Generator Variable Literal Symbol) :
    Status Variable Literal Symbol :=
  if !generator.started then
    engine.advance { run with stack := updateAt run.stack position fun generator => { generator with started := true } }
      position { generator with started := true } engine.rootStrategy
  else
  match generator.state.focus with
  | .solve obligation =>
        match engine.call? obligation generator.state.store with
        | some call =>
            match findTable run.tables call with
            | some (index, table) =>
                let waited := if table.complete then run else wait run position index false
                engine.advance waited position generator (engine.strategy run.tables)
            | none =>
                match generator.state.store.resolve obligation.goal with
                | .app symbol args => .running (engine.open_ run symbol args call)
                | _ => engine.advance run position generator (engine.strategy run.tables)
        | none =>
            match generator.state.store.resolve obligation.goal with
            | .defaultNeg (.app symbol args) =>
                if closedTerm (.app symbol args) && !engine.refutes (.app symbol args) then
                  match engine.callOfAtom generator.state.store symbol args obligation.scope.assumptions with
                  | some call =>
                      match findTable run.tables call with
                      | none => .running (engine.open_ run symbol args call)
                      | some (index, table) =>
                          if table.complete || table.answers.any (fun answer => decide (answer.atom = .app symbol args)) then
                            engine.advance run position generator (engine.strategy run.tables)
                          else engine.advance (wait run position index true) position generator (engine.strategy run.tables)
                  | none => engine.advance run position generator (engine.strategy run.tables)
                else engine.advance run position generator (engine.strategy run.tables)
            | _ => engine.advance run position generator (engine.strategy run.tables)
  | _ => engine.advance run position generator (engine.strategy run.tables)

/-- One transition of the run: complete the component on top when it has
nothing left, otherwise step the topmost generator with something left. The
query finishing with nothing left ends the run. -/
def step (run : Run Variable Literal Symbol) : Status Variable Literal Symbol :=
  match run.stack.findIdx? (fun generator => !State.done generator.state) with
  | none => .finished (outcomeOf (run.stack.flatMap (fun generator => generator.state.gaps) ++ run.gaps))
  | some position =>
      match (if position = 0 then none else complete? run position) with
      | some completed => .running completed
      | none =>
          match run.stack[position]? with
          | some generator => engine.stepAt run position generator
          | none => .finished (outcomeOf run.gaps)

/-- The outcome of a tabled run. `interrupted` keeps the run, whose top
generator's table names the call being evaluated. -/
inductive Outcome (Variable Literal Symbol : Type) where
  | success (proof : CompletedProof Variable Literal Symbol (Term Variable Literal Symbol) Unit) (resume : Run Variable Literal Symbol)
  | finished (outcome : Machine.Outcome Variable Literal Symbol (Term Variable Literal Symbol) Unit)
  | interrupted (run : Run Variable Literal Symbol)

/-- Run with fuel. -/
def run : Nat → Run Variable Literal Symbol → Outcome Variable Literal Symbol
  | 0, run => .interrupted run
  | fuel + 1, current =>
      match engine.step current with
      | .running next => run fuel next
      | .success proof resume => .success proof resume
      | .finished outcome => .finished outcome

/-- The run of a query: its machine state alone on the stack, no table yet. -/
def start (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) : Run Variable Literal Symbol :=
  ⟨[], [⟨none, State.init () [] context goal, 0, true⟩], []⟩

end Engine

end AnthillModKbSpec.Tabled
