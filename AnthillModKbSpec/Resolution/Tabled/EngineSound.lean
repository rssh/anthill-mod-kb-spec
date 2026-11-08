import AnthillModKbSpec.Resolution.Tabled.Engine

/-! # The tabled run keeps the machine's invariants (S24)

Every generator of a tabled run is an ordinary machine state stepped by the
machine's `step`, so the machine's invariants hold for it (`step_valid`,
`step_sound`). The run adds the tables and the waiting branches; its
invariants (`Run.Valid`, `Run.Sound`) are the machine's for every generator,
plus:

- every waiting branch is a valid and sound branch of its owner's machine
  state, so scheduling an answer to it is a valid and sound choice point;
- every table answer is derivable in its closed context (`TablesSound`).

With a sound base strategy and sound NAF refutations, the engine's strategy is
sound (`strategy_sound`), every transition keeps the invariants
(`step_valid`, `step_sound`), and a successful run reconstructs its answer
(`run_reconstructs`, `run_init_reconstructs`): the query's goal, read through
the final answers, is derivable. -/

namespace AnthillModKbSpec.Tabled

open Machine Semantics

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  [FreshNames Variable]

attribute [local instance] termEq

/-- NAF evidence by the completion's models: the operand fails in every model
of the KB with complement NAF, under every environment satisfying the
context. -/
def semanticNaf : NafFailure Variable Literal Symbol := fun hoApplySymbol kb context operand =>
  ∀ (Value : Type) (model : Model Literal Symbol Value hoApplySymbol), model.Models kb → model.ComplementNAF →
    ∀ environment, model.ContextHolds environment context → model.Satisfies environment (.defaultNeg operand)

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem semanticNaf_adequate {hoApplySymbol : Symbol} {Value : Type} (model : Model Literal Symbol Value hoApplySymbol)
    {kb : LogicalKb Variable Literal Symbol} (models : model.Models kb) (negation : model.ComplementNAF) :
    model.FailureAdequate kb semanticNaf :=
  fun _ _ evidence environment holds => evidence Value model models negation environment holds

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem resolve_closed (store : Store Variable Literal Symbol) {term : Term Variable Literal Symbol}
    (closed : closedTerm term = true) : store.resolve term = term :=
  resolveWith_unbound fun name inside => by
    simp only [closedTerm, List.isEmpty_iff] at closed
    rw [closed] at inside; cases inside

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem resolve_closed_all (store : Store Variable Literal Symbol) {terms : List (Term Variable Literal Symbol)}
    (closed : terms.all closedTerm = true) : terms.map store.resolve = terms := by
  simp only [List.all_eq_true] at closed
  exact (List.map_congr_left fun term member => resolve_closed store (closed term member)).trans (List.map_id' _)

namespace Engine

variable (engine : Engine Variable Literal Symbol) (kb : LogicalKb Variable Literal Symbol)
  (naf : NafFailure Variable Literal Symbol)

/-- The tables' contexts are closed; their answers name only their calls'
free names, rigid parameters of every consumer, and are derivable in their
context. -/
def TablesSound (tables : List (Table Variable Literal Symbol)) : Prop :=
  ∀ table ∈ tables, table.call.context.all closedTerm = true ∧
    ∀ answer ∈ table.answers, (∀ name ∈ answer.atom.freeVars, name ∈ table.call.names) ∧
      Derives engine.hoApplySymbol kb table.call.context answer.atom naf

/-- A refuted ground operand has NAF evidence in every context. -/
def RefutesSound : Prop :=
  ∀ operand, engine.refutes operand = true → closedTerm operand = true → ∀ context, naf engine.hoApplySymbol kb context operand

variable {engine} {kb} {naf}

omit [DecidableEq Literal] [DecidableEq Symbol] in
/-- A term whose names are rigid in a store reads as itself in every scoped
refinement: a rigid name is never bound. -/
theorem resolve_rigid {store later : Store Variable Literal Symbol} (refines : store.Refines later) (scopedLater : later.Scoped)
    {term : Term Variable Literal Symbol} (rigid : ∀ name ∈ term.freeVars, store.info? name = some .rigid) :
    later.resolve term = term :=
  resolveWith_unbound fun name inside bound => by
    obtain ⟨⟨_, value⟩, member, rfl⟩ := List.mem_map.mp bound
    obtain ⟨_, flexible, _⟩ := scopedLater.answers _ value member
    rw [refines.rigid _ (rigid _ inside)] at flexible
    cases flexible

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem names_rigid {store : Store Variable Literal Symbol} {call : Call Variable Literal Symbol}
    (inputs : call.inputs.all (rigidTerm store) = true) (context : call.context.all closedTerm = true) :
    ∀ name ∈ call.names, store.info? name = some .rigid := by
  intro name member
  simp only [Call.names, List.mem_flatMap, List.mem_append] at member
  obtain ⟨term, inside | inside, named⟩ := member
  · have rigid := List.all_eq_true.mp inputs term inside
    simp only [rigidTerm, List.all_eq_true, decide_eq_true_eq] at rigid
    exact rigid name named
  · have closed := List.all_eq_true.mp context term inside
    simp only [closedTerm, List.isEmpty_iff] at closed
    rw [closed] at named; cases named

omit [FreshNames Variable] in
theorem callOfAtom_spec {store : Store Variable Literal Symbol} {symbol : Symbol} {args : List (Term Variable Literal Symbol)}
    {context : ProofContext Variable Literal Symbol} {call : Call Variable Literal Symbol}
    (found : engine.callOfAtom store symbol args context = some call) :
    call.predicate = symbol ∧ call.context = context ∧ call.context.all closedTerm = true ∧
      ∀ name ∈ call.names, store.info? name = some .rigid := by
  unfold callOfAtom at found
  split at found
  · cases found
  · split at found
    · rename_i inputs outputs _
      split at found
      · rename_i checked
        cases found
        simp only [Bool.and_eq_true] at checked
        exact ⟨rfl, rfl, checked.1.2, names_rigid checked.1.1 checked.1.2⟩
      · cases found
    · cases found

theorem call?_spec {obligation : Obligation Variable Literal Symbol} {store : Store Variable Literal Symbol}
    {call : Call Variable Literal Symbol} (found : engine.call? obligation store = some call) :
    call.context = obligation.context ∧ call.context.all closedTerm = true ∧
      ∀ name ∈ call.names, store.info? name = some .rigid := by
  unfold call? at found
  split at found
  · obtain ⟨_, context, closed, rigid⟩ := callOfAtom_spec found
    exact ⟨context, closed, rigid⟩
  · cases found

omit [FreshNames Variable] in
theorem findTable_spec {tables : List (Table Variable Literal Symbol)} {call : Call Variable Literal Symbol}
    {index : Nat} {table : Table Variable Literal Symbol} (found : findTable tables call = some (index, table)) :
    tables[index]? = some table ∧ table.call = call := by
  unfold findTable at found
  obtain ⟨entry, inside, same⟩ := Option.map_eq_some_iff.mp found
  cases same
  have spec := List.find?_some inside
  have member := List.mem_of_find?_eq_some inside
  simp only [Call.same, Bool.and_eq_true, decide_eq_true_eq] at spec
  refine ⟨by
    obtain ⟨⟨table', position⟩⟩ := entry
    have := List.mem_zipIdx member
    simp only [Nat.zero_add] at this
    obtain ⟨_, positionBound, same⟩ := this
    rw [same]; exact List.getElem?_eq_getElem positionBound, ?_⟩
  revert spec
  generalize entry.1.call = found
  intro spec
  cases found; cases call
  simp only at spec
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := spec
  rfl

omit [FreshNames Variable] in
theorem mem_of_findTable {tables : List (Table Variable Literal Symbol)} {call : Call Variable Literal Symbol}
    {index : Nat} {table : Table Variable Literal Symbol} (found : findTable tables call = some (index, table)) :
    table ∈ tables :=
  List.mem_of_getElem? (findTable_spec found).1

/-- An attempt is sound when its candidate is, for each refinement of the store
that is scoped and reads the matched sides as one. -/
theorem attempt_sound_scoped {Certificate : Type} {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol} {store : Store Variable Literal Symbol}
    {obligation : Obligation Variable Literal Symbol} (valid : store.Scoped) {flexibles : List Variable}
    {left right : Term Variable Literal Symbol}
    {make : List (Variable × Term Variable Literal Symbol) → Expansion Variable Literal Symbol Certificate}
    (shape : ∀ bindings, (make bindings).flexibles = flexibles ∧ (make bindings).rigids = [] ∧
      (make bindings).bindings = bindings)
    (matched : ∀ bindings (later : Store Variable Literal Symbol), store.Refines later → later.Scoped →
      later.resolve left = later.resolve right → NodeSound hoApplySymbol kb naf later obligation (make bindings).premises) :
    AttemptSound hoApplySymbol kb naf store obligation
      (attempt ((store.prepare obligation flexibles []).unify obligation.scope hoApplySymbol left right) make) := by
  intro expansion found next woken committed later refines scopedLater
  unfold attempt at found
  split at found
  · rename_i final bindings computed
    cases found
    obtain ⟨sameFlexibles, noRigids, sameBindings⟩ := shape bindings
    rw [sameFlexibles, noRigids, sameBindings] at committed
    exact matched bindings later ((Store.commit_refines committed).trans refines) scopedLater
      (refines.resolve_eq (Store.commit_matched valid computed committed))
  all_goals cases found

/-- A table answer is a sound candidate for a consumer of its call, whose
store holds the call's names rigid. -/
theorem consume_sound_of {obligation : Obligation Variable Literal Symbol} {store : Store Variable Literal Symbol}
    (valid : store.Scoped) {call : Call Variable Literal Symbol} {atom : Term Variable Literal Symbol}
    (contextClosed : call.context.all closedTerm = true) (within : ∀ name ∈ atom.freeVars, name ∈ call.names)
    (rigid : ∀ name ∈ call.names, store.info? name = some .rigid)
    (derived : Derives engine.hoApplySymbol kb call.context atom naf) (context : call.context = obligation.context) :
    AttemptSound engine.hoApplySymbol kb naf store obligation (engine.consume obligation store call atom) := by
  unfold consume
  apply attempt_sound_scoped valid (flexibles := []) (fun _ => ⟨rfl, rfl, rfl⟩)
  intro bindings later refines scopedLater same _
  unfold ReadDerives
  rw [same, resolve_rigid refines scopedLater (fun name inside => rigid name (within name inside)), ← context,
    resolve_closed_all later contextClosed]
  exact derived

/-- A table answer is a sound candidate for a goal in the table's context. -/
theorem consume_sound (sound : TablesSound engine kb naf tables) {table : Table Variable Literal Symbol}
    (member : table ∈ tables) {answer : TableAnswer Variable Literal Symbol} (inAnswers : answer ∈ table.answers)
    {obligation : Obligation Variable Literal Symbol} {store : Store Variable Literal Symbol} (valid : store.Scoped)
    {call : Call Variable Literal Symbol} (context : call.context = obligation.context)
    (rigid : ∀ name ∈ call.names, store.info? name = some .rigid) (same : table.call = call) :
    AttemptSound engine.hoApplySymbol kb naf store obligation (engine.consume obligation store call answer.atom) := by
  obtain ⟨contextClosed, answers⟩ := sound table member
  obtain ⟨within, derived⟩ := answers answer inAnswers
  subst same
  exact consume_sound_of valid contextClosed within rigid derived context

/-- The engine's unfitted strategy is sound: its table answers by the tables,
its NAF nodes by the refutation, its equations by reflexivity, the rest by the
base strategy. -/
theorem strategyCore_sound (baseSound : Strategy.Sound engine.hoApplySymbol kb naf engine.base)
    (refutesSound : RefutesSound engine kb naf) {tables : List (Table Variable Literal Symbol)}
    (sound : TablesSound engine kb naf tables) : Strategy.Sound engine.hoApplySymbol kb naf (engine.strategyCore tables) := by
  intro obligation store valid declared expansion member
  unfold strategyCore at member
  split at member
  · rename_i call found
    split at member
    · rename_i index table tableFound
      obtain ⟨context, _, rigid⟩ := call?_spec found
      refine respond_sound (fun candidate inside => ?_) expansion member
      obtain ⟨answer, inAnswers, rfl⟩ := List.mem_map.mp inside
      exact consume_sound sound (mem_of_findTable tableFound) inAnswers valid context rigid (findTable_spec tableFound).2
    · cases member
  · split at member
    · rename_i _ operand reads
      split at member
      · rename_i closed
        split at member
        · rename_i refuted
          simp only [Response.alternatives, List.mem_singleton] at member
          subst member
          refine fixed_sound fun later refines _ => ?_
          unfold ReadDerives
          rw [valid.read_refines reads refines, Store.resolve_defaultNeg, resolve_closed later closed]
          exact .defaultNegIntro (refutesSound operand refuted closed _)
        · repeat' split at member
          all_goals simp [Response.alternatives] at member
      · exact baseSound obligation store valid declared expansion member
    · rename_i left right written _
      refine respond_sound (fun candidate inside => ?_) expansion member
      simp only [List.mem_singleton] at inside
      subst inside
      unfold equation
      apply attempt_sound valid (flexibles := []) (fun _ => ⟨rfl, rfl, rfl⟩)
      intro bindings later same _
      unfold ReadDerives
      rw [written, Store.resolve_equal, same]
      exact .equalRefl
    · exact baseSound obligation store valid declared expansion member

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
/-- Fitting keeps some of a response's alternatives. -/
theorem fit_alternatives (top : Nat) (response : Response Variable Literal Symbol (Term Variable Literal Symbol)) :
    ∀ expansion ∈ (engine.fit top response).alternatives, expansion ∈ response.alternatives := by
  intro expansion member
  unfold fit at member
  split at member
  · exact member
  · unfold fitTo at member
    split at member
    · split at member
      · exact member
      · exact (List.mem_filter.mp member).1
    · exact (List.mem_filter.mp member).1
    · exact member

omit [DecidableEq Literal] in
/-- A fitted sound strategy is sound. -/
theorem fit_sound {strategy : Strategy Variable Literal Symbol (Term Variable Literal Symbol)} (weight : Obligation Variable Literal Symbol → Nat)
    (sound : Strategy.Sound engine.hoApplySymbol kb naf strategy) :
    Strategy.Sound engine.hoApplySymbol kb naf (fun obligation store => engine.fit (weight obligation) (strategy obligation store)) :=
  fun obligation store valid declared expansion member =>
    sound obligation store valid declared expansion (engine.fit_alternatives _ _ expansion member)

/-- **The engine's strategy is sound**, fitted or not. -/
theorem strategy_sound (baseSound : Strategy.Sound engine.hoApplySymbol kb naf engine.base)
    (refutesSound : RefutesSound engine kb naf) {tables : List (Table Variable Literal Symbol)}
    (sound : TablesSound engine kb naf tables) : Strategy.Sound engine.hoApplySymbol kb naf (engine.strategy tables) :=
  fit_sound (fun obligation => goalSize engine.hoApplySymbol obligation.goal) (strategyCore_sound baseSound refutesSound sound)

/-- A generator's root strategy is sound. -/
theorem rootStrategy_sound (baseSound : Strategy.Sound engine.hoApplySymbol kb naf engine.base) :
    Strategy.Sound engine.hoApplySymbol kb naf engine.rootStrategy :=
  fit_sound (fun _ => engine.rootWeight) baseSound

end Engine

/-! ## The machine's counter and root -/

section Machine

variable {Certificate Snapshot : Type}

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem State.enter_nextHole (state : State Variable Literal Symbol Certificate Snapshot)
    (obligation : Obligation Variable Literal Symbol) (expansion : Expansion Variable Literal Symbol Certificate)
    (rest : List (Expansion Variable Literal Symbol Certificate)) :
    (state.enter obligation expansion rest).nextHole = state.nextHole := by
  unfold State.enter
  split <;> rfl

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
/-- The suspension counter only grows. -/
theorem step_nextHole (strategy : Strategy Variable Literal Symbol Certificate)
    {state next : State Variable Literal Symbol Certificate Snapshot} (stepped : step strategy state = .running next) :
    state.nextHole ≤ next.nextHole := by
  unfold step at stepped
  repeat' split at stepped
  all_goals (try cases stepped)
  all_goals (try simp only [State.enter_nextHole])
  all_goals (first | exact Nat.le_refl _ | exact Nat.le_succ _ | simp)

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
/-- A success's resume state is the state, failed. -/
theorem step_success_resume (strategy : Strategy Variable Literal Symbol Certificate)
    {state resume : State Variable Literal Symbol Certificate Snapshot}
    {proof : CompletedProof Variable Literal Symbol Certificate Snapshot}
    (stepped : step strategy state = .finished (.success proof resume)) :
    resume.root = state.root ∧ resume.nextHole = state.nextHole := by
  unfold step at stepped
  repeat' split at stepped
  all_goals (try cases stepped)
  all_goals exact ⟨rfl, rfl⟩

end Machine

/-! ## Updating a list at a position -/

section Lists

open Engine

variable {α β : Type}

theorem length_updateAt : ∀ (items : List α) (position : Nat) (change : α → α),
    (updateAt items position change).length = items.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: rest, position + 1, change => by simp [updateAt, length_updateAt rest position change]

theorem mem_updateAt : ∀ {items : List α} {position : Nat} {change : α → α} {item : α},
    item ∈ updateAt items position change → item ∈ items ∨ ∃ original, items[position]? = some original ∧ item = change original
  | [], _, _, _, member => by cases member
  | first :: rest, 0, change, item, member => by
      simp only [updateAt, List.mem_cons] at member
      rcases member with rfl | inRest
      · exact .inr ⟨first, rfl, rfl⟩
      · exact .inl (List.mem_cons_of_mem _ inRest)
  | first :: rest, position + 1, change, item, member => by
      simp only [updateAt, List.mem_cons] at member
      rcases member with rfl | inRest
      · exact .inl List.mem_cons_self
      · rcases mem_updateAt inRest with inside | ⟨original, found, rfl⟩
        · exact .inl (List.mem_cons_of_mem _ inside)
        · exact .inr ⟨original, by simpa using found, rfl⟩

theorem map_updateAt (view : α → β) {change : α → α} (keeps : ∀ item, view (change item) = view item) :
    ∀ (items : List α) (position : Nat), (updateAt items position change).map view = items.map view
  | [], _ => rfl
  | first :: rest, 0 => by simp [updateAt, keeps]
  | first :: rest, position + 1 => by simp [updateAt, map_updateAt view keeps rest position]

theorem getElem?_updateAt : ∀ (items : List α) (position index : Nat) (change : α → α),
    (updateAt items position change)[index]? = if position = index then items[index]?.map change else items[index]?
  | [], _, _, _ => by simp [updateAt]
  | first :: rest, 0, 0, change => by simp [updateAt]
  | first :: rest, 0, index + 1, change => by simp [updateAt]
  | first :: rest, position + 1, 0, change => by simp [updateAt]
  | first :: rest, position + 1, index + 1, change => by
      simp only [updateAt, List.getElem?_cons_succ, getElem?_updateAt rest position index change]
      simp

theorem eq_of_nodup_map {view : α → β} :
    ∀ {items : List α}, (items.map view).Nodup → ∀ {position : Nat} {item other : α}, items[position]? = some item →
      other ∈ items → view other = view item → other = item
  | [], _, _, _, _, found, _, _ => by simp at found
  | first :: rest, distinct, position, item, other, found, member, same => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at distinct
      cases position with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst found
          rcases List.mem_cons.mp member with rfl | inRest
          · rfl
          · exact absurd ⟨other, inRest, same⟩ distinct.1
      | succ position =>
          simp only [List.getElem?_cons_succ] at found
          rcases List.mem_cons.mp member with rfl | inRest
          · exact absurd ⟨item, List.mem_of_getElem? found, same.symm⟩ distinct.1
          · exact eq_of_nodup_map distinct.2 found inRest same

end Lists

/-! ## The run's invariant -/

namespace Engine

variable (engine : Engine Variable Literal Symbol) (kb : LogicalKb Variable Literal Symbol)
  (naf : NafFailure Variable Literal Symbol) (query : Obligation Variable Literal Symbol)

/-- A waiting branch is a valid branch of a machine state: valid for its root
and its counter. -/
def Waiter.Fits (state : State Variable Literal Symbol (Term Variable Literal Symbol) Unit) (waiter : Waiter Variable Literal Symbol) :
    Prop :=
  Branch.Valid state.root waiter.store (.solve waiter.obligation) waiter.frames waiter.deferred state.nextHole

/-- The invariant of a tabled run. Every generator is a valid and sound machine
state; generators have distinct tables, below the table count, and the query
generator proves the query; every waiting branch is a valid, sound branch of
its owner, and a consumer is in its table's context with the call's names
rigid; table answers name only their call's names and are derivable, and a
generator proves its table's call in its context. -/
structure Run.Inv (run : Run Variable Literal Symbol) : Prop where
  valid : ∀ generator ∈ run.stack, generator.state.Valid
  sound : ∀ generator ∈ run.stack, generator.state.Sound engine.hoApplySymbol kb naf
  owners : (run.stack.map Generator.table).Nodup
  bounded : ∀ generator ∈ run.stack, ∀ index, generator.table = some index → index < run.tables.length
  rooted : ∀ generator ∈ run.stack, generator.table = none → generator.state.root = query
  contexts : ∀ generator ∈ run.stack, ∀ index table, generator.table = some index → run.tables[index]? = some table →
    generator.state.root.context = table.call.context
  tables : TablesSound engine kb naf run.tables
  fits : ∀ table ∈ run.tables, ∀ waiter ∈ table.waiters, ∀ generator ∈ run.stack, generator.table = waiter.owner →
    Waiter.Fits generator.state waiter
  ownersBounded : ∀ table ∈ run.tables, ∀ waiter ∈ table.waiters, ∀ index, waiter.owner = some index → index < run.tables.length
  waiters : ∀ table ∈ run.tables, ∀ waiter ∈ table.waiters,
    Branch.Sound engine.hoApplySymbol kb naf waiter.store (.solve waiter.obligation) waiter.frames waiter.deferred ∧
      (waiter.negative = false → waiter.obligation.context = table.call.context ∧
        ∀ name ∈ table.call.names, waiter.store.info? name = some .rigid)

variable {engine} {kb} {naf} {query}

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem waiter_fits_raise {state next : State Variable Literal Symbol (Term Variable Literal Symbol) Unit}
    {waiter : Waiter Variable Literal Symbol} (fits : Waiter.Fits state waiter) (root : next.root = state.root)
    (grows : state.nextHole ≤ next.nextHole) : Waiter.Fits next waiter := by
  unfold Waiter.Fits at fits ⊢
  rw [root]; exact fits.raise grows

omit [DecidableEq Literal] [DecidableEq Symbol] in
/-- Replacing a generator by one with the same table whose machine state is
valid, sound, with the same root and a counter no smaller keeps the invariant. -/
theorem Run.Inv.replace {run : Run Variable Literal Symbol} (inv : Run.Inv engine kb naf query run) {position : Nat}
    {generator : Generator Variable Literal Symbol} (found : run.stack[position]? = some generator)
    {change : Generator Variable Literal Symbol → Generator Variable Literal Symbol}
    (keeps : ∀ other, (change other).table = other.table) (nextValid : (change generator).state.Valid)
    (nextSound : (change generator).state.Sound engine.hoApplySymbol kb naf)
    (root : (change generator).state.root = generator.state.root)
    (grows : generator.state.nextHole ≤ (change generator).state.nextHole) :
    Run.Inv engine kb naf query { run with stack := updateAt run.stack position change } := by
  have member := List.mem_of_getElem? found
  have cases : ∀ other ∈ updateAt run.stack position change, other ∈ run.stack ∨ other = change generator := by
    intro other inside
    rcases mem_updateAt inside with old | ⟨original, originalFound, rfl⟩
    · exact .inl old
    · rw [found] at originalFound; cases originalFound; exact .inr rfl
  refine ⟨fun other inside => ?_, fun other inside => ?_, ?_, fun other inside => ?_, fun other inside => ?_,
    fun other inside => ?_, inv.tables, fun table tableMember waiter waiterMember other inside => ?_, inv.ownersBounded,
    inv.waiters⟩
  · rcases cases other inside with old | rfl
    · exact inv.valid other old
    · exact nextValid
  · rcases cases other inside with old | rfl
    · exact inv.sound other old
    · exact nextSound
  · show ((updateAt run.stack position change).map Generator.table).Nodup
    rw [map_updateAt Generator.table keeps]
    exact inv.owners
  · rcases cases other inside with old | rfl
    · exact inv.bounded other old
    · rw [keeps]; exact inv.bounded generator member
  · rcases cases other inside with old | rfl
    · exact inv.rooted other old
    · intro none; rw [root]; exact inv.rooted generator member (by rw [← keeps]; exact none)
  · rcases cases other inside with old | rfl
    · exact inv.contexts other old
    · intro index table owned tableFound; rw [root]
      exact inv.contexts generator member index table (by rw [← keeps]; exact owned) tableFound
  · rcases cases other inside with old | rfl
    · exact inv.fits table tableMember waiter waiterMember other old
    · intro owned
      exact waiter_fits_raise (inv.fits table tableMember waiter waiterMember generator member (by rw [← keeps]; exact owned))
        root grows

omit [DecidableEq Literal] [DecidableEq Symbol] in
/-- Leaving the focused branch of a generator waiting on a table keeps the
invariant. A consumer must be in the table's context. -/
theorem Run.Inv.waited {run : Run Variable Literal Symbol} (inv : Run.Inv engine kb naf query run) {position : Nat}
    {generator : Generator Variable Literal Symbol} (found : run.stack[position]? = some generator)
    {obligation : Obligation Variable Literal Symbol} (focus : generator.state.focus = .solve obligation)
    {index : Nat} {table : Table Variable Literal Symbol} (tableFound : run.tables[index]? = some table) (negative : Bool)
    (context : negative = false → obligation.context = table.call.context ∧
      ∀ name ∈ table.call.names, generator.state.store.info? name = some .rigid) :
    Run.Inv engine kb naf query (wait run position index negative) := by
  have member := List.mem_of_getElem? found
  unfold wait
  rw [found]
  simp only [focus]
  let waiter : Waiter Variable Literal Symbol :=
    ⟨generator.table, negative, obligation, generator.state.store, generator.state.frames, generator.state.deferred⟩
  have stackCases : ∀ other ∈ updateAt run.stack position (fun generator => { generator with dep := min generator.dep index }),
      ∃ original ∈ run.stack, other.state = original.state ∧ other.table = original.table := by
    intro other inside
    rcases mem_updateAt inside with old | ⟨original, originalFound, rfl⟩
    · exact ⟨other, old, rfl, rfl⟩
    · exact ⟨original, List.mem_of_getElem? originalFound, rfl, rfl⟩
  have tableCases : ∀ other ∈ updateTable run.tables index (fun table => { table with waiters := table.waiters ++ [waiter] }),
      other ∈ run.tables ∨ other = { table with waiters := table.waiters ++ [waiter] } := by
    intro other inside
    rcases mem_updateAt inside with old | ⟨original, originalFound, rfl⟩
    · exact .inl old
    · rw [tableFound] at originalFound; cases originalFound; exact .inr rfl
  have lengths : (updateTable run.tables index (fun table => { table with waiters := table.waiters ++ [waiter] })).length =
      run.tables.length := length_updateAt _ _ _
  have tablesAt : ∀ (position' : Nat) (found' : Table Variable Literal Symbol), (updateTable run.tables index (fun table => { table with waiters := table.waiters ++ [waiter] }))[position']? =
      some found' → ∃ original : Table Variable Literal Symbol, run.tables[position']? = some original ∧
        found'.call = original.call ∧ found'.answers = original.answers := by
    intro position' found' inside
    unfold updateTable at inside
    rw [getElem?_updateAt] at inside
    split at inside
    · obtain ⟨original, originalFound, rfl⟩ := Option.map_eq_some_iff.mp inside
      exact ⟨original, originalFound, rfl, rfl⟩
    · exact ⟨found', inside, rfl, rfl⟩
  have owned : ∀ other ∈ run.stack, other.table = generator.table → other = generator := fun other inside same =>
    eq_of_nodup_map inv.owners found inside same
  refine ⟨fun other inside => ?_, fun other inside => ?_, ?_, fun other inside => ?_, fun other inside => ?_,
    fun other inside => ?_, fun other inside => ?_, fun other inside waiter' waiterMember gen genMember => ?_,
    fun other inside waiter' waiterMember => ?_, fun other inside waiter' waiterMember => ?_⟩
  · obtain ⟨original, originalMember, sameState, _⟩ := stackCases other inside
    rw [sameState]; exact inv.valid original originalMember
  · obtain ⟨original, originalMember, sameState, _⟩ := stackCases other inside
    rw [sameState]; exact inv.sound original originalMember
  · show ((updateAt run.stack position (fun generator => { generator with dep := min generator.dep index })).map
      Generator.table).Nodup
    rw [map_updateAt Generator.table (change := fun generator => { generator with dep := min generator.dep index })
      (fun _ => rfl)]
    exact inv.owners
  · rw [lengths]
    obtain ⟨original, originalMember, _, sameTable⟩ := stackCases other inside
    rw [sameTable]; exact inv.bounded original originalMember
  · obtain ⟨original, originalMember, sameState, sameTable⟩ := stackCases other inside
    rw [sameState, sameTable]; exact inv.rooted original originalMember
  · intro index' table' ownedIndex tableFound'
    obtain ⟨original', originalFound', sameCall, _⟩ := tablesAt index' table' tableFound'
    rw [sameCall]
    obtain ⟨original, originalMember, sameState, sameTable⟩ := stackCases other inside
    rw [sameState]
    exact inv.contexts original originalMember index' original' (by rw [← sameTable]; exact ownedIndex) originalFound'
  · rcases tableCases other inside with old | rfl
    · exact inv.tables other old
    · exact inv.tables table (List.mem_of_getElem? tableFound)
  · intro ownedBy
    obtain ⟨original, originalMember, sameState, sameTable⟩ := stackCases gen genMember
    unfold Waiter.Fits
    rw [sameState]
    rw [sameTable] at ownedBy
    change Waiter.Fits original.state waiter'
    rcases tableCases other inside with old | rfl
    · exact inv.fits other old waiter' waiterMember original originalMember ownedBy
    · rcases List.mem_append.mp waiterMember with inOld | inNew
      · exact inv.fits table (List.mem_of_getElem? tableFound) waiter' inOld original originalMember ownedBy
      · rw [List.mem_singleton] at inNew
        subst inNew
        rw [owned original originalMember ownedBy]
        have branch := (inv.valid generator member).branch
        rw [focus] at branch
        exact branch
  · intro index' ownedBy
    rw [lengths]
    rcases tableCases other inside with old | rfl
    · exact inv.ownersBounded other old waiter' waiterMember index' ownedBy
    · rcases List.mem_append.mp waiterMember with inOld | inNew
      · exact inv.ownersBounded table (List.mem_of_getElem? tableFound) waiter' inOld index' ownedBy
      · rw [List.mem_singleton] at inNew; subst inNew; exact inv.bounded generator member index' ownedBy
  · rcases tableCases other inside with old | rfl
    · exact inv.waiters other old waiter' waiterMember
    · rcases List.mem_append.mp waiterMember with inOld | inNew
      · exact inv.waiters table (List.mem_of_getElem? tableFound) waiter' inOld
      · rw [List.mem_singleton] at inNew; subst inNew
        have branch := (inv.sound generator member).branch
        rw [focus] at branch
        exact ⟨branch, context⟩


omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem generator_root (symbol : Symbol) (args : List (Term Variable Literal Symbol)) (call : Call Variable Literal Symbol) :
    (engine.generator symbol args call).root.context = call.context := by
  simp [Engine.generator, State.init, Obligation.root, Obligation.context]

/-- Opening the table of a new call keeps the invariant. -/
theorem Run.Inv.opened {run : Run Variable Literal Symbol} (inv : Run.Inv engine kb naf query run) {symbol : Symbol}
    {args : List (Term Variable Literal Symbol)} {context : ProofContext Variable Literal Symbol}
    {store : Store Variable Literal Symbol}
    {call : Call Variable Literal Symbol} (found : engine.callOfAtom store symbol args context = some call) :
    Run.Inv engine kb naf query (engine.open_ run symbol args call) := by
  obtain ⟨_, _, closed, _⟩ := callOfAtom_spec found
  unfold Engine.open_
  dsimp only
  generalize stateEq : engine.generator symbol args call = state
  have stateValid : state.Valid := stateEq ▸ State.init_valid _ _ _ _
  have stateSound : state.Sound engine.hoApplySymbol kb naf := stateEq ▸ State.init_sound _ _ _ _
  have stateContext : state.root.context = call.context := stateEq ▸ generator_root symbol args call
  have newIndex : ∀ generator ∈ run.stack, generator.table ≠ some run.tables.length := fun generator member same =>
    Nat.lt_irrefl _ (inv.bounded generator member _ same)
  have tablesAt : ∀ index table, (run.tables ++ [⟨call, state.root, [], [], false⟩])[index]? = some table →
      (index < run.tables.length ∧ run.tables[index]? = some table) ∨
        (index = run.tables.length ∧ table = ⟨call, state.root, [], [], false⟩) := by
    intro index table inside
    by_cases below : index < run.tables.length
    · rw [List.getElem?_append_left below] at inside; exact .inl ⟨below, inside⟩
    · rw [List.getElem?_append_right (by omega)] at inside
      have zero : index - run.tables.length = 0 := by
        cases h : index - run.tables.length with
        | zero => rfl
        | succ n => rw [h] at inside; simp at inside
      rw [zero] at inside
      simp only [List.getElem?_cons_zero, Option.some.injEq] at inside
      exact .inr ⟨by omega, inside.symm⟩
  refine ⟨fun generator inside => ?_, fun generator inside => ?_, ?_, fun generator inside => ?_,
    fun generator inside => ?_, fun generator inside => ?_, fun table inside => ?_,
    fun table inside waiter waiterMember generator genMember => ?_, fun table inside waiter waiterMember => ?_,
    fun table inside waiter waiterMember => ?_⟩
  · rcases List.mem_cons.mp inside with rfl | old
    · exact stateValid
    · exact inv.valid generator old
  · rcases List.mem_cons.mp inside with rfl | old
    · exact stateSound
    · exact inv.sound generator old
  · simp only [List.map_cons, List.nodup_cons, List.mem_map]
    exact ⟨fun ⟨generator, member, same⟩ => newIndex generator member same, inv.owners⟩
  · intro index owned
    simp only [List.length_append, List.length_singleton]
    rcases List.mem_cons.mp inside with rfl | old
    · cases owned; omega
    · have := inv.bounded generator old index owned; omega
  · rcases List.mem_cons.mp inside with rfl | old
    · intro none; cases none
    · exact inv.rooted generator old
  · intro index table owned tableFound
    rcases List.mem_cons.mp inside with rfl | old
    · cases owned
      rcases tablesAt _ _ tableFound with ⟨below, _⟩ | ⟨_, rfl⟩
      · exact absurd below (Nat.lt_irrefl _)
      · exact stateContext
    · rcases tablesAt _ _ tableFound with ⟨_, oldFound⟩ | ⟨rfl, _⟩
      · exact inv.contexts generator old index table owned oldFound
      · exact absurd owned (newIndex generator old)
  · rcases List.mem_append.mp inside with old | inNew
    · exact inv.tables table old
    · rw [List.mem_singleton] at inNew; subst inNew
      exact ⟨closed, fun answer member => by cases member⟩
  · intro owned
    rcases List.mem_append.mp inside with old | inNew
    · rcases List.mem_cons.mp genMember with rfl | oldGen
      · cases waiterOwner : waiter.owner with
        | none => rw [waiterOwner] at owned; cases owned
        | some index =>
            rw [waiterOwner] at owned; cases owned
            exact absurd (inv.ownersBounded table old waiter waiterMember _ waiterOwner) (Nat.lt_irrefl _)
      · exact inv.fits table old waiter waiterMember generator oldGen owned
    · rw [List.mem_singleton] at inNew; subst inNew; cases waiterMember
  · intro index owned
    simp only [List.length_append, List.length_singleton]
    rcases List.mem_append.mp inside with old | inNew
    · have := inv.ownersBounded table old waiter waiterMember index owned; omega
    · rw [List.mem_singleton] at inNew; subst inNew; cases waiterMember
  · rcases List.mem_append.mp inside with old | inNew
    · exact inv.waiters table old waiter waiterMember
    · rw [List.mem_singleton] at inNew; subst inNew; cases waiterMember

/-- Scheduling an answer of a table to one of its waiters keeps the invariant. -/
theorem Run.Inv.scheduled {run : Run Variable Literal Symbol} (inv : Run.Inv engine kb naf query run)
    {table : Table Variable Literal Symbol} (tableMember : table ∈ run.tables) {atom : Term Variable Literal Symbol}
    {proof : CompletedProof Variable Literal Symbol (Term Variable Literal Symbol) Unit}
    (answerMember : ⟨atom, proof⟩ ∈ table.answers) {waiter : Waiter Variable Literal Symbol} (waiterMember : waiter ∈ table.waiters)
    (gaps : List (Gap Variable Literal Symbol)) :
    Run.Inv engine kb naf query { run with stack := (engine.schedule run.stack table.call atom waiter).1, gaps := gaps } := by
  unfold schedule
  split
  · exact { inv with }
  · split
    · rename_i expansion consumed
      let push : Generator Variable Literal Symbol → Generator Variable Literal Symbol := fun generator =>
        if generator.table = waiter.owner then
          { generator with state := { generator.state with choices :=
              ⟨waiter.obligation, [expansion], waiter.store, waiter.frames, waiter.deferred, none⟩ :: generator.state.choices } }
        else generator
      have stackCases : ∀ other ∈ run.stack.map push, ∃ original ∈ run.stack,
          other.table = original.table ∧ other.state.root = original.state.root ∧
            other.state.nextHole = original.state.nextHole ∧ other.state.Valid ∧
            other.state.Sound engine.hoApplySymbol kb naf := by
        intro other inside
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp inside
        refine ⟨original, originalMember, ?_⟩
        simp only [push]
        split
        · rename_i owned
          have fits := inv.fits table tableMember waiter waiterMember original originalMember owned
          have soundWaiter := inv.waiters table tableMember waiter waiterMember
          have originalValid := inv.valid original originalMember
          have originalSound := inv.sound original originalMember
          refine ⟨rfl, rfl, rfl, ⟨originalValid.branch, fun point inside => ?_⟩, ⟨originalSound.branch, fun point inside => ?_⟩⟩
          · rcases List.mem_cons.mp inside with rfl | old
            · exact fits
            · exact originalValid.choices point old
          · rcases List.mem_cons.mp inside with rfl | old
            · refine ⟨soundWaiter.1, fun candidate candidateMember => ?_⟩
              simp only [List.mem_singleton] at candidateMember
              rw [candidateMember]
              obtain ⟨contextClosed, answers⟩ := inv.tables table tableMember
              obtain ⟨within, derived⟩ := answers _ answerMember
              obtain ⟨context, rigid⟩ := soundWaiter.2 (by simpa using ‹¬waiter.negative = true›)
              exact consume_sound_of (fits.storeScoped) contextClosed within rigid derived context.symm expansion consumed
            · exact originalSound.choices point old
        · exact ⟨rfl, rfl, rfl, inv.valid original originalMember, inv.sound original originalMember⟩
      have tablesSame : (run.stack.map push).map Generator.table = run.stack.map Generator.table := by
        rw [List.map_map]; exact List.map_congr_left fun generator _ => by simp only [Function.comp, push]; split <;> rfl
      refine ⟨fun other inside => ?_, fun other inside => ?_, by show ((run.stack.map push).map _).Nodup; rw [tablesSame]; exact inv.owners,
        fun other inside => ?_, fun other inside => ?_, fun other inside => ?_, inv.tables,
        fun table' inside' waiter' waiterMember' other inside => ?_, inv.ownersBounded, inv.waiters⟩
      · obtain ⟨_, _, _, _, _, valid, _⟩ := stackCases other inside; exact valid
      · obtain ⟨_, _, _, _, _, _, sound⟩ := stackCases other inside; exact sound
      · obtain ⟨original, member, sameTable, _⟩ := stackCases other inside
        rw [sameTable]; exact inv.bounded original member
      · obtain ⟨original, member, sameTable, sameRoot, _⟩ := stackCases other inside
        rw [sameTable, sameRoot]; exact inv.rooted original member
      · obtain ⟨original, member, sameTable, sameRoot, _⟩ := stackCases other inside
        rw [sameTable, sameRoot]; exact inv.contexts original member
      · obtain ⟨original, member, sameTable, sameRoot, sameHole, _⟩ := stackCases other inside
        intro owned
        unfold Waiter.Fits
        rw [sameRoot, sameHole]
        exact inv.fits table' inside' waiter' waiterMember' original member (by rw [← sameTable]; exact owned)
    · exact { inv with }
    · exact { inv with }


omit [DecidableEq Literal] [DecidableEq Symbol] in
/-- Updating tables keeps the invariant when calls and waiters stay and answers
stay sound. -/
theorem Run.Inv.retable {run : Run Variable Literal Symbol} (inv : Run.Inv engine kb naf query run)
    {tables : List (Table Variable Literal Symbol)} (lengths : tables.length = run.tables.length)
    (at_ : ∀ (index : Nat) (table : Table Variable Literal Symbol), tables[index]? = some table →
      ∃ original : Table Variable Literal Symbol, run.tables[index]? = some original ∧
        table.call = original.call ∧ (∀ waiter ∈ table.waiters, waiter ∈ original.waiters))
    (answers : TablesSound engine kb naf tables) :
    Run.Inv engine kb naf query { run with tables := tables } := by
  have members : ∀ table ∈ tables, ∃ original ∈ run.tables, table.call = original.call ∧
      (∀ waiter ∈ table.waiters, waiter ∈ original.waiters) := by
    intro table member
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨original, originalFound, sameCall, subset⟩ := at_ index table found
    exact ⟨original, List.mem_of_getElem? originalFound, sameCall, subset⟩
  refine ⟨inv.valid, inv.sound, inv.owners, fun generator inside index owned => ?_, inv.rooted,
    fun generator inside index table owned found => ?_, answers, fun table inside waiter waiterMember => ?_,
    fun table inside waiter waiterMember index owned => ?_, fun table inside waiter waiterMember => ?_⟩
  · rw [lengths]; exact inv.bounded generator inside index owned
  · obtain ⟨original, originalFound, sameCall, _⟩ := at_ index table found
    rw [sameCall]; exact inv.contexts generator inside index original owned originalFound
  · obtain ⟨original, originalMember, _, subset⟩ := members table inside
    exact inv.fits original originalMember waiter (subset waiter waiterMember)
  · obtain ⟨original, originalMember, _, subset⟩ := members table inside
    rw [lengths]; exact inv.ownersBounded original originalMember waiter (subset waiter waiterMember) index owned
  · obtain ⟨original, originalMember, sameCall, subset⟩ := members table inside
    rw [sameCall]; exact inv.waiters original originalMember waiter (subset waiter waiterMember)

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem getElem?_updateTable_cases {tables : List (Table Variable Literal Symbol)} {index position : Nat}
    {change : Table Variable Literal Symbol → Table Variable Literal Symbol} {table : Table Variable Literal Symbol}
    (found : (updateTable tables index change)[position]? = some table) :
    ∃ original, tables[position]? = some original ∧ (table = change original ∨ table = original) := by
  unfold updateTable at found
  rw [getElem?_updateAt] at found
  split at found
  · obtain ⟨original, originalFound, rfl⟩ := Option.map_eq_some_iff.mp found
    exact ⟨original, originalFound, .inl rfl⟩
  · exact ⟨table, found, .inr rfl⟩

/-- Recording a derivable answer of a table, naming only its call's names, and
scheduling it to the table's consumers, keeps the invariant. -/
theorem Run.Inv.answered {run : Run Variable Literal Symbol} (inv : Run.Inv engine kb naf query run) {index : Nat}
    {table : Table Variable Literal Symbol} (tableFound : run.tables[index]? = some table) {atom : Term Variable Literal Symbol}
    {proof : CompletedProof Variable Literal Symbol (Term Variable Literal Symbol) Unit}
    (within : ∀ name ∈ atom.freeVars, name ∈ table.call.names)
    (derived : Derives engine.hoApplySymbol kb table.call.context atom naf) :
    Run.Inv engine kb naf query (engine.answer run index atom proof) := by
  unfold Engine.answer
  rw [tableFound]
  dsimp only
  split
  · exact inv
  · let added : Table Variable Literal Symbol := { table with answers := table.answers ++ [⟨atom, proof⟩] }
    have addedMember : added ∈ updateTable run.tables index (fun table => { table with answers := table.answers ++ [⟨atom, proof⟩] }) := by
      apply List.mem_of_getElem? (i := index)
      unfold updateTable; rw [getElem?_updateAt, ite_eq_left rfl, tableFound]; rfl
    have first : Run.Inv engine kb naf query
        { run with tables := updateTable run.tables index (fun table => { table with answers := table.answers ++ [⟨atom, proof⟩] }) } := by
      refine inv.retable (length_updateAt _ _ _) (fun position table' found => ?_) (fun table' inside => ?_)
      · obtain ⟨original, originalFound, same | same⟩ := getElem?_updateTable_cases found
        · rw [same]; exact ⟨original, originalFound, rfl, fun _ member => member⟩
        · rw [same]; exact ⟨original, originalFound, rfl, fun _ member => member⟩
      · rcases mem_updateAt inside with old | ⟨original, originalFound, rfl⟩
        · exact inv.tables table' old
        · rw [tableFound] at originalFound; cases originalFound
          obtain ⟨contextClosed, answers⟩ := inv.tables table (List.mem_of_getElem? tableFound)
          refine ⟨contextClosed, fun answer member => ?_⟩
          rcases List.mem_append.mp member with old | inNew
          · exact answers answer old
          · rw [List.mem_singleton] at inNew; subst inNew; exact ⟨within, derived⟩
    have folded : ∀ (waiters : List (Waiter Variable Literal Symbol)), (∀ waiter ∈ waiters, waiter ∈ table.waiters) →
        ∀ (acc : List (Generator Variable Literal Symbol) × List (Gap Variable Literal Symbol)),
          Run.Inv engine kb naf query
            { tables := updateTable run.tables index (fun table => { table with answers := table.answers ++ [⟨atom, proof⟩] }),
              stack := acc.1, gaps := acc.2 } →
          Run.Inv engine kb naf query
            { tables := updateTable run.tables index (fun table => { table with answers := table.answers ++ [⟨atom, proof⟩] }),
              stack := (waiters.foldl (fun (acc : List (Generator Variable Literal Symbol) × List (Gap Variable Literal Symbol)) waiter =>
                let next := engine.schedule acc.1 table.call atom waiter
                (next.1, next.2 ++ acc.2)) acc).1, gaps := [] } := by
      intro waiters
      induction waiters with
      | nil => intro _ acc invAcc; exact { invAcc with }
      | cons waiter rest ih =>
          intro subset acc invAcc
          simp only [List.foldl_cons]
          apply ih (fun other member => subset other (List.mem_cons_of_mem _ member))
          exact Run.Inv.scheduled (table := added) (proof := proof) invAcc addedMember (by simp [added])
            (subset waiter List.mem_cons_self) _
    cases space : engine.inSpace atom
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact { first with }
    · simp only [↓reduceIte]; exact { folded table.waiters (fun _ member => member) (run.stack, []) { first with } with }

/-- Completing the top generators' tables and popping them keeps the invariant. -/
theorem Run.Inv.completed {run next : Run Variable Literal Symbol} (inv : Run.Inv engine kb naf query run) {count : Nat}
    (completed : complete? run count = some next) : Run.Inv engine kb naf query next := by
  unfold complete? at completed
  dsimp only at completed
  split at completed
  · split at completed
    · cases completed
      let clear : Table Variable Literal Symbol → Table Variable Literal Symbol := fun table => { table with complete := true, waiters := [] }
      have spec : ∀ (ids : List Nat) (tables : List (Table Variable Literal Symbol)), tables.length = run.tables.length →
          (∀ (index : Nat) (table : Table Variable Literal Symbol), tables[index]? = some table →
            ∃ original : Table Variable Literal Symbol, run.tables[index]? = some original ∧
            table.call = original.call ∧ table.answers = original.answers ∧ (∀ waiter ∈ table.waiters, waiter ∈ original.waiters)) →
          (ids.foldl (fun tables index => updateAt tables index clear) tables).length = run.tables.length ∧
          ∀ (index : Nat) (table : Table Variable Literal Symbol),
            (ids.foldl (fun tables index => updateAt tables index clear) tables)[index]? = some table →
            ∃ original : Table Variable Literal Symbol, run.tables[index]? = some original ∧ table.call = original.call ∧ table.answers = original.answers ∧
              (∀ waiter ∈ table.waiters, waiter ∈ original.waiters) := by
        intro ids
        induction ids with
        | nil => intro tables lengths at_; exact ⟨lengths, at_⟩
        | cons first rest ih =>
            intro tables lengths at_
            simp only [List.foldl_cons]
            apply ih
            · rw [length_updateAt]; exact lengths
            · intro index table found
              rw [getElem?_updateAt] at found
              split at found
              · obtain ⟨middle, middleFound, rfl⟩ := Option.map_eq_some_iff.mp found
                obtain ⟨original, originalFound, sameCall, sameAnswers, _⟩ := at_ index middle middleFound
                exact ⟨original, originalFound, sameCall, sameAnswers, fun _ member => by cases member⟩
              · exact at_ index table found
      obtain ⟨lengths, at_⟩ := spec _ run.tables rfl fun index table found =>
        ⟨table, found, rfl, rfl, fun _ member => member⟩
      have dropMember : ∀ generator ∈ run.stack.drop count, generator ∈ run.stack := fun _ member => List.mem_of_mem_drop member
      have base := inv.retable lengths (fun index table found => by
          obtain ⟨original, originalFound, sameCall, _, subset⟩ := at_ index table found
          exact ⟨original, originalFound, sameCall, subset⟩) (fun table inside => by
          obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp inside
          obtain ⟨original, originalFound, sameCall, sameAnswers, _⟩ := at_ index table found
          rw [sameCall, sameAnswers]; exact inv.tables original (List.mem_of_getElem? originalFound))
      exact ⟨fun generator inside => inv.valid generator (dropMember generator inside),
        fun generator inside => inv.sound generator (dropMember generator inside),
        (List.drop_sublist _ _).map Generator.table |>.nodup inv.owners,
        fun generator inside => base.bounded generator (dropMember generator inside),
        fun generator inside => inv.rooted generator (dropMember generator inside),
        fun generator inside => base.contexts generator (dropMember generator inside), base.tables,
        fun table inside waiter waiterMember generator genMember => base.fits table inside waiter waiterMember generator
          (dropMember generator genMember),
        base.ownersBounded, base.waiters⟩
    · cases completed
  · cases completed


omit [DecidableEq Literal] [DecidableEq Symbol] in
/-- A machine success reconstructs its root, read through the final answers. -/
theorem success_reconstructs {strategy : Strategy Variable Literal Symbol (Term Variable Literal Symbol)}
    {state resume : State Variable Literal Symbol (Term Variable Literal Symbol) Unit}
    {proof : CompletedProof Variable Literal Symbol (Term Variable Literal Symbol) Unit} (valid : state.Valid)
    (sound : state.Sound engine.hoApplySymbol kb naf) (stepped : Machine.step strategy state = .finished (.success proof resume)) :
    ReadDerives engine.hoApplySymbol kb naf proof.store proof.root ∧ proof.Valid state.root ∧ resume.Valid ∧
      resume.Sound engine.hoApplySymbol kb naf := by
  obtain ⟨completed, resumeValid, _⟩ := step_success strategy valid stepped
  obtain ⟨nodes, resumeSound⟩ := step_reconstructs strategy sound stepped
  have read := (nodes.mono fun _ _ from' => from' proof.store (.refl _) completed.answers).readDerives
    completed.coherent completed.complete
  rw [completed.proves, ← completed.rooted] at read
  exact ⟨read, completed, resumeValid, resumeSound⟩

/-- One machine transition of a generator keeps the invariant; a success of
the query reconstructs the query. -/
theorem Run.Inv.advanced {run : Run Variable Literal Symbol} (inv : Run.Inv engine kb naf query run) {position : Nat}
    {original generator : Generator Variable Literal Symbol} (found : run.stack[position]? = some original)
    (sameState : generator.state = original.state) (sameTable : generator.table = original.table)
    {strategy : Strategy Variable Literal Symbol (Term Variable Literal Symbol)}
    (strategySound : Strategy.Sound engine.hoApplySymbol kb naf strategy) :
    (∀ next, engine.advance run position generator strategy = .running next → Run.Inv engine kb naf query next) ∧
    (∀ proof resume, engine.advance run position generator strategy = .success proof resume →
      ReadDerives engine.hoApplySymbol kb naf proof.store proof.root ∧ proof.Valid query ∧ Run.Inv engine kb naf query resume) := by
  have member := List.mem_of_getElem? found
  have valid : generator.state.Valid := sameState ▸ inv.valid original member
  have sound : generator.state.Sound engine.hoApplySymbol kb naf := sameState ▸ inv.sound original member
  unfold advance
  cases stepped : Machine.step strategy generator.state with
  | running next =>
      refine ⟨fun final advanced => ?_, fun _ _ advanced => by cases advanced⟩
      cases advanced
      obtain ⟨nextValid, nextRoot⟩ := step_valid strategy valid stepped
      exact inv.replace found (change := fun generator => { generator with state := next }) (fun _ => rfl) nextValid
        (step_sound strategy strategySound valid sound stepped) (by rw [← sameState]; exact nextRoot)
        (by rw [← sameState]; exact step_nextHole strategy stepped)
  | finished outcome =>
      cases outcome with
      | success proof resume =>
          obtain ⟨read, completed, resumeValid, resumeSound⟩ := success_reconstructs valid sound stepped
          obtain ⟨resumeRoot, resumeHole⟩ := step_success_resume strategy stepped
          have resumed := inv.replace found (change := fun generator => { generator with state := resume }) (fun _ => rfl)
            resumeValid resumeSound (by rw [← sameState]; exact resumeRoot)
            (by show original.state.nextHole ≤ resume.nextHole; rw [← sameState, resumeHole]; exact Nat.le_refl _)
          dsimp only
          cases tableEq : generator.table with
          | none =>
              have rooted : generator.state.root = query := by
                rw [sameState]; exact inv.rooted original member (by rw [← sameTable]; exact tableEq)
              refine ⟨fun _ advanced => (by cases advanced), fun proof' resume' advanced => ?_⟩
              cases advanced
              exact ⟨read, rooted ▸ completed, resumed⟩
          | some index =>
              have bound := inv.bounded original member index (by rw [← sameTable]; exact tableEq)
              obtain ⟨table, tableFound⟩ : ∃ table, run.tables[index]? = some table :=
                ⟨run.tables[index], List.getElem?_eq_getElem bound⟩
              cases within : withinCall run.tables index (proof.store.resolve proof.root.goal) with
              | false =>
                  simp only [within, Bool.false_eq_true, ↓reduceIte]
                  refine ⟨fun final advanced => ?_, fun _ _ advanced => (by cases advanced)⟩
                  cases advanced
                  exact { resumed with }
              | true =>
                  simp only [within, ↓reduceIte]
                  refine ⟨fun final advanced => ?_, fun _ _ advanced => (by cases advanced)⟩
                  cases advanced
                  have context := inv.contexts original member index table (by rw [← sameTable]; exact tableEq) tableFound
                  obtain ⟨contextClosed, _⟩ := inv.tables table (List.mem_of_getElem? tableFound)
                  have derived : Derives engine.hoApplySymbol kb table.call.context (proof.store.resolve proof.root.goal) naf := by
                    unfold ReadDerives at read
                    rw [completed.rooted, sameState, context, resolve_closed_all _ contextClosed] at read
                    rw [completed.rooted, sameState]
                    exact read
                  have names : ∀ name ∈ (proof.store.resolve proof.root.goal).freeVars, name ∈ table.call.names := by
                    simp only [withinCall, tableFound, List.all_eq_true, decide_eq_true_eq] at within
                    exact within
                  exact resumed.answered tableFound names derived
      | _ => exact ⟨fun final advanced => (by cases advanced; exact inv), fun _ _ advanced => (by cases advanced)⟩


omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem wait_found {run : Run Variable Literal Symbol} {position : Nat} {generator : Generator Variable Literal Symbol}
    (found : run.stack[position]? = some generator) (index : Nat) (negative : Bool) :
    ∃ waiting, (wait run position index negative).stack[position]? = some waiting ∧ waiting.state = generator.state ∧
      waiting.table = generator.table := by
  unfold wait
  rw [found]
  dsimp only
  cases focus : generator.state.focus with
  | solve obligation =>
      refine ⟨{ generator with dep := min generator.dep index }, ?_, rfl, rfl⟩
      show (updateAt run.stack position _)[position]? = _
      rw [getElem?_updateAt, ite_eq_left rfl, found]; rfl
  | proved _ => exact ⟨generator, found, rfl, rfl⟩
  | failed => exact ⟨generator, found, rfl, rfl⟩

theorem call?_app {obligation : Obligation Variable Literal Symbol} {store : Store Variable Literal Symbol}
    {call : Call Variable Literal Symbol} (found : engine.call? obligation store = some call) {symbol : Symbol}
    {args : List (Term Variable Literal Symbol)} (reads : store.resolve obligation.goal = .app symbol args) :
    engine.callOfAtom store symbol args obligation.scope.assumptions = some call := by
  unfold call? at found; rw [reads] at found; exact found

variable (baseSound : Strategy.Sound engine.hoApplySymbol kb naf engine.base) (refutesSound : RefutesSound engine kb naf)
include baseSound refutesSound

/-- Stepping a generator keeps the invariant: opening a table, leaving a branch
waiting, or a machine transition; a success of the query reconstructs it. -/
theorem Run.Inv.steppedAt {run : Run Variable Literal Symbol} (inv : Run.Inv engine kb naf query run) {position : Nat}
    {generator : Generator Variable Literal Symbol} (found : run.stack[position]? = some generator) :
    (∀ next, engine.stepAt run position generator = .running next → Run.Inv engine kb naf query next) ∧
    (∀ proof resume, engine.stepAt run position generator = .success proof resume →
      ReadDerives engine.hoApplySymbol kb naf proof.store proof.root ∧ proof.Valid query ∧ Run.Inv engine kb naf query resume) := by
  have tabled := strategy_sound baseSound refutesSound inv.tables
  have plain := inv.advanced found rfl rfl tabled
  unfold stepAt
  split
  · -- The root: resolution against the clauses.
    have started := inv.replace found (change := fun generator => { generator with started := true }) (fun _ => rfl)
      (inv.valid generator (List.mem_of_getElem? found)) (inv.sound generator (List.mem_of_getElem? found)) rfl (Nat.le_refl _)
    have startedFound : (updateAt run.stack position fun generator => { generator with started := true })[position]? =
        some { generator with started := true } := by
      rw [getElem?_updateAt, ite_eq_left rfl, found]; rfl
    exact started.advanced startedFound rfl rfl (rootStrategy_sound baseSound)
  split
  · rename_i obligation focus
    split
    · rename_i call callFound
      cases tableEq : findTable run.tables call with
      | none =>
          simp only []
          split
          · rename_i symbol args reads
            exact ⟨fun next opened => by cases opened; exact inv.opened (call?_app callFound reads),
              fun _ _ opened => (by cases opened)⟩
          · exact plain
      | some found' =>
          obtain ⟨index, table⟩ := found'
          simp only []
          obtain ⟨tableAt, sameContext⟩ := findTable_spec tableEq
          have waitedInv : Run.Inv engine kb naf query (if table.complete then run else wait run position index false) := by
            split
            · exact inv
            · exact inv.waited found focus tableAt false fun _ => by
                rw [sameContext]; exact ⟨((call?_spec callFound).1).symm, (call?_spec callFound).2.2⟩
          obtain ⟨waiting, waitingFound, sameState, sameTable⟩ :
              ∃ waiting, (if table.complete then run else wait run position index false).stack[position]? = some waiting ∧
                waiting.state = generator.state ∧ waiting.table = generator.table := by
            split
            · exact ⟨generator, found, rfl, rfl⟩
            · exact wait_found found index false
          exact waitedInv.advanced waitingFound sameState.symm sameTable.symm tabled
    · split
      · rename_i symbol args _ reads
        split
        · split
          · rename_i call callFound
            split
            · exact ⟨fun next opened => by cases opened; exact inv.opened callFound, fun _ _ opened => (by cases opened)⟩
            · rename_i index table tableFound
              obtain ⟨tableAt, _⟩ := findTable_spec tableFound
              split
              · exact plain
              · obtain ⟨waiting, waitingFound, sameState, sameTable⟩ := wait_found found index true
                exact (inv.waited found focus tableAt true fun never => by cases never).advanced waitingFound
                  sameState.symm sameTable.symm tabled
          · exact plain
        · exact plain
      · exact plain
  · exact plain

/-- **Every transition keeps the invariant**, and a success of the query
reconstructs its answer instance. -/
theorem Run.Inv.step {run : Run Variable Literal Symbol} (inv : Run.Inv engine kb naf query run) :
    (∀ next, engine.step run = .running next → Run.Inv engine kb naf query next) ∧
    (∀ proof resume, engine.step run = .success proof resume →
      ReadDerives engine.hoApplySymbol kb naf proof.store proof.root ∧ proof.Valid query ∧ Run.Inv engine kb naf query resume) := by
  unfold Engine.step
  split
  · exact ⟨fun _ finished => (by cases finished), fun _ _ finished => (by cases finished)⟩
  · rename_i position _
    split
    · rename_i completed completedEq
      refine ⟨fun next stepped => ?_, fun _ _ stepped => (by cases stepped)⟩
      cases stepped
      split at completedEq
      · cases completedEq
      · exact inv.completed completedEq
    · split
      · rename_i generator found
        exact inv.steppedAt baseSound refutesSound found
      · exact ⟨fun _ finished => (by cases finished), fun _ _ finished => (by cases finished)⟩

/-- A run keeps the invariant; its success reconstructs the query's answer
instance. -/
theorem Run.Inv.run : ∀ (fuel : Nat) {run : Run Variable Literal Symbol}, Run.Inv engine kb naf query run →
    (∀ proof resume, engine.run fuel run = .success proof resume →
      ReadDerives engine.hoApplySymbol kb naf proof.store proof.root ∧ proof.Valid query ∧ Run.Inv engine kb naf query resume) ∧
    (∀ final, engine.run fuel run = .interrupted final → Run.Inv engine kb naf query final)
  | 0, run, inv => ⟨fun _ _ ran => (by cases ran), fun final ran => by cases ran; exact inv⟩
  | fuel + 1, run, inv => by
      unfold Engine.run
      have stepped := inv.step baseSound refutesSound
      split
      · rename_i next stepEq
        exact Run.Inv.run fuel (stepped.1 next stepEq)
      · rename_i proof resume stepEq
        exact ⟨fun proof' resume' ran => by cases ran; exact stepped.2 proof resume stepEq,
          fun _ ran => (by cases ran)⟩
      · exact ⟨fun _ _ ran => (by cases ran), fun _ ran => (by cases ran)⟩

omit baseSound refutesSound [DecidableEq Literal] [DecidableEq Symbol] in
/-- The invariant of a query's start. -/
theorem start_inv (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    Run.Inv engine kb naf (State.init (Certificate := Term Variable Literal Symbol) () [] context goal).root
      (Engine.start context goal) := by
  refine ⟨fun generator inside => ?_, fun generator inside => ?_, by simp [Engine.start], fun generator inside => ?_,
    fun generator inside _ => ?_, fun generator inside => ?_, fun _ inside => (by cases inside),
    fun _ inside => (by cases inside), fun _ inside => (by cases inside), fun _ inside => (by cases inside)⟩
  all_goals simp only [Engine.start, List.mem_singleton] at inside
  all_goals subst inside
  · exact State.init_valid _ _ _ _
  · exact State.init_sound _ _ _ _
  · intro _ owned; cases owned
  · rfl
  · intro _ _ owned; cases owned

/-- **A successful tabled run reconstructs its answer instance**: the query's
goal and context read through the final answers are derivable. -/
theorem run_init_reconstructs (fuel : Nat) (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol)
    {proof : CompletedProof Variable Literal Symbol (Term Variable Literal Symbol) Unit} {resume : Run Variable Literal Symbol}
    (ran : engine.run fuel (Engine.start context goal) = .success proof resume) :
    Derives engine.hoApplySymbol kb (context.map proof.store.resolve) (proof.store.resolve goal) naf := by
  obtain ⟨read, completed, _⟩ := ((start_inv context goal).run baseSound refutesSound fuel).1 proof resume ran
  unfold ReadDerives at read
  rw [completed.rooted] at read
  simpa [State.init, Obligation.root, Obligation.context] using read

end Engine

end AnthillModKbSpec.Tabled
