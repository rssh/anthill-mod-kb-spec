import AnthillModKbSpec.Resolution.Tabled.EngineSound

/-! # A bounded tabled run ends, without fuel (S24)

A bounded run (`Engine.bounds`, P1) tables only calls drawn from its bounds
and schedules only answers drawn from them, and keeps only the alternatives
lighter than the focused goal (`Engine.fit`). Its **rank** (`Engine.rank`)
falls at every transition (`Engine.step_rank`), lexicographically:

1. the calls of the bounds with no table yet (`openCalls`): opening a table
   lowers it;
2. for every table, the answers of the bounds it does not have yet
   (`openAnswers`): recording an answer the run schedules lowers it;
3. the weights of every generator's branches (`branches`), in the multiset
   order (`Tabled/Multiset`): every machine transition lowers it
   (`step_lower`), and a generator's first step weighs its root above every
   clause body (`Engine.rootWeight`);
4. the generators and their choice points (`points`): completing a component
   pops its generators, and dropping an empty choice point lowers it.

The bounds are finite lists (`Bounds.calls`, `Bounds.answers`), so the rank is
well-founded (`RunLower.wellFounded`), and the run is a total function with no
fuel (`Engine.runToEnd`). At most `|Bounds.calls|` tables are opened: the
predicates, the input lists of at most `arity` data terms, and the contexts
of at most `|assumptions|` assumptions, S23's count of distinct calls. -/

namespace AnthillModKbSpec.Tabled

open Machine

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  [FreshNames Variable]

attribute [local instance] termEq

/-! ## The calls and answers of the bounds -/

/-- Every list of at most `count` items drawn from `items`. -/
def upTo {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | count + 1, items => [] :: items.flatMap fun item => (upTo count items).map (item :: ·)

theorem mem_upTo {α : Type} {items : List α} : ∀ {count : Nat} {list : List α}, list.length ≤ count →
    (∀ item ∈ list, item ∈ items) → list ∈ upTo count items
  | 0, [], _, _ => List.mem_singleton_self _
  | 0, _ :: _, short, _ => by simp at short
  | _ + 1, [], _, _ => List.mem_cons_self
  | count + 1, item :: rest, short, drawn => by
      refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨item, drawn item List.mem_cons_self, ?_⟩)
      exact List.mem_map.mpr ⟨rest, mem_upTo (by simp at short; omega) (fun other inside => drawn other (List.mem_cons_of_mem _ inside)), rfl⟩

namespace Bounds

variable (bounds : Bounds Variable Literal Symbol)

/-- The calls a bounded run may table. -/
def calls : List (Call Variable Literal Symbol) :=
  bounds.predicates.flatMap fun predicate => (upTo bounds.arity bounds.data).flatMap fun inputs =>
    (upTo bounds.assumptions.length bounds.assumptions).map fun context => ⟨predicate, inputs, context⟩

/-- The answers a bounded run may schedule. -/
def answers : List (Term Variable Literal Symbol) :=
  bounds.predicates.flatMap fun predicate => (upTo bounds.arity bounds.data).map (.app predicate)

end Bounds

namespace Engine

variable (engine : Engine Variable Literal Symbol)

omit [FreshNames Variable] in
theorem admits_calls {bounds : Bounds Variable Literal Symbol} (bounded : engine.bounds = some bounds) {symbol : Symbol}
    {inputs : List (Term Variable Literal Symbol)} {context : ProofContext Variable Literal Symbol}
    (admitted : engine.admits symbol inputs context = true) : (⟨symbol, inputs, context⟩ : Call Variable Literal Symbol) ∈ bounds.calls := by
  unfold admits at admitted
  rw [bounded] at admitted
  simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq, List.all_eq_true] at admitted
  obtain ⟨⟨⟨⟨predicate, short⟩, data⟩, drawn⟩, distinct⟩ := admitted
  refine List.mem_flatMap.mpr ⟨symbol, predicate, List.mem_flatMap.mpr ⟨inputs, mem_upTo short data, ?_⟩⟩
  refine List.mem_map.mpr ⟨context, mem_upTo (distinct.length_le_of_subset fun term inside => drawn term inside) drawn, rfl⟩

omit [FreshNames Variable] in
theorem inSpace_answers {bounds : Bounds Variable Literal Symbol} (bounded : engine.bounds = some bounds)
    {atom : Term Variable Literal Symbol} (inside : engine.inSpace atom = true) : atom ∈ bounds.answers := by
  unfold inSpace at inside
  rw [bounded] at inside
  dsimp only at inside
  split at inside
  · rename_i symbol args
    simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq, List.all_eq_true] at inside
    obtain ⟨⟨predicate, short⟩, data⟩ := inside
    exact List.mem_flatMap.mpr ⟨symbol, predicate, List.mem_map.mpr ⟨args, mem_upTo short data, rfl⟩⟩
  · cases inside

omit [FreshNames Variable] in
theorem callOfAtom_calls {bounds : Bounds Variable Literal Symbol} (bounded : engine.bounds = some bounds)
    {store : Store Variable Literal Symbol} {symbol : Symbol} {args : List (Term Variable Literal Symbol)}
    {context : ProofContext Variable Literal Symbol} {call : Call Variable Literal Symbol}
    (found : engine.callOfAtom store symbol args context = some call) : call ∈ bounds.calls := by
  unfold callOfAtom at found
  split at found
  · cases found
  · split at found
    · split at found
      · rename_i checked
        cases found
        simp only [Bool.and_eq_true] at checked
        exact engine.admits_calls bounded checked.2
      · cases found
    · cases found

/-! ## The rank of a run -/

/-- A generator's branches: its root, before its first step, weighs above
every clause body. -/
def generatorWeights (generator : Generator Variable Literal Symbol) : List (Nat × Nat) :=
  if generator.started then weights engine.hoApplySymbol generator.state
  else weightsWith engine.hoApplySymbol (max engine.rootWeight (focusSize engine.hoApplySymbol generator.state.focus))
    generator.state

/-- The calls of the bounds with no table. -/
def openCalls (bounds : Bounds Variable Literal Symbol) (run : Run Variable Literal Symbol) : Nat :=
  (bounds.calls.filter fun call => !run.tables.any fun table => table.call.same call).length

/-- A table's answers still to come from the bounds. -/
def tableOpen (bounds : Bounds Variable Literal Symbol) (table : Table Variable Literal Symbol) : Nat :=
  (bounds.answers.filter fun atom => !table.answers.any fun answer => decide (answer.atom = atom)).length

/-- Every table's answers still to come from the bounds. -/
def openAnswers (bounds : Bounds Variable Literal Symbol) (run : Run Variable Literal Symbol) : Nat :=
  (run.tables.map (tableOpen bounds)).sum

/-- The weights of every generator's branches. -/
def branches (run : Run Variable Literal Symbol) : List (Nat × Nat) :=
  run.stack.flatMap engine.generatorWeights

/-- The generators and their choice points. -/
def points (run : Run Variable Literal Symbol) : Nat :=
  (run.stack.map fun generator => generator.state.choices.length + 1).sum

/-- The rank of a run. -/
def rank (bounds : Bounds Variable Literal Symbol) (run : Run Variable Literal Symbol) :
    Nat × Nat × List (Nat × Nat) × Nat :=
  (openCalls bounds run, openAnswers bounds run, engine.branches run, points run)

end Engine

/-- The order on ranks: lexicographic, the branches in the multiset order. -/
def RunLower : Nat × Nat × List (Nat × Nat) × Nat → Nat × Nat × List (Nat × Nat) × Nat → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (Lower Below) (· < ·)))

theorem RunLower.wellFounded : WellFounded RunLower := by
  have inner : WellFounded (Prod.Lex (Lower Below) (· < · : Nat → Nat → Prop)) :=
    ⟨fun (a, b) => Prod.lexAccessible ((Lower.wellFounded Below.wellFounded).apply a) Nat.lt_wfRel.wf.apply b⟩
  have middle : WellFounded (Prod.Lex (· < · : Nat → Nat → Prop) (Prod.Lex (Lower Below) (· < · : Nat → Nat → Prop))) :=
    ⟨fun (a, b) => Prod.lexAccessible (Nat.lt_wfRel.wf.apply a) inner.apply b⟩
  exact ⟨fun (a, b) => Prod.lexAccessible (Nat.lt_wfRel.wf.apply a) middle.apply b⟩


/-! ## Bookkeeping -/

section Lists

variable {α : Type}

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem split_found {items : List α} {position : Nat} {item : α} (found : items[position]? = some item) :
    items = items.take position ++ item :: items.drop (position + 1) := by
  obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp found
  conv => lhs; rw [← List.take_append_drop position items]
  rw [List.drop_eq_getElem_cons bound, same]

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem updateAt_split {items : List α} {position : Nat} {item : α} (found : items[position]? = some item) (change : α → α) :
    Engine.updateAt items position change = items.take position ++ change item :: items.drop (position + 1) := by
  induction items generalizing position with
  | nil => simp at found
  | cons first rest ih =>
      cases position with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst found; rfl
      | succ position => simp only [List.getElem?_cons_succ] at found; simp [Engine.updateAt, ih found]

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem sum_updateAt (weight : α → Nat) {items : List α} {position : Nat} {item : α} (found : items[position]? = some item)
    (change : α → α) : ((Engine.updateAt items position change).map weight).sum + weight item = (items.map weight).sum + weight (change item) := by
  rw [updateAt_split found]
  conv => rhs; rw [split_found found]
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  omega

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem length_filter_le_of {items : List α} {p q : α → Bool} (smaller : ∀ item ∈ items, q item = true → p item = true) :
    (items.filter q).length ≤ (items.filter p).length := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      have rest' := ih fun other member => smaller other (List.mem_cons_of_mem _ member)
      cases hq : q item <;> cases hp : p item <;> simp [hq, hp] <;>
        first | omega | exact absurd (smaller item List.mem_cons_self hq) (by simp [hp])

end Lists

namespace Engine

variable (engine : Engine Variable Literal Symbol)

omit [FreshNames Variable] in
theorem call_same_self (call : Call Variable Literal Symbol) : call.same call = true := by
  simp [Call.same]

omit [FreshNames Variable] in
theorem findTable_none {tables : List (Table Variable Literal Symbol)} {call : Call Variable Literal Symbol}
    (none_ : findTable tables call = none) : (tables.any fun table => table.call.same call) = false := by
  unfold findTable at none_
  have missing := List.find?_eq_none.mp (Option.map_eq_none_iff.mp none_)
  apply List.any_eq_false.mpr
  intro table member same
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  exact missing (table, index) (List.mem_zipIdx_iff_getElem?.mpr found) (by simpa using same)

omit [FreshNames Variable] in
theorem openCalls_congr {bounds : Bounds Variable Literal Symbol} {run other : Run Variable Literal Symbol}
    (same : other.tables.map Table.call = run.tables.map Table.call) : openCalls bounds other = openCalls bounds run := by
  unfold openCalls
  congr 2
  funext call
  have rewrite : ∀ tables : List (Table Variable Literal Symbol),
      (tables.any fun table => table.call.same call) = ((tables.map Table.call).any fun found => found.same call) := by
    intro tables; simp [List.any_map, Function.comp_def]
  rw [rewrite, rewrite run.tables, same]

omit [FreshNames Variable] in
theorem openAnswers_congr {bounds : Bounds Variable Literal Symbol} {run other : Run Variable Literal Symbol}
    (same : other.tables.map Table.answers = run.tables.map Table.answers) : openAnswers bounds other = openAnswers bounds run := by
  unfold openAnswers
  have rewrite : ∀ tables : List (Table Variable Literal Symbol),
      tables.map (tableOpen bounds) = (tables.map Table.answers).map fun answers =>
        (bounds.answers.filter fun atom => !answers.any fun answer => decide (answer.atom = atom)).length := by
    intro tables; simp [List.map_map, Function.comp_def, tableOpen]
  rw [rewrite, rewrite run.tables, same]

end Engine


/-! ## Building rank steps -/

theorem RunLower.of_calls {a b : Nat × Nat × List (Nat × Nat) × Nat} (lt : a.1 < b.1) : RunLower a b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; exact Prod.Lex.left _ _ lt

theorem RunLower.of_answers {a b : Nat × Nat × List (Nat × Nat) × Nat} (calls : a.1 = b.1) (lt : a.2.1 < b.2.1) :
    RunLower a b := by
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
  simp only at calls lt; subst calls; exact Prod.Lex.right _ (Prod.Lex.left _ _ lt)

theorem RunLower.of_branches {a b : Nat × Nat × List (Nat × Nat) × Nat} (calls : a.1 = b.1) (answers : a.2.1 = b.2.1)
    (lower : Lower Below a.2.2.1 b.2.2.1) : RunLower a b := by
  obtain ⟨a1, a2, a3, a4⟩ := a; obtain ⟨b1, b2, b3, b4⟩ := b
  simp only at calls answers lower; subst calls answers; exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.left _ _ lower))

theorem RunLower.of_points {a b : Nat × Nat × List (Nat × Nat) × Nat} (calls : a.1 = b.1) (answers : a.2.1 = b.2.1)
    (same : a.2.2.1 = b.2.2.1) (lt : a.2.2.2 < b.2.2.2) : RunLower a b := by
  obtain ⟨a1, a2, a3, a4⟩ := a; obtain ⟨b1, b2, b3, b4⟩ := b
  simp only at calls answers same lt; subst calls answers same; exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _ lt))

/-! ## Machine finishes -/

section Finish

variable {hoApplySymbol : Symbol}

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
/-- A machine step finishes only with nothing left, or with a success, whose
resume state has failed. -/
theorem step_finished {strategy : Strategy Variable Literal Symbol (Term Variable Literal Symbol)}
    {state : State Variable Literal Symbol (Term Variable Literal Symbol) Unit}
    {outcome : Machine.Outcome Variable Literal Symbol (Term Variable Literal Symbol) Unit}
    (stepped : Machine.step strategy state = .finished outcome) :
    State.done state = true ∨ ∃ proof tree, outcome = .success proof { state with focus := .failed } ∧ state.focus = .proved tree := by
  cases hfocus : state.focus with
  | solve obligation =>
      simp only [Machine.step, hfocus] at stepped
      repeat' split at stepped
      all_goals cases stepped
  | proved tree =>
      cases hframes : state.frames with
      | nil =>
          simp only [Machine.step, hfocus, hframes] at stepped
          split at stepped
          · cases stepped; exact .inr ⟨_, tree, rfl, rfl⟩
          · repeat' split at stepped
            all_goals cases stepped
      | cons continuation rest =>
          simp only [Machine.step, hfocus, hframes] at stepped
          repeat' split at stepped
          all_goals first | (cases stepped; done) | (exfalso; simp_all)
  | failed =>
      cases hchoices : state.choices with
      | nil => left; simp [State.done, hfocus, hchoices]
      | cons point rest =>
          simp only [Machine.step, hfocus, hchoices] at stepped
          repeat' split at stepped
          all_goals cases stepped

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem done_weights {state : State Variable Literal Symbol (Term Variable Literal Symbol) Unit} (done : State.done state = true)
    (top : Nat) : weightsWith hoApplySymbol top state = [] := by
  unfold State.done at done
  split at done
  · rename_i focus choices
    simp [weightsWith, focus, choices, branchElement]
  · cases done

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem success_lower {state : State Variable Literal Symbol (Term Variable Literal Symbol) Unit}
    {tree : ProofTree Variable Literal Symbol (Term Variable Literal Symbol)} (focus : state.focus = .proved tree) (top : Nat) :
    Lower Below (weights hoApplySymbol { state with focus := .failed }) (weightsWith hoApplySymbol top state) := by
  simp only [weights, weightsWith, focus, branchElement, List.nil_append, List.singleton_append]
  exact Lower.erase _ _

end Finish

namespace Engine

variable (engine : Engine Variable Literal Symbol)

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem generatorWeights_done {generator : Generator Variable Literal Symbol} (done : State.done generator.state = true) :
    engine.generatorWeights generator = [] := by
  unfold generatorWeights
  split
  · exact done_weights done _
  · exact done_weights done _

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem branches_split {run : Run Variable Literal Symbol} {position : Nat} {generator : Generator Variable Literal Symbol}
    (found : run.stack[position]? = some generator) :
    engine.branches run = (run.stack.take position).flatMap engine.generatorWeights ++ engine.generatorWeights generator ++
      (run.stack.drop (position + 1)).flatMap engine.generatorWeights := by
  unfold branches
  conv => lhs; rw [split_found found]
  simp [List.flatMap_append, List.append_assoc]

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem branches_updateAt {run : Run Variable Literal Symbol} {position : Nat} {generator : Generator Variable Literal Symbol}
    (found : run.stack[position]? = some generator) (change : Generator Variable Literal Symbol → Generator Variable Literal Symbol)
    (gaps : List (Gap Variable Literal Symbol)) :
    engine.branches { run with stack := updateAt run.stack position change, gaps := gaps } =
      (run.stack.take position).flatMap engine.generatorWeights ++ engine.generatorWeights (change generator) ++
        (run.stack.drop (position + 1)).flatMap engine.generatorWeights := by
  unfold branches
  rw [updateAt_split found]
  simp [List.flatMap_append, List.append_assoc]

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem points_updateAt {run : Run Variable Literal Symbol} {position : Nat} {generator : Generator Variable Literal Symbol}
    (found : run.stack[position]? = some generator) (change : Generator Variable Literal Symbol → Generator Variable Literal Symbol)
    (gaps : List (Gap Variable Literal Symbol)) :
    points { run with stack := updateAt run.stack position change, gaps := gaps } + (generator.state.choices.length + 1) =
      points run + ((change generator).state.choices.length + 1) :=
  sum_updateAt (fun generator => generator.state.choices.length + 1) found change

/-- Recording an answer keeps the calls; it lowers the answers still to come
when the run schedules it, and otherwise keeps the generators. -/
theorem answer_rank {bounds : Bounds Variable Literal Symbol} (bounded : engine.bounds = some bounds)
    (run : Run Variable Literal Symbol) (index : Nat) (atom : Term Variable Literal Symbol)
    (proof : CompletedProof Variable Literal Symbol (Term Variable Literal Symbol) Unit) :
    openCalls bounds (engine.answer run index atom proof) = openCalls bounds run ∧
      (openAnswers bounds (engine.answer run index atom proof) < openAnswers bounds run ∨
        ((engine.answer run index atom proof).stack = run.stack ∧
          openAnswers bounds (engine.answer run index atom proof) = openAnswers bounds run)) := by
  unfold answer
  cases hfound : run.tables[index]? with
  | none => exact ⟨rfl, .inr ⟨rfl, rfl⟩⟩
  | some table =>
      simp only []
      split
      · exact ⟨rfl, .inr ⟨rfl, rfl⟩⟩
      · rename_i fresh
        let change : Table Variable Literal Symbol → Table Variable Literal Symbol :=
          fun table => { table with answers := table.answers ++ [⟨atom, proof⟩] }
        have calls : ∀ (stack : List (Generator Variable Literal Symbol)) (gaps : List (Gap Variable Literal Symbol)),
            openCalls bounds { tables := updateTable run.tables index change, stack := stack, gaps := gaps } = openCalls bounds run :=
          fun _ _ => openCalls_congr (by unfold updateTable; exact map_updateAt Table.call (change := change) (fun _ => rfl) run.tables index)
        have sum := sum_updateAt (tableOpen bounds) hfound change
        have le : tableOpen bounds (change table) ≤ tableOpen bounds table := by
          apply length_filter_le_of
          intro other _ after
          simp only [change, List.any_append, Bool.not_or, Bool.and_eq_true] at after
          exact after.1
        have answers : ∀ (stack : List (Generator Variable Literal Symbol)) (gaps : List (Gap Variable Literal Symbol)),
            openAnswers bounds { tables := updateTable run.tables index change, stack := stack, gaps := gaps } +
              tableOpen bounds table = openAnswers bounds run + tableOpen bounds (change table) := fun _ _ => sum
        have general : ∀ (stack : List (Generator Variable Literal Symbol)) (gaps : List (Gap Variable Literal Symbol)),
            openAnswers bounds { tables := updateTable run.tables index change, stack := stack, gaps := gaps } ≤
              openAnswers bounds run := fun stack gaps => by have := answers stack gaps; omega
        have choose : ∀ other : Run Variable Literal Symbol, other.stack = run.stack →
            openAnswers bounds other ≤ openAnswers bounds run →
              openAnswers bounds other < openAnswers bounds run ∨
                (other.stack = run.stack ∧ openAnswers bounds other = openAnswers bounds run) :=
          fun _ same le => (Nat.lt_or_eq_of_le le).imp id fun eq => ⟨same, eq⟩
        cases space : engine.inSpace atom
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨calls _ _, (Nat.lt_or_eq_of_le (general _ _)).imp id fun eq => ⟨trivial, eq⟩⟩
        · simp only [↓reduceIte]
          refine ⟨calls _ _, .inl ?_⟩
          have lt : tableOpen bounds (change table) < tableOpen bounds table := by
            apply filter_length_lt
            · intro other _ after
              simp only [change, List.any_append, Bool.not_or, Bool.and_eq_true] at after
              exact after.1
            · refine ⟨atom, engine.inSpace_answers bounded space, by simpa using fresh, ?_⟩
              simp [change]
          have strict : ∀ (stack : List (Generator Variable Literal Symbol)) (gaps : List (Gap Variable Literal Symbol)),
              openAnswers bounds { tables := updateTable run.tables index change, stack := stack, gaps := gaps } <
                openAnswers bounds run := fun stack gaps => by have := answers stack gaps; omega
          exact strict _ _

/-- Opening a new call's table lowers the calls without a table. -/
theorem open_rank {bounds : Bounds Variable Literal Symbol} {run : Run Variable Literal Symbol} {symbol : Symbol}
    {args : List (Term Variable Literal Symbol)} {call : Call Variable Literal Symbol} (inBounds : call ∈ bounds.calls)
    (fresh : findTable run.tables call = none) :
    RunLower (engine.rank bounds (engine.open_ run symbol args call)) (engine.rank bounds run) := by
  apply RunLower.of_calls
  simp only [rank, openCalls, open_]
  apply filter_length_lt
  · intro other _ after
    simp only [List.any_append, Bool.not_or, Bool.and_eq_true] at after
    exact after.1
  · refine ⟨call, inBounds, by simp [findTable_none fresh], ?_⟩
    simp [call_same_self]

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem fold_complete_tables (clear : Table Variable Literal Symbol → Table Variable Literal Symbol)
    (calls : ∀ table, (clear table).call = table.call) (answers : ∀ table, (clear table).answers = table.answers) :
    ∀ (ids : List Nat) (tables : List (Table Variable Literal Symbol)),
      (ids.foldl (fun tables index => updateAt tables index clear) tables).map Table.call = tables.map Table.call ∧
        (ids.foldl (fun tables index => updateAt tables index clear) tables).map Table.answers = tables.map Table.answers
  | [], _ => ⟨rfl, rfl⟩
  | index :: rest, tables => by
      simp only [List.foldl_cons]
      obtain ⟨one, two⟩ := fold_complete_tables clear calls answers rest (updateAt tables index clear)
      exact ⟨one.trans (map_updateAt _ calls _ _), two.trans (map_updateAt _ answers _ _)⟩

/-- Completing a component pops generators with nothing left: the points fall. -/
theorem complete_rank {bounds : Bounds Variable Literal Symbol} {run next : Run Variable Literal Symbol} {count : Nat}
    (positive : 0 < count) (short : count ≤ run.stack.length)
    (done : ∀ generator ∈ run.stack.take count, State.done generator.state = true)
    (completed : complete? run count = some next) : RunLower (engine.rank bounds next) (engine.rank bounds run) := by
  unfold complete? at completed
  dsimp only at completed
  split at completed
  · split at completed
    · cases completed
      obtain ⟨calls, answers⟩ := fold_complete_tables (fun table => { table with complete := true, waiters := [] })
        (fun _ => rfl) (fun _ => rfl) ((run.stack.take count).filterMap Generator.table) run.tables
      have empty : (run.stack.take count).flatMap engine.generatorWeights = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro generator member
        exact engine.generatorWeights_done (done generator member)
      apply RunLower.of_points
      · exact openCalls_congr calls
      · exact openAnswers_congr answers
      · show (run.stack.drop count).flatMap engine.generatorWeights = engine.branches run
        unfold branches
        conv => rhs; rw [← List.take_append_drop count run.stack]
        rw [List.flatMap_append, empty, List.nil_append]
      · show points { run with stack := run.stack.drop count } < points run
        unfold points
        conv => rhs; rw [← List.take_append_drop count run.stack]
        rw [List.map_append, List.sum_append]
        have : 0 < ((run.stack.take count).map fun generator => generator.state.choices.length + 1).sum := by
          have length : (run.stack.take count).length = count := List.length_take_of_le short
          obtain ⟨first, rest, split⟩ : ∃ first rest, run.stack.take count = first :: rest := by
            cases h : run.stack.take count with
            | nil => rw [h] at length; simp at length; omega
            | cons first rest => exact ⟨first, rest, rfl⟩
          rw [split]; simp only [List.map_cons, List.sum_cons]; omega
        simp only
        omega
    · cases completed
  · cases completed

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem take_updateAt {α : Type} : ∀ (items : List α) (position : Nat) (change : α → α),
    (updateAt items position change).take position = items.take position
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | first :: rest, position + 1, change => by simp [updateAt, take_updateAt rest position change]

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem drop_updateAt {α : Type} : ∀ (items : List α) (position : Nat) (change : α → α),
    (updateAt items position change).drop (position + 1) = items.drop (position + 1)
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | first :: rest, position + 1, change => by simp [updateAt, drop_updateAt rest position change]

/-- The rank of a run with the branches at one position weighed `around`. -/
def around (bounds : Bounds Variable Literal Symbol) (run : Run Variable Literal Symbol) (position : Nat)
    (here : List (Nat × Nat)) : Nat × Nat × List (Nat × Nat) × Nat :=
  (openCalls bounds run, openAnswers bounds run,
    (run.stack.take position).flatMap engine.generatorWeights ++ here ++
      (run.stack.drop (position + 1)).flatMap engine.generatorWeights, points run)

omit [FreshNames Variable] in
theorem rank_around {bounds : Bounds Variable Literal Symbol} {run : Run Variable Literal Symbol} {position : Nat}
    {generator : Generator Variable Literal Symbol} (found : run.stack[position]? = some generator) :
    engine.rank bounds run = engine.around bounds run position (engine.generatorWeights generator) := by
  simp only [rank, around]; rw [engine.branches_split found]

omit [FreshNames Variable] in
/-- Changing a generator at a position without changing its state, its
start, or its choice points, and the tables without changing their calls or
answers, keeps the rank around it. -/
theorem around_keep {bounds : Bounds Variable Literal Symbol} {run : Run Variable Literal Symbol} {position : Nat}
    {generator : Generator Variable Literal Symbol} (found : run.stack[position]? = some generator)
    (change : Generator Variable Literal Symbol → Generator Variable Literal Symbol)
    (keeps : (change generator).state = generator.state)
    (tables : List (Table Variable Literal Symbol)) (calls : tables.map Table.call = run.tables.map Table.call)
    (answers : tables.map Table.answers = run.tables.map Table.answers) (gaps : List (Gap Variable Literal Symbol))
    (here : List (Nat × Nat)) :
    engine.around bounds { tables := tables, stack := updateAt run.stack position change, gaps := gaps } position here =
      engine.around bounds run position here := by
  have pointsEq := sum_updateAt (fun generator => generator.state.choices.length + 1) found change
  rw [keeps] at pointsEq
  simp only [around, take_updateAt, drop_updateAt]
  rw [openCalls_congr (run := run) calls, openAnswers_congr (run := run) answers]
  congr 1
  congr 1
  congr 1
  show ((updateAt run.stack position change).map fun generator => generator.state.choices.length + 1).sum =
    (run.stack.map fun generator => generator.state.choices.length + 1).sum
  omega

omit [FreshNames Variable] in
/-- Leaving a branch waiting keeps the rank around its generator. -/
theorem wait_around {bounds : Bounds Variable Literal Symbol} {run : Run Variable Literal Symbol} {position : Nat}
    {generator : Generator Variable Literal Symbol} (found : run.stack[position]? = some generator) (index : Nat)
    (negative : Bool) (here : List (Nat × Nat)) :
    ∃ waiting, (wait run position index negative).stack[position]? = some waiting ∧ waiting.state = generator.state ∧
      waiting.started = generator.started ∧
      engine.around bounds (wait run position index negative) position here = engine.around bounds run position here := by
  unfold wait
  rw [found]
  dsimp only
  cases focus : generator.state.focus with
  | solve obligation =>
      refine ⟨{ generator with dep := min generator.dep index }, ?_, rfl, rfl, ?_⟩
      · show (updateAt run.stack position _)[position]? = _
        rw [getElem?_updateAt, ite_eq_left rfl, found]; rfl
      · exact engine.around_keep found _ rfl _ (by unfold updateTable; apply map_updateAt; intro; rfl)
          (by unfold updateTable; apply map_updateAt; intro; rfl) _ here
  | proved _ => exact ⟨generator, found, rfl, rfl, rfl⟩
  | failed => exact ⟨generator, found, rfl, rfl, rfl⟩

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem fit_fits {bounds : Bounds Variable Literal Symbol} (bounded : engine.bounds = some bounds) {top : Nat} (two : 2 ≤ top)
    (response : Response Variable Literal Symbol (Term Variable Literal Symbol)) :
    ∀ expansion ∈ (engine.fit top response).alternatives, Fits engine.hoApplySymbol top expansion := by
  intro expansion member
  unfold fit at member
  rw [bounded] at member
  dsimp only at member
  cases response with
  | candidates alternatives =>
      simp only [fitTo] at member
      by_cases all : (alternatives.all fun expansion => decide (Fits engine.hoApplySymbol top expansion)) = true
      · simp only [all, ↓reduceIte] at member
        exact of_decide_eq_true (List.all_eq_true.mp all expansion member)
      · simp only [all, Bool.false_eq_true, ↓reduceIte] at member
        exact of_decide_eq_true (List.mem_filter.mp member).2
  | incomplete alternatives =>
      unfold fitTo at member
      exact of_decide_eq_true (List.mem_filter.mp member).2
  | negate certificate =>
      simp only [fitTo, Response.alternatives, List.mem_singleton] at member
      subst member
      simp only [Fits, startCost, Expansion.negation]; omega
  | unsupported => simp [fitTo, Response.alternatives] at member
  | delay _ => simp [fitTo, Response.alternatives] at member
  | opened => simp [fitTo, Response.alternatives] at member

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem fits_mono {top larger : Nat} {expansion : Expansion Variable Literal Symbol (Term Variable Literal Symbol)}
    (fits : Fits engine.hoApplySymbol top expansion) (le : top ≤ larger) : Fits engine.hoApplySymbol larger expansion := by
  unfold Fits at fits ⊢; omega

/-- A machine transition of a started generator lowers the rank around it,
its branches weighed `top`. -/
theorem advance_rank {bounds : Bounds Variable Literal Symbol} (bounded : engine.bounds = some bounds)
    {run : Run Variable Literal Symbol} {position : Nat} {stored generator : Generator Variable Literal Symbol}
    (found : run.stack[position]? = some stored) (sameState : stored.state = generator.state) (started : stored.started = true)
    (live : State.done generator.state = false) {strategy : Strategy Variable Literal Symbol (Term Variable Literal Symbol)}
    {top : Nat}
    (heavy : ∀ obligation, generator.state.focus = .solve obligation → goalSize engine.hoApplySymbol obligation.goal ≤ top ∧
      ∀ expansion ∈ (strategy obligation generator.state.store).alternatives, Fits engine.hoApplySymbol top expansion)
    {next : Run Variable Literal Symbol} (advanced : engine.advance run position generator strategy = .running next) :
    RunLower (engine.rank bounds next) (engine.around bounds run position (weightsWith engine.hoApplySymbol top generator.state)) := by
  unfold advance at advanced
  cases hstep : Machine.step strategy generator.state with
  | running state =>
      rw [hstep] at advanced
      cases advanced
      have low := step_lower (hoApplySymbol := engine.hoApplySymbol) strategy hstep heavy
      have branchesEq := engine.branches_updateAt found (fun generator => { generator with state := state }) run.gaps
      have genEq : engine.generatorWeights { stored with state := state } = weights engine.hoApplySymbol state := by
        simp [generatorWeights, started]
      have pointsEq := points_updateAt found (fun generator => { generator with state := state }) run.gaps
      rcases low with lower | ⟨equal, fewer⟩
      · apply RunLower.of_branches
        · rfl
        · rfl
        show Lower Below (engine.branches _) _
        rw [branchesEq, genEq]
        exact (lower.append_left _).append_right _
      · apply RunLower.of_points
        · rfl
        · rfl
        · show engine.branches _ = _
          rw [branchesEq, genEq, equal]
          rfl
        · show points _ < points run
          simp only at pointsEq
          rw [sameState] at pointsEq
          omega
  | finished outcome =>
      rcases step_finished hstep with done | ⟨proof, tree, rfl, proved⟩
      · rw [live] at done; cases done
      · rw [hstep] at advanced
        dsimp only at advanced
        have branchesEq := engine.branches_updateAt found
          (fun generator' => { generator' with state := { generator.state with focus := .failed } }) run.gaps
        have genEq : engine.generatorWeights { stored with state := { generator.state with focus := .failed } } =
            weights engine.hoApplySymbol { generator.state with focus := .failed } := by
          simp [generatorWeights, started]
        have lower : Lower Below
            (engine.branches { run with stack := updateAt run.stack position fun generator' =>
              { generator' with state := { generator.state with focus := .failed } } })
            ((run.stack.take position).flatMap engine.generatorWeights ++ weightsWith engine.hoApplySymbol top generator.state ++
              (run.stack.drop (position + 1)).flatMap engine.generatorWeights) := by
          rw [branchesEq, genEq]; exact ((success_lower proved top).append_left _).append_right _
        cases htable : generator.table with
        | none => rw [htable] at advanced; cases advanced
        | some index =>
            rw [htable] at advanced
            dsimp only at advanced
            split at advanced
            · cases advanced
              obtain ⟨calls, answers⟩ := engine.answer_rank bounded
                { run with stack := updateAt run.stack position fun generator' =>
                    { generator' with state := { generator.state with focus := .failed } } } index
                (proof.store.resolve proof.root.goal) proof
              rcases answers with lt | ⟨stackSame, eq⟩
              · exact RunLower.of_answers calls lt
              · apply RunLower.of_branches calls eq
                show Lower Below (engine.branches _) _
                unfold branches at lower ⊢
                rw [stackSame]; exact lower
            · cases advanced
              apply RunLower.of_branches
              · rfl
              · rfl
              exact lower

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem rootWeight_two : 2 ≤ engine.rootWeight := by unfold rootWeight; omega

/-- **Every step of a generator lowers the run's rank.** -/
theorem stepAt_rank {bounds : Bounds Variable Literal Symbol} (bounded : engine.bounds = some bounds)
    {run : Run Variable Literal Symbol} {position : Nat} {generator : Generator Variable Literal Symbol}
    (found : run.stack[position]? = some generator) (live : State.done generator.state = false)
    {next : Run Variable Literal Symbol} (stepped : engine.stepAt run position generator = .running next) :
    RunLower (engine.rank bounds next) (engine.rank bounds run) := by
  unfold stepAt at stepped
  split at stepped
  · -- The root: resolution against the clauses, weighed above every body.
    rename_i notStarted
    have startedFalse : generator.started = false := by simpa using notStarted
    have found₀ : (updateAt run.stack position fun generator => { generator with started := true })[position]? =
        some { generator with started := true } := by
      rw [getElem?_updateAt, ite_eq_left rfl, found]; rfl
    have result := engine.advance_rank bounded (stored := { generator with started := true })
      (generator := { generator with started := true }) found₀ rfl rfl live
      (top := max engine.rootWeight (focusSize engine.hoApplySymbol generator.state.focus))
      (fun obligation focus => ⟨by rw [focus]; exact Nat.le_max_right _ _, fun expansion member =>
        engine.fits_mono (engine.fit_fits bounded engine.rootWeight_two _ expansion member) (Nat.le_max_left _ _)⟩) stepped
    have weightsEq : engine.generatorWeights generator =
        weightsWith engine.hoApplySymbol (max engine.rootWeight (focusSize engine.hoApplySymbol generator.state.focus))
          generator.state := by
      simp [generatorWeights, startedFalse]
    rw [engine.rank_around found, weightsEq]
    rw [engine.around_keep found (fun generator => { generator with started := true }) rfl run.tables rfl rfl run.gaps]
      at result
    exact result
  · rename_i isStarted
    have startedTrue : generator.started = true := by simpa using isStarted
    have weightsEq : engine.generatorWeights generator =
        weightsWith engine.hoApplySymbol (focusSize engine.hoApplySymbol generator.state.focus) generator.state := by
      simp [generatorWeights, startedTrue, weights]
    have heavy : ∀ obligation, generator.state.focus = .solve obligation →
        goalSize engine.hoApplySymbol obligation.goal ≤ focusSize engine.hoApplySymbol generator.state.focus ∧
          ∀ expansion ∈ (engine.strategy run.tables obligation generator.state.store).alternatives,
            Fits engine.hoApplySymbol (focusSize engine.hoApplySymbol generator.state.focus) expansion := by
      intro obligation focus
      rw [focus]
      exact ⟨Nat.le_refl _, engine.fit_fits bounded (two_le_goalSize _ _) _⟩
    have plain : ∀ next, engine.advance run position generator (engine.strategy run.tables) = .running next →
        RunLower (engine.rank bounds next) (engine.rank bounds run) := by
      intro _ advanced
      rw [engine.rank_around found, weightsEq]
      exact engine.advance_rank bounded found rfl startedTrue live heavy advanced
    have waited : ∀ index negative next,
        engine.advance (wait run position index negative) position generator (engine.strategy run.tables) = .running next →
        RunLower (engine.rank bounds next) (engine.rank bounds run) := by
      intro index negative next advanced
      obtain ⟨waiting, waitingFound, sameState, sameStarted, aroundEq⟩ := engine.wait_around (bounds := bounds) found index negative
        (weightsWith engine.hoApplySymbol (focusSize engine.hoApplySymbol generator.state.focus) generator.state)
      rw [engine.rank_around found, weightsEq, ← aroundEq]
      exact engine.advance_rank bounded waitingFound sameState (sameStarted.trans startedTrue) live heavy advanced
    split at stepped
    · rename_i obligation focus
      split at stepped
      · rename_i call callFound
        split at stepped
        · rename_i index table tableFound
          dsimp only at stepped
          split at stepped
          · exact plain _ stepped
          · exact waited _ _ _ stepped
        · split at stepped
          · rename_i symbol args reads
            cases stepped
            exact engine.open_rank (engine.callOfAtom_calls bounded (call?_app callFound reads)) ‹_›
          · exact plain _ stepped
      · split at stepped
        · rename_i symbol args _ reads
          split at stepped
          · split at stepped
            · rename_i call callFound
              split at stepped
              · cases stepped
                exact engine.open_rank (engine.callOfAtom_calls bounded callFound) ‹_›
              · split at stepped
                · exact plain _ stepped
                · exact waited _ _ _ stepped
            · exact plain _ stepped
          · exact plain _ stepped
        · exact plain _ stepped
    · exact plain _ stepped

/-- **Every transition of a bounded run lowers its rank.** -/
theorem step_rank {bounds : Bounds Variable Literal Symbol} (bounded : engine.bounds = some bounds)
    {run next : Run Variable Literal Symbol} (stepped : engine.step run = .running next) :
    RunLower (engine.rank bounds next) (engine.rank bounds run) := by
  unfold Engine.step at stepped
  split at stepped
  · cases stepped
  · rename_i position located
    obtain ⟨bound, live, before⟩ := List.findIdx?_eq_some_iff_getElem.mp located
    split at stepped
    · rename_i completed completedEq
      cases stepped
      split at completedEq
      · cases completedEq
      · rename_i nonzero
        refine engine.complete_rank (by omega) (Nat.le_of_lt bound) (fun generator member => ?_) completedEq
        obtain ⟨index, indexBound, rfl⟩ := List.mem_take_iff_getElem.mp member
        have := before index (by omega)
        simpa using this
    · split at stepped
      · rename_i generator found
        have same : run.stack[position] = generator := by
          rw [List.getElem?_eq_getElem bound] at found; exact Option.some.inj found
        have liveGenerator : State.done generator.state = false := by
          rw [← same]; simpa using live
        exact engine.stepAt_rank bounded found liveGenerator stepped
      · cases stepped

/-- The rank, ordered by `RunLower`. -/
structure Rank where
  value : Nat × Nat × List (Nat × Nat) × Nat

instance : WellFoundedRelation Rank := ⟨fun a b => RunLower a.value b.value, InvImage.wf Rank.value RunLower.wellFounded⟩

/-- **A bounded run without fuel**: it steps until it succeeds or finishes,
and terminates because every step lowers its rank. -/
def runToEnd {bounds : Bounds Variable Literal Symbol} (bounded : engine.bounds = some bounds)
    (run : Run Variable Literal Symbol) : Outcome Variable Literal Symbol :=
  match _stepped : engine.step run with
  | .running next => runToEnd bounded next
  | .success proof resume => .success proof resume
  | .finished outcome => .finished outcome
termination_by (⟨engine.rank bounds run⟩ : Rank)
decreasing_by exact engine.step_rank bounded _stepped

/-- The run without fuel is the run with enough fuel: it is never
interrupted. -/
theorem runToEnd_fuel {bounds : Bounds Variable Literal Symbol} (bounded : engine.bounds = some bounds)
    (run : Run Variable Literal Symbol) : ∃ fuel, engine.run fuel run = engine.runToEnd bounded run := by
  rw [runToEnd]
  split
  · rename_i next stepped
    obtain ⟨fuel, same⟩ := runToEnd_fuel bounded next
    exact ⟨fuel + 1, by simp only [Engine.run, stepped]; exact same⟩
  · rename_i proof resume stepped
    exact ⟨1, by simp [Engine.run, stepped]⟩
  · rename_i outcome stepped
    exact ⟨1, by simp [Engine.run, stepped]⟩
termination_by (⟨engine.rank bounds run⟩ : Rank)
decreasing_by exact engine.step_rank bounded ‹_›

/-- A run without fuel is never interrupted. -/
theorem runToEnd_ended {bounds : Bounds Variable Literal Symbol} (bounded : engine.bounds = some bounds)
    (run : Run Variable Literal Symbol) : ∀ final, engine.runToEnd bounded run ≠ .interrupted final := by
  rw [runToEnd]
  split
  · rename_i next stepped
    exact runToEnd_ended bounded next
  · intro final same; cases same
  · intro final same; cases same
termination_by (⟨engine.rank bounds run⟩ : Rank)
decreasing_by exact engine.step_rank bounded ‹_›

end Engine

end AnthillModKbSpec.Tabled
