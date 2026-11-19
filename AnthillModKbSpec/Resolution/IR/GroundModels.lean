import AnthillModKbSpec.Resolution.IR.Exact

/-! # The relevant program's models (S28)

The evaluator decides a closed query of P0 or P1 on the ground form of its
exact relevant program (`Program.groundProgram`): the relevant atoms, the
relevant instances as heads and ground bodies, the denials' and the query's
passing instances as ground bodies, and the query's conditions, all ground.
A **model** of it (`GroundProgram.Model`) is an assignment of the relevant
atoms and of the marker atoms in which each relevant atom holds exactly when
one of its instances' ground bodies does, and no denial body holds: S27's
relevant program's completion (`RelevantHolds`) with the denials read on
their passing instances (`denied_iff`).

- **The body lemma** (`body_holds_iff`): at a ground instance, a body holds in
  a key model exactly when its ground body holds and its fixed literals are
  true.
- **Closure** (`groundProgram_closed`): the atoms an instance's ground body
  reads are relevant atoms, so a model is about the relevant atoms only.
- **Every key fixpoint is a model** (`fixpoint_model`): restricted to the
  relevant atoms, by S27's `relevant_of_fixpoint`; and the query's conditions
  and formula have the same truth in the key model and in its restriction
  (`context_iff`, `formula_iff`). -/

namespace AnthillModKbSpec.IR

open Semantics Completion Tabled Answers

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

attribute [local instance] Machine.termEq

/-- A ground body holds under an interpretation of the closed atoms and one of
the marker atoms: its calls' atoms hold, its NAF literals' atoms do not, and
its marker atoms hold. -/
def GroundBody.Holds (closed marked : GAtom Variable Literal Symbol → Prop) (body : GroundBody Variable Literal Symbol) : Prop :=
  (∀ atom ∈ body.1, closed atom) ∧ (∀ atom ∈ body.2.1, ¬ closed atom) ∧ (∀ atom ∈ body.2.2, marked atom)

/-- A ground program: the relevant atoms, the relevant instances as heads and
ground bodies, the denials' and the query's ground bodies, the ground body of
the query's conditions, and whether their fixed literals are true. -/
structure GroundProgram (Variable Literal Symbol : Type) where
  atoms : List (GAtom Variable Literal Symbol)
  rules : List (GAtom Variable Literal Symbol × GroundBody Variable Literal Symbol)
  denials : List (GroundBody Variable Literal Symbol)
  goals : List (GroundBody Variable Literal Symbol)
  conditions : GroundBody Variable Literal Symbol
  conditionsFixed : Bool

/-- Equality of atom lists, from `termEq`. -/
@[reducible] def atomListEq : DecidableEq (List (GAtom Variable Literal Symbol)) := inferInstance

/-- Equality of ground bodies. -/
@[reducible] def groundBodyEq : DecidableEq (GroundBody Variable Literal Symbol) :=
  @instDecidableEqProd _ _ atomListEq (@instDecidableEqProd _ _ atomListEq atomListEq)

attribute [local instance] atomListEq groundBodyEq in
/-- Equality of ground programs: a certificate is compared with its
recomputation. -/
@[reducible] def groundProgramEq : DecidableEq (GroundProgram Variable Literal Symbol) := fun first second => by
  cases first; cases second
  simp only [GroundProgram.mk.injEq]
  exact inferInstance

namespace GroundProgram

variable (ground : GroundProgram Variable Literal Symbol)

/-- A model of a ground program: every atom holds exactly when one of its
instances' bodies does, and no denial body holds. -/
def Model (closed marked : GAtom Variable Literal Symbol → Prop) : Prop :=
  (∀ atom ∈ ground.atoms, closed atom ↔ ∃ body, (atom, body) ∈ ground.rules ∧ body.Holds closed marked) ∧
    ∀ body ∈ ground.denials, ¬ body.Holds closed marked

/-- The query's conditions hold. -/
def ConditionsHold (closed marked : GAtom Variable Literal Symbol → Prop) : Prop :=
  ground.conditions.Holds closed marked ∧ ground.conditionsFixed = true

/-- The query's goals hold: one of its instances' bodies does. -/
def GoalHolds (closed marked : GAtom Variable Literal Symbol → Prop) : Prop :=
  ∃ body ∈ ground.goals, body.Holds closed marked

/-- The program reads only its atoms: every body's calls and NAF literals are
of its atoms. -/
def Closed : Prop :=
  (∀ entry ∈ ground.rules, entry.1 ∈ ground.atoms ∧ ∀ atom, atom ∈ entry.2.1 ∨ atom ∈ entry.2.2.1 → atom ∈ ground.atoms) ∧
    (∀ body ∈ ground.denials ++ ground.conditions :: ground.goals, ∀ atom, atom ∈ body.1 ∨ atom ∈ body.2.1 → atom ∈ ground.atoms)

end GroundProgram

namespace Program

variable (program : Program Variable Literal Symbol)

/-- The substitution of a closed query's conditions: they have no names. -/
def noNames : Variable → Term Variable Literal Symbol := fun name => .var name

/-- **The ground relevant program** of a closed query of P0 or P1: the level
table and the relevant calls computed once for every part. -/
def groundProgram (query : Query Variable Literal Symbol)
    (closes_ : ∃ n, program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) = true) :
    GroundProgram Variable Literal Symbol :=
  let answers := program.answersWith (program.levelTable (program.vertices query))
  let calls := program.roundsFrom answers query closes_ 0 (program.callRounds answers query 0) rfl
    fun _ lt => absurd lt (Nat.not_lt_zero _)
  ⟨(calls.flatMap (atomsAt answers)).eraseDups, (calls.flatMap (program.instancesOfCall answers)).eraseDups,
    (program.denials.flatMap (program.groundBodies answers [])).eraseDups,
    (program.groundBodies answers query.parameters query.goals).eraseDups, groundBody noNames query.conditions,
    query.conditions.all (program.fixedB noNames)⟩

section Parts

variable {query : Query Variable Literal Symbol}
  {closes_ : ∃ n, program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) = true}

theorem groundProgram_atoms : (program.groundProgram query closes_).atoms = program.relevantAtoms query closes_ := rfl

theorem groundProgram_rules : (program.groundProgram query closes_).rules = program.relevantInstances query closes_ := rfl

theorem groundProgram_denials : (program.groundProgram query closes_).denials = program.denialBodies query := rfl

theorem groundProgram_goals : (program.groundProgram query closes_).goals = program.goalBodies query := rfl

theorem groundProgram_conditions : (program.groundProgram query closes_).conditions = groundBody noNames query.conditions := rfl

end Parts

/-- The interpretation of the closed atoms a key interpretation gives. -/
def closedOf (interp : Interp Literal Symbol) : GAtom Variable Literal Symbol → Prop := fun atom => interp atom.1 (keyArgs atom)

/-! ## The body lemma -/

variable {program}

/-- A marker atom holds in a key model exactly by the markers. -/
theorem key_marker_iff {markers interp : Interp Literal Symbol} {symbol : Symbol}
    {args : List (Term Variable Literal Symbol)} (declared : program.declares (.marker symbol args) = true)
    (data : ∀ arg ∈ args, dataIn program.constructors arg = true) (σ : Variable → Term Variable Literal Symbol) :
    (program.keyModel markers interp).Satisfies (fun name => Open.dataKey (σ name)) (.app symbol args) ↔
      markers symbol ((args.map (subst σ)).map Open.dataKey) := by
  simp only [declares, Bool.and_eq_true, Option.isNone_iff_eq_none, bne_iff_ne, ne_eq] at declared
  obtain ⟨undeclared, ordinary⟩ := declared
  have keysEq : args.map ((program.keyModel markers interp).eval fun name => Open.dataKey (σ name)) =
      (args.map (subst σ)).map Open.dataKey := by
    rw [keys_evalAll_subst _ σ args (dataInAll_of data), List.map_map]
  simp only [Model.Satisfies, Model.eval]
  rw [keysEq]
  show resolveKey program.hoApply _ symbol _ ↔ _
  rw [resolveKey_ordinary _ ordinary, join_open (not_closed_of_none undeclared _)]
  simp [base, undeclared]

/-- **One literal at a ground instance**, by its ground atoms and its fixed
truth. -/
theorem goal_holds_iff (wellFormed : program.WellFormed) {markers interp : Interp Literal Symbol}
    {goal : Goal Variable Literal Symbol} (declared : program.declares goal = true) (data : program.data goal = true)
    {σ : Variable → Term Variable Literal Symbol} (ground : GroundOn program.constructors σ goal.names) :
    (program.keyModel markers interp).Satisfies (fun name => Open.dataKey (σ name)) goal.toTerm ↔
      (∀ atom, goal.callAtom σ = some atom → closedOf interp atom) ∧
        (∀ atom, goal.nafAtom σ = some atom → ¬ closedOf interp atom) ∧
          (∀ atom, goal.markerAtom σ = some atom → closedOf markers atom) ∧ program.fixedB σ goal = true := by
  have allData : ∀ arg ∈ goal.args, dataIn program.constructors arg = true := List.all_eq_true.mp data
  cases goal with
  | call predicate args =>
      rw [show (Goal.call predicate args).toTerm = Term.app predicate args from rfl,
        key_closed_iff wellFormed declared allData σ]
      simp [Goal.callAtom, Goal.nafAtom, Goal.markerAtom, fixedB, closedOf, keyArgs]
  | naf predicate args =>
      rw [show (Goal.naf predicate args).toTerm = Term.defaultNeg (.app predicate args) from rfl,
        sat_neg _ _ (Model.keys_complement _), key_closed_iff wellFormed declared allData σ]
      simp [Goal.callAtom, Goal.nafAtom, Goal.markerAtom, fixedB, closedOf, keyArgs]
  | marker symbol args =>
      rw [show (Goal.marker symbol args).toTerm = Term.app symbol args from rfl, key_marker_iff declared allData σ]
      simp [Goal.callAtom, Goal.nafAtom, Goal.markerAtom, fixedB, closedOf, keyArgs]
  | equal left right =>
      rw [key_fixed_iff wellFormed declared data ground rfl (by intro _ _ same; cases same), ← fixedB_iff]
      simp [Goal.callAtom, Goal.nafAtom, Goal.markerAtom]
  | differ left right =>
      rw [key_fixed_iff wellFormed declared data ground rfl (by intro _ _ same; cases same), ← fixedB_iff]
      simp [Goal.callAtom, Goal.nafAtom, Goal.markerAtom]
  | guard symbol arg =>
      rw [key_fixed_iff wellFormed declared data ground rfl (by intro _ _ same; cases same), ← fixedB_iff]
      simp [Goal.callAtom, Goal.nafAtom, Goal.markerAtom]
  | primitive symbol inputs output =>
      rw [key_fixed_iff wellFormed declared data ground rfl (by intro _ _ same; cases same), ← fixedB_iff]
      simp [Goal.callAtom, Goal.nafAtom, Goal.markerAtom]

/-- **The body lemma**: at a ground instance, a body holds in a key model
exactly when its ground body holds and its fixed literals are true. -/
theorem body_holds_iff (wellFormed : program.WellFormed) {markers interp : Interp Literal Symbol}
    {body : List (Goal Variable Literal Symbol)} (ok : ∀ goal ∈ body, program.declares goal = true ∧ program.data goal = true)
    {σ : Variable → Term Variable Literal Symbol} (ground : GroundOn program.constructors σ (bodyNames body)) :
    (program.keyModel markers interp).Satisfies (fun name => Open.dataKey (σ name)) (bodyTerm body) ↔
      (groundBody σ body).Holds (closedOf interp) (closedOf markers) ∧ body.all (program.fixedB σ) = true := by
  have each : ∀ goal ∈ body, ((program.keyModel markers interp).Satisfies (fun name => Open.dataKey (σ name)) goal.toTerm ↔
      (∀ atom, goal.callAtom σ = some atom → closedOf interp atom) ∧
        (∀ atom, goal.nafAtom σ = some atom → ¬ closedOf interp atom) ∧
          (∀ atom, goal.markerAtom σ = some atom → closedOf markers atom) ∧ program.fixedB σ goal = true) :=
    fun goal member => goal_holds_iff wellFormed (ok goal member).1 (ok goal member).2
      fun name inside => ground name (List.mem_flatMap.mpr ⟨goal, member, inside⟩)
  unfold bodyTerm
  rw [Model.satisfies_conjunction]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, GroundBody.Holds, groundBody,
    List.mem_filterMap, List.all_eq_true]
  constructor
  · intro holds
    refine ⟨⟨fun atom goal member found => ((each goal member).mp (holds goal member)).1 atom found,
      fun atom goal member found => ((each goal member).mp (holds goal member)).2.1 atom found,
      fun atom goal member found => ((each goal member).mp (holds goal member)).2.2.1 atom found⟩,
      fun goal member => ((each goal member).mp (holds goal member)).2.2.2⟩
  · rintro ⟨⟨calls, nafs, marks⟩, fixed⟩ goal member
    exact (each goal member).mpr ⟨fun atom found => calls atom goal member found, fun atom found => nafs atom goal member found,
      fun atom found => marks atom goal member found, fixed goal member⟩

theorem fixedB_of_vertex {σ : Variable → Term Variable Literal Symbol} {goal : Goal Variable Literal Symbol} {bound : List Variable}
    {vertex : Vertex Symbol} (found : goal.vertex? bound = some vertex) : program.fixedB σ goal = true := by
  cases goal <;> simp_all [Goal.vertex?, fixedB]

/-- A passing instance's fixed literals are true. -/
theorem passes_fixed {σ : Variable → Term Variable Literal Symbol} :
    ∀ {bound : List Variable} {body : List (Goal Variable Literal Symbol)}, program.Passes σ bound body →
      body.all (program.fixedB σ) = true
  | _, [], _ => rfl
  | bound, goal :: rest, passes => by
      have split : program.fixedB σ goal = true ∧ program.Passes σ (after bound goal) rest := by
        cases passes with
        | free found _ _ restPasses => exact ⟨fixedB_of_vertex found, restPasses⟩
        | fixed _ fixed restPasses => exact ⟨fixedB_iff.mpr fixed, restPasses⟩
      simp only [List.all_cons, split.1, passes_fixed split.2, Bool.and_self]

/-- At a passing ground instance, a body holds in a key model exactly when its
ground body holds. -/
theorem passing_holds_iff (wellFormed : program.WellFormed) {markers interp : Interp Literal Symbol}
    {body : List (Goal Variable Literal Symbol)} (ok : ∀ goal ∈ body, program.declares goal = true ∧ program.data goal = true)
    {σ : Variable → Term Variable Literal Symbol} (ground : GroundOn program.constructors σ (bodyNames body))
    {bound : List Variable} (passes : program.Passes σ bound body) :
    (program.keyModel markers interp).Satisfies (fun name => Open.dataKey (σ name)) (bodyTerm body) ↔
      (groundBody σ body).Holds (closedOf interp) (closedOf markers) := by
  rw [body_holds_iff wellFormed ok ground]
  exact ⟨fun holds => holds.1, fun holds => ⟨holds, passes_fixed passes⟩⟩

/-! ## Closure: bodies read relevant atoms -/

/-- A passing instance's calls that leave an output free are at possible
answers. -/
theorem passes_free {σ : Variable → Term Variable Literal Symbol} :
    ∀ {position : Nat} {bound : List Variable} {body : List (Goal Variable Literal Symbol)}, program.Passes σ bound body →
      ∀ call ∈ bodyCalls position bound body, call.2.2.2.2.free = true →
        program.Ans call.2.2.2 (call.2.2.2.1, call.2.1.args.map (subst σ))
  | _, _, [], _, _, member, _ => by cases member
  | position, bound, goal :: rest, passes, call, member, free => by
      have split : ((∃ vertex, goal.vertex? bound = some vertex ∧ vertex.2.free = true ∧
            program.Ans vertex (vertex.1, goal.args.map (subst σ))) ∨
          ((∀ vertex, goal.vertex? bound = some vertex → vertex.2.free = false) ∧ program.fixedAt σ goal)) ∧
          program.Passes σ (after bound goal) rest := by
        cases passes with
        | free found free answer restPasses => exact ⟨.inl ⟨_, found, free, answer⟩, restPasses⟩
        | fixed notFree fixed restPasses => exact ⟨.inr ⟨notFree, fixed⟩, restPasses⟩
      simp only [bodyCalls, List.mem_append] at member
      rcases member with here | there
      · cases found : goal.vertex? bound with
        | none => rw [found] at here; cases here
        | some vertex =>
            rw [found] at here
            rcases List.mem_singleton.mp here with rfl
            rcases split.1 with ⟨other, otherFound, _, answer⟩ | ⟨notFree, _⟩
            · rw [found] at otherFound; cases otherFound; exact answer
            · rw [notFree vertex found] at free; cases free
      · exact passes_free split.2 call there free

omit [DecidableEq Literal] [DecidableEq Symbol] in
/-- Every literal of a body that has a vertex at every reading is among its
calls. -/
theorem exists_call {goal : Goal Variable Literal Symbol} (hasVertex : ∀ bound : List Variable, ∃ vertex, goal.vertex? bound = some vertex) :
    ∀ {position : Nat} {bound : List Variable} {body : List (Goal Variable Literal Symbol)}, goal ∈ body →
      ∃ call ∈ bodyCalls position bound body, call.2.1 = goal
  | _, _, [], member => by cases member
  | position, bound, first :: rest, member => by
      rcases List.mem_cons.mp member with rfl | inRest
      · obtain ⟨vertex, found⟩ := hasVertex bound
        exact ⟨_, mem_bodyCalls_head (rest := rest) (position := position) found, rfl⟩
      · obtain ⟨call, inside, same⟩ := exists_call hasVertex (position := position + 1) (bound := after bound first) inRest
        exact ⟨call, mem_bodyCalls_tail inside, same⟩

/-- **The atoms a passing instance's body reads are relevant**, when its calls
are relevant calls. -/
theorem body_atoms_relevant {query : Query Variable Literal Symbol} {σ : Variable → Term Variable Literal Symbol}
    {start : List Variable} {body : List (Goal Variable Literal Symbol)}
    (ok : ∀ goal ∈ body, program.declares goal = true ∧ program.data goal = true)
    (ground : GroundOn program.constructors σ (bodyNames body)) (passes : program.Passes σ start body)
    (relevant : ∀ call ∈ bodyCalls 0 start body,
      program.Relevant query call.2.2.2 (boundArgs call.2.2.2.2 (call.2.1.args.map (subst σ)))) :
    ∀ atom, atom ∈ (groundBody σ body).1 ∨ atom ∈ (groundBody σ body).2.1 → program.RelevantAtom query atom := by
  have entryOf : ∀ goal ∈ body, ∀ (predicate : Symbol) (args : List (Term Variable Literal Symbol)),
      (goal = .call predicate args ∨ goal = .naf predicate args) → program.RelevantAtom query (predicate, args.map (subst σ)) := by
    intro goal member predicate args shape
    have hasVertex : ∀ bound : List Variable, ∃ vertex, goal.vertex? bound = some vertex := by
      intro bound; rcases shape with rfl | rfl <;> exact ⟨_, rfl⟩
    obtain ⟨⟨position, goal', bound, vertex⟩, inCalls, same⟩ := exists_call hasVertex (position := 0) (bound := start) member
    simp only at same
    subst goal'
    have found := (mem_bodyCalls inCalls).2
    have argsEq : goal.args = args := by rcases shape with rfl | rfl <;> rfl
    have symbolEq : vertex.1 = predicate := by
      rcases shape with rfl | rfl <;> simp only [Goal.vertex?, Option.some.injEq] at found <;> rw [← found]
    have lengths : (args.map (subst σ)).length = vertex.2.length := by rw [List.length_map, vertex?_length found, argsEq]
    have groundArgs : ∀ term ∈ args.map (subst σ), groundIn program.constructors term = true :=
      groundIn_substs (fun arg inside => List.all_eq_true.mp (ok goal member).2 arg (argsEq ▸ inside))
        fun name inside => ground name (List.mem_flatMap.mpr ⟨goal, member, by
          show name ∈ namesOf goal.args; rw [argsEq]; exact inside⟩)
    refine ⟨vertex, ?_, symbolEq.symm, lengths, groundArgs, ?_⟩
    · have := relevant _ inCalls
      simp only at this
      rw [argsEq] at this
      exact this
    · cases free : vertex.2.free with
      | false => exact .inl rfl
      | true =>
          have := passes_free passes _ inCalls free
          simp only at this
          rw [argsEq, symbolEq] at this
          exact .inr this
  intro atom inside
  simp only [groundBody, List.mem_filterMap] at inside
  rcases inside with ⟨goal, member, produced⟩ | ⟨goal, member, produced⟩
  · cases goal with
    | call predicate args =>
        simp only [Goal.callAtom, Option.some.injEq] at produced; subst produced
        exact entryOf _ member predicate args (.inl rfl)
    | _ => simp [Goal.callAtom] at produced
  · cases goal with
    | naf predicate args =>
        simp only [Goal.nafAtom, Option.some.injEq] at produced; subst produced
        exact entryOf _ member predicate args (.inr rfl)
    | _ => simp [Goal.nafAtom] at produced

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem noNames_closed {goal : Goal Variable Literal Symbol} (none : goal.names = []) :
    ∀ arg ∈ goal.args, subst noNames arg = arg := by
  intro arg member
  rw [subst_congr (τ := fun name => Term.var name) arg fun name occurs => by
    have := names_args_sub member occurs; rw [none] at this; cases this]
  exact subst_var arg

/-- **The ground relevant program is closed**: every body it holds reads only
relevant atoms, and every instance's head is one. -/
theorem groundProgram_closed (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) (noParameters : query.parameters = [])
    (conditionsGround : ∀ goal ∈ query.conditions, goal.names = [])
    (closes_ : ∃ n, program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) = true) :
    (program.groundProgram query closes_).Closed := by
  have atomsIff := relevantAtoms_iff wellFormed queryOk evidence noParameters conditionsGround closes_
  refine ⟨fun entry member => ?_, fun body member atom inside => ?_⟩
  · obtain ⟨atom, body⟩ := entry
    obtain ⟨rule, σ, ⟨vertex, index, entryAt, atVertex, groundRule, headEq, passes⟩, rfl⟩ :=
      (relevantInstances_iff wellFormed queryOk evidence noParameters closes_ atom body).mp member
    have ruleOk := wellFormed.rules rule (rulesOf_mem (mem_rulesAt.mp atVertex).1)
    refine ⟨(atomsIff atom).mpr ⟨vertex, entryAt⟩, fun other inside => (atomsIff other).mpr ?_⟩
    refine body_atoms_relevant (Scans.goals ruleOk.scans) (fun name inside => groundRule name (List.mem_append_right _ inside))
      passes (fun call inCalls => ?_) other inside
    exact Relevant.rule entryAt.1 entryAt.2.1 entryAt.2.2.2.2 atVertex groundRule headEq passes inCalls
  · refine (atomsIff atom).mpr ?_
    simp only [groundProgram_denials, groundProgram_conditions, groundProgram_goals, List.mem_append, List.mem_cons] at member
    rcases member with fromDenials | rfl | fromGoals
    · obtain ⟨denial, denialMember, σ, ground, passes, rfl⟩ := (denialBodies_iff wellFormed queryOk evidence body).mp fromDenials
      exact body_atoms_relevant (Scans.goals (wellFormed.denials denial denialMember)) ground passes
        (fun call inCalls => Relevant.denial denialMember ground passes inCalls) atom inside
    · simp only [groundBody, List.mem_filterMap] at inside
      have conditionEntry : ∀ goal ∈ query.conditions, ∀ (predicate : Symbol) (args : List (Term Variable Literal Symbol)),
          (goal = .call predicate args ∨ goal = .naf predicate args) →
            program.RelevantAtom query (predicate, args.map (subst noNames)) := by
        intro goal member predicate args shape
        have none := conditionsGround goal member
        have argsEq : goal.args = args := by rcases shape with rfl | rfl <;> rfl
        have closedArgs : args.map (subst noNames) = args :=
          List.map_congr_left (fun arg inside => noNames_closed none arg (argsEq ▸ inside)) |>.trans (List.map_id _)
        rw [closedArgs]
        have argsClosed : ∀ arg ∈ args, arg.freeVars = [] := by
          intro arg inside
          cases names : arg.freeVars with
          | nil => rfl
          | cons name _ =>
              have := names_args_sub (argsEq ▸ inside) (by rw [names]; exact List.mem_cons_self : name ∈ arg.freeVars)
              rw [none] at this; cases this
        have data := (queryOk.conditions goal member).2.1
        have groundArgs : ∀ term ∈ args, groundIn program.constructors term = true :=
          fun term inside => groundIn_of_closed (List.all_eq_true.mp data term (argsEq ▸ inside)) (argsClosed term inside)
        have hasVertex : ∃ vertex, goal.vertex? query.parameters = some vertex := by rcases shape with rfl | rfl <;> exact ⟨_, rfl⟩
        obtain ⟨vertex, found⟩ := hasVertex
        have allBound : vertex.2.free = false := by
          rcases shape with rfl | rfl
          · simp only [Goal.vertex?, Option.some.injEq] at found; subst found
            simp only [Pattern.free, patternOf, List.any_map, List.any_eq_false, Function.comp, beq_iff_eq]
            intro arg inside
            simp [available, argsClosed arg inside]
          · simp only [Goal.vertex?, Option.some.injEq] at found; subst found
            simp [Pattern.free, full]
        have lengths : args.length = vertex.2.length := by rw [vertex?_length found, argsEq]
        have symbolEq : vertex.1 = predicate := by
          rcases shape with rfl | rfl <;> simp only [Goal.vertex?, Option.some.injEq] at found <;> rw [← found]
        have relevant := Relevant.condition (program := program) member found
        rw [argsEq, boundArgs_all (all_bound_of_not_free allBound) lengths.symm] at relevant
        refine ⟨vertex, ?_, symbolEq.symm, lengths, groundArgs, .inl allBound⟩
        rw [boundArgs_all (all_bound_of_not_free allBound) lengths.symm]
        exact relevant
      rcases inside with ⟨goal, member, produced⟩ | ⟨goal, member, produced⟩
      · cases goal with
        | call predicate args =>
            simp only [Goal.callAtom, Option.some.injEq] at produced; subst produced
            exact conditionEntry _ member predicate args (.inl rfl)
        | _ => simp [Goal.callAtom] at produced
      · cases goal with
        | naf predicate args =>
            simp only [Goal.nafAtom, Option.some.injEq] at produced; subst produced
            exact conditionEntry _ member predicate args (.inr rfl)
        | _ => simp [Goal.nafAtom] at produced
    · obtain ⟨σ, ⟨ground, passes⟩, rfl⟩ := (goalBodies_iff wellFormed queryOk evidence noParameters body).mp fromGoals
      exact body_atoms_relevant (Scans.goals queryOk.goals) ground passes
        (fun call inCalls => Relevant.goal ⟨ground, passes⟩ inCalls) atom inside

/-! ## Every key fixpoint is a model -/

/-- **A key fixpoint restricted to the relevant atoms is a model of the ground
relevant program.** -/
theorem fixpoint_model (wellFormed : program.WellFormed) (guarded : program.Guarded) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) (noParameters : query.parameters = [])
    (conditionsGround : ∀ goal ∈ query.conditions, goal.names = [])
    (closes_ : ∃ n, program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) = true)
    {markers interp : Interp Literal Symbol} (fixed : program.KeyFixpoint markers interp) :
    (program.groundProgram query closes_).Model (closedOf interp) (closedOf markers) := by
  have atomsIff := relevantAtoms_iff wellFormed queryOk evidence noParameters conditionsGround closes_
  have instancesIff := relevantInstances_iff wellFormed queryOk evidence noParameters closes_
  have instanceHolds : ∀ {atom : GAtom Variable Literal Symbol} {rule : Rule Variable Literal Symbol}
      {σ : Variable → Term Variable Literal Symbol}, program.Instance query atom rule σ →
        ((program.keyModel markers interp).Satisfies (fun name => Open.dataKey (σ name)) (bodyTerm rule.body) ↔
          (groundBody σ rule.body).Holds (closedOf interp) (closedOf markers)) := by
    intro atom rule σ ⟨_, _, _, atVertex, groundRule, _, passes⟩
    have ruleOk := wellFormed.rules rule (rulesOf_mem (mem_rulesAt.mp atVertex).1)
    exact passing_holds_iff wellFormed (Scans.goals ruleOk.scans)
      (fun name inside => groundRule name (List.mem_append_right _ inside)) passes
  refine ⟨fun atom member => ?_, fun body member holds => ?_⟩
  · have relevantHolds := relevant_of_fixpoint wellFormed guarded queryOk evidence fixed ((atomsIff atom).mp member)
    unfold RelevantHolds at relevantHolds
    rw [show closedOf interp atom = interp atom.1 (keyArgs atom) from rfl, relevantHolds]
    constructor
    · rintro ⟨rule, σ, inst, bodyHolds⟩
      exact ⟨_, (instancesIff atom _).mpr ⟨rule, σ, inst, rfl⟩, (instanceHolds inst).mp bodyHolds⟩
    · rintro ⟨body, bodyMember, bodyHolds⟩
      obtain ⟨rule, σ, inst, rfl⟩ := (instancesIff atom body).mp bodyMember
      exact ⟨rule, σ, inst, (instanceHolds inst).mpr bodyHolds⟩
  · obtain ⟨denial, denialMember, σ, ground, passes, rfl⟩ := (denialBodies_iff wellFormed queryOk evidence body).mp member
    have keyHolds := (passing_holds_iff (markers := markers) (interp := interp) wellFormed
      (Scans.goals (wellFormed.denials denial denialMember)) ground passes).mpr holds
    exact fixed.2 (denial.map Goal.toTerm) (List.mem_append_right _ (List.mem_map.mpr ⟨denial, denialMember, rfl⟩)) _ keyHolds

/-- **The query's conditions** hold in a key model exactly when their ground
body holds in its restriction and their fixed literals are true. -/
theorem context_iff (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol} (queryOk : QueryOk program query)
    (conditionsGround : ∀ goal ∈ query.conditions, goal.names = [])
    (closes_ : ∃ n, program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) = true)
    {markers interp : Interp Literal Symbol} (environment : Environment Variable (Key Literal Symbol)) :
    (program.keyModel markers interp).ContextHolds environment query.context ↔
      (program.groundProgram query closes_).ConditionsHold (closedOf interp) (closedOf markers) := by
  have namesNil : bodyNames query.conditions = [] := by
    simp only [bodyNames, List.flatMap_eq_nil_iff]; exact conditionsGround
  have contextIff : (program.keyModel markers interp).ContextHolds environment query.context ↔
      (program.keyModel markers interp).Satisfies environment (bodyTerm query.conditions) := by
    unfold bodyTerm Query.context Model.ContextHolds
    rw [Model.satisfies_conjunction]
  rw [contextIff]
  have sameEnv : (program.keyModel markers interp).Satisfies environment (bodyTerm query.conditions) ↔
      (program.keyModel markers interp).Satisfies (fun name => Open.dataKey (noNames name)) (bodyTerm query.conditions) := by
    unfold Model.Satisfies
    rw [Model.eval_congr _ _ (left := environment) (right := fun name => Open.dataKey (noNames name)) fun name occurs => by
      have := bodyNames_of_freeVars occurs; rw [namesNil] at this; cases this]
  rw [sameEnv, body_holds_iff wellFormed (fun goal member => ⟨(queryOk.conditions goal member).1, (queryOk.conditions goal member).2.1⟩)
    (fun name inside => by rw [namesNil] at inside; cases inside)]
  rfl

/-- **The query's formula** holds in a key fixpoint exactly when one of its
ground instance bodies holds in its restriction. -/
theorem formula_iff (wellFormed : program.WellFormed) (guarded : program.Guarded) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) (closed : Closed program query)
    (closes_ : ∃ n, program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) = true)
    {markers interp : Interp Literal Symbol} (fixed : program.KeyFixpoint markers interp)
    (environment : Environment Variable (Key Literal Symbol)) :
    (program.keyModel markers interp).Satisfies environment query.formula ↔
      (program.groundProgram query closes_).GoalHolds (closedOf interp) (closedOf markers) := by
  have goalsIff := goalBodies_iff wellFormed queryOk evidence closed.parameters
  have goalsOk := Scans.goals queryOk.goals
  have namesAnswers : ∀ name ∈ bodyNames query.goals, name ∈ query.answers :=
    fun name inside => Closed.names_answers closed (.inr inside)
  unfold Query.formula
  constructor
  · intro holds
    obtain ⟨other, _, bodyHolds⟩ := satisfies_exists_to _ (bodyTerm query.goals) query.answers environment holds
    have spec : ∀ name ∈ bodyNames query.goals, groundIn program.constructors (program.groundsOfKeys other name) = true ∧
        Open.dataKey (program.groundsOfKeys other name) = other name :=
      fun name inside => program.groundsOfKeys_spec
        (key_of_guarded wellFormed bodyHolds (closed.answers name (namesAnswers name inside)))
    let σ := program.groundsOfKeys other
    have ground : GroundOn program.constructors σ (bodyNames query.goals) := fun name inside => (spec name inside).1
    have keyBody : (program.keyModel markers interp).Satisfies (fun name => Open.dataKey (σ name)) (bodyTerm query.goals) := by
      unfold Model.Satisfies
      rw [Model.eval_congr _ _ (left := fun name => Open.dataKey (σ name)) (right := other)
        fun name occurs => (spec name (bodyNames_of_freeVars occurs)).2]
      exact bodyHolds
    have supported : program.Supported markers interp := fun symbol keys closedKey holds => (fixed.1 symbol keys closedKey).mp holds
    have passes : program.Passes σ query.parameters query.goals := by
      rw [closed.parameters]
      refine passes_of_holds wellFormed goalsOk ground [] keyBody
        fun position bound predicate args callMember calleeFree closedCall argsGround atomHolds => ?_
      have calleeMember : (predicate, patternOf bound args) ∈ program.vertices query :=
        queryVertices_mem (List.mem_append_right _ (List.mem_map.mpr ⟨_, by rw [closed.parameters]; exact callMember, rfl⟩))
      exact ans_complete wellFormed guarded evidence supported _ calleeMember calleeFree
        (by simpa [length_patternOf] using closedCall) _ (by simp [length_patternOf]) argsGround atomHolds
    exact ⟨_, (goalsIff _).mpr ⟨σ, ⟨ground, passes⟩, rfl⟩, (passing_holds_iff wellFormed goalsOk ground passes).mp keyBody⟩
  · rintro ⟨body, member, holds⟩
    obtain ⟨σ, ⟨ground, passes⟩, rfl⟩ := (goalsIff body).mp member
    have keyBody := (passing_holds_iff (markers := markers) (interp := interp) wellFormed goalsOk ground passes).mpr holds
    refine satisfies_exists_of _ (bodyTerm query.goals) query.answers environment (fun name => Open.dataKey (σ name)) ?_
    unfold Model.Satisfies at keyBody ⊢
    rw [Model.eval_congr _ _ (left := override environment (fun name => Open.dataKey (σ name)) query.answers)
      (right := fun name => Open.dataKey (σ name)) fun name occurs => by
        simp [override, namesAnswers name (bodyNames_of_freeVars occurs)]]
    exact keyBody

end Program

/-! ## Deciding the models: the Kripke–Kleene iteration, then enumeration -/

/-- Every sublist of a list, as a list. -/
def subsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | item :: rest => subsets rest ++ (subsets rest).map (item :: ·)

theorem filter_mem_subsets {α : Type} (keep : α → Bool) : ∀ items : List α, items.filter keep ∈ subsets items
  | [] => by simp [subsets]
  | item :: rest => by
      cases kept : keep item
      · simp only [List.filter_cons, kept, Bool.false_eq_true, ite_false, subsets, List.mem_append]
        exact .inl (filter_mem_subsets keep rest)
      · simp only [List.filter_cons, kept, ite_true, subsets, List.mem_append]
        exact .inr (List.mem_map.mpr ⟨_, filter_mem_subsets keep rest, rfl⟩)

/-- Some sublist passes a test, tried one at a time, stopping at the first:
the sublists are never built as a list. -/
def anySubset {α : Type} (test : List α → Bool) : List α → Bool
  | [] => test []
  | item :: rest => anySubset test rest || anySubset (fun subset => test (item :: subset)) rest

theorem anySubset_iff {α : Type} : ∀ (items : List α) (test : List α → Bool),
    anySubset test items = true ↔ ∃ subset ∈ subsets items, test subset = true
  | [], test => by simp [anySubset, subsets]
  | item :: rest, test => by
      simp only [anySubset, Bool.or_eq_true, anySubset_iff rest, subsets, List.mem_append, List.mem_map]
      constructor
      · rintro (⟨subset, member, holds⟩ | ⟨subset, member, holds⟩)
        · exact ⟨subset, .inl member, holds⟩
        · exact ⟨item :: subset, .inr ⟨subset, member, rfl⟩, holds⟩
      · rintro ⟨subset, (member | ⟨smaller, member, rfl⟩), holds⟩
        · exact .inl ⟨subset, member, holds⟩
        · exact .inr ⟨smaller, member, holds⟩

namespace GroundBody

variable (closed marked : List (GAtom Variable Literal Symbol))

/-- A ground body holds under listed true atoms and listed true markers. -/
def holdsIn (body : GroundBody Variable Literal Symbol) : Bool :=
  body.1.all (fun atom => decide (atom ∈ closed)) && body.2.1.all (fun atom => !decide (atom ∈ closed)) &&
    body.2.2.all (fun atom => decide (atom ∈ marked))

theorem holdsIn_iff (body : GroundBody Variable Literal Symbol) :
    body.holdsIn closed marked = true ↔ body.Holds (· ∈ closed) (· ∈ marked) := by
  simp [holdsIn, Holds, List.all_eq_true, and_assoc]

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
/-- Bodies read their atoms only: assignments that agree on them agree on the
body. -/
theorem holds_congr {closed closed' marked marked' : GAtom Variable Literal Symbol → Prop}
    {body : GroundBody Variable Literal Symbol} (agreeClosed : ∀ atom, atom ∈ body.1 ∨ atom ∈ body.2.1 → (closed atom ↔ closed' atom))
    (agreeMarked : ∀ atom ∈ body.2.2, marked atom ↔ marked' atom) : body.Holds closed marked ↔ body.Holds closed' marked' := by
  unfold Holds
  constructor
  · rintro ⟨calls, nafs, marks⟩
    exact ⟨fun atom inside => (agreeClosed atom (.inl inside)).mp (calls atom inside),
      fun atom inside holds => nafs atom inside ((agreeClosed atom (.inr inside)).mpr holds),
      fun atom inside => (agreeMarked atom inside).mp (marks atom inside)⟩
  · rintro ⟨calls, nafs, marks⟩
    exact ⟨fun atom inside => (agreeClosed atom (.inl inside)).mpr (calls atom inside),
      fun atom inside holds => nafs atom inside ((agreeClosed atom (.inr inside)).mp holds),
      fun atom inside => (agreeMarked atom inside).mpr (marks atom inside)⟩

end GroundBody

namespace GroundProgram

variable (ground : GroundProgram Variable Literal Symbol)

/-- The marker atoms the program reads. -/
def markerAtoms : List (GAtom Variable Literal Symbol) :=
  (ground.rules.flatMap (·.2.2.2) ++ (ground.denials ++ ground.conditions :: ground.goals).flatMap (·.2.2)).eraseDups

/-- An assignment of listed true atoms and markers is a model, decided. -/
def isModel (closed marked : List (GAtom Variable Literal Symbol)) : Bool :=
  ground.atoms.all (fun atom => decide (atom ∈ closed) ==
      ground.rules.any fun entry => decide (entry.1 = atom) && entry.2.holdsIn closed marked) &&
    ground.denials.all fun body => !body.holdsIn closed marked

theorem isModel_iff (closed marked : List (GAtom Variable Literal Symbol)) :
    ground.isModel closed marked = true ↔ ground.Model (· ∈ closed) (· ∈ marked) := by
  simp only [isModel, Model, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Bool.not_eq_true',
    ← GroundBody.holdsIn_iff]
  constructor
  · rintro ⟨atoms, denials⟩
    refine ⟨fun atom member => ?_, fun body member holds => by rw [denials body member] at holds; cases holds⟩
    have := atoms atom member
    rw [Bool.eq_iff_iff, decide_eq_true_eq] at this
    rw [this]
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨entry, entryMember, rfl, holds⟩; exact ⟨entry.2, entryMember, holds⟩
    · rintro ⟨body, bodyMember, holds⟩; exact ⟨(atom, body), bodyMember, rfl, holds⟩
  · rintro ⟨atoms, denials⟩
    refine ⟨fun atom member => ?_, fun body member => ?_⟩
    · rw [Bool.eq_iff_iff, decide_eq_true_eq, atoms atom member]
      simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨body, bodyMember, holds⟩; exact ⟨(atom, body), bodyMember, rfl, holds⟩
      · rintro ⟨entry, entryMember, rfl, holds⟩; exact ⟨entry.2, entryMember, holds⟩
    · cases holds : body.holdsIn closed marked
      · rfl
      · exact absurd holds (denials body member)

/-- One round of the Kripke–Kleene iteration on the ground program: an atom
is definitely true when one of its instances has its calls definitely true,
its NAF literals definitely false, and no marker; definitely false when every
instance has a call definitely false or a NAF literal definitely true. -/
def kkStep (state : List (GAtom Variable Literal Symbol) × List (GAtom Variable Literal Symbol)) :
    List (GAtom Variable Literal Symbol) × List (GAtom Variable Literal Symbol) :=
  (ground.atoms.filter fun atom => ground.rules.any fun entry =>
      decide (entry.1 = atom) && entry.2.1.all (fun call => decide (call ∈ state.1)) &&
        entry.2.2.1.all (fun naf => decide (naf ∈ state.2)) && entry.2.2.2.isEmpty,
    ground.atoms.filter fun atom => ground.rules.all fun entry =>
      !decide (entry.1 = atom) || entry.2.1.any (fun call => decide (call ∈ state.2)) ||
        entry.2.2.1.any (fun naf => decide (naf ∈ state.1)))

/-- The iteration's rounds. -/
def kk : Nat → List (GAtom Variable Literal Symbol) × List (GAtom Variable Literal Symbol)
  | 0 => ([], [])
  | n + 1 => ground.kkStep (kk n)

/-- **The Kripke–Kleene iteration** (S24's `kk`, on the ground relevant
program): the definitely true and the definitely false atoms, stopped once a
round changes nothing. -/
def kleene : List (GAtom Variable Literal Symbol) × List (GAtom Variable Literal Symbol) :=
  untilStable (fun next current => decide (next = current)) ground.kkStep (2 * ground.atoms.length + 2) ([], [])

theorem kleene_round : ∃ round, ground.kleene = ground.kk round :=
  untilStable_round _ _ ground.kk (fun _ => rfl) _ 0

/-- **Every round is sound**: in every model, the definitely true atoms hold
and the definitely false ones do not. -/
theorem kk_sound {closed marked : GAtom Variable Literal Symbol → Prop} (model : ground.Model closed marked) :
    ∀ n, (∀ atom ∈ (ground.kk n).1, closed atom) ∧ (∀ atom ∈ (ground.kk n).2, ¬ closed atom)
  | 0 => by simp [kk]
  | n + 1 => by
      obtain ⟨definite, refuted⟩ := kk_sound model n
      simp only [kk, kkStep, List.mem_filter, List.any_eq_true, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.isEmpty_iff]
      refine ⟨fun atom ⟨member, entry, entryMember, ⟨⟨same, calls⟩, nafs⟩, noMarks⟩ => ?_,
        fun atom ⟨member, every⟩ holds => ?_⟩
      · refine (model.1 atom member).mpr ⟨entry.2, by rw [← same]; exact entryMember, fun call inside => definite call (calls call inside),
          fun naf inside => refuted naf (nafs naf inside), fun mark inside => by rw [noMarks] at inside; cases inside⟩
      · obtain ⟨body, bodyMember, bodyHolds⟩ := (model.1 atom member).mp holds
        rcases every (atom, body) bodyMember with (different | ⟨call, inside, false⟩) | ⟨naf, inside, true⟩
        · exact different rfl
        · exact refuted call false (bodyHolds.1 call inside)
        · exact bodyHolds.2.1 naf inside (definite naf true)

/-- The atoms an iteration's result leaves undefined. -/
def undefinedWith (state : List (GAtom Variable Literal Symbol) × List (GAtom Variable Literal Symbol)) :
    List (GAtom Variable Literal Symbol) :=
  ground.atoms.filter fun atom => !decide (atom ∈ state.1) && !decide (atom ∈ state.2)

/-- The atoms the iteration leaves undefined. -/
def undefinedAtoms : List (GAtom Variable Literal Symbol) := ground.undefinedWith ground.kleene

/-- The candidate assignments: the definitely true atoms with each subset of
the undefined ones, and each subset of the markers. The iteration runs once. -/
def candidates : List (List (GAtom Variable Literal Symbol) × List (GAtom Variable Literal Symbol)) :=
  let state := ground.kleene
  let markerChoices := subsets ground.markerAtoms
  (subsets (ground.undefinedWith state)).flatMap fun chosen => markerChoices.map fun marks => (state.1 ++ chosen, marks)

/-- **A model exists**, decided with early exit: the candidates tried one at a
time (`anySubset`), never built as a list. -/
def hasModel : Bool :=
  let state := ground.kleene
  anySubset (fun chosen => anySubset (fun marks => ground.isModel (state.1 ++ chosen) marks) ground.markerAtoms)
    (ground.undefinedWith state)

theorem hasModel_iff : ground.hasModel = true ↔ ∃ candidate ∈ ground.candidates, ground.isModel candidate.1 candidate.2 = true := by
  simp only [hasModel, candidates, anySubset_iff, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨chosen, chosenMember, marks, marksMember, isModel⟩
    exact ⟨_, ⟨chosen, chosenMember, marks, marksMember, rfl⟩, isModel⟩
  · rintro ⟨_, ⟨chosen, chosenMember, marks, marksMember, rfl⟩, isModel⟩
    exact ⟨chosen, chosenMember, marks, marksMember, isModel⟩

/-- **The models of the ground program**: the candidates that are models. -/
def models : List (List (GAtom Variable Literal Symbol) × List (GAtom Variable Literal Symbol)) :=
  ground.candidates.filter fun candidate => ground.isModel candidate.1 candidate.2

theorem models_model {candidate : List (GAtom Variable Literal Symbol) × List (GAtom Variable Literal Symbol)}
    (member : candidate ∈ ground.models) : ground.Model (· ∈ candidate.1) (· ∈ candidate.2) :=
  (ground.isModel_iff _ _).mp (List.mem_filter.mp member).2

theorem markerAtoms_rules {entry : GAtom Variable Literal Symbol × GroundBody Variable Literal Symbol}
    (member : entry ∈ ground.rules) : ∀ atom ∈ entry.2.2.2, atom ∈ ground.markerAtoms := fun _ inside =>
  List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_flatMap.mpr ⟨entry, member, inside⟩))

theorem markerAtoms_bodies {body : GroundBody Variable Literal Symbol}
    (member : body ∈ ground.denials ++ ground.conditions :: ground.goals) : ∀ atom ∈ body.2.2, atom ∈ ground.markerAtoms :=
  fun _ inside => List.mem_eraseDups.mpr (List.mem_append_right _ (List.mem_flatMap.mpr ⟨body, member, inside⟩))

/-- **The enumeration is complete**: every model of a closed ground program
agrees with one of the models found on the atoms and the markers. -/
theorem models_complete (closedProgram : ground.Closed) {closed marked : GAtom Variable Literal Symbol → Prop}
    (model : ground.Model closed marked) :
    ∃ candidate ∈ ground.models, (∀ atom ∈ ground.atoms, atom ∈ candidate.1 ↔ closed atom) ∧
      ∀ atom ∈ ground.markerAtoms, atom ∈ candidate.2 ↔ marked atom := by
  classical
  obtain ⟨round, roundEq⟩ := ground.kleene_round
  obtain ⟨definite, refuted⟩ := ground.kk_sound model round
  rw [← roundEq] at definite refuted
  let chosen := ground.undefinedAtoms.filter fun atom => decide (closed atom)
  let marks := ground.markerAtoms.filter fun atom => decide (marked atom)
  have atomsAgree : ∀ atom ∈ ground.atoms, atom ∈ ground.kleene.1 ++ chosen ↔ closed atom := by
    intro atom member
    simp only [List.mem_append, chosen, List.mem_filter, undefinedAtoms, undefinedWith, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, decide_eq_true_eq]
    constructor
    · rintro (true | ⟨_, holds⟩)
      · exact definite atom true
      · exact holds
    · intro holds
      by_cases true : atom ∈ ground.kleene.1
      · exact .inl true
      · exact .inr ⟨⟨member, true, fun false => refuted atom false holds⟩, holds⟩
  have marksAgree : ∀ atom ∈ ground.markerAtoms, atom ∈ marks ↔ marked atom := by
    intro atom member
    simp [marks, member]
  refine ⟨(ground.kleene.1 ++ chosen, marks), ?_, atomsAgree, marksAgree⟩
  have bodyAgree : ∀ body : GroundBody Variable Literal Symbol, (∀ atom, atom ∈ body.1 ∨ atom ∈ body.2.1 → atom ∈ ground.atoms) →
      (∀ atom ∈ body.2.2, atom ∈ ground.markerAtoms) →
        (body.Holds (· ∈ ground.kleene.1 ++ chosen) (· ∈ marks) ↔ body.Holds closed marked) :=
    fun body inAtoms inMarkers => GroundBody.holds_congr (fun atom inside => atomsAgree atom (inAtoms atom inside))
      (fun atom inside => marksAgree atom (inMarkers atom inside))
  refine List.mem_filter.mpr ⟨?_, (ground.isModel_iff _ _).mpr ⟨fun atom member => ?_, fun body member holds => ?_⟩⟩
  · exact List.mem_flatMap.mpr ⟨chosen, filter_mem_subsets _ _, List.mem_map.mpr ⟨marks, filter_mem_subsets _ _, rfl⟩⟩
  · show atom ∈ ground.kleene.1 ++ chosen ↔
      ∃ body, (atom, body) ∈ ground.rules ∧ GroundBody.Holds (· ∈ ground.kleene.1 ++ chosen) (· ∈ marks) body
    rw [atomsAgree atom member, model.1 atom member]
    constructor
    · rintro ⟨body, bodyMember, holds⟩
      exact ⟨body, bodyMember, (bodyAgree body (closedProgram.1 _ bodyMember).2 (ground.markerAtoms_rules bodyMember)).mpr holds⟩
    · rintro ⟨body, bodyMember, holds⟩
      exact ⟨body, bodyMember, (bodyAgree body (closedProgram.1 _ bodyMember).2 (ground.markerAtoms_rules bodyMember)).mp holds⟩
  · have inBodies : body ∈ ground.denials ++ ground.conditions :: ground.goals := List.mem_append_left _ member
    exact model.2 body member ((bodyAgree body (closedProgram.2 body inBodies) (ground.markerAtoms_bodies inBodies)).mp holds)

end GroundProgram

end AnthillModKbSpec.IR
