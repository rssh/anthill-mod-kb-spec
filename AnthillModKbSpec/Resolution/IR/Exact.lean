import AnthillModKbSpec.Resolution.IR.Possible

/-! # The exact relevant program (S28)

S27 defines a closed query's relevant program (`Relevant`, `RelevantAtom`,
`Instance`), proves it finite under P1 (`relevant_finite`), and computes a
superset of it with fuel. The evaluator runs on the relevant program itself,
computed here without fuel:

- **Calls** (`Program.relevantCalls`): from the roots (the calls of the
  query's checked passing instances, its conditions, and the denials' checked
  passing instances), every call of a checked passing instance of a call
  found, round by round until a round adds nothing. Each call found is
  relevant, since every instance it comes from is checked
  (`callRounds_sound`), and the rounds stop: they stay inside S27's finite
  relevant calls and grow until one closes (`closes`). They are run each
  from the one before until one closes (`Program.roundsFrom`), with no fuel:
  the loop's termination is that existence. The closed round holds every
  relevant call (`callRounds_complete`), so the calls found are exactly S27's
  (`relevantCalls_iff`).
- **Atoms** (`Program.atomsAt`): a call that leaves an output free answers
  its possible answers (`answersOf`, exact under P1), any other call its one
  atom. They are exactly the relevant atoms (`relevantAtoms_iff`).
- **Instances** (`Program.instancesOfCall`): the checked passing instances at
  the relevant calls, each as its head and its **ground body**: the atoms of
  its calls, of its NAF literals, and of its marker literals, its fixed
  literals true and dropped. They are exactly S27's relevant instances
  (`relevantInstances_iff`), and so are the denials' and the query's
  (`denialBodies_iff`, `goalBodies_iff`).

The relevant program is computed for a closed query of P0 or P1: the loop's
termination is S27's finiteness, which needs the evidence, and the evaluator
supplies it (`Program.closes_of_decides`). Each definition that computes with
the answer lists builds the level table once (`Program.answersWith`). -/

namespace AnthillModKbSpec.IR

open Semantics Completion Tabled Answers

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  [FreshNames Variable]

attribute [local instance] Machine.termEq

/-! ## Ground bodies -/

/-- A ground body: the atoms of an instance's calls, of its NAF literals, and
of its marker literals. Its fixed literals are true at the instance and are
dropped. -/
abbrev GroundBody (Variable Literal Symbol : Type) :=
  List (GAtom Variable Literal Symbol) × List (GAtom Variable Literal Symbol) × List (GAtom Variable Literal Symbol)

/-- The atom of a call at an instance. -/
def Goal.callAtom (σ : Variable → Term Variable Literal Symbol) : Goal Variable Literal Symbol → Option (GAtom Variable Literal Symbol)
  | .call predicate args => some (predicate, args.map (IR.subst σ))
  | _ => none

/-- The atom of a NAF literal at an instance. -/
def Goal.nafAtom (σ : Variable → Term Variable Literal Symbol) : Goal Variable Literal Symbol → Option (GAtom Variable Literal Symbol)
  | .naf predicate args => some (predicate, args.map (IR.subst σ))
  | _ => none

/-- The atom of a marker literal at an instance. -/
def Goal.markerAtom (σ : Variable → Term Variable Literal Symbol) : Goal Variable Literal Symbol → Option (GAtom Variable Literal Symbol)
  | .marker symbol args => some (symbol, args.map (IR.subst σ))
  | _ => none

/-- The ground body of an instance. -/
def groundBody (σ : Variable → Term Variable Literal Symbol) (body : List (Goal Variable Literal Symbol)) :
    GroundBody Variable Literal Symbol :=
  (body.filterMap (Goal.callAtom σ), body.filterMap (Goal.nafAtom σ), body.filterMap (Goal.markerAtom σ))

/-- The calls an instance makes, read from the names bound before its body:
each call's vertex and bound values. -/
def instanceCalls (σ : Variable → Term Variable Literal Symbol) (bound : List Variable) (body : List (Goal Variable Literal Symbol)) :
    List (Vertex Symbol × List (Term Variable Literal Symbol)) :=
  (bodyCalls 0 bound body).map fun call => (call.2.2.2, boundArgs call.2.2.2.2 (call.2.1.args.map (subst σ)))

namespace Program

variable (program : Program Variable Literal Symbol)

/-! ## The relevant calls -/

/-- The checked passing instances of a body read from the names bound before
it, from a start: each by the values of the body's names. -/
def bodyInstances (answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol))
    (bound : List Variable) (start : Env Variable Literal Symbol) (body : List (Goal Variable Literal Symbol)) :
    List (List (Term Variable Literal Symbol)) :=
  ((program.bodyEnvs answers bound [start] body).filterMap fun env =>
    let values := (bodyNames body).map (envSubst env)
    if (bodyNames body).all (fun name => groundIn program.constructors (substOf (bodyNames body) values name)) &&
        program.passesWith answers (substOf (bodyNames body) values) bound body then some values else none).eraseDups

/-- The calls a call makes: those of its checked passing instances. -/
def callsOf (answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol))
    (call : Vertex Symbol × List (Term Variable Literal Symbol)) : List (Vertex Symbol × List (Term Variable Literal Symbol)) :=
  (program.instancesAt answers call.1 call.2).flatMap fun entry =>
    match program.rules[entry.1]? with
    | some rule => instanceCalls (substOf rule.names entry.2) (startNames call.1.2 rule.args) rule.body
    | none => []

/-- The roots: the calls of the query's checked passing instances, of its
conditions, and of the denials' checked passing instances. -/
def roots (answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol))
    (query : Query Variable Literal Symbol) : List (Vertex Symbol × List (Term Variable Literal Symbol)) :=
  ((program.bodyInstances answers query.parameters (fun _ => none) query.goals).flatMap fun values =>
      instanceCalls (substOf (bodyNames query.goals) values) query.parameters query.goals) ++
    query.conditions.filterMap (fun goal => (goal.vertex? query.parameters).map fun vertex => (vertex, boundArgs vertex.2 goal.args)) ++
    program.denials.flatMap fun body => (program.bodyInstances answers [] (fun _ => none) body).flatMap fun values =>
      instanceCalls (substOf (bodyNames body) values) [] body

/-- One round: the calls found and the calls they make. -/
def grow (answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol))
    (calls : List (Vertex Symbol × List (Term Variable Literal Symbol))) : List (Vertex Symbol × List (Term Variable Literal Symbol)) :=
  (calls ++ calls.flatMap (program.callsOf answers)).eraseDups

/-- The calls found after some rounds. -/
def callRounds (answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol))
    (query : Query Variable Literal Symbol) : Nat → List (Vertex Symbol × List (Term Variable Literal Symbol))
  | 0 => (program.roots answers query).eraseDups
  | n + 1 => program.grow answers (callRounds answers query n)

/-- Calls closed under the calls they make. -/
def closedCalls (answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol))
    (calls : List (Vertex Symbol × List (Term Variable Literal Symbol))) : Bool :=
  (calls.flatMap (program.callsOf answers)).all calls.contains

/-- The possible answers by rank, read from a level table. -/
def answersWith (table : List (Vertex Symbol × Nat)) :
    Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol) :=
  program.answersOf (levelIn table)

/-- The answer lists of a query's evaluation: the possible answers by rank.
Each definition that computes with them builds the level table once, by
`answersWith`, and passes the lists down. -/
def answersFor (query : Query Variable Literal Symbol) :
    Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol) :=
  program.answersWith (program.levelTable (program.vertices query))

/-- The rounds from a round on, each computed from the one before, until one
closes: no round is recomputed from the start. -/
def roundsFrom (answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol))
    (query : Query Variable Literal Symbol)
    (closes : ∃ n, program.closedCalls answers (program.callRounds answers query n) = true) (n : Nat)
    (calls : List (Vertex Symbol × List (Term Variable Literal Symbol))) (current : calls = program.callRounds answers query n)
    (below : ∀ k < n, program.closedCalls answers (program.callRounds answers query k) = false) :
    List (Vertex Symbol × List (Term Variable Literal Symbol)) :=
  let made := calls.flatMap (program.callsOf answers)
  if closed : made.all calls.contains = true then calls
  else roundsFrom answers query closes (n + 1) (calls ++ made).eraseDups (by subst current; rfl) fun k lt => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp lt with lower | same
    · exact below k lower
    · subst same; rw [← current]; exact Bool.eq_false_iff.mpr closed
termination_by Classical.choose closes + 1 - n
decreasing_by
  have witness := Classical.choose_spec closes
  have lt : n < Classical.choose closes := by
    rcases Nat.lt_or_ge n (Classical.choose closes) with lt | ge
    · exact lt
    · rcases Nat.lt_or_eq_of_le ge with gt | same
      · rw [below _ gt] at witness; cases witness
      · rw [same, ← current] at witness; exact absurd witness closed
  omega

omit [FreshNames Variable] in
theorem roundsFrom_spec {answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)}
    {query : Query Variable Literal Symbol}
    (closes : ∃ n, program.closedCalls answers (program.callRounds answers query n) = true) :
    ∀ (n : Nat) (calls : List (Vertex Symbol × List (Term Variable Literal Symbol))) (current : calls = program.callRounds answers query n)
      (below : ∀ k < n, program.closedCalls answers (program.callRounds answers query k) = false),
      ∃ m, program.roundsFrom answers query closes n calls current below = program.callRounds answers query m ∧
        program.closedCalls answers (program.callRounds answers query m) = true := by
  intro n calls current below
  unfold roundsFrom
  dsimp only
  split
  · rename_i closed
    exact ⟨n, current, current ▸ closed⟩
  · exact roundsFrom_spec closes (n + 1) _ _ _
termination_by n => Classical.choose closes + 1 - n
decreasing_by
  rename_i closed
  have witness := Classical.choose_spec closes
  have lt : n < Classical.choose closes := by
    rcases Nat.lt_or_ge n (Classical.choose closes) with lt | ge
    · exact lt
    · rcases Nat.lt_or_eq_of_le ge with gt | same
      · rw [below _ gt] at witness; cases witness
      · rw [same, ← current] at witness; exact absurd witness closed
  omega

/-- **The relevant calls**: the first closed round, found round by round,
given that one closes (`closes`, from the evidence). -/
def relevantCalls (query : Query Variable Literal Symbol)
    (closes : ∃ n, program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) = true) :
    List (Vertex Symbol × List (Term Variable Literal Symbol)) :=
  let answers := program.answersWith (program.levelTable (program.vertices query))
  program.roundsFrom answers query closes 0 (program.callRounds answers query 0) rfl fun _ lt => absurd lt (Nat.not_lt_zero _)

/-! ## The relevant atoms and instances -/

/-- The atoms of a call: its possible answers when it leaves an output free,
its one atom otherwise. -/
def atomsAt (answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol))
    (call : Vertex Symbol × List (Term Variable Literal Symbol)) : List (GAtom Variable Literal Symbol) :=
  if call.1.2.free then answers call.1 call.2 else [(call.1.1, call.2)]

/-- The checked passing instances at a call, each as its head and its ground
body. -/
def instancesOfCall (answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol))
    (call : Vertex Symbol × List (Term Variable Literal Symbol)) :
    List (GAtom Variable Literal Symbol × GroundBody Variable Literal Symbol) :=
  (program.instancesAt answers call.1 call.2).filterMap fun entry =>
    (program.rules[entry.1]?).map fun rule =>
      ((rule.head, rule.args.map (subst (substOf rule.names entry.2))), groundBody (substOf rule.names entry.2) rule.body)

/-- The ground bodies of a body's checked passing instances. -/
def groundBodies (answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol))
    (bound : List Variable) (body : List (Goal Variable Literal Symbol)) : List (GroundBody Variable Literal Symbol) :=
  (program.bodyInstances answers bound (fun _ => none) body).map fun values => groundBody (substOf (bodyNames body) values) body

/-! ## Facts -/

variable {program}

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
mutual
theorem subst_var : ∀ term : Term Variable Literal Symbol, subst (fun name => Term.var name) term = term
  | .var _ => rfl
  | .app symbol args => by simp only [subst]; rw [substAll_var args]
  | .lit _ | .truth | .falsity | .conj _ _ | .disj _ _ | .imp _ _ | .defaultNeg _ | .forallVar _ _ | .existsVar _ _
  | .dictionaryCall _ _ _ _ | .equal _ _ => rfl

theorem substAll_var : ∀ args : List (Term Variable Literal Symbol), substAll (fun name => Term.var name) args = args
  | [] => rfl
  | arg :: rest => by simp only [substAll, subst_var arg, substAll_var rest]
end

omit [FreshNames Variable] in
/-- A data term with no name is ground. -/
theorem groundIn_of_closed {constructors : List (Constructor Literal Symbol)} {term : Term Variable Literal Symbol}
    (data : dataIn constructors term = true) (closed : term.freeVars = []) : groundIn constructors term = true := by
  have := groundIn_subst (σ := fun name => Term.var name) term data fun name occurs => by rw [closed] at occurs; cases occurs
  rwa [subst_var] at this

omit [FreshNames Variable] in
/-- A possible answer is an atom of its vertex's predicate and arity, over
ground data terms. -/
theorem ans_atom (wellFormed : program.WellFormed) {vertex : Vertex Symbol} {atom : GAtom Variable Literal Symbol}
    (answer : program.Ans vertex atom) :
    atom.1 = vertex.1 ∧ atom.2.length = vertex.2.length ∧ ∀ term ∈ atom.2, groundIn program.constructors term = true := by
  cases answer with
  | @rule _ index rule σ atVertex groundRule _ =>
      obtain ⟨inRules, lengths⟩ := mem_rulesAt.mp atVertex
      obtain ⟨found, headEq⟩ := mem_rulesOf.mp inRules
      refine ⟨headEq, by simpa using lengths, ?_⟩
      exact groundIn_substs (wellFormed.rules rule (List.mem_of_getElem? found)).data
        fun name inside => groundRule name (List.mem_append_left _ inside)

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem all_bound_of_not_free {pattern : Pattern} (notFree : pattern.free = false) : ∀ flag ∈ pattern, flag = true := by
  intro flag inside
  simp only [Pattern.free, List.any_eq_false, beq_iff_eq] at notFree
  cases flag
  · exact absurd rfl (notFree false inside)
  · rfl

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem vertex?_length {goal : Goal Variable Literal Symbol} {bound : List Variable} {vertex : Vertex Symbol}
    (found : goal.vertex? bound = some vertex) : vertex.2.length = goal.args.length := by
  cases goal with
  | call predicate args =>
      simp only [Goal.vertex?, Option.some.injEq] at found; subst found
      simp [patternOf, Goal.args]
  | naf predicate args =>
      simp only [Goal.vertex?, Option.some.injEq] at found; subst found
      simp [full, Goal.args]
  | _ => simp [Goal.vertex?] at found

omit [FreshNames Variable] in
/-- The answer lists of an evaluation are sound. -/
theorem answersFor_sound {query : Query Variable Literal Symbol} {vertex : Vertex Symbol}
    {values : List (Term Variable Literal Symbol)} {atom : GAtom Variable Literal Symbol}
    (member : atom ∈ program.answersFor query vertex values) : program.Ans vertex atom ∧ boundArgs vertex.2 atom.2 = values :=
  answersOf_sound _ _ _ _ member

/-! ## Instances and calls are relevant -/

omit [FreshNames Variable] in
/-- A kept instance at a call passes. -/
theorem instancesAt_passes {query : Query Variable Literal Symbol} {vertex : Vertex Symbol}
    {values : List (Term Variable Literal Symbol)} {entry : Nat × List (Term Variable Literal Symbol)}
    (member : entry ∈ program.instancesAt (program.answersFor query) vertex values) :
    ∃ rule, (entry.1, rule) ∈ program.rulesAt vertex ∧ entry.2 = rule.names.map (substOf rule.names entry.2) ∧
      GroundOn program.constructors (substOf rule.names entry.2) rule.names ∧
      (boundArgs vertex.2 rule.args).map (subst (substOf rule.names entry.2)) = values ∧
      program.Passes (substOf rule.names entry.2) (startNames vertex.2 rule.args) rule.body := by
  obtain ⟨rule, atVertex, valuesEq, ok⟩ := instancesAt_sound member
  obtain ⟨ground, boundEq, passes⟩ := checked_parts ok
  exact ⟨rule, atVertex, valuesEq, ground, boundEq, passesWith_sound (fun _ _ _ inside => (answersFor_sound inside).1) passes⟩

omit [FreshNames Variable] in
/-- **The calls a relevant call makes are relevant.** -/
theorem callsOf_sound {query : Query Variable Literal Symbol} {call : Vertex Symbol × List (Term Variable Literal Symbol)}
    (relevant : program.Relevant query call.1 call.2) {made : Vertex Symbol × List (Term Variable Literal Symbol)}
    (member : made ∈ program.callsOf (program.answersFor query) call) : program.Relevant query made.1 made.2 := by
  obtain ⟨entry, entryMember, inside⟩ := List.mem_flatMap.mp member
  obtain ⟨rule, atVertex, _, ground, boundEq, passes⟩ := instancesAt_passes entryMember
  have found := mem_rulesOf.mp (mem_rulesAt.mp atVertex).1
  simp only [found.1] at inside
  obtain ⟨⟨position, goal, bound, callee⟩, inCalls, rfl⟩ := List.mem_map.mp inside
  refine Relevant.rule (atom := (rule.head, rule.args.map (subst (substOf rule.names entry.2)))) ?_ found.2
    (.inr (.rule atVertex ground passes)) atVertex ground rfl passes inCalls
  simp only
  rw [boundArgs_map, boundEq]
  exact relevant

omit [FreshNames Variable] in
theorem bodyInstances_sound
    {answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)}
    {bound : List Variable} {start : Env Variable Literal Symbol} {body : List (Goal Variable Literal Symbol)}
    {values : List (Term Variable Literal Symbol)} (member : values ∈ program.bodyInstances answers bound start body) :
    values = (bodyNames body).map (substOf (bodyNames body) values) ∧
      GroundOn program.constructors (substOf (bodyNames body) values) (bodyNames body) ∧
      program.passesWith answers (substOf (bodyNames body) values) bound body = true := by
  unfold bodyInstances at member
  rw [List.mem_eraseDups] at member
  obtain ⟨env, _, produced⟩ := List.mem_filterMap.mp member
  dsimp only at produced
  split at produced
  · rename_i ok
    cases produced
    simp only [Bool.and_eq_true, List.all_eq_true] at ok
    exact ⟨map_substOf.symm, ok.1, ok.2⟩
  · cases produced

omit [FreshNames Variable] in
/-- **The roots are relevant.** -/
theorem roots_sound {query : Query Variable Literal Symbol} {made : Vertex Symbol × List (Term Variable Literal Symbol)}
    (member : made ∈ program.roots (program.answersFor query) query) : program.Relevant query made.1 made.2 := by
  have answersSound : ∀ vertex values atom, atom ∈ program.answersFor query vertex values → program.Ans vertex atom :=
    fun _ _ _ inside => (answersFor_sound inside).1
  simp only [roots, List.mem_append] at member
  rcases member with (fromGoals | fromConditions) | fromDenials
  · obtain ⟨values, valuesMember, inside⟩ := List.mem_flatMap.mp fromGoals
    obtain ⟨_, ground, passes⟩ := bodyInstances_sound valuesMember
    obtain ⟨⟨position, goal, bound, callee⟩, inCalls, rfl⟩ := List.mem_map.mp inside
    exact .goal ⟨ground, passesWith_sound answersSound passes⟩ inCalls
  · obtain ⟨goal, goalMember, produced⟩ := List.mem_filterMap.mp fromConditions
    cases found : goal.vertex? query.parameters with
    | none => rw [found] at produced; cases produced
    | some vertex =>
        rw [found] at produced
        cases produced
        exact .condition goalMember found
  · obtain ⟨body, bodyMember, inside⟩ := List.mem_flatMap.mp fromDenials
    obtain ⟨values, valuesMember, inside⟩ := List.mem_flatMap.mp inside
    obtain ⟨_, ground, passes⟩ := bodyInstances_sound valuesMember
    obtain ⟨⟨position, goal, bound, callee⟩, inCalls, rfl⟩ := List.mem_map.mp inside
    exact .denial bodyMember ground (passesWith_sound answersSound passes) inCalls

omit [FreshNames Variable] in
/-- **Every call found is relevant**, at every round. -/
theorem callRounds_sound {query : Query Variable Literal Symbol} :
    ∀ n, ∀ made ∈ program.callRounds (program.answersFor query) query n, program.Relevant query made.1 made.2
  | 0, made, member => roots_sound (List.mem_eraseDups.mp member)
  | n + 1, made, member => by
      simp only [callRounds, grow, List.mem_eraseDups, List.mem_append] at member
      rcases member with old | new
      · exact callRounds_sound n made old
      · obtain ⟨caller, callerMember, inside⟩ := List.mem_flatMap.mp new
        exact callsOf_sound (callRounds_sound n caller callerMember) inside

omit [FreshNames Variable] in
theorem callRounds_sub {answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)}
    {query : Query Variable Literal Symbol} {n : Nat} {made : Vertex Symbol × List (Term Variable Literal Symbol)}
    (member : made ∈ program.callRounds answers query n) : made ∈ program.callRounds answers query (n + 1) := by
  simp only [callRounds, grow, List.mem_eraseDups, List.mem_append]
  exact .inl member

omit [FreshNames Variable] in
theorem callRounds_le {answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)}
    {query : Query Variable Literal Symbol} {made : Vertex Symbol × List (Term Variable Literal Symbol)} :
    ∀ {n m : Nat}, n ≤ m → made ∈ program.callRounds answers query n → made ∈ program.callRounds answers query m
  | n, m, le, member => by
      induction m with
      | zero => rw [Nat.le_zero.mp le] at member; exact member
      | succ m ih =>
          rcases Nat.lt_or_eq_of_le le with lt | same
          · exact callRounds_sub (ih (Nat.le_of_lt_succ lt))
          · rw [same] at member; exact member

omit [FreshNames Variable] in
theorem callRounds_nodup {answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)}
    {query : Query Variable Literal Symbol} : ∀ n, (program.callRounds answers query n).Nodup
  | 0 => nodup_eraseDups _
  | _ + 1 => nodup_eraseDups _

/-! ## The relevant calls are complete, and the rounds close -/

theorem filterMap_congr {α β : Type} {f g : α → Option β} :
    ∀ {items : List α}, (∀ item ∈ items, f item = g item) → items.filterMap f = items.filterMap g
  | [], _ => rfl
  | item :: rest, agree => by
      simp only [List.filterMap_cons, agree item List.mem_cons_self,
        filterMap_congr fun other inside => agree other (List.mem_cons_of_mem _ inside)]

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem groundBody_congr {σ τ : Variable → Term Variable Literal Symbol} {body : List (Goal Variable Literal Symbol)}
    (agree : ∀ name ∈ bodyNames body, σ name = τ name) : groundBody σ body = groundBody τ body := by
  have each : ∀ goal ∈ body, ∀ arg ∈ goal.args, subst σ arg = subst τ arg := fun goal member arg argMember =>
    subst_congr arg fun name occurs => agree name (List.mem_flatMap.mpr ⟨goal, member, names_args_sub argMember occurs⟩)
  simp only [groundBody, Prod.mk.injEq]
  refine ⟨filterMap_congr fun goal member => ?_, filterMap_congr fun goal member => ?_,
    filterMap_congr fun goal member => ?_⟩ <;>
  · cases goal <;> simp only [Goal.callAtom, Goal.nafAtom, Goal.markerAtom] <;>
      exact congrArg (fun values => some (_, values)) (List.map_congr_left fun arg inside => each _ member arg inside)

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem instanceCalls_congr {σ τ : Variable → Term Variable Literal Symbol} {bound : List Variable}
    {body : List (Goal Variable Literal Symbol)} (agree : ∀ name ∈ bodyNames body, σ name = τ name) :
    instanceCalls σ bound body = instanceCalls τ bound body := by
  unfold instanceCalls
  refine List.map_congr_left fun call inside => ?_
  have goalMember := (mem_bodyCalls inside).1
  rw [map_subst_congr fun name occurs => agree name (List.mem_flatMap.mpr ⟨call.2.1, goalMember, occurs⟩)]

omit [FreshNames Variable] in
/-- A passing instance of a body is computed, when the answer lists cover its
calls that leave an output free. -/
theorem bodyInstances_complete
    {answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)}
    (enumerates : program.Enumerates) {σ : Variable → Term Variable Literal Symbol} {bound : List Variable}
    {body : List (Goal Variable Literal Symbol)} {start : Env Variable Literal Symbol}
    (covered : ∀ call ∈ bodyCalls 0 bound body, call.2.2.2.2.free = true →
      program.Ans call.2.2.2 (call.2.2.2.1, call.2.1.args.map (subst σ)) →
        (call.2.2.2.1, call.2.1.args.map (subst σ)) ∈ answers call.2.2.2 (boundArgs call.2.2.2.2 (call.2.1.args.map (subst σ))))
    (faithful : Faithful start σ) (gives : Gives start σ bound) (scans : Scans program bound body)
    (ground : GroundOn program.constructors σ (bodyNames body)) (passes : program.Passes σ bound body) :
    (bodyNames body).map σ ∈ program.bodyInstances answers bound start body := by
  obtain ⟨next, nextMember, _, nextGives⟩ :=
    bodyEnvs_complete (position := 0) enumerates covered (List.mem_singleton.mpr rfl) faithful gives scans ground passes
  have givesBody : ∀ name ∈ bodyNames body, next name = some (σ name) :=
    fun name inside => nextGives name ((boundAfter_append_names bound body name).mpr (.inr inside))
  have valuesEq : (bodyNames body).map (envSubst next) = (bodyNames body).map σ :=
    List.map_congr_left fun name inside => by simp [envSubst, givesBody name inside]
  have agree : ∀ name ∈ bodyNames body, substOf (bodyNames body) ((bodyNames body).map σ) name = σ name :=
    fun _ inside => substOf_map σ inside
  have ok : ((bodyNames body).all fun name =>
      groundIn program.constructors (substOf (bodyNames body) ((bodyNames body).map σ) name)) &&
        program.passesWith answers (substOf (bodyNames body) ((bodyNames body).map σ)) bound body = true := by
    rw [passesWith_congr agree]
    simp only [Bool.and_eq_true, List.all_eq_true]
    exact ⟨fun name inside => by rw [agree name inside]; exact ground name inside,
      passesWith_complete (position := 0) passes covered⟩
  unfold bodyInstances
  rw [List.mem_eraseDups]
  refine List.mem_filterMap.mpr ⟨next, nextMember, ?_⟩
  dsimp only
  rw [valuesEq]
  exact ite_eq_left_of_eq_true _ _ (eq_true ok)

omit [FreshNames Variable] in
/-- With the evidence, the answer lists of an evaluation cover a call of the
graph that leaves an output free. -/
theorem answersFor_covers (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) {callee : Vertex Symbol}
    (member : callee ∈ program.vertices query) (free : callee.2.free = true) {atom : GAtom Variable Literal Symbol}
    (answer : program.Ans callee atom) : atom ∈ program.answersFor query callee (boundArgs callee.2 atom.2) :=
  answersOf_complete wellFormed queryOk evidence callee member free atom answer

omit [FreshNames Variable] in
/-- A passing instance of a vertex's rule is kept at the call of its bound
head values. -/
theorem instance_kept (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol} (queryOk : QueryOk program query)
    (evidence : program.notes query = []) {vertex : Vertex Symbol} (member : vertex ∈ program.vertices query) {index : Nat}
    {rule : Rule Variable Literal Symbol} (atVertex : (index, rule) ∈ program.rulesAt vertex)
    {σ : Variable → Term Variable Literal Symbol} (groundRule : GroundOn program.constructors σ rule.names)
    (passes : program.Passes σ (startNames vertex.2 rule.args) rule.body) :
    (index, rule.names.map σ) ∈
      program.instancesAt (program.answersFor query) vertex ((boundArgs vertex.2 rule.args).map (subst σ)) := by
  have covered : ∀ call ∈ bodyCalls 0 (startNames vertex.2 rule.args) rule.body, call.2.2.2.2.free = true →
      program.Ans call.2.2.2 (call.2.2.2.1, call.2.1.args.map (subst σ)) →
        (call.2.2.2.1, call.2.1.args.map (subst σ)) ∈
          program.answersFor query call.2.2.2 (boundArgs call.2.2.2.2 (call.2.1.args.map (subst σ))) :=
    fun call inside calleeFree answer => answersFor_covers wellFormed queryOk evidence
      (successor_mem member (mem_callsAt atVertex inside)) calleeFree answer
  obtain ⟨_, start, started, next, nextMember, gives⟩ := walk_at (Recorded := fun _ => True) wellFormed queryOk member
    atVertex groundRule passes (fun call inside calleeFree _ answer => covered call inside calleeFree answer) (fun _ _ => trivial)
  exact instancesAt_complete atVertex groundRule passes covered started nextMember gives

omit [FreshNames Variable] in
/-- **The closed round holds every relevant call**, with the evidence. -/
theorem callRounds_complete (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) (noParameters : query.parameters = [])
    {n : Nat} (closed : program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) = true) :
    ∀ vertex values, program.Relevant query vertex values → (vertex, values) ∈ program.callRounds (program.answersFor query) query n := by
  have enumerates := enumerates_of_wellFormed wellFormed
  have inRoots : ∀ made ∈ program.roots (program.answersFor query) query,
      made ∈ program.callRounds (program.answersFor query) query n :=
    fun made inside => callRounds_le (Nat.zero_le n) (List.mem_eraseDups.mpr inside)
  simp only [closedCalls, List.all_eq_true, List.contains_iff_mem] at closed
  intro vertex values relevant
  induction relevant with
  | @goal σ position goal bound vertex queryPasses inCalls =>
      obtain ⟨ground, passes⟩ := queryPasses
      have computed := bodyInstances_complete (answers := program.answersFor query) (start := fun _ => none) enumerates
        (fun call inside calleeFree answer => answersFor_covers wellFormed queryOk evidence
          (queryVertices_mem (List.mem_append_right _ (List.mem_map.mpr ⟨call, inside, rfl⟩))) calleeFree answer)
        (fun _ _ found => by cases found) (by rw [noParameters]; intro _ inside; cases inside) queryOk.goals ground passes
      refine inRoots _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, computed, ?_⟩)))
      rw [instanceCalls_congr fun name inside => substOf_map σ inside]
      exact List.mem_map.mpr ⟨_, inCalls, rfl⟩
  | @condition goal vertex member found =>
      exact inRoots _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_filterMap.mpr ⟨goal, member, by simp [found]⟩)))
  | @denial body σ position goal bound vertex denialMember ground passes inCalls =>
      have computed := bodyInstances_complete (answers := program.answersFor query) (start := fun _ => none) enumerates
        (fun call inside calleeFree answer => answersFor_covers wellFormed queryOk evidence
          (denialVertices_mem (List.mem_flatMap.mpr ⟨body, denialMember, List.mem_map.mpr ⟨call, inside, rfl⟩⟩)) calleeFree answer)
        (fun _ _ found => by cases found) (fun _ inside => by cases inside) (wellFormed.denials body denialMember) ground passes
      refine inRoots _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨body, denialMember, List.mem_flatMap.mpr ⟨_, computed, ?_⟩⟩))
      rw [instanceCalls_congr fun name inside => substOf_map σ inside]
      exact List.mem_map.mpr ⟨_, inCalls, rfl⟩
  | @rule vertex atom index rule σ position goal bound callee callerRelevant _ _ atVertex groundRule headEq passes inCalls ih =>
      have member := (relevant_vertex wellFormed queryOk callerRelevant).1
      have kept := instance_kept wellFormed queryOk evidence member atVertex groundRule passes
      have valuesEq : boundArgs vertex.2 atom.2 = (boundArgs vertex.2 rule.args).map (subst σ) := by
        rw [← headEq, boundArgs_map]
      rw [valuesEq] at ih
      refine closed _ (List.mem_flatMap.mpr ⟨_, ih, List.mem_flatMap.mpr ⟨_, kept, ?_⟩⟩)
      simp only [(mem_rulesOf.mp (mem_rulesAt.mp atVertex).1).1]
      rw [instanceCalls_congr (τ := σ) fun name inside =>
        substOf_map σ (show name ∈ rule.names from List.mem_append_right _ inside)]
      exact List.mem_map.mpr ⟨_, inCalls, rfl⟩

omit [FreshNames Variable] in
/-- A round that does not close grows: it finds a call it did not hold. -/
theorem grow_length {answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)}
    {query : Query Variable Literal Symbol} {n : Nat}
    (open_ : program.closedCalls answers (program.callRounds answers query n) = false) :
    (program.callRounds answers query n).length < (program.callRounds answers query (n + 1)).length := by
  simp only [closedCalls, List.all_eq_false, List.contains_iff_mem] at open_
  obtain ⟨made, inside, notHeld⟩ := open_
  have nodupCons : (made :: program.callRounds answers query n).Nodup :=
    List.nodup_cons.mpr ⟨notHeld, callRounds_nodup n⟩
  have sub : made :: program.callRounds answers query n ⊆ program.callRounds answers query (n + 1) := by
    intro other member
    rcases List.mem_cons.mp member with rfl | old
    · simp only [callRounds, grow, List.mem_eraseDups, List.mem_append]
      exact .inr inside
    · exact callRounds_sub old
  exact Nat.lt_of_succ_le (nodupCons.length_le_of_subset sub)

omit [FreshNames Variable] in
/-- **The rounds close**, with the evidence: they stay inside S27's finite
relevant calls, and grow until they close. -/
theorem closes (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) (noParameters : query.parameters = []) :
    ∃ n, program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) = true := by
  obtain ⟨calls, spec⟩ := relevant_finite wellFormed queryOk evidence noParameters
  have bounded : ∀ n, (program.callRounds (program.answersFor query) query n).length ≤ calls.length := fun n =>
    (callRounds_nodup n).length_le_of_subset fun made inside => spec _ _ (callRounds_sound n made inside)
  refine Classical.byContradiction fun none => ?_
  have growing : ∀ n, n ≤ (program.callRounds (program.answersFor query) query n).length := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
        have open_ : program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) =
            false := by
          cases closedEq : program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n)
          · rfl
          · exact absurd ⟨n, closedEq⟩ none
        have := grow_length open_
        omega
  have := Nat.le_trans (growing (calls.length + 1)) (bounded (calls.length + 1))
  omega

omit [FreshNames Variable] in
/-- **The relevant calls are exactly S27's**: every call found is relevant,
and, with the evidence, every relevant call is found. -/
theorem relevantCalls_iff (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) (noParameters : query.parameters = [])
    (closes_ : ∃ n, program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) = true)
    (vertex : Vertex Symbol) (values : List (Term Variable Literal Symbol)) :
    (vertex, values) ∈ program.relevantCalls query closes_ ↔ program.Relevant query vertex values := by
  obtain ⟨m, same, closed⟩ := program.roundsFrom_spec closes_ 0 _ rfl fun _ lt => absurd lt (Nat.not_lt_zero _)
  have spec : program.relevantCalls query closes_ = program.callRounds (program.answersFor query) query m := same
  rw [spec]
  exact ⟨fun member => callRounds_sound _ _ member, callRounds_complete wellFormed queryOk evidence noParameters closed vertex values⟩

/-! ## The relevant atoms -/

variable (program) in
/-- **The relevant atoms**: those of the relevant calls. -/
def relevantAtoms (query : Query Variable Literal Symbol)
    (closes_ : ∃ n, program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) = true) :
    List (GAtom Variable Literal Symbol) :=
  let answers := program.answersWith (program.levelTable (program.vertices query))
  ((program.relevantCalls query closes_).flatMap (atomsAt answers)).eraseDups

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
/-- The bound values of a call whose arguments are all bound are its
arguments. -/
theorem boundArgs_full {goal : Goal Variable Literal Symbol} {bound : List Variable} {vertex : Vertex Symbol}
    (found : goal.vertex? bound = some vertex) (notFree : vertex.2.free = false) {args : List (Term Variable Literal Symbol)}
    (lengths : args.length = goal.args.length) : boundArgs vertex.2 args = args :=
  boundArgs_all (all_bound_of_not_free notFree) (by rw [vertex?_length found, lengths])

omit [FreshNames Variable] in
/-- A relevant call of a closed query has ground values. -/
theorem relevant_ground (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (conditionsGround : ∀ goal ∈ query.conditions, goal.names = [])
    {vertex : Vertex Symbol} {values : List (Term Variable Literal Symbol)} (relevant : program.Relevant query vertex values) :
    ∀ term ∈ values, groundIn program.constructors term = true := by
  have instanceGround : ∀ {body : List (Goal Variable Literal Symbol)} {goal : Goal Variable Literal Symbol}
      {σ : Variable → Term Variable Literal Symbol}, (∀ other ∈ body, program.declares other = true ∧ program.data other = true) →
      goal ∈ body → (∀ name ∈ bodyNames body, groundIn program.constructors (σ name) = true) → ∀ {pattern : Pattern},
        ∀ term ∈ boundArgs pattern (goal.args.map (subst σ)), groundIn program.constructors term = true := by
    intro body goal σ ok member ground pattern term inside
    exact groundIn_substs (List.all_eq_true.mp (ok goal member).2)
      (fun name occurs => ground name (List.mem_flatMap.mpr ⟨goal, member, occurs⟩)) term (mem_of_mem_boundArgs inside)
  induction relevant with
  | goal queryPasses inCalls =>
      exact instanceGround (Scans.goals queryOk.goals) (mem_bodyCalls inCalls).1 queryPasses.1
  | @condition goal vertex member found =>
      intro term inside
      have argMember := mem_of_mem_boundArgs inside
      refine groundIn_of_closed (List.all_eq_true.mp (queryOk.conditions goal member).2.1 term argMember) ?_
      have none := conditionsGround goal member
      cases names : term.freeVars with
      | nil => rfl
      | cons name _ =>
          have : name ∈ goal.names := names_args_sub argMember (by rw [names]; exact List.mem_cons_self)
          rw [none] at this; cases this
  | denial denialMember ground _ inCalls =>
      exact instanceGround (Scans.goals (wellFormed.denials _ denialMember)) (mem_bodyCalls inCalls).1 ground
  | rule _ _ _ atVertex groundRule _ _ inCalls =>
      have ruleOk := wellFormed.rules _ (rulesOf_mem (mem_rulesAt.mp atVertex).1)
      exact instanceGround (Scans.goals ruleOk.scans) (mem_bodyCalls inCalls).1
        fun name inside => groundRule name (List.mem_append_right _ inside)

omit [FreshNames Variable] in
/-- A relevant call that leaves no argument free has all its arguments as
values. -/
theorem relevant_full {query : Query Variable Literal Symbol} {vertex : Vertex Symbol}
    {values : List (Term Variable Literal Symbol)} (relevant : program.Relevant query vertex values)
    (notFree : vertex.2.free = false) : values.length = vertex.2.length := by
  cases relevant with
  | goal _ inCalls =>
      rw [boundArgs_full (mem_bodyCalls inCalls).2 notFree (by simp), vertex?_length (mem_bodyCalls inCalls).2]; simp
  | condition _ found => rw [boundArgs_full found notFree rfl, vertex?_length found]
  | denial _ _ _ inCalls =>
      rw [boundArgs_full (mem_bodyCalls inCalls).2 notFree (by simp), vertex?_length (mem_bodyCalls inCalls).2]; simp
  | rule _ _ _ _ _ _ _ inCalls =>
      rw [boundArgs_full (mem_bodyCalls inCalls).2 notFree (by simp), vertex?_length (mem_bodyCalls inCalls).2]; simp

omit [FreshNames Variable] in
/-- **The relevant atoms are exactly S27's**, with the evidence. -/
theorem relevantAtoms_iff (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) (noParameters : query.parameters = [])
    (conditionsGround : ∀ goal ∈ query.conditions, goal.names = [])
    (closes_ : ∃ n, program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) = true)
    (atom : GAtom Variable Literal Symbol) :
    atom ∈ program.relevantAtoms query closes_ ↔ program.RelevantAtom query atom := by
  have calls := relevantCalls_iff wellFormed queryOk evidence noParameters closes_
  unfold relevantAtoms
  rw [List.mem_eraseDups]
  constructor
  · intro member
    obtain ⟨call, callMember, inside⟩ := List.mem_flatMap.mp member
    have relevant := (calls call.1 call.2).mp callMember
    unfold atomsAt at inside
    cases free : call.1.2.free with
    | true =>
        simp only [free, ite_true] at inside
        obtain ⟨answer, boundEq⟩ := answersFor_sound inside
        obtain ⟨symbolEq, lengths, ground⟩ := ans_atom wellFormed answer
        exact ⟨call.1, by rw [boundEq]; exact relevant, symbolEq, lengths, ground, .inr answer⟩
    | false =>
        simp only [free, Bool.false_eq_true, ite_false] at inside
        rcases List.mem_singleton.mp inside with rfl
        have lengths := relevant_full relevant free
        refine ⟨call.1, ?_, rfl, lengths, relevant_ground wellFormed queryOk conditionsGround relevant, .inl free⟩
        rw [boundArgs_all (all_bound_of_not_free free) lengths.symm]
        exact relevant
  · rintro ⟨vertex, relevant, symbolEq, lengths, _, answer⟩
    refine List.mem_flatMap.mpr ⟨(vertex, boundArgs vertex.2 atom.2), (calls _ _).mpr relevant, ?_⟩
    unfold atomsAt
    cases free : vertex.2.free with
    | true =>
        simp only [ite_true]
        rcases answer with notFree | answer
        · rw [free] at notFree; cases notFree
        · exact answersFor_covers wellFormed queryOk evidence (relevant_vertex wellFormed queryOk relevant).1 free answer
    | false =>
        simp only [Bool.false_eq_true, ite_false]
        rw [boundArgs_all (all_bound_of_not_free free) lengths.symm]
        obtain ⟨symbol, args⟩ := atom
        simp only at symbolEq
        simp [symbolEq]

/-! ## The relevant instances -/

variable (program) in
/-- **The relevant instances**: those at the relevant calls, each as its head
and its ground body. -/
def relevantInstances (query : Query Variable Literal Symbol)
    (closes_ : ∃ n, program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) = true) :
    List (GAtom Variable Literal Symbol × GroundBody Variable Literal Symbol) :=
  let answers := program.answersWith (program.levelTable (program.vertices query))
  ((program.relevantCalls query closes_).flatMap (program.instancesOfCall answers)).eraseDups

omit [FreshNames Variable] in
/-- **The relevant instances are exactly S27's**, with the evidence: each
computed one is a relevant instance's head and ground body, and each relevant
instance's head and ground body is computed. -/
theorem relevantInstances_iff (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) (noParameters : query.parameters = [])
    (closes_ : ∃ n, program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) = true)
    (atom : GAtom Variable Literal Symbol) (body : GroundBody Variable Literal Symbol) :
    (atom, body) ∈ program.relevantInstances query closes_ ↔
      ∃ rule σ, program.Instance query atom rule σ ∧ body = groundBody σ rule.body := by
  have calls := relevantCalls_iff wellFormed queryOk evidence noParameters closes_
  unfold relevantInstances
  rw [List.mem_eraseDups]
  constructor
  · intro member
    obtain ⟨call, callMember, inside⟩ := List.mem_flatMap.mp member
    have relevant := (calls call.1 call.2).mp callMember
    obtain ⟨entry, entryMember, produced⟩ := List.mem_filterMap.mp inside
    obtain ⟨rule, atVertex, _, ground, boundEq, passes⟩ := instancesAt_passes entryMember
    obtain ⟨found, headEq⟩ := mem_rulesOf.mp (mem_rulesAt.mp atVertex).1
    rw [found] at produced
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at produced
    obtain ⟨rfl, rfl⟩ := produced
    have answer : program.Ans call.1 (rule.head, rule.args.map (subst (substOf rule.names entry.2))) := .rule atVertex ground passes
    obtain ⟨_, lengths, groundArgs⟩ := ans_atom wellFormed answer
    refine ⟨rule, _, ⟨call.1, entry.1, ⟨?_, headEq, lengths, groundArgs, .inr answer⟩, atVertex, ground, rfl, passes⟩, rfl⟩
    simp only
    rw [boundArgs_map, boundEq]
    exact relevant
  · rintro ⟨rule, σ, ⟨vertex, index, entry, atVertex, groundRule, headEq, passes⟩, rfl⟩
    have member := (relevant_vertex wellFormed queryOk entry.1).1
    have kept := instance_kept wellFormed queryOk evidence member atVertex groundRule passes
    have valuesEq : boundArgs vertex.2 atom.2 = (boundArgs vertex.2 rule.args).map (subst σ) := by
      rw [← headEq, boundArgs_map]
    have callMember := (calls _ _).mpr entry.1
    rw [valuesEq] at callMember
    refine List.mem_flatMap.mpr ⟨_, callMember, List.mem_filterMap.mpr ⟨_, kept, ?_⟩⟩
    obtain ⟨found, ruleHead⟩ := mem_rulesOf.mp (mem_rulesAt.mp atVertex).1
    simp only [found, Option.map_some, Option.some.injEq, Prod.mk.injEq]
    refine ⟨?_, groundBody_congr fun name inside => substOf_map σ (List.mem_append_right _ inside)⟩
    obtain ⟨symbol, args⟩ := atom
    have symbolEq : symbol = vertex.1 := entry.2.1
    simp only at headEq
    rw [ruleHead, ← symbolEq, ← headEq]
    congr 1
    exact map_subst_congr fun name inside => substOf_map σ (List.mem_append_left _ inside)

/-! ## The denials' and the query's instances -/

variable (program) in
/-- The ground bodies of the denials' passing instances. -/
def denialBodies (query : Query Variable Literal Symbol) : List (GroundBody Variable Literal Symbol) :=
  let answers := program.answersWith (program.levelTable (program.vertices query))
  (program.denials.flatMap (program.groundBodies answers [])).eraseDups

variable (program) in
/-- The ground bodies of the query's passing instances. -/
def goalBodies (query : Query Variable Literal Symbol) : List (GroundBody Variable Literal Symbol) :=
  let answers := program.answersWith (program.levelTable (program.vertices query))
  (program.groundBodies answers query.parameters query.goals).eraseDups

omit [FreshNames Variable] in
/-- **The denials' ground bodies are exactly their passing instances'**, with
the evidence for completeness. -/
theorem denialBodies_iff (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) (body' : GroundBody Variable Literal Symbol) :
    body' ∈ program.denialBodies query ↔ ∃ body ∈ program.denials, ∃ σ : Variable → Term Variable Literal Symbol,
      GroundOn program.constructors σ (bodyNames body) ∧ program.Passes σ [] body ∧ body' = groundBody σ body := by
  unfold denialBodies groundBodies
  rw [List.mem_eraseDups]
  constructor
  · intro member
    obtain ⟨body, bodyMember, inside⟩ := List.mem_flatMap.mp member
    obtain ⟨values, valuesMember, rfl⟩ := List.mem_map.mp inside
    obtain ⟨_, ground, passes⟩ := bodyInstances_sound valuesMember
    exact ⟨body, bodyMember, _, ground, passesWith_sound (fun _ _ _ inside => (answersFor_sound inside).1) passes, rfl⟩
  · rintro ⟨body, bodyMember, σ, ground, passes, rfl⟩
    have computed := bodyInstances_complete (answers := program.answersFor query) (start := fun _ => none)
      (enumerates_of_wellFormed wellFormed)
      (fun call inside calleeFree answer => answersFor_covers wellFormed queryOk evidence
        (denialVertices_mem (List.mem_flatMap.mpr ⟨body, bodyMember, List.mem_map.mpr ⟨call, inside, rfl⟩⟩)) calleeFree answer)
      (fun _ _ found => by cases found) (fun _ inside => by cases inside) (wellFormed.denials body bodyMember) ground passes
    refine List.mem_flatMap.mpr ⟨body, bodyMember, List.mem_map.mpr ⟨_, computed, ?_⟩⟩
    exact groundBody_congr fun name inside => substOf_map σ inside

omit [FreshNames Variable] in
/-- **The query's ground bodies are exactly its passing instances'**, with the
evidence for completeness. -/
theorem goalBodies_iff (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) (noParameters : query.parameters = [])
    (body' : GroundBody Variable Literal Symbol) :
    body' ∈ program.goalBodies query ↔ ∃ σ : Variable → Term Variable Literal Symbol,
      program.QueryPasses query σ ∧ body' = groundBody σ query.goals := by
  unfold goalBodies groundBodies
  rw [List.mem_eraseDups]
  constructor
  · intro member
    obtain ⟨values, valuesMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨_, ground, passes⟩ := bodyInstances_sound valuesMember
    exact ⟨_, ⟨ground, passesWith_sound (fun _ _ _ inside => (answersFor_sound inside).1) passes⟩, rfl⟩
  · rintro ⟨σ, ⟨ground, passes⟩, rfl⟩
    have computed := bodyInstances_complete (answers := program.answersFor query) (start := fun _ => none)
      (enumerates_of_wellFormed wellFormed)
      (fun call inside calleeFree answer => answersFor_covers wellFormed queryOk evidence
        (queryVertices_mem (List.mem_append_right _ (List.mem_map.mpr ⟨call, inside, rfl⟩))) calleeFree answer)
      (fun _ _ found => by cases found) (by rw [noParameters]; intro _ inside; cases inside) queryOk.goals ground passes
    refine List.mem_map.mpr ⟨_, computed, ?_⟩
    exact groundBody_congr fun name inside => substOf_map σ inside

end Program

end AnthillModKbSpec.IR
