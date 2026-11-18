import AnthillModKbSpec.Resolution.IR.Finite

/-! # The relevant program is finite (S27)

With the finiteness evidence, a closed query's relevant calls are finitely
many (`relevant_finite`), and so are its relevant atoms (`atoms_finite`), the
relevant program, its passing ground rule instances at the relevant atoms
(`instances_finite`), and the denials' passing ground instances
(`denials_finite`).

The proof runs down the levels. A call at a level has bound values that are
data terms of an entry call of the level (`relevant_entry`: S23's bound along
the level, `same_level_data`). An entry is a root, a call of the query's goals
or conditions or of the denials, or a call made from a strictly higher level.
The roots, and the calls a passing instance makes at the values of its
vertex's bound arguments, are among those the enumeration computes
(`bodyCallValues_complete`), given the finitely many possible answers of the
calls that leave an output free (`ans_finite`). So the entries of a level are
finitely many once the higher levels' calls are, and a level's calls are
tuples over their data terms (S24's `tuples`).

**Computing it.** `Program.relevantProgram` saturates a table of calls and
their answers, reading bodies left to right, within a fuel
(`Program.saturate`, `Program.round`), and gives a closed query's relevant
program once the table is stable (`Program.stable`, a computed check): its
calls, its rule instances, and its denial instances, each instance by its
rule's or denial's index and the values of its names, without repeats. It
holds every possible answer at its free calls (`stable_answers`) and every
relevant call, rule instance, and denial instance (`relevantProgram_complete`),
so the sizes the traces report bound the relevant program from above. The
computed program can hold more: a call is made before the literals after it
are read, and the enumeration's soundness is not proved here. Building the
exact relevant program a decision runs on is S28's. A query with rigid
parameters has none of its own: it is read through its split's instances. -/

namespace AnthillModKbSpec.IR

open Semantics Completion Tabled Answers

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  [FreshNames Variable]

attribute [local instance] Machine.termEq
attribute [local irreducible] Program.levels Program.vertices

namespace Program

variable (program : Program Variable Literal Symbol)

/-! ## The calls the enumeration makes -/

/-- The calls of a body read left to right, each with its bound arguments
instantiated by every partial substitution passing the literals before it. -/
def bodyCallValues (answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)) :
    List Variable → List (Env Variable Literal Symbol) → List (Goal Variable Literal Symbol) →
      List (Vertex Symbol × List (Term Variable Literal Symbol))
  | _, _, [] => []
  | bound, envs, goal :: rest =>
      (match goal.vertex? bound with
        | some vertex => envs.filterMap fun env => (instAll env (boundArgs vertex.2 goal.args)).map (vertex, ·)
        | none => []) ++
        bodyCallValues answers (after bound goal) (envs.flatMap fun env => program.stepEnvs answers bound env goal) rest

/-- A rule read under a vertex starts from the match of its bound head
arguments against the values of the vertex's bound arguments. -/
def startEnv (vertex : Vertex Symbol) (rule : Rule Variable Literal Symbol) (values : List (Term Variable Literal Symbol)) :
    Option (Env Variable Literal Symbol) :=
  matchAll (fun _ => none) (boundArgs vertex.2 rule.args) values

/-- The calls a vertex's rules make at the values of its bound arguments. -/
def callsFrom (answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol))
    (vertex : Vertex Symbol) (values : List (Term Variable Literal Symbol)) :
    List (Vertex Symbol × List (Term Variable Literal Symbol)) :=
  (program.rulesAt vertex).flatMap fun (_, rule) =>
    match startEnv vertex rule values with
    | some start => program.bodyCallValues answers (startNames vertex.2 rule.args) [start] rule.body
    | none => []

/-- A query's root calls: its goals' calls, read from its rigid parameters,
its conditions' calls, and the denials' calls, read from no bound name. -/
def rootCalls (answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol))
    (query : Query Variable Literal Symbol) : List (Vertex Symbol × List (Term Variable Literal Symbol)) :=
  program.bodyCallValues answers query.parameters [fun _ => none] query.goals ++
    query.conditions.filterMap (fun goal => (goal.vertex? query.parameters).map fun vertex => (vertex, boundArgs vertex.2 goal.args)) ++
    program.denials.flatMap fun body => program.bodyCallValues answers [] [fun _ => none] body

variable {program}

omit [DecidableEq Literal] [FreshNames Variable] in
/-- A call's bound arguments have their names bound before it. -/
theorem boundArgs_bound {bound : List Variable} {goal : Goal Variable Literal Symbol} {vertex : Vertex Symbol}
    (found : goal.vertex? bound = some vertex) (needed : program.needs bound goal = true) :
    ∀ name ∈ namesOf (boundArgs vertex.2 goal.args), name ∈ bound := by
  cases goal with
  | call predicate args =>
      simp only [Goal.vertex?, Option.some.injEq] at found; subst found
      exact boundArgs_names
  | naf predicate args =>
      simp only [Goal.vertex?, Option.some.injEq] at found; subst found
      have allBound : boundArgs (full args.length) args = args :=
        boundArgs_all (fun flag inside => (List.mem_replicate.mp inside).2) (by simp [full])
      show ∀ name ∈ namesOf (boundArgs (full args.length) args), name ∈ bound
      rw [allBound]
      simp only [needs] at needed
      exact available_iff.mp needed
  | _ => simp [Goal.vertex?] at found

omit [FreshNames Variable] in
/-- **The walk**: reading a passing instance's body left to right, every call
the enumeration makes is recorded; when every recorded call that leaves an
output free has its possible answers listed, every call of the instance is
made, and the instance extends a computed partial substitution. -/
theorem bodyCallValues_walk
    {answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)}
    (enumerates : program.Enumerates) {σ : Variable → Term Variable Literal Symbol}
    {Recorded : Vertex Symbol × List (Term Variable Literal Symbol) → Prop} :
    ∀ {position : Nat} {bound : List Variable} {body : List (Goal Variable Literal Symbol)} {envs : List (Env Variable Literal Symbol)}
      {env : Env Variable Literal Symbol},
      (∀ call ∈ bodyCalls position bound body, call.2.2.2.2.free = true →
        Recorded (call.2.2.2, boundArgs call.2.2.2.2 (call.2.1.args.map (subst σ))) →
        program.Ans call.2.2.2 (call.2.2.2.1, call.2.1.args.map (subst σ)) →
          (call.2.2.2.1, call.2.1.args.map (subst σ)) ∈ answers call.2.2.2 (boundArgs call.2.2.2.2 (call.2.1.args.map (subst σ)))) →
      (∀ made ∈ program.bodyCallValues answers bound envs body, Recorded made) →
      env ∈ envs → Faithful env σ → Gives env σ bound → Scans program bound body →
        GroundOn program.constructors σ (bodyNames body) → program.Passes σ bound body →
          (∀ call ∈ bodyCalls position bound body,
            (call.2.2.2, boundArgs call.2.2.2.2 (call.2.1.args.map (subst σ))) ∈ program.bodyCallValues answers bound envs body) ∧
          ∃ next ∈ program.bodyEnvs answers bound envs body, Faithful next σ ∧ Gives next σ (boundAfter bound body)
  | _, _, [], _, env, _, _, member, faithful, gives, _, _, _ => ⟨fun _ inside => (by cases inside), env, member, faithful, gives⟩
  | position, bound, goal :: rest, envs, env, covered, records, member, faithful, gives, .cons declared data needed restScans,
      ground, passes => by
      have goalGround : GroundOn program.constructors σ goal.names := fun name occurs =>
        ground name (List.mem_flatMap.mpr ⟨goal, List.mem_cons_self, occurs⟩)
      have restGround : GroundOn program.constructors σ (bodyNames rest) := fun name occurs =>
        ground name (by simp only [bodyNames, List.flatMap_cons, List.mem_append]; exact .inr occurs)
      have headMade : ∀ vertex, goal.vertex? bound = some vertex →
          (vertex, boundArgs vertex.2 (goal.args.map (subst σ))) ∈ program.bodyCallValues answers bound envs (goal :: rest) := by
        intro vertex found
        simp only [bodyCallValues, found, List.mem_append]
        refine .inl (List.mem_filterMap.mpr ⟨env, member, ?_⟩)
        have boundData : dataInAll program.constructors (boundArgs vertex.2 goal.args) = true :=
          (dataInAll_iff _).mpr fun arg inside => List.all_eq_true.mp data arg (mem_of_mem_boundArgs inside)
        rw [instAll_gives _ boundData fun name inside => gives name (boundArgs_bound found needed name inside), boundArgs_map]
        rfl
      have split : ((∃ vertex, goal.vertex? bound = some vertex ∧ vertex.2.free = true ∧
            program.Ans vertex (vertex.1, goal.args.map (subst σ))) ∨
          ((∀ vertex, goal.vertex? bound = some vertex → vertex.2.free = false) ∧ program.fixedAt σ goal)) ∧
          program.Passes σ (after bound goal) rest := by
        cases passes with
        | free found free answer restPasses => exact ⟨.inl ⟨_, found, free, answer⟩, restPasses⟩
        | fixed notFree fixed restPasses => exact ⟨.inr ⟨notFree, fixed⟩, restPasses⟩
      have coveredHere : ∀ vertex, goal.vertex? bound = some vertex → vertex.2.free = true →
          program.Ans vertex (vertex.1, goal.args.map (subst σ)) →
            (vertex.1, goal.args.map (subst σ)) ∈ answers vertex (boundArgs vertex.2 (goal.args.map (subst σ))) :=
        fun vertex found free answer => covered _ (mem_bodyCalls_head (rest := rest) (position := position) found) free
          (records _ (headMade vertex found)) answer
      obtain ⟨step, stepMember, stepFaithful, stepGives⟩ :=
        stepEnvs_complete enumerates faithful gives coveredHere data needed goalGround declared split.1
      obtain ⟨restMade, next, nextMember, nextFaithful, nextGives⟩ := bodyCallValues_walk (position := position + 1) enumerates
        (fun other inside => covered other (mem_bodyCalls_tail inside))
        (fun made inside => records made (by simp only [bodyCallValues, List.mem_append]; exact .inr inside))
        (List.mem_flatMap.mpr ⟨env, member, stepMember⟩) stepFaithful stepGives restScans restGround split.2
      refine ⟨fun call callMember => ?_, next, nextMember, nextFaithful, nextGives⟩
      simp only [bodyCalls, List.mem_append] at callMember
      rcases callMember with here | there
      · cases found : goal.vertex? bound with
        | none => rw [found] at here; cases here
        | some vertex =>
            rw [found] at here
            simp only [List.mem_singleton] at here
            subst here
            exact headMade vertex found
      · simp only [bodyCallValues, List.mem_append]
        exact .inr (restMade call there)

omit [FreshNames Variable] in
/-- **The enumeration makes every call of a passing instance**: given answer
lists holding the possible answers of the body's calls that leave an output
free, each call of a passing instance, with its bound arguments' values, is
among the calls the enumeration computes. -/
theorem bodyCallValues_complete
    {answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)}
    (enumerates : program.Enumerates) {σ : Variable → Term Variable Literal Symbol} {position : Nat} {bound : List Variable}
    {body : List (Goal Variable Literal Symbol)} {envs : List (Env Variable Literal Symbol)} {env : Env Variable Literal Symbol}
    (covered : ∀ call ∈ bodyCalls position bound body, call.2.2.2.2.free = true →
      program.Ans call.2.2.2 (call.2.2.2.1, call.2.1.args.map (subst σ)) →
        (call.2.2.2.1, call.2.1.args.map (subst σ)) ∈ answers call.2.2.2 (boundArgs call.2.2.2.2 (call.2.1.args.map (subst σ))))
    (member : env ∈ envs) (faithful : Faithful env σ) (gives : Gives env σ bound) (scans : Scans program bound body)
    (ground : GroundOn program.constructors σ (bodyNames body)) (passes : program.Passes σ bound body) :
    ∀ call ∈ bodyCalls position bound body,
      (call.2.2.2, boundArgs call.2.2.2.2 (call.2.1.args.map (subst σ))) ∈ program.bodyCallValues answers bound envs body :=
  (bodyCallValues_walk (Recorded := fun _ => True) enumerates (fun call inside free _ answer => covered call inside free answer)
    (fun _ _ => trivial) member faithful gives scans ground passes).1

variable [FreshNames Variable] in
omit [FreshNames Variable] in
/-- The possible answers the enumeration reads: with the evidence, a call of
the graph that leaves an output free has its possible answers in
`answerList`. -/
theorem answerList_covers (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) {vertex : Vertex Symbol}
    (member : vertex ∈ program.vertices query) (free : vertex.2.free = true) {atom : GAtom Variable Literal Symbol}
    (answer : program.Ans vertex atom) : atom ∈ answerList program vertex (boundArgs vertex.2 atom.2) :=
  answerList_spec (ans_finite wellFormed queryOk evidence (enumerates_of_wellFormed wellFormed) vertex member free _) _ answer rfl

omit [FreshNames Variable] in
/-- **The walk at a vertex**: a passing instance of a vertex's rule, read from
the values of the vertex's bound arguments, makes its calls among those the
vertex's rules make there, and extends a computed partial substitution on
every name of its rule, when every recorded call that leaves an output free
has its possible answers listed. -/
theorem walk_at (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol} (queryOk : QueryOk program query)
    {answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)}
    {Recorded : Vertex Symbol × List (Term Variable Literal Symbol) → Prop} {vertex : Vertex Symbol}
    (member : vertex ∈ program.vertices query) {index : Nat} {rule : Rule Variable Literal Symbol}
    (atVertex : (index, rule) ∈ program.rulesAt vertex) {σ : Variable → Term Variable Literal Symbol}
    (groundRule : GroundOn program.constructors σ rule.names)
    (passes : program.Passes σ (startNames vertex.2 rule.args) rule.body)
    (covered : ∀ call ∈ bodyCalls 0 (startNames vertex.2 rule.args) rule.body, call.2.2.2.2.free = true →
      Recorded (call.2.2.2, boundArgs call.2.2.2.2 (call.2.1.args.map (subst σ))) →
      program.Ans call.2.2.2 (call.2.2.2.1, call.2.1.args.map (subst σ)) →
        (call.2.2.2.1, call.2.1.args.map (subst σ)) ∈ answers call.2.2.2 (boundArgs call.2.2.2.2 (call.2.1.args.map (subst σ))))
    (records : ∀ made ∈ program.callsFrom answers vertex ((boundArgs vertex.2 rule.args).map (subst σ)), Recorded made) :
    (∀ call ∈ bodyCalls 0 (startNames vertex.2 rule.args) rule.body,
      (call.2.2.2, boundArgs call.2.2.2.2 (call.2.1.args.map (subst σ))) ∈
        program.callsFrom answers vertex ((boundArgs vertex.2 rule.args).map (subst σ))) ∧
    ∃ start, startEnv vertex rule ((boundArgs vertex.2 rule.args).map (subst σ)) = some start ∧
      ∃ next ∈ program.bodyEnvs answers (startNames vertex.2 rule.args) [start] rule.body,
        ∀ name ∈ rule.names, next name = some (σ name) := by
  have ruleOk := wellFormed.rules rule (rulesOf_mem (mem_rulesAt.mp atVertex).1)
  have headData : ∀ arg ∈ boundArgs vertex.2 rule.args, dataIn program.constructors arg = true :=
    fun arg inside => ruleOk.data _ (mem_of_mem_boundArgs inside)
  obtain ⟨start, matched, startFaithful, startGives, _⟩ := matchAll_complete (σ := σ) (env := fun _ => Option.none)
    (boundArgs vertex.2 rule.args) ((dataInAll_iff _).mpr headData) (fun _ _ found => by cases found)
  have covers := start_covers wellFormed (covering_of_check wellFormed queryOk vertex member) atVertex
  have inCallsFrom : ∀ made ∈ program.bodyCallValues answers (startNames vertex.2 rule.args) [start] rule.body,
      made ∈ program.callsFrom answers vertex ((boundArgs vertex.2 rule.args).map (subst σ)) := by
    intro made inside
    refine List.mem_flatMap.mpr ⟨(index, rule), atVertex, ?_⟩
    simp only [startEnv, matched]
    exact inside
  obtain ⟨made, next, nextMember, _, nextGives⟩ := bodyCallValues_walk (position := 0) (enumerates_of_wellFormed wellFormed)
    covered (fun made inside => records made (inCallsFrom made inside)) (List.mem_singleton.mpr rfl) startFaithful startGives
    (Scans.mono ruleOk.scans covers) (fun name occurs => groundRule name (List.mem_append_right _ occurs)) passes
  refine ⟨fun call inside => inCallsFrom _ (made call inside), start, matched, next, nextMember, fun name inside => nextGives name ?_⟩
  rcases List.mem_append.mp inside with fromHead | fromBody
  · obtain ⟨arg, argMember, occurs⟩ := List.mem_flatMap.mp fromHead
    rcases (boundAfter_append_names _ rule.body name).mp (ruleOk.bound arg argMember name occurs) with fromInputs | inBody
    · exact (boundAfter_append_names _ rule.body name).mpr (.inl (covers name fromInputs))
    · exact (boundAfter_append_names _ rule.body name).mpr (.inr inBody)
  · exact (boundAfter_append_names _ rule.body name).mpr (.inr fromBody)

omit [FreshNames Variable] in
/-- **A passing instance's calls are among those its vertex's rules make** at
the values of the vertex's bound arguments. -/
theorem callsFrom_complete (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) {vertex : Vertex Symbol}
    (member : vertex ∈ program.vertices query) {index : Nat} {rule : Rule Variable Literal Symbol}
    (atVertex : (index, rule) ∈ program.rulesAt vertex) {σ : Variable → Term Variable Literal Symbol}
    (groundRule : GroundOn program.constructors σ rule.names)
    (passes : program.Passes σ (startNames vertex.2 rule.args) rule.body)
    {call : Nat × Goal Variable Literal Symbol × List Variable × Vertex Symbol}
    (inCalls : call ∈ bodyCalls 0 (startNames vertex.2 rule.args) rule.body) :
    (call.2.2.2, boundArgs call.2.2.2.2 (call.2.1.args.map (subst σ))) ∈
      program.callsFrom (answerList program) vertex ((boundArgs vertex.2 rule.args).map (subst σ)) :=
  (walk_at (Recorded := fun _ => True) wellFormed queryOk member atVertex groundRule passes
    (fun _ inside calleeFree _ answer => answerList_covers wellFormed queryOk evidence
      (successor_mem member (mem_callsAt atVertex inside)) calleeFree answer)
    (fun _ _ => trivial)).1 call inCalls

/-! ## Entries of a level -/

variable (program) in
/-- An entry of its level: a root call, or a call made by a relevant call at
a strictly higher level. -/
def EntryCall (query : Query Variable Literal Symbol) (entry : Vertex Symbol × List (Term Variable Literal Symbol)) : Prop :=
  entry ∈ program.rootCalls (answerList program) query ∨
    ∃ caller : Vertex Symbol × List (Term Variable Literal Symbol), program.Relevant query caller.1 caller.2 ∧
      program.levels query entry.1 < program.levels query caller.1 ∧
        entry ∈ program.callsFrom (answerList program) caller.1 caller.2

omit [FreshNames Variable] in
/-- **Every relevant call keeps to the data terms of an entry of its level**:
its bound values are data terms of the entry's and the program's ground
terms. -/
theorem relevant_entry (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) (noParameters : query.parameters = [])
    {vertex : Vertex Symbol} {values : List (Term Variable Literal Symbol)} (relevant : program.Relevant query vertex values) :
    ∃ entry, program.EntryCall query entry ∧ program.levels query entry.1 = program.levels query vertex ∧
      ∀ value ∈ values, InData program.groundTerms entry.2 value := by
  have self : ∀ items : List (Term Variable Literal Symbol), ∀ value ∈ items, InData program.groundTerms items value :=
    fun _ value member => .inl ⟨value, member, .refl _⟩
  induction relevant with
  | @goal σ position goal bound vertex queryPasses inCalls =>
      refine ⟨(vertex, boundArgs vertex.2 (goal.args.map (subst σ))), .inl (List.mem_append_left _ (List.mem_append_left _ ?_)),
        rfl, self _⟩
      obtain ⟨ground, passes⟩ := queryPasses
      exact bodyCallValues_complete (env := fun _ => Option.none) (enumerates_of_wellFormed wellFormed)
        (fun other inside calleeFree answer => answerList_covers wellFormed queryOk evidence
          (queryVertices_mem (List.mem_append_right _ (List.mem_map.mpr ⟨other, inside, rfl⟩))) calleeFree answer)
        (List.mem_singleton.mpr rfl) (fun _ _ found => by cases found) (by rw [noParameters]; intro _ member; cases member)
        queryOk.goals ground passes (position, goal, bound, vertex) inCalls
  | @condition goal vertex member found =>
      refine ⟨(vertex, boundArgs vertex.2 goal.args), .inl (List.mem_append_left _ (List.mem_append_right _ ?_)), rfl, self _⟩
      exact List.mem_filterMap.mpr ⟨goal, member, by simp [found]⟩
  | @denial body σ position goal bound vertex denialMember ground passes inCalls =>
      refine ⟨(vertex, boundArgs vertex.2 (goal.args.map (subst σ))),
        .inl (List.mem_append_right _ (List.mem_flatMap.mpr ⟨body, denialMember, ?_⟩)), rfl, self _⟩
      exact bodyCallValues_complete (env := fun _ => Option.none) (enumerates_of_wellFormed wellFormed)
        (fun other inside calleeFree answer => answerList_covers wellFormed queryOk evidence
          (denialVertices_mem (List.mem_flatMap.mpr ⟨body, denialMember, List.mem_map.mpr ⟨other, inside, rfl⟩⟩)) calleeFree answer)
        (List.mem_singleton.mpr rfl) (fun _ _ found => by cases found) (fun _ member => by cases member)
        (wellFormed.denials body denialMember) ground passes (position, goal, bound, vertex) inCalls
  | @rule vertex atom index rule σ position goal bound callee callerRelevant _ _ atVertex groundRule headEq passes inCalls ih =>
      have member := (relevant_vertex wellFormed queryOk callerRelevant).1
      have inCallsAt := mem_callsAt atVertex inCalls
      have levelLe := program.levels_le member (List.mem_map.mpr ⟨_, inCallsAt, rfl⟩)
      rcases Nat.lt_or_eq_of_le levelLe with lower | same
      · refine ⟨(callee, boundArgs callee.2 (goal.args.map (subst σ))),
          .inr ⟨(vertex, boundArgs vertex.2 atom.2), callerRelevant, lower, ?_⟩, rfl, self _⟩
        rw [← headEq, boundArgs_map]
        exact callsFrom_complete (call := (position, goal, bound, callee)) wellFormed queryOk evidence member atVertex groundRule
          passes inCalls
      · obtain ⟨entry, entryCall, entryLevel, inData⟩ := ih
        refine ⟨entry, entryCall, entryLevel.trans same.symm, fun value inside => ?_⟩
        have sameData := same_level_data (call := (position, goal, bound, callee)) wellFormed evidence
          (enumerates_of_wellFormed wellFormed) member atVertex groundRule passes inCalls same value inside
        rw [headEq] at sameData
        exact sameData.trans inData

/-! ## Finiteness -/

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem length_boundArgs_le {α : Type} : ∀ (pattern : Pattern) (args : List α), (boundArgs pattern args).length ≤ pattern.length
  | [], args => by cases args <;> simp [boundArgs]
  | _ :: _, [] => by simp [boundArgs]
  | bound :: pattern, arg :: args => by
      have rest := length_boundArgs_le pattern args
      simp only [boundArgs, List.zip_cons_cons, List.filterMap_cons] at rest ⊢
      cases bound <;> simp <;> omega

omit [FreshNames Variable] in
theorem relevant_length {query : Query Variable Literal Symbol} {vertex : Vertex Symbol}
    {values : List (Term Variable Literal Symbol)} (relevant : program.Relevant query vertex values) :
    values.length ≤ vertex.2.length := by
  cases relevant <;> exact length_boundArgs_le _ _

omit [DecidableEq Literal] [FreshNames Variable] in
theorem levels_le_length {query : Query Variable Literal Symbol} {vertex : Vertex Symbol}
    (member : vertex ∈ program.vertices query) : program.levels query vertex ≤ (program.vertices query).length := by
  unfold levels
  rw [program.levelIn_table member]
  exact List.length_filter_le _ _

omit [FreshNames Variable] in
/-- **The relevant calls are finite.** With the evidence, a closed query has
finitely many relevant calls: by induction down the levels, a level's calls
are tuples over the data terms of its entries, the roots and the calls made
from the higher levels' finitely many calls. -/
theorem relevant_finite (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) (noParameters : query.parameters = []) :
    ∃ calls : List (Vertex Symbol × List (Term Variable Literal Symbol)),
      ∀ vertex values, program.Relevant query vertex values → (vertex, values) ∈ calls := by
  let Bounded := fun (level : Nat) => ∃ calls : List (Vertex Symbol × List (Term Variable Literal Symbol)),
    ∀ vertex values, program.Relevant query vertex values → level ≤ program.levels query vertex → (vertex, values) ∈ calls
  have top : Bounded ((program.vertices query).length + 1) := by
    refine ⟨[], fun vertex values relevant above => ?_⟩
    have := levels_le_length (relevant_vertex wellFormed queryOk relevant).1
    omega
  have step : ∀ level, Bounded (level + 1) → Bounded level := by
    intro level ⟨higher, higherSpec⟩
    let entries := program.rootCalls (answerList program) query ++
      higher.flatMap fun caller => program.callsFrom (answerList program) caller.1 caller.2
    let terms := entries.flatMap fun entry => dataTerms program.groundTerms entry.2
    refine ⟨higher ++ (program.vertices query).flatMap fun vertex =>
      (List.range (vertex.2.length + 1)).flatMap fun count => (tuples terms count).map (vertex, ·), ?_⟩
    intro vertex values relevant atLeast
    by_cases above : level + 1 ≤ program.levels query vertex
    · exact List.mem_append_left _ (higherSpec vertex values relevant above)
    · obtain ⟨entry, entryCall, entryLevel, inData⟩ := relevant_entry wellFormed queryOk evidence noParameters relevant
      have entryMember : entry ∈ entries := by
        rcases entryCall with root | ⟨caller, callerRelevant, lower, inCalls⟩
        · exact List.mem_append_left _ root
        · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨caller,
            higherSpec caller.1 caller.2 callerRelevant (by omega), inCalls⟩)
      have valuesIn : ∀ value ∈ values, value ∈ terms := fun value inside =>
        List.mem_flatMap.mpr ⟨entry, entryMember, (inData value inside).mem⟩
      have vertexMember := (relevant_vertex wellFormed queryOk relevant).1
      have lengthLe := relevant_length relevant
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨vertex, vertexMember, List.mem_flatMap.mpr
        ⟨values.length, List.mem_range.mpr (by omega), List.mem_map.mpr ⟨values, mem_tuples valuesIn, rfl⟩⟩⟩)
  have down : ∀ count level, level + count = (program.vertices query).length + 1 → Bounded level := by
    intro count
    induction count with
    | zero => intro level sum; rw [Nat.add_zero] at sum; rw [sum]; exact top
    | succ count ih => intro level sum; exact step level (ih (level + 1) (by omega))
  obtain ⟨calls, spec⟩ := down _ 0 (Nat.zero_add _)
  exact ⟨calls, fun vertex values relevant => spec vertex values relevant (Nat.zero_le _)⟩

omit [FreshNames Variable] in
/-- **The relevant atoms are finite**: those of a vertex that leaves an output
free are possible answers at a relevant call, the others are the relevant
calls themselves. -/
theorem atoms_finite (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) (noParameters : query.parameters = []) :
    ∃ atoms : List (GAtom Variable Literal Symbol), ∀ atom, program.RelevantAtom query atom → atom ∈ atoms := by
  obtain ⟨calls, spec⟩ := relevant_finite wellFormed queryOk evidence noParameters
  refine ⟨calls.flatMap fun call => if call.1.2.free then answerList program call.1 call.2 else [(call.1.1, call.2)], ?_⟩
  intro atom ⟨vertex, relevant, symbolEq, lengths, _, answer⟩
  refine List.mem_flatMap.mpr ⟨(vertex, boundArgs vertex.2 atom.2), spec _ _ relevant, ?_⟩
  cases free : vertex.2.free with
  | false =>
      have allBound : ∀ flag ∈ vertex.2, flag = true := by
        intro flag inside
        simp only [Pattern.free, List.any_eq_false, beq_iff_eq] at free
        cases flag
        · exact absurd rfl (free false inside)
        · rfl
      simp only [Bool.false_eq_true, ite_false, List.mem_singleton]
      rw [boundArgs_all allBound lengths.symm]
      exact Prod.ext symbolEq rfl
  | true =>
      simp only [ite_true]
      have isAnswer := answer.resolve_left (by simp [free])
      exact answerList_covers wellFormed queryOk evidence (relevant_vertex wellFormed queryOk relevant).1
        free isAnswer

variable (program) in
/-- The passing instances the enumeration computes at calls: each rule of a
call's vertex, read from the call's values, by the rule's index and the values
a computed partial substitution gives its names. -/
def instancesOf (answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol))
    (calls : List (Vertex Symbol × List (Term Variable Literal Symbol))) :
    List (Nat × List (Option (Term Variable Literal Symbol))) :=
  calls.flatMap fun call => (program.rulesAt call.1).flatMap fun (index, rule) =>
    match startEnv call.1 rule call.2 with
    | some start => (program.bodyEnvs answers (startNames call.1.2 rule.args) [start] rule.body).map fun env =>
        (index, rule.names.map env)
    | none => []

variable (program) in
/-- The denials' passing instances the enumeration computes, read from no
bound name, by the denial's index and the values given its names. -/
def denialInstancesOf (answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)) :
    List (Nat × List (Option (Term Variable Literal Symbol))) :=
  program.denials.zipIdx.flatMap fun (body, index) =>
    (program.bodyEnvs answers [] [fun _ => none] body).map fun env => (index, (bodyNames body).map env)

omit [FreshNames Variable] in
theorem instance_mem {answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)}
    {calls : List (Vertex Symbol × List (Term Variable Literal Symbol))} {vertex : Vertex Symbol} {index : Nat}
    {rule : Rule Variable Literal Symbol} {σ : Variable → Term Variable Literal Symbol}
    (atVertex : (index, rule) ∈ program.rulesAt vertex)
    (callMember : (vertex, (boundArgs vertex.2 rule.args).map (subst σ)) ∈ calls) {start : Env Variable Literal Symbol}
    (started : startEnv vertex rule ((boundArgs vertex.2 rule.args).map (subst σ)) = some start) {next : Env Variable Literal Symbol}
    (nextMember : next ∈ program.bodyEnvs answers (startNames vertex.2 rule.args) [start] rule.body)
    (gives : ∀ name ∈ rule.names, next name = some (σ name)) :
    (index, rule.names.map fun name => some (σ name)) ∈ program.instancesOf answers calls := by
  refine List.mem_flatMap.mpr ⟨_, callMember, List.mem_flatMap.mpr ⟨(index, rule), atVertex, ?_⟩⟩
  simp only [started]
  refine List.mem_map.mpr ⟨next, nextMember, ?_⟩
  rw [List.map_congr_left gives]

omit [FreshNames Variable] in
/-- **The relevant program is finite**: its passing ground rule instances at
the relevant atoms are finitely many, each given by its rule's index and the
values of its rule's names. -/
theorem instances_finite (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) (noParameters : query.parameters = []) :
    ∃ instances : List (Nat × List (Option (Term Variable Literal Symbol))),
      ∀ atom rule σ, program.Instance query atom rule σ →
        ∃ index, program.rules[index]? = some rule ∧ (index, rule.names.map fun name => some (σ name)) ∈ instances := by
  obtain ⟨calls, spec⟩ := relevant_finite wellFormed queryOk evidence noParameters
  refine ⟨program.instancesOf (answerList program) calls, ?_⟩
  intro atom rule σ ⟨vertex, index, entry, atVertex, groundRule, headEq, passes⟩
  have member := (relevant_vertex wellFormed queryOk entry.1).1
  have valuesEq : boundArgs vertex.2 atom.2 = (boundArgs vertex.2 rule.args).map (subst σ) := by
    rw [← headEq, boundArgs_map]
  obtain ⟨_, start, started, next, nextMember, gives⟩ := walk_at (Recorded := fun _ => True) wellFormed queryOk member atVertex
    groundRule passes (fun _ inside calleeFree _ answer => answerList_covers wellFormed queryOk evidence
      (successor_mem member (mem_callsAt atVertex inside)) calleeFree answer) (fun _ _ => trivial)
  exact ⟨index, (mem_rulesOf.mp (mem_rulesAt.mp atVertex).1).1,
    instance_mem atVertex (valuesEq ▸ spec _ _ entry.1) started nextMember gives⟩

omit [FreshNames Variable] in
theorem denialInstance_mem {answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)}
    {index : Nat} {body : List (Goal Variable Literal Symbol)} (found : program.denials[index]? = some body)
    {σ : Variable → Term Variable Literal Symbol} {next : Env Variable Literal Symbol}
    (nextMember : next ∈ program.bodyEnvs answers [] [fun _ => Option.none] body)
    (gives : Gives next σ (boundAfter [] body)) :
    (index, (bodyNames body).map fun name => some (σ name)) ∈ program.denialInstancesOf answers := by
  refine List.mem_flatMap.mpr ⟨(body, index), List.mem_zipIdx_iff_getElem?.mpr found, List.mem_map.mpr ⟨next, nextMember, ?_⟩⟩
  rw [List.map_congr_left fun name inside => gives name ((boundAfter_append_names _ body name).mpr (.inr inside))]

omit [FreshNames Variable] in
/-- **The denials' passing instances are finite**, each given by its denial's
index and the values of its names. -/
theorem denials_finite (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) :
    ∃ instances : List (Nat × List (Option (Term Variable Literal Symbol))),
      ∀ index body, program.denials[index]? = some body → ∀ σ : Variable → Term Variable Literal Symbol,
        GroundOn program.constructors σ (bodyNames body) → program.Passes σ [] body →
          (index, (bodyNames body).map fun name => some (σ name)) ∈ instances := by
  refine ⟨program.denialInstancesOf (answerList program), ?_⟩
  intro index body found σ ground passes
  have denialMember := List.mem_of_getElem? found
  obtain ⟨next, nextMember, _, nextGives⟩ := bodyEnvs_complete (answers := answerList program) (position := 0)
    (env := fun _ => Option.none) (enumerates_of_wellFormed wellFormed)
    (fun other inside calleeFree answer => answerList_covers wellFormed queryOk evidence
      (denialVertices_mem (List.mem_flatMap.mpr ⟨body, denialMember, List.mem_map.mpr ⟨other, inside, rfl⟩⟩)) calleeFree answer)
    (List.mem_singleton.mpr rfl) (fun _ _ found => by cases found) (fun _ member => by cases member)
    (wellFormed.denials body denialMember) ground passes
  exact denialInstance_mem found nextMember nextGives

end Program

/-! ## Computing the relevant program -/

/-- A table of calls, each with the answers listed for it. -/
abbrev CallTable (Variable Literal Symbol : Type) :=
  List ((Vertex Symbol × List (Term Variable Literal Symbol)) × List (GAtom Variable Literal Symbol))

/-- The answers a table lists for a call. -/
def tableAnswers (table : CallTable Variable Literal Symbol) (vertex : Vertex Symbol)
    (values : List (Term Variable Literal Symbol)) : List (GAtom Variable Literal Symbol) :=
  ((table.find? (·.1 == (vertex, values))).map (·.2)).getD []

namespace Program

variable {program : Program Variable Literal Symbol}

variable (program) in
/-- The heads a vertex's rules give at the values of its bound arguments, from
the answers listed for their calls. -/
def answersFrom (answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol))
    (vertex : Vertex Symbol) (values : List (Term Variable Literal Symbol)) : List (GAtom Variable Literal Symbol) :=
  ((program.rulesAt vertex).flatMap fun (_, rule) =>
    match startEnv vertex rule values with
    | some start => (program.bodyEnvs answers (startNames vertex.2 rule.args) [start] rule.body).filterMap fun env =>
        (instAll env rule.args).map (rule.head, ·)
    | none => []).eraseDups

variable (program) in
/-- One round of the saturation: the table's calls, the roots, and the calls
the table's calls make, each with its answers and those its vertex's rules
give from the table's. -/
def round (query : Query Variable Literal Symbol) (table : CallTable Variable Literal Symbol) : CallTable Variable Literal Symbol :=
  ((table.map (·.1) ++ program.rootCalls (tableAnswers table) query ++
      table.flatMap fun entry => program.callsFrom (tableAnswers table) entry.1.1 entry.1.2).eraseDups).map fun call =>
    (call, (tableAnswers table call.1 call.2 ++
      if call.1.2.free then program.answersFrom (tableAnswers table) call.1 call.2 else []).eraseDups)

variable (program) in
/-- A table is stable when a round adds nothing to it: it lists every root,
every call its calls make, and every answer their rules give. -/
def stable (query : Query Variable Literal Symbol) (table : CallTable Variable Literal Symbol) : Bool :=
  (program.rootCalls (tableAnswers table) query).all (table.map (·.1)).contains &&
    (table.map (·.1)).all fun call =>
      (program.callsFrom (tableAnswers table) call.1 call.2).all (table.map (·.1)).contains &&
        (!call.1.2.free || (program.answersFrom (tableAnswers table) call.1 call.2).all (tableAnswers table call.1 call.2).contains)

/-- A table's size: its calls and their answers. A round never shrinks it. -/
def tableSize (table : CallTable Variable Literal Symbol) : Nat :=
  table.length + (table.map (·.2.length)).sum

variable (program) in
/-- Rounds until a round adds nothing, within `fuel` rounds. Whether the
result is stable is checked once, by `relevantProgram`. -/
def saturate (query : Query Variable Literal Symbol) : Nat → CallTable Variable Literal Symbol → CallTable Variable Literal Symbol
  | 0, table => table
  | fuel + 1, table =>
      let next := program.round query table
      if tableSize next = tableSize table then table else saturate query fuel next

/-- A computed relevant program: its calls, and its rule instances and its
denial instances, each by its rule's or its denial's index and the values of
its names, without repeats. -/
structure Computed (Variable Literal Symbol : Type) where
  calls : List (Vertex Symbol × List (Term Variable Literal Symbol))
  instances : List (Nat × List (Option (Term Variable Literal Symbol)))
  denials : List (Nat × List (Option (Term Variable Literal Symbol)))

variable (program) in
/-- **The computed relevant program** of a closed query: the saturated table's
calls, and the passing rule and denial instances the enumeration gives from
its answers. None for a query with rigid parameters (read through its split's
instances) and when the table is not stable within the fuel. -/
def relevantProgram (query : Query Variable Literal Symbol) (fuel : Nat) : Option (Computed Variable Literal Symbol) :=
  if query.parameters.isEmpty then
    let table := program.saturate query fuel []
    if program.stable query table then
      some ⟨table.map (·.1), (program.instancesOf (tableAnswers table) (table.map (·.1))).eraseDups,
        (program.denialInstancesOf (tableAnswers table)).eraseDups⟩
    else none
  else none

omit [FreshNames Variable] in
/-- **A stable table lists every possible answer** at a listed call of the
graph that leaves an output free, by induction on the call's rank. -/
theorem stable_answers (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) {table : CallTable Variable Literal Symbol}
    (stableTable : program.stable query table = true) :
    ∀ vertex values, (vertex, values) ∈ table.map (·.1) → vertex ∈ program.vertices query → vertex.2.free = true →
      ∀ atom, program.Ans vertex atom → boundArgs vertex.2 atom.2 = values → atom ∈ tableAnswers table vertex values := by
  simp only [stable, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, Bool.or_eq_true, Bool.not_eq_true'] at stableTable
  obtain ⟨_, closedCalls⟩ := stableTable
  have parts := evidence_of_notes evidence
  have listed : ∀ n m, ∀ vertex values, (vertex, values) ∈ table.map (·.1) → vertex ∈ program.vertices query →
      vertex.2.free = true → program.levels query vertex = n → sizeAll values = m → ∀ atom, program.Ans vertex atom →
        boundArgs vertex.2 atom.2 = values → atom ∈ tableAnswers table vertex values := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ihLevel =>
    intro m
    induction m using Nat.strongRecOn with
    | ind m ihSize =>
    intro vertex values recorded member free levelEq sizeEq atom answer boundEq
    cases answer with
    | @rule _ index rule σ atVertex groundRule passes =>
        have ruleOk := wellFormed.rules rule (rulesOf_mem (mem_rulesAt.mp atVertex).1)
        have valuesEq : values = (boundArgs vertex.2 rule.args).map (subst σ) := by rw [← boundEq, boundArgs_map]
        subst valuesEq
        obtain ⟨_, start, started, next, nextMember, gives⟩ :=
          walk_at (Recorded := (· ∈ table.map (·.1))) wellFormed queryOk member atVertex groundRule passes
            (fun call inside calleeFree calleeRecorded calleeAnswer => by
              obtain ⟨calleeMember, rank⟩ := call_rank parts member free atVertex inside calleeFree σ
              obtain ⟨_, goal, bound, callee⟩ := call
              simp only at calleeFree calleeRecorded calleeAnswer calleeMember rank ⊢
              generalize hLevel : program.levels query callee = calleeLevel at rank
              generalize hVertexLevel : program.levels query vertex = vertexLevel at rank levelEq
              subst levelEq
              rcases rank with lower | ⟨same, smaller⟩
              · exact ihLevel calleeLevel lower _ _ _ calleeRecorded calleeMember calleeFree hLevel rfl _ calleeAnswer rfl
              · subst same
                rw [← boundArgs_map] at smaller
                exact ihSize _ (by rw [← sizeEq]; exact smaller) _ _ calleeRecorded calleeMember calleeFree
                  hLevel rfl _ calleeAnswer rfl)
            (fun made inside => (closedCalls _ recorded).1 made inside)
        have headInst : instAll next rule.args = some (rule.args.map (subst σ)) :=
          instAll_gives _ ((dataInAll_iff _).mpr ruleOk.data) fun name inside => gives name (List.mem_append_left _ inside)
        have inFrom : (rule.head, rule.args.map (subst σ)) ∈
            program.answersFrom (tableAnswers table) vertex ((boundArgs vertex.2 rule.args).map (subst σ)) := by
          unfold answersFrom
          rw [List.mem_eraseDups]
          refine List.mem_flatMap.mpr ⟨(index, rule), atVertex, ?_⟩
          simp only [started]
          exact List.mem_filterMap.mpr ⟨next, nextMember, by rw [headInst]; rfl⟩
        rcases (closedCalls _ recorded).2 with notFree | answersListed
        · simp [free] at notFree
        · exact answersListed _ inFrom
  exact fun vertex values recorded member free => listed _ _ vertex values recorded member free rfl rfl

omit [FreshNames Variable] in
/-- **A stable table holds the relevant program**: with the evidence, every
relevant call of a closed query is listed, and every relevant rule instance
and every passing denial instance is among those the enumeration gives from
the table. -/
theorem stable_complete (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) (noParameters : query.parameters = [])
    {table : CallTable Variable Literal Symbol} (stableTable : program.stable query table = true) :
    (∀ vertex values, program.Relevant query vertex values → (vertex, values) ∈ table.map (·.1)) ∧
      (∀ atom rule σ, program.Instance query atom rule σ → ∃ index, program.rules[index]? = some rule ∧
        (index, rule.names.map fun name => some (σ name)) ∈ program.instancesOf (tableAnswers table) (table.map (·.1))) ∧
      ∀ index body, program.denials[index]? = some body → ∀ σ : Variable → Term Variable Literal Symbol,
        GroundOn program.constructors σ (bodyNames body) → program.Passes σ [] body →
          (index, (bodyNames body).map fun name => some (σ name)) ∈ program.denialInstancesOf (tableAnswers table) := by
  have covers := stable_answers wellFormed queryOk evidence stableTable
  simp only [stable, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, Bool.or_eq_true, Bool.not_eq_true'] at stableTable
  obtain ⟨roots, closedCalls⟩ := stableTable
  -- Every relevant call is listed.
  have calls : ∀ vertex values, program.Relevant query vertex values → (vertex, values) ∈ table.map (·.1) := by
    intro vertex values relevant
    induction relevant with
    | @goal σ position goal bound vertex queryPasses inCalls =>
        obtain ⟨ground, passes⟩ := queryPasses
        refine roots _ (List.mem_append_left _ (List.mem_append_left _ ?_))
        exact (bodyCallValues_walk (Recorded := (· ∈ table.map (·.1))) (env := fun _ => Option.none)
          (enumerates_of_wellFormed wellFormed)
          (fun other inside calleeFree calleeRecorded answer => covers _ _ calleeRecorded
            (queryVertices_mem (List.mem_append_right _ (List.mem_map.mpr ⟨other, inside, rfl⟩))) calleeFree _ answer rfl)
          (fun made inside => roots made (List.mem_append_left _ (List.mem_append_left _ inside)))
          (List.mem_singleton.mpr rfl) (fun _ _ found => by cases found) (by rw [noParameters]; intro _ member; cases member)
          queryOk.goals ground passes).1 (position, goal, bound, vertex) inCalls
    | @condition goal vertex member found =>
        exact roots _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_filterMap.mpr ⟨goal, member, by simp [found]⟩)))
    | @denial body σ position goal bound vertex denialMember ground passes inCalls =>
        have inDenials : ∀ made ∈ program.bodyCallValues (tableAnswers table) [] [fun _ => Option.none] body,
            made ∈ program.rootCalls (tableAnswers table) query :=
          fun made inside => List.mem_append_right _ (List.mem_flatMap.mpr ⟨body, denialMember, inside⟩)
        refine roots _ (inDenials _ ?_)
        exact (bodyCallValues_walk (Recorded := (· ∈ table.map (·.1))) (env := fun _ => Option.none)
          (enumerates_of_wellFormed wellFormed)
          (fun other inside calleeFree calleeRecorded answer => covers _ _ calleeRecorded
            (denialVertices_mem (List.mem_flatMap.mpr ⟨body, denialMember, List.mem_map.mpr ⟨other, inside, rfl⟩⟩))
            calleeFree _ answer rfl)
          (fun made inside => roots made (inDenials made inside))
          (List.mem_singleton.mpr rfl) (fun _ _ found => by cases found) (fun _ member => by cases member)
          (wellFormed.denials body denialMember) ground passes).1 (position, goal, bound, vertex) inCalls
    | @rule vertex atom index rule σ position goal bound callee callerRelevant _ _ atVertex groundRule headEq passes inCalls ih =>
        have member := (relevant_vertex wellFormed queryOk callerRelevant).1
        have valuesEq : boundArgs vertex.2 atom.2 = (boundArgs vertex.2 rule.args).map (subst σ) := by
          rw [← headEq, boundArgs_map]
        rw [valuesEq] at ih
        have made := (walk_at (Recorded := (· ∈ table.map (·.1))) wellFormed queryOk member atVertex groundRule passes
          (fun other inside calleeFree calleeRecorded answer => covers _ _ calleeRecorded
            (successor_mem member (mem_callsAt atVertex inside)) calleeFree _ answer rfl)
          (fun made inside => (closedCalls _ ih).1 made inside)).1 (position, goal, bound, callee) inCalls
        exact (closedCalls _ ih).1 _ made
  refine ⟨calls, fun atom rule σ ⟨vertex, index, entry, atVertex, groundRule, headEq, passes⟩ => ?_,
    fun index body found σ ground passes => ?_⟩
  · have member := (relevant_vertex wellFormed queryOk entry.1).1
    have valuesEq : boundArgs vertex.2 atom.2 = (boundArgs vertex.2 rule.args).map (subst σ) := by
      rw [← headEq, boundArgs_map]
    have recorded := valuesEq ▸ calls _ _ entry.1
    obtain ⟨_, start, started, next, nextMember, gives⟩ := walk_at (Recorded := (· ∈ table.map (·.1))) wellFormed queryOk member
      atVertex groundRule passes
      (fun other inside calleeFree calleeRecorded answer => covers _ _ calleeRecorded
        (successor_mem member (mem_callsAt atVertex inside)) calleeFree _ answer rfl)
      (fun made inside => (closedCalls _ recorded).1 made inside)
    exact ⟨index, (mem_rulesOf.mp (mem_rulesAt.mp atVertex).1).1, instance_mem atVertex recorded started nextMember gives⟩
  · have denialMember := List.mem_of_getElem? found
    have inDenials : ∀ made ∈ program.bodyCallValues (tableAnswers table) [] [fun _ => Option.none] body,
        made ∈ program.rootCalls (tableAnswers table) query :=
      fun made inside => List.mem_append_right _ (List.mem_flatMap.mpr ⟨body, denialMember, inside⟩)
    obtain ⟨_, next, nextMember, _, nextGives⟩ := bodyCallValues_walk (Recorded := (· ∈ table.map (·.1)))
      (env := fun _ => Option.none) (position := 0) (enumerates_of_wellFormed wellFormed)
      (fun other inside calleeFree calleeRecorded answer => covers _ _ calleeRecorded
        (denialVertices_mem (List.mem_flatMap.mpr ⟨body, denialMember, List.mem_map.mpr ⟨other, inside, rfl⟩⟩))
        calleeFree _ answer rfl)
      (fun made inside => roots made (inDenials made inside))
      (List.mem_singleton.mpr rfl) (fun _ _ found => by cases found) (fun _ member => by cases member)
      (wellFormed.denials body denialMember) ground passes
    exact denialInstance_mem found nextMember nextGives

omit [FreshNames Variable] in
/-- **The computed relevant program holds the relevant program**: when it is
computed, it lists every relevant call, every relevant rule instance, and
every passing denial instance. -/
theorem relevantProgram_complete (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) {fuel : Nat}
    {computed : Computed Variable Literal Symbol} (found : program.relevantProgram query fuel = some computed) :
    (∀ vertex values, program.Relevant query vertex values → (vertex, values) ∈ computed.calls) ∧
      (∀ atom rule σ, program.Instance query atom rule σ → ∃ index, program.rules[index]? = some rule ∧
        (index, rule.names.map fun name => some (σ name)) ∈ computed.instances) ∧
      ∀ index body, program.denials[index]? = some body → ∀ σ : Variable → Term Variable Literal Symbol,
        GroundOn program.constructors σ (bodyNames body) → program.Passes σ [] body →
          (index, (bodyNames body).map fun name => some (σ name)) ∈ computed.denials := by
  unfold relevantProgram at found
  by_cases closed : query.parameters.isEmpty = true
  · simp only [closed, ite_true] at found
    by_cases stableTable : program.stable query (program.saturate query fuel []) = true
    · simp only [stableTable, ite_true, Option.some.injEq] at found
      subst found
      obtain ⟨calls, instances, denials⟩ :=
        stable_complete wellFormed queryOk evidence (List.isEmpty_iff.mp closed) stableTable
      refine ⟨calls, fun atom rule σ instance' => ?_, fun index body found σ ground passes => ?_⟩
      · obtain ⟨index, ruleFound, member⟩ := instances atom rule σ instance'
        exact ⟨index, ruleFound, List.mem_eraseDups.mpr member⟩
      · exact List.mem_eraseDups.mpr (denials index body found σ ground passes)
    · simp [stableTable] at found
  · simp [closed] at found

end Program

end AnthillModKbSpec.IR
