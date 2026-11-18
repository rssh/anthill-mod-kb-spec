import AnthillModKbSpec.Resolution.IR.Parameters

/-! # Enumerating the instances of a body (S27)

A rule body read left to right binds each name from a finite source: the
head's bound arguments, the possible answers of a call that leaves an output
free, the members of a finite guard, one side of an equation, a primitive's
evaluator. `Program.bodyEnvs` computes the partial substitutions of a body's
names that pass each literal, given lists of answers for the calls that leave
an output free. It is complete: when the answer lists hold the possible
answers of the body's free calls, every passing instance extends one of its
results (`bodyEnvs_complete`), so a rule has finitely many passing instances
at an atom. An answer is read only at its own predicate, and a primitive's
value only when it is a ground data term. -/

namespace AnthillModKbSpec.IR

open Semantics Completion Tabled Answers

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  [FreshNames Variable]

attribute [local instance] Machine.termEq

/-! ## Matching ground terms -/

mutual
/-- Match a data term against a ground term, extending a partial
substitution: a bound name must have the value, an unbound one takes it. -/
def matchTerm (env : Env Variable Literal Symbol) : Term Variable Literal Symbol → Term Variable Literal Symbol →
    Option (Env Variable Literal Symbol)
  | .var name, value =>
      match env name with
      | some bound => if bound = value then some env else none
      | none => some (env.set name (some value))
  | .lit literal, .lit other => if literal = other then some env else none
  | .app symbol args, .app other values => if symbol = other then matchAll env args values else none
  | _, _ => none

def matchAll (env : Env Variable Literal Symbol) : List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) →
    Option (Env Variable Literal Symbol)
  | [], [] => some env
  | pattern :: patterns, value :: values => (matchTerm env pattern value).bind fun next => matchAll next patterns values
  | _, _ => none
end

/-- A partial substitution keeps to a total one: every value it has is the
total one's. -/
def Faithful (env : Env Variable Literal Symbol) (σ : Variable → Term Variable Literal Symbol) : Prop :=
  ∀ name value, env name = some value → value = σ name

/-- A partial substitution gives the names their total one's values. -/
def Gives (env : Env Variable Literal Symbol) (σ : Variable → Term Variable Literal Symbol) (names : List Variable) : Prop :=
  ∀ name ∈ names, env name = some (σ name)

omit [FreshNames Variable] in
mutual
/-- A data term whose names a partial substitution gives instantiates to the
total substitution. -/
theorem inst_gives {constructors : List (Constructor Literal Symbol)} {σ : Variable → Term Variable Literal Symbol}
    {env : Env Variable Literal Symbol} :
    ∀ term : Term Variable Literal Symbol, dataIn constructors term = true → Gives env σ term.freeVars →
      inst env term = some (subst σ term)
  | .var name, _, gives => by simp [inst, subst, gives name (by simp [Term.freeVars])]
  | .lit _, _, _ => by simp [inst, subst]
  | .app symbol args, data, gives => by
      simp only [dataIn, Bool.and_eq_true] at data
      simp only [inst, subst]
      rw [instAll_gives args data.2 fun name occurs => gives name (by simpa [Term.freeVars] using occurs), substAll_eq]
      rfl
  | .truth, data, _ | .falsity, data, _ | .conj _ _, data, _ | .disj _ _, data, _ | .imp _ _, data, _
  | .defaultNeg _, data, _ | .forallVar _ _, data, _ | .existsVar _ _, data, _ | .dictionaryCall _ _ _ _, data, _
  | .equal _ _, data, _ => by simp [dataIn] at data

theorem instAll_gives {constructors : List (Constructor Literal Symbol)} {σ : Variable → Term Variable Literal Symbol}
    {env : Env Variable Literal Symbol} :
    ∀ args : List (Term Variable Literal Symbol), dataInAll constructors args = true →
      Gives env σ (args.flatMap Term.freeVars) → instAll env args = some (args.map (subst σ))
  | [], _, _ => rfl
  | arg :: rest, data, gives => by
      simp only [dataInAll, Bool.and_eq_true] at data
      simp only [instAll]
      rw [inst_gives arg data.1 fun name occurs => gives name (by simp [occurs]),
        instAll_gives rest data.2 fun name occurs => gives name (by simp only [List.flatMap_cons, List.mem_append]; exact .inr occurs)]
      rfl
end

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
mutual
/-- A faithful partial substitution instantiates a term only to its total
substitution. -/
theorem inst_faithful {σ : Variable → Term Variable Literal Symbol} {env : Env Variable Literal Symbol} (faithful : Faithful env σ) :
    ∀ {term value : Term Variable Literal Symbol}, inst env term = some value → value = subst σ term
  | .var name, value, found => by simp only [inst] at found; simp [subst, faithful name value found]
  | .lit _, value, found => by simp only [inst, Option.some.injEq] at found; simp [subst, found]
  | .app symbol args, value, found => by
      simp only [inst] at found
      cases instEq : instAll env args with
      | none => rw [instEq] at found; cases found
      | some values =>
          rw [instEq] at found
          simp only [Option.map_some, Option.some.injEq] at found
          subst found
          simp only [subst, substAll_eq, instAll_faithful faithful instEq]
  | .truth, _, found | .falsity, _, found | .conj _ _, _, found | .disj _ _, _, found | .imp _ _, _, found
  | .defaultNeg _, _, found | .forallVar _ _, _, found | .existsVar _ _, _, found | .dictionaryCall _ _ _ _, _, found
  | .equal _ _, _, found => by simp [inst] at found

theorem instAll_faithful {σ : Variable → Term Variable Literal Symbol} {env : Env Variable Literal Symbol} (faithful : Faithful env σ) :
    ∀ {terms values : List (Term Variable Literal Symbol)}, instAll env terms = some values → values = terms.map (subst σ)
  | [], values, found => by simp only [instAll, Option.some.injEq] at found; simp [← found]
  | term :: rest, values, found => by
      simp only [instAll] at found
      cases termEq : inst env term with
      | none => rw [termEq] at found; cases found
      | some value =>
          cases restEq : instAll env rest with
          | none => rw [termEq, restEq] at found; cases found
          | some more =>
              rw [termEq, restEq] at found
              simp only [Option.some.injEq] at found
              subst found
              simp [inst_faithful faithful termEq, instAll_faithful faithful restEq]
end

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem Gives.mono {env env' : Env Variable Literal Symbol} {σ : Variable → Term Variable Literal Symbol} {names : List Variable}
    (gives : Gives env σ names) (more : Extends env env') : Gives env' σ names :=
  fun name member => more name _ (gives name member)

omit [FreshNames Variable] in
mutual
/-- Matching a data term against its total substitution succeeds from a
faithful partial substitution, extends it faithfully, and gives the term's
names. -/
theorem matchTerm_complete {constructors : List (Constructor Literal Symbol)} {σ : Variable → Term Variable Literal Symbol} :
    ∀ {env : Env Variable Literal Symbol} (term : Term Variable Literal Symbol), dataIn constructors term = true → Faithful env σ →
      ∃ next, matchTerm env term (subst σ term) = some next ∧ Faithful next σ ∧ Gives next σ term.freeVars ∧ Extends env next
  | env, .var name, _, faithful => by
      cases found : env name with
      | some bound =>
          have same := faithful name bound found
          subst same
          exact ⟨env, by simp [matchTerm, subst, found], faithful,
            fun other member => by simp only [Term.freeVars, List.mem_singleton] at member; subst member; exact found,
            Extends.refl _⟩
      | none =>
          refine ⟨env.set name (some (σ name)), by simp [matchTerm, subst, found], ?_, ?_, ?_⟩
          · intro other value setFound
            by_cases same : other = name
            · subst same; simp at setFound; exact setFound.symm
            · rw [Env.set_other _ _ same] at setFound; exact faithful other value setFound
          · intro other member
            simp only [Term.freeVars, List.mem_singleton] at member; subst member; simp
          · intro other value bound
            have different : other ≠ name := fun same => by rw [same, found] at bound; cases bound
            rw [Env.set_other _ _ different]; exact bound
  | env, .lit _, _, faithful => ⟨env, by simp [matchTerm, subst], faithful, by simp [Gives, Term.freeVars], Extends.refl _⟩
  | env, .app symbol args, data, faithful => by
      simp only [dataIn, Bool.and_eq_true] at data
      obtain ⟨next, matched, nextFaithful, gives, more⟩ := matchAll_complete args data.2 faithful
      refine ⟨next, ?_, nextFaithful, fun name member => gives name (by simpa [Term.freeVars] using member), more⟩
      simp only [subst, matchTerm, ite_true, substAll_eq]
      exact matched
  | _, .truth, data, _ | _, .falsity, data, _ | _, .conj _ _, data, _ | _, .disj _ _, data, _ | _, .imp _ _, data, _
  | _, .defaultNeg _, data, _ | _, .forallVar _ _, data, _ | _, .existsVar _ _, data, _
  | _, .dictionaryCall _ _ _ _, data, _ | _, .equal _ _, data, _ => by simp [dataIn] at data

theorem matchAll_complete {constructors : List (Constructor Literal Symbol)} {σ : Variable → Term Variable Literal Symbol} :
    ∀ {env : Env Variable Literal Symbol} (args : List (Term Variable Literal Symbol)), dataInAll constructors args = true →
      Faithful env σ → ∃ next, matchAll env args (args.map (subst σ)) = some next ∧ Faithful next σ ∧
        Gives next σ (args.flatMap Term.freeVars) ∧ Extends env next
  | env, [], _, faithful => ⟨env, rfl, faithful, by simp [Gives], Extends.refl _⟩
  | env, arg :: rest, data, faithful => by
      simp only [dataInAll, Bool.and_eq_true] at data
      obtain ⟨middle, matched, middleFaithful, middleGives, middleMore⟩ := matchTerm_complete arg data.1 faithful
      obtain ⟨next, restMatched, nextFaithful, nextGives, nextMore⟩ := matchAll_complete rest data.2 middleFaithful
      refine ⟨next, by simp [matchAll, matched, restMatched], nextFaithful, ?_, middleMore.trans nextMore⟩
      intro name member
      simp only [List.flatMap_cons, List.mem_append] at member
      rcases member with here | there
      · exact (middleGives.mono nextMore) name here
      · exact nextGives name there
end

/-! ## The partial substitutions of a body -/

namespace Program

variable (program : Program Variable Literal Symbol)

/-- The extensions of a partial substitution that pass one literal, with these
names bound before it and these answers for the calls that leave an output
free. -/
def stepEnvs (answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol))
    (bound : List Variable) (env : Env Variable Literal Symbol) : Goal Variable Literal Symbol → List (Env Variable Literal Symbol)
  | .call predicate args =>
      let pattern := patternOf bound args
      if pattern.free then
        match instAll env (boundArgs pattern args) with
        | some values => (answers (predicate, pattern) values).filterMap fun atom =>
            if atom.1 = predicate then matchAll env args atom.2 else none
        | none => []
      else [env]
  | .naf _ _ | .marker _ _ => [env]
  | .equal left right =>
      match inst env left, inst env right with
      | some first, some second => if first = second then [env] else []
      | some first, none => (matchTerm env right first).toList
      | none, some second => (matchTerm env left second).toList
      | none, none => []
  | .differ left right =>
      match inst env left, inst env right with
      | some first, some second => if first = second then [] else [env]
      | _, _ => []
  | .guard symbol arg =>
      match inst env arg with
      | some value => if program.guardHolds symbol value then [env] else []
      | none =>
          match program.members symbol with
          | some members => members.filterMap fun member => matchTerm env arg member
          | none => []
  | .primitive symbol inputs output =>
      match instAll env inputs with
      | some values =>
          match program.evaluate symbol values with
          | some value => if groundIn program.constructors value then (matchTerm env output value).toList else []
          | none => []
      | none => []

/-- The partial substitutions passing a body, literal by literal. -/
def bodyEnvs (answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)) :
    List Variable → List (Env Variable Literal Symbol) → List (Goal Variable Literal Symbol) → List (Env Variable Literal Symbol)
  | _, envs, [] => envs
  | bound, envs, goal :: rest =>
      bodyEnvs answers (after bound goal) (envs.flatMap fun env => program.stepEnvs answers bound env goal) rest

variable {program}

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem available_mono {bound bound' names : List Variable} (avail : available bound names = true)
    (sub : ∀ name ∈ bound, name ∈ bound') : available bound' names = true :=
  available_iff.mpr fun name member => sub name (available_iff.mp avail name member)

omit [DecidableEq Literal] [FreshNames Variable] in
theorem needs_mono {bound bound' : List Variable} {goal : Goal Variable Literal Symbol} (needed : program.needs bound goal = true)
    (sub : ∀ name ∈ bound, name ∈ bound') : program.needs bound' goal = true := by
  cases goal with
  | call _ _ | naf _ _ | marker _ _ | differ _ _ | primitive _ _ _ => exact available_mono needed sub
  | equal left right =>
      simp only [Program.needs, Bool.or_eq_true] at needed ⊢
      exact needed.elim (fun left => .inl (available_mono left sub)) (fun right => .inr (available_mono right sub))
  | guard symbol arg =>
      simp only [Program.needs, Bool.or_eq_true] at needed ⊢
      exact needed.elim (fun left => .inl (available_mono left sub)) .inr

omit [FreshNames Variable] in
theorem Scans.mono : ∀ {bound bound' : List Variable} {body : List (Goal Variable Literal Symbol)},
    Scans program bound body → (∀ name ∈ bound, name ∈ bound') → Scans program bound' body
  | _, _, [], _, _ => .nil
  | bound, bound', goal :: rest, .cons declared data needed restScans, sub => by
      refine .cons declared data (needs_mono needed sub) (Scans.mono restScans fun name member => ?_)
      simp only [after, List.mem_append] at member ⊢
      rcases member with inside | own
      · exact .inl (sub name inside)
      · exact .inr own

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem available_patternOf {bound : List Variable} {args : List (Term Variable Literal Symbol)}
    (closed : (patternOf bound args).free = false) : ∀ name ∈ namesOf args, name ∈ bound := by
  intro name member
  obtain ⟨arg, argMember, occurs⟩ := List.mem_flatMap.mp member
  simp only [Pattern.free, patternOf, List.any_map, List.any_eq_false, Function.comp, beq_iff_eq] at closed
  have := closed arg argMember
  simp only [Bool.not_eq_false] at this
  exact available_iff.mp this name occurs

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem boundArgs_names {bound : List Variable} :
    ∀ {args : List (Term Variable Literal Symbol)}, ∀ name ∈ namesOf (boundArgs (patternOf bound args) args), name ∈ bound
  | [], name, member => by simp [boundArgs, namesOf] at member
  | arg :: rest, name, member => by
      simp only [patternOf, List.map_cons, boundArgs, List.zip_cons_cons, List.filterMap_cons] at member
      by_cases avail : available bound arg.freeVars = true
      · simp only [avail, ite_true, namesOf, List.flatMap_cons, List.mem_append] at member
        rcases member with here | there
        · exact available_iff.mp avail name here
        · exact boundArgs_names (args := rest) name (by simpa [patternOf, boundArgs, namesOf] using there)
      · simp only [avail, Bool.false_eq_true, ite_false] at member
        exact boundArgs_names (args := rest) name (by simpa [patternOf, boundArgs, namesOf] using member)

omit [FreshNames Variable] in
/-- **One literal.** A passing instance's literal has an extension among the
literal's partial substitutions that keeps to the instance and gives its
names. -/
theorem stepEnvs_complete {answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)}
    (enumerates : program.Enumerates) {σ : Variable → Term Variable Literal Symbol}
    {bound : List Variable} {env : Env Variable Literal Symbol} (faithful : Faithful env σ) (gives : Gives env σ bound)
    {goal : Goal Variable Literal Symbol}
    (covered : ∀ vertex, goal.vertex? bound = some vertex → vertex.2.free = true →
      program.Ans vertex (vertex.1, goal.args.map (subst σ)) →
        (vertex.1, goal.args.map (subst σ)) ∈ answers vertex (boundArgs vertex.2 (goal.args.map (subst σ))))
    (data : program.data goal = true) (needed : program.needs bound goal = true)
    (ground : GroundOn program.constructors σ goal.names) (declared : program.declares goal = true)
    (passes : (∃ vertex, goal.vertex? bound = some vertex ∧ vertex.2.free = true ∧
        program.Ans vertex (vertex.1, goal.args.map (subst σ))) ∨
      ((∀ vertex, goal.vertex? bound = some vertex → vertex.2.free = false) ∧ program.fixedAt σ goal)) :
    ∃ next ∈ program.stepEnvs answers bound env goal, Faithful next σ ∧ Gives next σ (after bound goal) := by
  have allData : ∀ arg ∈ goal.args, dataIn program.constructors arg = true := List.all_eq_true.mp data
  have givesAfter : ∀ {next : Env Variable Literal Symbol}, Extends env next → Gives next σ goal.names →
      Gives next σ (after bound goal) := fun more own name member => by
    rcases List.mem_append.mp member with inside | inside
    · exact (gives.mono more) name inside
    · exact own name inside
  have givesBound : (∀ name ∈ goal.names, name ∈ bound) → Gives env σ (after bound goal) :=
    fun inside => givesAfter (Extends.refl _) fun name member => gives name (inside name member)
  cases goal with
  | call predicate args =>
      have argsData : ∀ arg ∈ args, dataIn program.constructors arg = true := fun arg member => allData arg member
      cases freePattern : (patternOf bound args).free with
      | false =>
          refine ⟨env, by simp [stepEnvs, freePattern], faithful, givesBound (available_patternOf freePattern)⟩
      | true =>
          rcases passes with ⟨vertex, vertexEq, _, answer⟩ | ⟨fixed, _⟩
          · simp only [Goal.vertex?, Option.some.injEq] at vertexEq
            subst vertexEq
            have boundData : ∀ arg ∈ boundArgs (patternOf bound args) args, dataIn program.constructors arg = true :=
              fun arg member => argsData _ (mem_of_mem_boundArgs member)
            have values := instAll_gives (σ := σ) (env := env) _ ((dataInAll_iff _).mpr boundData)
              fun name member => gives name (boundArgs_names name member)
            have listed := covered _ rfl (by assumption) answer
            simp only at listed
            rw [boundArgs_map] at listed
            obtain ⟨next, matched, nextFaithful, nextGives, more⟩ := matchAll_complete (σ := σ) (env := env) args
              ((dataInAll_iff _).mpr argsData) faithful
            refine ⟨next, ?_, nextFaithful, givesAfter more nextGives⟩
            simp only [stepEnvs, freePattern, ite_true, values]
            exact List.mem_filterMap.mpr ⟨_, listed, by simpa [Goal.args] using matched⟩
          · exact absurd (fixed _ rfl) (by simp [freePattern])
  | naf predicate args =>
      exact ⟨env, by simp [stepEnvs], faithful, givesBound fun name member => available_iff.mp needed name member⟩
  | marker symbol args =>
      exact ⟨env, by simp [stepEnvs], faithful, givesBound fun name member => available_iff.mp needed name member⟩
  | equal left right =>
      rcases passes with ⟨_, vertexEq, _⟩ | ⟨_, same⟩
      · cases vertexEq
      have leftData := allData left (by simp [Goal.args])
      have rightData := allData right (by simp [Goal.args])
      simp only [fixedAt] at same
      cases leftInst : inst env left with
      | some first =>
          have firstEq := inst_faithful faithful leftInst
          cases rightInst : inst env right with
          | some second =>
              have secondEq := inst_faithful faithful rightInst
              refine ⟨env, by simp [stepEnvs, leftInst, rightInst, firstEq, secondEq, same], faithful, givesAfter (Extends.refl _) ?_⟩
              intro name member
              simp only [Goal.names, Goal.args, namesOf, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at member
              rcases member with inLeft | inRight
              · obtain ⟨part, partFound, _⟩ := inst_name leftInst name inLeft
                rw [partFound, faithful name part partFound]
              · obtain ⟨part, partFound, _⟩ := inst_name rightInst name inRight
                rw [partFound, faithful name part partFound]
          | none =>
              obtain ⟨next, matched, nextFaithful, nextGives, more⟩ := matchTerm_complete (σ := σ) (env := env) right rightData faithful
              refine ⟨next, by simp [stepEnvs, leftInst, rightInst, firstEq, same, matched], nextFaithful, givesAfter more ?_⟩
              intro name member
              simp only [Goal.names, Goal.args, namesOf, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at member
              rcases member with inLeft | inRight
              · obtain ⟨part, partFound, _⟩ := inst_name leftInst name inLeft
                rw [more name part partFound, faithful name part partFound]
              · exact nextGives name inRight
      | none =>
          cases rightInst : inst env right with
          | some second =>
              have secondEq := inst_faithful faithful rightInst
              obtain ⟨next, matched, nextFaithful, nextGives, more⟩ := matchTerm_complete (σ := σ) (env := env) left leftData faithful
              refine ⟨next, by simp [stepEnvs, leftInst, rightInst, secondEq, ← same, matched], nextFaithful, givesAfter more ?_⟩
              intro name member
              simp only [Goal.names, Goal.args, namesOf, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at member
              rcases member with inLeft | inRight
              · exact nextGives name inLeft
              · obtain ⟨part, partFound, _⟩ := inst_name rightInst name inRight
                rw [more name part partFound, faithful name part partFound]
          | none =>
              simp only [Program.needs, Bool.or_eq_true] at needed
              rcases needed with leftAvail | rightAvail
              · have := inst_gives (σ := σ) (env := env) left leftData fun name member => gives name (available_iff.mp leftAvail name member)
                rw [leftInst] at this; cases this
              · have := inst_gives (σ := σ) (env := env) right rightData fun name member => gives name (available_iff.mp rightAvail name member)
                rw [rightInst] at this; cases this
  | differ left right =>
      rcases passes with ⟨_, vertexEq, _⟩ | ⟨_, different⟩
      · cases vertexEq
      have leftData := allData left (by simp [Goal.args])
      have rightData := allData right (by simp [Goal.args])
      simp only [fixedAt] at different
      have both := available_iff.mp needed
      have leftInst := inst_gives (σ := σ) (env := env) left leftData fun name member => gives name (both name (List.mem_append_left _ member))
      have rightInst := inst_gives (σ := σ) (env := env) right rightData fun name member => gives name (both name (List.mem_append_right _ member))
      refine ⟨env, by simp [stepEnvs, leftInst, rightInst, different], faithful, givesBound fun name member => both name ?_⟩
      simpa [Goal.names, Goal.args, namesOf] using member
  | guard symbol arg =>
      rcases passes with ⟨_, vertexEq, _⟩ | ⟨_, holds⟩
      · cases vertexEq
      have argData := allData arg (by simp [Goal.args])
      simp only [fixedAt] at holds
      cases argInst : inst env arg with
      | some value =>
          have valueEq := inst_faithful faithful argInst
          refine ⟨env, by simp [stepEnvs, argInst, valueEq, holds], faithful, givesAfter (Extends.refl _) fun name member => ?_⟩
          obtain ⟨part, partFound, _⟩ := inst_name argInst name (by simpa [Goal.names, Goal.args, namesOf] using member)
          rw [partFound, faithful name part partFound]
      | none =>
          simp only [Program.needs, Bool.or_eq_true] at needed
          rcases needed with avail | finite
          · have := inst_gives (σ := σ) (env := env) arg argData fun name member => gives name (available_iff.mp avail name member)
            rw [argInst] at this; cases this
          · obtain ⟨members, membersEq⟩ := Option.isSome_iff_exists.mp finite
            have argGround := groundIn_subst arg argData fun name occurs =>
              ground name (by simpa [Goal.names, Goal.args, namesOf] using occurs)
            have member := ((enumerates symbol members declared membersEq).2 _).mp holds
            obtain ⟨next, matched, nextFaithful, nextGives, more⟩ := matchTerm_complete (σ := σ) (env := env) arg argData faithful
            refine ⟨next, ?_, nextFaithful, givesAfter more fun name inside => nextGives name (by
              simpa [Goal.names, Goal.args, namesOf] using inside)⟩
            simp only [stepEnvs, argInst, membersEq]
            exact List.mem_filterMap.mpr ⟨_, member, matched⟩
  | primitive symbol inputs output =>
      rcases passes with ⟨_, vertexEq, _⟩ | ⟨_, evaluated⟩
      · cases vertexEq
      have inputsData : ∀ arg ∈ inputs, dataIn program.constructors arg = true :=
        fun arg member => allData arg (List.mem_append_left _ member)
      have outputData := allData output (by simp [Goal.args])
      simp only [fixedAt] at evaluated
      have inputsInst := instAll_gives (σ := σ) (env := env) inputs ((dataInAll_iff _).mpr inputsData)
        fun name member => gives name (available_iff.mp needed name member)
      obtain ⟨next, matched, nextFaithful, nextGives, more⟩ := matchTerm_complete (σ := σ) (env := env) output outputData faithful
      have outputGround := groundIn_subst output outputData fun name occurs =>
        ground name (by simp [Goal.names, Goal.args, namesOf, occurs])
      refine ⟨next, by simp [stepEnvs, inputsInst, evaluated, outputGround, matched], nextFaithful, givesAfter more fun name member => ?_⟩
      simp only [Goal.names, Goal.args, namesOf, List.flatMap_append, List.mem_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil] at member
      rcases member with inInputs | inOutput
      · exact (gives.mono more) name (available_iff.mp needed name inInputs)
      · exact nextGives name inOutput

omit [FreshNames Variable] in
/-- **The body's partial substitutions are complete.** When the answer lists
cover the possible answers and the finite guards list their members exactly,
every passing instance of a body that scans extends a partial substitution
the enumeration computes, which keeps to it and gives every name bound at the
body's end. -/
theorem bodyEnvs_complete {answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)}
    (enumerates : program.Enumerates) {σ : Variable → Term Variable Literal Symbol} :
    ∀ {position : Nat} {bound : List Variable} {body : List (Goal Variable Literal Symbol)} {envs : List (Env Variable Literal Symbol)}
      {env : Env Variable Literal Symbol},
      (∀ call ∈ bodyCalls position bound body, call.2.2.2.2.free = true →
        program.Ans call.2.2.2 (call.2.2.2.1, call.2.1.args.map (subst σ)) →
          (call.2.2.2.1, call.2.1.args.map (subst σ)) ∈ answers call.2.2.2 (boundArgs call.2.2.2.2 (call.2.1.args.map (subst σ)))) →
      env ∈ envs → Faithful env σ → Gives env σ bound → Scans program bound body →
        GroundOn program.constructors σ (bodyNames body) → program.Passes σ bound body →
          ∃ next ∈ program.bodyEnvs answers bound envs body, Faithful next σ ∧ Gives next σ (boundAfter bound body)
  | _, bound, [], envs, env, _, member, faithful, gives, _, _, _ => ⟨env, member, faithful, gives⟩
  | position, bound, goal :: rest, envs, env, covered, member, faithful, gives, .cons declared data needed restScans, ground,
      passes => by
      have goalGround : GroundOn program.constructors σ goal.names := fun name occurs =>
        ground name (List.mem_flatMap.mpr ⟨goal, List.mem_cons_self, occurs⟩)
      have restGround : GroundOn program.constructors σ (bodyNames rest) := fun name occurs =>
        ground name (by simp only [bodyNames, List.flatMap_cons, List.mem_append]; exact .inr occurs)
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
        fun vertex found free answer => covered _ (mem_bodyCalls_head (rest := rest) (position := position) found) free answer
      obtain ⟨step, stepMember, stepFaithful, stepGives⟩ :=
        stepEnvs_complete enumerates faithful gives coveredHere data needed goalGround declared split.1
      exact bodyEnvs_complete (position := position + 1) (bound := after bound goal) (body := rest)
        (envs := envs.flatMap fun env => program.stepEnvs answers bound env goal) (env := step) enumerates
        (fun call inside => covered call (mem_bodyCalls_tail inside))
        (List.mem_flatMap.mpr ⟨env, member, stepMember⟩) stepFaithful stepGives restScans restGround split.2

end Program

end AnthillModKbSpec.IR
