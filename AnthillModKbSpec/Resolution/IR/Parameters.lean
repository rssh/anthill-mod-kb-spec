import AnthillModKbSpec.Resolution.IR.Relevance

/-! # P1, and queries with rigid parameters (S27)

**What P1 gives.** A closed query the checker classifies P0 or P1
(`Program.classifyClosed`) has a well-formed program whose rules and denials
are guarded, is well formed itself, and has the finiteness evidence
(`p1_parts`): the hypotheses of the Herbrand reduction and of relevance.

**Rigid parameters** (decided with the user, 2026-11-18). A query's rigid
parameters range over the carrier, unless its conditions restrict them. A
parameter is P1 when a condition guards it by a finite guard, which holds
exactly of its listed members (`Program.guardHolds`); every other parameter
is P2 (`Program.unsplit`). The split gives one ground query per assignment of
members (`Program.splitValues`, `Query.instantiate`), and the query is P1
when every instance is P0 or P1, each classified as a closed query
(`Program.classify_split`). Its meaning is theirs (`meaning_split`): Yes
exactly when every instance's truth holds, No exactly when every instance's
falsity holds, and Unknown exactly when one instance is not No and another is
not Yes. An instance whose conditions no model satisfies is both Yes and No,
so the combination reads each instance's meaning, not one answer per
instance: "Unknown when neither all are Yes nor all are No" holds only when no
instance is vacuous (S26 settles vacuous contexts). A checked program lists
its finite guards' members as ground data terms (`enumerates_of_wellFormed`). -/

namespace AnthillModKbSpec.IR

open Semantics Completion Tabled Answers

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  [FreshNames Variable]

namespace Program

variable {program : Program Variable Literal Symbol}

/-! ## What P1 gives -/

omit [DecidableEq Literal] [FreshNames Variable] in
theorem guarded_of_unguarded {query : Query Variable Literal Symbol} (clean : program.unguarded query = []) :
    program.Guarded ∧ ∀ name ∈ query.answers, program.guarded query.goals name = true := by
  unfold unguarded at clean
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff] at clean
  obtain ⟨⟨rulesClean, denialsClean⟩, answersClean⟩ := clean
  refine ⟨⟨fun rule member name inside => ?_, fun body member name inside => ?_⟩, fun name inside => ?_⟩
  · obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    have := rulesClean (rule, index) (List.mem_zipIdx_iff_getElem?.mpr found) name (List.mem_eraseDups.mpr inside)
    simpa using this
  · obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    have := denialsClean (body, index) (List.mem_zipIdx_iff_getElem?.mpr found) name (List.mem_eraseDups.mpr inside)
    simpa using this
  · have := answersClean name (List.mem_eraseDups.mpr inside)
    simpa using this

omit [FreshNames Variable] in
/-- **What P1 or P0 gives a closed query**: a well-formed program whose rules
and denials are guarded, a well-formed query, the finiteness evidence, and
guarded answer names. P0 has every note P1 has, and none. -/
theorem p1_parts {query : Query Variable Literal Symbol} (decided : (program.classifyClosed query).decides = true) :
    program.WellFormed ∧ program.Guarded ∧ QueryOk program query ∧ program.notes query = [] ∧
      (∀ name ∈ query.answers, program.guarded query.goals name = true) ∧ query.parameters = [] := by
  obtain ⟨clean, none, evidence⟩ := program.classifyClosed_decides decided
  have unguardedClean := (evidence_of_notes evidence).guarded
  obtain ⟨guarded, answers⟩ := guarded_of_unguarded unguardedClean
  exact ⟨program.wellFormed_of_check clean, guarded, program.queryOk_of_check clean, evidence, answers, none⟩

omit [FreshNames Variable] in
/-- A P1 query without rigid parameters is closed, the Herbrand reduction's
hypothesis on the query. -/
theorem closed_of_parts {query : Query Variable Literal Symbol} (queryOk : QueryOk program query)
    (answers : ∀ name ∈ query.answers, program.guarded query.goals name = true) (none : query.parameters = []) :
    Closed program query where
  parameters := none
  conditions := fun goal member => ⟨(queryOk.conditions goal member).1, (queryOk.conditions goal member).2.1⟩
  goals := Scans.goals queryOk.goals
  apart := queryOk.apart
  answers := answers

/-! ## Instances of a query -/

end Program

namespace Program

variable (program : Program Variable Literal Symbol)

/-- A finite guard lists ground data terms, and holds exactly of them
(`guardHolds`): what the split and the enumeration read of the finite
guards. A checked program has it (`enumerates_of_wellFormed`). -/
def Enumerates : Prop :=
  ∀ symbol members, program.kindAt .guard symbol 1 = true → program.members symbol = some members →
    (∀ term ∈ members, groundIn program.constructors term = true) ∧
      ∀ term, program.guardHolds symbol term = true ↔ term ∈ members

/-- The instances of a query's split: each rigid parameter a member of a
finite guard among the conditions that guards it. -/
def Splits (query : Query Variable Literal Symbol) (values : Variable → Term Variable Literal Symbol) : Prop :=
  ∀ name ∈ query.parameters, ∃ symbol members, Goal.guard symbol (.var name) ∈ query.conditions ∧
    program.kindAt .guard symbol 1 = true ∧ program.members symbol = some members ∧ values name ∈ members

variable {program} in
attribute [local instance] Machine.termEq in
omit [FreshNames Variable] in
theorem enumerates_of_wellFormed (wellFormed : program.WellFormed) : program.Enumerates := by
  intro symbol members kind found
  obtain ⟨declared, declaredEq, declaredKind, _⟩ := kindAt_declared kind
  obtain ⟨member, symbolEq⟩ := predicate?_mem declaredEq
  refine ⟨wellFormed.members declared member declaredKind members (by rw [symbolEq]; exact found), fun term => ?_⟩
  simp [guardHolds, found]

end Program

/-! ## Evaluation under a substitution -/

section Evaluation

variable {Value : Type} {hoApplySymbol : Symbol} (model : Model Literal Symbol Value hoApplySymbol)

omit [FreshNames Variable] in
mutual
/-- A data term's substitution evaluates as the term where each name has its
replacement's value. -/
theorem eval_subst_env {constructors : List (Constructor Literal Symbol)} (environment : Environment Variable Value)
    (σ : Variable → Term Variable Literal Symbol) :
    ∀ term : Term Variable Literal Symbol, dataIn constructors term = true →
      model.eval environment (subst σ term) = model.eval (fun name => model.eval environment (σ name)) term
  | .var _, _ => by simp [subst, Model.eval]
  | .lit _, _ => by simp [subst, Model.eval]
  | .app symbol args, data => by
      simp only [dataIn, Bool.and_eq_true] at data
      simp only [subst, Model.eval]
      rw [substAll_eq]
      exact congrArg (model.application symbol) (evalAll_subst_env environment σ args data.2)
  | .truth, data | .falsity, data | .conj _ _, data | .disj _ _, data | .imp _ _, data | .defaultNeg _, data
  | .forallVar _ _, data | .existsVar _ _, data | .dictionaryCall _ _ _ _, data | .equal _ _, data => by
      simp [dataIn] at data

theorem evalAll_subst_env {constructors : List (Constructor Literal Symbol)} (environment : Environment Variable Value)
    (σ : Variable → Term Variable Literal Symbol) :
    ∀ args : List (Term Variable Literal Symbol), dataInAll constructors args = true →
      (args.map (subst σ)).map (model.eval environment) = args.map (model.eval fun name => model.eval environment (σ name))
  | [], _ => rfl
  | arg :: rest, data => by
      simp only [dataInAll, Bool.and_eq_true] at data
      simp only [List.map_cons, eval_subst_env environment σ arg data.1, evalAll_subst_env environment σ rest data.2]
end

omit [FreshNames Variable] in
/-- A literal's substitution holds as the literal where each name has its
replacement's value. -/
theorem satisfies_goal_subst {constructors : List (Constructor Literal Symbol)} {goal : Goal Variable Literal Symbol}
    (data : ∀ arg ∈ goal.args, dataIn constructors arg = true) (σ : Variable → Term Variable Literal Symbol)
    (environment : Environment Variable Value) :
    model.Satisfies environment (goal.subst σ).toTerm ↔
      model.Satisfies (fun name => model.eval environment (σ name)) goal.toTerm := by
  have list : ∀ (args : List (Term Variable Literal Symbol)), (∀ arg ∈ args, dataIn constructors arg = true) →
      (args.map (subst σ)).map (model.eval environment) = args.map (model.eval fun name => model.eval environment (σ name)) :=
    fun args argsData => evalAll_subst_env model environment σ args ((dataInAll_iff constructors).mpr argsData)
  cases goal with
  | call predicate args =>
      simp only [Goal.subst, Goal.toTerm, Model.Satisfies, Model.eval]
      rw [list args fun arg member => data arg member]
  | naf predicate args =>
      simp only [Goal.subst, Goal.toTerm, Model.Satisfies, Model.eval]
      rw [list args fun arg member => data arg member]
  | marker symbol args =>
      simp only [Goal.subst, Goal.toTerm, Model.Satisfies, Model.eval]
      rw [list args fun arg member => data arg member]
  | equal left right =>
      simp only [Goal.subst, Goal.toTerm, Model.Satisfies, Model.eval]
      rw [eval_subst_env model environment σ left (data left (by simp [Goal.args])),
        eval_subst_env model environment σ right (data right (by simp [Goal.args]))]
  | differ left right =>
      simp only [Goal.subst, Goal.toTerm, Model.Satisfies, Model.eval]
      rw [eval_subst_env model environment σ left (data left (by simp [Goal.args])),
        eval_subst_env model environment σ right (data right (by simp [Goal.args]))]
  | guard symbol arg =>
      simp only [Goal.subst, Goal.toTerm, Model.Satisfies, Model.eval, List.map_cons, List.map_nil]
      rw [eval_subst_env model environment σ arg (data arg (by simp [Goal.args]))]
  | primitive symbol inputs output =>
      simp only [Goal.subst, Goal.toTerm, Model.Satisfies, Model.eval]
      have joined : (inputs.map (subst σ) ++ [subst σ output]) = (inputs ++ [output]).map (subst σ) := by simp
      rw [joined, list (inputs ++ [output]) fun arg member => data arg member]

omit [FreshNames Variable] in
/-- The values a substitution gives, where it keeps some names and replaces
the others by ground terms. -/
theorem values_update {constructors : List (Constructor Literal Symbol)} {σ : Variable → Term Variable Literal Symbol}
    (shape : ∀ name, σ name = .var name ∨ groundIn constructors (σ name) = true) (environment : Environment Variable Value)
    {binder : Variable} (kept : σ binder = .var binder) (value : Value) :
    (fun name => model.eval (update environment binder value) (σ name)) =
      update (fun name => model.eval environment (σ name)) binder value := by
  funext name
  by_cases same : name = binder
  · subst same; rw [kept]; simp [update, Model.eval]
  · rcases shape name with keptName | ground
    · simp only [update, same, ite_false, keptName, Model.eval]
    · simp only [update, same, ite_false]
      rw [eval_ground _ _ ground, eval_ground _ _ ground]

end Evaluation

namespace Program

variable {program : Program Variable Literal Symbol}

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem instantiate_eq (query : Query Variable Literal Symbol) (values : Variable → Term Variable Literal Symbol) :
    query.instantiate values =
      ⟨query.conditions.map (Goal.subst (query.instanceSubst values)), query.goals.map (Goal.subst (query.instanceSubst values)),
        query.answers⟩ := rfl

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem answer_not_parameter {query : Query Variable Literal Symbol} {name : Variable} (answer : name ∈ query.answers) :
    name ∉ query.parameters := by
  intro parameter
  unfold Query.parameters at parameter
  simp [answer] at parameter

variable {Value : Type} {model : Model Literal Symbol Value program.hoApply}

omit [FreshNames Variable] in
/-- A query and its instance at the same model: the instance at an
environment means the query at the environment its substitution gives. -/
theorem instance_iff {query : Query Variable Literal Symbol} (queryOk : QueryOk program query)
    {values : Variable → Term Variable Literal Symbol} (splits : program.Splits query values) (enumerates : program.Enumerates)
    (environment : Environment Variable Value) :
    (model.ContextHolds environment (query.instantiate values).context ↔
        model.ContextHolds (fun name => model.eval environment (query.instanceSubst values name)) query.context) ∧
      (model.Satisfies environment (query.instantiate values).formula ↔
        model.Satisfies (fun name => model.eval environment (query.instanceSubst values name)) query.formula) := by
  have shape : ∀ name, query.instanceSubst values name = .var name ∨
      groundIn program.constructors (query.instanceSubst values name) = true := by
    intro name
    by_cases parameter : name ∈ query.parameters
    · refine .inr ?_
      simp only [Query.instanceSubst, parameter, ite_true]
      obtain ⟨symbol, members, _, kind, found, member⟩ := splits name parameter
      exact (enumerates symbol members kind found).1 _ member
    · exact .inl (by simp [Query.instanceSubst, parameter])
  have conditionsData : ∀ goal ∈ query.conditions, ∀ arg ∈ goal.args, dataIn program.constructors arg = true :=
    fun goal member => List.all_eq_true.mp (queryOk.conditions goal member).2.1
  have goalsData : ∀ goal ∈ query.goals, ∀ arg ∈ goal.args, dataIn program.constructors arg = true :=
    fun goal member => List.all_eq_true.mp (Scans.goals queryOk.goals goal member).2
  constructor
  · simp only [instantiate_eq, Query.context]
    constructor
    · intro holds term member
      obtain ⟨goal, goalMember, rfl⟩ := List.mem_map.mp member
      exact (satisfies_goal_subst model (conditionsData goal goalMember) _ environment).mp
        (holds _ (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨goal, goalMember, rfl⟩, rfl⟩))
    · intro holds term member
      obtain ⟨substituted, inside, rfl⟩ := List.mem_map.mp member
      obtain ⟨goal, goalMember, rfl⟩ := List.mem_map.mp inside
      exact (satisfies_goal_subst model (conditionsData goal goalMember) _ environment).mpr
        (holds _ (List.mem_map.mpr ⟨goal, goalMember, rfl⟩))
  · simp only [instantiate_eq, Query.formula]
    have bodyIff : ∀ env : Environment Variable Value,
        model.Satisfies env (bodyTerm (query.goals.map (Goal.subst (query.instanceSubst values)))) ↔
          model.Satisfies (fun name => model.eval env (query.instanceSubst values name)) (bodyTerm query.goals) := by
      intro env
      unfold bodyTerm
      rw [Model.satisfies_conjunction, Model.satisfies_conjunction]
      constructor
      · intro holds term member
        obtain ⟨goal, goalMember, rfl⟩ := List.mem_map.mp member
        exact (satisfies_goal_subst model (goalsData goal goalMember) _ env).mp
          (holds _ (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨goal, goalMember, rfl⟩, rfl⟩))
      · intro holds term member
        obtain ⟨substituted, inside, rfl⟩ := List.mem_map.mp member
        obtain ⟨goal, goalMember, rfl⟩ := List.mem_map.mp inside
        exact (satisfies_goal_subst model (goalsData goal goalMember) _ env).mpr
          (holds _ (List.mem_map.mpr ⟨goal, goalMember, rfl⟩))
    have answersKept : ∀ name ∈ query.answers, query.instanceSubst values name = .var name := fun name answer => by
      simp [Query.instanceSubst, answer_not_parameter answer]
    suffices walk : ∀ (binders : List Variable), (∀ name ∈ binders, name ∈ query.answers) → ∀ env : Environment Variable Value,
        (model.Satisfies env (binders.foldr Term.existsVar (bodyTerm (query.goals.map (Goal.subst (query.instanceSubst values))))) ↔
          model.Satisfies (fun name => model.eval env (query.instanceSubst values name))
            (binders.foldr Term.existsVar (bodyTerm query.goals))) from
      walk query.answers (fun _ inside => inside) environment
    intro binders
    induction binders with
    | nil => intro _ env; exact bodyIff env
    | cons binder rest ih =>
        intro inside env
        simp only [List.foldr_cons]
        rw [sat_exists, sat_exists]
        constructor
        · rintro ⟨value, holds⟩
          refine ⟨value, ?_⟩
          rw [← values_update model shape env (answersKept binder (inside binder List.mem_cons_self)) value]
          exact (ih (fun name member => inside name (List.mem_cons_of_mem _ member)) _).mp holds
        · rintro ⟨value, holds⟩
          refine ⟨value, (ih (fun name member => inside name (List.mem_cons_of_mem _ member)) _).mpr ?_⟩
          rw [values_update model shape env (answersKept binder (inside binder List.mem_cons_self)) value]
          exact holds

/-- Where a model satisfies the conditions, the finite guards give the rigid
parameters members' values: an instance of the split at the same
environment. -/
theorem splits_of_context {query : Query Variable Literal Symbol} (models : program.Models model) (enumerates : program.Enumerates)
    (split : ∀ name ∈ query.parameters, program.splits query name = true) {environment : Environment Variable Value}
    (holds : model.ContextHolds environment query.context) :
    ∃ values, program.Splits query values ∧ ∀ name ∈ query.parameters, den model (values name) = environment name := by
  have each : ∀ name ∈ query.parameters, ∃ term symbol members, Goal.guard symbol (.var name) ∈ query.conditions ∧
      program.kindAt .guard symbol 1 = true ∧ program.members symbol = some members ∧ term ∈ members ∧
        den model term = environment name := by
    intro name parameter
    have found := split name parameter
    unfold Program.splits at found
    obtain ⟨goal, member, test⟩ := List.any_eq_true.mp found
    cases goal with
    | guard symbol arg =>
        cases arg with
        | var other =>
            simp only [Bool.and_eq_true, beq_iff_eq] at test
            obtain ⟨⟨kind, finite⟩, same⟩ := test
            subst same
            obtain ⟨members, membersEq⟩ := Option.isSome_iff_exists.mp finite
            have atom := holds _ (List.mem_map.mpr ⟨_, member, rfl⟩)
            obtain ⟨declared, declaredEq, declaredKind, _⟩ := kindAt_declared kind
            simp only [Goal.toTerm, Model.Satisfies, Model.eval, List.map_cons, List.map_nil] at atom
            obtain ⟨term, ground, holdsOf, same⟩ := (models.2.2.guards symbol ⟨declared, declaredEq, declaredKind⟩ _).mp atom
            exact ⟨term, symbol, members, member, kind, membersEq, ((enumerates symbol members kind membersEq).2 term).mp holdsOf, same⟩
        | _ => simp at test
    | _ => simp at test
  classical
  refine ⟨fun name => if parameter : name ∈ query.parameters then Classical.choose (each name parameter) else .truth, ?_, ?_⟩
  · intro name parameter
    obtain ⟨symbol, members, member, kind, membersEq, inMembers, _⟩ := Classical.choose_spec (each name parameter)
    exact ⟨symbol, members, member, kind, membersEq, by simpa [parameter] using inMembers⟩
  · intro name parameter
    obtain ⟨_, _, _, _, _, _, same⟩ := Classical.choose_spec (each name parameter)
    simpa [parameter] using same

omit [FreshNames Variable] in
/-- An instance's environment: where the parameters already have the
values' values, the substitution gives the same environment. -/
theorem instance_environment {query : Query Variable Literal Symbol} {values : Variable → Term Variable Literal Symbol}
    (splits : program.Splits query values) (enumerates : program.Enumerates) {environment : Environment Variable Value}
    (same : ∀ name ∈ query.parameters, den model (values name) = environment name) :
    (fun name => model.eval environment (query.instanceSubst values name)) = environment := by
  funext name
  by_cases parameter : name ∈ query.parameters
  · simp only [Query.instanceSubst, parameter, ite_true]
    obtain ⟨symbol, members, _, kind, found, member⟩ := splits name parameter
    rw [eval_ground _ _ ((enumerates symbol members kind found).1 _ member), same name parameter]
  · simp [Query.instanceSubst, parameter, Model.eval]

/-- **A finite guard splits the query.** Its meaning is its ground
instances': Yes exactly when every instance is Yes, No exactly when every
instance is No, and Unknown exactly when one instance is not No and one is not
Yes. -/
theorem meaning_split {query : Query Variable Literal Symbol} (queryOk : QueryOk program query) (enumerates : program.Enumerates)
    (split : ∀ name ∈ query.parameters, program.splits query name = true) :
    ((program.meaning query).truth ↔
        ∀ values, program.Splits query values → (program.meaning (query.instantiate values)).truth) ∧
      ((program.meaning query).falsity ↔
        ∀ values, program.Splits query values → (program.meaning (query.instantiate values)).falsity) ∧
      ((program.meaning query).independence ↔
        (∃ values, program.Splits query values ∧ ¬ (program.meaning (query.instantiate values)).falsity) ∧
          ∃ values, program.Splits query values ∧ ¬ (program.meaning (query.instantiate values)).truth) := by
  refine ⟨⟨fun truth values splits Value model models environment context => ?_,
      fun truth Value model models environment context => ?_⟩,
    ⟨fun falsity values splits Value model models environment context => ?_,
      fun falsity Value model models environment context => ?_⟩,
    ⟨fun ⟨⟨Value, model, models, environment, context, holds⟩, ⟨Value', model', models', environment', context', fails⟩⟩ => ?_,
      fun ⟨⟨values, splits, notFalse⟩, ⟨values', splits', notTrue⟩⟩ => ?_⟩⟩
  · have same := instance_iff (model := model) queryOk splits enumerates environment
    exact same.2.mpr (truth _ _ models _ (same.1.mp context))
  · obtain ⟨values, splits, valuesEq⟩ := splits_of_context models enumerates split context
    have same := instance_iff (model := model) queryOk splits enumerates environment
    rw [instance_environment splits enumerates valuesEq] at same
    exact same.2.mp (truth values splits _ _ models environment (same.1.mpr context))
  · have same := instance_iff (model := model) queryOk splits enumerates environment
    exact fun holds => falsity _ _ models _ (same.1.mp context) (same.2.mp holds)
  · obtain ⟨values, splits, valuesEq⟩ := splits_of_context models enumerates split context
    have same := instance_iff (model := model) queryOk splits enumerates environment
    rw [instance_environment splits enumerates valuesEq] at same
    exact fun holds => falsity values splits _ _ models environment (same.1.mpr context) (same.2.mpr holds)
  · obtain ⟨values, splits, valuesEq⟩ := splits_of_context models enumerates split context
    obtain ⟨values', splits', valuesEq'⟩ := splits_of_context models' enumerates split context'
    have same := instance_iff (model := model) queryOk splits enumerates environment
    have same' := instance_iff (model := model') queryOk splits' enumerates environment'
    rw [instance_environment splits enumerates valuesEq] at same
    rw [instance_environment splits' enumerates valuesEq'] at same'
    exact ⟨⟨values, splits, fun falsity => falsity _ _ models environment (same.1.mpr context) (same.2.mpr holds)⟩,
      ⟨values', splits', fun truth => fails (same'.2.mp (truth _ _ models' environment' (same'.1.mpr context')))⟩⟩
  · classical
    have holding : ∃ (Value : Type) (model : Model Literal Symbol Value program.hoApply), program.Models model ∧
        ∃ environment, model.ContextHolds environment (query.instantiate values).context ∧
          model.Satisfies environment (query.instantiate values).formula :=
      Classical.byContradiction fun none =>
        notFalse fun Value model models environment context holds => none ⟨Value, model, models, environment, context, holds⟩
    have failing : ∃ (Value : Type) (model : Model Literal Symbol Value program.hoApply), program.Models model ∧
        ∃ environment, model.ContextHolds environment (query.instantiate values').context ∧
          ¬ model.Satisfies environment (query.instantiate values').formula :=
      Classical.byContradiction fun none =>
        notTrue fun Value model models environment context => Classical.byContradiction fun fails =>
          none ⟨Value, model, models, environment, context, fails⟩
    obtain ⟨Value, model, models, environment, context, holds⟩ := holding
    obtain ⟨Value', model', models', environment', context', fails⟩ := failing
    have same := instance_iff (model := model) queryOk splits enumerates environment
    have same' := instance_iff (model := model') queryOk splits' enumerates environment'
    exact ⟨⟨Value, model, models, _, same.1.mp context, same.2.mp holds⟩,
      ⟨Value', model', models', _, same'.1.mp context', fun satisfied => fails (same'.2.mpr satisfied)⟩⟩

end Program

end AnthillModKbSpec.IR
