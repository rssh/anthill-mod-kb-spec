import AnthillModKbSpec.Resolution.IR.Semantics
import AnthillModKbSpec.Resolution.IR.Evidence

/-! # The Herbrand reduction (S27)

When every name of an IR program is guarded, by a guard literal of its rule's
or its denial's body, and a query is closed, its answers over the models of
the completion (`Program.meaning`) are its answers over the key fixpoints
(`Program.keyMeaning`): truth in every model is truth in every key fixpoint,
falsity in every model is falsity in each, and independence is independence
(`herbrand`).

One direction holds because every key fixpoint is such a model
(`keyFixpoint_models`). For the other, each model `M` gives a key fixpoint
with its truths (`herbrandInterp`): an atom over keys holds when the keys are
those of ground data terms whose values satisfy the atom in `M`. A guarded
name holds the value of a ground data term in every instance whose body holds,
since a guard holds only of such values; the completion's equality theory
makes the declared constructors free in `M`, so those values are distinct
(S24's `free_of_equality`); and so every literal has the same truth in `M`
and in the key model, under environments related through the ground terms
(`goal_iff`). The key interpretation is then a fixpoint by the completion's
two halves in `M` (`herbrand_fixpoint`). -/

namespace AnthillModKbSpec.IR

open Semantics Completion Tabled Answers

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  [FreshNames Variable]

namespace Program

variable (program : Program Variable Literal Symbol)

/-- Every name of a rule and of a denial is guarded by a guard literal of its
body. -/
structure Guarded : Prop where
  rules : ∀ rule ∈ program.rules, ∀ name ∈ rule.names, program.guarded rule.body name = true
  denials : ∀ body ∈ program.denials, ∀ name ∈ bodyNames body, program.guarded body name = true

/-- What a query's answers claim over the key fixpoints. -/
def keyMeaning (query : Query Variable Literal Symbol) : Meaning where
  truth := ∀ markers interp, program.KeyFixpoint markers interp → ∀ environment,
    (program.keyModel markers interp).ContextHolds environment query.context →
      (program.keyModel markers interp).Satisfies environment query.formula
  falsity := ∀ markers interp, program.KeyFixpoint markers interp → ∀ environment,
    (program.keyModel markers interp).ContextHolds environment query.context →
      ¬ (program.keyModel markers interp).Satisfies environment query.formula
  independence :=
    (∃ markers interp environment, program.KeyFixpoint markers interp ∧
      (program.keyModel markers interp).ContextHolds environment query.context ∧
        (program.keyModel markers interp).Satisfies environment query.formula) ∧
    (∃ markers interp environment, program.KeyFixpoint markers interp ∧
      (program.keyModel markers interp).ContextHolds environment query.context ∧
        ¬ (program.keyModel markers interp).Satisfies environment query.formula)

/-- The atoms of a model over keys: those at the keys of ground data terms
whose values satisfy the atom. -/
def herbrandInterp {Value : Type} (model : Model Literal Symbol Value program.hoApply) : Interp Literal Symbol :=
  fun symbol keys => ∃ terms : List (Term Variable Literal Symbol),
    (∀ term ∈ terms, groundIn program.constructors term = true) ∧ keys = terms.map Open.dataKey ∧
      model.holds (model.application symbol (terms.map (den model)))

/-- The key model of a model's atoms. -/
abbrev herbrandModel {Value : Type} (model : Model Literal Symbol Value program.hoApply) :
    Model Literal Symbol (Key Literal Symbol) program.hoApply :=
  program.keyModel (program.herbrandInterp model) (program.herbrandInterp model)

end Program

/-! ## Facts about lists of ground terms -/

section Lists

omit [FreshNames Variable] in
/-- Ground terms with the same keys are the same (S24's `den_injectives`, in
the key model). -/
theorem dataKeys_injective_of (hoApplySymbol : Symbol) {constructors : List (Constructor Literal Symbol)}
    {terms others : List (Term Variable Literal Symbol)}
    (ground : ∀ term ∈ terms, groundIn constructors term = true) (otherGround : ∀ other ∈ others, groundIn constructors other = true)
    (same : terms.map Open.dataKey = others.map Open.dataKey) : terms = others := by
  have allGround := (groundInAll_iff constructors).mpr ground
  have allOther := (groundInAll_iff constructors).mpr otherGround
  apply den_injectives (free_keys (hoApplySymbol := hoApplySymbol) (fun _ _ => False) constructors) terms others allGround allOther
  rw [dens_keys _ _ terms allGround, dens_keys _ _ others allOther, same]

omit [FreshNames Variable] in
/-- Ground terms with the same values in a model over free constructors are
the same (S24's `den_injectives`). -/
theorem dens_injective_of {Value : Type} {hoApplySymbol : Symbol} {model : Model Literal Symbol Value hoApplySymbol}
    {constructors : List (Constructor Literal Symbol)} (free : Free model constructors)
    {terms others : List (Term Variable Literal Symbol)}
    (ground : ∀ term ∈ terms, groundIn constructors term = true) (otherGround : ∀ other ∈ others, groundIn constructors other = true)
    (same : terms.map (den model) = others.map (den model)) : terms = others :=
  den_injectives free terms others ((groundInAll_iff constructors).mpr ground) ((groundInAll_iff constructors).mpr otherGround) same

omit [FreshNames Variable] in
theorem groundIn_substs {constructors : List (Constructor Literal Symbol)} {σ : Variable → Term Variable Literal Symbol}
    {args : List (Term Variable Literal Symbol)} (data : ∀ arg ∈ args, dataIn constructors arg = true)
    (ground : ∀ name ∈ namesOf args, groundIn constructors (σ name) = true) :
    ∀ term ∈ args.map (subst σ), groundIn constructors term = true := by
  intro term member
  obtain ⟨arg, argMember, rfl⟩ := List.mem_map.mp member
  exact groundIn_subst arg (data arg argMember) fun name occurs =>
    ground name (List.mem_flatMap.mpr ⟨arg, argMember, occurs⟩)

end Lists

namespace Program

variable {program : Program Variable Literal Symbol}

/-! ## Each literal has the same truth -/

section Literals

variable {Value : Type} {model : Model Literal Symbol Value program.hoApply}

/-- A model of the completion makes the declared constructors free. -/
theorem free_of_models (models : program.Models model) : Free model program.constructors :=
  (Completes.of_models (signature := program.signature) (clauses := program.clauses) models.1).free

omit [DecidableEq Variable] [FreshNames Variable] in
theorem dataInAll_of {constructors : List (Constructor Literal Symbol)} {args : List (Term Variable Literal Symbol)}
    (data : ∀ arg ∈ args, dataIn constructors arg = true) : dataInAll constructors args = true :=
  (dataInAll_iff constructors).mpr data

omit [FreshNames Variable] in
/-- An atom of a closed predicate, or of a symbol the base reads from
`markers` at the model's own atoms, has the same truth in the model and in its
key model, at ground arguments. -/
theorem atom_iff {symbol : Symbol} {args : List (Term Variable Literal Symbol)}
    (data : ∀ arg ∈ args, dataIn program.constructors arg = true) {σ : Variable → Term Variable Literal Symbol}
    (ground : ∀ name ∈ namesOf args, groundIn program.constructors (σ name) = true)
    (holdsIff : (program.herbrandModel model).holds ((program.herbrandModel model).application symbol
        ((args.map (subst σ)).map Open.dataKey)) ↔ program.herbrandInterp model symbol ((args.map (subst σ)).map Open.dataKey)) :
    (program.herbrandModel model).Satisfies (fun name => Open.dataKey (σ name)) (.app symbol args) ↔
      model.Satisfies (fun name => den model (σ name)) (.app symbol args) := by
  have keysEq : args.map ((program.herbrandModel model).eval fun name => Open.dataKey (σ name)) =
      (args.map (subst σ)).map Open.dataKey := by
    rw [keys_evalAll_subst _ σ args (dataInAll_of data), List.map_map]
  have valuesEq : args.map (model.eval fun name => den model (σ name)) = (args.map (subst σ)).map (den model) := by
    rw [evalAll_subst model σ args (dataInAll_of data), List.map_map]
  have substGround := groundIn_substs data ground
  simp only [Model.Satisfies, Model.eval]
  rw [keysEq, valuesEq]
  change (program.herbrandModel model).holds ((program.herbrandModel model).application symbol _) ↔ _
  rw [holdsIff]
  constructor
  · rintro ⟨terms, termsGround, keys, holds⟩
    rw [dataKeys_injective_of program.hoApply substGround termsGround keys]; exact holds
  · intro holds
    exact ⟨_, substGround, rfl, holds⟩

/-- **Each literal has the same truth** in a model and in its key model, under
environments that give each of its names a ground term's value and key. -/
theorem goal_iff (wellFormed : program.WellFormed) (models : program.Models model) {goal : Goal Variable Literal Symbol}
    (declared : program.declares goal = true) (data : program.data goal = true) {σ : Variable → Term Variable Literal Symbol}
    (ground : ∀ name ∈ goal.names, groundIn program.constructors (σ name) = true) :
    (program.herbrandModel model).Satisfies (fun name => Open.dataKey (σ name)) goal.toTerm ↔
      model.Satisfies (fun name => den model (σ name)) goal.toTerm := by
  have free := free_of_models models
  have allData : ∀ arg ∈ goal.args, dataIn program.constructors arg = true := List.all_eq_true.mp data
  -- A closed predicate's atom.
  have closedAtom : ∀ {symbol : Symbol} {args : List (Term Variable Literal Symbol)},
      program.closedAt symbol args.length = true → (∀ arg ∈ args, dataIn program.constructors arg = true) →
        (∀ name ∈ namesOf args, groundIn program.constructors (σ name) = true) →
        ((program.herbrandModel model).Satisfies (fun name => Open.dataKey (σ name)) (.app symbol args) ↔
          model.Satisfies (fun name => den model (σ name)) (.app symbol args)) := by
    intro symbol args closed argsData argsGround
    apply atom_iff argsData argsGround
    obtain ⟨found, foundEq, _, _⟩ := closedAt_declared closed
    show resolveKey program.hoApply _ symbol _ ↔ _
    rw [resolveKey_ordinary _ (ordinary_of_declared wellFormed.reserved foundEq)]
    exact join_closed (by rw [List.length_map, List.length_map]; exact closedAt_mem closed)
  -- An equation between data terms.
  have equation : ∀ {left right : Term Variable Literal Symbol}, dataIn program.constructors left = true →
      dataIn program.constructors right = true → (∀ name ∈ left.freeVars ++ right.freeVars, groundIn program.constructors (σ name) = true) →
        ((program.herbrandModel model).Satisfies (fun name => Open.dataKey (σ name)) (.equal left right) ↔
          model.Satisfies (fun name => den model (σ name)) (.equal left right)) := by
    intro left right leftData rightData sidesGround
    have leftGround := groundIn_subst left leftData fun name occurs => sidesGround name (List.mem_append_left _ occurs)
    have rightGround := groundIn_subst right rightData fun name occurs => sidesGround name (List.mem_append_right _ occurs)
    rw [Model.satisfies_equal, Model.satisfies_equal, keys_eval_subst _ σ left leftData, keys_eval_subst _ σ right rightData,
      eval_subst model σ left leftData, eval_subst model σ right rightData]
    constructor
    · intro same; rw [dataKey_injective program.hoApply leftGround rightGround same]
    · intro same; rw [den_injective free _ _ leftGround rightGround same]
  have negation : ∀ (body : Term Variable Literal Symbol),
      ((program.herbrandModel model).Satisfies (fun name => Open.dataKey (σ name)) body ↔
        model.Satisfies (fun name => den model (σ name)) body) →
      ((program.herbrandModel model).Satisfies (fun name => Open.dataKey (σ name)) (.defaultNeg body) ↔
        model.Satisfies (fun name => den model (σ name)) (.defaultNeg body)) := by
    intro body same
    rw [sat_neg _ _ (Model.keys_complement _), sat_neg _ _ models.2.1, same]
  cases goal with
  | call predicate args =>
      exact closedAtom declared (fun arg member => allData arg member) ground
  | naf predicate args =>
      exact negation _ (closedAtom declared (fun arg member => allData arg member) ground)
  | equal left right =>
      exact equation (allData left (by simp [Goal.args])) (allData right (by simp [Goal.args]))
        (fun name occurs => ground name (by simpa [Goal.names, Goal.args, namesOf] using occurs))
  | differ left right =>
      exact negation _ (equation (allData left (by simp [Goal.args])) (allData right (by simp [Goal.args]))
        (fun name occurs => ground name (by simpa [Goal.names, Goal.args, namesOf] using occurs)))
  | guard symbol arg =>
      obtain ⟨found, foundEq, kind, _⟩ := kindAt_declared declared
      have argData := allData arg (by simp [Goal.args])
      have argGround := groundIn_subst arg argData fun name occurs => ground name (by simpa [Goal.names, Goal.args, namesOf] using occurs)
      simp only [Goal.toTerm, Model.Satisfies, Model.eval, List.map_cons, List.map_nil]
      change (program.herbrandModel model).holds ((program.herbrandModel model).application symbol _) ↔
        model.holds (model.application symbol _)
      rw [program.keyModel_base wellFormed foundEq (by simp [Predicate.closed, kind]),
        models.2.2.guards symbol ⟨found, foundEq, kind⟩, keys_eval_subst _ σ arg argData, eval_subst model σ arg argData]
      simp only [base, foundEq, kind]
      constructor
      · rintro ⟨term, termGround, decided, same⟩
        have equal := dataKey_injective program.hoApply argGround termGround (by simpa using same)
        exact ⟨term, termGround, decided, by rw [equal]⟩
      · rintro ⟨term, termGround, decided, same⟩
        have equal := den_injective free _ _ termGround argGround same
        exact ⟨term, termGround, decided, by rw [equal]⟩
  | primitive symbol inputs output =>
      obtain ⟨found, foundEq, kind, _⟩ := kindAt_declared declared
      have argsData : ∀ arg ∈ inputs ++ [output], dataIn program.constructors arg = true := fun arg member => allData arg member
      have argsGround := groundIn_substs argsData fun name occurs => ground name occurs
      simp only [Goal.toTerm, Model.Satisfies, Model.eval]
      change (program.herbrandModel model).holds ((program.herbrandModel model).application symbol _) ↔
        model.holds (model.application symbol _)
      rw [program.keyModel_base wellFormed foundEq (by simp [Predicate.closed, kind]),
        models.2.2.primitives symbol ⟨found, foundEq, kind⟩, keys_evalAll_subst _ σ _ (dataInAll_of argsData),
        evalAll_subst model σ _ (dataInAll_of argsData)]
      simp only [base, foundEq, kind]
      have groundAll : ∀ {firsts : List (Term Variable Literal Symbol)} {last : Term Variable Literal Symbol},
          (∀ term ∈ firsts, groundIn program.constructors term = true) → groundIn program.constructors last = true →
            ∀ term ∈ firsts ++ [last], groundIn program.constructors term = true := by
        intro firsts last firstsGround lastGround term member
        rcases List.mem_append.mp member with inside | inside
        · exact firstsGround term inside
        · rcases List.mem_singleton.mp inside with rfl; exact lastGround
      constructor
      · rintro ⟨firsts, last, firstsGround, lastGround, evaluated, same⟩
        rw [← List.map_map] at same
        have equal := dataKeys_injective_of program.hoApply argsGround (groundAll firstsGround lastGround) same
        exact ⟨firsts, last, firstsGround, lastGround, evaluated, by rw [← List.map_map, equal]⟩
      · rintro ⟨firsts, last, firstsGround, lastGround, evaluated, same⟩
        rw [← List.map_map] at same
        have equal := dens_injective_of free argsGround (groundAll firstsGround lastGround) same
        exact ⟨firsts, last, firstsGround, lastGround, evaluated, by rw [← List.map_map, equal]⟩
  | marker symbol args =>
      simp only [declares, Bool.and_eq_true, Option.isNone_iff_eq_none, bne_iff_ne, ne_eq] at declared
      apply atom_iff (fun arg member => allData arg member) ground
      show resolveKey program.hoApply _ symbol _ ↔ _
      rw [resolveKey_ordinary _ declared.2, join_open (not_closed_of_none declared.1 _)]
      simp only [base, declared.1]

/-- A body has the same truth, literal by literal. -/
theorem body_iff (wellFormed : program.WellFormed) (models : program.Models model)
    {body : List (Goal Variable Literal Symbol)}
    (each : ∀ goal ∈ body, program.declares goal = true ∧ program.data goal = true) {σ : Variable → Term Variable Literal Symbol}
    (ground : ∀ name ∈ bodyNames body, groundIn program.constructors (σ name) = true) :
    (program.herbrandModel model).Satisfies (fun name => Open.dataKey (σ name)) (bodyTerm body) ↔
      model.Satisfies (fun name => den model (σ name)) (bodyTerm body) := by
  unfold bodyTerm
  rw [Model.satisfies_conjunction, Model.satisfies_conjunction]
  constructor
  · intro holds term member
    obtain ⟨goal, goalMember, rfl⟩ := List.mem_map.mp member
    exact (goal_iff wellFormed models (each goal goalMember).1 (each goal goalMember).2
      fun name occurs => ground name (List.mem_flatMap.mpr ⟨goal, goalMember, occurs⟩)).mp
        (holds _ (List.mem_map.mpr ⟨goal, goalMember, rfl⟩))
  · intro holds term member
    obtain ⟨goal, goalMember, rfl⟩ := List.mem_map.mp member
    exact (goal_iff wellFormed models (each goal goalMember).1 (each goal goalMember).2
      fun name occurs => ground name (List.mem_flatMap.mpr ⟨goal, goalMember, occurs⟩)).mpr
        (holds _ (List.mem_map.mpr ⟨goal, goalMember, rfl⟩))

end Literals

/-! ## Guarded names hold ground terms -/

section Guards

variable {Value : Type} {model : Model Literal Symbol Value program.hoApply}

omit [DecidableEq Literal] [FreshNames Variable] in
theorem guard_of_guarded {body : List (Goal Variable Literal Symbol)} {name : Variable}
    (isGuarded : program.guarded body name = true) :
    ∃ symbol, program.kindAt .guard symbol 1 = true ∧ Goal.guard symbol (.var name) ∈ body := by
  unfold Program.guarded at isGuarded
  obtain ⟨goal, member, holds⟩ := List.any_eq_true.mp isGuarded
  cases goal with
  | guard symbol arg =>
      cases arg with
      | var other =>
          simp only [Bool.and_eq_true, beq_iff_eq] at holds
          exact ⟨symbol, holds.1, by rw [← holds.2]; exact member⟩
      | _ => simp at holds
  | _ => simp at holds

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem satisfies_of_mem {Value' : Type} {model' : Model Literal Symbol Value' program.hoApply}
    {environment : Environment Variable Value'} {body : List (Goal Variable Literal Symbol)} {goal : Goal Variable Literal Symbol}
    (holds : model'.Satisfies environment (bodyTerm body)) (member : goal ∈ body) : model'.Satisfies environment goal.toTerm :=
  (Model.satisfies_conjunction model' environment _).mp holds _ (List.mem_map.mpr ⟨goal, member, rfl⟩)

/-- In a model, a body that holds gives each guarded name a ground term's
value. -/
theorem ground_of_guarded (models : program.Models model) {body : List (Goal Variable Literal Symbol)}
    {environment : Environment Variable Value} (holds : model.Satisfies environment (bodyTerm body)) {name : Variable}
    (guarded : program.guarded body name = true) :
    ∃ term : Term Variable Literal Symbol, groundIn program.constructors term = true ∧ den model term = environment name := by
  obtain ⟨symbol, kind, member⟩ := guard_of_guarded guarded
  have atom := satisfies_of_mem holds member
  obtain ⟨found, foundEq, foundKind, _⟩ := kindAt_declared kind
  simp only [Goal.toTerm, Model.Satisfies, Model.eval, List.map_cons, List.map_nil] at atom
  obtain ⟨term, ground, _, same⟩ := (models.2.2.guards symbol ⟨found, foundEq, foundKind⟩ _).mp atom
  exact ⟨term, ground, same⟩

omit [FreshNames Variable] in
/-- In a key model, a body that holds gives each guarded name a ground term's
key. -/
theorem key_of_guarded (wellFormed : program.WellFormed) {markers interp : Interp Literal Symbol}
    {body : List (Goal Variable Literal Symbol)} {environment : Environment Variable (Key Literal Symbol)}
    (holds : (program.keyModel markers interp).Satisfies environment (bodyTerm body)) {name : Variable}
    (guarded : program.guarded body name = true) :
    ∃ term : Term Variable Literal Symbol, groundIn program.constructors term = true ∧ Open.dataKey term = environment name := by
  obtain ⟨symbol, kind, member⟩ := guard_of_guarded guarded
  have atom := satisfies_of_mem holds member
  obtain ⟨found, foundEq, foundKind, _⟩ := kindAt_declared kind
  simp only [Goal.toTerm, Model.Satisfies, Model.eval, List.map_cons, List.map_nil] at atom
  change (program.keyModel markers interp).holds ((program.keyModel markers interp).application symbol _) at atom
  rw [program.keyModel_base wellFormed foundEq (by simp [Predicate.closed, foundKind])] at atom
  simp only [base, foundEq, foundKind] at atom
  obtain ⟨term, ground, _, same⟩ := atom
  exact ⟨term, ground, by simpa using same.symm⟩

open Classical in
/-- Ground terms for a model's environment, where its values are those of
ground terms. -/
noncomputable def groundsOf (model : Model Literal Symbol Value program.hoApply) (environment : Environment Variable Value) :
    Variable → Term Variable Literal Symbol := fun name =>
  if found : ∃ term : Term Variable Literal Symbol, groundIn program.constructors term = true ∧
      den model term = environment name then
    Classical.choose found else .truth

omit [FreshNames Variable] in
theorem groundsOf_spec {environment : Environment Variable Value} {name : Variable}
    (found : ∃ term : Term Variable Literal Symbol, groundIn program.constructors term = true ∧
      den model term = environment name) :
    groundIn program.constructors (program.groundsOf model environment name) = true ∧
      den model (program.groundsOf model environment name) = environment name := by
  unfold groundsOf
  rw [dite_eq_left found]
  exact Classical.choose_spec found

open Classical in
/-- Ground terms for a key environment, where its keys are those of ground
terms. -/
noncomputable def groundsOfKeys (environment : Environment Variable (Key Literal Symbol)) :
    Variable → Term Variable Literal Symbol := fun name =>
  if found : ∃ term : Term Variable Literal Symbol, groundIn program.constructors term = true ∧
      Open.dataKey term = environment name then
    Classical.choose found else .truth

omit [DecidableEq Variable] [FreshNames Variable] in
theorem groundsOfKeys_spec {environment : Environment Variable (Key Literal Symbol)} {name : Variable}
    (found : ∃ term : Term Variable Literal Symbol, groundIn program.constructors term = true ∧
      Open.dataKey term = environment name) :
    groundIn program.constructors (program.groundsOfKeys environment name) = true ∧
      Open.dataKey (program.groundsOfKeys environment name) = environment name := by
  unfold groundsOfKeys
  rw [dite_eq_left found]
  exact Classical.choose_spec found

end Guards

/-! ## The key fixpoint of a model -/

section Fixpoint

variable {Value : Type} {model : Model Literal Symbol Value program.hoApply}

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
/-- A definite clause of the rendering is a rule's. -/
theorem rule_of_clause {symbol : Symbol} {args body : List (Term Variable Literal Symbol)}
    (member : HornClause.definite (.app symbol args) body ∈ program.clauses) :
    ∃ rule ∈ program.rules, rule.head = symbol ∧ rule.args = args ∧ body = rule.body.map Goal.toTerm := by
  rcases List.mem_append.mp member with inRules | inDenials
  · obtain ⟨rule, ruleMember, same⟩ := List.mem_map.mp inRules
    simp only [Rule.toClause, HornClause.definite.injEq, Term.app.injEq] at same
    exact ⟨rule, ruleMember, same.1.1, same.1.2, same.2.symm⟩
  · obtain ⟨_, _, same⟩ := List.mem_map.mp inDenials
    cases same

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem body_names_of_rule {rule : Rule Variable Literal Symbol} {goal : Goal Variable Literal Symbol}
    (member : goal ∈ rule.body) {name : Variable} (occurs : name ∈ goal.names) : name ∈ rule.names :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨goal, member, occurs⟩)

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem head_names_of_rule {rule : Rule Variable Literal Symbol} {arg : Term Variable Literal Symbol}
    (member : arg ∈ rule.args) {name : Variable} (occurs : name ∈ arg.freeVars) : name ∈ rule.names :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨arg, member, occurs⟩)

omit [FreshNames Variable] in
/-- Every literal of a body that scans is declared and data. -/
theorem Scans.goals {bound : List Variable} {body : List (Goal Variable Literal Symbol)} (scans : Scans program bound body) :
    ∀ goal ∈ body, program.declares goal = true ∧ program.data goal = true := by
  induction scans with
  | nil => intro _ inside; cases inside
  | cons declared data _ _ ih =>
      intro goal inside
      rcases List.mem_cons.mp inside with rfl | later
      · exact ⟨declared, data⟩
      · exact ih goal later

omit [FreshNames Variable] in
theorem goals_ok (wellFormed : program.WellFormed) {rule : Rule Variable Literal Symbol} (member : rule ∈ program.rules) :
    ∀ goal ∈ rule.body, program.declares goal = true ∧ program.data goal = true :=
  Scans.goals (wellFormed.rules rule member).scans

omit [FreshNames Variable] in
theorem denial_goals_ok (wellFormed : program.WellFormed) {body : List (Goal Variable Literal Symbol)}
    (member : body ∈ program.denials) : ∀ goal ∈ body, program.declares goal = true ∧ program.data goal = true :=
  Scans.goals (wellFormed.denials body member)

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
/-- A name of a body's formula is a name of one of its literals. -/
theorem bodyNames_of_freeVars {body : List (Goal Variable Literal Symbol)} {name : Variable}
    (occurs : name ∈ (bodyTerm body).freeVars) : name ∈ bodyNames body := by
  unfold bodyTerm at occurs
  obtain ⟨term, termMember, inside⟩ := mem_freeVars_conjunction occurs
  obtain ⟨goal, goalMember, rfl⟩ := List.mem_map.mp termMember
  rw [Goal.toTerm_freeVars] at inside
  exact List.mem_flatMap.mpr ⟨goal, goalMember, inside⟩

/-- **The key fixpoint of a model.** For a guarded program, a model's atoms
over the keys of ground data terms are a key fixpoint. -/
theorem herbrand_fixpoint (wellFormed : program.WellFormed) (guarded : program.Guarded) (models : program.Models model) :
    program.KeyFixpoint (program.herbrandInterp model) (program.herbrandInterp model) := by
  have completes := Completes.of_models (signature := program.signature) (clauses := program.clauses) models.1
  have free := completes.free
  refine ⟨fun symbol keys closed => ⟨fun holds => ?_, fun derived => ?_⟩, fun body member environment holds => ?_⟩
  -- An atom of the model holds by an instance of one of its rules.
  · obtain ⟨terms, termsGround, rfl, atomHolds⟩ := holds
    have onlyIfHolds := completes.onlyIf _ (by simpa using closed)
    obtain ⟨args, body, environment, defining, argsEq, bodyHolds⟩ :=
      onlyIf_case model (values := terms.map (den model)) (by simpa using onlyIfHolds) atomHolds
    obtain ⟨inClauses, _⟩ := definitions_mem defining
    obtain ⟨rule, ruleMember, rfl, rfl, rfl⟩ := rule_of_clause inClauses
    have ruleGuarded := guarded.rules rule ruleMember
    let σ := program.groundsOf model environment
    have bodyHolds' : model.Satisfies environment (bodyTerm rule.body) := bodyHolds
    have spec : ∀ name ∈ rule.names, groundIn program.constructors (σ name) = true ∧ den model (σ name) = environment name :=
      fun name inside => program.groundsOf_spec (ground_of_guarded models bodyHolds' (ruleGuarded name inside))
    have agree : ∀ term, (∀ name ∈ term.freeVars, name ∈ rule.names) →
        model.eval (fun name => den model (σ name)) term = model.eval environment term :=
      fun term inside => Model.eval_congr model term fun name occurs => (spec name (inside name occurs)).2
    have each := goals_ok wellFormed ruleMember
    refine ⟨closed, rule.args, rule.body.map Goal.toTerm, inClauses, fun name => Open.dataKey (σ name), ?_, ?_⟩
    · have ruleData := (wellFormed.rules rule ruleMember).data
      rw [keys_evalAll_subst _ σ rule.args (dataInAll_of ruleData)]
      have substGround := groundIn_substs ruleData fun name occurs =>
        (spec name (List.mem_append_left _ occurs)).1
      have values : (rule.args.map (subst σ)).map (den model) = terms.map (den model) := by
        rw [← argsEq, List.map_map]
        refine List.map_congr_left fun arg member => ?_
        rw [Function.comp, ← eval_subst model σ arg (ruleData arg member)]
        exact agree arg fun name occurs => head_names_of_rule member occurs
      rw [← List.map_map, dens_injective_of free substGround termsGround values]
    · show (program.herbrandModel model).Satisfies _ (bodyTerm rule.body)
      refine (body_iff wellFormed models each fun name occurs => (spec name (List.mem_append_right _ occurs)).1).mpr ?_
      unfold Model.Satisfies
      rw [Model.eval_congr model (bodyTerm rule.body) (left := fun name => den model (σ name)) (right := environment)
        fun name occurs => (spec name (List.mem_append_right _ (bodyNames_of_freeVars occurs))).2]
      exact bodyHolds'
  -- An instance of a rule whose body holds makes its head hold.
  · obtain ⟨_, args, body, inClauses, environment, argsEq, bodyHolds⟩ := derived
    obtain ⟨rule, ruleMember, rfl, rfl, rfl⟩ := rule_of_clause inClauses
    have ruleGuarded := guarded.rules rule ruleMember
    let σ := program.groundsOfKeys environment
    have bodyHolds' : (program.herbrandModel model).Satisfies environment (bodyTerm rule.body) := bodyHolds
    have spec : ∀ name ∈ rule.names, groundIn program.constructors (σ name) = true ∧ Open.dataKey (σ name) = environment name :=
      fun name inside => program.groundsOfKeys_spec (key_of_guarded wellFormed bodyHolds' (ruleGuarded name inside))
    have each := goals_ok wellFormed ruleMember
    have keyBody : (program.herbrandModel model).Satisfies (fun name => Open.dataKey (σ name)) (bodyTerm rule.body) := by
      unfold Model.Satisfies
      rw [Model.eval_congr _ (bodyTerm rule.body) (left := fun name => Open.dataKey (σ name)) (right := environment)
        fun name occurs => (spec name (List.mem_append_right _ (bodyNames_of_freeVars occurs))).2]
      exact bodyHolds'
    have modelBody := (body_iff wellFormed models each fun name occurs => (spec name (List.mem_append_right _ occurs)).1).mp keyBody
    have headHolds := completes.program rule.head rule.args _ inClauses (fun name => den model (σ name))
    rw [sat_imp] at headHolds
    have atom := headHolds modelBody
    have ruleData := (wellFormed.rules rule ruleMember).data
    have substGround := groundIn_substs ruleData fun name occurs => (spec name (List.mem_append_left _ occurs)).1
    refine ⟨rule.args.map (subst σ), substGround, ?_, ?_⟩
    · rw [← argsEq, List.map_map]
      refine List.map_congr_left fun arg member => ?_
      rw [Function.comp, ← keys_eval_subst (program.herbrandInterp model |> join program.signature (program.base (program.herbrandInterp model)))
        σ arg (ruleData arg member)]
      exact Model.eval_congr _ arg fun name occurs => (spec name (head_names_of_rule member occurs)).2.symm
    · simp only [Model.Satisfies, Model.eval] at atom
      rw [evalAll_subst model σ rule.args (dataInAll_of ruleData), ← List.map_map] at atom
      exact atom
  -- No denial's body holds.
  · rcases List.mem_append.mp member with inRules | inDenials
    · obtain ⟨_, _, same⟩ := List.mem_map.mp inRules
      cases same
    · obtain ⟨denial, denialMember, same⟩ := List.mem_map.mp inDenials
      simp only [denialClause, HornClause.goal.injEq] at same
      subst same
      have denialGuarded := guarded.denials denial denialMember
      let σ := program.groundsOfKeys environment
      have holds' : (program.herbrandModel model).Satisfies environment (bodyTerm denial) := holds
      have spec : ∀ name ∈ bodyNames denial, groundIn program.constructors (σ name) = true ∧
          Open.dataKey (σ name) = environment name :=
        fun name inside => program.groundsOfKeys_spec (key_of_guarded wellFormed holds' (denialGuarded name inside))
      have keyBody : (program.herbrandModel model).Satisfies (fun name => Open.dataKey (σ name)) (bodyTerm denial) := by
        unfold Model.Satisfies
        rw [Model.eval_congr _ (bodyTerm denial) (left := fun name => Open.dataKey (σ name)) (right := environment)
          fun name occurs => (spec name (bodyNames_of_freeVars occurs)).2]
        exact holds'
      have modelBody := (body_iff wellFormed models (denial_goals_ok wellFormed denialMember)
        fun name occurs => (spec name occurs).1).mp keyBody
      have denied := models.1 _ (show denialClause denial ∈ program.completion.clauses from
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨denial, denialMember, rfl⟩))))
        (fun name => den model (σ name))
      simp only [denialClause, HornClause.toFormula] at denied
      rw [sat_imp] at denied
      exact not_sat_falsity model _ (denied modelBody)

end Fixpoint

/-! ## Closed queries -/

section Queries

/-- A closed query: no rigid parameter, its literals declared and data, no
answer name in a condition, and every answer name guarded by its goals. Its
conditions then have no name at all. -/
structure Closed (program : Program Variable Literal Symbol) (query : Query Variable Literal Symbol) : Prop where
  parameters : query.parameters = []
  conditions : ∀ goal ∈ query.conditions, program.declares goal = true ∧ program.data goal = true
  goals : ∀ goal ∈ query.goals, program.declares goal = true ∧ program.data goal = true
  apart : ∀ goal ∈ query.conditions, ∀ name ∈ goal.names, name ∉ query.answers
  answers : ∀ name ∈ query.answers, program.guarded query.goals name = true

omit [FreshNames Variable] in
theorem Closed.names_answers {query : Query Variable Literal Symbol} (closed : Closed program query) {name : Variable}
    (occurs : name ∈ bodyNames query.conditions ∨ name ∈ bodyNames query.goals) : name ∈ query.answers := by
  have none := closed.parameters
  unfold Query.parameters at none
  by_cases answer : name ∈ query.answers
  · exact answer
  · have inside : name ∈ (bodyNames query.conditions ++ bodyNames query.goals).eraseDups.filter
        (fun name => !query.answers.contains name) :=
      List.mem_filter.mpr ⟨List.mem_eraseDups.mpr (List.mem_append.mpr occurs), by simp [answer]⟩
    rw [none] at inside
    cases inside

omit [FreshNames Variable] in
theorem Closed.conditions_ground {query : Query Variable Literal Symbol} (closed : Closed program query) :
    ∀ goal ∈ query.conditions, goal.names = [] := by
  intro goal member
  cases names : goal.names with
  | nil => rfl
  | cons name _ =>
      have occurs : name ∈ goal.names := by rw [names]; exact List.mem_cons_self
      exact absurd (closed.names_answers (.inl (List.mem_flatMap.mpr ⟨goal, member, occurs⟩)))
        (closed.apart goal member name occurs)

variable {Value : Type} {model : Model Literal Symbol Value program.hoApply}

/-- A closed query's conditions and formula have the same truth in a model
and in its key model, under any environments. -/
theorem query_iff (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol} (closed : Closed program query)
    (models : program.Models model) (environment : Environment Variable Value)
    (keyEnvironment : Environment Variable (Key Literal Symbol)) :
    ((program.herbrandModel model).ContextHolds keyEnvironment query.context ↔ model.ContextHolds environment query.context) ∧
      ((program.herbrandModel model).Satisfies keyEnvironment query.formula ↔ model.Satisfies environment query.formula) := by
  constructor
  -- The conditions have no names.
  · let σ : Variable → Term Variable Literal Symbol := fun _ => .truth
    have each : ∀ goal ∈ query.conditions,
        ((program.herbrandModel model).Satisfies keyEnvironment goal.toTerm ↔ model.Satisfies environment goal.toTerm) := by
      intro goal member
      have ground := closed.conditions_ground goal member
      have keyFree : ∀ name ∈ goal.toTerm.freeVars, keyEnvironment name = Open.dataKey (σ name) := by
        intro name occurs; rw [Goal.toTerm_freeVars, ground] at occurs; cases occurs
      have valueFree : ∀ name ∈ goal.toTerm.freeVars, environment name = den model (σ name) := by
        intro name occurs; rw [Goal.toTerm_freeVars, ground] at occurs; cases occurs
      unfold Model.Satisfies
      rw [Model.eval_congr _ _ keyFree, Model.eval_congr _ _ valueFree]
      exact goal_iff wellFormed models (closed.conditions goal member).1 (closed.conditions goal member).2
        fun name occurs => by rw [ground] at occurs; cases occurs
    constructor
    · intro holds term member
      obtain ⟨goal, goalMember, rfl⟩ := List.mem_map.mp member
      exact (each goal goalMember).mp (holds _ (List.mem_map.mpr ⟨goal, goalMember, rfl⟩))
    · intro holds term member
      obtain ⟨goal, goalMember, rfl⟩ := List.mem_map.mp member
      exact (each goal goalMember).mpr (holds _ (List.mem_map.mpr ⟨goal, goalMember, rfl⟩))
  -- The formula: its answer names are guarded, and it has no other name.
  · have inAnswers : ∀ name ∈ (bodyTerm query.goals).freeVars, name ∈ query.answers := fun name occurs =>
      closed.names_answers (.inr (bodyNames_of_freeVars occurs))
    unfold Query.formula
    constructor
    · intro holds
      obtain ⟨other, _, bodyHolds⟩ := satisfies_exists_to _ _ _ _ holds
      let σ := program.groundsOfKeys other
      have spec : ∀ name ∈ query.answers, groundIn program.constructors (σ name) = true ∧ Open.dataKey (σ name) = other name :=
        fun name inside => program.groundsOfKeys_spec (key_of_guarded wellFormed bodyHolds (closed.answers name inside))
      have keyBody : (program.herbrandModel model).Satisfies (fun name => Open.dataKey (σ name)) (bodyTerm query.goals) := by
        unfold Model.Satisfies
        rw [Model.eval_congr _ _ (right := other) fun name occurs => (spec name (inAnswers name occurs)).2]
        exact bodyHolds
      have modelBody := (body_iff wellFormed models closed.goals fun name occurs =>
        (spec name (closed.names_answers (.inr occurs))).1).mp keyBody
      apply satisfies_exists_of model _ query.answers environment (fun name => den model (σ name))
      unfold Model.Satisfies
      rw [Model.eval_congr model _ (right := fun name => den model (σ name)) fun name occurs => by
        simp [override, inAnswers name occurs]]
      exact modelBody
    · intro holds
      obtain ⟨other, _, bodyHolds⟩ := satisfies_exists_to _ _ _ _ holds
      let σ := program.groundsOf model other
      have spec : ∀ name ∈ query.answers, groundIn program.constructors (σ name) = true ∧ den model (σ name) = other name :=
        fun name inside => program.groundsOf_spec (ground_of_guarded models bodyHolds (closed.answers name inside))
      have modelBody : model.Satisfies (fun name => den model (σ name)) (bodyTerm query.goals) := by
        unfold Model.Satisfies
        rw [Model.eval_congr model _ (right := other) fun name occurs => (spec name (inAnswers name occurs)).2]
        exact bodyHolds
      have keyBody := (body_iff wellFormed models closed.goals fun name occurs =>
        (spec name (closed.names_answers (.inr occurs))).1).mpr modelBody
      apply satisfies_exists_of _ _ query.answers keyEnvironment (fun name => Open.dataKey (σ name))
      unfold Model.Satisfies
      rw [Model.eval_congr _ _ (right := fun name => Open.dataKey (σ name)) fun name occurs => by
        simp [override, inAnswers name occurs]]
      exact keyBody

end Queries

/-- **The Herbrand reduction.** For a well-formed program whose rules and
denials are guarded, and a closed query whose answer names are guarded, the
answers over the models of the completion are the answers over its key
fixpoints: Yes, No, and Unknown each mean the same over both. -/
theorem herbrand (wellFormed : program.WellFormed) (guarded : program.Guarded) {query : Query Variable Literal Symbol}
    (closed : Closed program query) :
    ((program.meaning query).truth ↔ (program.keyMeaning query).truth) ∧
      ((program.meaning query).falsity ↔ (program.keyMeaning query).falsity) ∧
      ((program.meaning query).independence ↔ (program.keyMeaning query).independence) := by
  let anyKey : Environment Variable (Key Literal Symbol) := fun _ => .truth False
  refine ⟨⟨fun truth markers interp fixed environment context => ?_, fun truth Value model models environment context => ?_⟩,
    ⟨fun falsity markers interp fixed environment context => ?_, fun falsity Value model models environment context => ?_⟩,
    ⟨fun ⟨⟨Value, model, models, environment, context, holds⟩, ⟨Value', model', models', environment', context', fails⟩⟩ => ?_,
      fun ⟨⟨markers, interp, environment, fixed, context, holds⟩, ⟨markers', interp', environment', fixed', context', fails⟩⟩ => ?_⟩⟩
  · exact truth _ _ (program.keyFixpoint_models wellFormed fixed) environment context
  · have same := query_iff wellFormed closed models environment anyKey
    exact same.2.mp (truth _ _ (herbrand_fixpoint wellFormed guarded models) anyKey (same.1.mpr context))
  · exact falsity _ _ (program.keyFixpoint_models wellFormed fixed) environment context
  · have same := query_iff wellFormed closed models environment anyKey
    exact fun holds => falsity _ _ (herbrand_fixpoint wellFormed guarded models) anyKey (same.1.mpr context) (same.2.mpr holds)
  · have same := query_iff wellFormed closed models environment anyKey
    have same' := query_iff wellFormed closed models' environment' anyKey
    exact ⟨⟨_, _, anyKey, herbrand_fixpoint wellFormed guarded models, same.1.mpr context, same.2.mpr holds⟩,
      ⟨_, _, anyKey, herbrand_fixpoint wellFormed guarded models', same'.1.mpr context', fun satisfied => fails (same'.2.mp satisfied)⟩⟩
  · exact ⟨⟨_, _, program.keyFixpoint_models wellFormed fixed, environment, context, holds⟩,
      ⟨_, _, program.keyFixpoint_models wellFormed fixed', environment', context', fails⟩⟩

end Program

end AnthillModKbSpec.IR
