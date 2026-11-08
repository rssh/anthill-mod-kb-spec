import AnthillModKbSpec.Resolution.P0.Open

/-! # The completion's models are fixpoints (S24)

A model of a program's Clark completion over constructor keys is a fixpoint of
the clauses' consequence operator, and every fixpoint is one
(`fixpoint_iff_models`). An interpretation `I` gives the closed atoms, those
of the predicates the signature closes; `base` gives every other atom (unknown
markers, guards, and symbols with no clauses). The **consequence operator**
`consequence` makes a closed atom true when some clause with that head has a
true body instance, evaluated in the key model of `I` and `base`:

- the program's clauses hold exactly when `consequence I ≤ I` (a pre-fixpoint);
- the only-if clauses hold exactly when `I ≤ consequence I` (a post-fixpoint);
- the free equality theory holds in every key model.

The covered programs (`Covered`) have only definite clauses with an atomic head
of a closed predicate, and denials, which must be false in the model.

For **positive** bodies (`positiveGoal`: conjunction, disjunction, quantifiers,
data equations, and atoms over data, no NAF and no implication) the operator is
monotone (`consequence_mono`), so it has a least and a greatest fixpoint
(`lfp`, `gfp`, by Knaster–Tarski): every model of the completion lies between
them. These are the two witnesses of an open goal in P1 (`Tabled/Witness`). -/

namespace AnthillModKbSpec.Tabled

open Semantics Completion

variable {Variable Literal Symbol : Type}

/-- An interpretation of atoms over constructor keys. -/
abbrev Interp (Literal Symbol : Type) := Symbol → List (Key Literal Symbol) → Prop

/-- `I ≤ J`: every atom true in `I` is true in `J`. -/
def Interp.Le (first second : Interp Literal Symbol) : Prop :=
  ∀ symbol keys, first symbol keys → second symbol keys

theorem Interp.Le.refl (interp : Interp Literal Symbol) : interp.Le interp := fun _ _ holds => holds

theorem Interp.Le.trans {first second third : Interp Literal Symbol} (left : first.Le second)
    (right : second.Le third) : first.Le third :=
  fun symbol keys holds => right symbol keys (left symbol keys holds)

section Model

variable [DecidableEq Variable] [DecidableEq Symbol] (hoApplySymbol : Symbol) (signature : Signature Literal Symbol)

/-- A closed atom: of a predicate the signature closes, at its arity. -/
def Closed (symbol : Symbol) (keys : List (Key Literal Symbol)) : Prop := (symbol, keys.length) ∈ signature.predicates

/-- The atoms of a model: closed atoms by `I`, every other atom by `base`. -/
def join (base interp : Interp Literal Symbol) : Interp Literal Symbol := fun symbol keys =>
  ((symbol, keys.length) ∈ signature.predicates ∧ interp symbol keys) ∨
    ((symbol, keys.length) ∉ signature.predicates ∧ base symbol keys)

/-- The key model of an interpretation of the closed atoms. -/
abbrev keyModel (base interp : Interp Literal Symbol) : Model Literal Symbol (Key Literal Symbol) hoApplySymbol :=
  Model.keys hoApplySymbol (join signature base interp)

omit [DecidableEq Variable] [DecidableEq Symbol] in
variable {signature} in
theorem join_closed {base interp : Interp Literal Symbol} {symbol : Symbol} {keys : List (Key Literal Symbol)}
    (closed : (symbol, keys.length) ∈ signature.predicates) : join signature base interp symbol keys ↔ interp symbol keys := by
  simp [join, closed]

omit [DecidableEq Variable] [DecidableEq Symbol] in
variable {signature} in
theorem join_open {base interp : Interp Literal Symbol} {symbol : Symbol} {keys : List (Key Literal Symbol)}
    (opened : (symbol, keys.length) ∉ signature.predicates) : join signature base interp symbol keys ↔ base symbol keys := by
  simp [join, opened]

variable (clauses : List (HornClause Variable Literal Symbol))

/-- The consequence operator: a closed atom holds when a clause with its head
has a true body instance in the model of `I`. -/
def consequence (base interp : Interp Literal Symbol) : Interp Literal Symbol := fun symbol keys =>
  (symbol, keys.length) ∈ signature.predicates ∧ ∃ args body, HornClause.definite (.app symbol args) body ∈ clauses ∧
    ∃ environment : Environment Variable (Key Literal Symbol),
      args.map ((keyModel hoApplySymbol signature base interp).eval environment) = keys ∧
        (keyModel hoApplySymbol signature base interp).Satisfies environment (.conjunction body)

/-- A fixpoint on the closed atoms. -/
def Fixpoint (base interp : Interp Literal Symbol) : Prop :=
  ∀ symbol keys, (symbol, keys.length) ∈ signature.predicates →
    (interp symbol keys ↔ consequence hoApplySymbol signature clauses base interp symbol keys)

/-- Every denial's body is false in the model. -/
def Denied (base interp : Interp Literal Symbol) : Prop :=
  ∀ body, HornClause.goal body ∈ clauses → ∀ environment : Environment Variable (Key Literal Symbol),
    ¬ (keyModel hoApplySymbol signature base interp).Satisfies environment (.conjunction body)

/-- The covered programs: definite clauses with an atomic head of a closed
predicate, and denials; no closed predicate is `ho_apply`. -/
structure Covered : Prop where
  shape : ∀ clause ∈ clauses,
    (∃ symbol args body, clause = .definite (.app symbol args) body ∧ (symbol, args.length) ∈ signature.predicates) ∨
      ∃ body, clause = .goal body
  ordinary : ∀ key ∈ signature.predicates, key.1 ≠ hoApplySymbol

end Model

/-! ## Key models: basic facts -/

section Keys

variable [DecidableEq Variable] [DecidableEq Symbol] {hoApplySymbol : Symbol} (interpretation : Interp Literal Symbol)

theorem keys_imp (environment : Environment Variable (Key Literal Symbol)) (left right : Term Variable Literal Symbol) :
    (Model.keys hoApplySymbol interpretation).Satisfies environment (.imp left right) ↔
      ((Model.keys hoApplySymbol interpretation).Satisfies environment left →
        (Model.keys hoApplySymbol interpretation).Satisfies environment right) := by
  simp only [Model.Satisfies, Model.eval]; exact (Model.keys hoApplySymbol interpretation).holds_implication _ _

theorem keys_conjunction (environment : Environment Variable (Key Literal Symbol)) (terms : List (Term Variable Literal Symbol)) :
    (Model.keys hoApplySymbol interpretation).Satisfies environment (.conjunction terms) ↔
      ∀ term ∈ terms, (Model.keys hoApplySymbol interpretation).Satisfies environment term :=
  Model.satisfies_conjunction _ environment terms

theorem keys_foldr_disj (environment : Environment Variable (Key Literal Symbol)) :
    ∀ cases : List (Term Variable Literal Symbol),
      (Model.keys hoApplySymbol interpretation).Satisfies environment (cases.foldr .disj .falsity) ↔
        ∃ case ∈ cases, (Model.keys hoApplySymbol interpretation).Satisfies environment case :=
  Open.satisfies_foldr_disj environment

theorem keys_equal (environment : Environment Variable (Key Literal Symbol)) (left right : Term Variable Literal Symbol) :
    (Model.keys hoApplySymbol interpretation).Satisfies environment (.equal left right) ↔
      (Model.keys hoApplySymbol interpretation).eval environment left =
        (Model.keys hoApplySymbol interpretation).eval environment right :=
  Model.satisfies_equal _ environment left right

/-- The free equality theory holds in every key model: equality is identity
of constructor trees. -/
theorem keys_equality [DecidableEq Literal] [FreshNames Variable]
    {constructors : List (Constructor Literal Symbol)} {clause : HornClause Variable Literal Symbol}
    (member : clause ∈ equality constructors) (environment : Environment Variable (Key Literal Symbol)) :
    (Model.keys hoApplySymbol interpretation).Satisfies environment clause.toFormula := by
  rcases List.mem_append.mp member with inClashes | inInjections
  · simp only [clashes, List.mem_flatMap, List.mem_filterMap] at inClashes
    obtain ⟨first, _, second, _, produced⟩ := inClashes
    split at produced
    · cases produced
    rename_i distinct
    cases produced
    show (Model.keys hoApplySymbol interpretation).Satisfies environment (.imp (.conjunction [_]) .falsity)
    rw [keys_imp, keys_conjunction]
    intro holds
    have equal := holds _ List.mem_cons_self
    rw [Model.satisfies_equal] at equal
    have names := freshNames_length (Variable := Variable) [] (first.arity + second.arity)
    exfalso
    cases first with
    | literal value =>
        cases second with
        | literal other =>
            simp only [Constructor.pattern, Model.eval] at equal
            change Key.lit _ = Key.lit _ at equal
            exact distinct (by cases equal; rfl)
        | application _ _ =>
            simp only [Constructor.pattern, Model.eval] at equal
            change Key.lit _ = Key.app _ _ at equal
            cases equal
    | application symbol count =>
        cases second with
        | literal _ =>
            simp only [Constructor.pattern, Model.eval] at equal
            change Key.app _ _ = Key.lit _ at equal
            cases equal
        | application other otherCount =>
            simp only [Constructor.pattern, Model.eval, Constructor.arity] at equal names
            change Key.app _ _ = Key.app _ _ at equal
            simp only [Key.app.injEq] at equal
            obtain ⟨sameSymbol, sameArgs⟩ := equal
            have counts := congrArg List.length sameArgs
            simp only [List.length_map, List.length_take, List.length_drop, names] at counts
            exact distinct (by rw [sameSymbol]; congr 1; omega)
  · simp only [injections, List.mem_flatMap] at inInjections
    obtain ⟨constructor, _, produced⟩ := inInjections
    cases constructor with
    | literal _ => cases produced
    | application symbol count =>
        simp only [injective, List.mem_map] at produced
        obtain ⟨⟨left, right⟩, inZip, rfl⟩ := produced
        show (Model.keys hoApplySymbol interpretation).Satisfies environment (.imp (.conjunction [_]) (.equal _ _))
        rw [keys_imp, keys_conjunction, Model.satisfies_equal]
        intro holds
        have equal := holds _ List.mem_cons_self
        rw [Model.satisfies_equal] at equal
        simp only [Model.eval, List.map_map] at equal
        change Key.app _ _ = Key.app _ _ at equal
        simp only [Key.app.injEq] at equal
        exact Open.eq_of_mem_zip_map (f := (Model.keys hoApplySymbol interpretation).eval environment ∘ Term.var)
          (g := (Model.keys hoApplySymbol interpretation).eval environment ∘ Term.var) inZip equal.2

end Keys

/-! ## Opening a case's names -/

section Names

variable [DecidableEq Variable] {Value : Type} {hoApplySymbol : Symbol}
  (model : Model Literal Symbol Value hoApplySymbol)

/-- `env` overridden by `other` on `names`. -/
def override (env other : Environment Variable Value) (names : List Variable) : Environment Variable Value :=
  fun name => if name ∈ names then other name else env name

theorem override_cons (env other : Environment Variable Value) (name : Variable) (names : List Variable) :
    override (update env name (other name)) other names = override env other (name :: names) := by
  funext candidate
  by_cases inside : candidate ∈ names
  · simp [override, inside]
  · by_cases same : candidate = name
    · subst same; simp [override, update, inside]
    · simp [override, update, inside, same]

/-- Existentials over `names` hold when the body holds with the names given
other values. -/
theorem satisfies_exists_of (φ : Term Variable Literal Symbol) :
    ∀ (names : List Variable) (env other : Environment Variable Value),
      model.Satisfies (override env other names) φ → model.Satisfies env (names.foldr Term.existsVar φ)
  | [], env, other, holds => by
      have same : override env other [] = env := by funext name; simp [override]
      rw [same] at holds; exact holds
  | name :: names, env, other, holds => by
      simp only [List.foldr_cons, Model.Satisfies, Model.eval, model.holds_existential]
      refine ⟨other name, ?_⟩
      apply satisfies_exists_of φ names _ other
      rw [override_cons]; exact holds

/-- Existentials over `names` hold only with some values of the names. -/
theorem satisfies_exists_to (φ : Term Variable Literal Symbol) :
    ∀ (names : List Variable) (env : Environment Variable Value),
      model.Satisfies env (names.foldr Term.existsVar φ) →
        ∃ other : Environment Variable Value, (∀ name, name ∉ names → other name = env name) ∧ model.Satisfies other φ
  | [], env, holds => ⟨env, fun _ _ => rfl, holds⟩
  | name :: names, env, holds => by
      simp only [List.foldr_cons, Model.Satisfies, Model.eval, model.holds_existential] at holds
      obtain ⟨value, holds⟩ := holds
      obtain ⟨other, outside, satisfied⟩ := satisfies_exists_to φ names _ holds
      refine ⟨other, fun candidate notIn => ?_, satisfied⟩
      have notHere : candidate ≠ name := fun same => notIn (same ▸ List.mem_cons_self)
      rw [outside candidate (fun inside => notIn (List.mem_cons_of_mem _ inside))]
      simp [update, notHere]

theorem freeVars_conjunction_of {terms : List (Term Variable Literal Symbol)} {term : Term Variable Literal Symbol}
    (member : term ∈ terms) {name : Variable} (occurs : name ∈ term.freeVars) :
    name ∈ (Term.conjunction terms).freeVars := by
  induction terms with
  | nil => cases member
  | cons head rest ih =>
      simp only [Term.conjunction, List.foldr_cons, Term.freeVars, List.mem_append]
      rcases List.mem_cons.mp member with rfl | inRest
      · exact .inl occurs
      · exact .inr (ih inRest)

theorem mem_caseNames {args body : List (Term Variable Literal Symbol)} {term : Term Variable Literal Symbol}
    (member : term ∈ args ++ body) {name : Variable} (occurs : name ∈ term.freeVars) : name ∈ caseNames args body := by
  unfold caseNames
  exact List.mem_eraseDups.mpr (freeVars_conjunction_of member occurs)

end Names

/-! ## Fixpoints and models -/

section Fixpoints

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable]
  {hoApplySymbol : Symbol} {signature : Signature Literal Symbol} {clauses : List (HornClause Variable Literal Symbol)}
  {base interp : Interp Literal Symbol}

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem definitions_mem {symbol : Symbol} {arity : Nat} {pair : List (Term Variable Literal Symbol) × List (Term Variable Literal Symbol)}
    (member : pair ∈ definitions clauses symbol arity) :
    HornClause.definite (.app symbol pair.1) pair.2 ∈ clauses ∧ pair.1.length = arity := by
  simp only [definitions, List.mem_filterMap] at member
  obtain ⟨clause, inClauses, produced⟩ := member
  split at produced
  · rename_i head args body
    split at produced
    · rename_i same
      cases produced
      obtain ⟨rfl, lengths⟩ := same
      exact ⟨inClauses, lengths⟩
    · cases produced
  · cases produced

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem mem_definitions {symbol : Symbol} {args body : List (Term Variable Literal Symbol)}
    (member : HornClause.definite (.app symbol args) body ∈ clauses) :
    (args, body) ∈ definitions clauses symbol args.length :=
  List.mem_filterMap.mpr ⟨_, member, by simp⟩

/-- The keys of a list of names under an environment that maps them, in order. -/
def zipEnv (names : List Variable) (keys : List (Key Literal Symbol)) : Environment Variable (Key Literal Symbol) :=
  fun name => ((names.zip keys).find? (·.1 = name)).elim (.truth False) Prod.snd

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem zipEnv_map : ∀ {names : List Variable} {keys : List (Key Literal Symbol)},
    names.Nodup → names.length = keys.length → names.map (zipEnv names keys) = keys
  | [], [], _, _ => rfl
  | name :: names, key :: keys, distinct, lengths => by
      simp only [List.nodup_cons] at distinct
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · simp [zipEnv]
      · refine Eq.trans (List.map_congr_left fun other member => ?_) (zipEnv_map distinct.2 (by simpa using lengths))
        have different : other ≠ name := fun same => distinct.1 (same ▸ member)
        simp [zipEnv, Ne.symm different]

omit [DecidableEq Literal] in
/-- A fixpoint satisfies the only-if clause of every closed predicate. -/
theorem fixpoint_onlyIf (covered : Covered hoApplySymbol signature clauses)
    (fixpoint : Fixpoint hoApplySymbol signature clauses base interp) {symbol : Symbol} {arity : Nat}
    (key : (symbol, arity) ∈ signature.predicates) (environment : Environment Variable (Key Literal Symbol)) :
    (keyModel hoApplySymbol signature base interp).Satisfies environment (onlyIf clauses symbol arity).toFormula := by
  have ordinary := covered.ordinary _ key
  simp only at ordinary
  unfold onlyIf
  simp only [HornClause.toFormula]
  have headsAvoid := freshNames_avoid ((definitions clauses symbol arity).flatMap fun pair => caseNames pair.1 pair.2) arity
  have headsLength := freshNames_length ((definitions clauses symbol arity).flatMap fun pair => caseNames pair.1 pair.2) arity
  generalize freshNames ((definitions clauses symbol arity).flatMap fun pair => caseNames pair.1 pair.2) arity = heads
    at headsAvoid headsLength ⊢
  rw [keys_imp, keys_conjunction]
  intro holds
  have atomHolds := holds _ List.mem_cons_self
  rw [Model.keys_atom _ environment ordinary] at atomHolds
  have keysLength : (heads.map Term.var |>.map ((keyModel hoApplySymbol signature base interp).eval environment)).length
      = arity := by simp [headsLength]
  rw [join_closed (by rw [keysLength]; exact key)] at atomHolds
  obtain ⟨_, args, body, inClauses, other, argsEq, bodyHolds⟩ :=
    (fixpoint _ _ (by rw [keysLength]; exact key)).mp atomHolds
  have lengths : args.length = arity := by
    simpa [headsLength] using congrArg List.length argsEq
  have defining : (args, body) ∈ definitions clauses symbol arity := lengths ▸ mem_definitions inClauses
  rw [keys_foldr_disj]
  refine ⟨case heads args body, List.mem_map.mpr ⟨(args, body), defining, rfl⟩, ?_⟩
  apply satisfies_exists_of (keyModel hoApplySymbol signature base interp) _ (caseNames args body) environment other
  rw [keys_conjunction]
  have agree : ∀ term ∈ args ++ body, ∀ name ∈ term.freeVars,
      override environment other (caseNames args body) name = other name := fun term member name occurs => by
    simp [override, mem_caseNames member occurs]
  intro conjunct inside
  rcases List.mem_append.mp inside with inEquations | inBody
  · obtain ⟨⟨head, arg⟩, inZip, rfl⟩ := List.mem_map.mp inEquations
    rw [keys_equal]
    have headFresh : head ∉ caseNames args body := by
      have avoid := headsAvoid head (List.of_mem_zip inZip).1
      exact fun inside => avoid (List.mem_flatMap.mpr ⟨(args, body), defining, inside⟩)
    have argMember : arg ∈ args := (List.of_mem_zip inZip).2
    rw [Model.eval_congr _ arg (fun name occurs => agree arg (List.mem_append_left _ argMember) name occurs)]
    simp only [Model.eval, override, headFresh, ite_false]
    simp only [List.map_map] at argsEq
    exact Open.eq_of_mem_zip_map (f := (keyModel hoApplySymbol signature base interp).eval environment ∘ Term.var)
      (g := (keyModel hoApplySymbol signature base interp).eval other) inZip argsEq.symm |> fun same => by
        simpa [Function.comp, Model.eval] using same
  · have holdsHere := (keys_conjunction _ other body).mp bodyHolds conjunct inBody
    show (keyModel hoApplySymbol signature base interp).Satisfies _ conjunct
    unfold Model.Satisfies at holdsHere ⊢
    rw [Model.eval_congr _ conjunct (fun name occurs => agree conjunct (List.mem_append_right _ inBody) name occurs)]
    exact holdsHere

omit [DecidableEq Literal] [FreshNames Variable] in
/-- A fixpoint satisfies every definite clause of a covered program. -/
theorem fixpoint_program (covered : Covered hoApplySymbol signature clauses)
    (fixpoint : Fixpoint hoApplySymbol signature clauses base interp) {symbol : Symbol}
    {args body : List (Term Variable Literal Symbol)} (inProgram : HornClause.definite (.app symbol args) body ∈ clauses)
    (environment : Environment Variable (Key Literal Symbol)) :
    (keyModel hoApplySymbol signature base interp).Satisfies environment (.imp (.conjunction body) (.app symbol args)) := by
  rcases covered.shape _ inProgram with ⟨_, _, _, same, closed⟩ | ⟨_, same⟩
  · cases same
    have ordinary := covered.ordinary _ closed
    rw [keys_imp, Model.keys_atom _ environment ordinary]
    intro holds
    have lengths : (args.map ((keyModel hoApplySymbol signature base interp).eval environment)).length = args.length := by
      simp
    rw [join_closed (by rw [lengths]; exact closed)]
    exact ((fixpoint _ _ (by rw [lengths]; exact closed)).mpr
      ⟨by rw [lengths]; exact closed, args, body, inProgram, environment, rfl, holds⟩)
  · cases same

/-- A pre- and post-fixpoint whose denials are false is a model of the
completed program, with complement NAF. -/
theorem models_of_fixpoint (covered : Covered hoApplySymbol signature clauses)
    (fixpoint : Fixpoint hoApplySymbol signature clauses base interp)
    (denied : Denied hoApplySymbol signature clauses base interp) :
    (keyModel hoApplySymbol signature base interp).Models
      (fun clause => clause ∈ (completion clauses signature).clauses : LogicalKb Variable Literal Symbol) := by
  intro clause member environment
  have member : clause ∈ clauses ++ signature.predicates.map (fun key => onlyIf clauses key.1 key.2) ++
      equality signature.constructors := member
  rcases List.mem_append.mp member with inFirst | inEquality
  rcases List.mem_append.mp inFirst with inProgram | inOnlyIfs
  -- The program's clauses and denials.
  · rcases covered.shape clause inProgram with ⟨symbol, args, body, rfl, closed⟩ | ⟨body, rfl⟩
    · have ordinary := covered.ordinary _ closed
      show (keyModel hoApplySymbol signature base interp).Satisfies environment (.imp (.conjunction body) (.app symbol args))
      rw [keys_imp, Model.keys_atom _ environment ordinary]
      intro holds
      have lengths : (args.map ((keyModel hoApplySymbol signature base interp).eval environment)).length = args.length := by
        simp
      rw [join_closed (by rw [lengths]; exact closed)]
      exact ((fixpoint _ _ (by rw [lengths]; exact closed)).mpr
        ⟨by rw [lengths]; exact closed, args, body, inProgram, environment, rfl, holds⟩)
    · show (keyModel hoApplySymbol signature base interp).Satisfies environment (.imp (.conjunction body) .falsity)
      rw [keys_imp]
      exact fun holds => absurd holds (denied body inProgram environment)
  -- The only-if clauses.
  · obtain ⟨⟨symbol, arity⟩, key, rfl⟩ := List.mem_map.mp inOnlyIfs
    exact fixpoint_onlyIf covered fixpoint key environment
  -- The free equality theory.
  · exact keys_equality _ inEquality environment

theorem map_eq_of_zip {α β γ : Type} {f : α → γ} {g : β → γ} :
    ∀ {left : List α} {right : List β}, left.length = right.length →
      (∀ pair ∈ left.zip right, f pair.1 = g pair.2) → left.map f = right.map g
  | [], [], _, _ => rfl
  | a :: left, b :: right, lengths, pointwise => by
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨pointwise (a, b) (by simp), map_eq_of_zip (by simpa using lengths)
        (fun pair member => pointwise pair (by simp [member]))⟩

/-- A model of the completed program is a fixpoint, and its denials are false. -/
theorem fixpoint_of_models (covered : Covered hoApplySymbol signature clauses)
    (models : (keyModel hoApplySymbol signature base interp).Models
      (fun clause => clause ∈ (completion clauses signature).clauses : LogicalKb Variable Literal Symbol)) :
    Fixpoint hoApplySymbol signature clauses base interp ∧ Denied hoApplySymbol signature clauses base interp := by
  have inCompleted : ∀ clause ∈ clauses, clause ∈ (completion clauses signature).clauses := fun clause member => by
    show clause ∈ clauses ++ _ ++ _; exact List.mem_append_left _ (List.mem_append_left _ member)
  refine ⟨fun symbol keys closed => ⟨fun holds => ?_, fun ⟨_, args, body, inClauses, other, argsEq, bodyHolds⟩ => ?_⟩,
    fun body member environment holds => ?_⟩
  -- Only-if: an atom holds only by a clause.
  · have ordinary := covered.ordinary _ closed
    have onlyIfMember : onlyIf clauses symbol keys.length ∈ (completion clauses signature).clauses := by
      show _ ∈ clauses ++ _ ++ _
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨_, closed, rfl⟩))
    have headsAvoid := freshNames_avoid ((definitions clauses symbol keys.length).flatMap fun pair => caseNames pair.1 pair.2) keys.length
    have headsLength := freshNames_length ((definitions clauses symbol keys.length).flatMap fun pair => caseNames pair.1 pair.2) keys.length
    have headsDistinct := freshNames_nodup ((definitions clauses symbol keys.length).flatMap fun pair => caseNames pair.1 pair.2) keys.length
    have satisfied := models _ onlyIfMember
    unfold onlyIf at satisfied
    dsimp only at satisfied
    generalize freshNames ((definitions clauses symbol keys.length).flatMap fun pair => caseNames pair.1 pair.2) keys.length = heads
      at headsAvoid headsLength headsDistinct satisfied
    have atKeys := satisfied (zipEnv heads keys)
    simp only [HornClause.toFormula] at atKeys
    rw [keys_imp, keys_conjunction] at atKeys
    have keysEq : (heads.map Term.var).map ((keyModel hoApplySymbol signature base interp).eval (zipEnv heads keys)) = keys := by
      simp only [List.map_map]
      exact (List.map_congr_left fun name _ => by simp [Model.eval]).trans (zipEnv_map headsDistinct headsLength)
    have cases := atKeys fun term member => by
      rcases List.mem_singleton.mp member with rfl
      rw [Model.keys_atom _ _ ordinary, keysEq, join_closed closed]
      exact holds
    rw [keys_foldr_disj] at cases
    obtain ⟨found, inCases, foundHolds⟩ := cases
    obtain ⟨⟨args, body⟩, defining, rfl⟩ := List.mem_map.mp inCases
    obtain ⟨inClauses, lengths⟩ := definitions_mem defining
    obtain ⟨other, outside, conjunctHolds⟩ := satisfies_exists_to _ _ _ _ foundHolds
    rw [keys_conjunction] at conjunctHolds
    refine ⟨closed, args, body, inClauses, other, ?_, (keys_conjunction _ other body).mpr fun goal inside =>
      conjunctHolds goal (List.mem_append_right _ inside)⟩
    have headsFresh : ∀ head ∈ heads, head ∉ caseNames args body := fun head member inside =>
      headsAvoid head member (List.mem_flatMap.mpr ⟨(args, body), defining, inside⟩)
    calc args.map ((keyModel hoApplySymbol signature base interp).eval other)
        = heads.map (zipEnv heads keys) := by
          refine (map_eq_of_zip (by rw [headsLength, lengths]) fun pair member => ?_).symm
          have equal := conjunctHolds _ (List.mem_append_left _ (List.mem_map.mpr ⟨pair, member, rfl⟩))
          rw [keys_equal] at equal
          simp only [Model.eval] at equal
          rw [← equal, outside _ (headsFresh _ (List.of_mem_zip member).1)]
      _ = keys := zipEnv_map headsDistinct headsLength
  -- A clause instance with a true body makes its head true.
  · have ordinary := covered.ordinary _ closed
    have satisfied := models _ (inCompleted _ inClauses) other
    simp only [HornClause.toFormula] at satisfied
    rw [keys_imp, Model.keys_atom _ _ ordinary, argsEq, join_closed closed] at satisfied
    exact satisfied bodyHolds
  -- Denials.
  · have satisfied := models _ (inCompleted _ member) environment
    simp only [HornClause.toFormula] at satisfied
    rw [keys_imp] at satisfied
    have contradiction := satisfied holds
    simp only [Model.Satisfies, Model.eval] at contradiction
    exact (Model.keys hoApplySymbol _).holds_bottom contradiction

/-- **The completion's models are the fixpoints.** For a covered program, the
key model of an interpretation of the closed atoms satisfies the completed
program exactly when the interpretation is a fixpoint of the consequence
operator and every denial's body is false. -/
theorem fixpoint_iff_models (covered : Covered hoApplySymbol signature clauses) :
    (keyModel hoApplySymbol signature base interp).Models
        (fun clause => clause ∈ (completion clauses signature).clauses : LogicalKb Variable Literal Symbol) ↔
      Fixpoint hoApplySymbol signature clauses base interp ∧ Denied hoApplySymbol signature clauses base interp :=
  ⟨fixpoint_of_models covered, fun ⟨fixpoint, denied⟩ => models_of_fixpoint covered fixpoint denied⟩

end Fixpoints

/-! ## Least and greatest fixpoints -/

section Lattice

variable (operator : Interp Literal Symbol → Interp Literal Symbol)

/-- The meet of the pre-fixpoints. -/
def lfp : Interp Literal Symbol := fun symbol keys =>
  ∀ other : Interp Literal Symbol, (operator other).Le other → other symbol keys

/-- The join of the post-fixpoints. -/
def gfp : Interp Literal Symbol := fun symbol keys =>
  ∃ other : Interp Literal Symbol, other.Le (operator other) ∧ other symbol keys

def Monotone : Prop := ∀ first second, first.Le second → (operator first).Le (operator second)

variable {operator}

theorem lfp_le {other : Interp Literal Symbol} (pre : (operator other).Le other) : (lfp operator).Le other :=
  fun _ _ holds => holds other pre

theorem le_gfp {other : Interp Literal Symbol} (post : other.Le (operator other)) : other.Le (gfp operator) :=
  fun _ _ holds => ⟨other, post, holds⟩

theorem lfp_pre (mono : Monotone operator) : (operator (lfp operator)).Le (lfp operator) :=
  fun symbol keys holds _ pre => pre symbol keys (mono _ _ (lfp_le pre) symbol keys holds)

theorem lfp_post (mono : Monotone operator) : (lfp operator).Le (operator (lfp operator)) :=
  lfp_le (mono _ _ (lfp_pre mono))

theorem gfp_post (mono : Monotone operator) : (gfp operator).Le (operator (gfp operator)) :=
  fun symbol keys ⟨_, post, holds⟩ => mono _ _ (le_gfp post) symbol keys (post symbol keys holds)

theorem gfp_pre (mono : Monotone operator) : (operator (gfp operator)).Le (gfp operator) :=
  le_gfp (mono _ _ (gfp_post mono))

end Lattice

/-! ## Positive programs -/

section Positive

variable [DecidableEq Symbol]

mutual
/-- A data term: names, literals, and applications of data terms. -/
def dataArg : Term Variable Literal Symbol → Bool
  | .var _ | .lit _ => true
  | .app _ args => dataArgs args
  | _ => false

def dataArgs : List (Term Variable Literal Symbol) → Bool
  | [] => true
  | arg :: rest => dataArg arg && dataArgs rest
end

omit [DecidableEq Symbol] in
theorem dataArgs_iff : ∀ {args : List (Term Variable Literal Symbol)}, dataArgs args = true ↔ ∀ arg ∈ args, dataArg arg = true
  | [] => by simp [dataArgs]
  | arg :: rest => by simp [dataArgs, dataArgs_iff (args := rest)]

/-- A positive goal: truth, falsity, conjunction, disjunction, quantifiers,
equations between data terms, and atoms of ordinary symbols over data terms. -/
def positiveGoal (hoApplySymbol : Symbol) : Term Variable Literal Symbol → Bool
  | .truth | .falsity => true
  | .conj left right | .disj left right => positiveGoal hoApplySymbol left && positiveGoal hoApplySymbol right
  | .existsVar _ body | .forallVar _ body => positiveGoal hoApplySymbol body
  | .equal left right => dataArg left && dataArg right
  | .app symbol args => decide (symbol ≠ hoApplySymbol) && dataArgs args
  | _ => false

variable [DecidableEq Variable] {hoApplySymbol : Symbol}

mutual
/-- A data term's key does not depend on the interpretation. -/
theorem eval_dataArg (first second : Interp Literal Symbol) (environment : Environment Variable (Key Literal Symbol)) :
    ∀ (term : Term Variable Literal Symbol), dataArg term = true →
      (Model.keys hoApplySymbol first).eval environment term = (Model.keys hoApplySymbol second).eval environment term
  | .var _, _ => by simp only [Model.eval]
  | .lit _, _ => by simp only [Model.eval]; rfl
  | .app symbol args, data => by
      simp only [Model.eval]
      exact congrArg (Key.app symbol) (eval_dataArgs first second environment args (by simpa [dataArg] using data))

theorem eval_dataArgs (first second : Interp Literal Symbol) (environment : Environment Variable (Key Literal Symbol)) :
    ∀ (args : List (Term Variable Literal Symbol)), dataArgs args = true →
      args.map ((Model.keys hoApplySymbol first).eval environment) = args.map ((Model.keys hoApplySymbol second).eval environment)
  | [], _ => rfl
  | arg :: rest, data => by
      simp only [dataArgs, Bool.and_eq_true] at data
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨eval_dataArg first second environment arg data.1, eval_dataArgs first second environment rest data.2⟩
end

/-- Positive goals are monotone in the interpretation. -/
theorem satisfies_mono {first second : Interp Literal Symbol} (le : first.Le second) :
    ∀ (goal : Term Variable Literal Symbol) (environment : Environment Variable (Key Literal Symbol)),
      positiveGoal hoApplySymbol goal = true →
        (Model.keys hoApplySymbol first).Satisfies environment goal → (Model.keys hoApplySymbol second).Satisfies environment goal
  | .truth, environment, _, _ => by simp only [Model.Satisfies, Model.eval]; exact (Model.keys hoApplySymbol second).holds_top
  | .falsity, environment, _, holds => by
      simp only [Model.Satisfies, Model.eval] at holds; exact absurd holds (Model.keys hoApplySymbol first).holds_bottom
  | .conj left right, environment, positive, holds => by
      simp only [positiveGoal, Bool.and_eq_true] at positive
      simp only [Model.Satisfies, Model.eval, (Model.keys hoApplySymbol first).holds_conjunction,
        (Model.keys hoApplySymbol second).holds_conjunction] at holds ⊢
      exact ⟨satisfies_mono le left environment positive.1 holds.1, satisfies_mono le right environment positive.2 holds.2⟩
  | .disj left right, environment, positive, holds => by
      simp only [positiveGoal, Bool.and_eq_true] at positive
      simp only [Model.Satisfies, Model.eval, (Model.keys hoApplySymbol first).holds_disjunction,
        (Model.keys hoApplySymbol second).holds_disjunction] at holds ⊢
      exact holds.elim (fun inLeft => .inl (satisfies_mono le left environment positive.1 inLeft))
        (fun inRight => .inr (satisfies_mono le right environment positive.2 inRight))
  | .existsVar name body, environment, positive, holds => by
      simp only [positiveGoal] at positive
      simp only [Model.Satisfies, Model.eval, (Model.keys hoApplySymbol first).holds_existential,
        (Model.keys hoApplySymbol second).holds_existential] at holds ⊢
      obtain ⟨value, holds⟩ := holds
      exact ⟨value, satisfies_mono le body _ positive holds⟩
  | .forallVar name body, environment, positive, holds => by
      simp only [positiveGoal] at positive
      simp only [Model.Satisfies, Model.eval, (Model.keys hoApplySymbol first).holds_universal,
        (Model.keys hoApplySymbol second).holds_universal] at holds ⊢
      exact fun value => satisfies_mono le body _ positive (holds value)
  | .equal left right, environment, positive, holds => by
      simp only [positiveGoal, Bool.and_eq_true] at positive
      rw [keys_equal] at holds ⊢
      rw [← eval_dataArg first second environment left positive.1, ← eval_dataArg first second environment right positive.2]
      exact holds
  | .app symbol args, environment, positive, holds => by
      simp only [positiveGoal, Bool.and_eq_true, decide_eq_true_eq] at positive
      rw [Model.keys_atom _ _ positive.1] at holds ⊢
      rw [← eval_dataArgs first second environment args positive.2]
      exact le _ _ holds
  | .var _, _, positive, _ | .lit _, _, positive, _ | .imp _ _, _, positive, _ | .defaultNeg _, _, positive, _
  | .dictionaryCall _ _ _ _, _, positive, _ => by simp [positiveGoal] at positive

omit [DecidableEq Symbol] in
theorem join_mono (signature : Signature Literal Symbol) (base : Interp Literal Symbol) {first second : Interp Literal Symbol}
    (le : first.Le second) : (join signature base first).Le (join signature base second) :=
  fun _ _ holds => holds.elim (fun ⟨closed, inFirst⟩ => .inl ⟨closed, le _ _ inFirst⟩) .inr

/-- A program whose definite clauses have data head arguments and positive bodies. -/
def PositiveProgram (hoApplySymbol : Symbol) (clauses : List (HornClause Variable Literal Symbol)) : Prop :=
  ∀ symbol args body, HornClause.definite (.app symbol args) body ∈ clauses →
    dataArgs args = true ∧ ∀ goal ∈ body, positiveGoal hoApplySymbol goal = true

omit [DecidableEq Variable] in
theorem positiveGoal_conjunction : ∀ {goals : List (Term Variable Literal Symbol)},
    (∀ goal ∈ goals, positiveGoal hoApplySymbol goal = true) → positiveGoal hoApplySymbol (Term.conjunction goals) = true
  | [], _ => rfl
  | goal :: rest, positive => by
      simp only [Term.conjunction, List.foldr_cons, positiveGoal, Bool.and_eq_true]
      exact ⟨positive goal List.mem_cons_self, positiveGoal_conjunction fun other member => positive other (List.mem_cons_of_mem _ member)⟩

/-- The consequence operator of a positive program is monotone. -/
theorem consequence_mono (signature : Signature Literal Symbol) {clauses : List (HornClause Variable Literal Symbol)}
    (positive : PositiveProgram hoApplySymbol clauses) (base : Interp Literal Symbol) :
    Monotone (consequence hoApplySymbol signature clauses base) := by
  intro first second le symbol keys ⟨closed, args, body, inClauses, environment, argsEq, holds⟩
  refine ⟨closed, args, body, inClauses, environment, ?_, satisfies_mono (join_mono signature base le) _ environment
    (positiveGoal_conjunction (positive _ _ body inClauses).2) holds⟩
  rw [← argsEq]
  exact (eval_dataArgs _ _ environment args (positive _ _ body inClauses).1).symm

end Positive

end AnthillModKbSpec.Tabled
