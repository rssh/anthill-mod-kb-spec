import AnthillModKbSpec.Resolution.Tabled.Abstract

/-! # The abstract fixpoints are sound (S24)

Every value of a model whose declared constructors are free (`Free`: distinct
and injective, as the completion's equality theory states) has exactly one
abstraction (`Abs`, `Abs.unique`, `Abs.exists`): the term of the universe that
denotes it, or ⋆ when none does. Abstract evaluation commutes with the
model's (`aeval_abs`), so a body true in a model is possibly true under the
abstraction, and a definitely true body is true (`body_sound`).

- In every model of the completion, the possibly-true atoms of every
  Kripke–Kleene round over-approximate the model's true atoms, and the
  definitely-true ones are true (`kk_sound`). A refuted goal is false in every
  model (`refutes_sound`).
- In the key model of the least fixpoint of a positive program, a goal that
  fails over a closed abstract least fixpoint is false (`least_model`).
- In the key model of the greatest fixpoint, a goal true over a post-fixpoint
  of the universe and one fresh value is true (`greatest_model`).
- A ground fixpoint is a model of the completion (`ground_model`). -/

namespace AnthillModKbSpec.Tabled

open Semantics Completion

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

attribute [local instance] Machine.termEq

/-! ## Lists in step -/

/-- Two lists related pointwise. -/
inductive Along {α β : Type} (relation : α → β → Prop) : List α → List β → Prop
  | nil : Along relation [] []
  | cons {first : α} {second : β} {firsts : List α} {seconds : List β} :
      relation first second → Along relation firsts seconds → Along relation (first :: firsts) (second :: seconds)

theorem Along.length {α β : Type} {relation : α → β → Prop} {firsts : List α} {seconds : List β}
    (along : Along relation firsts seconds) : firsts.length = seconds.length := by
  induction along with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem along_map {α β γ : Type} {relation : α → β → Prop} {f : γ → α} {g : γ → β} :
    ∀ {items : List γ}, (∀ item ∈ items, relation (f item) (g item)) → Along relation (items.map f) (items.map g)
  | [], _ => .nil
  | item :: _, each => .cons (each item List.mem_cons_self) (along_map fun other member => each other (List.mem_cons_of_mem _ member))

theorem Along.map_eq {α β : Type} {relation : α → β → Prop} {f : β → α} (functional : ∀ a b, relation a b → a = f b) :
    ∀ {firsts : List α} {seconds : List β}, Along relation firsts seconds → firsts = seconds.map f
  | _, _, .nil => rfl
  | _, _, .cons here rest => by rw [List.map_cons, functional _ _ here, Along.map_eq functional rest]

theorem Along.unique {α β : Type} {relation : α → β → Prop} (unique : ∀ a b b', relation a b → relation a b' → b = b') :
    ∀ {firsts : List α} {seconds others : List β}, Along relation firsts seconds → Along relation firsts others → seconds = others
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons here rest, .cons there more => by rw [unique _ _ _ here there, Along.unique unique rest more]

theorem Along.mem {α β : Type} {relation : α → β → Prop} :
    ∀ {firsts : List α} {seconds : List β}, Along relation firsts seconds → ∀ second ∈ seconds, ∃ first ∈ firsts, relation first second
  | _, _, .nil, _, member => by cases member
  | _, _, .cons here rest, second, member => by
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨_, List.mem_cons_self, here⟩
      · obtain ⟨first, inFirsts, related⟩ := Along.mem rest second inRest
        exact ⟨first, List.mem_cons_of_mem _ inFirsts, related⟩

theorem Along.mem_left {α β : Type} {relation : α → β → Prop} :
    ∀ {firsts : List α} {seconds : List β}, Along relation firsts seconds → ∀ first ∈ firsts, ∃ second ∈ seconds, relation first second
  | _, _, .nil, _, member => by cases member
  | _, _, .cons here rest, first, member => by
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨_, List.mem_cons_self, here⟩
      · obtain ⟨second, inSeconds, related⟩ := Along.mem_left rest first inRest
        exact ⟨second, List.mem_cons_of_mem _ inSeconds, related⟩

theorem exists_of_map_eq {α β γ : Type} {f : α → γ} {g : β → γ} :
    ∀ {left : List α} {right : List β}, left.map f = right.map g → ∀ b ∈ right, ∃ a ∈ left, f a = g b
  | [], [], _, _, member => by cases member
  | [], _ :: _, same, _, _ => by cases same
  | _ :: _, [], same, _, _ => by cases same
  | a :: left, b :: right, same, item, member => by
      simp only [List.map_cons, List.cons.injEq] at same
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨a, List.mem_cons_self, same.1⟩
      · obtain ⟨found, inLeft, eq⟩ := exists_of_map_eq same.2 item inRest
        exact ⟨found, List.mem_cons_of_mem _ inLeft, eq⟩

theorem allSome_eq_some {α : Type} : ∀ {items : List (Option α)} {found : List α},
    allSome items = some found ↔ items = found.map some
  | [], found => by cases found <;> simp [allSome]
  | some value :: rest, found => by
      cases found with
      | nil => simp [allSome]
      | cons head tail =>
          simp only [allSome, List.map_cons, List.cons.injEq]
          rw [Option.map_eq_some_iff]
          constructor
          · rintro ⟨others, computed, same⟩
            cases same
            exact ⟨rfl, allSome_eq_some.mp computed⟩
          · rintro ⟨same, rfl⟩
            cases Option.some.inj same
            exact ⟨tail, allSome_eq_some.mpr rfl, rfl⟩
  | none :: _, found => by cases found <;> simp [allSome]

theorem allSome_eq_none {α : Type} : ∀ {items : List (Option α)}, allSome items = none → none ∈ items
  | [], found => by simp [allSome] at found
  | some _ :: rest, found => by
      simp only [allSome, Option.map_eq_none_iff] at found
      exact List.mem_cons_of_mem _ (allSome_eq_none found)
  | none :: _, _ => List.mem_cons_self

/-! ## Satisfaction in any model -/

section Satisfaction

variable {Value : Type} {hoApplySymbol : Symbol} (model : Model Literal Symbol Value hoApplySymbol)
  (environment : Environment Variable Value)

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem sat_truth : model.Satisfies environment (.truth : Term Variable Literal Symbol) := by
  simp only [Model.Satisfies, Model.eval]; exact model.holds_top

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem not_sat_falsity : ¬ model.Satisfies environment (.falsity : Term Variable Literal Symbol) := by
  simp only [Model.Satisfies, Model.eval]; exact model.holds_bottom

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem sat_conj (left right : Term Variable Literal Symbol) :
    model.Satisfies environment (.conj left right) ↔ model.Satisfies environment left ∧ model.Satisfies environment right := by
  simp only [Model.Satisfies, Model.eval]; exact model.holds_conjunction _ _

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem sat_disj (left right : Term Variable Literal Symbol) :
    model.Satisfies environment (.disj left right) ↔ model.Satisfies environment left ∨ model.Satisfies environment right := by
  simp only [Model.Satisfies, Model.eval]; exact model.holds_disjunction _ _

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem sat_imp (left right : Term Variable Literal Symbol) :
    model.Satisfies environment (.imp left right) ↔ (model.Satisfies environment left → model.Satisfies environment right) := by
  simp only [Model.Satisfies, Model.eval]; exact model.holds_implication _ _

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem sat_neg (negation : model.ComplementNAF) (body : Term Variable Literal Symbol) :
    model.Satisfies environment (.defaultNeg body) ↔ ¬ model.Satisfies environment body := by
  simp only [Model.Satisfies, Model.eval]; exact negation _

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem sat_exists (name : Variable) (body : Term Variable Literal Symbol) :
    model.Satisfies environment (.existsVar name body) ↔ ∃ value, model.Satisfies (update environment name value) body := by
  simp only [Model.Satisfies, Model.eval]; exact model.holds_existential _

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem sat_forall (name : Variable) (body : Term Variable Literal Symbol) :
    model.Satisfies environment (.forallVar name body) ↔ ∀ value, model.Satisfies (update environment name value) body := by
  simp only [Model.Satisfies, Model.eval]; exact model.holds_universal _

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem sat_app (symbol : Symbol) (args : List (Term Variable Literal Symbol)) :
    model.Satisfies environment (.app symbol args) ↔
      model.holds (model.application symbol (args.map (model.eval environment))) := by
  simp only [Model.Satisfies, Model.eval]

end Satisfaction

/-! ## Free constructors and abstraction -/

section Abstraction

variable {Value : Type} {hoApplySymbol : Symbol} (model : Model Literal Symbol Value hoApplySymbol)

/-- The value of a ground term. -/
def den (term : Term Variable Literal Symbol) : Value := model.eval (fun _ => model.inhabitant) term

/-- The declared constructors are free in the model: injective, and pairwise
distinct, literals included. -/
structure Free (constructors : List (Constructor Literal Symbol)) : Prop where
  injective : ∀ symbol (firsts seconds : List Value), Constructor.application symbol firsts.length ∈ constructors →
    firsts.length = seconds.length → model.application symbol firsts = model.application symbol seconds → firsts = seconds
  apps : ∀ symbol other (firsts seconds : List Value), Constructor.application symbol firsts.length ∈ constructors →
    Constructor.application other seconds.length ∈ constructors → (symbol ≠ other ∨ firsts.length ≠ seconds.length) →
      model.application symbol firsts ≠ model.application other seconds
  appLit : ∀ symbol (firsts : List Value) value, Constructor.application symbol firsts.length ∈ constructors →
    Constructor.literal value ∈ constructors → model.application symbol firsts ≠ model.literal value
  lits : ∀ value other, Constructor.literal value ∈ constructors → Constructor.literal other ∈ constructors → value ≠ other →
    model.literal value ≠ model.literal other

variable {model} {constructors : List (Constructor Literal Symbol)}

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem den_app (symbol : Symbol) (args : List (Term Variable Literal Symbol)) :
    den model (.app symbol args) = model.application symbol (args.map (den model)) := by
  simp only [den, Model.eval]; rfl

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem den_lit (value : Literal) : den model (.lit value : Term Variable Literal Symbol) = model.literal value := by
  simp only [den, Model.eval]

mutual
/-- A ground term's value is its value in every environment. -/
theorem eval_ground (environment : Environment Variable Value) :
    ∀ term : Term Variable Literal Symbol, groundIn constructors term = true → model.eval environment term = den model term
  | .lit _, _ => by simp only [den, Model.eval]
  | .app symbol args, ground => by
      simp only [groundIn, Bool.and_eq_true] at ground
      rw [den_app]; simp only [Model.eval]
      exact congrArg (model.application symbol) (eval_grounds environment args ground.2)
  | .var _, ground | .truth, ground | .falsity, ground | .conj _ _, ground | .disj _ _, ground | .imp _ _, ground
  | .defaultNeg _, ground | .forallVar _ _, ground | .existsVar _ _, ground | .dictionaryCall _ _ _ _, ground
  | .equal _ _, ground => by simp [groundIn] at ground

theorem eval_grounds (environment : Environment Variable Value) :
    ∀ args : List (Term Variable Literal Symbol), groundInAll constructors args = true →
      args.map (model.eval environment) = args.map (den model)
  | [], _ => rfl
  | arg :: rest, ground => by
      simp only [groundInAll, Bool.and_eq_true] at ground
      simp only [List.map_cons, eval_ground environment arg ground.1, eval_grounds environment rest ground.2]
end

mutual
/-- Free constructors give distinct values to distinct ground terms. -/
theorem den_injective (free : Free model constructors) :
    ∀ (term other : Term Variable Literal Symbol), groundIn constructors term = true → groundIn constructors other = true →
      den model term = den model other → term = other
  | .lit value, .lit other, ground, otherGround, same => by
      simp only [groundIn, decide_eq_true_eq] at ground otherGround
      rw [den_lit, den_lit] at same
      by_cases equal : value = other
      · rw [equal]
      · exact absurd same (free.lits _ _ ground otherGround equal)
  | .lit value, .app symbol args, ground, otherGround, same => by
      simp only [groundIn, decide_eq_true_eq, Bool.and_eq_true] at ground otherGround
      rw [den_lit, den_app] at same
      exact absurd same.symm (free.appLit _ _ _ (by simpa using otherGround.1) ground)
  | .app symbol args, .lit value, ground, otherGround, same => by
      simp only [groundIn, decide_eq_true_eq, Bool.and_eq_true] at ground otherGround
      rw [den_lit, den_app] at same
      exact absurd same (free.appLit _ _ _ (by simpa using ground.1) otherGround)
  | .app symbol args, .app other others, ground, otherGround, same => by
      simp only [groundIn, decide_eq_true_eq, Bool.and_eq_true] at ground otherGround
      rw [den_app, den_app] at same
      by_cases shape : symbol = other ∧ args.length = others.length
      · obtain ⟨rfl, lengths⟩ := shape
        have values := free.injective symbol _ _ (by simpa using ground.1) (by simpa using lengths) same
        rw [den_injectives free args others ground.2 otherGround.2 values]
      · refine absurd same (free.apps _ _ _ _ (by simpa using ground.1) (by simpa using otherGround.1) ?_)
        simp only [List.length_map]
        by_cases equal : symbol = other
        · exact .inr fun lengths => shape ⟨equal, lengths⟩
        · exact .inl equal
  | .var _, _, ground, _, _ | .truth, _, ground, _, _ | .falsity, _, ground, _, _ | .conj _ _, _, ground, _, _
  | .disj _ _, _, ground, _, _ | .imp _ _, _, ground, _, _ | .defaultNeg _, _, ground, _, _
  | .forallVar _ _, _, ground, _, _ | .existsVar _ _, _, ground, _, _ | .dictionaryCall _ _ _ _, _, ground, _, _
  | .equal _ _, _, ground, _, _ => by simp [groundIn] at ground
  | .lit _, .var _, _, otherGround, _ | .lit _, .truth, _, otherGround, _ | .lit _, .falsity, _, otherGround, _
  | .lit _, .conj _ _, _, otherGround, _ | .lit _, .disj _ _, _, otherGround, _ | .lit _, .imp _ _, _, otherGround, _
  | .lit _, .defaultNeg _, _, otherGround, _ | .lit _, .forallVar _ _, _, otherGround, _
  | .lit _, .existsVar _ _, _, otherGround, _ | .lit _, .dictionaryCall _ _ _ _, _, otherGround, _
  | .lit _, .equal _ _, _, otherGround, _
  | .app _ _, .var _, _, otherGround, _ | .app _ _, .truth, _, otherGround, _ | .app _ _, .falsity, _, otherGround, _
  | .app _ _, .conj _ _, _, otherGround, _ | .app _ _, .disj _ _, _, otherGround, _ | .app _ _, .imp _ _, _, otherGround, _
  | .app _ _, .defaultNeg _, _, otherGround, _ | .app _ _, .forallVar _ _, _, otherGround, _
  | .app _ _, .existsVar _ _, _, otherGround, _ | .app _ _, .dictionaryCall _ _ _ _, _, otherGround, _
  | .app _ _, .equal _ _, _, otherGround, _ => by simp [groundIn] at otherGround

theorem den_injectives (free : Free model constructors) :
    ∀ (args others : List (Term Variable Literal Symbol)), groundInAll constructors args = true →
      groundInAll constructors others = true → args.map (den model) = others.map (den model) → args = others
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, same => by cases same
  | _ :: _, [], _, _, same => by cases same
  | arg :: rest, other :: more, ground, otherGround, same => by
      simp only [groundInAll, Bool.and_eq_true] at ground otherGround
      simp only [List.map_cons, List.cons.injEq] at same
      rw [den_injective free arg other ground.1 otherGround.1 same.1, den_injectives free rest more ground.2 otherGround.2 same.2]
end

variable (model) (space : List (Term Variable Literal Symbol))

/-- The abstraction of a value: the universe's term that denotes it, or ⋆ when
none does. -/
def Abs (value : Value) : AValue Variable Literal Symbol → Prop
  | some term => term ∈ space ∧ den model term = value
  | none => ∀ term ∈ space, den model term ≠ value

variable {model} {space}

theorem validUniverse_ground (valid : validUniverse constructors space = true) {term : Term Variable Literal Symbol}
    (member : term ∈ space) : groundIn constructors term = true := by
  simp only [validUniverse, List.all_eq_true, Bool.and_eq_true] at valid
  exact (valid term member).1

theorem validUniverse_args (valid : validUniverse constructors space = true) {symbol : Symbol}
    {args : List (Term Variable Literal Symbol)} (member : Term.app symbol args ∈ space) : ∀ arg ∈ args, arg ∈ space := by
  simp only [validUniverse, List.all_eq_true, Bool.and_eq_true] at valid
  have := (valid _ member).2
  simpa using this

theorem Abs.unique (valid : validUniverse constructors space = true) (free : Free model constructors) {value : Value}
    {first second : AValue Variable Literal Symbol} (left : Abs model space value first) (right : Abs model space value second) :
    first = second := by
  cases first with
  | some term =>
      cases second with
      | some other =>
          obtain ⟨member, denotes⟩ := left
          obtain ⟨otherMember, otherDenotes⟩ := right
          rw [den_injective free term other (validUniverse_ground valid member) (validUniverse_ground valid otherMember)
            (denotes.trans otherDenotes.symm)]
      | none => exact absurd left.2 (right term left.1)
  | none =>
      cases second with
      | some other => exact absurd right.2 (left other right.1)
      | none => rfl

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem Abs.exists (value : Value) : ∃ abstract, Abs model space value abstract := by
  by_cases found : ∃ term ∈ space, den model term = value
  · obtain ⟨term, member, denotes⟩ := found
    exact ⟨some term, member, denotes⟩
  · exact ⟨none, fun term member denotes => found ⟨term, member, denotes⟩⟩

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem Abs.mem_values {value : Value} {abstract : AValue Variable Literal Symbol} (abs : Abs model space value abstract) :
    abstract ∈ values space := by
  cases abstract with
  | none => exact List.mem_cons_self
  | some term => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨term, abs.1, rfl⟩)

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem Abs.some_iff {value : Value} {term : Term Variable Literal Symbol} :
    Abs model space value (some term) ↔ term ∈ space ∧ den model term = value := Iff.rfl

/-! ## Abstract evaluation commutes with the model's -/

theorem aevals_eq (env : AEnv Variable Literal Symbol) :
    ∀ args : List (Term Variable Literal Symbol), aevals space env args = allSome (args.map (aeval space env))
  | [] => rfl
  | arg :: rest => by
      simp only [aevals, List.map_cons, aevals_eq env rest]
      cases aeval space env arg with
      | none => simp [allSome]
      | some value => simp only [allSome]; cases allSome (rest.map (aeval space env)) <;> rfl

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem along_some {values : List Value} :
    ∀ {terms : List (Term Variable Literal Symbol)}, Along (Abs model space) values (terms.map some) →
      values = terms.map (den model) ∧ ∀ term ∈ terms, term ∈ space
  | [], along => by cases along; exact ⟨rfl, fun _ member => by cases member⟩
  | term :: rest, along => by
      cases along with
      | cons here more =>
          obtain ⟨member, denotes⟩ := here
          obtain ⟨same, inside⟩ := along_some more
          refine ⟨by rw [List.map_cons, denotes, same], fun other otherMember => ?_⟩
          rcases List.mem_cons.mp otherMember with rfl | inRest
          · exact member
          · exact inside other inRest

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem freeVars_app_mem {symbol : Symbol} {args : List (Term Variable Literal Symbol)} {arg : Term Variable Literal Symbol}
    (member : arg ∈ args) {name : Variable} (occurs : name ∈ arg.freeVars) : name ∈ (Term.app symbol args).freeVars := by
  simp only [Term.freeVars, List.mem_flatMap]; exact ⟨arg, member, occurs⟩

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem freeVars_head_mem {arg : Term Variable Literal Symbol} {rest : List (Term Variable Literal Symbol)} {name : Variable}
    (occurs : name ∈ arg.freeVars) : name ∈ (arg :: rest).flatMap Term.freeVars :=
  List.mem_flatMap.mpr ⟨arg, List.mem_cons_self, occurs⟩

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem freeVars_tail_mem {arg : Term Variable Literal Symbol} {rest : List (Term Variable Literal Symbol)} {name : Variable}
    (occurs : name ∈ rest.flatMap Term.freeVars) : name ∈ (arg :: rest).flatMap Term.freeVars := by
  obtain ⟨other, member, inside⟩ := List.mem_flatMap.mp occurs
  exact List.mem_flatMap.mpr ⟨other, List.mem_cons_of_mem _ member, inside⟩

mutual
/-- A data term evaluated to a term of the universe denotes that term, with no
freeness needed. -/
theorem aeval_some {environment : Environment Variable Value} {env : AEnv Variable Literal Symbol} :
    ∀ (term found : Term Variable Literal Symbol), (∀ name ∈ term.freeVars, Abs model space (environment name) (env name)) →
      aeval space env term = some found → model.eval environment term = den model found
  | .var name, found, abs, evaluated => by
      simp only [aeval] at evaluated
      have := abs name (by simp [Term.freeVars]); rw [evaluated] at this
      simp only [Model.eval]; exact this.2.symm
  | .lit value, found, _, evaluated => by
      simp only [aeval] at evaluated
      split at evaluated
      · cases evaluated; rw [den_lit]; simp only [Model.eval]
      · cases evaluated
  | .app symbol args, found, abs, evaluated => by
      simp only [aeval] at evaluated
      split at evaluated
      · rename_i terms computed
        split at evaluated
        · cases evaluated
          rw [den_app]; simp only [Model.eval]
          exact congrArg (model.application symbol)
            (aevals_some args terms (fun name occurs => abs name (by simpa [Term.freeVars] using occurs)) computed)
        · cases evaluated
      · cases evaluated
  | .truth, _, _, evaluated | .falsity, _, _, evaluated | .conj _ _, _, _, evaluated | .disj _ _, _, _, evaluated
  | .imp _ _, _, _, evaluated | .defaultNeg _, _, _, evaluated | .forallVar _ _, _, _, evaluated
  | .existsVar _ _, _, _, evaluated | .dictionaryCall _ _ _ _, _, _, evaluated | .equal _ _, _, _, evaluated => by
      simp [aeval] at evaluated

theorem aevals_some {environment : Environment Variable Value} {env : AEnv Variable Literal Symbol} :
    ∀ (args terms : List (Term Variable Literal Symbol)),
      (∀ name ∈ args.flatMap Term.freeVars, Abs model space (environment name) (env name)) →
      aevals space env args = some terms → args.map (model.eval environment) = terms.map (den model)
  | [], terms, _, evaluated => by simp only [aevals] at evaluated; cases evaluated; rfl
  | arg :: rest, terms, abs, evaluated => by
      simp only [aevals] at evaluated
      split at evaluated
      · rename_i value found here there
        cases evaluated
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨aeval_some arg value (fun name occurs => abs name (freeVars_head_mem occurs)) here,
          aevals_some rest found (fun name occurs => abs name (freeVars_tail_mem occurs)) there⟩
      · cases evaluated
end

theorem aeval_app_some {env : AEnv Variable Literal Symbol} {symbol : Symbol} {args terms : List (Term Variable Literal Symbol)}
    (computed : aevals space env args = some terms) :
    aeval space env (.app symbol args) = if Term.app symbol terms ∈ space then some (.app symbol terms) else none := by
  simp [aeval, computed]

theorem aeval_app_none {env : AEnv Variable Literal Symbol} {symbol : Symbol} {args : List (Term Variable Literal Symbol)}
    (computed : aevals space env args = none) : aeval space env (.app symbol args) = none := by
  simp [aeval, computed]


mutual
/-- **Abstraction commutes with evaluation.** The abstraction of a data term's
value over declared constructors is its abstract value. -/
theorem aeval_abs (valid : validUniverse constructors space = true) (free : Free model constructors)
    {environment : Environment Variable Value} {env : AEnv Variable Literal Symbol} :
    ∀ term : Term Variable Literal Symbol, dataIn constructors term = true →
      (∀ name ∈ term.freeVars, Abs model space (environment name) (env name)) →
      Abs model space (model.eval environment term) (aeval space env term)
  | .var name, _, abs => by simp only [Model.eval, aeval]; exact abs name (by simp [Term.freeVars])
  | .lit value, data, _ => by
      simp only [dataIn, decide_eq_true_eq] at data
      simp only [aeval, Model.eval]
      split
      · rename_i member; exact ⟨member, den_lit value⟩
      · rename_i absent
        intro term member denotes
        have ground := validUniverse_ground valid member
        cases term with
        | lit other =>
            simp only [groundIn, decide_eq_true_eq] at ground
            rw [den_lit] at denotes
            by_cases same : other = value
            · exact absent (same ▸ member)
            · exact free.lits _ _ ground data same denotes
        | app symbol args =>
            simp only [groundIn, decide_eq_true_eq, Bool.and_eq_true] at ground
            rw [den_app] at denotes
            exact free.appLit _ _ _ (by simpa using ground.1) data denotes
        | _ => simp [groundIn] at ground
  | .app symbol args, data, abs => by
      simp only [dataIn, decide_eq_true_eq, Bool.and_eq_true] at data
      have along := aevals_abs valid free args data.2 (fun name occurs => abs name (by simpa [Term.freeVars] using occurs))
      have evalApp : model.eval environment (.app symbol args) = model.application symbol (args.map (model.eval environment)) := by
        simp only [Model.eval]
      rw [evalApp]
      cases computed : aevals space env args with
      | some terms =>
          rw [aeval_app_some computed]
          rw [aevals_eq, allSome_eq_some] at computed
          rw [computed] at along
          obtain ⟨values, inside⟩ := along_some along
          rw [values]
          have lengths : terms.length = args.length := by
            have := congrArg List.length computed; simp at this; exact this.symm
          by_cases inSpace : Term.app symbol terms ∈ space
          · rw [ite_eq_left inSpace]; exact (Abs.some_iff).mpr ⟨inSpace, den_app symbol terms⟩
          · rw [ite_eq_right inSpace]
            intro other member denotes
            have ground := validUniverse_ground valid member
            cases other with
            | lit value =>
                simp only [groundIn, decide_eq_true_eq] at ground
                rw [den_lit] at denotes
                exact free.appLit _ _ _ (by simpa [lengths] using data.1) ground denotes.symm
            | app other others =>
                simp only [groundIn, decide_eq_true_eq, Bool.and_eq_true] at ground
                rw [den_app] at denotes
                by_cases shape : other = symbol ∧ others.length = terms.length
                · obtain ⟨rfl, otherLengths⟩ := shape
                  have same := free.injective other _ _ (by simpa using ground.1) (by simpa using otherLengths) denotes
                  have termsGround : groundInAll constructors terms = true :=
                    (groundInAll_iff constructors).mpr fun term inTerms => validUniverse_ground valid (inside term inTerms)
                  rw [den_injectives free others terms ground.2 termsGround same] at member
                  exact inSpace member
                · refine free.apps _ _ _ _ (by simpa using ground.1) (by simpa [lengths] using data.1) ?_ denotes
                  simp only [List.length_map]
                  by_cases equal : other = symbol
                  · exact .inr fun lengths => shape ⟨equal, lengths⟩
                  · exact .inl equal
            | _ => simp [groundIn] at ground
      | none =>
          rw [aeval_app_none computed]
          rw [aevals_eq] at computed
          have missing := allSome_eq_none computed
          obtain ⟨argValue, valueMember, related⟩ := Along.mem along none missing
          intro other member denotes
          have ground := validUniverse_ground valid member
          cases other with
          | lit value =>
              simp only [groundIn, decide_eq_true_eq] at ground
              rw [den_lit] at denotes
              exact free.appLit _ _ _ (by simpa using data.1) ground denotes.symm
          | app other others =>
              simp only [groundIn, decide_eq_true_eq, Bool.and_eq_true] at ground
              rw [den_app] at denotes
              by_cases shape : other = symbol ∧ others.length = args.length
              · obtain ⟨rfl, otherLengths⟩ := shape
                have same := free.injective other _ _ (by simpa using ground.1) (by simpa using otherLengths) denotes
                rw [← same] at valueMember
                obtain ⟨part, partMember, partDenotes⟩ := List.mem_map.mp valueMember
                exact related part (validUniverse_args valid member part partMember) partDenotes
              · refine free.apps _ _ _ _ (by simpa using ground.1) (by simpa using data.1) ?_ denotes
                simp only [List.length_map]
                by_cases equal : other = symbol
                · exact .inr fun lengths => shape ⟨equal, lengths⟩
                · exact .inl equal
          | _ => simp [groundIn] at ground
  | .truth, data, _ | .falsity, data, _ | .conj _ _, data, _ | .disj _ _, data, _ | .imp _ _, data, _
  | .defaultNeg _, data, _ | .forallVar _ _, data, _ | .existsVar _ _, data, _ | .dictionaryCall _ _ _ _, data, _
  | .equal _ _, data, _ => by simp [dataIn] at data

theorem aevals_abs (valid : validUniverse constructors space = true) (free : Free model constructors)
    {environment : Environment Variable Value} {env : AEnv Variable Literal Symbol} :
    ∀ args : List (Term Variable Literal Symbol), dataInAll constructors args = true →
      (∀ name ∈ args.flatMap Term.freeVars, Abs model space (environment name) (env name)) →
      Along (Abs model space) (args.map (model.eval environment)) (args.map (aeval space env))
  | [], _, _ => .nil
  | arg :: rest, data, abs => by
      simp only [dataInAll, Bool.and_eq_true] at data
      exact .cons (aeval_abs valid free arg data.1 (fun name occurs => abs name (freeVars_head_mem occurs)))
        (aevals_abs valid free rest data.2 (fun name occurs => abs name (freeVars_tail_mem occurs)))
end

end Abstraction

/-! ## Bodies -/

section Body

variable {Value : Type} {hoApplySymbol : Symbol} (model : Model Literal Symbol Value hoApplySymbol)
  (space : List (Term Variable Literal Symbol)) (signature : Signature Literal Symbol)

/-- The possibly-true atoms over-approximate the model: a true closed atom's
abstraction is among them. -/
def SoundPossible (possibly : List (AAtom Variable Literal Symbol)) : Prop :=
  ∀ symbol (args : List Value) (abstract : List (AValue Variable Literal Symbol)), (symbol, args.length) ∈ signature.predicates →
    model.holds (model.application symbol args) → Along (Abs model space) args abstract → (symbol, abstract) ∈ possibly

/-- The definitely-true atoms are true in the model. -/
def SoundDefinite (definitely : List (GAtom Variable Literal Symbol)) : Prop :=
  ∀ atom ∈ definitely, model.holds (model.application atom.1 (atom.2.map (den model)))

variable {model} {space} {signature}

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem mem_freeVars_conj_left {left right : Term Variable Literal Symbol} {name : Variable} (occurs : name ∈ left.freeVars) :
    name ∈ (Term.conj left right).freeVars := by simp [Term.freeVars, occurs]
omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem mem_freeVars_conj_right {left right : Term Variable Literal Symbol} {name : Variable} (occurs : name ∈ right.freeVars) :
    name ∈ (Term.conj left right).freeVars := by simp [Term.freeVars, occurs]
omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem mem_freeVars_disj_left {left right : Term Variable Literal Symbol} {name : Variable} (occurs : name ∈ left.freeVars) :
    name ∈ (Term.disj left right).freeVars := by simp [Term.freeVars, occurs]
omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem mem_freeVars_disj_right {left right : Term Variable Literal Symbol} {name : Variable} (occurs : name ∈ right.freeVars) :
    name ∈ (Term.disj left right).freeVars := by simp [Term.freeVars, occurs]
omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem mem_freeVars_imp_left {left right : Term Variable Literal Symbol} {name : Variable} (occurs : name ∈ left.freeVars) :
    name ∈ (Term.imp left right).freeVars := by simp [Term.freeVars, occurs]
omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem mem_freeVars_imp_right {left right : Term Variable Literal Symbol} {name : Variable} (occurs : name ∈ right.freeVars) :
    name ∈ (Term.imp left right).freeVars := by simp [Term.freeVars, occurs]
omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem mem_freeVars_equal_left {left right : Term Variable Literal Symbol} {name : Variable} (occurs : name ∈ left.freeVars) :
    name ∈ (Term.equal left right).freeVars := by simp [Term.freeVars, occurs]
omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem mem_freeVars_equal_right {left right : Term Variable Literal Symbol} {name : Variable} (occurs : name ∈ right.freeVars) :
    name ∈ (Term.equal left right).freeVars := by simp [Term.freeVars, occurs]
omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem mem_freeVars_exists {binder name : Variable} {body : Term Variable Literal Symbol} (occurs : name ∈ body.freeVars)
    (other : name ≠ binder) : name ∈ (Term.existsVar binder body).freeVars := by simp [Term.freeVars, occurs, other]
omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem mem_freeVars_forall {binder name : Variable} {body : Term Variable Literal Symbol} (occurs : name ∈ body.freeVars)
    (other : name ≠ binder) : name ∈ (Term.forallVar binder body).freeVars := by simp [Term.freeVars, occurs, other]

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem abs_update {environment : Environment Variable Value} {env : AEnv Variable Literal Symbol} {binder : Variable}
    {body : Term Variable Literal Symbol} {value : Value} {abstract : AValue Variable Literal Symbol}
    (outer : ∀ name, name ∈ body.freeVars → name ≠ binder → Abs model space (environment name) (env name))
    (here : Abs model space value abstract) :
    ∀ name ∈ body.freeVars, Abs model space (update environment binder value name) (update env binder abstract name) := by
  intro name occurs
  by_cases same : name = binder
  · subst same; simpa [update] using here
  · simpa [update, same] using outer name occurs same

variable (valid : validUniverse signature.constructors space = true) (free : Free model signature.constructors)
  (negation : model.ComplementNAF) {definitely : List (GAtom Variable Literal Symbol)}
  {possibly : List (AAtom Variable Literal Symbol)}
  (soundPossible : SoundPossible model space signature possibly) (soundDefinite : SoundDefinite model definitely)
include valid free negation soundPossible soundDefinite

/-- **The body lemma.** A goal true in the model is possibly true under its
abstraction, and a definitely true goal is true. -/
theorem body_sound : ∀ (goal : Term Variable Literal Symbol) (environment : Environment Variable Value)
    (env : AEnv Variable Literal Symbol), (∀ name ∈ goal.freeVars, Abs model space (environment name) (env name)) →
      (model.Satisfies environment goal → possible signature space definitely possibly env goal = true) ∧
        (definite signature space definitely possibly env goal = true → model.Satisfies environment goal)
  | .truth, environment, _, _ => ⟨fun _ => by simp [possible], fun _ => sat_truth model environment⟩
  | .falsity, environment, _, _ =>
      ⟨fun holds => absurd holds (not_sat_falsity model environment), fun found => by simp [definite] at found⟩
  | .conj left right, environment, env, abs => by
      have leftSound := body_sound left environment env fun name occurs => abs name (mem_freeVars_conj_left occurs)
      have rightSound := body_sound right environment env fun name occurs => abs name (mem_freeVars_conj_right occurs)
      simp only [possible, definite, Bool.and_eq_true, sat_conj]
      exact ⟨fun holds => ⟨leftSound.1 holds.1, rightSound.1 holds.2⟩,
        fun found => ⟨leftSound.2 found.1, rightSound.2 found.2⟩⟩
  | .disj left right, environment, env, abs => by
      have leftSound := body_sound left environment env fun name occurs => abs name (mem_freeVars_disj_left occurs)
      have rightSound := body_sound right environment env fun name occurs => abs name (mem_freeVars_disj_right occurs)
      simp only [possible, definite, Bool.or_eq_true, sat_disj]
      exact ⟨fun holds => holds.imp leftSound.1 rightSound.1, fun found => found.imp leftSound.2 rightSound.2⟩
  | .imp left right, environment, env, abs => by
      have leftSound := body_sound left environment env fun name occurs => abs name (mem_freeVars_imp_left occurs)
      have rightSound := body_sound right environment env fun name occurs => abs name (mem_freeVars_imp_right occurs)
      simp only [possible, definite, Bool.or_eq_true, Bool.not_eq_true', sat_imp]
      refine ⟨fun holds => ?_, fun found => ?_⟩
      · cases leftDefinite : definite signature space definitely possibly env left
        · exact .inl rfl
        · exact .inr (rightSound.1 (holds (leftSound.2 leftDefinite)))
      · rcases found with notPossible | rightDefinite
        · exact fun leftHolds => absurd (leftSound.1 leftHolds) (by rw [notPossible]; simp)
        · exact fun _ => rightSound.2 rightDefinite
  | .defaultNeg body, environment, env, abs => by
      have bodySound := body_sound body environment env fun name occurs => abs name (by simpa [Term.freeVars] using occurs)
      simp only [possible, definite, Bool.not_eq_true', sat_neg model environment negation]
      refine ⟨fun holds => ?_, fun found bodyHolds => ?_⟩
      · cases bodyDefinite : definite signature space definitely possibly env body
        · rfl
        · exact absurd (bodySound.2 bodyDefinite) holds
      · exact absurd (bodySound.1 bodyHolds) (by rw [found]; simp)
  | .existsVar binder body, environment, env, abs => by
      have outer : ∀ name, name ∈ body.freeVars → name ≠ binder → Abs model space (environment name) (env name) :=
        fun name occurs other => abs name (mem_freeVars_exists occurs other)
      simp only [possible, definite, List.any_eq_true, sat_exists]
      refine ⟨fun ⟨value, holds⟩ => ?_, fun ⟨term, member, found⟩ => ?_⟩
      · obtain ⟨abstract, related⟩ := Abs.exists (model := model) (space := space) value
        exact ⟨abstract, related.mem_values,
          (body_sound body _ _ (abs_update outer related)).1 holds⟩
      · exact ⟨den model term, (body_sound body _ _ (abs_update outer (Abs.some_iff.mpr ⟨member, rfl⟩))).2 found⟩
  | .forallVar binder body, environment, env, abs => by
      have outer : ∀ name, name ∈ body.freeVars → name ≠ binder → Abs model space (environment name) (env name) :=
        fun name occurs other => abs name (mem_freeVars_forall occurs other)
      simp only [possible, definite, List.all_eq_true, sat_forall]
      refine ⟨fun holds term member => ?_, fun found => by simp at found⟩
      exact (body_sound body _ _ (abs_update outer (Abs.some_iff.mpr ⟨member, rfl⟩))).1 (holds (den model term))
  | .equal left right, environment, env, abs => by
      have leftAbs : dataIn signature.constructors left = true →
          Abs model space (model.eval environment left) (aeval space env left) := fun data =>
        aeval_abs valid free left data fun name occurs => abs name (mem_freeVars_equal_left occurs)
      have rightAbs : dataIn signature.constructors right = true →
          Abs model space (model.eval environment right) (aeval space env right) := fun data =>
        aeval_abs valid free right data fun name occurs => abs name (mem_freeVars_equal_right occurs)
      simp only [possible, definite]
      rw [Model.satisfies_equal]
      by_cases data : dataIn signature.constructors left = true ∧ dataIn signature.constructors right = true
      · simp only [data, Bool.and_self, ite_true]
        refine ⟨fun same => ?_, fun found => ?_⟩
        · have equal := Abs.unique valid free (leftAbs data.1) (same ▸ rightAbs data.2)
          rw [equal]
          cases aeval space env right <;> simp
        · split at found
          · rename_i first second leftEq rightEq
            simp only [decide_eq_true_eq] at found
            subst found
            rw [aeval_some left first (fun name occurs => abs name (mem_freeVars_equal_left occurs)) leftEq,
              aeval_some right first (fun name occurs => abs name (mem_freeVars_equal_right occurs)) rightEq]
          · simp at found
      · have notBoth : (dataIn signature.constructors left && dataIn signature.constructors right) = false := by
          simpa [Bool.and_eq_true] using data
        simp only [notBoth]
        exact ⟨fun _ => rfl, fun found => by simp at found⟩
  | .app symbol args, environment, env, abs => by
      have argsAbs : ∀ name ∈ args.flatMap Term.freeVars, Abs model space (environment name) (env name) :=
        fun name occurs => abs name (by simpa [Term.freeVars] using occurs)
      simp only [possible, definite, sat_app]
      by_cases closed : (decide ((symbol, args.length) ∈ signature.predicates) && dataInAll signature.constructors args) = true
      · simp only [closed, ite_true]
        simp only [Bool.and_eq_true, decide_eq_true_eq] at closed
        refine ⟨fun holds => ?_, fun found => ?_⟩
        · exact decide_eq_true (soundPossible symbol _ _ (by simpa using closed.1) holds (aevals_abs valid free args closed.2 argsAbs))
        · split at found
          · rename_i terms computed
            have values := aevals_some args terms argsAbs computed
            rw [values]
            exact soundDefinite _ (of_decide_eq_true found)
          · simp at found
      · have notClosed : (decide ((symbol, args.length) ∈ signature.predicates) && dataInAll signature.constructors args) = false := by
          simpa using closed
        simp only [notClosed]
        exact ⟨fun _ => rfl, fun found => by simp at found⟩
  | .var _, _, _, _ => ⟨fun _ => by simp [possible], fun found => by simp [definite] at found⟩
  | .lit _, _, _, _ => ⟨fun _ => by simp [possible], fun found => by simp [definite] at found⟩
  | .dictionaryCall _ _ _ _, _, _, _ => ⟨fun _ => by simp [possible], fun found => by simp [definite] at found⟩

end Body


/-! ## Models of the completion -/

section Completion

variable [FreshNames Variable] {Value : Type} {hoApplySymbol : Symbol} (model : Model Literal Symbol Value hoApplySymbol)

omit [FreshNames Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem sat_foldr_disj (environment : Environment Variable Value) :
    ∀ cases : List (Term Variable Literal Symbol),
      model.Satisfies environment (cases.foldr .disj .falsity) ↔ ∃ case ∈ cases, model.Satisfies environment case
  | [] => by simp only [List.foldr_nil, List.not_mem_nil, false_and, exists_false, iff_false]; exact not_sat_falsity model environment
  | case :: rest => by
      simp only [List.foldr_cons, sat_disj, List.mem_cons, exists_eq_or_imp, sat_foldr_disj environment rest]

/-- The values of names, in order, others the default. -/
def zipEnvOf (default : Value) (names : List Variable) (values : List Value) : Environment Variable Value :=
  fun name => ((names.zip values).find? (·.1 = name)).elim default Prod.snd

omit [FreshNames Variable] in
theorem zipEnvOf_map (default : Value) : ∀ {names : List Variable} {values : List Value},
    names.Nodup → names.length = values.length → names.map (zipEnvOf default names values) = values
  | [], [], _, _ => rfl
  | name :: names, value :: values, distinct, lengths => by
      simp only [List.nodup_cons] at distinct
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · simp [zipEnvOf]
      · refine Eq.trans (List.map_congr_left fun other member => ?_) (zipEnvOf_map default distinct.2 (by simpa using lengths))
        have different : other ≠ name := fun same => distinct.1 (same ▸ member)
        simp [zipEnvOf, Ne.symm different]

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem mem_freeVars_conjunction : ∀ {terms : List (Term Variable Literal Symbol)} {name : Variable},
    name ∈ (Term.conjunction terms).freeVars → ∃ term ∈ terms, name ∈ term.freeVars
  | [], name, occurs => by simp [Term.conjunction, Term.freeVars] at occurs
  | term :: rest, name, occurs => by
      simp only [Term.conjunction, List.foldr_cons, Term.freeVars, List.mem_append] at occurs
      rcases occurs with here | there
      · exact ⟨term, List.mem_cons_self, here⟩
      · obtain ⟨other, member, inside⟩ := mem_freeVars_conjunction (terms := rest) there
        exact ⟨other, List.mem_cons_of_mem _ member, inside⟩

variable {clauses : List (HornClause Variable Literal Symbol)} in
omit [DecidableEq Literal] in
/-- In a model of an only-if clause, a true atom has a defining clause whose
instance is true. -/
theorem onlyIf_case {symbol : Symbol} {values : List Value}
    (holds : ∀ environment, model.Satisfies environment (onlyIf clauses symbol values.length).toFormula)
    (atomHolds : model.holds (model.application symbol values)) :
    ∃ args body, ∃ other : Environment Variable Value, (args, body) ∈ definitions clauses symbol values.length ∧
      args.map (model.eval other) = values ∧ model.Satisfies other (.conjunction body) := by
  have headsAvoid := freshNames_avoid ((definitions clauses symbol values.length).flatMap fun pair => caseNames pair.1 pair.2) values.length
  have headsLength := freshNames_length ((definitions clauses symbol values.length).flatMap fun pair => caseNames pair.1 pair.2) values.length
  have headsDistinct := freshNames_nodup ((definitions clauses symbol values.length).flatMap fun pair => caseNames pair.1 pair.2) values.length
  unfold onlyIf at holds
  dsimp only at holds
  generalize freshNames ((definitions clauses symbol values.length).flatMap fun pair => caseNames pair.1 pair.2) values.length = heads
    at headsAvoid headsLength headsDistinct holds
  have atValues := holds (zipEnvOf model.inhabitant heads values)
  simp only [HornClause.toFormula] at atValues
  rw [sat_imp, Model.satisfies_conjunction] at atValues
  have valuesEq : (heads.map Term.var).map (model.eval (zipEnvOf model.inhabitant heads values)) = values := by
    simp only [List.map_map]
    exact (List.map_congr_left fun name _ => by simp [Model.eval]).trans (zipEnvOf_map model.inhabitant headsDistinct headsLength)
  have cases := atValues fun term member => by
    rcases List.mem_singleton.mp member with rfl
    rw [sat_app, valuesEq]; exact atomHolds
  rw [sat_foldr_disj] at cases
  obtain ⟨found, inCases, foundHolds⟩ := cases
  obtain ⟨⟨args, body⟩, defining, rfl⟩ := List.mem_map.mp inCases
  have lengths := (definitions_mem defining).2
  obtain ⟨other, outside, conjunctHolds⟩ := satisfies_exists_to model _ _ _ foundHolds
  rw [Model.satisfies_conjunction] at conjunctHolds
  refine ⟨args, body, other, defining, ?_, (Model.satisfies_conjunction model other body).mpr fun goal inside =>
    conjunctHolds goal (List.mem_append_right _ inside)⟩
  have headsFresh : ∀ head ∈ heads, head ∉ caseNames args body := fun head member inside =>
    headsAvoid head member (List.mem_flatMap.mpr ⟨(args, body), defining, inside⟩)
  calc args.map (model.eval other)
      = heads.map (zipEnvOf model.inhabitant heads values) := by
        refine (map_eq_of_zip (by rw [headsLength, lengths]) fun pair member => ?_).symm
        have equal := conjunctHolds _ (List.mem_append_left _ (List.mem_map.mpr ⟨pair, member, rfl⟩))
        rw [Model.satisfies_equal] at equal
        simp only [Model.eval] at equal
        rw [← equal, outside _ (headsFresh _ (List.of_mem_zip member).1)]
    _ = values := zipEnvOf_map model.inhabitant headsDistinct headsLength

variable (signature : Signature Literal Symbol) (clauses : List (HornClause Variable Literal Symbol))

/-- What the abstract fixpoints need of a model: the program's clauses hold,
the only-if clauses of the closed predicates hold, and the declared
constructors are free. Every model of the completed program has them
(`Completes.of_models`); so does every fixpoint over keys
(`Completes.of_fixpoint`), its denials aside. -/
structure Completes : Prop where
  program : ∀ symbol args body, HornClause.definite (.app symbol args) body ∈ clauses → ∀ environment,
    model.Satisfies environment (.imp (.conjunction body) (.app symbol args))
  onlyIf : ∀ key ∈ signature.predicates, ∀ environment, model.Satisfies environment (onlyIf clauses key.1 key.2).toFormula
  free : Free model signature.constructors

variable {model} {signature} {clauses}

/-- A constructor's value at argument values. -/
def constructorValue (model : Model Literal Symbol Value hoApplySymbol) : Constructor Literal Symbol → List Value → Value
  | .literal value, _ => model.literal value
  | .application symbol _, values => model.application symbol values

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem eval_pattern (environment : Environment Variable Value) (names : List Variable) :
    ∀ constructor : Constructor Literal Symbol,
      model.eval environment (constructor.pattern names) = constructorValue model constructor ((names.take constructor.arity).map environment)
  | .literal value => by simp [Constructor.pattern, constructorValue, Model.eval]
  | .application symbol arity => by
      simp only [Constructor.pattern, constructorValue, Model.eval, List.map_map, Constructor.arity]
      congr 1
      exact List.map_congr_left fun name _ => by simp [Model.eval]

/-- Distinct declared constructors have distinct values, by their clash clause. -/
theorem clash_values (holds : ∀ clause ∈ equality signature.constructors, ∀ environment : Environment Variable Value,
      model.Satisfies environment clause.toFormula)
    {first second : Constructor Literal Symbol} (firstMember : first ∈ signature.constructors)
    (secondMember : second ∈ signature.constructors) (distinct : first ≠ second) {firsts seconds : List Value}
    (firstLength : firsts.length = first.arity) (secondLength : seconds.length = second.arity) :
    constructorValue model first firsts ≠ constructorValue model second seconds := by
  intro same
  have member : (clash first second : HornClause Variable Literal Symbol) ∈ equality signature.constructors :=
    List.mem_append_left _ (clash_mem_clashes firstMember secondMember distinct)
  let names := freshNames (Variable := Variable) [] (first.arity + second.arity)
  have namesDistinct : names.Nodup := freshNames_nodup _ _
  have namesLength : names.length = first.arity + second.arity := freshNames_length _ _
  let environment := zipEnvOf model.inhabitant names (firsts ++ seconds)
  have allValues : names.map environment = firsts ++ seconds :=
    zipEnvOf_map model.inhabitant namesDistinct (by simp [namesLength, firstLength, secondLength])
  have satisfied := holds _ member environment
  simp only [clash, HornClause.toFormula] at satisfied
  rw [sat_imp, Model.satisfies_conjunction] at satisfied
  apply not_sat_falsity model environment
  apply satisfied
  intro term inside
  rcases List.mem_singleton.mp inside with rfl
  rw [Model.satisfies_equal, eval_pattern, eval_pattern]
  have takeFirst : (names.take first.arity).map environment = firsts := by
    rw [List.map_take, allValues, List.take_left' firstLength]
  have takeSecond : ((names.drop first.arity).take second.arity).map environment = seconds := by
    rw [List.map_take, List.map_drop, allValues, List.drop_left' firstLength, List.take_of_length_le (by omega)]
  rw [takeFirst, takeSecond]
  exact same

/-- The equality theory makes the declared constructors free. -/
theorem free_of_equality (holds : ∀ clause ∈ equality signature.constructors, ∀ environment : Environment Variable Value,
    model.Satisfies environment clause.toFormula) : Free model signature.constructors := by
  constructor
  -- Injectivity.
  · intro symbol firsts seconds declared lengths same
    have member : ∀ clause ∈ injective (Variable := Variable) symbol firsts.length, clause ∈ equality signature.constructors :=
      fun clause inside => List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, declared, inside⟩)
    let names := freshNames (Variable := Variable) [] (firsts.length + firsts.length)
    have distinct : names.Nodup := freshNames_nodup _ _
    have namesLength : names.length = firsts.length + firsts.length := freshNames_length _ _
    let environment := zipEnvOf model.inhabitant names (firsts ++ seconds)
    have allValues : names.map environment = firsts ++ seconds :=
      zipEnvOf_map model.inhabitant distinct (by simp [namesLength, lengths])
    have leftValues : (names.take firsts.length).map environment = firsts := by
      rw [List.map_take, allValues, List.take_left' rfl]
    have rightValues : (names.drop firsts.length).map environment = seconds := by
      rw [List.map_drop, allValues, List.drop_left' rfl]
    suffices pointwise : ∀ pair ∈ firsts.zip seconds, pair.1 = pair.2 by
      simpa using map_eq_of_zip (f := (id : Value → Value)) (g := id) lengths pointwise
    intro pair inZip
    have pairMember : pair ∈ firsts.zip seconds := inZip
    rw [← leftValues, ← rightValues, List.zip_map, List.mem_map] at pairMember
    obtain ⟨⟨left, right⟩, namesZip, rfl⟩ := pairMember
    have clauseMember := member _ (List.mem_map.mpr ⟨(left, right), namesZip, rfl⟩)
    have satisfied := holds _ clauseMember environment
    simp only [HornClause.equation, HornClause.toFormula] at satisfied
    rw [sat_imp, Model.satisfies_conjunction, Model.satisfies_equal] at satisfied
    simp only [Model.eval] at satisfied
    apply satisfied
    intro term inside
    rcases List.mem_singleton.mp inside with rfl
    rw [Model.satisfies_equal]
    simp only [Model.eval, List.map_map]
    have leftEval : (names.take firsts.length).map (model.eval environment ∘ Term.var) = firsts :=
      (List.map_congr_left fun name _ => by simp [Model.eval]).trans leftValues
    have rightEval : (names.drop firsts.length).map (model.eval environment ∘ Term.var) = seconds :=
      (List.map_congr_left fun name _ => by simp [Model.eval]).trans rightValues
    rw [leftEval, rightEval]; exact same
  -- Distinct applications.
  · intro symbol other firsts seconds firstDeclared secondDeclared different
    have distinct : (Constructor.application symbol firsts.length : Constructor Literal Symbol) ≠
        Constructor.application other seconds.length := by
      intro same
      simp only [Constructor.application.injEq] at same
      exact different.elim (fun notSame => notSame same.1) (fun notLength => notLength same.2)
    exact clash_values holds firstDeclared secondDeclared distinct rfl rfl
  -- An application and a literal.
  · intro symbol firsts value appDeclared litDeclared
    exact clash_values (firsts := firsts) (seconds := []) holds appDeclared litDeclared (by simp) rfl rfl
  -- Distinct literals.
  · intro value other firstDeclared secondDeclared different
    exact clash_values (firsts := []) (seconds := []) holds firstDeclared secondDeclared (by simpa using different) rfl rfl

/-- A model of the completed program has what the abstract fixpoints need. -/
theorem Completes.of_models
    (models : model.Models (fun clause => clause ∈ (completion clauses signature).clauses : LogicalKb Variable Literal Symbol)) :
    Completes model signature clauses where
  program _ _ _ member environment :=
    models _ (show _ ∈ clauses ++ _ ++ _ from List.mem_append_left _ (List.mem_append_left _ member)) environment
  onlyIf key member environment :=
    models _ (show _ ∈ clauses ++ _ ++ _ from List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨key, member, rfl⟩)))
      environment
  free := free_of_equality fun _ member environment =>
    models _ (show _ ∈ clauses ++ _ ++ _ from List.mem_append_right _ member) environment

end Completion

/-! ## Enumerations -/

section Enumerations

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem mem_envsOver {choices : List (AValue Variable Literal Symbol)} :
    ∀ {names : List Variable} {env : AEnv Variable Literal Symbol}, env ∈ envsOver choices names → ∀ name ∈ names, env name ∈ choices
  | [], _, _, _, member => by cases member
  | first :: rest, env, inside, name, member => by
      simp only [envsOver, List.mem_flatMap, List.mem_map] at inside
      obtain ⟨previous, previousMember, choice, choiceMember, rfl⟩ := inside
      by_cases same : name = first
      · subst same; simpa [update] using choiceMember
      · simp only [update, same, ite_false]
        exact mem_envsOver previousMember name (by simpa [same] using member)

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem envsOver_complete {choices : List (AValue Variable Literal Symbol)} :
    ∀ (names : List Variable) (target : AEnv Variable Literal Symbol), (∀ name ∈ names, target name ∈ choices) →
      ∃ env ∈ envsOver choices names, ∀ name ∈ names, env name = target name
  | [], _, _ => ⟨fun _ => none, List.mem_singleton_self _, fun _ member => by cases member⟩
  | first :: rest, target, inChoices => by
      obtain ⟨env, member, agrees⟩ := envsOver_complete rest target fun name inside => inChoices name (List.mem_cons_of_mem _ inside)
      refine ⟨update env first (target first), ?_, fun name inside => ?_⟩
      · simp only [envsOver, List.mem_flatMap, List.mem_map]
        exact ⟨env, member, target first, inChoices first List.mem_cons_self, rfl⟩
      · by_cases same : name = first
        · subst same; simp [update]
        · simp only [update, same, ite_false]
          exact agrees name (by simpa [same] using inside)

theorem mem_tuples {α : Type} {choices : List α} :
    ∀ {items : List α}, (∀ item ∈ items, item ∈ choices) → items ∈ tuples choices items.length
  | [], _ => List.mem_singleton_self _
  | item :: rest, inside => by
      simp only [List.length_cons, tuples, List.mem_flatMap, List.mem_map]
      exact ⟨rest, mem_tuples fun other member => inside other (List.mem_cons_of_mem _ member), item,
        inside item List.mem_cons_self, rfl⟩

end Enumerations

/-! ## Every round of the completion is sound -/

section Rounds

variable [FreshNames Variable] {Value : Type} {hoApplySymbol : Symbol} {model : Model Literal Symbol Value hoApplySymbol}
  {signature : Signature Literal Symbol} {clauses : List (HornClause Variable Literal Symbol)}
  {space : List (Term Variable Literal Symbol)}

/-- An abstraction of a whole environment. -/
noncomputable def abstractEnv (model : Model Literal Symbol Value hoApplySymbol) (space : List (Term Variable Literal Symbol))
    (environment : Environment Variable Value) : AEnv Variable Literal Symbol :=
  fun name => Classical.choose (Abs.exists (model := model) (space := space) (environment name))

omit [FreshNames Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem abstractEnv_abs (environment : Environment Variable Value) (name : Variable) :
    Abs model space (environment name) (abstractEnv model space environment name) :=
  Classical.choose_spec (Abs.exists (model := model) (space := space) (environment name))

omit [FreshNames Variable] [DecidableEq Literal] [DecidableEq Symbol] in
/-- An enumerated environment abstracting `environment` on `names`. -/
theorem envsOver_abstracts (environment : Environment Variable Value) (names : List Variable) :
    ∃ env ∈ envsOver (values space) names, ∀ name ∈ names, Abs model space (environment name) (env name) := by
  obtain ⟨env, member, agrees⟩ := envsOver_complete (choices := values space) names (abstractEnv model space environment)
    fun name _ => (abstractEnv_abs environment name).mem_values
  exact ⟨env, member, fun name inside => agrees name inside ▸ abstractEnv_abs environment name⟩

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem freeVars_case_body {args body : List (Term Variable Literal Symbol)} {name : Variable}
    (occurs : name ∈ (Term.conjunction body).freeVars) : name ∈ caseNames args body := by
  obtain ⟨term, member, inside⟩ := mem_freeVars_conjunction occurs
  exact mem_caseNames (List.mem_append_right _ member) inside

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem freeVars_case_args {args body : List (Term Variable Literal Symbol)} {name : Variable}
    (occurs : name ∈ args.flatMap Term.freeVars) : name ∈ caseNames args body := by
  obtain ⟨term, member, inside⟩ := List.mem_flatMap.mp occurs
  exact mem_caseNames (List.mem_append_left _ member) inside

omit [FreshNames Variable] in
theorem mem_stepPossible {definitely : List (GAtom Variable Literal Symbol)} {possibly : List (AAtom Variable Literal Symbol)}
    {key : Symbol × Nat} {pair : List (Term Variable Literal Symbol) × List (Term Variable Literal Symbol)}
    {env : AEnv Variable Literal Symbol} (keyMember : key ∈ signature.predicates)
    (defining : pair ∈ definitions clauses key.1 key.2) (data : dataInAll signature.constructors pair.1 = true)
    (envMember : env ∈ envsOver (values space) (caseNames pair.1 pair.2))
    (bodyPossible : possible signature space definitely possibly env (.conjunction pair.2) = true) :
    (key.1, pair.1.map (aeval space env)) ∈ stepPossible signature space clauses definitely possibly := by
  unfold stepPossible
  refine List.mem_flatMap.mpr ⟨key, keyMember, List.mem_flatMap.mpr ⟨pair, defining, ?_⟩⟩
  simp only [data, ite_true]
  exact List.mem_filterMap.mpr ⟨env, envMember, by simp [bodyPossible]⟩

omit [FreshNames Variable] in
theorem mem_stepPossible_tuples {definitely : List (GAtom Variable Literal Symbol)} {possibly : List (AAtom Variable Literal Symbol)}
    {key : Symbol × Nat} {pair : List (Term Variable Literal Symbol) × List (Term Variable Literal Symbol)}
    (keyMember : key ∈ signature.predicates) (defining : pair ∈ definitions clauses key.1 key.2)
    (data : dataInAll signature.constructors pair.1 = false) {abstract : List (AValue Variable Literal Symbol)}
    (inTuples : abstract ∈ tuples (values space) key.2) :
    (key.1, abstract) ∈ stepPossible signature space clauses definitely possibly := by
  unfold stepPossible
  refine List.mem_flatMap.mpr ⟨key, keyMember, List.mem_flatMap.mpr ⟨pair, defining, ?_⟩⟩
  simp only [data]
  exact List.mem_map.mpr ⟨abstract, inTuples, rfl⟩

variable (completes : Completes model signature clauses) (valid : validUniverse signature.constructors space = true)
  (negation : model.ComplementNAF)
include completes valid negation

theorem stepPossible_sound {definitely : List (GAtom Variable Literal Symbol)} {possibly : List (AAtom Variable Literal Symbol)}
    (soundPossible : SoundPossible model space signature possibly) (soundDefinite : SoundDefinite model definitely) :
    SoundPossible model space signature (stepPossible signature space clauses definitely possibly) := by
  intro symbol args abstract closed holds along
  have onlyIfHolds := completes.onlyIf _ closed
  dsimp only at onlyIfHolds
  obtain ⟨heads, body, other, defining, argsEq, bodyHolds⟩ := onlyIf_case model (values := args) onlyIfHolds holds
  cases data : dataInAll signature.constructors heads with
  | true =>
      obtain ⟨env, envMember, abstracts⟩ := envsOver_abstracts (space := space) other (caseNames heads body)
      have bodyPossible := (body_sound valid completes.free negation soundPossible soundDefinite (.conjunction body) other env
        fun name occurs => abstracts name (freeVars_case_body occurs)).1 bodyHolds
      have headsAlong := aevals_abs valid completes.free heads data
        fun name occurs => abstracts name (freeVars_case_args occurs)
      rw [argsEq] at headsAlong
      obtain rfl : abstract = heads.map (aeval space env) :=
        Along.unique (relation := Abs model space) (fun _ _ _ left right => Abs.unique valid completes.free left right)
          along headsAlong
      exact mem_stepPossible (key := (symbol, args.length)) closed defining data envMember bodyPossible
  | false =>
      have lengths : abstract.length = args.length := along.length.symm
      exact mem_stepPossible_tuples (key := (symbol, args.length)) closed defining data (lengths ▸ mem_tuples fun item member => by
        obtain ⟨value, _, related⟩ := Along.mem along item member
        exact related.mem_values)

theorem stepDefinite_sound {definitely : List (GAtom Variable Literal Symbol)} {possibly : List (AAtom Variable Literal Symbol)}
    (soundPossible : SoundPossible model space signature possibly) (soundDefinite : SoundDefinite model definitely) :
    SoundDefinite model (stepDefinite signature space clauses definitely possibly) := by
  intro atom member
  simp only [stepDefinite, List.mem_flatMap, List.mem_filterMap] at member
  obtain ⟨key, _, ⟨heads, body⟩, defining, env, envMember, produced⟩ := member
  split at produced
  · rename_i bodyDefinite
    obtain ⟨found, computed, rfl⟩ := Option.map_eq_some_iff.mp produced
    let environment : Environment Variable Value := fun name =>
      match env name with
      | some term => den model term
      | none => model.inhabitant
    have abstracts : ∀ name ∈ caseNames heads body, Abs model space (environment name) (env name) := by
      intro name inside
      have choice := mem_envsOver envMember name inside
      obtain ⟨term, termMember, same⟩ := List.mem_map.mp choice
      simp only [environment, ← same]
      exact ⟨termMember, rfl⟩
    have holds := (body_sound valid completes.free negation soundPossible soundDefinite (.conjunction body) environment env
      fun name occurs => abstracts name (freeVars_case_body occurs)).2 bodyDefinite
    have clauseHolds := completes.program _ _ _ (definitions_mem defining).1 environment
    rw [sat_imp, sat_app] at clauseHolds
    have values := aevals_some heads found (fun name occurs => abstracts name (freeVars_case_args occurs)) computed
    rw [← values]
    exact clauseHolds holds
  · cases produced

/-- **Every Kripke–Kleene round is sound**: in a model of the completion, the
possibly-true atoms over-approximate its true atoms and the definitely-true
atoms are true. -/
theorem kk_sound : ∀ count : Nat,
    SoundPossible model space signature (kk signature space clauses count).2 ∧ SoundDefinite model (kk signature space clauses count).1
  | 0 => by
      refine ⟨fun symbol args abstract closed _ along => ?_, fun _ member => by cases member⟩
      simp only [kk, allAtoms, List.mem_flatMap, List.mem_map]
      refine ⟨_, closed, abstract, ?_, rfl⟩
      show abstract ∈ tuples (values space) args.length
      rw [along.length]
      exact mem_tuples fun item member => by
        obtain ⟨value, _, related⟩ := Along.mem along item member
        exact related.mem_values
  | count + 1 => by
      obtain ⟨soundPossible, soundDefinite⟩ := kk_sound count
      refine ⟨fun symbol args abstract closed holds along => ?_, fun atom member => ?_⟩
      · simp only [kk]
        exact List.mem_eraseDups.mpr (stepPossible_sound completes valid negation soundPossible soundDefinite symbol args abstract
          closed holds along)
      · simp only [kk] at member
        exact stepDefinite_sound completes valid negation soundPossible soundDefinite atom (List.mem_eraseDups.mp member)

/-- **A refuted goal is false in every model of the completion**, under every
environment. This is No, and the evidence of a NAF. -/
theorem refutes_sound {count : Nat} {goal : Term Variable Literal Symbol}
    (refuted : refutes signature space clauses count goal = true) (environment : Environment Variable Value) :
    ¬ model.Satisfies environment goal := by
  intro holds
  obtain ⟨soundPossible, soundDefinite⟩ := kk_sound completes valid negation count
  obtain ⟨env, envMember, abstracts⟩ := envsOver_abstracts (space := space) environment goal.freeVars.eraseDups
  have possible := (body_sound valid completes.free negation soundPossible soundDefinite goal environment env
    fun name occurs => abstracts name (List.mem_eraseDups.mpr occurs)).1 holds
  simp only [refutes, refutesWith, List.all_eq_true, Bool.not_eq_true'] at refuted
  rw [refuted env envMember] at possible
  cases possible

end Rounds



/-! ## Key models -/

section KeyModels

variable {hoApplySymbol : Symbol}

omit [DecidableEq Literal] in
theorem free_keys (interpretation : Interp Literal Symbol) (constructors : List (Constructor Literal Symbol)) :
    Free (Model.keys hoApplySymbol interpretation) constructors where
  injective _ _ _ _ _ same := by cases same; rfl
  apps symbol other firsts seconds _ _ different same := by
    change Key.app symbol firsts = Key.app other seconds at same
    simp only [Key.app.injEq] at same
    exact different.elim (fun notSame => notSame same.1) (fun notLength => notLength (by rw [same.2]))
  appLit _ _ _ _ _ same := by cases same
  lits _ _ _ _ different same := by cases same; exact different rfl

mutual
theorem den_keys (interpretation : Interp Literal Symbol) (constructors : List (Constructor Literal Symbol)) :
    ∀ term : Term Variable Literal Symbol, groundIn constructors term = true →
      den (Model.keys hoApplySymbol interpretation) term = Open.dataKey term
  | .lit _, _ => by rw [den_lit]; rfl
  | .app symbol args, ground => by
      simp only [groundIn, Bool.and_eq_true] at ground
      rw [den_app, Open.dataKey, Open.dataKeys_eq]
      exact congrArg (Key.app symbol) (dens_keys interpretation constructors args ground.2)
  | .var _, ground | .truth, ground | .falsity, ground | .conj _ _, ground | .disj _ _, ground | .imp _ _, ground
  | .defaultNeg _, ground | .forallVar _ _, ground | .existsVar _ _, ground | .dictionaryCall _ _ _ _, ground
  | .equal _ _, ground => by simp [groundIn] at ground

theorem dens_keys (interpretation : Interp Literal Symbol) (constructors : List (Constructor Literal Symbol)) :
    ∀ args : List (Term Variable Literal Symbol), groundInAll constructors args = true →
      args.map (den (Model.keys hoApplySymbol interpretation)) = args.map Open.dataKey
  | [], _ => rfl
  | arg :: rest, ground => by
      simp only [groundInAll, Bool.and_eq_true] at ground
      simp only [List.map_cons, den_keys interpretation constructors arg ground.1, dens_keys interpretation constructors rest ground.2]
end

/-- The abstraction of a key: the universe's term whose key it is, or ⋆. -/
def AbsKey (space : List (Term Variable Literal Symbol)) (key : Key Literal Symbol) : AValue Variable Literal Symbol → Prop
  | some term => term ∈ space ∧ Open.dataKey term = key
  | none => ∀ term ∈ space, Open.dataKey term ≠ key

theorem abs_keys_iff {constructors : List (Constructor Literal Symbol)} {space : List (Term Variable Literal Symbol)}
    (valid : validUniverse constructors space = true) (interpretation : Interp Literal Symbol) (key : Key Literal Symbol)
    (abstract : AValue Variable Literal Symbol) :
    Abs (Model.keys hoApplySymbol interpretation) space key abstract ↔ AbsKey space key abstract := by
  cases abstract with
  | some term =>
      show term ∈ space ∧ _ = key ↔ term ∈ space ∧ _ = key
      constructor
      · rintro ⟨member, same⟩; exact ⟨member, by rw [← same, den_keys interpretation constructors term (validUniverse_ground valid member)]⟩
      · rintro ⟨member, same⟩; exact ⟨member, by rw [den_keys interpretation constructors term (validUniverse_ground valid member), same]⟩
  | none =>
      show (∀ term ∈ space, _ ≠ key) ↔ (∀ term ∈ space, _ ≠ key)
      constructor
      · intro outside term member; rw [← den_keys interpretation constructors term (validUniverse_ground valid member)]
        exact outside term member
      · intro outside term member; rw [den_keys interpretation constructors term (validUniverse_ground valid member)]
        exact outside term member

theorem along_abs_keys {constructors : List (Constructor Literal Symbol)} {space : List (Term Variable Literal Symbol)}
    (valid : validUniverse constructors space = true) (interpretation : Interp Literal Symbol) :
    ∀ {keys : List (Key Literal Symbol)} {abstract : List (AValue Variable Literal Symbol)},
      Along (Abs (Model.keys hoApplySymbol interpretation) space) keys abstract ↔ Along (AbsKey space) keys abstract
  | [], [] => ⟨fun _ => .nil, fun _ => .nil⟩
  | [], _ :: _ => ⟨fun along => (by cases along), fun along => (by cases along)⟩
  | _ :: _, [] => ⟨fun along => (by cases along), fun along => (by cases along)⟩
  | key :: keys, abstract :: rest => by
      constructor
      · intro along; cases along with
        | cons here more => exact .cons ((abs_keys_iff valid interpretation key abstract).mp here) ((along_abs_keys valid interpretation).mp more)
      · intro along; cases along with
        | cons here more => exact .cons ((abs_keys_iff valid interpretation key abstract).mpr here) ((along_abs_keys valid interpretation).mpr more)

end KeyModels

/-! ## A goal false everywhere a set over-approximates -/

section NotPossible

variable [FreshNames Variable] {Value : Type} {hoApplySymbol : Symbol} {model : Model Literal Symbol Value hoApplySymbol}
  {signature : Signature Literal Symbol} {space : List (Term Variable Literal Symbol)}

omit [FreshNames Variable] in
/-- A goal not possibly true under any abstract value of its names is false in
every model the sets are sound for. -/
theorem notPossible_sound (valid : validUniverse signature.constructors space = true) (free : Free model signature.constructors)
    (negation : model.ComplementNAF) {definitely : List (GAtom Variable Literal Symbol)} {possibly : List (AAtom Variable Literal Symbol)}
    (soundPossible : SoundPossible model space signature possibly) (soundDefinite : SoundDefinite model definitely)
    {goal : Term Variable Literal Symbol}
    (refuted : (envsOver (values space) goal.freeVars.eraseDups).all (fun env => !possible signature space definitely possibly env goal) = true)
    (environment : Environment Variable Value) : ¬ model.Satisfies environment goal := by
  intro holds
  obtain ⟨env, envMember, abstracts⟩ := envsOver_abstracts (space := space) environment goal.freeVars.eraseDups
  have isPossible := (body_sound valid free negation soundPossible soundDefinite goal environment env
    fun name occurs => abstracts name (List.mem_eraseDups.mpr occurs)).1 holds
  simp only [List.all_eq_true, Bool.not_eq_true'] at refuted
  rw [refuted env envMember] at isPossible
  cases isPossible

end NotPossible

end AnthillModKbSpec.Tabled
