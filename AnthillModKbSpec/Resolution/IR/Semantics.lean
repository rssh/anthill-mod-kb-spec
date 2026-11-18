import AnthillModKbSpec.Resolution.IR.Check
import AnthillModKbSpec.Resolution.Tabled.AbstractSound

/-! # The IR's semantics: key fixpoints (S27)

An IR program means its rendering's Clark completion (`Program.completion`).
The answers are about the models of the completion with complement NAF that
**realize** the program's guards and primitives (`Program.Realizes`): a guard
holds exactly of the values of the ground data terms it decides, and a
primitive's atom exactly at an evaluation of its evaluator. `Program.meaning`
is S22's `Meaning.ofModels` over that class.

Over constructor keys, S24's consequence operator (`Tabled.consequence`) reads
the closed atoms from an interpretation and every other atom from a base,
here `Program.base`: guards exact, by the constructors of their argument;
primitives by their evaluators; markers free, from any interpretation. A
**key fixpoint** (`Program.KeyFixpoint`) is a fixpoint of the operator whose
denials are false. They are exactly the completion's models over keys
(`keyModel_models_iff`, S24's `fixpoint_iff_models` on the rendering, which
is covered: `Program.covered`), and every one is a model the answers are about
(`keyFixpoint_models`). The converse direction, from any model to a key
fixpoint with the same truths, is the Herbrand reduction (`IR/Herbrand`). -/

namespace AnthillModKbSpec.IR

open Semantics Completion Tabled Answers

variable {Variable Literal Symbol : Type}

/-! ## Data terms under substitutions -/

section Substitution

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

mutual
/-- A data term over declared constructors, its names replaced by ground data
terms over them, is a ground data term over them. -/
theorem groundIn_subst {constructors : List (Constructor Literal Symbol)} {σ : Variable → Term Variable Literal Symbol} :
    ∀ term : Term Variable Literal Symbol, dataIn constructors term = true →
      (∀ name ∈ term.freeVars, groundIn constructors (σ name) = true) → groundIn constructors (subst σ term) = true
  | .var name, _, ground => ground name (by simp [Term.freeVars])
  | .lit _, data, _ => by simpa [subst, dataIn, groundIn] using data
  | .app symbol args, data, ground => by
      simp only [dataIn, Bool.and_eq_true] at data
      simp only [subst, groundIn, Bool.and_eq_true]
      refine ⟨by rw [substAll_eq, List.length_map]; exact data.1, groundInAll_subst args data.2 fun name occurs => ?_⟩
      exact ground name (by simpa [Term.freeVars] using occurs)
  | .truth, data, _ | .falsity, data, _ | .conj _ _, data, _ | .disj _ _, data, _ | .imp _ _, data, _
  | .defaultNeg _, data, _ | .forallVar _ _, data, _ | .existsVar _ _, data, _ | .dictionaryCall _ _ _ _, data, _
  | .equal _ _, data, _ => by simp [dataIn] at data

theorem groundInAll_subst {constructors : List (Constructor Literal Symbol)} {σ : Variable → Term Variable Literal Symbol} :
    ∀ args : List (Term Variable Literal Symbol), dataInAll constructors args = true →
      (∀ name ∈ args.flatMap Term.freeVars, groundIn constructors (σ name) = true) →
        groundInAll constructors (substAll σ args) = true
  | [], _, _ => rfl
  | arg :: rest, data, ground => by
      simp only [dataInAll, Bool.and_eq_true] at data
      simp only [substAll, groundInAll, Bool.and_eq_true]
      exact ⟨groundIn_subst arg data.1 fun name occurs => ground name (by simp [occurs]),
        groundInAll_subst rest data.2 fun name occurs => ground name (by simp only [List.flatMap_cons, List.mem_append]; exact .inr occurs)⟩
end

variable {Value : Type} {hoApplySymbol : Symbol}

mutual
/-- In any model, a data term evaluated where each name has a ground term's
value is the value of the substituted term. -/
theorem eval_subst (model : Model Literal Symbol Value hoApplySymbol) (σ : Variable → Term Variable Literal Symbol) :
    ∀ term : Term Variable Literal Symbol, dataIn constructors term = true →
      model.eval (fun name => den model (σ name)) term = den model (subst σ term)
  | .var _, _ => by simp [subst, Model.eval]
  | .lit _, _ => by simp [subst, den, Model.eval]
  | .app symbol args, data => by
      simp only [dataIn, Bool.and_eq_true] at data
      simp only [subst, Model.eval, den_app]
      rw [substAll_eq, List.map_map]
      congr 1
      have each := evalAll_subst model σ args data.2
      rw [each]
  | .truth, data | .falsity, data | .conj _ _, data | .disj _ _, data | .imp _ _, data | .defaultNeg _, data
  | .forallVar _ _, data | .existsVar _ _, data | .dictionaryCall _ _ _ _, data | .equal _ _, data => by
      simp [dataIn] at data

theorem evalAll_subst (model : Model Literal Symbol Value hoApplySymbol) (σ : Variable → Term Variable Literal Symbol) :
    ∀ args : List (Term Variable Literal Symbol), dataInAll constructors args = true →
      args.map (model.eval fun name => den model (σ name)) = args.map (den model ∘ subst σ)
  | [], _ => rfl
  | arg :: rest, data => by
      simp only [dataInAll, Bool.and_eq_true] at data
      simp only [List.map_cons, Function.comp, eval_subst model σ arg data.1]
      exact congrArg _ (evalAll_subst model σ rest data.2)
end

mutual
/-- In a constructor-key model, a data term evaluated where each name is a
ground term's key is the key of the substituted term. -/
theorem keys_eval_subst (interpretation : Interp Literal Symbol) (σ : Variable → Term Variable Literal Symbol) :
    ∀ term : Term Variable Literal Symbol, dataIn constructors term = true →
      (Model.keys hoApplySymbol interpretation).eval (fun name => Open.dataKey (σ name)) term = Open.dataKey (subst σ term)
  | .var _, _ => by simp [subst, Model.eval]
  | .lit _, _ => by simp only [subst, Model.eval, Open.dataKey]; rfl
  | .app symbol args, data => by
      simp only [dataIn, Bool.and_eq_true] at data
      simp only [subst, Model.eval, Open.dataKey]
      rw [Open.dataKeys_eq, substAll_eq]
      change Key.app symbol _ = Key.app symbol _
      congr 1
      rw [keys_evalAll_subst interpretation σ args data.2, List.map_map]
  | .truth, data | .falsity, data | .conj _ _, data | .disj _ _, data | .imp _ _, data | .defaultNeg _, data
  | .forallVar _ _, data | .existsVar _ _, data | .dictionaryCall _ _ _ _, data | .equal _ _, data => by
      simp [dataIn] at data

theorem keys_evalAll_subst (interpretation : Interp Literal Symbol) (σ : Variable → Term Variable Literal Symbol) :
    ∀ args : List (Term Variable Literal Symbol), dataInAll constructors args = true →
      args.map ((Model.keys hoApplySymbol interpretation).eval fun name => Open.dataKey (σ name)) =
        args.map (Open.dataKey ∘ subst σ)
  | [], _ => rfl
  | arg :: rest, data => by
      simp only [dataInAll, Bool.and_eq_true] at data
      simp only [List.map_cons, Function.comp, keys_eval_subst interpretation σ arg data.1]
      exact congrArg _ (keys_evalAll_subst interpretation σ rest data.2)
end

/-- In a constructor-key model, a ground term's value is its key. -/
theorem den_keys_eq {constructors : List (Constructor Literal Symbol)} (interpretation : Interp Literal Symbol)
    {term : Term Variable Literal Symbol} (ground : groundIn constructors term = true) :
    den (Model.keys hoApplySymbol interpretation) term = Open.dataKey term :=
  den_keys interpretation constructors term ground

/-- Keys of ground data terms are the terms' own: distinct terms, distinct keys. -/
theorem dataKey_injective (hoApplySymbol : Symbol) {constructors : List (Constructor Literal Symbol)}
    {term other : Term Variable Literal Symbol}
    (ground : groundIn constructors term = true) (otherGround : groundIn constructors other = true)
    (same : Open.dataKey term = Open.dataKey other) : term = other := by
  apply den_injective (free_keys (hoApplySymbol := hoApplySymbol) (fun _ _ => False) constructors) term other ground otherGround
  rw [den_keys_eq (hoApplySymbol := hoApplySymbol) _ ground, den_keys_eq (hoApplySymbol := hoApplySymbol) _ otherGround, same]

end Substitution

/-! ## The models an IR program's answers are about -/

namespace Program

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable]
  (program : Program Variable Literal Symbol)

/-- A declared symbol of a kind. -/
def HasKind (symbol : Symbol) (kind : Kind) : Prop :=
  ∃ declared, program.predicate? symbol = some declared ∧ declared.kind = kind

/-- A model realizes the program's guards and primitives: a guard holds
exactly of the values of the ground data terms it holds of (a finite guard of
its listed members, `guardHolds`), and a primitive
holds exactly at its evaluator's evaluations, its output last. -/
structure Realizes {Value : Type} (model : Model Literal Symbol Value program.hoApply) : Prop where
  guards : ∀ symbol, program.HasKind symbol .guard → ∀ value,
    model.holds (model.application symbol [value]) ↔
      ∃ term, groundIn program.constructors term = true ∧ program.guardHolds symbol term = true ∧ den model term = value
  primitives : ∀ symbol, program.HasKind symbol .primitive → ∀ values,
    model.holds (model.application symbol values) ↔
      ∃ inputs output, (∀ input ∈ inputs, groundIn program.constructors input = true) ∧
        groundIn program.constructors output = true ∧ program.evaluate symbol inputs = some output ∧
          values = (inputs ++ [output]).map (den model)

/-- The models the answers are about: of the completion, with complement NAF,
realizing the guards and primitives. -/
def Models {Value : Type} (model : Model Literal Symbol Value program.hoApply) : Prop :=
  model.Models (fun clause => clause ∈ program.completion.clauses) ∧ model.ComplementNAF ∧ program.Realizes model

/-- What a query's answers claim (S22): the goals, their answer names
existentially closed, hold in every such model under every environment
satisfying the conditions (Yes), fail in each (No), or hold in one and fail in
another (Unknown). -/
def meaning (query : Query Variable Literal Symbol) : Meaning :=
  Meaning.ofModels (fun _ model => program.Models model) query.context query.formula

/-! ## Key fixpoints -/

/-- The atoms the closed predicates do not give: a guard holds exactly of the
keys of the ground data terms it decides; a primitive exactly at its
evaluations; every other atom, a marker's, by `markers`. -/
def base (markers : Interp Literal Symbol) : Interp Literal Symbol := fun symbol keys =>
  match program.predicate? symbol with
  | some declared =>
      match declared.kind with
      | .guard => ∃ term, groundIn program.constructors term = true ∧ program.guardHolds symbol term = true ∧
          keys = [Open.dataKey term]
      | .primitive => ∃ inputs output, (∀ input ∈ inputs, groundIn program.constructors input = true) ∧
          groundIn program.constructors output = true ∧ program.evaluate symbol inputs = some output ∧
            keys = (inputs ++ [output]).map Open.dataKey
      | _ => markers symbol keys
  | none => markers symbol keys

/-- The constructor-key model of an interpretation of the closed atoms, the
markers read from `markers`. -/
abbrev keyModel (markers interp : Interp Literal Symbol) : Model Literal Symbol (Key Literal Symbol) program.hoApply :=
  Tabled.keyModel program.hoApply program.signature (program.base markers) interp

/-- A key fixpoint: a fixpoint of the consequence operator on the closed
atoms, the base giving the rest, with every denial's body false. -/
def KeyFixpoint (markers interp : Interp Literal Symbol) : Prop :=
  Fixpoint program.hoApply program.signature program.clauses (program.base markers) interp ∧
    Denied program.hoApply program.signature program.clauses (program.base markers) interp

/-! ## Declarations -/

variable {program}

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem predicate?_mem {symbol : Symbol} {declared : Predicate Symbol} (found : program.predicate? symbol = some declared) :
    declared ∈ program.predicates ∧ declared.symbol = symbol := by
  unfold predicate? at found
  exact ⟨List.mem_of_find?_eq_some found, by simpa using List.find?_some found⟩

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
/-- Declared once, a symbol has one declaration. -/
theorem declaration_unique (unique : (program.predicates.map (·.symbol)).Nodup) {first second : Predicate Symbol}
    (firstMember : first ∈ program.predicates) (secondMember : second ∈ program.predicates)
    (same : first.symbol = second.symbol) : first = second :=
  Machine.nodup_map_inj unique firstMember secondMember same

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
/-- A symbol declared with a kind the completion does not close is closed at
no arity. -/
theorem not_closed_of_kind (unique : (program.predicates.map (·.symbol)).Nodup) {symbol : Symbol}
    {declared : Predicate Symbol} (found : program.predicate? symbol = some declared) (open_ : declared.closed = false)
    (arity : Nat) : (symbol, arity) ∉ program.signature.predicates := by
  intro member
  obtain ⟨other, otherMember, closed, same⟩ := mem_closedKeys.mp member
  obtain ⟨declaredMember, declaredSymbol⟩ := predicate?_mem found
  simp only [Prod.mk.injEq] at same
  have equal := declaration_unique unique declaredMember otherMember (declaredSymbol.trans same.1)
  rw [equal] at open_
  rw [open_] at closed
  cases closed

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
/-- An undeclared symbol is closed at no arity. -/
theorem not_closed_of_none {symbol : Symbol} (found : program.predicate? symbol = none) (arity : Nat) :
    (symbol, arity) ∉ program.signature.predicates := by
  intro member
  obtain ⟨other, otherMember, _, same⟩ := mem_closedKeys.mp member
  simp only [Prod.mk.injEq] at same
  unfold predicate? at found
  exact absurd (List.find?_eq_none.mp found other otherMember) (by simp [same.1])

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
/-- A predicate closed at an arity is closed by the signature. -/
theorem closedAt_mem {symbol : Symbol} {arity : Nat} (closed : program.closedAt symbol arity = true) :
    (symbol, arity) ∈ program.signature.predicates := by
  unfold closedAt at closed
  split at closed
  · rename_i declared found
    simp only [Bool.and_eq_true, beq_iff_eq] at closed
    obtain ⟨member, same⟩ := predicate?_mem found
    exact mem_closedKeys.mpr ⟨declared, member, closed.1, by rw [same, closed.2]⟩
  · cases closed

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem closedAt_declared {symbol : Symbol} {arity : Nat} (closed : program.closedAt symbol arity = true) :
    ∃ declared, program.predicate? symbol = some declared ∧ declared.closed = true ∧ declared.arity = arity := by
  unfold closedAt at closed
  split at closed
  · rename_i declared found
    simp only [Bool.and_eq_true, beq_iff_eq] at closed
    exact ⟨declared, found, closed.1, closed.2⟩
  · cases closed

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem kindAt_declared {kind : Kind} {symbol : Symbol} {arity : Nat} (declared : program.kindAt kind symbol arity = true) :
    ∃ found, program.predicate? symbol = some found ∧ found.kind = kind ∧ found.arity = arity := by
  unfold kindAt at declared
  split at declared
  · rename_i found same
    simp only [Bool.and_eq_true, beq_iff_eq] at declared
    exact ⟨found, same, declared.1, declared.2⟩
  · cases declared

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
/-- A symbol declared by the program is not the reserved `ho_apply`. -/
theorem ordinary_of_declared (reserved : ∀ predicate ∈ program.predicates, predicate.symbol ≠ program.hoApply)
    {symbol : Symbol} {declared : Predicate Symbol} (found : program.predicate? symbol = some declared) :
    symbol ≠ program.hoApply := by
  obtain ⟨member, same⟩ := predicate?_mem found
  rw [← same]; exact reserved declared member

/-! ## Key fixpoints are the completion's models -/

omit [FreshNames Variable] in
/-- The rendering is covered (S24): definite clauses with an atomic head of a
closed predicate, and denials; no closed predicate is `ho_apply`. -/
theorem covered (wellFormed : program.WellFormed) : Covered program.hoApply program.signature program.clauses where
  shape := by
    intro clause member
    rcases List.mem_append.mp member with inRules | inDenials
    · obtain ⟨rule, ruleMember, rfl⟩ := List.mem_map.mp inRules
      exact .inl ⟨rule.head, rule.args, rule.body.map Goal.toTerm, rfl, closedAt_mem (wellFormed.rules rule ruleMember).closed⟩
    · obtain ⟨body, _, rfl⟩ := List.mem_map.mp inDenials
      exact .inr ⟨_, rfl⟩
  ordinary := by
    intro key member
    obtain ⟨predicate, predicateMember, _, rfl⟩ := mem_closedKeys.mp member
    exact wellFormed.reserved predicate predicateMember

/-- **Key fixpoints are the completion's models over keys** (S24's
`fixpoint_iff_models` on the rendering). -/
theorem keyModel_models_iff (wellFormed : program.WellFormed) {markers interp : Interp Literal Symbol} :
    (program.keyModel markers interp).Models (fun clause => clause ∈ program.completion.clauses) ↔
      program.KeyFixpoint markers interp :=
  fixpoint_iff_models (program.covered wellFormed)

omit [FreshNames Variable] in
/-- A key model's guard and primitive atoms are the base's. -/
theorem keyModel_base (wellFormed : program.WellFormed) {markers interp : Interp Literal Symbol} {symbol : Symbol}
    {declared : Predicate Symbol} (found : program.predicate? symbol = some declared) (open_ : declared.closed = false)
    (keys : List (Key Literal Symbol)) :
    (program.keyModel markers interp).holds ((program.keyModel markers interp).application symbol keys) ↔
      program.base markers symbol keys := by
  show resolveKey program.hoApply _ symbol keys ↔ _
  rw [resolveKey_ordinary _ (ordinary_of_declared wellFormed.reserved found)]
  exact join_open (not_closed_of_kind wellFormed.unique found open_ keys.length)

/-- Every key fixpoint is a model the answers are about: of the completion,
with complement NAF, realizing the guards and primitives. -/
theorem keyFixpoint_models (wellFormed : program.WellFormed) {markers interp : Interp Literal Symbol}
    (fixed : program.KeyFixpoint markers interp) : program.Models (program.keyModel markers interp) := by
  refine ⟨(program.keyModel_models_iff wellFormed).mpr fixed, Model.keys_complement _, ⟨?_, ?_⟩⟩
  · rintro symbol ⟨declared, found, kind⟩ value
    rw [program.keyModel_base wellFormed found (by simp [Predicate.closed, kind]) [value]]
    simp only [base, found, kind]
    constructor
    · rintro ⟨term, ground, decided, same⟩
      exact ⟨term, ground, decided, by rw [den_keys_eq (constructors := program.constructors) _ ground]; simpa using same.symm⟩
    · rintro ⟨term, ground, decided, same⟩
      exact ⟨term, ground, decided, by rw [← same, den_keys_eq (constructors := program.constructors) _ ground]⟩
  · rintro symbol ⟨declared, found, kind⟩ values
    rw [program.keyModel_base wellFormed found (by simp [Predicate.closed, kind]) values]
    simp only [base, found, kind]
    have keysOf : ∀ (inputs : List (Term Variable Literal Symbol)) (output : Term Variable Literal Symbol),
        (∀ input ∈ inputs, groundIn program.constructors input = true) → groundIn program.constructors output = true →
          (inputs ++ [output]).map (den (program.keyModel markers interp)) = (inputs ++ [output]).map Open.dataKey := by
      intro inputs output inputsGround outputGround
      refine List.map_congr_left fun term member => den_keys_eq (constructors := program.constructors) _ ?_
      rcases List.mem_append.mp member with inside | inside
      · exact inputsGround term inside
      · rcases List.mem_singleton.mp inside with rfl; exact outputGround
    constructor
    · rintro ⟨inputs, output, inputsGround, outputGround, evaluated, same⟩
      exact ⟨inputs, output, inputsGround, outputGround, evaluated, by rw [keysOf inputs output inputsGround outputGround]; exact same⟩
    · rintro ⟨inputs, output, inputsGround, outputGround, evaluated, same⟩
      exact ⟨inputs, output, inputsGround, outputGround, evaluated, by rw [same, keysOf inputs output inputsGround outputGround]⟩

end Program

end AnthillModKbSpec.IR
