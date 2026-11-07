import AnthillModKbSpec.Foundation.Negation

namespace AnthillModKbSpec.Semantics

/-! # The constructor-key model (S22)

A model whose values are constructor trees and truth values, nothing else.
Equality is identity of values, so every constructor is free and injective,
and distinct literals and constructors denote distinct values: every clause of
a free equality theory holds (`Completion.equality`). An atom holds by a given
interpretation of the predicate at its argument values, `ho_apply` resolving
to the predicate it applies; NAF is complement.

`Model.herbrand` pairs keys with propositions, so a value with a data key may
carry any proposition, and an only-if clause `x = t ∨ … :- p(x)` can fail at
such a value. Here a data value is its key, and an only-if clause holds
exactly when the interpretation is supported by the clauses. S22 builds its
witness models from this model. -/

/-- Values: literals, constructor applications, and truth values. -/
inductive Key (Literal Symbol : Type) where
  | lit (value : Literal)
  | app (symbol : Symbol) (args : List (Key Literal Symbol))
  | truth (holds : Prop)

variable {Literal Symbol : Type} [DecidableEq Symbol]

/-- An application's truth: the interpretation, with `ho_apply` of a constant
resolved to the predicate it applies. Each resolution removes an argument. -/
def resolveKey (hoApplySymbol : Symbol) (interpretation : Symbol → List (Key Literal Symbol) → Prop)
    (symbol : Symbol) (args : List (Key Literal Symbol)) : Prop :=
  match args with
  | .app predicate [] :: rest =>
      if symbol = hoApplySymbol then resolveKey hoApplySymbol interpretation predicate rest
      else interpretation symbol args
  | _ => interpretation symbol args
termination_by args.length

theorem resolveKey_ordinary {hoApplySymbol : Symbol} (interpretation : Symbol → List (Key Literal Symbol) → Prop)
    {symbol : Symbol} (ordinary : symbol ≠ hoApplySymbol) (args : List (Key Literal Symbol)) :
    resolveKey hoApplySymbol interpretation symbol args ↔ interpretation symbol args := by
  cases args with
  | nil => simp [resolveKey]
  | cons first rest =>
      cases first with
      | lit value => simp [resolveKey]
      | truth holds => simp [resolveKey]
      | app predicate values => cases values <;> simp [resolveKey, ordinary]

/-- The truth of a value: a truth value's proposition, an application's
interpretation, and false for a literal. -/
def Key.holds (hoApplySymbol : Symbol) (interpretation : Symbol → List (Key Literal Symbol) → Prop) :
    Key Literal Symbol → Prop
  | .truth holds => holds
  | .app symbol args => resolveKey hoApplySymbol interpretation symbol args
  | .lit _ => False

/-- The constructor-key model of an interpretation. -/
def Model.keys (hoApplySymbol : Symbol) (interpretation : Symbol → List (Key Literal Symbol) → Prop) :
    Model Literal Symbol (Key Literal Symbol) hoApplySymbol where
  inhabitant := .truth False
  literal := .lit
  application := .app
  holds := Key.holds hoApplySymbol interpretation
  top := .truth True
  bottom := .truth False
  conjunction := fun a b => .truth (a.holds hoApplySymbol interpretation ∧ b.holds hoApplySymbol interpretation)
  disjunction := fun a b => .truth (a.holds hoApplySymbol interpretation ∨ b.holds hoApplySymbol interpretation)
  implication := fun a b => .truth (a.holds hoApplySymbol interpretation → b.holds hoApplySymbol interpretation)
  universal := fun f => .truth (∀ value, (f value).holds hoApplySymbol interpretation)
  existential := fun f => .truth (∃ value, (f value).holds hoApplySymbol interpretation)
  defaultNegation := fun value => .truth (¬ value.holds hoApplySymbol interpretation)
  equality := fun a b => .truth (a = b)
  holds_top := True.intro
  holds_bottom := id
  holds_conjunction := fun _ _ => Iff.rfl
  holds_disjunction := fun _ _ => Iff.rfl
  holds_implication := fun _ _ => Iff.rfl
  holds_universal := fun _ => Iff.rfl
  holds_existential := fun _ => Iff.rfl
  holds_equality := fun _ _ => Iff.rfl
  defaultNegation_coherent := fun _ no yes => no yes
  holds_hoApply := by
    intro predicate args
    show resolveKey hoApplySymbol interpretation hoApplySymbol (.app predicate [] :: args) ↔
      resolveKey hoApplySymbol interpretation predicate args
    rw [resolveKey]
    simp

variable {hoApplySymbol : Symbol} (interpretation : Symbol → List (Key Literal Symbol) → Prop)

theorem Model.keys_complement : (Model.keys hoApplySymbol interpretation).ComplementNAF := fun _ => Iff.rfl

/-- An ordinary atom holds exactly by the interpretation at its argument values. -/
theorem Model.keys_atom {Variable : Type} [DecidableEq Variable]
    (environment : Environment Variable (Key Literal Symbol)) {symbol : Symbol} (ordinary : symbol ≠ hoApplySymbol)
    (args : List (Term Variable Literal Symbol)) :
    (Model.keys hoApplySymbol interpretation).Satisfies environment (.app symbol args) ↔
      interpretation symbol (args.map ((Model.keys hoApplySymbol interpretation).eval environment)) := by
  simp only [Model.Satisfies, Model.eval]
  exact resolveKey_ordinary interpretation ordinary _

end AnthillModKbSpec.Semantics
