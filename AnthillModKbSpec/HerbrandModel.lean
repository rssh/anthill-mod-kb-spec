import AnthillModKbSpec.CompletedGround

namespace AnthillModKbSpec.Semantics

/-- Constructor keys distinguish data independently from the truth carried by
values. No quotient identifies distinct literal or constructor trees. -/
inductive DataKey (Literal Symbol : Type) where
  | lit (value : Literal)
  | app (symbol : Symbol) (args : List (DataKey Literal Symbol))

/-- Resolve concrete-symbol applications, including repeated explicit ho_apply.
Each resolution removes one argument, so even applying ho_apply to itself is
well founded. Unresolved predicate values remain ordinary interpretation keys. -/
def resolveAtom {Literal Symbol : Type} [DecidableEq Symbol] (hoApplySymbol : Symbol)
    (interpretation : Symbol → List (DataKey Literal Symbol) → Prop)
    (symbol : Symbol) (args : List (DataKey Literal Symbol)) : Prop :=
  match args with
  | .app predicate [] :: rest =>
      if symbol = hoApplySymbol then resolveAtom hoApplySymbol interpretation predicate rest
      else interpretation symbol args
  | _ => interpretation symbol args
termination_by args.length

variable {Literal Symbol : Type} [DecidableEq Symbol] {hoApplySymbol : Symbol}
variable (interpretation : Symbol → List (DataKey Literal Symbol) → Prop)

theorem resolveAtom_ordinary {symbol : Symbol} (ordinary : symbol ≠ hoApplySymbol)
    (args : List (DataKey Literal Symbol)) :
    resolveAtom hoApplySymbol interpretation symbol args ↔ interpretation symbol args := by
  cases args with
  | nil => simp [resolveAtom]
  | cons first rest =>
      cases first with
      | lit value => simp [resolveAtom]
      | app predicate values =>
          cases values <;> simp [resolveAtom, ordinary]

theorem resolveAtom_hoApply (predicate : Symbol) (args : List (DataKey Literal Symbol)) :
    resolveAtom hoApplySymbol interpretation hoApplySymbol (.app predicate [] :: args) ↔
      resolveAtom hoApplySymbol interpretation predicate args := by
  rw [resolveAtom]
  simp

/-- A compositional model built from a ground-atom interpretation. Values pair
constructor keys with propositions. Logical operators carry their ordinary
truth conditions; NAF is truth complement. Its domain also includes formula
values, as required by the raw shared syntax, not only constructor trees. -/
def Model.herbrand (hoApplySymbol : Symbol)
    (interpretation : Symbol → List (DataKey Literal Symbol) → Prop) :
    Model Literal Symbol (DataKey Literal Symbol × Prop) hoApplySymbol where
  inhabitant := ⟨.app hoApplySymbol [], False⟩
  literal := fun value => ⟨.lit value, False⟩
  application := fun symbol args =>
    ⟨.app symbol (args.map Prod.fst), resolveAtom hoApplySymbol interpretation symbol (args.map Prod.fst)⟩
  holds := Prod.snd
  top := ⟨.app hoApplySymbol [], True⟩
  bottom := ⟨.app hoApplySymbol [], False⟩
  conjunction := fun a b => ⟨.app hoApplySymbol [], a.2 ∧ b.2⟩
  disjunction := fun a b => ⟨.app hoApplySymbol [], a.2 ∨ b.2⟩
  implication := fun a b => ⟨.app hoApplySymbol [], a.2 → b.2⟩
  universal := fun f => ⟨.app hoApplySymbol [], ∀ value, (f value).2⟩
  existential := fun f => ⟨.app hoApplySymbol [], ∃ value, (f value).2⟩
  defaultNegation := fun value => ⟨.app hoApplySymbol [], ¬ value.2⟩
  equality := fun a b => ⟨.app hoApplySymbol [], a = b⟩
  holds_top := True.intro
  holds_bottom := id
  holds_conjunction := by intros; rfl
  holds_disjunction := by intros; rfl
  holds_implication := by intros; rfl
  holds_universal := by intros; rfl
  holds_existential := by intros; rfl
  defaultNegation_coherent := by intros value no yes; exact no yes
  holds_hoApply := by
    intro predicate args
    exact resolveAtom_hoApply interpretation predicate (args.map Prod.fst)
  holds_equality := fun _ _ => Iff.rfl

theorem Model.herbrand_complement :
    (Model.herbrand hoApplySymbol interpretation).ComplementNAF := by intro value; rfl

/-- Useful even without a groundness proof: an ordinary head reads exactly the
specified interpretation at the constructor keys of its argument values. -/
theorem Model.herbrand_atom {Variable : Type} [DecidableEq Variable]
    (environment : Environment Variable (DataKey Literal Symbol × Prop))
    {symbol : Symbol} (ordinary : symbol ≠ hoApplySymbol) (args : List (Term Variable Literal Symbol)) :
    (Model.herbrand hoApplySymbol interpretation).Satisfies environment (.app symbol args) ↔
      interpretation symbol ((args.map ((Model.herbrand hoApplySymbol interpretation).eval environment)).map Prod.fst) := by
  simp only [Model.Satisfies, Model.eval]
  exact resolveAtom_ordinary interpretation ordinary _

end AnthillModKbSpec.Semantics
