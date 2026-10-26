import AnthillModKbSpec.Foundation.Semantics

namespace AnthillModKbSpec.Semantics

/-- A concrete nonempty model witnessing consistency of atomic-headed definite
KBs in the positive calculus. All applications denote true; this deliberately
coarse model supplies no intended constructor semantics or closed-world policy. -/
def Model.trueAtoms (Literal Symbol : Type) (hoApplySymbol : Symbol) : Model Literal Symbol Bool hoApplySymbol where
  inhabitant := false
  literal := fun _ => true
  application := fun _ _ => true
  holds := fun value => value = true
  top := true
  bottom := false
  conjunction := Bool.and
  disjunction := Bool.or
  implication := fun a b => !a || b
  universal := fun f => f false && f true
  existential := fun f => f false || f true
  defaultNegation := Bool.not
  equality := fun a b => a == b
  holds_top := rfl
  holds_bottom := by decide
  holds_conjunction := by intro a b; cases a <;> cases b <;> decide
  holds_disjunction := by intro a b; cases a <;> cases b <;> decide
  holds_implication := by intro a b; cases a <;> cases b <;> decide
  holds_universal := by
    intro f
    simp only [Bool.and_eq_true]
    constructor
    · intro both value; cases value; exact both.1; exact both.2
    · intro all; exact ⟨all false, all true⟩
  holds_existential := by
    intro f
    simp only [Bool.or_eq_true]
    constructor
    · intro either
      rcases either with yes | yes
      · exact ⟨false, yes⟩
      · exact ⟨true, yes⟩
    · intro ⟨value, yes⟩; cases value; exact Or.inl yes; exact Or.inr yes
  defaultNegation_coherent := by intro value; cases value <;> decide
  holds_hoApply := by intros; rfl
  holds_equality := by intro a b; cases a <;> cases b <;> decide

variable {Variable Literal Symbol : Type} [DecidableEq Variable] {hoApplySymbol : Symbol}

/-- Every body is allowed: an always-true atomic head validates the implication. -/
theorem Model.trueAtoms_definite (environment : Environment Variable Bool) (symbol : Symbol)
    (args body : List (Term Variable Literal Symbol)) :
    (Model.trueAtoms Literal Symbol hoApplySymbol).Satisfies environment
      (HornClause.definite (.app symbol args) body).toFormula := by
  simp only [Model.Satisfies, HornClause.toFormula, Model.eval]
  apply ((Model.trueAtoms Literal Symbol hoApplySymbol).holds_implication _ _).mpr
  intro premise
  rfl

end AnthillModKbSpec.Semantics
