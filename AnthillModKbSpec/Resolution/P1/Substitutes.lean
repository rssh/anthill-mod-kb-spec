import AnthillModKbSpec.Resolution.Machine.Unification

/-! # Deciding capture-avoiding substitution (S08)

`Substitutes σ before after` is a relation: at a binder it lets `after` choose
the output binder, so a substitution has many results up to the names of
nested binders. A proof tree states the result it uses, so a checker needs to
decide the relation for a given `after`, not compute one result.
`substitutes` reads each output binder off `after`, checks that it captures no
substituted name, and recurses. It decides the relation exactly
(`substitutes_iff`). -/

namespace AnthillModKbSpec.P1

open Machine

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

attribute [local instance] termEq

/-- A binder renamed to `renamed` captures no name the substitution brings into
the body. -/
def keepsFree (σ : Substitution Variable Literal Symbol) (binder renamed : Variable)
    (body : Term Variable Literal Symbol) : Bool :=
  body.freeVars.all fun name => name == binder || !decide (renamed ∈ (σ name).freeVars)

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem keepsFree_iff {σ : Substitution Variable Literal Symbol} {binder renamed : Variable}
    {body : Term Variable Literal Symbol} :
    keepsFree σ binder renamed body = true ↔ ∀ name ∈ body.freeVars, name ≠ binder → renamed ∉ (σ name).freeVars := by
  simp only [keepsFree, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · intro holds name member different
    rcases holds name member with same | absent
    · exact absurd same different
    · exact absent
  · intro holds name member
    by_cases same : name = binder
    · exact .inl same
    · exact .inr (holds name member same)

mutual
/-- Decide `Substitutes σ before after`. -/
def substitutes : Substitution Variable Literal Symbol → Term Variable Literal Symbol → Term Variable Literal Symbol → Bool
  | σ, .var name, after => decide (σ name = after)
  | _, .lit value, .lit other => decide (value = other)
  | _, .truth, .truth => true
  | _, .falsity, .falsity => true
  | σ, .app symbol before, .app other after => decide (symbol = other) && substitutesList σ before after
  | σ, .conj a b, .conj c d => substitutes σ a c && substitutes σ b d
  | σ, .disj a b, .disj c d => substitutes σ a c && substitutes σ b d
  | σ, .imp a b, .imp c d => substitutes σ a c && substitutes σ b d
  | σ, .equal a b, .equal c d => substitutes σ a c && substitutes σ b d
  | σ, .defaultNeg before, .defaultNeg after => substitutes σ before after
  | σ, .forallVar binder body, .forallVar renamed result =>
      keepsFree σ binder renamed body && substitutes (Substitution.bind σ binder (.var renamed)) body result
  | σ, .existsVar binder body, .existsVar renamed result =>
      keepsFree σ binder renamed body && substitutes (Substitution.bind σ binder (.var renamed)) body result
  | σ, .dictionaryCall dictionary path operation before, .dictionaryCall dictionary' path' operation' after =>
      substitutes σ dictionary dictionary' && decide (path = path') && decide (operation = operation') &&
        substitutesList σ before after
  | _, _, _ => false

def substitutesList : Substitution Variable Literal Symbol → List (Term Variable Literal Symbol) →
    List (Term Variable Literal Symbol) → Bool
  | _, [], [] => true
  | σ, before :: befores, after :: afters => substitutes σ before after && substitutesList σ befores afters
  | _, _, _ => false
end

mutual
theorem substitutes_complete {σ : Substitution Variable Literal Symbol} {before after : Term Variable Literal Symbol} :
    Substitutes σ before after → substitutes σ before after = true
  | .var => by simp [substitutes]
  | .lit => by simp [substitutes]
  | .truth => by simp [substitutes]
  | .falsity => by simp [substitutes]
  | .app args => by simp [substitutes, substitutesList_complete args]
  | .conj left right => by simp [substitutes, substitutes_complete left, substitutes_complete right]
  | .disj left right => by simp [substitutes, substitutes_complete left, substitutes_complete right]
  | .imp left right => by simp [substitutes, substitutes_complete left, substitutes_complete right]
  | .equal left right => by simp [substitutes, substitutes_complete left, substitutes_complete right]
  | .defaultNeg body => by simp [substitutes, substitutes_complete body]
  | .forallVar fresh body => by simp [substitutes, keepsFree_iff.mpr fresh, substitutes_complete body]
  | .existsVar fresh body => by simp [substitutes, keepsFree_iff.mpr fresh, substitutes_complete body]
  | .dictionaryCall dictionary args => by
      simp [substitutes, substitutes_complete dictionary, substitutesList_complete args]

theorem substitutesList_complete {σ : Substitution Variable Literal Symbol}
    {befores afters : List (Term Variable Literal Symbol)} :
    SubstitutesList σ befores afters → substitutesList σ befores afters = true
  | .nil => rfl
  | .cons head tail => by simp [substitutesList, substitutes_complete head, substitutesList_complete tail]
end

theorem substitutes_sound (before : Term Variable Literal Symbol) :
    ∀ (σ : Substitution Variable Literal Symbol) after, substitutes σ before after = true → Substitutes σ before after := by
  refine Term.rec
    (motive_1 := fun before => ∀ (σ : Substitution Variable Literal Symbol) after,
      substitutes σ before after = true → Substitutes σ before after)
    (motive_2 := fun befores => ∀ (σ : Substitution Variable Literal Symbol) afters,
      substitutesList σ befores afters = true → SubstitutesList σ befores afters)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ before
  · intro name σ after checked
    simp only [substitutes, decide_eq_true_eq] at checked
    subst checked; exact .var
  · intro value σ after checked
    cases after <;> simp only [substitutes, decide_eq_true_eq, Bool.false_eq_true] at checked
    subst checked; exact .lit
  · intro symbol args ih σ after checked
    cases after <;> simp only [substitutes, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at checked
    obtain ⟨rfl, rest⟩ := checked
    exact .app (ih σ _ rest)
  · intro σ after checked
    cases after <;> simp only [substitutes, Bool.false_eq_true] at checked
    exact .truth
  · intro σ after checked
    cases after <;> simp only [substitutes, Bool.false_eq_true] at checked
    exact .falsity
  · intro a b ihA ihB σ after checked
    cases after <;> simp only [substitutes, Bool.and_eq_true, Bool.false_eq_true] at checked
    exact .conj (ihA σ _ checked.1) (ihB σ _ checked.2)
  · intro a b ihA ihB σ after checked
    cases after <;> simp only [substitutes, Bool.and_eq_true, Bool.false_eq_true] at checked
    exact .disj (ihA σ _ checked.1) (ihB σ _ checked.2)
  · intro a b ihA ihB σ after checked
    cases after <;> simp only [substitutes, Bool.and_eq_true, Bool.false_eq_true] at checked
    exact .imp (ihA σ _ checked.1) (ihB σ _ checked.2)
  · intro body ih σ after checked
    cases after <;> simp only [substitutes, Bool.false_eq_true] at checked
    exact .defaultNeg (ih σ _ checked)
  · intro binder body ih σ after checked
    cases after <;> simp only [substitutes, Bool.and_eq_true, Bool.false_eq_true] at checked
    exact .forallVar (keepsFree_iff.mp checked.1) (ih _ _ checked.2)
  · intro binder body ih σ after checked
    cases after <;> simp only [substitutes, Bool.and_eq_true, Bool.false_eq_true] at checked
    exact .existsVar (keepsFree_iff.mp checked.1) (ih _ _ checked.2)
  · intro dictionary path operation args ihD ihArgs σ after checked
    cases after <;> simp only [substitutes, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at checked
    obtain ⟨⟨⟨dictionaryOk, rfl⟩, rfl⟩, argsOk⟩ := checked
    exact .dictionaryCall (ihD σ _ dictionaryOk) (ihArgs σ _ argsOk)
  · intro a b ihA ihB σ after checked
    cases after <;> simp only [substitutes, Bool.and_eq_true, Bool.false_eq_true] at checked
    exact .equal (ihA σ _ checked.1) (ihB σ _ checked.2)
  · intro σ afters checked
    cases afters <;> simp only [substitutesList, Bool.false_eq_true] at checked
    exact .nil
  · intro head tail ihHead ihTail σ afters checked
    cases afters <;> simp only [substitutesList, Bool.and_eq_true, Bool.false_eq_true] at checked
    exact .cons (ihHead σ _ checked.1) (ihTail σ _ checked.2)

/-- `substitutes` decides capture-avoiding substitution with a stated result. -/
theorem substitutes_iff {σ : Substitution Variable Literal Symbol} {before after : Term Variable Literal Symbol} :
    substitutes σ before after = true ↔ Substitutes σ before after :=
  ⟨substitutes_sound before σ after, substitutes_complete⟩

end AnthillModKbSpec.P1
