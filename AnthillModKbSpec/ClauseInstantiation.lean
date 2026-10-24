import AnthillModKbSpec.Opening

namespace AnthillModKbSpec

variable {Variable Literal Symbol : Type} [DecidableEq Variable]

/-- A partial executable substitution. It shadows binders correctly and refuses
capture; a caller needing alpha-renaming must choose a renamed clause first.
None is an unsupported instantiation, never logical failure of the goal. -/
def Term.instantiate? (σ : Substitution Variable Literal Symbol) :
    Term Variable Literal Symbol → Option (Term Variable Literal Symbol)
  | .var name => some (σ name)
  | .lit value => some (.lit value)
  | .truth => some .truth
  | .falsity => some .falsity
  | .app symbol args => (args.mapM (Term.instantiate? σ)).map (.app symbol)
  | .dictionaryCall dictionary path operation args =>
      (dictionary.instantiate? σ).bind (fun value =>
        (args.mapM (Term.instantiate? σ)).map (.dictionaryCall value path operation))
  | .conj a b => (a.instantiate? σ).bind (fun left => (b.instantiate? σ).map (.conj left))
  | .disj a b => (a.instantiate? σ).bind (fun left => (b.instantiate? σ).map (.disj left))
  | .imp a b => (a.instantiate? σ).bind (fun left => (b.instantiate? σ).map (.imp left))
  | .equal a b => (a.instantiate? σ).bind (fun left => (b.instantiate? σ).map (.equal left))
  | .defaultNeg body => (body.instantiate? σ).map .defaultNeg
  | .forallVar name body =>
      if body.freeVars.all (fun other => decide (other = name ∨ name ∉ (σ other).freeVars)) then
        (body.instantiate? (Substitution.bind σ name (.var name))).map (.forallVar name)
      else none
  | .existsVar name body =>
      if body.freeVars.all (fun other => decide (other = name ∨ name ∉ (σ other).freeVars)) then
        (body.instantiate? (Substitution.bind σ name (.var name))).map (.existsVar name)
      else none

theorem Term.instantiate?_sound (term : Term Variable Literal Symbol)
    {σ : Substitution Variable Literal Symbol} {result : Term Variable Literal Symbol}
    (computed : term.instantiate? σ = some result) : Substitutes σ term result := by
  refine Term.rec
    (motive_1 := fun term => ∀ σ result, term.instantiate? σ = some result → Substitutes σ term result)
    (motive_2 := fun terms => ∀ σ result, terms.mapM (Term.instantiate? σ) = some result → SubstitutesList σ terms result)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ term σ result computed
  · intro name σ result computed; simp only [Term.instantiate?, Option.some.injEq] at computed; subst result; exact .var
  · intro value σ result computed; simp only [Term.instantiate?, Option.some.injEq] at computed; subst result; exact .lit
  · intro symbol args ih σ result computed
    simp only [Term.instantiate?] at computed
    obtain ⟨mapped, success, rfl⟩ := Option.map_eq_some_iff.mp computed
    exact .app (ih σ mapped success)
  · intro σ result computed; simp only [Term.instantiate?, Option.some.injEq] at computed; subst result; exact .truth
  · intro σ result computed; simp only [Term.instantiate?, Option.some.injEq] at computed; subst result; exact .falsity
  · intro a b ihA ihB σ result computed
    simp only [Term.instantiate?] at computed
    obtain ⟨a', first, rest⟩ := Option.bind_eq_some_iff.mp computed
    obtain ⟨b', second, rfl⟩ := Option.map_eq_some_iff.mp rest
    exact .conj (ihA σ a' first) (ihB σ b' second)
  · intro a b ihA ihB σ result computed
    simp only [Term.instantiate?] at computed
    obtain ⟨a', first, rest⟩ := Option.bind_eq_some_iff.mp computed
    obtain ⟨b', second, rfl⟩ := Option.map_eq_some_iff.mp rest
    exact .disj (ihA σ a' first) (ihB σ b' second)
  · intro a b ihA ihB σ result computed
    simp only [Term.instantiate?] at computed
    obtain ⟨a', first, rest⟩ := Option.bind_eq_some_iff.mp computed
    obtain ⟨b', second, rfl⟩ := Option.map_eq_some_iff.mp rest
    exact .imp (ihA σ a' first) (ihB σ b' second)
  · intro body ih σ result computed
    simp only [Term.instantiate?] at computed
    obtain ⟨mapped, success, rfl⟩ := Option.map_eq_some_iff.mp computed
    exact .defaultNeg (ih σ mapped success)
  · intro name body ih σ result computed
    simp only [Term.instantiate?] at computed
    split at computed
    · rename_i safe
      obtain ⟨mapped, success, rfl⟩ := Option.map_eq_some_iff.mp computed
      apply Substitutes.forallVar (bodySubst := ih _ mapped success)
      intro other occurs different
      have condition := (List.all_eq_true.mp safe) other occurs
      simp only [decide_eq_true_eq] at condition
      exact condition.resolve_left different
    · cases computed
  · intro name body ih σ result computed
    simp only [Term.instantiate?] at computed
    split at computed
    · rename_i safe
      obtain ⟨mapped, success, rfl⟩ := Option.map_eq_some_iff.mp computed
      apply Substitutes.existsVar (bodySubst := ih _ mapped success)
      intro other occurs different
      have condition := (List.all_eq_true.mp safe) other occurs
      simp only [decide_eq_true_eq] at condition
      exact condition.resolve_left different
    · cases computed
  · intro dictionary path operation args ihDictionary ihArgs σ result computed
    simp only [Term.instantiate?] at computed
    obtain ⟨dictionary', first, rest⟩ := Option.bind_eq_some_iff.mp computed
    obtain ⟨args', second, rfl⟩ := Option.map_eq_some_iff.mp rest
    exact .dictionaryCall (ihDictionary σ dictionary' first) (ihArgs σ args' second)
  · intro a b ihA ihB σ result computed
    simp only [Term.instantiate?] at computed
    obtain ⟨a', first, rest⟩ := Option.bind_eq_some_iff.mp computed
    obtain ⟨b', second, rfl⟩ := Option.map_eq_some_iff.mp rest
    exact .equal (ihA σ a' first) (ihB σ b' second)
  · intro σ result computed; cases computed; exact .nil
  · intro head tail ihHead ihTail σ result computed
    rw [List.mapM_cons] at computed
    obtain ⟨head', first, rest⟩ := Option.bind_eq_some_iff.mp computed
    obtain ⟨tail', second, last⟩ := Option.bind_eq_some_iff.mp rest
    have same : head' :: tail' = result := Option.some.inj last
    subst result
    exact .cons (ihHead σ head' first) (ihTail σ tail' second)

end AnthillModKbSpec
