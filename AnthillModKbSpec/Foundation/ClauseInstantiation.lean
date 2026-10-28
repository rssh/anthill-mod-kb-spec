import AnthillModKbSpec.Foundation.Opening

namespace AnthillModKbSpec

variable {Variable Literal Symbol : Type} [DecidableEq Variable]

/-- Substituting under a binder may keep it: the binder captures no substituted
free name of the body. -/
abbrev Substitution.keeps (σ : Substitution Variable Literal Symbol) (name : Variable)
    (body : Term Variable Literal Symbol) : Bool :=
  body.freeVars.all (fun other => decide (other = name ∨ name ∉ (σ other).freeVars))

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
      if σ.keeps name body then
        (body.instantiate? (Substitution.bind σ name (.var name))).map (.forallVar name)
      else none
  | .existsVar name body =>
      if σ.keeps name body then
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

/-! ## Instantiation with alpha-renaming

`instantiate?` refuses a capture hazard. `instantiate` renames the binder
instead, so every substitution has an instance: a capture hazard is never a
logical failure. It keeps each binder whenever `instantiate?` would, and then
both compute the same instance. -/

section Renaming

variable [FreshNames Variable]

/-- The binder used when substituting under `name`: `name` itself unless it
would capture a substituted free name of the body, otherwise a name fresh for
every such value. Only the values at the quantifier's free names are read. -/
def Substitution.binder (σ : Substitution Variable Literal Symbol) (name : Variable)
    (body : Term Variable Literal Symbol) : Variable :=
  if σ.keeps name body then name
  else FreshNames.fresh (body.freeVars.flatMap (fun other => if other = name then [] else (σ other).freeVars))

/-- Total capture-avoiding substitution, renaming a binder only on a hazard. -/
def Term.instantiate (σ : Substitution Variable Literal Symbol) :
    Term Variable Literal Symbol → Term Variable Literal Symbol
  | .var name => σ name
  | .lit value => .lit value
  | .truth => .truth
  | .falsity => .falsity
  | .app symbol args => .app symbol (args.map (Term.instantiate σ))
  | .dictionaryCall dictionary path operation args =>
      .dictionaryCall (dictionary.instantiate σ) path operation (args.map (Term.instantiate σ))
  | .conj a b => .conj (a.instantiate σ) (b.instantiate σ)
  | .disj a b => .disj (a.instantiate σ) (b.instantiate σ)
  | .imp a b => .imp (a.instantiate σ) (b.instantiate σ)
  | .equal a b => .equal (a.instantiate σ) (b.instantiate σ)
  | .defaultNeg body => .defaultNeg (body.instantiate σ)
  | .forallVar name body =>
      let renamed := σ.binder name body
      .forallVar renamed (body.instantiate (Substitution.bind σ name (.var renamed)))
  | .existsVar name body =>
      let renamed := σ.binder name body
      .existsVar renamed (body.instantiate (Substitution.bind σ name (.var renamed)))

theorem Substitution.binder_fresh (σ : Substitution Variable Literal Symbol) (name : Variable)
    (body : Term Variable Literal Symbol) :
    ∀ other ∈ body.freeVars, other ≠ name → σ.binder name body ∉ (σ other).freeVars := by
  intro other member different
  unfold Substitution.binder
  split
  · rename_i safe
    have condition := (List.all_eq_true.mp safe) other member
    simp only [decide_eq_true_eq] at condition
    exact condition.resolve_left different
  · intro occurs
    apply FreshNames.fresh_not_mem
      (body.freeVars.flatMap (fun other => if other = name then [] else (σ other).freeVars))
    exact List.mem_flatMap.mpr ⟨other, member, by simpa only [different, ite_false] using occurs⟩

private theorem all_congr {α : Type} {items : List α} {p q : α → Bool}
    (agree : ∀ item ∈ items, p item = q item) : items.all p = items.all q := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.all_cons, agree item List.mem_cons_self,
        ih (fun other member => agree other (List.mem_cons_of_mem _ member))]

private theorem flatMap_congr {α β : Type} {items : List α} {f g : α → List β}
    (agree : ∀ item ∈ items, f item = g item) : items.flatMap f = items.flatMap g := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.flatMap_cons, agree item List.mem_cons_self,
        ih (fun other member => agree other (List.mem_cons_of_mem _ member))]

theorem Substitution.binder_congr {σ τ : Substitution Variable Literal Symbol} {name : Variable}
    {body : Term Variable Literal Symbol}
    (agree : ∀ other ∈ body.freeVars, other ≠ name → σ other = τ other) :
    σ.binder name body = τ.binder name body := by
  have safe := all_congr (items := body.freeVars)
    (p := fun other => decide (other = name ∨ name ∉ (σ other).freeVars))
    (q := fun other => decide (other = name ∨ name ∉ (τ other).freeVars)) (fun other member => by
      by_cases same : other = name
      · simp [same]
      · rw [agree other member same])
  have avoid := flatMap_congr (items := body.freeVars)
    (f := fun other => if other = name then [] else (σ other).freeVars)
    (g := fun other => if other = name then [] else (τ other).freeVars) (fun other member => by
      by_cases same : other = name
      · simp [same]
      · simp only [same, ite_false, agree other member same])
  simp only [Substitution.binder, Substitution.keeps, safe, avoid]

/-- The computed instance is a capture-avoiding instance. -/
theorem Term.instantiate_substitutes (term : Term Variable Literal Symbol) :
    ∀ σ, Substitutes σ term (term.instantiate σ) := by
  refine Term.rec
    (motive_1 := fun term => ∀ σ, Substitutes σ term (term.instantiate σ))
    (motive_2 := fun terms => ∀ σ, SubstitutesList σ terms (terms.map (Term.instantiate σ)))
    ?var ?lit ?app ?truth ?falsity ?conj ?disj ?imp ?defaultNeg ?forallVar ?existsVar ?dictionaryCall ?equal ?nil ?cons term
  case forallVar | existsVar =>
    intro name body ih σ
    simp only [Term.instantiate]
    constructor
    · exact Substitution.binder_fresh σ name body
    · exact ih _
  all_goals intros; simp only [Term.instantiate, List.map]; constructor <;> simp_all

/-- Only the values at the term's free names matter. -/
theorem Term.instantiate_congr (term : Term Variable Literal Symbol) :
    ∀ σ τ : Substitution Variable Literal Symbol, (∀ name ∈ term.freeVars, σ name = τ name) →
      term.instantiate σ = term.instantiate τ := by
  refine Term.rec
    (motive_1 := fun term => ∀ σ τ : Substitution Variable Literal Symbol,
      (∀ name ∈ term.freeVars, σ name = τ name) → term.instantiate σ = term.instantiate τ)
    (motive_2 := fun terms => ∀ σ τ : Substitution Variable Literal Symbol,
      (∀ name ∈ terms.flatMap Term.freeVars, σ name = τ name) →
        terms.map (Term.instantiate σ) = terms.map (Term.instantiate τ))
    ?var ?lit ?app ?truth ?falsity ?conj ?disj ?imp ?defaultNeg ?forallVar ?existsVar ?dictionaryCall ?equal ?nil ?cons term
  case var => intro name σ τ agree; simpa only [Term.instantiate] using agree name (by simp [Term.freeVars])
  case lit | truth | falsity | nil => intros; simp only [Term.instantiate, List.map]
  case app | defaultNeg =>
    intros; rename_i ih σ τ agree
    simp only [Term.instantiate, ih σ τ (fun n m => agree n (by simpa only [Term.freeVars] using m))]
  case conj | disj | imp | equal | dictionaryCall | cons =>
    intros; rename_i ihA ihB σ τ agree
    simp only [Term.instantiate, List.map_cons, ihA σ τ (fun n m => agree n (by simp [Term.freeVars, m])),
      ihB σ τ (fun n m => agree n (by simp [Term.freeVars, m]))]
  case forallVar | existsVar =>
    intro name body ih σ τ agree
    have outer : ∀ other ∈ body.freeVars, other ≠ name → σ other = τ other :=
      fun other member different => agree other (by simp [Term.freeVars, member, different])
    simp only [Term.instantiate, Substitution.binder_congr outer]
    congr 1
    apply ih
    intro other member
    by_cases same : other = name
    · simp [Substitution.bind, same]
    · simp [Substitution.bind, same, outer other member same]

/-- When `instantiate?` succeeds, it kept every binder, and so does
`instantiate`: the two agree, and existing certificates are unchanged. -/
theorem Term.instantiate?_eq (term : Term Variable Literal Symbol) {σ : Substitution Variable Literal Symbol}
    {result : Term Variable Literal Symbol} (computed : term.instantiate? σ = some result) :
    term.instantiate σ = result := by
  refine Term.rec
    (motive_1 := fun term => ∀ σ result, term.instantiate? σ = some result → term.instantiate σ = result)
    (motive_2 := fun terms => ∀ σ result, terms.mapM (Term.instantiate? σ) = some result →
      terms.map (Term.instantiate σ) = result)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ term σ result computed
  · intro name σ result computed
    simp only [Term.instantiate?, Option.some.injEq] at computed; subst computed; simp only [Term.instantiate]
  · intro value σ result computed
    simp only [Term.instantiate?, Option.some.injEq] at computed; subst computed; simp only [Term.instantiate]
  · intro symbol args ih σ result computed
    simp only [Term.instantiate?] at computed
    obtain ⟨mapped, success, rfl⟩ := Option.map_eq_some_iff.mp computed
    simp only [Term.instantiate, ih σ mapped success]
  · intro σ result computed
    simp only [Term.instantiate?, Option.some.injEq] at computed; subst computed; simp only [Term.instantiate]
  · intro σ result computed
    simp only [Term.instantiate?, Option.some.injEq] at computed; subst computed; simp only [Term.instantiate]
  · intro a b ihA ihB σ result computed
    simp only [Term.instantiate?] at computed
    obtain ⟨a', first, rest⟩ := Option.bind_eq_some_iff.mp computed
    obtain ⟨b', second, rfl⟩ := Option.map_eq_some_iff.mp rest
    simp only [Term.instantiate, ihA σ a' first, ihB σ b' second]
  · intro a b ihA ihB σ result computed
    simp only [Term.instantiate?] at computed
    obtain ⟨a', first, rest⟩ := Option.bind_eq_some_iff.mp computed
    obtain ⟨b', second, rfl⟩ := Option.map_eq_some_iff.mp rest
    simp only [Term.instantiate, ihA σ a' first, ihB σ b' second]
  · intro a b ihA ihB σ result computed
    simp only [Term.instantiate?] at computed
    obtain ⟨a', first, rest⟩ := Option.bind_eq_some_iff.mp computed
    obtain ⟨b', second, rfl⟩ := Option.map_eq_some_iff.mp rest
    simp only [Term.instantiate, ihA σ a' first, ihB σ b' second]
  · intro body ih σ result computed
    simp only [Term.instantiate?] at computed
    obtain ⟨mapped, success, rfl⟩ := Option.map_eq_some_iff.mp computed
    simp only [Term.instantiate, ih σ mapped success]
  · intro name body ih σ result computed
    simp only [Term.instantiate?] at computed
    split at computed
    · rename_i safe
      obtain ⟨mapped, success, rfl⟩ := Option.map_eq_some_iff.mp computed
      have kept : σ.binder name body = name := by simp only [Substitution.binder, safe, ite_true]
      simp only [Term.instantiate, kept, ih _ mapped success]
    · cases computed
  · intro name body ih σ result computed
    simp only [Term.instantiate?] at computed
    split at computed
    · rename_i safe
      obtain ⟨mapped, success, rfl⟩ := Option.map_eq_some_iff.mp computed
      have kept : σ.binder name body = name := by simp only [Substitution.binder, safe, ite_true]
      simp only [Term.instantiate, kept, ih _ mapped success]
    · cases computed
  · intro dictionary path operation args ihDictionary ihArgs σ result computed
    simp only [Term.instantiate?] at computed
    obtain ⟨dictionary', first, rest⟩ := Option.bind_eq_some_iff.mp computed
    obtain ⟨args', second, rfl⟩ := Option.map_eq_some_iff.mp rest
    simp only [Term.instantiate, ihDictionary σ dictionary' first, ihArgs σ args' second]
  · intro a b ihA ihB σ result computed
    simp only [Term.instantiate?] at computed
    obtain ⟨a', first, rest⟩ := Option.bind_eq_some_iff.mp computed
    obtain ⟨b', second, rfl⟩ := Option.map_eq_some_iff.mp rest
    simp only [Term.instantiate, ihA σ a' first, ihB σ b' second]
  · intro σ result computed; cases computed; rfl
  · intro head tail ihHead ihTail σ result computed
    rw [List.mapM_cons] at computed
    obtain ⟨head', first, rest⟩ := Option.bind_eq_some_iff.mp computed
    obtain ⟨tail', second, last⟩ := Option.bind_eq_some_iff.mp rest
    have same : head' :: tail' = result := Option.some.inj last
    subst result
    simp only [List.map_cons, ihHead σ head' first, ihTail σ tail' second]

/-- The identity substitution keeps every binder. -/
theorem Term.instantiate_identity (term : Term Variable Literal Symbol) :
    term.instantiate Term.var = term := by
  have kept : ∀ (name : Variable) (body : Term Variable Literal Symbol),
      Substitution.binder (Term.var : Substitution Variable Literal Symbol) name body = name := by
    intro name body
    simp only [Substitution.binder, ite_eq_left_iff]
    intro notKept
    exfalso; apply notKept
    apply List.all_eq_true.mpr
    intro other _
    by_cases same : other = name
    · simp [same]
    · simp [same, Term.freeVars, Ne.symm same]
  refine Term.rec
    (motive_1 := fun term => term.instantiate Term.var = term)
    (motive_2 := fun terms => terms.map (Term.instantiate Term.var) = terms)
    ?var ?lit ?app ?truth ?falsity ?conj ?disj ?imp ?defaultNeg ?forallVar ?existsVar ?dictionaryCall ?equal ?nil ?cons term
  all_goals intros; simp_all [Term.instantiate, Substitution.bind_identity]

/-- A substitution fixing every free name leaves the term unchanged. -/
theorem Term.instantiate_fixed {term : Term Variable Literal Symbol} {σ : Substitution Variable Literal Symbol}
    (fixed : ∀ name ∈ term.freeVars, σ name = .var name) : term.instantiate σ = term :=
  (term.instantiate_congr σ Term.var fixed).trans term.instantiate_identity

/-- Instantiating an instance composes the substitutions: substituting `τ`
into a `σ`-instance gives the instance of the template under `τ ∘ σ`. -/
theorem Substitutes.instantiate {σ : Substitution Variable Literal Symbol}
    {before after : Term Variable Literal Symbol} (proof : Substitutes σ before after)
    (τ : Substitution Variable Literal Symbol) :
    Substitutes (fun name => (σ name).instantiate τ) before (after.instantiate τ) := by
  refine Substitutes.rec
    (motive_1 := fun σ before after _ => ∀ τ : Substitution Variable Literal Symbol,
      Substitutes (fun name => (σ name).instantiate τ) before (after.instantiate τ))
    (motive_2 := fun σ before after _ => ∀ τ : Substitution Variable Literal Symbol,
      SubstitutesList (fun name => (σ name).instantiate τ) before (after.map (Term.instantiate τ)))
    ?var ?lit ?truth ?falsity ?app ?conj ?disj ?imp ?defaultNeg ?forallVar ?existsVar ?dictionaryCall ?equal ?nil ?cons proof τ
  case var => intro σ name τ; exact .var
  case forallVar | existsVar =>
    intro binder σ renamed body result fresh bodySubst ih τ
    simp only [Term.instantiate]
    constructor
    · intro name member different occurs
      obtain ⟨middle, middleMember, inside⟩ := ((σ name).instantiate_substitutes τ).freeVars_cover _ occurs
      have resultMember : middle ∈ result.freeVars :=
        bodySubst.freeVars_subset name member middle (by simpa [Substitution.bind, different] using middleMember)
      have notRenamed : middle ≠ renamed := fun same => fresh name member different (same ▸ middleMember)
      exact Substitution.binder_fresh τ renamed result middle resultMember notRenamed inside
    · apply (ih (Substitution.bind τ renamed (.var (Substitution.binder τ renamed result)))).congr
      intro name member
      by_cases same : name = binder
      · subst same; simp [Substitution.bind, Term.instantiate]
      · simp only [Substitution.bind, same, ite_false]
        apply Term.instantiate_congr
        intro other occurs
        have different : other ≠ renamed := fun equal => fresh name member same (equal ▸ occurs)
        simp [Substitution.bind, different]
  all_goals intros; simp only [Term.instantiate, List.map]; constructor <;> simp_all

/-- A free name of a single-name instance is a free name of the term other than
the replaced name, or a free name of the value replacing one of its occurrences. -/
theorem Term.freeVars_instantiate_single {term value : Term Variable Literal Symbol} {name other : Variable}
    (member : other ∈ (term.instantiate (Substitution.single name value)).freeVars) :
    (other ∈ term.freeVars ∧ other ≠ name) ∨ (name ∈ term.freeVars ∧ other ∈ value.freeVars) := by
  obtain ⟨source, sourceMember, inside⟩ := (term.instantiate_substitutes _).freeVars_cover other member
  by_cases same : source = name
  · subst same
    simp only [Substitution.single, Substitution.bind, ite_true] at inside
    exact .inr ⟨sourceMember, inside⟩
  · simp only [Substitution.single, Substitution.bind, same, ite_false, Term.freeVars,
      List.mem_singleton] at inside
    subst inside
    exact .inl ⟨sourceMember, same⟩

end Renaming

end AnthillModKbSpec
