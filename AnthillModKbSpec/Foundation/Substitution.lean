import AnthillModKbSpec.Foundation.Syntax

namespace AnthillModKbSpec

/-- Free variable names, with repetitions allowed. Binder names are removed only
from their own bodies; application arguments can themselves contain scopes. -/
def Term.freeVars {Variable Literal Symbol : Type} [DecidableEq Variable] :
    Term Variable Literal Symbol → List Variable
  | .var name => [name]
  | .lit _ | .truth | .falsity => []
  | .app _ args => args.flatMap Term.freeVars
  | .dictionaryCall dictionary _ _ args => dictionary.freeVars ++ args.flatMap Term.freeVars
  | .defaultNeg body => body.freeVars
  | .conj left right | .disj left right | .imp left right | .equal left right =>
      left.freeVars ++ right.freeVars
  | .forallVar name body | .existsVar name body => body.freeVars.filter (· != name)

/-- A simultaneous substitution for free variables. Its images are not
recursively substituted. Substitutions instantiate clause templates, never the
surrounding proof context or the rigid parameters of an existing goal. -/
abbrev Substitution (Variable Literal Symbol : Type) :=
  Variable → Term Variable Literal Symbol

/-- Override one name in a substitution. -/
def Substitution.bind {Variable Literal Symbol : Type} [DecidableEq Variable]
    (σ : Substitution Variable Literal Symbol) (name : Variable)
    (value : Term Variable Literal Symbol) : Substitution Variable Literal Symbol :=
  fun candidate => if candidate = name then value else σ candidate

/-- Replace one free variable and leave all other names unchanged. -/
def Substitution.single {Variable Literal Symbol : Type} [DecidableEq Variable]
    (name : Variable) (value : Term Variable Literal Symbol) : Substitution Variable Literal Symbol :=
  Substitution.bind Term.var name value

mutual
/-- Capture-avoiding simultaneous substitution, expressed as a relation.
At a binder `x`, choose an output binder `y` that cannot capture any substituted
free variable of the body. Override `x` by `y` while traversing that body. Thus
bound variables are preserved (possibly alpha-renamed) and inner binders shadow
outer bindings. No arbitrary fresh-name algorithm is built into the syntax. -/
inductive Substitutes {Variable Literal Symbol : Type} [DecidableEq Variable] :
    Substitution Variable Literal Symbol →
    Term Variable Literal Symbol → Term Variable Literal Symbol → Prop where
  | var : Substitutes σ (.var name) (σ name)
  | lit : Substitutes σ (.lit value) (.lit value)
  | truth : Substitutes σ .truth .truth
  | falsity : Substitutes σ .falsity .falsity
  | app (args : SubstitutesList σ before after) :
      Substitutes σ (.app symbol before) (.app symbol after)
  | conj (left : Substitutes σ a a') (right : Substitutes σ b b') :
      Substitutes σ (.conj a b) (.conj a' b')
  | disj (left : Substitutes σ a a') (right : Substitutes σ b b') :
      Substitutes σ (.disj a b) (.disj a' b')
  | imp (premise : Substitutes σ a a') (conclusion : Substitutes σ b b') :
      Substitutes σ (.imp a b) (.imp a' b')
  | defaultNeg (body : Substitutes σ before after) :
      Substitutes σ (.defaultNeg before) (.defaultNeg after)
  | forallVar
      (fresh : ∀ name ∈ body.freeVars, name ≠ binder → renamed ∉ (σ name).freeVars)
      (bodySubst : Substitutes (Substitution.bind σ binder (.var renamed)) body result) :
      Substitutes σ (.forallVar binder body) (.forallVar renamed result)
  | existsVar
      (fresh : ∀ name ∈ body.freeVars, name ≠ binder → renamed ∉ (σ name).freeVars)
      (bodySubst : Substitutes (Substitution.bind σ binder (.var renamed)) body result) :
      Substitutes σ (.existsVar binder body) (.existsVar renamed result)
  | dictionaryCall (dictionary : Substitutes σ beforeDictionary afterDictionary)
      (args : SubstitutesList σ before after) :
      Substitutes σ (.dictionaryCall beforeDictionary path operation before)
        (.dictionaryCall afterDictionary path operation after)
  | equal (left : Substitutes σ a a') (right : Substitutes σ b b') :
      Substitutes σ (.equal a b) (.equal a' b')

/-- The same substitution applied pointwise to argument lists. -/
inductive SubstitutesList {Variable Literal Symbol : Type} [DecidableEq Variable] :
    Substitution Variable Literal Symbol →
    List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) → Prop where
  | nil : SubstitutesList σ [] []
  | cons (head : Substitutes σ a b) (tail : SubstitutesList σ as bs) :
      SubstitutesList σ (a :: as) (b :: bs)
end

/-- A single substitution replaces the selected variable by its witness. -/
theorem Substitutes.singleVar {Variable Literal Symbol : Type} [DecidableEq Variable]
    (name : Variable) (witness : Term Variable Literal Symbol) :
    Substitutes (Substitution.single name witness) (.var name) witness := by
  simpa [Substitution.single, Substitution.bind] using
    (Substitutes.var (σ := Substitution.single name witness) (name := name) :
      Substitutes (Substitution.single name witness) (.var name)
        ((Substitution.single name witness) name))

/-- Substituting a goal list pointwise substitutes its conjunction. -/
theorem SubstitutesList.conjunction {Variable Literal Symbol : Type} [DecidableEq Variable]
    {σ : Substitution Variable Literal Symbol} {before after : List (Term Variable Literal Symbol)}
    (proof : SubstitutesList σ before after) : Substitutes σ (.conjunction before) (.conjunction after) := by
  induction before generalizing after with
  | nil => cases proof; exact .truth
  | cons head tail ih => cases proof with | cons first rest => exact .conj first (ih rest)

/-! ## Free names, agreement, and cancellation

An instance's free names are exactly the free names of the values substituted
for the template's free names: a binder neither captures a substituted name nor
lets its own bound name escape. Only the values at the template's free names
matter, and a substitution that factors through an intermediate instance may be
cancelled against it, whatever binder names either instance chose. -/

section Theory

variable {Variable Literal Symbol : Type} [DecidableEq Variable]

private theorem bind_other {σ : Substitution Variable Literal Symbol} {binder renamed name : Variable}
    (different : name ≠ binder) : Substitution.bind σ binder (.var renamed) name = σ name := by
  simp [Substitution.bind, different]

/-- The free names of an instance are exactly the free names of the values
substituted for the template's free names. -/
theorem Substitutes.mem_freeVars {σ : Substitution Variable Literal Symbol}
    {before after : Term Variable Literal Symbol} (proof : Substitutes σ before after) (other : Variable) :
    other ∈ after.freeVars ↔ ∃ name ∈ before.freeVars, other ∈ (σ name).freeVars := by
  refine Substitutes.rec
    (motive_1 := fun σ before after _ => ∀ other,
      other ∈ after.freeVars ↔ ∃ name ∈ before.freeVars, other ∈ (σ name).freeVars)
    (motive_2 := fun σ before after _ => ∀ other,
      other ∈ after.flatMap Term.freeVars ↔ ∃ name ∈ before.flatMap Term.freeVars, other ∈ (σ name).freeVars)
    ?var ?lit ?truth ?falsity ?app ?conj ?disj ?imp ?defaultNeg ?forallVar ?existsVar ?dictionaryCall ?equal
    ?nil ?cons proof other
  case var | lit | truth | falsity | nil => intros; simp [Term.freeVars]
  case app | defaultNeg => intros; rename_i ih other; simpa only [Term.freeVars] using ih other
  case conj | disj | imp | equal | cons | dictionaryCall =>
    intros; rename_i ihLeft ihRight other
    simp only [Term.freeVars, List.flatMap_cons, List.mem_append, ihLeft, ihRight, or_and_right, exists_or]
  case forallVar | existsVar =>
    intro binder σ renamed body result fresh bodySubst ih other
    simp only [Term.freeVars, List.mem_filter, bne_iff_ne, ne_eq, ih]
    constructor
    · rintro ⟨⟨name, member, inside⟩, different⟩
      by_cases same : name = binder
      · subst same; simp [Substitution.bind, Term.freeVars] at inside; exact absurd inside different
      · exact ⟨name, ⟨member, same⟩, by rwa [bind_other same] at inside⟩
    · rintro ⟨name, ⟨member, different⟩, inside⟩
      exact ⟨⟨name, member, by rwa [bind_other different]⟩,
        fun same => fresh name member different (same ▸ inside)⟩

/-- Every free name of a substituted value occurs free in the instance. -/
theorem Substitutes.freeVars_subset {σ : Substitution Variable Literal Symbol}
    {before after : Term Variable Literal Symbol} (proof : Substitutes σ before after) :
    ∀ name ∈ before.freeVars, ∀ other ∈ (σ name).freeVars, other ∈ after.freeVars :=
  fun name member other inside => (proof.mem_freeVars other).mpr ⟨name, member, inside⟩

/-- Every free name of the instance comes from the value of a free template name. -/
theorem Substitutes.freeVars_cover {σ : Substitution Variable Literal Symbol}
    {before after : Term Variable Literal Symbol} (proof : Substitutes σ before after) :
    ∀ other ∈ after.freeVars, ∃ name ∈ before.freeVars, other ∈ (σ name).freeVars :=
  fun other member => (proof.mem_freeVars other).mp member

/-- Only the values at the template's free names matter. -/
theorem Substitutes.congr {σ τ : Substitution Variable Literal Symbol}
    {before after : Term Variable Literal Symbol} (proof : Substitutes σ before after)
    (agree : ∀ name ∈ before.freeVars, σ name = τ name) : Substitutes τ before after := by
  refine Substitutes.rec
    (motive_1 := fun σ before after _ => ∀ τ : Substitution Variable Literal Symbol,
      (∀ name ∈ before.freeVars, σ name = τ name) → Substitutes τ before after)
    (motive_2 := fun σ before after _ => ∀ τ : Substitution Variable Literal Symbol,
      (∀ name ∈ before.flatMap Term.freeVars, σ name = τ name) → SubstitutesList τ before after)
    ?var ?lit ?truth ?falsity ?app ?conj ?disj ?imp ?defaultNeg ?forallVar ?existsVar ?dictionaryCall ?equal
    ?nil ?cons proof τ agree
  case var => intro σ name τ agree; rw [agree name (by simp [Term.freeVars])]; exact .var
  case lit | truth | falsity | nil => intros; constructor
  case app | defaultNeg =>
    intros; rename_i ih τ agree
    constructor; exact ih τ (fun n m => agree n (by simpa only [Term.freeVars] using m))
  case conj | disj | imp | equal | cons | dictionaryCall =>
    intros; rename_i ihLeft ihRight τ agree
    constructor
    · exact ihLeft τ (fun n m => agree n (by simp [Term.freeVars, m]))
    · exact ihRight τ (fun n m => agree n (by simp [Term.freeVars, m]))
  case forallVar | existsVar =>
    intro binder σ renamed body result fresh bodySubst ih τ agree
    constructor
    · intro name member different
      rw [← agree name (by simp [Term.freeVars, member, different])]
      exact fresh name member different
    · apply ih
      intro name member
      by_cases same : name = binder
      · simp [Substitution.bind, same]
      · rw [bind_other same, bind_other same]
        exact agree name (by simp [Term.freeVars, member, same])

/-- Cancel a substitution through an intermediate instance. If `ρ` instantiates
`before` to `after`, and each `ρ name` is a `θ`-instance of `σ name`, then
`after` is a `θ`-instance of the `σ`-instance `middle`. The binder names chosen
in `middle` and `after` are unrelated: the relation accepts every capture-free
choice, so reading an opened goal through later answers stays an opening of the
read quantifier. -/
theorem Substitutes.cancel {σ ρ θ : Substitution Variable Literal Symbol}
    {before middle after : Term Variable Literal Symbol}
    (first : Substitutes σ before middle) (whole : Substitutes ρ before after)
    (pointwise : ∀ name ∈ before.freeVars, Substitutes θ (σ name) (ρ name)) :
    Substitutes θ middle after := by
  refine Substitutes.rec
    (motive_1 := fun σ before middle _ => ∀ (ρ θ : Substitution Variable Literal Symbol) after,
      Substitutes ρ before after → (∀ name ∈ before.freeVars, Substitutes θ (σ name) (ρ name)) →
        Substitutes θ middle after)
    (motive_2 := fun σ before middle _ => ∀ (ρ θ : Substitution Variable Literal Symbol) after,
      SubstitutesList ρ before after →
        (∀ name ∈ before.flatMap Term.freeVars, Substitutes θ (σ name) (ρ name)) →
        SubstitutesList θ middle after)
    ?var ?lit ?truth ?falsity ?app ?conj ?disj ?imp ?defaultNeg ?forallVar ?existsVar ?dictionaryCall ?equal
    ?nil ?cons first ρ θ after whole pointwise
  case var => intro σ name ρ θ after whole pointwise; cases whole; exact pointwise name (by simp [Term.freeVars])
  case lit | truth | falsity | nil => intros; rename_i whole _; cases whole; constructor
  case app | defaultNeg =>
    intros; rename_i ih ρ θ after whole pointwise
    cases whole; rename_i rest
    constructor; exact ih ρ θ _ rest (fun n m => pointwise n (by simpa only [Term.freeVars] using m))
  case conj | disj | imp | equal | cons | dictionaryCall =>
    intros; rename_i ihLeft ihRight ρ θ after whole pointwise
    cases whole; rename_i l r
    constructor
    · exact ihLeft ρ θ _ l (fun n m => pointwise n (by simp [Term.freeVars, m]))
    · exact ihRight ρ θ _ r (fun n m => pointwise n (by simp [Term.freeVars, m]))
  case forallVar | existsVar =>
    intro binder σ renamed body result fresh bodySubst ih ρ θ after whole pointwise
    cases whole; rename_i renamed' result' fresh' bodySubst'
    constructor
    · intro name member different inside
      obtain ⟨source, sourceMember, occurs⟩ := bodySubst.freeVars_cover name member
      by_cases same : source = binder
      · subst same
        simp [Substitution.bind, Term.freeVars] at occurs
        exact different occurs
      · rw [bind_other same] at occurs
        have point := pointwise source (by simp [Term.freeVars, sourceMember, same])
        exact fresh' source sourceMember same (point.freeVars_subset name occurs renamed' inside)
    · apply ih _ _ _ bodySubst'
      intro name member
      by_cases same : name = binder
      · subst same
        simpa [Substitution.bind] using
          (Substitutes.var (σ := Substitution.bind θ renamed (.var renamed')) (name := renamed))
      · rw [bind_other same, bind_other same]
        apply (pointwise name (by simp [Term.freeVars, member, same])).congr
        intro other occurs
        have different : other ≠ renamed := fun equal => fresh name member same (equal ▸ occurs)
        simp [Substitution.bind, different]

end Theory

end AnthillModKbSpec
