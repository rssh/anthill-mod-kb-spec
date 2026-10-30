import AnthillModKbSpec.Resolution.Machine.Store
import AnthillModKbSpec.Foundation.Freshening

namespace AnthillModKbSpec.Machine

open OperationDictionaries (lookup lookup_eq_none)

/-! # Reading through the store, and freshening clause uses

Goals, pending premises, and captured local assumptions are stored as written
and read through the committed answers (`Store.resolve`). A later binding
therefore reaches every pending goal and context without rewriting the state,
and a reading taken earlier is extended, not replaced (`Store.resolve_extends`).
Reading commutes with instantiation: it turns a clause instance into an
instance of the clause (`resolveWith_substitutes`) and an opened quantifier
into an opening of the read quantifier (`resolveWith_forallVar`), whatever
binders alpha-renaming chose on either side. -/

variable {Variable Literal Symbol : Type} [DecidableEq Variable]

/-- Bound names are flexible, so a rigid or undeclared name is never bound. -/
theorem Store.Scoped.unbound {store : Store Variable Literal Symbol} (valid : store.Scoped) {name : Variable}
    (notFlexible : ∀ dependencies, store.info? name ≠ some (.flexible dependencies)) :
    name ∉ store.bindings.map Prod.fst := by
  intro member
  obtain ⟨⟨_, value⟩, inside, rfl⟩ := List.mem_map.mp member
  obtain ⟨dependencies, flexible, _⟩ := valid.answers _ value inside
  exact notFlexible dependencies flexible

/-! ## Reading -/

section Reading

variable [FreshNames Variable]

theorem resolveWith_cons (name : Variable) (value : Term Variable Literal Symbol)
    (rest : List (Variable × Term Variable Literal Symbol)) (term : Term Variable Literal Symbol) :
    resolveWith ((name, value) :: rest) term =
      (resolveWith rest term).instantiate (Substitution.single name value) := rfl

/-- Later answers apply after earlier ones. -/
theorem resolveWith_append (added older : List (Variable × Term Variable Literal Symbol))
    (term : Term Variable Literal Symbol) :
    resolveWith (added ++ older) term = resolveWith added (resolveWith older term) := by
  simp [resolveWith, List.foldr_append]

/-- Reading through an extended store reads the earlier reading through the
added bindings: equal readings stay equal, and a matched pair stays matched. -/
theorem Store.resolve_extends {store next : Store Variable Literal Symbol}
    {added : List (Variable × Term Variable Literal Symbol)} (extended : next.bindings = added ++ store.bindings)
    (term : Term Variable Literal Symbol) : next.resolve term = resolveWith added (store.resolve term) := by
  simp only [Store.resolve, extended, resolveWith_append]

/-- A term mentioning no bound name reads as itself. -/
theorem resolveWith_unbound {bindings : List (Variable × Term Variable Literal Symbol)}
    {term : Term Variable Literal Symbol} (unbound : ∀ name ∈ term.freeVars, name ∉ bindings.map Prod.fst) :
    resolveWith bindings term = term := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
      obtain ⟨name, value⟩ := binding
      rw [resolveWith_cons, ih (fun other member inside => unbound other member (by simp [inside]))]
      apply Term.instantiate_fixed
      intro other member
      have different : other ≠ name := fun same => unbound other member (by simp [same])
      simp [Substitution.single, Substitution.bind, different]

/-- Every free name of a reading comes from reading one free name of the term. -/
theorem resolveWith_freeVars (bindings : List (Variable × Term Variable Literal Symbol))
    {term : Term Variable Literal Symbol} :
    ∀ other ∈ (resolveWith bindings term).freeVars,
      ∃ name ∈ term.freeVars, other ∈ (resolveWith bindings (.var name)).freeVars := by
  induction bindings with
  | nil => intro other member; exact ⟨other, member, by simp [resolveWith, Term.freeVars]⟩
  | cons binding rest ih =>
      obtain ⟨name, value⟩ := binding
      intro other member
      rw [resolveWith_cons] at member
      obtain ⟨middle, middleMember, inside⟩ := (Term.instantiate_substitutes _ _).freeVars_cover other member
      obtain ⟨source, sourceMember, occurs⟩ := ih middle middleMember
      refine ⟨source, sourceMember, ?_⟩
      rw [resolveWith_cons]
      exact (Term.instantiate_substitutes _ _).freeVars_subset middle occurs other inside

/-- Reading an instance is an instance of the template by the read values. A
freshened clause read through the final answers is therefore one clause
instance, as `Derives.clause` requires. -/
theorem resolveWith_substitutes (bindings : List (Variable × Term Variable Literal Symbol))
    {σ : Substitution Variable Literal Symbol} {before after : Term Variable Literal Symbol}
    (proof : Substitutes σ before after) :
    Substitutes (fun name => resolveWith bindings (σ name)) before (resolveWith bindings after) := by
  induction bindings with
  | nil => exact proof
  | cons binding rest ih => exact ih.instantiate _

private theorem cancel_opening {bindings : List (Variable × Term Variable Literal Symbol)}
    {binder renamed : Variable} {body result : Term Variable Literal Symbol}
    (fresh : ∀ name ∈ body.freeVars, name ≠ binder → renamed ∉ (resolveWith bindings (.var name)).freeVars)
    (bodySubst : Substitutes (Substitution.bind (fun name => resolveWith bindings (.var name)) binder (.var renamed))
      body result)
    {witness instantiated : Term Variable Literal Symbol}
    (instantiation : Substitutes (Substitution.single binder witness) body instantiated) :
    Substitutes (Substitution.single renamed (resolveWith bindings witness)) result
      (resolveWith bindings instantiated) := by
  apply bodySubst.cancel (resolveWith_substitutes bindings instantiation)
  intro name member
  by_cases same : name = binder
  · subst same
    simpa [Substitution.bind, Substitution.single] using
      (Substitutes.var (σ := Substitution.single renamed (resolveWith bindings witness)) (name := renamed))
  · simp only [Substitution.bind, Substitution.single, same, ite_false]
    apply Substitutes.fixed
    intro other occurs
    have different : other ≠ renamed := fun equal => fresh name member same (equal ▸ occurs)
    simp [Substitution.bind, different]

/-- A read universal is a universal, and reading an instance of its body is an
instance of the read body with the read witness. This covers opening with an
eigenvariable (whose reading is itself) and elimination with any witness. -/
theorem resolveWith_forallVar (bindings : List (Variable × Term Variable Literal Symbol))
    (binder : Variable) (body : Term Variable Literal Symbol) :
    ∃ renamed result, resolveWith bindings (.forallVar binder body) = .forallVar renamed result ∧
      ∀ {witness instantiated : Term Variable Literal Symbol},
        Substitutes (Substitution.single binder witness) body instantiated →
        Substitutes (Substitution.single renamed (resolveWith bindings witness)) result
          (resolveWith bindings instantiated) := by
  have whole := resolveWith_substitutes bindings (Substitutes.identity (Term.forallVar binder body))
  generalize resolveWith bindings (.forallVar binder body) = read at whole ⊢
  cases whole with
  | forallVar fresh bodySubst => exact ⟨_, _, rfl, fun instantiation => cancel_opening fresh bodySubst instantiation⟩

theorem resolveWith_existsVar (bindings : List (Variable × Term Variable Literal Symbol))
    (binder : Variable) (body : Term Variable Literal Symbol) :
    ∃ renamed result, resolveWith bindings (.existsVar binder body) = .existsVar renamed result ∧
      ∀ {witness instantiated : Term Variable Literal Symbol},
        Substitutes (Substitution.single binder witness) body instantiated →
        Substitutes (Substitution.single renamed (resolveWith bindings witness)) result
          (resolveWith bindings instantiated) := by
  have whole := resolveWith_substitutes bindings (Substitutes.identity (Term.existsVar binder body))
  generalize resolveWith bindings (.existsVar binder body) = read at whole ⊢
  cases whole with
  | existsVar fresh bodySubst => exact ⟨_, _, rfl, fun instantiation => cancel_opening fresh bodySubst instantiation⟩

/-- Reading preserves the other constructors. -/
theorem resolveWith_conj (bindings : List (Variable × Term Variable Literal Symbol))
    (left right : Term Variable Literal Symbol) :
    resolveWith bindings (.conj left right) = .conj (resolveWith bindings left) (resolveWith bindings right) := by
  induction bindings <;> simp_all [resolveWith, Term.instantiate]

theorem resolveWith_disj (bindings : List (Variable × Term Variable Literal Symbol))
    (left right : Term Variable Literal Symbol) :
    resolveWith bindings (.disj left right) = .disj (resolveWith bindings left) (resolveWith bindings right) := by
  induction bindings <;> simp_all [resolveWith, Term.instantiate]

theorem resolveWith_imp (bindings : List (Variable × Term Variable Literal Symbol))
    (left right : Term Variable Literal Symbol) :
    resolveWith bindings (.imp left right) = .imp (resolveWith bindings left) (resolveWith bindings right) := by
  induction bindings <;> simp_all [resolveWith, Term.instantiate]

theorem resolveWith_equal (bindings : List (Variable × Term Variable Literal Symbol))
    (left right : Term Variable Literal Symbol) :
    resolveWith bindings (.equal left right) = .equal (resolveWith bindings left) (resolveWith bindings right) := by
  induction bindings <;> simp_all [resolveWith, Term.instantiate]

theorem resolveWith_defaultNeg (bindings : List (Variable × Term Variable Literal Symbol))
    (body : Term Variable Literal Symbol) :
    resolveWith bindings (.defaultNeg body) = .defaultNeg (resolveWith bindings body) := by
  induction bindings <;> simp_all [resolveWith, Term.instantiate]

theorem resolveWith_app (bindings : List (Variable × Term Variable Literal Symbol)) (symbol : Symbol)
    (args : List (Term Variable Literal Symbol)) :
    resolveWith bindings (.app symbol args) = .app symbol (args.map (resolveWith bindings)) := by
  induction bindings with
  | nil =>
      have identity : resolveWith ([] : List (Variable × Term Variable Literal Symbol)) = id := funext fun _ => rfl
      rw [identity, List.map_id]; rfl
  | cons binding rest ih =>
      obtain ⟨name, value⟩ := binding
      simp only [resolveWith_cons, ih, Term.instantiate, List.map_map]; rfl

theorem resolveWith_truth (bindings : List (Variable × Term Variable Literal Symbol)) :
    resolveWith bindings (.truth : Term Variable Literal Symbol) = .truth := by
  induction bindings <;> simp_all [resolveWith, Term.instantiate]

theorem resolveWith_falsity (bindings : List (Variable × Term Variable Literal Symbol)) :
    resolveWith bindings (.falsity : Term Variable Literal Symbol) = .falsity := by
  induction bindings <;> simp_all [resolveWith, Term.instantiate]

/-! Reading in store form. -/

@[simp] theorem Store.resolve_truth (store : Store Variable Literal Symbol) :
    store.resolve (.truth : Term Variable Literal Symbol) = .truth := resolveWith_truth _

@[simp] theorem Store.resolve_falsity (store : Store Variable Literal Symbol) :
    store.resolve (.falsity : Term Variable Literal Symbol) = .falsity := resolveWith_falsity _

@[simp] theorem Store.resolve_conj (store : Store Variable Literal Symbol) (left right : Term Variable Literal Symbol) :
    store.resolve (.conj left right) = .conj (store.resolve left) (store.resolve right) := resolveWith_conj _ _ _

@[simp] theorem Store.resolve_disj (store : Store Variable Literal Symbol) (left right : Term Variable Literal Symbol) :
    store.resolve (.disj left right) = .disj (store.resolve left) (store.resolve right) := resolveWith_disj _ _ _

@[simp] theorem Store.resolve_imp (store : Store Variable Literal Symbol) (left right : Term Variable Literal Symbol) :
    store.resolve (.imp left right) = .imp (store.resolve left) (store.resolve right) := resolveWith_imp _ _ _

@[simp] theorem Store.resolve_equal (store : Store Variable Literal Symbol) (left right : Term Variable Literal Symbol) :
    store.resolve (.equal left right) = .equal (store.resolve left) (store.resolve right) := resolveWith_equal _ _ _

@[simp] theorem Store.resolve_defaultNeg (store : Store Variable Literal Symbol) (body : Term Variable Literal Symbol) :
    store.resolve (.defaultNeg body) = .defaultNeg (store.resolve body) := resolveWith_defaultNeg _ _

theorem Store.resolve_unbound (store : Store Variable Literal Symbol) {name : Variable}
    (unbound : name ∉ store.bindings.map Prod.fst) : store.resolve (.var name) = .var name :=
  resolveWith_unbound (fun other inside => by
    simp only [Term.freeVars, List.mem_singleton] at inside; subst inside; exact unbound)

theorem Store.resolve_forallVar (store : Store Variable Literal Symbol) (binder : Variable)
    (body : Term Variable Literal Symbol) :
    ∃ renamed result, store.resolve (.forallVar binder body) = .forallVar renamed result ∧
      ∀ {witness instantiated : Term Variable Literal Symbol},
        Substitutes (Substitution.single binder witness) body instantiated →
        Substitutes (Substitution.single renamed (store.resolve witness)) result (store.resolve instantiated) :=
  resolveWith_forallVar store.bindings binder body

theorem Store.resolve_existsVar (store : Store Variable Literal Symbol) (binder : Variable)
    (body : Term Variable Literal Symbol) :
    ∃ renamed result, store.resolve (.existsVar binder body) = .existsVar renamed result ∧
      ∀ {witness instantiated : Term Variable Literal Symbol},
        Substitutes (Substitution.single binder witness) body instantiated →
        Substitutes (Substitution.single renamed (store.resolve witness)) result (store.resolve instantiated) :=
  resolveWith_existsVar store.bindings binder body

theorem Store.resolve_substitutes (store : Store Variable Literal Symbol) {σ : Substitution Variable Literal Symbol}
    {before after : Term Variable Literal Symbol} (proof : Substitutes σ before after) :
    Substitutes (fun name => store.resolve (σ name)) before (store.resolve after) :=
  resolveWith_substitutes store.bindings proof

/-- A derived local rule read through the answers yields its read instances. -/
theorem Derives.resolve_instantiateLeading {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
    {context : ProofContext Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}
    (bindings : List (Variable × Term Variable Literal Symbol)) {rule : Term Variable Literal Symbol}
    (witnesses : List (Term Variable Literal Symbol)) {instantiated : Term Variable Literal Symbol}
    (computed : rule.instantiateLeading witnesses = some instantiated)
    (proof : Derives hoApplySymbol kb context (resolveWith bindings rule) naf) :
    Derives hoApplySymbol kb context (resolveWith bindings instantiated) naf := by
  induction witnesses generalizing rule with
  | nil => cases computed; exact proof
  | cons witness rest ih =>
      cases rule with
      | forallVar binder body =>
          obtain ⟨renamed, result, read, opening⟩ := resolveWith_forallVar bindings binder body
          rw [read] at proof
          exact ih computed (.forallElim proof (opening (body.instantiate_substitutes _)))
      | _ => cases computed

/-- Resolution leaves no bound name. -/
theorem Triangular.resolve_unbound {bindings : List (Variable × Term Variable Literal Symbol)}
    (triangular : Triangular bindings) (term : Term Variable Literal Symbol) :
    ∀ other ∈ (resolveWith bindings term).freeVars, other ∉ bindings.map Prod.fst := by
  induction triangular with
  | nil => intros; simp
  | @cons name value older unbound resolved rest ih =>
      intro other member
      rw [resolveWith_cons] at member
      rcases Term.freeVars_instantiate_single member with ⟨inside, different⟩ | ⟨_, inside⟩
      · simp [different, ih other inside]
      · have ⟨notSelf, notOlder⟩ := resolved other inside
        simp [notSelf, notOlder]

end Reading

/-! ## Refinement and the scope of resolved answers -/

/-- `later` keeps every name of `store` with its kind, flexible names only lose
dependencies, and bindings are only added. Commits refine the store, so the
store at any later point of a successful path refines every earlier one. -/
structure Store.Refines (store later : Store Variable Literal Symbol) : Prop where
  rigid : ∀ name, store.info? name = some .rigid → later.info? name = some .rigid
  flexible : ∀ name dependencies, store.info? name = some (.flexible dependencies) →
    ∃ narrowed, later.info? name = some (.flexible narrowed) ∧ ∀ rigid ∈ narrowed, rigid ∈ dependencies
  bindings : ∃ added, later.bindings = added ++ store.bindings

/-- A store with the same names and bindings refines it, whatever suspensions
and constraints either holds. -/
theorem Store.Refines.of_same {store later : Store Variable Literal Symbol} (names : later.names = store.names)
    (bindings : later.bindings = store.bindings) : store.Refines later := by
  have info : ∀ name, later.info? name = store.info? name := fun name => by simp only [Store.info?, names]
  exact ⟨fun name rigid => (info name).trans rigid,
    fun name dependencies flexible => ⟨dependencies, (info name).trans flexible, fun _ member => member⟩,
    ⟨[], by rw [bindings]; rfl⟩⟩

theorem Store.Refines.refl (store : Store Variable Literal Symbol) : store.Refines store := .of_same rfl rfl

theorem Store.Refines.trans {first second third : Store Variable Literal Symbol}
    (earlier : first.Refines second) (later : second.Refines third) : first.Refines third := by
  refine ⟨fun name rigid => later.rigid name (earlier.rigid name rigid), fun name dependencies flexible => ?_, ?_⟩
  · obtain ⟨middle, middleEq, middleContained⟩ := earlier.flexible name dependencies flexible
    obtain ⟨narrowed, narrowedEq, contained⟩ := later.flexible name middle middleEq
    exact ⟨narrowed, narrowedEq, fun rigid member => middleContained rigid (contained rigid member)⟩
  · obtain ⟨added, addedEq⟩ := earlier.bindings
    obtain ⟨more, moreEq⟩ := later.bindings
    exact ⟨more ++ added, by rw [moreEq, addedEq, List.append_assoc]⟩

/-- Equal readings stay equal in every refinement: a matched pair stays matched
for the rest of the path, and so does a goal closed against an assumption. -/
theorem Store.Refines.resolve_eq [FreshNames Variable] {store later : Store Variable Literal Symbol}
    (refines : store.Refines later) {left right : Term Variable Literal Symbol}
    (equal : store.resolve left = store.resolve right) : later.resolve left = later.resolve right := by
  obtain ⟨added, extended⟩ := refines.bindings
  rw [Store.resolve_extends extended, Store.resolve_extends extended, equal]

theorem Store.bind_refines {store next : Store Variable Literal Symbol} {scope : Scope Variable Literal Symbol}
    {name : Variable} {value : Term Variable Literal Symbol}
    (committed : store.bind scope name value = .bound next) : store.Refines next := by
  refine ⟨fun other rigid => ?_, fun other dependencies flexible => Store.bind_flexible committed flexible, ?_⟩
  · obtain ⟨dependencies, _, _, outcome⟩ := Store.bind_committed committed
    rcases outcome with ⟨_, rfl⟩ | ⟨rfl, _, _⟩
    · exact rigid
    · show (store.narrow value.freeVars dependencies).info? other = _
      rw [Store.info?_narrow, rigid]; rfl
  · obtain ⟨dependencies, _, _, outcome⟩ := Store.bind_committed committed
    rcases outcome with ⟨_, rfl⟩ | ⟨rfl, _, _⟩
    · exact ⟨[], rfl⟩
    · exact ⟨[(name, value)], rfl⟩

theorem Store.bindAll_refines {store next : Store Variable Literal Symbol} {scope : Scope Variable Literal Symbol}
    {bindings : List (Variable × Term Variable Literal Symbol)}
    (committed : store.bindAll scope bindings = .bound next) : store.Refines next := by
  induction bindings generalizing store with
  | nil => cases committed; exact .refl _
  | cons binding rest ih =>
      obtain ⟨name, value⟩ := binding
      simp only [Store.bindAll] at committed
      split at committed
      · rename_i middle bound
        exact (Store.bind_refines bound).trans (ih committed)
      · cases committed
      · cases committed

/-- Waking removes suspensions only: the store's names and bindings stay. -/
theorem Store.Refines.wake (store : Store Variable Literal Symbol) : store.Refines store.wake := .of_same rfl rfl

/-- Suspending a goal changes no name or binding. -/
theorem Store.Refines.suspend (store : Store Variable Literal Symbol) (suspension : Suspension Variable Literal Symbol) :
    store.Refines (store.suspend suspension) := .of_same rfl rfl

theorem Store.declare_refines (store : Store Variable Literal Symbol) (info : NameInfo Variable)
    {names : List Variable} (fresh : ∀ name ∈ names, store.info? name = none) :
    store.Refines (store.declare info names) := by
  have old : ∀ name, store.info? name ≠ none → (store.declare info names).info? name = store.info? name :=
    fun _ present => Store.info?_declare_of_ne_none fresh present
  refine ⟨fun name rigid => ?_, fun name dependencies flexible => ?_, ⟨[], rfl⟩⟩
  · rw [old name (by rw [rigid]; exact Option.some_ne_none _), rigid]
  · exact ⟨dependencies, by rw [old name (by rw [flexible]; exact Option.some_ne_none _), flexible],
      fun _ member => member⟩

/-- Preparing a candidate's names refines the store. -/
theorem Store.prepare_refines (store : Store Variable Literal Symbol) {obligation : Obligation Variable Literal Symbol}
    {flexibles rigids : List Variable} (distinct : (flexibles ++ rigids).Nodup)
    (fresh : ∀ name ∈ flexibles ++ rigids, store.info? name = none) :
    store.Refines (store.prepare obligation flexibles rigids) := by
  exact (store.declare_refines (.flexible obligation.scope.rigids) (names := flexibles)
    (fun name member => fresh name (List.mem_append_left _ member))).trans
    (Store.declare_refines _ .rigid (Store.declare_keeps_fresh distinct fresh))

theorem Store.commit_refines {store next : Store Variable Literal Symbol}
    {obligation : Obligation Variable Literal Symbol} {flexibles rigids : List Variable}
    {premises : List (Premise Variable Literal Symbol)} {bindings : List (Variable × Term Variable Literal Symbol)}
    {woken : List (Suspension Variable Literal Symbol)}
    (committed : store.commit obligation flexibles rigids premises bindings = .committed next woken) :
    store.Refines next := by
  obtain ⟨⟨distinct, fresh, _, _, _⟩, bound, boundEq, rfl, _⟩ := Store.commit_checks committed
  exact ((store.prepare_refines distinct fresh).trans (Store.bindAll_refines boundEq)).trans (.wake bound)

/-- A commit declares its premises' rigid names rigid. -/
theorem Store.commit_rigid {store next : Store Variable Literal Symbol}
    {obligation : Obligation Variable Literal Symbol} {flexibles rigids : List Variable}
    {premises : List (Premise Variable Literal Symbol)} {bindings : List (Variable × Term Variable Literal Symbol)}
    {woken : List (Suspension Variable Literal Symbol)}
    (committed : store.commit obligation flexibles rigids premises bindings = .committed next woken)
    {opened : Variable} (member : opened ∈ rigids) : next.info? opened = some .rigid := by
  obtain ⟨_, bound, boundEq, rfl, _⟩ := Store.commit_checks committed
  apply (Store.bindAll_refines boundEq).rigid
  simp only [Store.prepare, Store.info?_declare, member, ite_true]

/-- A refinement declares every name the store declares. -/
theorem Store.Refines.declared {store later : Store Variable Literal Symbol} (refines : store.Refines later)
    {name : Variable} (present : store.info? name ≠ none) : later.info? name ≠ none := by
  cases info : store.info? name with
  | none => exact absurd info present
  | some found =>
      cases found with
      | rigid => rw [refines.rigid name info]; exact Option.some_ne_none _
      | flexible dependencies =>
          obtain ⟨narrowed, narrowedEq, _⟩ := refines.flexible name dependencies info
          rw [narrowedEq]; exact Option.some_ne_none _

/-- The name invariant survives every refinement, in particular every commit. -/
theorem Obligation.Declared.refines {store later : Store Variable Literal Symbol}
    {obligation : Obligation Variable Literal Symbol} (declared : obligation.Declared store)
    (refines : store.Refines later) : obligation.Declared later :=
  declared.mono fun _ present => refines.declared present

/-- A rigid name a commit opens never becomes a dependency of a flexible name
that already existed, so by `Scoped` it never enters that name's answer: the
opened eigenvariable or existential witness cannot escape its premise. -/
theorem Store.commit_no_escape {store next : Store Variable Literal Symbol} (valid : store.Scoped)
    {obligation : Obligation Variable Literal Symbol} {flexibles rigids : List Variable}
    {premises : List (Premise Variable Literal Symbol)} {bindings : List (Variable × Term Variable Literal Symbol)}
    {woken : List (Suspension Variable Literal Symbol)}
    (committed : store.commit obligation flexibles rigids premises bindings = .committed next woken)
    {opened : Variable} (member : opened ∈ rigids) {name : Variable} {dependencies : List Variable}
    (existing : store.info? name = some (.flexible dependencies)) :
    ∃ narrowed, next.info? name = some (.flexible narrowed) ∧ opened ∉ narrowed := by
  obtain ⟨narrowed, narrowedEq, _⟩ := (Store.commit_refines committed).flexible name dependencies existing
  exact ⟨narrowed, narrowedEq, Store.commit_independent valid committed member narrowedEq⟩

/-- A commit keeps the obligation declared and declares every premise
obligation: the premises' own names are declared in the prepared store, and
the parent's assumptions were declared before. -/
theorem Store.commit_declared {store next : Store Variable Literal Symbol}
    {obligation : Obligation Variable Literal Symbol} {flexibles rigids : List Variable}
    {premises : List (Premise Variable Literal Symbol)} {bindings : List (Variable × Term Variable Literal Symbol)}
    {woken : List (Suspension Variable Literal Symbol)}
    (committed : store.commit obligation flexibles rigids premises bindings = .committed next woken)
    (declared : obligation.Declared store) :
    obligation.Declared next ∧ ∀ premise ∈ premises, (obligation.premise premise).Declared next := by
  obtain ⟨⟨_, _, _, _, admitted⟩, bound, boundEq, rfl, _⟩ := Store.commit_checks committed
  have whole := Store.commit_refines committed
  refine ⟨declared.refines whole, fun premise member name inside => ?_⟩
  rcases Obligation.mem_premise_freeVars.mp inside with own | context
  · exact ((Store.bindAll_refines boundEq).trans (.wake bound)).declared
      (Store.inScope_within (admitted premise member name own)).declared
  · exact whole.declared (declared name (List.mem_append_right _ context))

theorem Store.Within.mono {store : Store Variable Literal Symbol} {small large : List Variable}
    {other : Variable} (within : store.Within small other) (contained : ∀ rigid ∈ small, rigid ∈ large) :
    store.Within large other := by
  rcases within with ⟨rigid, member⟩ | ⟨own, flexible, inside⟩
  · exact .inl ⟨rigid, contained other member⟩
  · exact .inr ⟨own, flexible, fun rigid member => contained rigid (inside rigid member)⟩

section Scope

variable [FreshNames Variable]

private theorem within_resolveWith {store : Store Variable Literal Symbol} (valid : store.Scoped)
    {dependencies : List Variable} {term : Term Variable Literal Symbol}
    (within : ∀ name ∈ term.freeVars, store.Within dependencies name) :
    ∀ bindings : List (Variable × Term Variable Literal Symbol), (∀ binding ∈ bindings, binding ∈ store.bindings) →
      ∀ other ∈ (resolveWith bindings term).freeVars, store.Within dependencies other := by
  intro bindings
  induction bindings with
  | nil => intro _ other member; exact within other member
  | cons binding rest ih =>
      obtain ⟨name, value⟩ := binding
      intro included other member
      rw [resolveWith_cons] at member
      have older := ih (fun b m => included b (List.mem_cons_of_mem _ m))
      rcases Term.freeVars_instantiate_single member with ⟨inside, _⟩ | ⟨bound, inside⟩
      · exact older other inside
      · obtain ⟨own, ownEq, valueWithin⟩ := valid.answers _ value (included _ List.mem_cons_self)
        rcases older name bound with ⟨rigid, _⟩ | ⟨outer, flexible, contained⟩
        · rw [ownEq] at rigid; cases rigid
        · rw [ownEq] at flexible
          cases flexible
          exact (valueWithin other inside).mono contained

/-- Reading a term whose names are within a dependency set gives a term whose
names are within it and unbound: the answer scope propagates through every
alias and binding chain. -/
theorem Store.Scoped.resolve_within {store : Store Variable Literal Symbol} (valid : store.Scoped)
    {dependencies : List Variable} {term : Term Variable Literal Symbol}
    (within : ∀ name ∈ term.freeVars, store.Within dependencies name) :
    ∀ other ∈ (store.resolve term).freeVars, store.Within dependencies other ∧ store.binding? other = none :=
  fun other member => ⟨within_resolveWith valid within store.bindings (fun _ m => m) other member,
    lookup_eq_none.mpr (valid.triangular.resolve_unbound term other member)⟩

/-- A fully resolved answer mentions only unbound names: rigid names among its
name's dependencies, and flexible names depending only on them. -/
theorem Store.Scoped.resolve_answer {store : Store Variable Literal Symbol} (valid : store.Scoped)
    {name : Variable} {dependencies : List Variable} (flexible : store.info? name = some (.flexible dependencies)) :
    ∀ other ∈ (store.resolve (.var name)).freeVars, store.Within dependencies other ∧ store.binding? other = none :=
  valid.resolve_within fun other member => by
    simp only [Term.freeVars, List.mem_singleton] at member
    subst member
    exact .inr ⟨dependencies, flexible, fun _ inside => inside⟩

/-- A rigid name outside a flexible name's dependencies never occurs in its
resolved answer. -/
theorem Store.Scoped.not_mem_answer {store : Store Variable Literal Symbol} (valid : store.Scoped)
    {name : Variable} {dependencies : List Variable} (flexible : store.info? name = some (.flexible dependencies))
    {rigid : Variable} (isRigid : store.info? rigid = some .rigid) (outside : rigid ∉ dependencies) :
    rigid ∉ (store.resolve (.var name)).freeVars := by
  intro member
  rcases (valid.resolve_answer flexible rigid member).1 with ⟨_, inside⟩ | ⟨_, flexibleEq, _⟩
  · exact outside inside
  · rw [isRigid] at flexibleEq; cases flexibleEq

/-- A rigid name absent from a term and from the dependencies of its flexible
names is absent from its reading: the freshness `Derives` checks for an opened
name survives reading the obligation through later answers. -/
theorem Store.Scoped.fresh_resolve {store : Store Variable Literal Symbol} (valid : store.Scoped)
    {opened : Variable} (isRigid : store.info? opened = some .rigid) {term : Term Variable Literal Symbol}
    (outside : ∀ name ∈ term.freeVars, name ≠ opened ∧
      ∀ dependencies, store.info? name = some (.flexible dependencies) → opened ∉ dependencies) :
    opened ∉ (store.resolve term).freeVars := by
  intro member
  obtain ⟨name, nameMember, occurs⟩ := resolveWith_freeVars store.bindings opened member
  have ⟨different, independent⟩ := outside name nameMember
  -- A name that is not flexible is never bound, so it reads as itself.
  have readsItself (notFlexible : ∀ dependencies, store.info? name ≠ some (.flexible dependencies)) : False := by
    rw [show resolveWith store.bindings (.var name) = .var name from
      store.resolve_unbound (valid.unbound notFlexible)] at occurs
    simp only [Term.freeVars, List.mem_singleton] at occurs
    exact different occurs.symm
  cases info : store.info? name with
  | none => exact readsItself fun _ equal => by rw [info] at equal; cases equal
  | some found =>
      cases found with
      | rigid => exact readsItself fun _ equal => by rw [info] at equal; cases equal
      | flexible dependencies => exact valid.not_mem_answer info isRigid (independent dependencies info) occurs

/-- `name` may open a quantifier of the obligation read through `store`: it is
unbound there and absent from the read goal and the read assumptions. These are
the freshness conditions `Derives` checks; binders impose nothing, since an
opening renames a binder that would capture. -/
structure Obligation.FreshUnder (store : Store Variable Literal Symbol)
    (obligation : Obligation Variable Literal Symbol) (name : Variable) : Prop where
  unbound : name ∉ store.bindings.map Prod.fst
  goal : name ∉ (store.resolve obligation.goal).freeVars
  context : FreshForContext name (obligation.context.map store.resolve)

/-- A rigid name opened by a commit is absent from the reading, in a later
scoped refinement, of a term whose names the committed store declares and that
does not name it itself. -/
private theorem commit_fresh_term {store next later : Store Variable Literal Symbol}
    (valid : store.Scoped) {obligation : Obligation Variable Literal Symbol} {flexibles rigids : List Variable}
    {premises : List (Premise Variable Literal Symbol)} {bindings : List (Variable × Term Variable Literal Symbol)}
    {woken : List (Suspension Variable Literal Symbol)}
    (committed : store.commit obligation flexibles rigids premises bindings = .committed next woken)
    (refines : next.Refines later) (laterScoped : later.Scoped)
    {opened : Variable} (member : opened ∈ rigids) {term : Term Variable Literal Symbol}
    (names : ∀ name ∈ term.freeVars, name ≠ opened ∧ next.info? name ≠ none) :
    opened ∉ (later.resolve term).freeVars := by
  refine laterScoped.fresh_resolve (refines.rigid opened (Store.commit_rigid committed member))
    fun name nameMember => ⟨(names name nameMember).1, fun dependencies flexible => ?_⟩
  cases info : next.info? name with
  | none => exact absurd info (names name nameMember).2
  | some found =>
      cases found with
      | rigid => rw [refines.rigid name info] at flexible; cases flexible
      | flexible own =>
          obtain ⟨final, finalEq, contained⟩ := refines.flexible name own info
          rw [finalEq] at flexible; cases flexible
          exact fun inside => Store.commit_independent valid committed member info (contained opened inside)

/-- A rigid name opened by a commit never occurs in the resolved answer of a
flexible name that existed before the commit, in the committed store or in any
store refining it: an eigenvariable or opened witness cannot escape its scope
through any chain of answers. -/
theorem Store.commit_no_escape_resolved {store next later : Store Variable Literal Symbol}
    (valid : store.Scoped) {obligation : Obligation Variable Literal Symbol} {flexibles rigids : List Variable}
    {premises : List (Premise Variable Literal Symbol)} {bindings : List (Variable × Term Variable Literal Symbol)}
    {woken : List (Suspension Variable Literal Symbol)}
    (committed : store.commit obligation flexibles rigids premises bindings = .committed next woken)
    (refines : next.Refines later) (laterScoped : later.Scoped)
    {opened : Variable} (member : opened ∈ rigids) {name : Variable} {dependencies : List Variable}
    (existing : store.info? name = some (.flexible dependencies)) :
    opened ∉ (later.resolve (.var name)).freeVars := by
  have present : store.info? name ≠ none := by rw [existing]; exact Option.some_ne_none _
  have undeclared := Store.commit_fresh committed opened (List.mem_append_right _ member)
  refine commit_fresh_term valid committed refines laterScoped member fun other inside => ?_
  simp only [Term.freeVars, List.mem_singleton] at inside
  subst inside
  exact ⟨fun same => present (same ▸ undeclared), (Store.commit_refines committed).declared present⟩

/-- A rigid name opened by a commit may open a quantifier in every later
scoped store refining the commit: it is unbound there, and absent from the read
goal and context of the obligation and of every premise that does not open it
(for `existsElim`, the opened existential). The obligation's names are declared
by the name invariant and the premises' names by the commit, so no per-term
hypothesis is needed. -/
theorem Store.commit_fresh_resolved {store next later : Store Variable Literal Symbol}
    (valid : store.Scoped) {obligation : Obligation Variable Literal Symbol} {flexibles rigids : List Variable}
    {premises : List (Premise Variable Literal Symbol)} {bindings : List (Variable × Term Variable Literal Symbol)}
    (declared : obligation.Declared store)
    {woken : List (Suspension Variable Literal Symbol)}
    (committed : store.commit obligation flexibles rigids premises bindings = .committed next woken)
    (refines : next.Refines later) (laterScoped : later.Scoped) {opened : Variable} (member : opened ∈ rigids) :
    obligation.FreshUnder later opened ∧
      ∀ premise ∈ premises, opened ∉ premise.discharge.rigids → (obligation.premise premise).FreshUnder later opened := by
  obtain ⟨⟨_, fresh, _, _, admitted⟩, bound, boundEq, nextEq, _⟩ := Store.commit_checks committed
  have undeclared := fresh opened (List.mem_append_right _ member)
  have rigid := refines.rigid opened (Store.commit_rigid committed member)
  have old : ∀ name, store.info? name ≠ none → name ≠ opened ∧ next.info? name ≠ none :=
    fun name present => ⟨fun same => present (same ▸ undeclared), (Store.commit_refines committed).declared present⟩
  have freshUnder : ∀ target : Obligation Variable Literal Symbol,
      (∀ name ∈ target.freeVars, name ≠ opened ∧ next.info? name ≠ none) → target.FreshUnder later opened := by
    intro target names
    refine ⟨laterScoped.unbound (fun dependencies flexible => by rw [rigid] at flexible; cases flexible),
      commit_fresh_term valid committed refines laterScoped member
        (fun name inside => names name (List.mem_append_left _ inside)), fun read readMember => ?_⟩
    obtain ⟨assumption, assumptionMember, rfl⟩ := List.mem_map.mp readMember
    exact commit_fresh_term valid committed refines laterScoped member fun name inside =>
      names name (List.mem_append_right _ (List.mem_flatMap.mpr ⟨assumption, assumptionMember, inside⟩))
  refine ⟨freshUnder obligation fun name inside => old name (declared name inside),
    fun premise premiseMember outside => freshUnder _ fun name inside => ?_⟩
  rcases Obligation.mem_premise_freeVars.mp inside with own | context
  · exact ⟨fun same => Store.commit_fresh_premise committed member premiseMember outside (same ▸ own),
      nextEq ▸ ((Store.bindAll_refines boundEq).trans (.wake bound)).declared
        (Store.inScope_within (admitted premise premiseMember name own)).declared⟩
  · exact old name (declared name (List.mem_append_right _ context))

end Scope

/-! ## Fresh names for a clause use -/

section Fresh

variable [FreshNames Variable]

/-- Fresh flexible names for the templates of one clause use: distinct,
undeclared, and absent from the templates and from `avoid`. They pass the
commit's freshness check, and by the name invariant they are fresh for every
obligation the store reads. -/
def Store.freshen (store : Store Variable Literal Symbol) (templates : List Variable) (avoid : List Variable := []) :
    List (Variable × Variable) :=
  freshenNames (store.names.map Prod.fst ++ avoid) templates

omit [DecidableEq Variable] in
theorem Store.freshen_fst (store : Store Variable Literal Symbol) (templates avoid : List Variable) :
    (store.freshen templates avoid).map Prod.fst = templates :=
  freshenNames_fst _ _

omit [DecidableEq Variable] in
theorem Store.freshen_nodup (store : Store Variable Literal Symbol) (templates avoid : List Variable) :
    ((store.freshen templates avoid).map Prod.snd).Nodup := by
  rw [Store.freshen, freshenNames_snd]; exact freshNames_nodup _ _

theorem Store.freshen_fresh (store : Store Variable Literal Symbol) (templates avoid : List Variable) :
    ∀ name ∈ (store.freshen templates avoid).map Prod.snd,
      store.info? name = none ∧ name ∉ templates ∧ name ∉ avoid := by
  intro name member
  rw [Store.freshen, freshenNames_snd] at member
  have outside := freshNames_avoid _ _ name member
  simp only [List.mem_append, not_or] at outside
  exact ⟨lookup_eq_none.mpr outside.2.1, outside.1, outside.2.2⟩

/-- Binder names of the obligation's goal and assumptions as read through the
store. The commit needs only store freshness, but a strategy that matches
syntactically should also avoid these when it picks new names: an opening, or a
later reading, then renames no binder into an alpha-variant that `Store.unify`
reports as unsupported. -/
def Store.readBinders (store : Store Variable Literal Symbol) (obligation : Obligation Variable Literal Symbol) :
    List Variable :=
  (store.resolve obligation.goal :: obligation.context.map store.resolve).flatMap Term.binderNames

end Fresh

end AnthillModKbSpec.Machine
