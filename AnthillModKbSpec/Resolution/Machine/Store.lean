import AnthillModKbSpec.Foundation.Derivation
import AnthillModKbSpec.Foundation.ClauseInstantiation
import AnthillModKbSpec.Foundation.OperationDictionaries

namespace AnthillModKbSpec.Machine

open OperationDictionaries (lookup lookup_eq_none)

/-- A declared name. Rigid names are fixed parameters: the query's own, universal
eigenvariables, and witnesses opened from existential assumptions. No transition
assigns them. A flexible name is a shared answer metavariable; it lists the rigid
names its answer may mention, those in scope where it was created, narrowed when
it is placed in another flexible name's answer. These dependency sets are the
exact form of universe levels (Qi §4.2): a level number orders nested scopes but
cannot separate two sibling scopes of the same depth. -/
inductive NameInfo (Variable : Type) where
  | rigid
  | flexible (dependencies : List Variable)
  deriving DecidableEq, Repr

variable {Variable Literal Symbol : Type}

/-- Shared answer state, threaded through AND branches and restored on
backtracking. `names` declares every name introduced so far, including the
query's own. `bindings` is triangular, newest first: each right-hand side was
resolved against the older bindings when committed, so it mentions no name
bound before it. Commits only prepend; rollback restores a saved store. -/
structure Store (Variable Literal Symbol : Type) where
  names : List (Variable × NameInfo Variable)
  bindings : List (Variable × Term Variable Literal Symbol)

/-- The local scope of one obligation. Assumptions are formulas with fixed free
names, not clause templates; `rigids` lists the rigid names in scope. -/
structure Scope (Variable Literal Symbol : Type) where
  rigids : List Variable
  assumptions : ProofContext Variable Literal Symbol

/-- What one premise adds to its parent's scope. At the parent's node these
assumptions are discharged and these rigid names go out of scope. -/
structure Discharge (Variable Literal Symbol : Type) where
  assumptions : ProofContext Variable Literal Symbol := []
  rigids : List Variable := []

/-- A premise obligation of a rule application, relative to the parent scope. -/
structure Premise (Variable Literal Symbol : Type) where
  discharge : Discharge Variable Literal Symbol := {}
  goal : Formula Variable Literal Symbol

/-- An obligation `Gamma; Scope |- goal`. The goal may mention flexible names;
its meaning is the goal instantiated by the final answer bindings. -/
structure Obligation (Variable Literal Symbol : Type) where
  scope : Scope Variable Literal Symbol
  goal : Formula Variable Literal Symbol

def Scope.enter (scope : Scope Variable Literal Symbol) (discharge : Discharge Variable Literal Symbol) :
    Scope Variable Literal Symbol :=
  ⟨discharge.rigids ++ scope.rigids, discharge.assumptions ++ scope.assumptions⟩

/-- A premise's obligation is computed from its parent's scope alone, so
assumptions proved or opened in a sibling never reach it. -/
def Obligation.premise (obligation : Obligation Variable Literal Symbol)
    (premise : Premise Variable Literal Symbol) : Obligation Variable Literal Symbol :=
  ⟨obligation.scope.enter premise.discharge, premise.goal⟩

def Obligation.context (obligation : Obligation Variable Literal Symbol) : ProofContext Variable Literal Symbol :=
  obligation.scope.assumptions

def Obligation.root (rigids : List Variable) (context : ProofContext Variable Literal Symbol)
    (goal : Formula Variable Literal Symbol) : Obligation Variable Literal Symbol :=
  ⟨⟨rigids, context⟩, goal⟩

@[simp] theorem Obligation.premise_context (obligation : Obligation Variable Literal Symbol)
    (premise : Premise Variable Literal Symbol) :
    (obligation.premise premise).context = premise.discharge.assumptions ++ obligation.context := rfl

/-- Result of committing a candidate's names and bindings. `rejected` is a
candidate miss: the binding fails the occurs check or would let a rigid name
escape the scope of the name it is bound to. `violated` means the command broke
the machine contract (a name that is not fresh, a premise naming an undeclared
name or a rigid name outside its scope, an unresolved value, a rigid name
outside the scope, an assigned rigid, a rebound answer); it also abandons the
candidate but is recorded as a gap, never as failure. -/
inductive Commit (Variable Literal Symbol : Type) where
  | committed (store : Store Variable Literal Symbol)
  | rejected
  | violated

variable [DecidableEq Variable]

def Store.info? (store : Store Variable Literal Symbol) (name : Variable) : Option (NameInfo Variable) :=
  lookup store.names name

def Store.binding? (store : Store Variable Literal Symbol) (name : Variable) :
    Option (Term Variable Literal Symbol) :=
  lookup store.bindings name

/-- Free names of the obligation's goal and assumptions. Bound names are not
among them: an opening renames a binder that would capture. -/
def Obligation.freeVars (obligation : Obligation Variable Literal Symbol) : List Variable :=
  obligation.goal.freeVars ++ obligation.context.flatMap Term.freeVars

/-- Free names of a premise's goal and of the assumptions it discharges. -/
def Premise.freeVars (premise : Premise Variable Literal Symbol) : List Variable :=
  premise.goal.freeVars ++ premise.discharge.assumptions.flatMap Term.freeVars

/-- The machine's name invariant: every free name of the obligation is declared
in the store it is read through. A name the store has not declared is then
fresh for the obligation, whatever its binders (`Obligation.Declared.fresh`). -/
def Obligation.Declared (store : Store Variable Literal Symbol) (obligation : Obligation Variable Literal Symbol) :
    Prop :=
  ∀ name ∈ obligation.freeVars, store.info? name ≠ none

theorem Obligation.mem_premise_freeVars {obligation : Obligation Variable Literal Symbol}
    {premise : Premise Variable Literal Symbol} {name : Variable} :
    name ∈ (obligation.premise premise).freeVars ↔
      name ∈ premise.freeVars ∨ name ∈ obligation.context.flatMap Term.freeVars := by
  simp [Obligation.freeVars, Premise.freeVars, Obligation.premise, Obligation.context, Scope.enter, or_assoc]

/-- A name the store has not declared gives the freshness conditions `Derives`
checks for opening the goal of an obligation whose names it declares. -/
theorem Obligation.Declared.fresh {store : Store Variable Literal Symbol}
    {obligation : Obligation Variable Literal Symbol} (declared : obligation.Declared store) {name : Variable}
    (undeclared : store.info? name = none) :
    FreshForContext name obligation.context ∧ name ∉ obligation.goal.freeVars :=
  ⟨fun assumption member free =>
      declared name (List.mem_append_right _ (List.mem_flatMap.mpr ⟨assumption, member, free⟩)) undeclared,
    fun free => declared name (List.mem_append_left _ free) undeclared⟩

theorem Obligation.Declared.mono {store later : Store Variable Literal Symbol}
    {obligation : Obligation Variable Literal Symbol} (declared : obligation.Declared store)
    (grows : ∀ name, store.info? name ≠ none → later.info? name ≠ none) : obligation.Declared later :=
  fun name member => grows name (declared name member)

def Store.declare (store : Store Variable Literal Symbol) (info : NameInfo Variable) (names : List Variable) :
    Store Variable Literal Symbol :=
  { store with names := names.map (fun name => (name, info)) ++ store.names }

/-- A name not declared in the store and not in `avoid`. The commit accepts it
as a new name; by the name invariant it is fresh for every obligation the
store reads. -/
def Store.freshFor [FreshNames Variable] (store : Store Variable Literal Symbol) (avoid : List Variable := []) :
    Variable :=
  FreshNames.fresh (store.names.map Prod.fst ++ avoid)

theorem Store.freshFor_fresh [FreshNames Variable] (store : Store Variable Literal Symbol) (avoid : List Variable) :
    store.info? (store.freshFor avoid) = none ∧ store.freshFor avoid ∉ avoid := by
  have outside := FreshNames.fresh_not_mem (store.names.map Prod.fst ++ avoid)
  simp only [List.mem_append, not_or] at outside
  exact ⟨lookup_eq_none.mpr outside.1, outside.2⟩

/-- Restrict the dependencies of the flexible names among `targets`. -/
def narrowInfo (targets allowed : List Variable) (name : Variable) : NameInfo Variable → NameInfo Variable
  | .flexible own => if name ∈ targets then .flexible (own.filter (· ∈ allowed)) else .flexible own
  | .rigid => .rigid

def Store.narrow (store : Store Variable Literal Symbol) (targets allowed : List Variable) :
    Store Variable Literal Symbol :=
  { store with names := store.names.map (fun entry => (entry.1, narrowInfo targets allowed entry.1 entry.2)) }

/-- A name may occur in a committed value: a rigid name in this scope, or a
declared flexible name that is still unbound (the value is resolved). -/
def Store.usable (store : Store Variable Literal Symbol) (scope : Scope Variable Literal Symbol)
    (name : Variable) : Bool :=
  match store.info? name with
  | some .rigid => decide (name ∈ scope.rigids)
  | some (.flexible _) => (store.binding? name).isNone
  | none => false

/-- A rigid name may enter an answer only if the bound name depends on it. -/
def Store.allowed (store : Store Variable Literal Symbol) (dependencies : List Variable) (name : Variable) : Bool :=
  match store.info? name with
  | some .rigid => decide (name ∈ dependencies)
  | _ => true

def isName : Term Variable Literal Symbol → Variable → Bool
  | .var other, name => decide (other = name)
  | _, _ => false

/-- Bind one unbound flexible name to a resolved value. Binding a name to itself
changes nothing. Otherwise the occurs and dependency checks apply, and the
flexible names in the value inherit the bound name's dependencies. -/
def Store.bind (store : Store Variable Literal Symbol) (scope : Scope Variable Literal Symbol)
    (name : Variable) (value : Term Variable Literal Symbol) : Commit Variable Literal Symbol :=
  match store.info? name, store.binding? name with
  | some (.flexible dependencies), none =>
      if isName value name then .committed store
      else
        let free := value.freeVars
        if free.all (store.usable scope) then
          if name ∉ free ∧ free.all (store.allowed dependencies) then
            .committed { (store.narrow free dependencies) with bindings := (name, value) :: store.bindings }
          else .rejected
        else .violated
  | _, _ => .violated

def Store.bindAll (store : Store Variable Literal Symbol) (scope : Scope Variable Literal Symbol) :
    List (Variable × Term Variable Literal Symbol) → Commit Variable Literal Symbol
  | [] => .committed store
  | (name, value) :: rest =>
      match store.bind scope name value with
      | .committed next => next.bindAll scope rest
      | .rejected => .rejected
      | .violated => .violated

/-- The store a candidate's bindings are committed against: its flexible names
declared, depending on the obligation's rigid names, then its premises' rigid
names. A command matching for a candidate matches against this store. -/
def Store.prepare (store : Store Variable Literal Symbol) (obligation : Obligation Variable Literal Symbol)
    (flexibles rigids : List Variable) : Store Variable Literal Symbol :=
  (store.declare (.flexible obligation.scope.rigids) flexibles).declare .rigid rigids

/-- `other` is within a set of rigid names: a rigid name among them, or a
flexible name depending only on them. An answer mentions only names within its
name's dependencies; a premise mentions only names within its scope. -/
def Store.Within (store : Store Variable Literal Symbol) (dependencies : List Variable) (other : Variable) : Prop :=
  (store.info? other = some .rigid ∧ other ∈ dependencies) ∨
    ∃ own, store.info? other = some (.flexible own) ∧ ∀ rigid ∈ own, rigid ∈ dependencies

/-- Decides `Store.Within`. -/
def Store.inScope (store : Store Variable Literal Symbol) (rigids : List Variable) (name : Variable) : Bool :=
  match store.info? name with
  | some .rigid => decide (name ∈ rigids)
  | some (.flexible own) => own.all (· ∈ rigids)
  | none => false

theorem Store.inScope_within {store : Store Variable Literal Symbol} {rigids : List Variable} {name : Variable}
    (inside : store.inScope rigids name = true) : store.Within rigids name := by
  unfold Store.inScope at inside
  split at inside
  · rename_i rigidEq; exact .inl ⟨rigidEq, by simpa using inside⟩
  · rename_i own flexibleEq
    exact .inr ⟨own, flexibleEq, fun rigid member => by simpa using List.all_eq_true.mp inside rigid member⟩
  · cases inside

/-- Every free name of the premises is within the premise's scope in the
prepared store: a rigid name of the obligation or one the premise opens, or a
flexible name depending only on those. In particular it is declared. A rigid
name opened for one premise is out of scope in its siblings, and a rigid name
that went out of scope cannot return through a premise, written or through a
flexible name created in its scope. -/
def Store.Admits (prepared : Store Variable Literal Symbol) (obligation : Obligation Variable Literal Symbol)
    (premises : List (Premise Variable Literal Symbol)) : Prop :=
  ∀ premise ∈ premises, ∀ name ∈ premise.freeVars,
    prepared.inScope (premise.discharge.rigids ++ obligation.scope.rigids) name = true

instance (prepared : Store Variable Literal Symbol) (obligation : Obligation Variable Literal Symbol)
    (premises : List (Premise Variable Literal Symbol)) : Decidable (prepared.Admits obligation premises) := by
  unfold Store.Admits; infer_instance

/-- The checks a commit makes before binding: the candidate's new names are
distinct and undeclared, the obligation's rigid names are declared rigid, every
rigid name a premise opens is one of the new names, and the prepared store
admits the premises. -/
def Store.Accepts (store : Store Variable Literal Symbol) (obligation : Obligation Variable Literal Symbol)
    (flexibles rigids : List Variable) (premises : List (Premise Variable Literal Symbol)) : Prop :=
  (flexibles ++ rigids).Nodup ∧ (∀ name ∈ flexibles ++ rigids, store.info? name = none) ∧
    (∀ name ∈ obligation.scope.rigids, store.info? name = some .rigid) ∧
    (∀ premise ∈ premises, ∀ name ∈ premise.discharge.rigids, name ∈ rigids) ∧
    (store.prepare obligation flexibles rigids).Admits obligation premises

instance (store : Store Variable Literal Symbol) (obligation : Obligation Variable Literal Symbol)
    (flexibles rigids : List Variable) (premises : List (Premise Variable Literal Symbol)) :
    Decidable (store.Accepts obligation flexibles rigids premises) := by
  unfold Store.Accepts; infer_instance

/-- Commit one candidate for an obligation: check its names and premises
(`Store.Accepts`); declare the new flexible names, depending on the
obligation's rigid names, and the premises' rigid names; then bind. Bindings
may use the new flexible names but not the premises' rigid names. A new name
may equal a binder name of the obligation: openings rename binders. -/
def Store.commit (store : Store Variable Literal Symbol) (obligation : Obligation Variable Literal Symbol)
    (flexibles rigids : List Variable) (premises : List (Premise Variable Literal Symbol))
    (bindings : List (Variable × Term Variable Literal Symbol)) : Commit Variable Literal Symbol :=
  if store.Accepts obligation flexibles rigids premises then
    (store.prepare obligation flexibles rigids).bindAll obligation.scope bindings
  else .violated

/-- Resolution by the binding chain, oldest binding applied first. -/
inductive Resolves : List (Variable × Term Variable Literal Symbol) →
    Term Variable Literal Symbol → Term Variable Literal Symbol → Prop where
  | nil : Resolves [] term term
  | cons (older : Resolves rest term middle)
      (newest : Substitutes (Substitution.single name value) middle result) :
      Resolves ((name, value) :: rest) term result

section Resolution

variable [FreshNames Variable]

/-- Apply bindings, oldest first. A value that a binder would capture renames
the binder (`Term.instantiate`), so resolution never fails on a capture hazard. -/
def resolveWith (bindings : List (Variable × Term Variable Literal Symbol))
    (term : Term Variable Literal Symbol) : Term Variable Literal Symbol :=
  bindings.foldr (fun binding resolved => resolved.instantiate (Substitution.single binding.1 binding.2)) term

/-- Read a term through the committed answers. Pending goals and the local
assumptions they captured are stored as written and read this way when focused
or exported, so a later binding reaches them without rewriting the state. -/
def Store.resolve (store : Store Variable Literal Symbol) (term : Term Variable Literal Symbol) :
    Term Variable Literal Symbol :=
  resolveWith store.bindings term

theorem resolveWith_sound (bindings : List (Variable × Term Variable Literal Symbol))
    (term : Term Variable Literal Symbol) : Resolves bindings term (resolveWith bindings term) := by
  induction bindings with
  | nil => exact .nil
  | cons binding rest ih =>
      obtain ⟨name, value⟩ := binding
      exact .cons ih (Term.instantiate_substitutes _ _)

/-- Resolution by the committed bindings is a chain of capture-avoiding substitutions. -/
theorem Store.resolve_sound (store : Store Variable Literal Symbol) (term : Term Variable Literal Symbol) :
    Resolves store.bindings term (store.resolve term) :=
  resolveWith_sound store.bindings term

end Resolution

/-! ## Association lists -/

theorem lookup_append_of_not_mem {α : Type} (front back : List (Variable × α)) {name : Variable}
    (absent : name ∉ front.map Prod.fst) : lookup (front ++ back) name = lookup back name := by
  induction front with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      simp only [List.cons_append, lookup, Ne.symm absent.1, ite_false, ih absent.2]

theorem lookup_declared {α : Type} (names : List Variable) (value : α) (back : List (Variable × α))
    (name : Variable) (member : name ∈ names) :
    lookup (names.map (fun candidate => (candidate, value)) ++ back) name = some value := by
  induction names with
  | nil => cases member
  | cons candidate rest ih =>
      by_cases same : candidate = name
      · simp [lookup, same]
      · simp only [List.mem_cons] at member
        simp only [List.map_cons, List.cons_append, lookup, same, ite_false]
        exact ih (member.resolve_left (Ne.symm same))

theorem lookup_undeclared {α : Type} (names : List Variable) (value : α) (back : List (Variable × α))
    {name : Variable} (absent : name ∉ names) :
    lookup (names.map (fun candidate => (candidate, value)) ++ back) name = lookup back name :=
  lookup_append_of_not_mem _ _ (by simpa using absent)

theorem lookup_map_keyed {α β : Type} (entries : List (Variable × α)) (f : Variable → α → β) (name : Variable) :
    lookup (entries.map (fun entry => (entry.1, f entry.1 entry.2))) name =
      (lookup entries name).map (f name) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      by_cases same : candidate = name
      · subst candidate; simp [lookup]
      · simp [lookup, same, ih]

theorem lookup_isSome_of_mem {α : Type} {entries : List (Variable × α)} {name : Variable} {value : α}
    (member : (name, value) ∈ entries) : (lookup entries name).isSome := by
  induction entries with
  | nil => cases member
  | cons entry rest ih =>
      obtain ⟨candidate, other⟩ := entry
      by_cases same : candidate = name
      · simp [lookup, same]
      · simp only [List.mem_cons, Prod.mk.injEq] at member
        simp only [lookup, same, ite_false]
        exact ih (member.resolve_left (fun equal => same equal.1.symm))

theorem lookup_mem {α : Type} {entries : List (Variable × α)} {name : Variable} {value : α}
    (found : lookup entries name = some value) : (name, value) ∈ entries := by
  induction entries with
  | nil => cases found
  | cons entry rest ih =>
      obtain ⟨candidate, other⟩ := entry
      by_cases same : candidate = name
      · simp only [lookup, same, ite_true, Option.some.injEq] at found
        subst same found
        simp
      · simp only [lookup, same, ite_false] at found
        exact List.mem_cons_of_mem _ (ih found)

/-! ## Commit specification -/

theorem Store.info?_declare (store : Store Variable Literal Symbol) (info : NameInfo Variable)
    (names : List Variable) (name : Variable) :
    (store.declare info names).info? name = if name ∈ names then some info else store.info? name := by
  by_cases member : name ∈ names
  · simp only [member, ite_true]; exact lookup_declared _ _ _ _ member
  · simp only [member, ite_false]; exact lookup_undeclared _ _ _ member

/-- Declaring new names leaves every already declared name as it was. -/
theorem Store.info?_declare_of_ne_none {store : Store Variable Literal Symbol} {info : NameInfo Variable}
    {names : List Variable} (fresh : ∀ name ∈ names, store.info? name = none) {name : Variable}
    (present : store.info? name ≠ none) : (store.declare info names).info? name = store.info? name := by
  rw [Store.info?_declare]
  split
  · rename_i member; exact absurd (fresh name member) present
  · rfl

/-- A candidate's rigid names are still undeclared once its flexible names are. -/
theorem Store.declare_keeps_fresh {store : Store Variable Literal Symbol} {info : NameInfo Variable}
    {flexibles rigids : List Variable} (distinct : (flexibles ++ rigids).Nodup)
    (fresh : ∀ name ∈ flexibles ++ rigids, store.info? name = none) :
    ∀ name ∈ rigids, (store.declare info flexibles).info? name = none := by
  intro name member
  have notFlexible : name ∉ flexibles := fun flexible =>
    (List.nodup_append.mp distinct).2.2 name flexible name member rfl
  rw [Store.info?_declare]
  simp only [notFlexible, ite_false]
  exact fresh name (List.mem_append_right _ member)

theorem Store.info?_narrow (store : Store Variable Literal Symbol) (targets allowed : List Variable)
    (name : Variable) :
    (store.narrow targets allowed).info? name = (store.info? name).map (narrowInfo targets allowed name) :=
  lookup_map_keyed store.names (narrowInfo targets allowed) name

theorem narrowInfo_flexible {targets allowed : List Variable} {name : Variable} {info : NameInfo Variable}
    {narrowed : List Variable} (equal : narrowInfo targets allowed name info = .flexible narrowed) :
    ∃ own, info = .flexible own ∧ ∀ rigid ∈ narrowed, rigid ∈ own := by
  cases info with
  | rigid => cases equal
  | flexible own =>
      refine ⟨own, rfl, ?_⟩
      by_cases target : name ∈ targets
      · simp only [narrowInfo, target, ite_true, NameInfo.flexible.injEq] at equal
        subst equal
        exact fun rigid member => (List.mem_filter.mp member).1
      · simp only [narrowInfo, target, ite_false, NameInfo.flexible.injEq] at equal
        subst equal
        exact fun _ member => member

theorem Store.bind_committed {store next : Store Variable Literal Symbol} {scope : Scope Variable Literal Symbol}
    {name : Variable} {value : Term Variable Literal Symbol}
    (committed : store.bind scope name value = .committed next) :
    ∃ dependencies, store.info? name = some (.flexible dependencies) ∧ store.binding? name = none ∧
      ((isName value name = true ∧ next = store) ∨
        (next = { (store.narrow value.freeVars dependencies) with bindings := (name, value) :: store.bindings } ∧
          name ∉ value.freeVars ∧ ∀ other ∈ value.freeVars,
            store.usable scope other = true ∧ store.allowed dependencies other = true)) := by
  unfold Store.bind at committed
  split at committed
  · rename_i dependencies infoEq boundEq
    refine ⟨dependencies, infoEq, boundEq, ?_⟩
    split at committed
    · rename_i trivial
      cases committed
      exact .inl ⟨trivial, rfl⟩
    · dsimp only at committed
      split at committed
      · rename_i usable
        split at committed
        · rename_i checks
          cases committed
          exact .inr ⟨rfl, checks.1, fun other member =>
            ⟨List.all_eq_true.mp usable other member, List.all_eq_true.mp checks.2 other member⟩⟩
        · cases committed
      · cases committed
  · cases committed

/-- A committed binding mentions only rigid names that are in the obligation's
scope and among the bound name's dependencies: a rigid name cannot escape into
the answer of a name created outside its scope. -/
theorem Store.bind_respects_scope {store next : Store Variable Literal Symbol}
    {scope : Scope Variable Literal Symbol} {name : Variable} {value : Term Variable Literal Symbol}
    (committed : store.bind scope name value = .committed next) :
    ∃ dependencies, store.info? name = some (.flexible dependencies) ∧
      ∀ other ∈ value.freeVars, store.info? other = some .rigid →
        other ∈ scope.rigids ∧ other ∈ dependencies := by
  obtain ⟨dependencies, infoEq, _, outcome⟩ := Store.bind_committed committed
  refine ⟨dependencies, infoEq, fun other member rigidEq => ?_⟩
  rcases outcome with ⟨trivial, _⟩ | ⟨_, _, checks⟩
  · cases value with
    | var bound =>
        simp only [isName, decide_eq_true_eq] at trivial
        subst bound
        simp only [Term.freeVars, List.mem_singleton] at member
        subst other
        rw [infoEq] at rigidEq
        cases rigidEq
    | _ => simp [isName] at trivial
  · have ⟨usable, allowed⟩ := checks other member
    simp only [Store.usable, rigidEq, decide_eq_true_eq] at usable
    simp only [Store.allowed, rigidEq, decide_eq_true_eq] at allowed
    exact ⟨usable, allowed⟩

/-- An already bound name is never rebound: a later AND sibling cannot replace
an earlier sibling's answer. -/
theorem Store.bind_bound {store : Store Variable Literal Symbol} {scope : Scope Variable Literal Symbol}
    {name : Variable} {value existing : Term Variable Literal Symbol}
    (bound : store.binding? name = some existing) : store.bind scope name value = .violated := by
  unfold Store.bind
  split
  · rename_i none
    rw [bound] at none
    cases none
  · rfl

theorem Store.bindAll_extends {store next : Store Variable Literal Symbol}
    {scope : Scope Variable Literal Symbol} {bindings : List (Variable × Term Variable Literal Symbol)}
    (committed : store.bindAll scope bindings = .committed next) :
    ∃ added, next.bindings = added ++ store.bindings ∧ ∀ binding ∈ added, binding ∈ bindings := by
  induction bindings generalizing store with
  | nil => cases committed; exact ⟨[], rfl, by simp⟩
  | cons binding rest ih =>
      obtain ⟨name, value⟩ := binding
      simp only [Store.bindAll] at committed
      split at committed
      · rename_i middle bound
        obtain ⟨added, sameBindings, fromRest⟩ := ih committed
        obtain ⟨_, _, _, outcome⟩ := Store.bind_committed bound
        rcases outcome with ⟨_, rfl⟩ | ⟨rfl, _, _⟩
        · exact ⟨added, sameBindings, fun b member => List.mem_cons_of_mem _ (fromRest b member)⟩
        · refine ⟨added ++ [(name, value)], by simp [sameBindings], fun b member => ?_⟩
          simp only [List.mem_append, List.mem_singleton] at member
          rcases member with member | rfl
          · exact List.mem_cons_of_mem _ (fromRest b member)
          · exact List.mem_cons_self
      · cases committed
      · cases committed

/-- A committed candidate passed every check of the commit, and its bindings
were committed against the prepared store. -/
theorem Store.commit_checks {store next : Store Variable Literal Symbol}
    {obligation : Obligation Variable Literal Symbol} {flexibles rigids : List Variable}
    {premises : List (Premise Variable Literal Symbol)} {bindings : List (Variable × Term Variable Literal Symbol)}
    (committed : store.commit obligation flexibles rigids premises bindings = .committed next) :
    store.Accepts obligation flexibles rigids premises ∧
      (store.prepare obligation flexibles rigids).bindAll obligation.scope bindings = .committed next := by
  unfold Store.commit at committed
  split at committed
  · rename_i checks; exact ⟨checks, committed⟩
  · cases committed

/-- Commits only add bindings, each one proposed by the candidate: the answers
of earlier AND siblings survive. -/
theorem Store.commit_extends {store next : Store Variable Literal Symbol}
    {obligation : Obligation Variable Literal Symbol} {flexibles rigids : List Variable}
    {premises : List (Premise Variable Literal Symbol)} {bindings : List (Variable × Term Variable Literal Symbol)}
    (committed : store.commit obligation flexibles rigids premises bindings = .committed next) :
    ∃ added, next.bindings = added ++ store.bindings ∧ ∀ binding ∈ added, binding ∈ bindings := by
  simpa [Store.prepare, Store.declare] using Store.bindAll_extends (Store.commit_checks committed).2

/-- Every name a commit opens is new to the store. By the name invariant it is
then fresh for the obligation's free names; binder names impose nothing. -/
theorem Store.commit_fresh {store next : Store Variable Literal Symbol}
    {obligation : Obligation Variable Literal Symbol} {flexibles rigids : List Variable}
    {premises : List (Premise Variable Literal Symbol)} {bindings : List (Variable × Term Variable Literal Symbol)}
    (committed : store.commit obligation flexibles rigids premises bindings = .committed next) :
    ∀ name ∈ flexibles ++ rigids, store.info? name = none :=
  (Store.commit_checks committed).1.2.1

/-! ## Scope invariant -/

/-- Bindings in commit order, newest first: no name is bound twice, and each
value mentions neither its own name nor a name bound before it. Resolution,
oldest first, therefore leaves no bound name. -/
inductive Triangular : List (Variable × Term Variable Literal Symbol) → Prop where
  | nil : Triangular []
  | cons {name : Variable} {value : Term Variable Literal Symbol}
      {older : List (Variable × Term Variable Literal Symbol)}
      (unbound : name ∉ older.map Prod.fst)
      (resolved : ∀ other ∈ value.freeVars, other ≠ name ∧ other ∉ older.map Prod.fst)
      (rest : Triangular older) : Triangular ((name, value) :: older)

/-- Every flexible name depends only on declared rigid names, every committed
answer mentions only names within its bound name's dependencies, and the
bindings are triangular. -/
structure Store.Scoped (store : Store Variable Literal Symbol) : Prop where
  dependencies : ∀ name dependencies, store.info? name = some (.flexible dependencies) →
    ∀ rigid ∈ dependencies, store.info? rigid = some .rigid
  answers : ∀ name value, (name, value) ∈ store.bindings → ∃ dependencies,
    store.info? name = some (.flexible dependencies) ∧ ∀ other ∈ value.freeVars, store.Within dependencies other
  triangular : Triangular store.bindings

theorem Store.Within.declared {store : Store Variable Literal Symbol} {dependencies : List Variable}
    {other : Variable} (within : store.Within dependencies other) : store.info? other ≠ none := by
  rcases within with ⟨rigid, _⟩ | ⟨own, flexible, _⟩
  · rw [rigid]; exact Option.some_ne_none _
  · rw [flexible]; exact Option.some_ne_none _

theorem Store.Within.narrow {store : Store Variable Literal Symbol} {dependencies targets allowed : List Variable}
    {other : Variable} (within : store.Within dependencies other) :
    (store.narrow targets allowed).Within dependencies other := by
  simp only [Store.Within, Store.info?_narrow]
  rcases within with ⟨rigid, member⟩ | ⟨own, flexible, contained⟩
  · exact .inl ⟨by simp [rigid, narrowInfo], member⟩
  · right
    rw [flexible]
    unfold narrowInfo
    split
    · exact ⟨_, rfl, fun rigid member => contained rigid (List.mem_filter.mp member).1⟩
    · exact ⟨own, rfl, contained⟩

theorem Store.declare_scoped {store : Store Variable Literal Symbol} (valid : store.Scoped)
    {info : NameInfo Variable} {names : List Variable} (fresh : ∀ name ∈ names, store.info? name = none)
    (declared : ∀ dependencies, info = .flexible dependencies →
      ∀ rigid ∈ dependencies, store.info? rigid = some .rigid) :
    (store.declare info names).Scoped := by
  have old : ∀ name, store.info? name ≠ none → (store.declare info names).info? name = store.info? name :=
    fun _ present => Store.info?_declare_of_ne_none fresh present
  constructor
  · intro name dependencies infoEq rigid member
    rw [Store.info?_declare] at infoEq
    split at infoEq
    · cases infoEq
      have rigidEq := declared dependencies rfl rigid member
      rw [old rigid (by rw [rigidEq]; exact Option.some_ne_none _), rigidEq]
    · have rigidEq := valid.dependencies name dependencies infoEq rigid member
      rw [old rigid (by rw [rigidEq]; exact Option.some_ne_none _), rigidEq]
  · intro name value member
    obtain ⟨dependencies, infoEq, within⟩ := valid.answers name value member
    refine ⟨dependencies, by rw [old name (by rw [infoEq]; exact Option.some_ne_none _), infoEq],
      fun other free => ?_⟩
    have present := (within other free).declared
    simp only [Store.Within, old other present]
    exact within other free
  · exact valid.triangular

theorem Store.bind_scoped {store next : Store Variable Literal Symbol} (valid : store.Scoped)
    {scope : Scope Variable Literal Symbol} {name : Variable} {value : Term Variable Literal Symbol}
    (committed : store.bind scope name value = .committed next) : next.Scoped := by
  obtain ⟨dependencies, infoEq, boundEq, outcome⟩ := Store.bind_committed committed
  rcases outcome with ⟨_, rfl⟩ | ⟨rfl, occurs, checks⟩
  · exact valid
  · have info : ∀ other, ({ (store.narrow value.freeVars dependencies) with
        bindings := (name, value) :: store.bindings } : Store Variable Literal Symbol).info? other =
        (store.info? other).map (narrowInfo value.freeVars dependencies other) :=
      fun other => Store.info?_narrow store _ _ other
    have unchanged : ∀ other, other ∉ value.freeVars → ∀ own, store.info? other = some (.flexible own) →
        ({ (store.narrow value.freeVars dependencies) with
          bindings := (name, value) :: store.bindings } : Store Variable Literal Symbol).info? other =
          some (.flexible own) := by
      intro other outside own flexible
      rw [info, flexible]
      simp [narrowInfo, outside]
    -- The value names only unbound flexible names and rigid names, which are never bound.
    have valueUnbound : ∀ other ∈ value.freeVars, other ∉ store.bindings.map Prod.fst := by
      intro other free bound
      obtain ⟨⟨_, value'⟩, member, rfl⟩ := List.mem_map.mp bound
      obtain ⟨own, ownEq, _⟩ := valid.answers _ value' member
      have usable := (checks _ free).1
      simp only [Store.usable, ownEq, Option.isNone_iff_eq_none] at usable
      exact lookup_eq_none.mp usable bound
    constructor
    · intro other narrowed infoNarrowed rigid member
      rw [info] at infoNarrowed
      obtain ⟨original, originalEq, narrowedEq⟩ := Option.map_eq_some_iff.mp infoNarrowed
      obtain ⟨own, rfl, contained⟩ := narrowInfo_flexible narrowedEq
      have rigidEq := valid.dependencies other own originalEq rigid (contained rigid member)
      rw [info, rigidEq]
      rfl
    · intro bound bindingValue member
      simp only [List.mem_cons, Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩ | member
      · refine ⟨dependencies, unchanged bound occurs dependencies infoEq, fun other free => ?_⟩
        have ⟨usable, allowed⟩ := checks other free
        unfold Store.usable at usable
        unfold Store.allowed at allowed
        split at usable
        · rename_i rigidEq
          simp only [rigidEq, decide_eq_true_eq] at allowed
          exact .inl ⟨by rw [info, rigidEq]; rfl, allowed⟩
        · rename_i own flexibleEq
          right
          refine ⟨own.filter (· ∈ dependencies), by rw [info, flexibleEq]; simp [narrowInfo, free],
            fun rigid member => by simpa using (List.mem_filter.mp member).2⟩
        · cases usable
      · obtain ⟨own, ownEq, within⟩ := valid.answers bound bindingValue member
        have outside : bound ∉ value.freeVars :=
          fun free => valueUnbound bound free (List.mem_map.mpr ⟨_, member, rfl⟩)
        exact ⟨own, unchanged bound outside own ownEq, fun other free => (within other free).narrow⟩
    · refine .cons (fun bound => ?_) (fun other free => ⟨fun same => occurs (same ▸ free), fun bound => ?_⟩)
        valid.triangular
      · exact lookup_eq_none.mp boundEq bound
      · exact valueUnbound other free bound

theorem Store.bindAll_scoped {store next : Store Variable Literal Symbol} (valid : store.Scoped)
    {scope : Scope Variable Literal Symbol} {bindings : List (Variable × Term Variable Literal Symbol)}
    (committed : store.bindAll scope bindings = .committed next) : next.Scoped := by
  induction bindings generalizing store with
  | nil => cases committed; exact valid
  | cons binding rest ih =>
      obtain ⟨name, value⟩ := binding
      simp only [Store.bindAll] at committed
      split at committed
      · rename_i middle bound
        exact ih (Store.bind_scoped valid bound) committed
      · cases committed
      · cases committed

/-- The store a candidate is matched and committed against is scoped when the
candidate passes the commit's name checks. -/
theorem Store.prepare_scoped {store : Store Variable Literal Symbol} (valid : store.Scoped)
    {obligation : Obligation Variable Literal Symbol} {flexibles rigids : List Variable}
    (distinct : (flexibles ++ rigids).Nodup) (fresh : ∀ name ∈ flexibles ++ rigids, store.info? name = none)
    (declared : ∀ name ∈ obligation.scope.rigids, store.info? name = some .rigid) :
    (store.prepare obligation flexibles rigids).Scoped := by
  have first := Store.declare_scoped valid (info := .flexible obligation.scope.rigids) (names := flexibles)
    (fun name member => fresh name (List.mem_append_left _ member))
    (fun dependencies equal rigid member => by cases equal; exact declared rigid member)
  exact Store.declare_scoped first (Store.declare_keeps_fresh distinct fresh) (fun _ equal => by cases equal)

theorem Store.commit_scoped {store next : Store Variable Literal Symbol} (valid : store.Scoped)
    {obligation : Obligation Variable Literal Symbol} {flexibles rigids : List Variable}
    {premises : List (Premise Variable Literal Symbol)} {bindings : List (Variable × Term Variable Literal Symbol)}
    (committed : store.commit obligation flexibles rigids premises bindings = .committed next) : next.Scoped := by
  obtain ⟨⟨distinct, fresh, declared, _, _⟩, bound⟩ := Store.commit_checks committed
  exact Store.bindAll_scoped (Store.prepare_scoped valid distinct fresh declared) bound

/-- A candidate whose names pass the commit's checks commits exactly the
bindings it computed against the prepared store. -/
theorem Store.commit_prepared {store next : Store Variable Literal Symbol}
    {obligation : Obligation Variable Literal Symbol} {flexibles rigids : List Variable}
    {premises : List (Premise Variable Literal Symbol)} {bindings : List (Variable × Term Variable Literal Symbol)}
    (accepted : store.Accepts obligation flexibles rigids premises)
    (committed : (store.prepare obligation flexibles rigids).bindAll obligation.scope bindings = .committed next) :
    store.commit obligation flexibles rigids premises bindings = .committed next := by
  unfold Store.commit
  split
  · exact committed
  · rename_i failed; exact absurd accepted failed

theorem Store.bind_flexible {store next : Store Variable Literal Symbol}
    {scope : Scope Variable Literal Symbol} {name : Variable} {value : Term Variable Literal Symbol}
    (committed : store.bind scope name value = .committed next) {other : Variable} {own : List Variable}
    (flexible : store.info? other = some (.flexible own)) :
    ∃ narrowed, next.info? other = some (.flexible narrowed) ∧ ∀ rigid ∈ narrowed, rigid ∈ own := by
  obtain ⟨dependencies, _, _, outcome⟩ := Store.bind_committed committed
  rcases outcome with ⟨_, rfl⟩ | ⟨rfl, _, _⟩
  · exact ⟨own, flexible, fun _ member => member⟩
  · show ∃ narrowed, (store.narrow value.freeVars dependencies).info? other = _ ∧ _
    rw [Store.info?_narrow, flexible]
    unfold narrowInfo
    split
    · exact ⟨_, rfl, fun rigid member => (List.mem_filter.mp member).1⟩
    · exact ⟨own, rfl, fun _ member => member⟩

theorem Store.bindAll_flexible {store next : Store Variable Literal Symbol}
    {scope : Scope Variable Literal Symbol} {bindings : List (Variable × Term Variable Literal Symbol)}
    (committed : store.bindAll scope bindings = .committed next) {other : Variable} {own : List Variable}
    (flexible : store.info? other = some (.flexible own)) :
    ∃ narrowed, next.info? other = some (.flexible narrowed) ∧ ∀ rigid ∈ narrowed, rigid ∈ own := by
  induction bindings generalizing store own with
  | nil => cases committed; exact ⟨own, flexible, fun _ member => member⟩
  | cons binding rest ih =>
      obtain ⟨name, value⟩ := binding
      simp only [Store.bindAll] at committed
      split at committed
      · rename_i middle bound
        obtain ⟨middleOwn, middleEq, middleContained⟩ := Store.bind_flexible bound flexible
        obtain ⟨narrowed, narrowedEq, contained⟩ := ih committed middleEq
        exact ⟨narrowed, narrowedEq, fun rigid member => middleContained rigid (contained rigid member)⟩
      · cases committed
      · cases committed

/-- A flexible name after a binding was flexible before it, with at least its
dependencies: binding only narrows. -/
theorem Store.bind_flexible_of {store next : Store Variable Literal Symbol}
    {scope : Scope Variable Literal Symbol} {name : Variable} {value : Term Variable Literal Symbol}
    (committed : store.bind scope name value = .committed next) {other : Variable} {narrowed : List Variable}
    (flexible : next.info? other = some (.flexible narrowed)) :
    ∃ own, store.info? other = some (.flexible own) ∧ ∀ rigid ∈ narrowed, rigid ∈ own := by
  obtain ⟨dependencies, _, _, outcome⟩ := Store.bind_committed committed
  rcases outcome with ⟨_, rfl⟩ | ⟨rfl, _, _⟩
  · exact ⟨narrowed, flexible, fun _ member => member⟩
  · change (store.narrow value.freeVars dependencies).info? other = _ at flexible
    rw [Store.info?_narrow] at flexible
    obtain ⟨original, originalEq, narrowedEq⟩ := Option.map_eq_some_iff.mp flexible
    obtain ⟨own, rfl, contained⟩ := narrowInfo_flexible narrowedEq
    exact ⟨own, originalEq, contained⟩

theorem Store.bindAll_flexible_of {store next : Store Variable Literal Symbol}
    {scope : Scope Variable Literal Symbol} {bindings : List (Variable × Term Variable Literal Symbol)}
    (committed : store.bindAll scope bindings = .committed next) {other : Variable} {narrowed : List Variable}
    (flexible : next.info? other = some (.flexible narrowed)) :
    ∃ own, store.info? other = some (.flexible own) ∧ ∀ rigid ∈ narrowed, rigid ∈ own := by
  induction bindings generalizing store with
  | nil => cases committed; exact ⟨narrowed, flexible, fun _ member => member⟩
  | cons binding rest ih =>
      obtain ⟨name, value⟩ := binding
      simp only [Store.bindAll] at committed
      split at committed
      · rename_i middle bound
        obtain ⟨middleOwn, middleEq, middleContained⟩ := ih committed
        obtain ⟨own, ownEq, contained⟩ := Store.bind_flexible_of bound middleEq
        exact ⟨own, ownEq, fun rigid member => contained rigid (middleContained rigid member)⟩
      · cases committed
      · cases committed

/-- Every flexible name of a committed store, old or new, depends only on rigid
names declared before the commit: none depends on a rigid name the commit
opens. -/
theorem Store.commit_independent {store next : Store Variable Literal Symbol} (valid : store.Scoped)
    {obligation : Obligation Variable Literal Symbol} {flexibles rigids : List Variable}
    {premises : List (Premise Variable Literal Symbol)} {bindings : List (Variable × Term Variable Literal Symbol)}
    (committed : store.commit obligation flexibles rigids premises bindings = .committed next)
    {opened : Variable} (member : opened ∈ rigids) {name : Variable} {dependencies : List Variable}
    (flexible : next.info? name = some (.flexible dependencies)) : opened ∉ dependencies := by
  obtain ⟨⟨_, fresh, declared, _, _⟩, bound⟩ := Store.commit_checks committed
  have undeclared := fresh opened (List.mem_append_right _ member)
  obtain ⟨own, ownEq, contained⟩ := Store.bindAll_flexible_of bound flexible
  intro inside
  have dependsOn := contained opened inside
  simp only [Store.prepare, Store.info?_declare] at ownEq
  split at ownEq
  · cases ownEq
  · split at ownEq
    · cases ownEq
      rw [declared opened dependsOn] at undeclared
      cases undeclared
    · rw [valid.dependencies name own ownEq opened dependsOn] at undeclared
      cases undeclared

/-- A rigid name a commit opens does not occur in a premise that does not open
it: it is out of that premise's scope. For `existsElim`, the opened existential
does not mention its eigenvariable. -/
theorem Store.commit_fresh_premise {store next : Store Variable Literal Symbol}
    {obligation : Obligation Variable Literal Symbol} {flexibles rigids : List Variable}
    {premises : List (Premise Variable Literal Symbol)} {bindings : List (Variable × Term Variable Literal Symbol)}
    (committed : store.commit obligation flexibles rigids premises bindings = .committed next)
    {opened : Variable} (member : opened ∈ rigids) {premise : Premise Variable Literal Symbol}
    (premiseMember : premise ∈ premises) (outside : opened ∉ premise.discharge.rigids) :
    opened ∉ premise.freeVars := by
  obtain ⟨⟨_, fresh, scopeRigid, _, admitted⟩, _⟩ := Store.commit_checks committed
  intro inside
  have undeclared := fresh opened (List.mem_append_right _ member)
  have preparedRigid : (store.prepare obligation flexibles rigids).info? opened = some .rigid := by
    simp only [Store.prepare, Store.info?_declare, member, ite_true]
  rcases Store.inScope_within (admitted premise premiseMember opened inside) with
    ⟨_, inScope⟩ | ⟨_, flexibleEq, _⟩
  · rcases List.mem_append.mp inScope with opens | old
    · exact outside opens
    · rw [scopeRigid opened old] at undeclared; cases undeclared
  · rw [preparedRigid] at flexibleEq; cases flexibleEq

/-- Only rigid names among a bound name's dependencies occur in its answer. -/
theorem Store.Scoped.answer_rigid {store : Store Variable Literal Symbol} (valid : store.Scoped)
    {name : Variable} {value : Term Variable Literal Symbol} (member : (name, value) ∈ store.bindings)
    {dependencies : List Variable} (flexible : store.info? name = some (.flexible dependencies))
    {other : Variable} (free : other ∈ value.freeVars) (rigid : store.info? other = some .rigid) :
    other ∈ dependencies := by
  obtain ⟨own, ownEq, within⟩ := valid.answers name value member
  rw [flexible] at ownEq
  cases ownEq
  rcases within other free with ⟨_, member⟩ | ⟨_, flexibleEq, _⟩
  · exact member
  · rw [rigid] at flexibleEq; cases flexibleEq

end AnthillModKbSpec.Machine
