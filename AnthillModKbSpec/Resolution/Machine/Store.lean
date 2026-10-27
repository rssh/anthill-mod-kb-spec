import AnthillModKbSpec.Foundation.Derivation
import AnthillModKbSpec.Foundation.ClauseInstantiation
import AnthillModKbSpec.Foundation.OperationDictionaries

namespace AnthillModKbSpec.Machine

open OperationDictionaries (lookup)

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
the machine contract (a name that is not fresh, an unresolved value, a rigid
name outside the scope, an assigned rigid, a rebound answer); it also abandons
the candidate but is recorded as a gap, never as failure. -/
inductive Commit (Variable Literal Symbol : Type) where
  | committed (store : Store Variable Literal Symbol)
  | rejected
  | violated

variable [DecidableEq Variable]

/-- Free and binder names of the obligation's goal and context. A name opened
for it must avoid all of them. -/
def Obligation.names (obligation : Obligation Variable Literal Symbol) : List Variable :=
  obligation.goal.freeVars ++ obligation.goal.binderNames ++
    obligation.context.flatMap (fun assumption => assumption.freeVars ++ assumption.binderNames)

/-- Avoiding the obligation's names gives the freshness conditions `Derives`
checks for opening its goal. -/
theorem Obligation.fresh_of_not_mem_names {obligation : Obligation Variable Literal Symbol} {name : Variable}
    (fresh : name ∉ obligation.names) :
    FreshForContext name obligation.context ∧ name ∉ obligation.goal.freeVars ∧
      name ∉ obligation.goal.binderNames := by
  simp only [Obligation.names, List.mem_append, List.mem_flatMap, not_or, not_exists, not_and] at fresh
  exact ⟨fun assumption member free => (fresh.2 assumption member).1 free, fresh.1.1, fresh.1.2⟩

def Store.info? (store : Store Variable Literal Symbol) (name : Variable) : Option (NameInfo Variable) :=
  lookup store.names name

def Store.binding? (store : Store Variable Literal Symbol) (name : Variable) :
    Option (Term Variable Literal Symbol) :=
  lookup store.bindings name

def Store.declare (store : Store Variable Literal Symbol) (info : NameInfo Variable) (names : List Variable) :
    Store Variable Literal Symbol :=
  { store with names := names.map (fun name => (name, info)) ++ store.names }

/-- A name not declared in the store and not in `avoid`. -/
def Store.fresh [FreshNames Variable] (store : Store Variable Literal Symbol) (avoid : List Variable) :
    Variable :=
  FreshNames.fresh (store.names.map Prod.fst ++ avoid)

/-- A name the commit accepts for opening this obligation's goal. -/
def Store.freshFor [FreshNames Variable] (store : Store Variable Literal Symbol)
    (obligation : Obligation Variable Literal Symbol) (avoid : List Variable := []) : Variable :=
  store.fresh (obligation.names ++ avoid)

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

/-- Commit one candidate for an obligation: check that its new names are fresh
for the store and the obligation, and that the obligation's rigid names are
declared; declare the new flexible names depending on the obligation's rigid
names and the premises' rigid names; then bind. Bindings may use the new
flexible names but not the premises' rigid names. -/
def Store.commit (store : Store Variable Literal Symbol) (obligation : Obligation Variable Literal Symbol)
    (flexibles rigids : List Variable) (bindings : List (Variable × Term Variable Literal Symbol)) :
    Commit Variable Literal Symbol :=
  if (flexibles ++ rigids).Nodup ∧
      (∀ name ∈ flexibles ++ rigids, store.info? name = none ∧ name ∉ obligation.names) ∧
      ∀ name ∈ obligation.scope.rigids, store.info? name = some .rigid then
    ((store.declare (.flexible obligation.scope.rigids) flexibles).declare .rigid rigids).bindAll
      obligation.scope bindings
  else .violated

/-- Apply the triangular bindings, oldest first. `none` is a capture hazard the
executable substitution refuses (alpha-renaming is required), not a failure. -/
def Store.resolve? (store : Store Variable Literal Symbol) (term : Term Variable Literal Symbol) :
    Option (Term Variable Literal Symbol) :=
  store.bindings.foldr
    (fun binding resolved => resolved.bind (Term.instantiate? (Substitution.single binding.1 binding.2)))
    (some term)

/-- Resolution by the binding chain, oldest binding applied first. -/
inductive Resolves : List (Variable × Term Variable Literal Symbol) →
    Term Variable Literal Symbol → Term Variable Literal Symbol → Prop where
  | nil : Resolves [] term term
  | cons (older : Resolves rest term middle)
      (newest : Substitutes (Substitution.single name value) middle result) :
      Resolves ((name, value) :: rest) term result

theorem Store.resolve?_sound (store : Store Variable Literal Symbol) {term result : Term Variable Literal Symbol}
    (computed : store.resolve? term = some result) : Resolves store.bindings term result := by
  obtain ⟨names, bindings⟩ := store
  simp only [Store.resolve?] at computed ⊢
  induction bindings generalizing result with
  | nil => cases computed; exact .nil
  | cons binding rest ih =>
      obtain ⟨name, value⟩ := binding
      simp only [List.foldr_cons] at computed
      obtain ⟨middle, older, newest⟩ := Option.bind_eq_some_iff.mp computed
      exact .cons (ih older) (Term.instantiate?_sound _ newest)

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

/-- Commits only add bindings, each one proposed by the candidate: the answers
of earlier AND siblings survive. -/
theorem Store.commit_extends {store next : Store Variable Literal Symbol}
    {obligation : Obligation Variable Literal Symbol} {flexibles rigids : List Variable}
    {bindings : List (Variable × Term Variable Literal Symbol)}
    (committed : store.commit obligation flexibles rigids bindings = .committed next) :
    ∃ added, next.bindings = added ++ store.bindings ∧ ∀ binding ∈ added, binding ∈ bindings := by
  unfold Store.commit at committed
  split at committed
  · simpa [Store.declare] using Store.bindAll_extends committed
  · cases committed

/-- Every name a commit opens is fresh for the store and for the obligation's
free and binder names. -/
theorem Store.commit_fresh {store next : Store Variable Literal Symbol}
    {obligation : Obligation Variable Literal Symbol} {flexibles rigids : List Variable}
    {bindings : List (Variable × Term Variable Literal Symbol)}
    (committed : store.commit obligation flexibles rigids bindings = .committed next) :
    ∀ name ∈ flexibles ++ rigids, store.info? name = none ∧ name ∉ obligation.names := by
  unfold Store.commit at committed
  split at committed
  · rename_i checks; exact checks.2.1
  · cases committed

/-! ## Scope invariant -/

/-- `other` may occur in an answer whose name depends on `dependencies`: it is a
rigid name among them, or a flexible name depending only on them. -/
def Store.Within (store : Store Variable Literal Symbol) (dependencies : List Variable) (other : Variable) : Prop :=
  (store.info? other = some .rigid ∧ other ∈ dependencies) ∨
    ∃ own, store.info? other = some (.flexible own) ∧ ∀ rigid ∈ own, rigid ∈ dependencies

/-- Every flexible name depends only on declared rigid names, and every committed
answer mentions only names within its bound name's dependencies. -/
structure Store.Scoped (store : Store Variable Literal Symbol) : Prop where
  dependencies : ∀ name dependencies, store.info? name = some (.flexible dependencies) →
    ∀ rigid ∈ dependencies, store.info? rigid = some .rigid
  answers : ∀ name value, (name, value) ∈ store.bindings → ∃ dependencies,
    store.info? name = some (.flexible dependencies) ∧ ∀ other ∈ value.freeVars, store.Within dependencies other

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
    fun name present => by
      rw [Store.info?_declare]
      split
      · rename_i member; exact absurd (fresh name member) present
      · rfl
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

theorem Store.bind_scoped {store next : Store Variable Literal Symbol} (valid : store.Scoped)
    {scope : Scope Variable Literal Symbol} {name : Variable} {value : Term Variable Literal Symbol}
    (committed : store.bind scope name value = .committed next) : next.Scoped := by
  obtain ⟨dependencies, infoEq, _, outcome⟩ := Store.bind_committed committed
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
        have outside : bound ∉ value.freeVars := by
          intro free
          have usable := (checks bound free).1
          simp only [Store.usable, ownEq, Option.isNone_iff_eq_none] at usable
          have present := lookup_isSome_of_mem member
          simp only [Store.binding?] at usable
          rw [usable] at present
          cases present
        exact ⟨own, unchanged bound outside own ownEq, fun other free => (within other free).narrow⟩

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

theorem Store.commit_scoped {store next : Store Variable Literal Symbol} (valid : store.Scoped)
    {obligation : Obligation Variable Literal Symbol} {flexibles rigids : List Variable}
    {bindings : List (Variable × Term Variable Literal Symbol)}
    (committed : store.commit obligation flexibles rigids bindings = .committed next) : next.Scoped := by
  unfold Store.commit at committed
  split at committed
  · rename_i checks
    obtain ⟨distinct, fresh, declared⟩ := checks
    have first := Store.declare_scoped valid (info := .flexible obligation.scope.rigids) (names := flexibles)
      (fun name member => (fresh name (List.mem_append_left _ member)).1)
      (fun dependencies equal rigid member => by cases equal; exact declared rigid member)
    refine Store.bindAll_scoped (Store.declare_scoped first (info := .rigid) (names := rigids) ?_ ?_) committed
    · intro name member
      rw [Store.info?_declare]
      have notFlexible : name ∉ flexibles := fun flexible =>
        (List.nodup_append.mp distinct).2.2 name flexible name member rfl
      simp only [notFlexible, ite_false]
      exact (fresh name (List.mem_append_right _ member)).1
    · intro _ equal; cases equal
  · cases committed

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

/-- A rigid name a commit opens never becomes a dependency of a flexible name
that already existed, so by `Scoped` it never enters that name's answer: the
opened eigenvariable or existential witness cannot escape its premise. -/
theorem Store.commit_no_escape {store next : Store Variable Literal Symbol} (valid : store.Scoped)
    {obligation : Obligation Variable Literal Symbol} {flexibles rigids : List Variable}
    {bindings : List (Variable × Term Variable Literal Symbol)}
    (committed : store.commit obligation flexibles rigids bindings = .committed next)
    {opened : Variable} (member : opened ∈ rigids) {name : Variable} {dependencies : List Variable}
    (existing : store.info? name = some (.flexible dependencies)) :
    ∃ narrowed, next.info? name = some (.flexible narrowed) ∧ opened ∉ narrowed := by
  have fresh := (Store.commit_fresh committed opened (List.mem_append_right _ member)).1
  unfold Store.commit at committed
  split at committed
  · rename_i checks
    have present : store.info? name ≠ none := by rw [existing]; exact Option.some_ne_none _
    have notNew : ∀ names : List Variable, (∀ new ∈ names, store.info? new = none) → name ∉ names :=
      fun _ allFresh new => present (allFresh name new)
    have declared :
        ((store.declare (.flexible obligation.scope.rigids) flexibles).declare .rigid rigids).info? name =
          some (.flexible dependencies) := by
      rw [Store.info?_declare, Store.info?_declare]
      simp only [notNew rigids (fun new m => (checks.2.1 new (List.mem_append_right _ m)).1),
        notNew flexibles (fun new m => (checks.2.1 new (List.mem_append_left _ m)).1), ite_false]
      exact existing
    obtain ⟨narrowed, narrowedEq, contained⟩ := Store.bindAll_flexible committed declared
    refine ⟨narrowed, narrowedEq, fun inNarrowed => ?_⟩
    have rigidEq := valid.dependencies name dependencies existing opened (contained opened inNarrowed)
    rw [fresh] at rigidEq
    cases rigidEq
  · cases committed

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
