import AnthillModKbSpec.Resolution.Elaboration
import AnthillModKbSpec.Resolution.Answer

/-! # The dictionary registry (S13)

Dictionaries are values in the shared carrier; names identify dictionaries and
interfaces. The registry records, for a signature snapshot:

- **interfaces**: a membership symbol (`OrdDictionary`), the operations every
  dictionary of it provides (a path of required-model fields, a field, the
  supported argument counts), and generic laws, each a formula about one
  dictionary;
- **registrations**: a dictionary's name (the constant `n()` denotes it), its
  version, its interface, its inductive domain `D_i`, and its primitive
  contracts (an operation total on domain arguments, with results in a domain).

Two relations read them, with no type system: `I(d)` for an interface `I`, and
`DomainMember(d, x)`. Their interpretation is exact (`Snapshot.Realizes`):

- `I(d)` holds exactly on the values of the names registered for `I`, as
  `P_n` holds exactly on registered references (S02);
- `DomainMember(d, x)` holds when `d`'s own member field, a predicate entry,
  holds at `x` (`Interpretation.Member`). It reads the dictionary value, for
  every carrier value, not a table.

A registration's claims are evidence, not table assertions
(`Registration.Checked`): its member field holds exactly on `D_i`, its
interface's operations resolve on its value, its interface's laws hold at its
value, and its primitive contracts hold. Under that evidence the generated
clauses are true (`models_kb`) and make the guards derivable
(`interface_derives`, `domainMember_derives`): `I(n).` and
`DomainMember(n, X) :- D_i(X)`. A generic law `∀d. I(d) → body` holds in every
realizing model (`law_valid`): a law is a statement with a validity theorem,
not a KB clause or an inference rule. One domain may have several
dictionaries, each with its own evidence.

`access?` classifies a dictionary call before anything runs, and
`Access.verdict` says what admission makes of it. A declared access runs: it
resolves to a callable entry and evaluates as direct application
(`access_eval`). An access the registry does not declare is blocked, with what
is missing, never refuted: an unbound dictionary variable needs a binding (a
mode); an unknown name, a dictionary that is no name, an operation outside the
interface, an unsupported argument count, and an operation call where a
formula is needed have no route, each with its reason. An operation's result
is a value, such as a Boolean; a law compares it with the value `true`, it
never reads it as truth. Only a registration naming an undeclared interface is
an invalid input, and a well-formed registry has none (`access?_consistent`).

An unknown name is no refutation in the realizing models: a name may denote a
registered dictionary's value without being registered (`InterfaceMember` is
about values; `not_interfaceMember`, `alias_interfaceMember`). A closed-world
reading of the registry's relations, by P0 or the completion, treats distinct
names as distinct values; it is snapshot-indexed and holds only in models that
do.

Snapshots index what is not monotone. The generated clauses only grow with the
registry (`kb_mono`), so derivations from them stay valid. An access, an
`unknown` above all, a registration's evidence, and the plans built on them,
are reused only while the signature, the naming, and the names they read keep
their declarations (`Snapshot.Unchanged`, `access_unchanged`,
`Registration.Checked.transfer`); registering a new name leaves the others
unchanged (`register_unchanged`), and a version change of a registration
changes it. -/

namespace AnthillModKbSpec.DictionaryRegistry

open Semantics InductiveDomains AdmissionSignature OperationDictionaries Elaboration

/-! ## Declarations -/

/-- An operation an interface requires: the required-model fields leading to
it, its field, and the argument counts it may be called with. -/
structure Operation (Symbol : Type) where
  path : List Symbol
  field : Symbol
  arities : List Nat
  deriving DecidableEq, Repr

/-- A generic law of an interface: a formula about one dictionary, the free
binder `dictionary`. The interface's guard closes it (`Law.formula`). -/
structure Law (Variable Literal Symbol : Type) where
  name : Symbol
  dictionary : Variable
  body : Formula Variable Literal Symbol

/-- An interface: its membership symbol, the operations every dictionary of it
provides, and its generic laws. -/
structure Interface (Variable Literal Symbol : Type) where
  symbol : Symbol
  operations : List (Operation Symbol)
  laws : List (Law Variable Literal Symbol)

/-- A primitive contract: the operation at this path and field, called with
arguments of these domains, returns a member of `result`. It claims totality
on the domains; evaluating with it is S14's. -/
structure Primitive (Domain Symbol : Type) where
  path : List Symbol
  field : Symbol
  arguments : List Domain
  result : Domain
  deriving DecidableEq, Repr

/-- One registered dictionary. The constant `name()` denotes it. -/
structure Registration (Domain Symbol : Type) where
  name : Symbol
  version : Nat
  interface : Symbol
  domain : Domain
  primitives : List (Primitive Domain Symbol)
  deriving DecidableEq, Repr

/-- The symbols the registry reads: the field holding every dictionary's own
domain predicate, and the relation `DomainMember(d, x)`. -/
structure Naming (Symbol : Type) where
  memberField : Symbol
  domainMember : Symbol
  deriving DecidableEq, Repr

structure Registry (Domain Variable Literal Symbol : Type) where
  naming : Naming Symbol
  interfaces : List (Interface Variable Literal Symbol)
  dictionaries : List (Registration Domain Symbol)

/-- A registry over a signature snapshot, with its own revision. -/
structure Snapshot (Domain Variable Literal Symbol : Type) where
  revision : Nat
  signature : SignatureSnapshot Domain Symbol
  registry : Registry Domain Variable Literal Symbol

variable {Domain Variable Literal Symbol Value : Type} {hoApplySymbol : Symbol}

/-- The guarded law: `∀d. I(d) → body`. -/
def Law.formula (interface : Interface Variable Literal Symbol) (law : Law Variable Literal Symbol) :
    Formula Variable Literal Symbol :=
  .forallVar law.dictionary (.imp (.app interface.symbol [.var law.dictionary]) law.body)

/-- The symbols of the registry's relations. -/
def Registry.symbols (registry : Registry Domain Variable Literal Symbol) : List Symbol :=
  registry.naming.domainMember :: registry.interfaces.map Interface.symbol

/-! ## Lookup and the access check -/

/-- What a successful `find?` by a decided property returns. -/
theorem find?_sound {α : Type} {list : List α} {property : α → Prop} [DecidablePred property] {found : α}
    (located : list.find? (fun item => decide (property item)) = some found) : found ∈ list ∧ property found :=
  ⟨List.mem_of_find?_eq_some located, by simpa using List.find?_some located⟩

/-- With unique keys, `find?` by a member's key returns that member. -/
theorem find?_key {α β : Type} [DecidableEq β] {key : α → β} :
    ∀ {list : List α}, (list.map key).Nodup → ∀ {item : α}, item ∈ list →
      list.find? (fun other => decide (key other = key item)) = some item
  | [], _, _, member => by cases member
  | head :: rest, unique, item, member => by
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with rfl | inside
    · simp
    · have different : key head ≠ key item := fun same => unique.1 (same ▸ List.mem_map_of_mem inside)
      simp [different, find?_key unique.2 inside]

section Lookup

variable [DecidableEq Symbol]

/-- The first registration with this name. -/
def Registry.dictionary? (registry : Registry Domain Variable Literal Symbol) (name : Symbol) :
    Option (Registration Domain Symbol) :=
  registry.dictionaries.find? fun registration => decide (registration.name = name)

/-- The first interface with this symbol. -/
def Registry.interface? (registry : Registry Domain Variable Literal Symbol) (symbol : Symbol) :
    Option (Interface Variable Literal Symbol) :=
  registry.interfaces.find? fun interface => decide (interface.symbol = symbol)

/-- The first operation of the interface at this path and field. -/
def Interface.operation? (interface : Interface Variable Literal Symbol) (path : List Symbol) (field : Symbol) :
    Option (Operation Symbol) :=
  interface.operations.find? fun operation => decide (operation.path = path ∧ operation.field = field)

/-- A consistent registry: names and interface symbols are unique and apart
from `DomainMember`; an interface declares each operation once, and none
starts at the member field, where a dictionary holds its domain predicate; and
every registration's interface is declared, with its primitive contracts for
operations of it at supported argument counts. A registry that fails this is
an invalid input, not a missing capability. -/
def Registry.WellFormed (registry : Registry Domain Variable Literal Symbol) : Prop :=
  (registry.dictionaries.map Registration.name).Nodup ∧
  registry.symbols.Nodup ∧
  (∀ interface ∈ registry.interfaces,
    (interface.operations.map fun operation => (operation.path, operation.field)).Nodup ∧
    ∀ operation ∈ interface.operations,
      (operation.path ++ [operation.field]).head? ≠ some registry.naming.memberField) ∧
  ∀ registration ∈ registry.dictionaries, ∃ interface ∈ registry.interfaces,
    interface.symbol = registration.interface ∧
    ∀ primitive ∈ registration.primitives, ∃ operation ∈ interface.operations,
      operation.path = primitive.path ∧ operation.field = primitive.field ∧
      primitive.arguments.length ∈ operation.arities

instance (registry : Registry Domain Variable Literal Symbol) : Decidable registry.WellFormed := by
  unfold Registry.WellFormed; infer_instance

/-- A consistent snapshot: a consistent registry whose symbols are none of the
signature's membership symbols or `D_all`. Separation from the `P_n` symbols,
an infinite family, is a naming hypothesis, as S22's `Separated` states it. -/
def Snapshot.WellFormed (snapshot : Snapshot Domain Variable Literal Symbol) : Prop :=
  snapshot.registry.WellFormed ∧
  ∀ symbol ∈ snapshot.registry.symbols, symbol ≠ snapshot.signature.signature.dataSymbol ∧
    ∀ domain ∈ snapshot.signature.signature.data.domains,
      symbol ≠ snapshot.signature.signature.membershipSymbol domain

instance (snapshot : Snapshot Domain Variable Literal Symbol) : Decidable snapshot.WellFormed := by
  unfold Snapshot.WellFormed; infer_instance

theorem Registry.WellFormed.interface? {registry : Registry Domain Variable Literal Symbol}
    (wellFormed : registry.WellFormed) {interface : Interface Variable Literal Symbol}
    (declared : interface ∈ registry.interfaces) : registry.interface? interface.symbol = some interface :=
  find?_key (List.nodup_cons.mp wellFormed.2.1).2 declared

/-- Where a call stands: as data, or where a formula is needed. -/
inductive Position where
  | value
  | formula
  deriving DecidableEq, Repr

/-- Why a call on a registered dictionary is outside its interface. -/
inductive AccessError where
  /-- The interface declares no operation at this path and field. -/
  | operation
  /-- The operation is not declared at this argument count. -/
  | arity (supported : List Nat)
  deriving DecidableEq, Repr

/-- A dictionary call, classified before anything runs. -/
inductive Access (Domain Symbol : Type) where
  /-- The registration and the interface's operation the call reaches. -/
  | declared (registration : Registration Domain Symbol) (operation : Operation Symbol)
  /-- An operation call standing where a formula is needed: its result is a
  value, a Boolean for instance, not a truth value. -/
  | formula
  /-- The dictionary is a variable: binding it is the strategy's. -/
  | unresolved
  /-- The dictionary is neither a name nor a variable: a literal, an
  application, a nested call. The registry resolves names only. -/
  | unnamed
  /-- A constant no registration names: a missing capability. -/
  | unknown (name : Symbol)
  /-- The registration names an undeclared interface: the registry is not
  well formed. -/
  | inconsistent (name : Symbol)
  /-- A registered dictionary called outside its interface. -/
  | invalid (name : Symbol) (error : AccessError)
  deriving DecidableEq, Repr

/-- Classify a call `dictionaryCall(dictionary, path, field, args)` with
`arity` arguments at `position`. -/
def Registry.access? (registry : Registry Domain Variable Literal Symbol) (position : Position)
    (dictionary : Term Variable Literal Symbol) (path : List Symbol) (field : Symbol) (arity : Nat) :
    Access Domain Symbol :=
  if position = .formula then .formula else
  match dictionary with
  | .app name [] =>
    match registry.dictionary? name with
    | none => .unknown name
    | some registration =>
      match registry.interface? registration.interface with
      | none => .inconsistent name
      | some interface =>
        match interface.operation? path field with
        | none => .invalid name .operation
        | some operation =>
          if arity ∈ operation.arities then .declared registration operation
          else .invalid name (.arity operation.arities)
  | .var _ => .unresolved
  | _ => .unnamed

/-- What a declared access establishes about the registry. -/
theorem access?_declared {registry : Registry Domain Variable Literal Symbol} {position : Position}
    {dictionary : Term Variable Literal Symbol} {path : List Symbol} {field : Symbol} {arity : Nat}
    {registration : Registration Domain Symbol} {operation : Operation Symbol}
    (declared : registry.access? position dictionary path field arity = .declared registration operation) :
    position = .value ∧ dictionary = .app registration.name [] ∧
      registration ∈ registry.dictionaries ∧
      ∃ interface, registry.interface? registration.interface = some interface ∧
        operation ∈ interface.operations ∧ operation.path = path ∧ operation.field = field ∧
        arity ∈ operation.arities := by
  unfold Registry.access? at declared
  cases position with
  | formula => simp at declared
  | value =>
    simp only [reduceCtorEq, ite_false] at declared
    split at declared
    next name =>
      split at declared
      next => simp at declared
      next found =>
        split at declared
        next => simp at declared
        next interface located =>
          split at declared
          next => simp at declared
          next selected =>
            split at declared
            next supported =>
              cases declared
              obtain ⟨member, named⟩ := find?_sound found
              obtain ⟨inside, samePath, sameField⟩ := find?_sound selected
              exact ⟨rfl, by rw [named], member, interface, located, inside, samePath, sameField, supported⟩
            next => simp at declared
    all_goals simp at declared

/-- A well-formed registry has no inconsistent access. -/
theorem access?_consistent {registry : Registry Domain Variable Literal Symbol}
    (wellFormed : registry.WellFormed) (position : Position) (dictionary : Term Variable Literal Symbol)
    (path : List Symbol) (field : Symbol) (arity : Nat) (name : Symbol) :
    registry.access? position dictionary path field arity ≠ .inconsistent name := by
  unfold Registry.access?
  split
  · simp
  · split
    · split
      · simp
      next registration found =>
        obtain ⟨registered, _⟩ := find?_sound found
        obtain ⟨interface, declared, symbol, _⟩ := wellFormed.2.2.2 registration registered
        rw [← symbol, wellFormed.interface? declared]
        dsimp only
        split
        · simp
        · split <;> simp
    · simp
    · simp

end Lookup

/-! ## What admission makes of an access -/

/-- An access runs, is blocked with what it lacks, or shows the registry
inconsistent (an invalid input). -/
inductive Verdict (Variable Literal Symbol : Type) where
  | runs
  | blocked (missing : Answers.Missing Variable Literal Symbol)
  | inconsistent

/-- What admission makes of an access, in S22's terms. An unbound dictionary
lacks a binding (a mode); every other undeclared access lacks a route, with
its reason. None is a refutation. -/
def Access.verdict : Access Domain Symbol → Verdict Variable Literal Symbol
  | .declared _ _ => .runs
  | .formula => .blocked (.construct (.dictionary .formula))
  | .unresolved => .blocked .mode
  | .unnamed => .blocked (.construct (.dictionary .unnamed))
  | .unknown _ => .blocked (.construct (.dictionary .unknown))
  | .inconsistent _ => .inconsistent
  | .invalid _ .operation => .blocked (.construct (.dictionary .operation))
  | .invalid _ (.arity _) => .blocked (.construct (.dictionary .arity))

theorem Access.verdict_runs {access : Access Domain Symbol} :
    access.verdict (Variable := Variable) (Literal := Literal) = .runs ↔
      ∃ registration operation, access = .declared registration operation := by
  rcases access with _ | _ | _ | _ | _ | _ | ⟨_, _ | _⟩ <;> simp [Access.verdict]

theorem Access.verdict_inconsistent {access : Access Domain Symbol} :
    access.verdict (Variable := Variable) (Literal := Literal) = .inconsistent ↔
      ∃ name, access = .inconsistent name := by
  rcases access with _ | _ | _ | _ | _ | _ | ⟨_, _ | _⟩ <;> simp [Access.verdict]

/-- The blocker of a blocked access at its place, path, and call. -/
def Access.blocker? (access : Access Domain Symbol) (place : Answers.Place Variable Literal Symbol)
    (path : List Nat) (call : Term Variable Literal Symbol) : Option (Answers.Blocker Variable Literal Symbol) :=
  match access.verdict with
  | .blocked missing => some ⟨place, path, call, missing⟩
  | _ => none

/-! ## Interpretation -/

/-- A model with checked dictionary calls: the base model, its dictionary
extension, and the value an invalid access denotes. -/
structure Interpretation (Literal Symbol Value : Type) [DecidableEq Symbol] (hoApplySymbol : Symbol) where
  base : Model Literal Symbol Value hoApplySymbol
  extension : Extension base Symbol
  invalid : Value

section Interpretation

variable [DecidableEq Symbol] (interp : Interpretation Literal Symbol Value hoApplySymbol)

def Interpretation.model : Model Literal Symbol Value hoApplySymbol :=
  interp.extension.withDictionaryCalls interp.invalid

/-- The value a dictionary name denotes: the constant `name()`. -/
def Interpretation.value (name : Symbol) : Value := interp.model.application name []

/-- The members of a dictionary value: its member field is a predicate entry,
true at the value. Read off the dictionary itself. -/
def Interpretation.Member (memberField : Symbol) (dict value : Value) : Prop :=
  ∃ entry, interp.extension.lookupAs dict memberField .predicate = some entry ∧
    interp.base.holds (interp.extension.invoke entry [value])

end Interpretation

section Semantics

variable [DecidableEq Symbol] (snapshot : Snapshot Domain Variable Literal Symbol)
  (interp : Interpretation Literal Symbol Value hoApplySymbol)

/-- The dictionaries of an interface: exactly the values of its registered
names. Another name may denote one of them. -/
def Snapshot.InterfaceMember (interface : Symbol) (value : Value) : Prop :=
  ∃ registration ∈ snapshot.registry.dictionaries, registration.interface = interface ∧
    interp.value registration.name = value

/-- Exact interpretation of the registry's relations, beside the signature's:
each interface symbol holds exactly on its registered dictionaries, and
`DomainMember(d, x)` is `d`'s own member predicate at `x`, for every value `d`. -/
structure Snapshot.Realizes : Prop where
  signature : AdmissionSignature.Realizes snapshot.signature interp.model
  interfaces : ∀ interface ∈ snapshot.registry.interfaces, ∀ value,
    interp.model.holds (interp.model.application interface.symbol [value]) ↔
      snapshot.InterfaceMember interp interface.symbol value
  domainMember : ∀ dict value,
    interp.model.holds (interp.model.application snapshot.registry.naming.domainMember [dict, value]) ↔
      interp.Member snapshot.registry.naming.memberField dict value

/-- A primitive contract at a dictionary value: on arguments of its domains,
the call returns a member of its result domain. It reads only the signature. -/
def Primitive.Holds (primitive : Primitive Domain Symbol) (signature : SignatureSnapshot Domain Symbol)
    (dict : Value) : Prop :=
  ∀ args : List Value, args.length = primitive.arguments.length →
    (∀ pair ∈ primitive.arguments.zip args,
      (Range.data [pair.1]).Contains signature interp.model pair.2) →
    (Range.data [primitive.result]).Contains signature interp.model
      (interp.model.dictionaryCall dict primitive.path primitive.field args)

variable [DecidableEq Variable]

/-- The evidence of one registration, at the value its name denotes: its
members are exactly its domain's, every operation of its interface resolves,
every law of its interface holds, and every primitive contract holds. It reads
the signature, the member field, its interface's declaration, and itself. -/
structure Registration.Checked (registration : Registration Domain Symbol) : Prop where
  domain : ∀ value, interp.Member snapshot.registry.naming.memberField (interp.value registration.name) value ↔
    (Range.data [registration.domain]).Contains snapshot.signature interp.model value
  operations : ∀ interface, snapshot.registry.interface? registration.interface = some interface →
    ∀ operation ∈ interface.operations, ∃ entry,
      interp.extension.lookupPathAs (interp.value registration.name) operation.path operation.field .operation =
        some entry
  laws : ∀ interface, snapshot.registry.interface? registration.interface = some interface →
    ∀ law ∈ interface.laws, ∀ environment : Environment Variable Value,
      interp.model.Satisfies (update environment law.dictionary (interp.value registration.name)) law.body
  primitives : ∀ primitive ∈ registration.primitives,
    primitive.Holds interp snapshot.signature (interp.value registration.name)

/-- Every registration's evidence. -/
def Snapshot.Checked : Prop :=
  ∀ registration ∈ snapshot.registry.dictionaries, registration.Checked snapshot interp

end Semantics

/-! ## Generated clauses -/

section Clauses

/-- `I(n).` for a registration of `n` at interface `I`. -/
def interfaceFact (registration : Registration Domain Symbol) : HornClause Variable Literal Symbol :=
  .definite (.app registration.interface [.app registration.name []]) []

/-- `DomainMember(n, X) :- D(X).` for a registration of `n` at domain `D`. -/
def domainClause (naming : Naming Symbol) (signature : AdmissionSignature.Naming Domain Symbol) (name : Variable)
    (registration : Registration Domain Symbol) : HornClause Variable Literal Symbol :=
  .definite (.app naming.domainMember [.app registration.name [], .var name])
    [.app (signature.membershipSymbol registration.domain) [.var name]]

/-- The signature's clauses and the registry's: one fact and one membership
clause per registration. Laws are not among them. -/
def Snapshot.kb (snapshot : Snapshot Domain Variable Literal Symbol) (names : Nat → Variable) :
    LogicalKb Variable Literal Symbol := fun clause =>
  clause ∈ signatureKb snapshot.signature names ∨
    ∃ registration ∈ snapshot.registry.dictionaries,
      interfaceFact registration = clause ∨
        domainClause snapshot.registry.naming snapshot.signature.naming (names 0) registration = clause

/-- The guards of a registered dictionary are true in a realizing model: its
domain predicate holds exactly where `DomainMember` does. -/
theorem domainMember_iff [DecidableEq Symbol] [DecidableEq Variable] {snapshot : Snapshot Domain Variable Literal Symbol}
    {interp : Interpretation Literal Symbol Value hoApplySymbol} (realizes : snapshot.Realizes interp)
    {registration : Registration Domain Symbol} (checked : registration.Checked snapshot interp) (value : Value) :
    interp.model.holds (interp.model.application snapshot.registry.naming.domainMember
        [interp.value registration.name, value]) ↔
      interp.model.holds (interp.model.application
        (snapshot.signature.signature.membershipSymbol registration.domain) [value]) := by
  rw [realizes.domainMember, checked.domain, realizes.signature.data_iff]
  simp

/-- A realizing model with checked registrations satisfies the generated clauses. -/
theorem models_kb [DecidableEq Symbol] [DecidableEq Variable] {snapshot : Snapshot Domain Variable Literal Symbol}
    {interp : Interpretation Literal Symbol Value hoApplySymbol} (realizes : snapshot.Realizes interp)
    (checked : snapshot.Checked interp) (wellFormed : snapshot.WellFormed) (names : Nat → Variable) :
    interp.model.Models (snapshot.kb (Literal := Literal) names) := by
  rintro clause (member | ⟨registration, registered, rfl | rfl⟩) environment
  · exact models_signatureKb snapshot.signature interp.model realizes.signature names clause member environment
  · simp only [interfaceFact, HornClause.toFormula, Term.conjunction, List.foldr_nil, Model.Satisfies,
      Model.eval, List.map_cons, List.map_nil, interp.model.holds_implication]
    intro _
    obtain ⟨interface, declared, symbol, _⟩ := wellFormed.1.2.2.2 registration registered
    rw [← symbol, realizes.interfaces interface declared]
    exact ⟨registration, registered, symbol.symm, rfl⟩
  · simp only [domainClause, HornClause.toFormula, Term.conjunction, List.foldr_cons, List.foldr_nil,
      Model.Satisfies, Model.eval, List.map_cons, List.map_nil, interp.model.holds_implication,
      interp.model.holds_conjunction]
    rintro ⟨holds, _⟩
    exact (domainMember_iff realizes (checked registration registered) _).mpr holds

theorem fact_mem {snapshot : Snapshot Domain Variable Literal Symbol} {names : Nat → Variable}
    {registration : Registration Domain Symbol} (registered : registration ∈ snapshot.registry.dictionaries) :
    (interfaceFact registration : HornClause Variable Literal Symbol) ∈ snapshot.kb names :=
  Or.inr ⟨registration, registered, Or.inl rfl⟩

/-- A registered dictionary derives its interface guard from its fact: a lookup
by name, with no case analysis over the registry. -/
theorem interface_derives [DecidableEq Variable] {snapshot : Snapshot Domain Variable Literal Symbol} {names : Nat → Variable}
    {kb : LogicalKb Variable Literal Symbol} (contains : ∀ clause, clause ∈ snapshot.kb names → clause ∈ kb)
    {context : ProofContext Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}
    {registration : Registration Domain Symbol} (registered : registration ∈ snapshot.registry.dictionaries) :
    Derives hoApplySymbol kb context (.app registration.interface [.app registration.name []]) naf :=
  .clause (σ := Term.var) (contains _ (fact_mem registered)) (Substitutes.identity _) (Substitutes.identity _) .truth

/-- `DomainMember(n, t)` for a generated member `t` of the registration's
domain, from its membership clause and the signature's constructor clauses. -/
theorem domainMember_derives [DecidableEq Variable] {snapshot : Snapshot Domain Variable Literal Symbol}
    {names : Nat → Variable} (distinct : DistinctNames snapshot.signature.signature.data.definitions names)
    {kb : LogicalKb Variable Literal Symbol} (contains : ∀ clause, clause ∈ snapshot.kb names → clause ∈ kb)
    {context : ProofContext Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}
    {registration : Registration Domain Symbol} (registered : registration ∈ snapshot.registry.dictionaries)
    {tree : Tree Symbol} (member : InductiveDomains.Member snapshot.signature.signature.data.definitions
      registration.domain tree) :
    Derives hoApplySymbol kb context
      (.app snapshot.registry.naming.domainMember [.app registration.name [], tree.toTerm]) naf := by
  have clause : (domainClause snapshot.registry.naming snapshot.signature.naming (names 0) registration :
      HornClause Variable Literal Symbol) ∈ kb :=
    contains _ (Or.inr ⟨registration, registered, Or.inr rfl⟩)
  have argument : SubstitutesList (Substitution.single (names 0) tree.toTerm)
      [(.app registration.name [] : Term Variable Literal Symbol), .var (names 0)]
      [.app registration.name [], tree.toTerm] :=
    .cons (.app .nil) (.cons (.singleVar _ _) .nil)
  have body : SubstitutesList (Substitution.single (names 0) tree.toTerm)
      [(.var (names 0) : Term Variable Literal Symbol)] [tree.toTerm] := .cons (.singleVar _ _) .nil
  exact .clause clause (.app argument) (SubstitutesList.conjunction (.cons (.app body) .nil))
    (.conjIntro (member.derives distinct (fun _ declared => contains _ (Or.inl (Or.inl (mem_membershipKb declared)))))
      .truth)

/-- Registering more dictionaries only adds generated clauses, so derivations
from them stay valid (`Derives.mono`). Closed-world evidence does not. -/
theorem kb_mono {snapshot grown : Snapshot Domain Variable Literal Symbol}
    (signature : grown.signature = snapshot.signature) (naming : grown.registry.naming = snapshot.registry.naming)
    (registered : ∀ registration ∈ snapshot.registry.dictionaries, registration ∈ grown.registry.dictionaries)
    (names : Nat → Variable) (clause : HornClause Variable Literal Symbol)
    (member : clause ∈ snapshot.kb names) : clause ∈ grown.kb names := by
  rcases member with member | ⟨registration, inside, generated⟩
  · left; rw [signature]; exact member
  · right
    refine ⟨registration, registered _ inside, ?_⟩
    rw [signature, naming]
    exact generated

end Clauses

/-! ## Laws -/

section Laws

variable [DecidableEq Symbol] [DecidableEq Variable]

/-- A generic law holds in every realizing model whose registrations are
checked: its guard admits exactly the registered dictionaries of the
interface, and each proves the law's body at its value. -/
theorem law_valid {snapshot : Snapshot Domain Variable Literal Symbol}
    {interp : Interpretation Literal Symbol Value hoApplySymbol} (realizes : snapshot.Realizes interp)
    (checked : snapshot.Checked interp) (wellFormed : snapshot.WellFormed)
    {interface : Interface Variable Literal Symbol} (declared : interface ∈ snapshot.registry.interfaces)
    {law : Law Variable Literal Symbol} (stated : law ∈ interface.laws) (environment : Environment Variable Value) :
    interp.model.Satisfies environment (law.formula interface) := by
  simp only [Law.formula, Model.Satisfies, Model.eval, interp.model.holds_universal,
    interp.model.holds_implication, List.map_cons, List.map_nil]
  intro value guard
  simp only [update, ite_true] at guard
  obtain ⟨registration, registered, symbol, rfl⟩ := (realizes.interfaces interface declared value).mp guard
  have located : snapshot.registry.interface? registration.interface = some interface := by
    rw [symbol]; exact wellFormed.1.interface? declared
  exact (checked registration registered).laws interface located law stated environment

end Laws

/-! ## Declared accesses evaluate -/

section Evaluation

variable [DecidableEq Symbol] [DecidableEq Variable]

/-- A declared access reaches a callable entry in every interpretation with
checked registrations, and the call evaluates as direct application of the
entry's symbol to its captures and the arguments. -/
theorem access_eval {snapshot : Snapshot Domain Variable Literal Symbol}
    {interp : Interpretation Literal Symbol Value hoApplySymbol} (checked : snapshot.Checked interp)
    {position : Position} {dictionary : Term Variable Literal Symbol} {path : List Symbol} {field : Symbol}
    {args : List (Term Variable Literal Symbol)} {registration : Registration Domain Symbol}
    {operation : Operation Symbol}
    (declared : snapshot.registry.access? position dictionary path field args.length = .declared registration operation) :
    ∃ entry, interp.extension.lookupPathAs (interp.value registration.name) path field .operation = some entry ∧
      ∀ environment : Environment Variable Value,
        interp.model.eval environment (.dictionaryCall dictionary path field args) =
          interp.base.application entry.symbol (entry.captures ++ args.map (interp.model.eval environment)) := by
  obtain ⟨_, rfl, registered, interface, located, member, rfl, rfl, _⟩ := access?_declared declared
  obtain ⟨entry, found⟩ := (checked registration registered).operations interface located operation member
  refine ⟨entry, found, fun environment => ?_⟩
  apply Extension.eval_dictionaryCall
  have named : interp.model.eval environment (.app registration.name [] : Term Variable Literal Symbol) =
      interp.value registration.name := by
    simp [Model.eval, Interpretation.value]
  exact named ▸ found

end Evaluation

/-! ## Unknown names in the realizing models -/

section Unknown

variable [DecidableEq Symbol]

/-- Excluding a value from an interface requires ruling out every registered
dictionary of it. An unknown name proves nothing: it may denote one. -/
theorem not_interfaceMember (snapshot : Snapshot Domain Variable Literal Symbol)
    (interp : Interpretation Literal Symbol Value hoApplySymbol) (interface : Symbol) (value : Value)
    (excluded : ∀ registration ∈ snapshot.registry.dictionaries, registration.interface = interface →
      interp.value registration.name ≠ value) :
    ¬ snapshot.InterfaceMember interp interface value := by
  rintro ⟨registration, registered, symbol, same⟩
  exact excluded registration registered symbol same

/-- A name that denotes a registered dictionary's value is in its interface,
registered or not. -/
theorem alias_interfaceMember (snapshot : Snapshot Domain Variable Literal Symbol)
    (interp : Interpretation Literal Symbol Value hoApplySymbol) {registration : Registration Domain Symbol}
    (registered : registration ∈ snapshot.registry.dictionaries) {name : Symbol}
    (same : interp.value name = interp.value registration.name) :
    snapshot.InterfaceMember interp registration.interface (interp.value name) :=
  ⟨registration, registered, rfl, same.symm⟩

end Unknown

/-! ## Invalidation -/

section Invalidation

variable [DecidableEq Symbol]

/-- Reuse across snapshots requires the whole snapshot to be equal; a changed
revision forbids it. -/
def Snapshot.ReusableAt (recorded current : Snapshot Domain Variable Literal Symbol) : Prop := recorded = current

omit [DecidableEq Symbol] in
theorem Snapshot.not_reusable_of_revision_ne {recorded current : Snapshot Domain Variable Literal Symbol}
    (different : recorded.revision ≠ current.revision) : ¬ recorded.ReusableAt current :=
  fun same => different (congrArg Snapshot.revision same)

/-- The names a call reads: the dictionary's name when it is a constant. -/
def reads : Term Variable Literal Symbol → List Symbol
  | .app name [] => [name]
  | _ => []

/-- Nothing an access read changed: each name keeps its registration, version
included, or its absence, and its interface keeps its declaration. -/
def Registry.Unchanged (recorded current : Registry Domain Variable Literal Symbol) (names : List Symbol) : Prop :=
  ∀ name ∈ names, recorded.dictionary? name = current.dictionary? name ∧
    ∀ registration, recorded.dictionary? name = some registration →
      recorded.interface? registration.interface = current.interface? registration.interface

/-- Nothing a plan or a registration's evidence read changed: the signature,
the registry's naming, and the names. -/
def Snapshot.Unchanged (recorded current : Snapshot Domain Variable Literal Symbol) (names : List Symbol) : Prop :=
  recorded.signature = current.signature ∧ recorded.registry.naming = current.registry.naming ∧
    recorded.registry.Unchanged current.registry names

/-- An access is reused only while the names it reads are unchanged. Then it
is the same access, `unknown` included. -/
theorem access_unchanged {recorded current : Registry Domain Variable Literal Symbol}
    {dictionary : Term Variable Literal Symbol} (unchanged : recorded.Unchanged current (reads dictionary))
    (position : Position) (path : List Symbol) (field : Symbol) (arity : Nat) :
    recorded.access? position dictionary path field arity = current.access? position dictionary path field arity := by
  unfold Registry.access?
  split
  · rfl
  · match dictionary with
    | .app name [] =>
      obtain ⟨sameRegistration, sameInterface⟩ := unchanged name (by simp [reads])
      simp only
      rw [← sameRegistration]
      cases found : recorded.dictionary? name with
      | none => rfl
      | some registration => simp only [sameInterface registration found]
    | .var _ | .lit _ | .app _ (_ :: _) | .truth | .falsity | .conj _ _ | .disj _ _ | .imp _ _
    | .defaultNeg _ | .forallVar _ _ | .existsVar _ _ | .dictionaryCall _ _ _ _ | .equal _ _ => rfl

/-- A registration's evidence carries over to a snapshot that leaves its name,
the signature, and the naming unchanged. -/
theorem Registration.Checked.transfer [DecidableEq Variable] {recorded current : Snapshot Domain Variable Literal Symbol}
    {interp : Interpretation Literal Symbol Value hoApplySymbol} {registration : Registration Domain Symbol}
    (unchanged : recorded.Unchanged current [registration.name])
    (found : recorded.registry.dictionary? registration.name = some registration)
    (checked : registration.Checked recorded interp) : registration.Checked current interp := by
  obtain ⟨signature, naming, names⟩ := unchanged
  have located := (names registration.name (List.mem_singleton_self _)).2 registration found
  refine ⟨fun value => ?_, fun interface inside => ?_, fun interface inside => ?_, fun primitive member => ?_⟩
  · rw [← signature, ← naming]; exact checked.domain value
  · rw [← located] at inside; exact checked.operations interface inside
  · rw [← located] at inside; exact checked.laws interface inside
  · rw [← signature]; exact checked.primitives primitive member

/-- Registering a dictionary under a new name changes nothing the other names read. -/
theorem register_unchanged {recorded : Registry Domain Variable Literal Symbol}
    (registration : Registration Domain Symbol) {names : List Symbol} (fresh : registration.name ∉ names) :
    recorded.Unchanged { recorded with dictionaries := recorded.dictionaries ++ [registration] } names := by
  intro name member
  have different : registration.name ≠ name := fun same => fresh (same ▸ member)
  have lookup : recorded.dictionary? name =
      ({ recorded with dictionaries := recorded.dictionaries ++ [registration] } : Registry Domain Variable Literal Symbol).dictionary? name := by
    simp only [Registry.dictionary?, List.find?_append]
    cases recorded.dictionaries.find? (fun registration => decide (registration.name = name)) <;>
      simp [different]
  exact ⟨lookup, fun _ _ => rfl⟩

end Invalidation

end AnthillModKbSpec.DictionaryRegistry
