import AnthillModKbSpec.Foundation.Semantics

namespace AnthillModKbSpec.OperationDictionaries

/-- Roles describe dictionary interfaces, not a type system for terms. -/
inductive Role where
  | predicate
  | operation
  deriving DecidableEq, Repr

/-- A named callable with an explicit environment of captured values. -/
structure Entry (Symbol Value : Type) where
  role : Role
  symbol : Symbol
  captures : List Value := []
  deriving DecidableEq, Repr

/-- A dictionary is a finite tree. Required models are subdictionary nodes,
while predicates and operations are callable leaves. -/
inductive Node (Field Symbol Value : Type) where
  | callable : Entry Symbol Value → Node Field Symbol Value
  | subdictionary : List (Field × Node Field Symbol Value) → Node Field Symbol Value
  deriving Repr

abbrev Dictionary (Field Symbol Value : Type) := List (Field × Node Field Symbol Value)

/-- Lookup uses the first occurrence of a field. -/
def lookup [DecidableEq Field] (entries : List (Field × Item))
    (field : Field) : Option Item :=
  match entries with
  | [] => none
  | (name, entry) :: rest => if name = field then some entry else lookup rest field

theorem lookup_map [DecidableEq Field] (entries : List (Field × Item))
    (field : Field) (transform : Item → Result) :
    lookup (entries.map (fun (name, item) => (name, transform item))) field =
      (lookup entries field).map transform := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
    rcases head with ⟨name, item⟩
    by_cases same : name = field <;> simp [lookup, same, ih]

theorem lookup_eq_none [DecidableEq Field] {entries : List (Field × Item)} {field : Field} :
    lookup entries field = none ↔ field ∉ entries.map Prod.fst := by
  induction entries with
  | nil => simp [lookup]
  | cons head rest ih =>
    rcases head with ⟨name, item⟩
    by_cases same : name = field
    · simp [lookup, same]
    · simp [lookup, same, ih, Ne.symm same]

/-- Additional semantic structure over the existing logic model. References are
explicit values; they are not defined as zero-argument evaluation. This contract
does not yet add reference/application constructors to `Term`. -/
structure Extension (model : Semantics.Model Literal Symbol Value hoApplySymbol)
    (Field : Type) [DecidableEq Field] where
  roleOf : Symbol → Role
  reference : Symbol → Value
  call : Value → List Value → Value
  dictionary : Dictionary Field Symbol Value → Value
  project : Value → Field → Option (Node Field Symbol Value)
  call_reference : ∀ symbol args,
    call (reference symbol) args = model.application symbol args
  project_dictionary : ∀ entries field,
    project (dictionary entries) field = lookup entries field

variable {Literal Symbol Value Field : Type} {hoApplySymbol : Symbol}
  {model : Semantics.Model Literal Symbol Value hoApplySymbol} [DecidableEq Field]

namespace Extension

variable (extension : Extension model Field)

def invoke (entry : Entry Symbol Value) (args : List Value) : Value :=
  extension.call (extension.reference entry.symbol) (entry.captures ++ args)

theorem invoke_eq (entry : Entry Symbol Value) (args : List Value) :
    extension.invoke entry args = model.application entry.symbol (entry.captures ++ args) :=
  extension.call_reference _ _

/-- Value equality makes replacement valid inside any semantic context. -/
theorem call_in_context (context : Value → Value) (symbol : Symbol) (args : List Value) :
    context (extension.call (extension.reference symbol) args) =
      context (model.application symbol args) :=
  congrArg context (extension.call_reference symbol args)

theorem holds_invoke (entry : Entry Symbol Value) (args : List Value) :
    model.holds (extension.invoke entry args) ↔
      model.holds (model.application entry.symbol (entry.captures ++ args)) := by
  rw [extension.invoke_eq]

/-- Both the stored tag and the symbol's declared role must match. A rejected
lookup is an interface error, with no logical or NAF interpretation. -/
def lookupAs (value : Value) (field : Field) (role : Role) : Option (Entry Symbol Value) := do
  match ← extension.project value field with
  | .callable entry =>
    if entry.role = role ∧ extension.roleOf entry.symbol = role then some entry else none
  | .subdictionary _ => none

/-- Projection of a required model yields the semantic value of its subtree. -/
def subdictionary (value : Value) (field : Field) : Option Value := do
  match ← extension.project value field with
  | .subdictionary entries => some (extension.dictionary entries)
  | .callable _ => none

/-- Follow required-model fields; the empty path denotes the starting dictionary. -/
def atPath (value : Value) : List Field → Option Value
  | [] => some value
  | field :: rest => do
    let child ← extension.subdictionary value field
    atPath child rest

def lookupPathAs (value : Value) (path : List Field) (field : Field)
    (role : Role) : Option (Entry Symbol Value) := do
  let child ← extension.atPath value path
  extension.lookupAs child field role

/-- Following two paths in sequence agrees with their concatenation. -/
theorem atPath_append (value : Value) (firstPath secondPath : List Field) :
    extension.atPath value (firstPath ++ secondPath) =
      (extension.atPath value firstPath).bind (fun child => extension.atPath child secondPath) := by
  induction firstPath generalizing value with
  | nil => rfl
  | cons field rest ih =>
    cases projected : extension.subdictionary value field <;>
      simp [atPath, projected, ih]

theorem subdictionary_dictionary (entries child : Dictionary Field Symbol Value)
    (field : Field) (found : lookup entries field = some (.subdictionary child)) :
    extension.subdictionary (extension.dictionary entries) field =
      some (extension.dictionary child) := by
  simp [subdictionary, extension.project_dictionary, found]

theorem subdictionary_sound {value child : Value} {field : Field}
    (found : extension.subdictionary value field = some child) :
    ∃ entries, extension.project value field = some (.subdictionary entries) ∧
      child = extension.dictionary entries := by
  unfold subdictionary at found
  cases projected : extension.project value field with
  | none => simp [projected] at found
  | some node =>
    cases node with
    | callable entry => simp [projected] at found
    | subdictionary entries =>
      simp only [projected, bind, Option.bind, Option.some.injEq] at found
      exact ⟨entries, rfl, found.symm⟩

theorem lookupAs_sound {value : Value} {field : Field} {role : Role}
    {entry : Entry Symbol Value} (found : extension.lookupAs value field role = some entry) :
    extension.project value field = some (.callable entry) ∧ entry.role = role ∧
      extension.roleOf entry.symbol = role := by
  unfold lookupAs at found
  cases projected : extension.project value field with
  | none => simp [projected] at found
  | some node =>
    cases node with
    | subdictionary entries => simp [projected] at found
    | callable actual =>
      simp only [projected, bind, Option.bind] at found
      split at found
      next valid =>
        cases Option.some.inj found
        exact ⟨rfl, valid⟩
      next => contradiction

theorem lookupAs_dictionary (entries : Dictionary Field Symbol Value) (field : Field)
    (role : Role) (entry : Entry Symbol Value)
    (found : lookup entries field = some (.callable entry))
    (tag : entry.role = role) (declared : extension.roleOf entry.symbol = role) :
    extension.lookupAs (extension.dictionary entries) field role = some entry := by
  simp [lookupAs, extension.project_dictionary, found, tag, declared]

theorem lookupPathAs_sound {value : Value} {path : List Field} {field : Field}
    {role : Role} {entry : Entry Symbol Value}
    (found : extension.lookupPathAs value path field role = some entry) :
    ∃ child, extension.atPath value path = some child ∧
      extension.project child field = some (.callable entry) ∧
      entry.role = role ∧ extension.roleOf entry.symbol = role := by
  unfold lookupPathAs at found
  cases located : extension.atPath value path with
  | none => simp [located] at found
  | some child =>
    simp only [located, bind, Option.bind] at found
    exact ⟨child, rfl, extension.lookupAs_sound found⟩

end Extension

/-- Interpret the syntax-level call using checked operation lookup. Field labels
share `Term`'s symbol namespace. A missing/invalid access denotes an explicitly
chosen value; this choice is not a search-failure certificate. -/
def Extension.withDictionaryCalls [DecidableEq Symbol]
    (extension : Extension model Symbol) (invalid : Value) :
    Semantics.Model Literal Symbol Value hoApplySymbol :=
  { model with dictionaryCall := fun value path operation args =>
      match extension.lookupPathAs value path operation .operation with
      | some entry => extension.invoke entry args
      | none => invalid }

/-- Successful dictionary calls agree with direct application as values,
including captured arguments. This is the link from the new syntax to lookup. -/
theorem Extension.eval_dictionaryCall [DecidableEq Variable] [DecidableEq Symbol]
    (extension : Extension model Symbol) (invalid : Value)
    (environment : Semantics.Environment Variable Value)
    (dictionary : Term Variable Literal Symbol) (path : List Symbol) (operation : Symbol)
    (args : List (Term Variable Literal Symbol)) (entry : Entry Symbol Value)
    (found : extension.lookupPathAs
      ((extension.withDictionaryCalls invalid).eval environment dictionary)
      path operation .operation = some entry) :
    (extension.withDictionaryCalls invalid).eval environment
      (.dictionaryCall dictionary path operation args) =
        model.application entry.symbol (entry.captures ++
          args.map ((extension.withDictionaryCalls invalid).eval environment)) := by
  simp only [Semantics.Model.eval, withDictionaryCalls] at found ⊢
  rw [found]
  exact extension.invoke_eq entry _

/-- Interfaces form a finite tree of required models. At each node, laws are
explicit predicates on that dictionary value, such as closure and equations. -/
inductive Interface (Field Value : Type) where
  | mk (required : List (Field × Role))
      (requiredModels : List (Field × Interface Field Value))
      (laws : Value → Prop)

def Implements (extension : Extension model Field) (value : Value)
    (interface : Interface Field Value) : Prop :=
  match interface with
  | .mk required requiredModels laws =>
    (∀ field role, (field, role) ∈ required →
      ∃ entry, extension.lookupAs value field role = some entry) ∧
    (∀ field childInterface, (field, childInterface) ∈ requiredModels →
      ∃ child, extension.subdictionary value field = some child ∧
        Implements extension child childInterface) ∧ laws value
termination_by sizeOf interface
decreasing_by
  have smaller := List.sizeOf_lt_of_mem (by assumption)
  simp_all only [Prod.mk.sizeOf_spec, Interface.mk.sizeOf_spec]
  omega

/-- A parent interface supplies an actual subdictionary satisfying the child's
interface, including its own required models and semantic laws. -/
theorem Implements.required_model (extension : Extension model Field) {value : Value}
    {required : List (Field × Role)} {requiredModels : List (Field × Interface Field Value)}
    {laws : Value → Prop}
    (valid : Implements extension value (.mk required requiredModels laws))
    (field : Field) (childInterface : Interface Field Value)
    (member : (field, childInterface) ∈ requiredModels) :
    ∃ child, extension.subdictionary value field = some child ∧
      Implements extension child childInterface := by
  rw [Implements] at valid
  exact valid.2.1 field childInterface member

end AnthillModKbSpec.OperationDictionaries
