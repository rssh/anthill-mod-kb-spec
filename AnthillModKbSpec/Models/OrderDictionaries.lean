import AnthillModKbSpec.Foundation.OperationDictionaries

namespace AnthillModKbSpec.OrderDictionaries

open OperationDictionaries

/-- Field labels and callable symbols share the untyped syntax's namespace. -/
inductive Symbol where
  | member | weakOrd | eqModel | compare | equal
  | isNat | isBool | natCompare | boolCompare | natEqual | boolEqual | hoApply
  deriving DecidableEq, Repr

inductive Data where
  | nat : Nat → Data
  | bool : Bool → Data
  | ordering : Ordering → Data
  deriving DecidableEq, Repr

/-- One untyped carrier for both domains, callable references, dictionary trees,
and logical values. The proposition constructor supports unrestricted forall. -/
inductive Value where
  | data : Data → Value
  | reference : Symbol → Value
  | callable : Entry Symbol Value → Value
  | dictionary : List (Symbol × Value) → Value
  | proposition : Prop → Value
  | invalid

abbrev nat (n : Nat) : Value := .data (.nat n)
abbrev boolean (b : Bool) : Value := .data (.bool b)
abbrev ordering (o : Ordering) : Value := .data (.ordering o)

def encode (node : Node Symbol Symbol Value) : Value := match node with
  | .callable entry => .callable entry
  | .subdictionary entries =>
    .dictionary (entries.map (fun pair => (pair.1, encode pair.2)))
termination_by sizeOf node
decreasing_by
  have smaller := List.sizeOf_lt_of_mem (by assumption)
  cases pair
  simp_all only [Prod.mk.sizeOf_spec, Node.subdictionary.sizeOf_spec]
  omega

def decode (value : Value) : Node Symbol Symbol Value := match value with
  | .callable entry => .callable entry
  | .dictionary entries =>
    .subdictionary (entries.map (fun pair => (pair.1, decode pair.2)))
  | _ => .subdictionary []
termination_by sizeOf value
decreasing_by
  have smaller := List.sizeOf_lt_of_mem (by assumption)
  cases pair
  simp_all only [Prod.mk.sizeOf_spec, Value.dictionary.sizeOf_spec]
  omega

theorem decode_encode (node : Node Symbol Symbol Value) : decode (encode node) = node := by
  cases node with
  | callable entry => simp [encode, decode]
  | subdictionary entries =>
    simp only [encode, decode, List.map_map]
    congr 1
    calc
      _ = entries.map id := by
        apply List.map_congr_left
        intro pair member
        rcases pair with ⟨field, child⟩
        simp only [Function.comp_def, id_eq]
        rw [decode_encode child]
      _ = entries := List.map_id entries
termination_by sizeOf node
decreasing_by
  have smaller := List.sizeOf_lt_of_mem (by assumption)
  simp_all only [Prod.mk.sizeOf_spec, Node.subdictionary.sizeOf_spec]
  omega

def compareNat (a b : Nat) : Ordering :=
  if a < b then .lt else if a = b then .eq else .gt

def boolRank : Bool → Nat
  | false => 0
  | true => 1

def primitive (symbol : Symbol) (args : List Value) : Value :=
  match symbol, args with
  | .natCompare, [.data (.nat a), .data (.nat b)] => ordering (compareNat a b)
  | .boolCompare, [.data (.bool a), .data (.bool b)] => ordering (compareNat (boolRank a) (boolRank b))
  | .natEqual, [.data (.nat a), .data (.nat b)] => boolean (decide (a = b))
  | .boolEqual, [.data (.bool a), .data (.bool b)] => boolean (a == b)
  | .isNat, [.data (.nat _)] | .isBool, [.data (.bool _)] => boolean true
  | .isNat, [_] | .isBool, [_] => boolean false
  | _, [] => .reference symbol
  | _, _ => .invalid

/-- Concrete-symbol ho_apply and dictionary references use the same callable
interpretation. Every recursive ho_apply removes one argument. -/
def application (symbol : Symbol) (args : List Value) : Value :=
  match symbol, args with
  | .hoApply, .reference predicate :: rest => application predicate rest
  | _, _ => primitive symbol args
termination_by args.length

@[simp] theorem application_nil (symbol : Symbol) : application symbol [] = .reference symbol := by
  cases symbol <;> simp [application, primitive]

def holds : Value → Prop
  | .data (.bool b) => b = true
  | .proposition p => p
  | _ => False

def baseModel : Semantics.Model Data Symbol Value .hoApply where
  inhabitant := .invalid
  literal := Value.data
  application := application
  holds := holds
  top := .proposition True
  bottom := .invalid
  conjunction := fun a b => .proposition (holds a ∧ holds b)
  disjunction := fun a b => .proposition (holds a ∨ holds b)
  implication := fun a b => .proposition (holds a → holds b)
  universal := fun f => .proposition (∀ value, holds (f value))
  existential := fun f => .proposition (∃ value, holds (f value))
  defaultNegation := fun value => .proposition (¬ holds value)
  equality := fun a b => .proposition (a = b)
  holds_top := True.intro
  holds_bottom := id
  holds_conjunction := fun _ _ => Iff.rfl
  holds_disjunction := fun _ _ => Iff.rfl
  holds_implication := fun _ _ => Iff.rfl
  holds_universal := fun _ => Iff.rfl
  holds_existential := fun _ => Iff.rfl
  defaultNegation_coherent := fun _ => id
  holds_equality := fun _ _ => Iff.rfl
  holds_hoApply := by
    intro predicate args
    rw [application_nil, application]

def extension : Extension baseModel Symbol where
  roleOf := fun | .isNat | .isBool => .predicate | _ => .operation
  reference := Value.reference
  call := fun value args => match value with
    | .reference symbol => application symbol args
    | _ => .invalid
  dictionary := fun entries => encode (.subdictionary entries)
  project := fun value field => match value with
    | .dictionary entries => (lookup entries field).map decode
    | _ => none
  call_reference := fun _ _ => rfl
  project_dictionary := by
    intro entries field
    simp only [encode, lookup_map, Option.map_map]
    have identity : decode ∘ encode = id := by
      funext node
      exact decode_encode node
    simp [identity]

@[simp] theorem project_dictionary (entries : Dictionary Symbol Symbol Value) (field : Symbol) :
    extension.project (extension.dictionary entries) field = lookup entries field :=
  extension.project_dictionary entries field

@[simp] theorem roleOf (symbol : Symbol) : extension.roleOf symbol =
    (match symbol with | .isNat | .isBool => .predicate | _ => .operation) := rfl

def model := extension.withDictionaryCalls .invalid

/-- Minimal Ord tree: the order supplies a WeakOrd dictionary, with compare and
its required Eq dictionary. Membership guards its untyped semantic laws. -/
def eqDictionary (equality : Symbol) : Dictionary Symbol Symbol Value :=
  [(.equal, .callable ⟨.operation, equality, []⟩)]

def weakDictionary (comparison equality : Symbol) : Dictionary Symbol Symbol Value :=
  [(.compare, .callable ⟨.operation, comparison, []⟩),
   (.eqModel, .subdictionary (eqDictionary equality))]

def dictionary (membership comparison equality : Symbol) : Dictionary Symbol Symbol Value :=
  [(.member, .callable ⟨.predicate, membership, []⟩),
   (.weakOrd, .subdictionary (weakDictionary comparison equality))]

def natOrd : Value := extension.dictionary (dictionary .isNat .natCompare .natEqual)
def boolOrd : Value := extension.dictionary (dictionary .isBool .boolCompare .boolEqual)

def comparison (dict a b : Value) : Value :=
  model.dictionaryCall dict [.weakOrd] .compare [a, b]

def equality (dict a b : Value) : Value :=
  model.dictionaryCall dict [.weakOrd, .eqModel] .equal [a, b]

def LessEq (dict a b : Value) : Prop :=
  comparison dict a b = ordering .lt ∨ comparison dict a b = ordering .eq

def NatDomain (value : Value) : Prop := ∃ n, value = nat n
def BoolDomain (value : Value) : Prop := ∃ b, value = boolean b

def Member (dict value : Value) : Prop :=
  ∃ entry, extension.lookupAs dict .member .predicate = some entry ∧
    model.holds (extension.invoke entry [value])

theorem member_dictionary (membership comparison equality : Symbol)
    (role : extension.roleOf membership = .predicate) (value : Value) :
    Member (extension.dictionary (dictionary membership comparison equality)) value ↔
      holds (application membership [value]) := by
  simp only [roleOf] at role
  simp [Member, Extension.lookupAs, dictionary, lookup, role]
  rw [extension.invoke_eq]
  rfl

theorem nat_member_exact (value : Value) : Member natOrd value ↔ NatDomain value := by
  rw [natOrd, member_dictionary _ _ _ rfl]
  cases value <;> simp [application, primitive, holds, NatDomain]
  rename_i payload
  cases payload <;> simp

theorem bool_member_exact (value : Value) : Member boolOrd value ↔ BoolDomain value := by
  rw [boolOrd, member_dictionary _ _ _ rfl]
  cases value <;> simp [application, primitive, holds, BoolDomain]
  rename_i payload
  cases payload <;> simp

/-- The laws are guarded by a domain predicate on the common untyped carrier. -/
structure OrdLaws (domain : Value → Prop) (dict : Value) : Prop where
  returnsOrdering : ∀ a b, domain a → domain b → ∃ result, comparison dict a b = ordering result
  reflexive : ∀ a, domain a → LessEq dict a a
  transitive : ∀ a b c, domain a → domain b → domain c →
    LessEq dict a b → LessEq dict b c → LessEq dict a c
  antisymmetric : ∀ a b, domain a → domain b → LessEq dict a b → LessEq dict b a → a = b
  total : ∀ a b, domain a → domain b → LessEq dict a b ∨ LessEq dict b a
  equality_correct : ∀ a b, domain a → domain b → (equality dict a b = boolean true ↔ a = b)
  compare_eq : ∀ a b, domain a → domain b →
    (comparison dict a b = ordering .eq ↔ equality dict a b = boolean true)

def rank : Value → Nat
  | .data (.nat n) => n
  | .data (.bool b) => boolRank b
  | _ => 0

theorem compareNat_eq (a b : Nat) : compareNat a b = .eq ↔ a = b := by
  by_cases less : a < b <;> by_cases same : a = b <;> simp [compareNat, less, same] <;> omega

theorem compareNat_le (a b : Nat) :
    (ordering (compareNat a b) = ordering .lt ∨ ordering (compareNat a b) = ordering .eq) ↔ a ≤ b := by
  by_cases less : a < b <;> by_cases same : a = b <;> simp [compareNat, less, same] <;> omega

theorem lookup_compare (membership comparison equality : Symbol)
    (role : extension.roleOf comparison = .operation) :
    extension.lookupPathAs (extension.dictionary (dictionary membership comparison equality))
      [.weakOrd] .compare .operation = some ⟨.operation, comparison, []⟩ := by
  simp only [roleOf] at role
  simp [Extension.lookupPathAs, Extension.atPath, Extension.subdictionary,
    Extension.lookupAs, dictionary, weakDictionary, lookup, role]

theorem lookup_equal (membership comparison equality : Symbol)
    (role : extension.roleOf equality = .operation) :
    extension.lookupPathAs (extension.dictionary (dictionary membership comparison equality))
      [.weakOrd, .eqModel] .equal .operation = some ⟨.operation, equality, []⟩ := by
  simp only [roleOf] at role
  simp [Extension.lookupPathAs, Extension.atPath, Extension.subdictionary,
    Extension.lookupAs, dictionary, weakDictionary, eqDictionary, lookup, role]

@[simp] theorem nat_comparison (a b : Nat) :
    comparison natOrd (nat a) (nat b) = ordering (compareNat a b) := by
  simp only [comparison, model, Extension.withDictionaryCalls, natOrd]
  rw [lookup_compare _ _ _ rfl]
  simp only [Extension.invoke_eq]
  simp [baseModel, application, primitive]

@[simp] theorem bool_comparison (a b : Bool) :
    comparison boolOrd (boolean a) (boolean b) = ordering (compareNat (boolRank a) (boolRank b)) := by
  simp only [comparison, model, Extension.withDictionaryCalls, boolOrd]
  rw [lookup_compare _ _ _ rfl]
  simp only [Extension.invoke_eq]
  simp [baseModel, application, primitive]

@[simp] theorem nat_equality (a b : Nat) :
    equality natOrd (nat a) (nat b) = boolean (decide (a = b)) := by
  simp only [equality, model, Extension.withDictionaryCalls, natOrd]
  rw [lookup_equal _ _ _ rfl]
  simp only [Extension.invoke_eq]
  simp [baseModel, application, primitive]

@[simp] theorem bool_equality (a b : Bool) :
    equality boolOrd (boolean a) (boolean b) = boolean (a == b) := by
  simp only [equality, model, Extension.withDictionaryCalls, boolOrd]
  rw [lookup_equal _ _ _ rfl]
  simp only [Extension.invoke_eq]
  simp [baseModel, application, primitive]

/-- A common proof discharges both instances via their injective Nat ranks. -/
theorem laws_of_rank {domain : Value → Prop} {dict : Value}
    (comp : ∀ a b, domain a → domain b → comparison dict a b = ordering (compareNat (rank a) (rank b)))
    (eqCorrect : ∀ a b, domain a → domain b → (equality dict a b = boolean true ↔ a = b))
    (injective : ∀ a b, domain a → domain b → rank a = rank b → a = b) : OrdLaws domain dict := by
  have le : ∀ a b, domain a → domain b → (LessEq dict a b ↔ rank a ≤ rank b) := by
    intro a b ha hb
    simp only [LessEq, comp a b ha hb]
    exact compareNat_le _ _
  constructor
  · intro a b ha hb; exact ⟨_, comp a b ha hb⟩
  · intro a ha; exact (le a a ha ha).mpr (Nat.le_refl _)
  · intro a b c ha hb hc hab hbc
    exact (le a c ha hc).mpr (Nat.le_trans ((le a b ha hb).mp hab) ((le b c hb hc).mp hbc))
  · intro a b ha hb hab hba
    exact injective a b ha hb (Nat.le_antisymm ((le a b ha hb).mp hab) ((le b a hb ha).mp hba))
  · intro a b ha hb
    rcases Nat.le_total (rank a) (rank b) with hab | hba
    · exact Or.inl ((le a b ha hb).mpr hab)
    · exact Or.inr ((le b a hb ha).mpr hba)
  · exact eqCorrect
  · intro a b ha hb
    rw [comp a b ha hb, eqCorrect a b ha hb]
    simp only [ordering, Value.data.injEq, Data.ordering.injEq, compareNat_eq]
    exact ⟨injective a b ha hb, fun equal => congrArg rank equal⟩

theorem nat_laws : OrdLaws NatDomain natOrd := by
  apply laws_of_rank
  · intro a b ha hb
    rcases ha with ⟨n, rfl⟩; rcases hb with ⟨m, rfl⟩
    exact nat_comparison n m
  · intro a b ha hb
    rcases ha with ⟨n, rfl⟩; rcases hb with ⟨m, rfl⟩
    simp
  · intro a b ha hb equal
    rcases ha with ⟨n, rfl⟩; rcases hb with ⟨m, rfl⟩
    exact congrArg nat equal

theorem bool_laws : OrdLaws BoolDomain boolOrd := by
  apply laws_of_rank
  · intro a b ha hb
    rcases ha with ⟨n, rfl⟩; rcases hb with ⟨m, rfl⟩
    exact bool_comparison n m
  · intro a b ha hb
    rcases ha with ⟨n, rfl⟩; rcases hb with ⟨m, rfl⟩
    cases n <;> cases m <;> simp
  · intro a b ha hb equal
    rcases ha with ⟨n, rfl⟩; rcases hb with ⟨m, rfl⟩
    cases n <;> cases m <;> simp_all [rank, boolRank]

/-- The required Eq dictionary has its own semantic law. -/
def EqLaws (domain : Value → Prop) (dict : Value) : Prop :=
  ∀ a b, domain a → domain b →
    (model.dictionaryCall dict [] .equal [a, b] = boolean true ↔ a = b)

theorem eq_call (symbol : Symbol) (role : extension.roleOf symbol = .operation) (a b : Value) :
    model.dictionaryCall (extension.dictionary (eqDictionary symbol)) [] .equal [a, b] =
      application symbol [a, b] := by
  simp only [roleOf] at role
  simp [model, Extension.withDictionaryCalls, Extension.lookupPathAs, Extension.atPath,
    Extension.lookupAs, eqDictionary, lookup, role]
  exact extension.invoke_eq _ _

theorem nat_eq_laws : EqLaws NatDomain (extension.dictionary (eqDictionary .natEqual)) := by
  intro a b ha hb
  rcases ha with ⟨n, rfl⟩; rcases hb with ⟨m, rfl⟩
  rw [eq_call _ rfl]
  simp [application, primitive]

theorem bool_eq_laws : EqLaws BoolDomain (extension.dictionary (eqDictionary .boolEqual)) := by
  intro a b ha hb
  rcases ha with ⟨n, rfl⟩; rcases hb with ⟨m, rfl⟩
  rw [eq_call _ rfl]
  cases n <;> cases m <;> simp [application, primitive]

def eqInterface (domain : Value → Prop) : Interface Symbol Value :=
  .mk [(.equal, .operation)] [] (EqLaws domain)

def weakOrdInterface (domain : Value → Prop) : Interface Symbol Value :=
  .mk [(.compare, .operation)] [(.eqModel, eqInterface domain)] (fun _ => True)

def ordInterface (domain : Value → Prop) : Interface Symbol Value :=
  .mk [(.member, .predicate)] [(.weakOrd, weakOrdInterface domain)]
    (fun dict => (∀ value, Member dict value ↔ domain value) ∧ OrdLaws domain dict)

theorem nat_implements : Implements extension natOrd (ordInterface NatDomain) := by
  simp only [ordInterface, Implements]
  refine ⟨?_, ?_, nat_member_exact, nat_laws⟩
  · simp [natOrd, dictionary, Extension.lookupAs, lookup]
  · simp [natOrd, dictionary, weakOrdInterface, eqInterface, Implements,
      Extension.subdictionary, Extension.lookupAs, weakDictionary, eqDictionary, lookup]
    exact nat_eq_laws

theorem bool_implements : Implements extension boolOrd (ordInterface BoolDomain) := by
  simp only [ordInterface, Implements]
  refine ⟨?_, ?_, bool_member_exact, bool_laws⟩
  · simp [boolOrd, dictionary, Extension.lookupAs, lookup]
  · simp [boolOrd, dictionary, weakOrdInterface, eqInterface, Implements,
      Extension.subdictionary, Extension.lookupAs, weakDictionary, eqDictionary, lookup]
    exact bool_eq_laws

/-- The same untyped term works with either order dictionary. -/
def compareTerm (dict a b : Term Variable Data Symbol) : Term Variable Data Symbol :=
  .dictionaryCall dict [.weakOrd] .compare [a, b]

def equalTerm (dict a b : Term Variable Data Symbol) : Term Variable Data Symbol :=
  .dictionaryCall dict [.weakOrd, .eqModel] .equal [a, b]

theorem eval_compareTerm [DecidableEq Variable] (environment : Semantics.Environment Variable Value)
    (dict a b : Term Variable Data Symbol) :
    model.eval environment (compareTerm dict a b) = comparison
      (model.eval environment dict) (model.eval environment a) (model.eval environment b) := by
  simp [compareTerm, Semantics.Model.eval, comparison]

theorem eval_equalTerm [DecidableEq Variable] (environment : Semantics.Environment Variable Value)
    (dict a b : Term Variable Data Symbol) :
    model.eval environment (equalTerm dict a b) = equality
      (model.eval environment dict) (model.eval environment a) (model.eval environment b) := by
  simp [equalTerm, Semantics.Model.eval, equality]

end AnthillModKbSpec.OrderDictionaries
