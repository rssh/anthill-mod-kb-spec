import AnthillModKbSpec.Foundation.OperationDictionaries
import AnthillModKbSpec.Foundation.InductiveDomains

namespace AnthillModKbSpec.OrderDictionaries

open OperationDictionaries InductiveDomains

/-- Field labels and callable symbols share the untyped syntax's namespace.
`zero`, `succ`, `boolTrue`, and `boolFalse` construct the Nat and Bool data;
`natOrd`, `natDesc`, and `boolOrd` name dictionaries, and `aliasOrd` is a
second name for `natOrd`'s value. `ordDictionary` and `domainMember` are the
relations `OrdDictionary(d)` and `DomainMember(d, x)`; `isData` and `isPred`
name all data and the predicate references; `asymmetric`, `lessCompare`, and
`equalCompare` name laws. -/
inductive Symbol where
  | member | weakOrd | eqModel | compare | equal | less
  | isNat | isBool | isData | isPred
  | natCompare | boolCompare | natEqual | boolEqual | natLess | boolLess
  | natCompareDesc | natLessDesc
  | zero | succ | boolTrue | boolFalse
  | natOrd | natDesc | boolOrd | aliasOrd
  | ordDictionary | domainMember
  | asymmetric | lessCompare | equalCompare
  | hoApply
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

def NatDomain (value : Value) : Prop := ∃ n, value = nat n
def BoolDomain (value : Value) : Prop := ∃ b, value = boolean b

/-- Minimal Ord tree: the order supplies `less` and a WeakOrd dictionary, with
compare and its required Eq dictionary. Membership guards its untyped laws. -/
def eqDictionary (equality : Symbol) : Dictionary Symbol Symbol Value :=
  [(.equal, .callable ⟨.operation, equality, []⟩)]

def weakDictionary (comparison equality : Symbol) : Dictionary Symbol Symbol Value :=
  [(.compare, .callable ⟨.operation, comparison, []⟩),
   (.eqModel, .subdictionary (eqDictionary equality))]

def dictionary (membership comparison equality order : Symbol) : Dictionary Symbol Symbol Value :=
  [(.member, .callable ⟨.predicate, membership, []⟩),
   (.less, .callable ⟨.operation, order, []⟩),
   (.weakOrd, .subdictionary (weakDictionary comparison equality))]

/-- Two dictionaries for Nat, ascending and descending, and one for Bool. -/
def natOrd : Value := encode (.subdictionary (dictionary .isNat .natCompare .natEqual .natLess))
def natDesc : Value := encode (.subdictionary (dictionary .isNat .natCompareDesc .natEqual .natLessDesc))
def boolOrd : Value := encode (.subdictionary (dictionary .isBool .boolCompare .boolEqual .boolLess))

/-- The unary predicates and what each holds of: the one place their meaning
is stated. They return logical values (`primitive`), and a dictionary may hold
any of them as its member field (`roleOf`). `DomainMember`, binary and read
off the dictionary, is a relation of the registry and no dictionary entry. -/
def predicateTruth : Symbol → Option (Value → Prop)
  | .isNat => some NatDomain
  | .isBool => some BoolDomain
  | .isData => some fun value => NatDomain value ∨ BoolDomain value
  | .isPred => some fun _ => False
  | .ordDictionary => some fun value => value = natOrd ∨ value = natDesc ∨ value = boolOrd
  | _ => none

/-- The truth of a member predicate at a value; false for an operation. -/
def memberTruth (symbol : Symbol) (value : Value) : Prop :=
  match predicateTruth symbol with
  | some truth => truth value
  | none => False

/-- `DomainMember(d, x)` reads d's own member field: a predicate entry without
captures, true at x. It looks nothing up in a table of dictionaries. -/
def domainTruth : Value → Value → Prop
  | .dictionary entries, value => ∃ entry, lookup entries .member = some (.callable entry) ∧
      entry.role = .predicate ∧ entry.captures = [] ∧ memberTruth entry.symbol value
  | _, _ => False

/-- Operations return data. Nullary constants denote Nat and Bool data and the
named dictionaries; every other symbol applied to nothing is its reference. -/
def operationValue (symbol : Symbol) (args : List Value) : Value :=
  match symbol, args with
  | .natCompare, [.data (.nat a), .data (.nat b)] => ordering (compareNat a b)
  | .natCompareDesc, [.data (.nat a), .data (.nat b)] => ordering (compareNat b a)
  | .boolCompare, [.data (.bool a), .data (.bool b)] => ordering (compareNat (boolRank a) (boolRank b))
  | .natEqual, [.data (.nat a), .data (.nat b)] => boolean (decide (a = b))
  | .boolEqual, [.data (.bool a), .data (.bool b)] => boolean (a == b)
  | .natLess, [.data (.nat a), .data (.nat b)] => boolean (decide (a < b))
  | .natLessDesc, [.data (.nat a), .data (.nat b)] => boolean (decide (b < a))
  | .boolLess, [.data (.bool a), .data (.bool b)] => boolean (decide (boolRank a < boolRank b))
  | .domainMember, [dict, value] => .proposition (domainTruth dict value)
  | .zero, [] => nat 0
  | .succ, [.data (.nat n)] => nat (n + 1)
  | .boolTrue, [] => boolean true
  | .boolFalse, [] => boolean false
  | .natOrd, [] => natOrd
  | .natDesc, [] => natDesc
  | .boolOrd, [] => boolOrd
  | .aliasOrd, [] => natOrd
  | _, [] => .reference symbol
  | _, _ => .invalid

/-- Predicates return logical values, by `predicateTruth`; the relation
`DomainMember` returns one too; operations return data. -/
def primitive (symbol : Symbol) (args : List Value) : Value :=
  match predicateTruth symbol, args with
  | some truth, [value] => .proposition (truth value)
  | some _, [] => .reference symbol
  | some _, _ => .invalid
  | none, _ => operationValue symbol args

/-- Concrete-symbol ho_apply and dictionary references use the same callable
interpretation. Every recursive ho_apply removes one argument. -/
def application (symbol : Symbol) (args : List Value) : Value :=
  match symbol, args with
  | .hoApply, .reference predicate :: rest => application predicate rest
  | _, _ => primitive symbol args
termination_by args.length

theorem application_primitive {symbol : Symbol} (other : symbol ≠ .hoApply) (args : List Value) :
    application symbol args = primitive symbol args :=
  application.eq_2 symbol args (fun _ _ same _ => other same)

theorem application_hoApply (predicate : Symbol) (args : List Value) :
    application .hoApply (.reference predicate :: args) = application predicate args := by
  rw [application]

/-- Only logical values hold. Numbers, Booleans, orderings, references, and
dictionaries are data: a Boolean result is compared with `true`, never read as
truth. -/
def holds : Value → Prop
  | .proposition p => p
  | _ => False

/-- The nullary constants that denote data or dictionaries, not references. -/
def Constant (symbol : Symbol) : Prop :=
  symbol = .zero ∨ symbol = .boolTrue ∨ symbol = .boolFalse ∨ symbol = .natOrd ∨
    symbol = .natDesc ∨ symbol = .boolOrd ∨ symbol = .aliasOrd

theorem application_nil {symbol : Symbol} (other : ¬ Constant symbol) :
    application symbol [] = .reference symbol := by
  unfold Constant at other
  cases symbol <;> simp_all [application, primitive, predicateTruth, operationValue]

theorem holds_hoApply (predicate : Symbol) (args : List Value) :
    holds (application .hoApply (application predicate [] :: args)) ↔ holds (application predicate args) := by
  by_cases constant : Constant predicate
  · unfold Constant at constant
    rcases constant with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      cases args <;> simp [application, primitive, predicateTruth, operationValue, holds, natOrd, natDesc, boolOrd, encode]
  · rw [application_nil constant, application_hoApply]

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
  holds_hoApply := holds_hoApply

def extension : Extension baseModel Symbol where
  roleOf := fun symbol => if (predicateTruth symbol).isSome then .predicate else .operation
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
    if (predicateTruth symbol).isSome then .predicate else .operation := rfl

theorem role_predicate {symbol : Symbol} : extension.roleOf symbol = .predicate ↔ predicateTruth symbol ≠ none := by
  rw [roleOf]; cases predicateTruth symbol <;> simp

theorem role_operation {symbol : Symbol} : extension.roleOf symbol = .operation ↔ predicateTruth symbol = none := by
  rw [roleOf]; cases predicateTruth symbol <;> simp

theorem natOrd_eq : natOrd = extension.dictionary (dictionary .isNat .natCompare .natEqual .natLess) := rfl
theorem natDesc_eq : natDesc = extension.dictionary (dictionary .isNat .natCompareDesc .natEqual .natLessDesc) := rfl
theorem boolOrd_eq : boolOrd = extension.dictionary (dictionary .isBool .boolCompare .boolEqual .boolLess) := rfl

def model := extension.withDictionaryCalls .invalid

def comparison (dict a b : Value) : Value :=
  model.dictionaryCall dict [.weakOrd] .compare [a, b]

def equality (dict a b : Value) : Value :=
  model.dictionaryCall dict [.weakOrd, .eqModel] .equal [a, b]

def lessThan (dict a b : Value) : Value :=
  model.dictionaryCall dict [] .less [a, b]

def LessEq (dict a b : Value) : Prop :=
  comparison dict a b = ordering .lt ∨ comparison dict a b = ordering .eq

def Member (dict value : Value) : Prop :=
  ∃ entry, extension.lookupAs dict .member .predicate = some entry ∧
    model.holds (extension.invoke entry [value])

theorem member_dictionary (membership comparison equality order : Symbol)
    (role : extension.roleOf membership = .predicate) (value : Value) :
    Member (extension.dictionary (dictionary membership comparison equality order)) value ↔
      holds (application membership [value]) := by
  rw [role_predicate] at role
  simp [Member, Extension.lookupAs, dictionary, lookup, role]
  rw [extension.invoke_eq]
  rfl

theorem holds_isNat (value : Value) : holds (application .isNat [value]) ↔ NatDomain value := by
  rw [application_primitive (by decide)]
  exact Iff.rfl

theorem holds_isBool (value : Value) : holds (application .isBool [value]) ↔ BoolDomain value := by
  rw [application_primitive (by decide)]
  exact Iff.rfl

theorem nat_member_exact (value : Value) : Member natOrd value ↔ NatDomain value := by
  rw [natOrd_eq, member_dictionary _ _ _ _ rfl, holds_isNat]

theorem desc_member_exact (value : Value) : Member natDesc value ↔ NatDomain value := by
  rw [natDesc_eq, member_dictionary _ _ _ _ rfl, holds_isNat]

theorem bool_member_exact (value : Value) : Member boolOrd value ↔ BoolDomain value := by
  rw [boolOrd_eq, member_dictionary _ _ _ _ rfl, holds_isBool]

@[simp] theorem project_value (entries : List (Symbol × Value)) (field : Symbol) :
    extension.project (.dictionary entries) field = (lookup entries field).map decode := rfl

theorem invoke_value (entry : Entry Symbol Value) (args : List Value) :
    extension.invoke entry args = application entry.symbol (entry.captures ++ args) := rfl

/-- A member predicate holds at a value only when called without captures. -/
theorem predicate_of_role {symbol : Symbol} (declared : extension.roleOf symbol = .predicate) :
    ∃ truth, predicateTruth symbol = some truth := by
  rw [roleOf] at declared
  cases found : predicateTruth symbol with
  | none => simp [found] at declared
  | some truth => exact ⟨truth, rfl⟩

theorem holds_member {symbol : Symbol} (declared : extension.roleOf symbol = .predicate)
    (captures : List Value) (value : Value) :
    holds (application symbol (captures ++ [value])) ↔ captures = [] ∧ memberTruth symbol value := by
  obtain ⟨truth, found⟩ := predicate_of_role declared
  have other : symbol ≠ .hoApply := by rintro rfl; simp [predicateTruth] at found
  rw [application_primitive other]
  unfold memberTruth primitive
  rw [found]
  cases captures with
  | nil => exact ⟨fun holds => ⟨rfl, holds⟩, fun ⟨_, holds⟩ => holds⟩
  | cons first rest => cases rest <;> simp [holds]

/-- The model's `DomainMember` is the dictionary's own member field, for every
carrier value: a value with no predicate at `member` has no members. -/
theorem domainMember_exact (dict value : Value) :
    holds (application .domainMember [dict, value]) ↔ Member dict value := by
  rw [application_primitive (by decide)]
  show domainTruth dict value ↔ _
  cases dict with
  | dictionary entries =>
    unfold domainTruth Member Extension.lookupAs
    rw [project_value]
    cases found : lookup entries .member with
    | none => simp [found]
    | some node =>
      cases node
      case callable entry =>
        rcases entry with ⟨role, symbol, captures⟩
        simp only [found, Option.map_some, decode, Option.some.injEq, Value.callable.injEq, exists_eq_left',
          bind, Option.bind]
        by_cases accepted : role = .predicate ∧ extension.roleOf symbol = .predicate
        · simp only [accepted, and_self, ite_true, Option.some.injEq, exists_eq_left', invoke_value]
          obtain ⟨rfl, declared⟩ := accepted
          change _ ↔ holds _
          rw [holds_member declared]
          exact ⟨fun ⟨_, rest⟩ => rest, fun rest => ⟨by trivial, rest⟩⟩
        · simp only [accepted, ite_false, reduceCtorEq, false_and, exists_false, iff_false, not_and]
          intro role _ truth
          apply accepted
          refine ⟨role, ?_⟩
          unfold memberTruth at truth
          rw [roleOf]
          cases found : predicateTruth symbol with
          | none => rw [found] at truth; exact truth.elim
          | some _ => simp
      all_goals simp [decode, found]
  | _ => simp [domainTruth, Member, Extension.lookupAs, extension]

/-! ## Nat and Bool as declared domains -/

inductive Domain where
  | nat | bool
  deriving DecidableEq, Repr

def zeroRule : Rule Domain Symbol := ⟨.nat, .zero, []⟩
def succRule : Rule Domain Symbol := ⟨.nat, .succ, [.nat]⟩
def trueRule : Rule Domain Symbol := ⟨.bool, .boolTrue, []⟩
def falseRule : Rule Domain Symbol := ⟨.bool, .boolFalse, []⟩

def sigma : Definitions Domain Symbol := fun rule =>
  rule = zeroRule ∨ rule = succRule ∨ rule = trueRule ∨ rule = falseRule

def family : FiniteFamily Domain Symbol := ⟨sigma, [.nat, .bool], by intro domain; cases domain <;> simp⟩

def membershipSymbol : Domain → Symbol
  | .nat => .isNat
  | .bool => .isBool

/-- The values of a domain, as the model's membership predicates state them. -/
def domainOf : Domain → Value → Prop
  | .nat => NatDomain
  | .bool => BoolDomain

def natTree : Nat → Tree Symbol
  | 0 => .node .zero []
  | n + 1 => .node .succ [natTree n]

def boolTree (b : Bool) : Tree Symbol := .node (if b then .boolTrue else .boolFalse) []

theorem natTree_member (n : Nat) : InductiveDomains.Member sigma .nat (natTree n) := by
  induction n with
  | zero =>
      simpa [zeroRule, natTree] using InductiveDomains.Member.construct (rule := zeroRule)
        (sigma := sigma) (Or.inl rfl) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  | succ n ih =>
      simpa [succRule, natTree] using InductiveDomains.Member.construct (rule := succRule)
        (sigma := sigma) (Or.inr (Or.inl rfl)) (fun _ => natTree n) (fun i => by
          have same : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) i 0
          subst i
          exact ih)

theorem boolTree_member (b : Bool) : InductiveDomains.Member sigma .bool (boolTree b) := by
  cases b
  · simpa [falseRule, boolTree] using InductiveDomains.Member.construct (rule := falseRule)
      (sigma := sigma) (Or.inr (Or.inr (Or.inr rfl))) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  · simpa [trueRule, boolTree] using InductiveDomains.Member.construct (rule := trueRule)
      (sigma := sigma) (Or.inr (Or.inr (Or.inl rfl))) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

theorem natTree_denote (n : Nat) : denote model (natTree n) = nat n := by
  induction n with
  | zero => simp [natTree, denote, model, Extension.withDictionaryCalls, baseModel, application, primitive, predicateTruth, operationValue]
  | succ n ih =>
    simp only [natTree, denote, List.map_cons, List.map_nil, ih]
    simp [model, Extension.withDictionaryCalls, baseModel, application, primitive, predicateTruth, operationValue]

theorem boolTree_denote (b : Bool) : denote model (boolTree b) = boolean b := by
  cases b <;> simp [boolTree, denote, model, Extension.withDictionaryCalls, baseModel, application, primitive, predicateTruth, operationValue]

theorem member_denote {domain : Domain} {tree : Tree Symbol} (member : InductiveDomains.Member sigma domain tree) :
    domainOf domain (denote model tree) := by
  induction member with
  | construct declared children members ih =>
      rcases declared with rfl | rfl | rfl | rfl
      all_goals dsimp only [zeroRule, succRule, trueRule, falseRule] at children members ih ⊢
      · exact ⟨0, by simp [denote, model, Extension.withDictionaryCalls, baseModel, application, primitive, predicateTruth, operationValue]⟩
      · obtain ⟨n, same⟩ := ih 0
        refine ⟨n + 1, ?_⟩
        simp only [denote, List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil]
        rw [same]
        simp [model, Extension.withDictionaryCalls, baseModel, application, primitive, predicateTruth, operationValue]
      · exact ⟨true, by simp [denote, model, Extension.withDictionaryCalls, baseModel, application, primitive, predicateTruth, operationValue]⟩
      · exact ⟨false, by simp [denote, model, Extension.withDictionaryCalls, baseModel, application, primitive, predicateTruth, operationValue]⟩

/-- Exact realization: `isNat` and `isBool` hold precisely on the values the
constructors build. -/
theorem realizes : Realizes model sigma membershipSymbol := by
  intro domain value
  have truth : model.holds (model.application (membershipSymbol domain) [value]) ↔ domainOf domain value := by
    cases domain
    · exact holds_isNat value
    · exact holds_isBool value
  rw [truth]
  constructor
  · intro member
    cases domain
    · obtain ⟨n, rfl⟩ := member; exact ⟨natTree n, natTree_member n, natTree_denote n⟩
    · obtain ⟨b, rfl⟩ := member; exact ⟨boolTree b, boolTree_member b, boolTree_denote b⟩
  · rintro ⟨tree, member, rfl⟩
    exact member_denote member

/-! ## Laws -/

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
  returnsBool : ∀ a b, domain a → domain b → ∃ result, lessThan dict a b = boolean result
  less_compare : ∀ a b, domain a → domain b →
    (lessThan dict a b = boolean true ↔ comparison dict a b = ordering .lt)

def rank : Value → Nat
  | .data (.nat n) => n
  | .data (.bool b) => boolRank b
  | _ => 0

theorem compareNat_eq (a b : Nat) : compareNat a b = .eq ↔ a = b := by
  by_cases less : a < b <;> by_cases same : a = b <;> simp [compareNat, less, same] <;> omega

theorem compareNat_lt (a b : Nat) : compareNat a b = .lt ↔ a < b := by
  by_cases less : a < b <;> by_cases same : a = b <;> simp [compareNat, less, same]

theorem compareNat_le (a b : Nat) :
    (ordering (compareNat a b) = ordering .lt ∨ ordering (compareNat a b) = ordering .eq) ↔ a ≤ b := by
  by_cases less : a < b <;> by_cases same : a = b <;> simp [compareNat, less, same] <;> omega

theorem lookup_compare (membership comparison equality order : Symbol)
    (role : extension.roleOf comparison = .operation) :
    extension.lookupPathAs (extension.dictionary (dictionary membership comparison equality order))
      [.weakOrd] .compare .operation = some ⟨.operation, comparison, []⟩ := by
  rw [role_operation] at role
  simp [Extension.lookupPathAs, Extension.atPath, Extension.subdictionary,
    Extension.lookupAs, dictionary, weakDictionary, lookup, role]

theorem lookup_equal (membership comparison equality order : Symbol)
    (role : extension.roleOf equality = .operation) :
    extension.lookupPathAs (extension.dictionary (dictionary membership comparison equality order))
      [.weakOrd, .eqModel] .equal .operation = some ⟨.operation, equality, []⟩ := by
  rw [role_operation] at role
  simp [Extension.lookupPathAs, Extension.atPath, Extension.subdictionary,
    Extension.lookupAs, dictionary, weakDictionary, eqDictionary, lookup, role]

theorem lookup_less (membership comparison equality order : Symbol)
    (role : extension.roleOf order = .operation) :
    extension.lookupPathAs (extension.dictionary (dictionary membership comparison equality order))
      [] .less .operation = some ⟨.operation, order, []⟩ := by
  rw [role_operation] at role
  simp [Extension.lookupPathAs, Extension.atPath, Extension.lookupAs, dictionary, lookup, role]

/-- A call through a dictionary built by `dictionary` applies the stored symbol. -/
theorem call_dictionary (membership comparison equality order : Symbol)
    {path : List Symbol} {field symbol : Symbol}
    (found : extension.lookupPathAs (extension.dictionary (dictionary membership comparison equality order))
      path field .operation = some ⟨.operation, symbol, []⟩) (args : List Value) :
    model.dictionaryCall (extension.dictionary (dictionary membership comparison equality order)) path field args =
      application symbol args := by
  simp only [model, Extension.withDictionaryCalls]
  rw [found]
  rfl

@[simp] theorem nat_comparison (a b : Nat) :
    comparison natOrd (nat a) (nat b) = ordering (compareNat a b) := by
  rw [comparison, natOrd_eq, call_dictionary _ _ _ _ (lookup_compare _ _ _ _ rfl)]
  simp [application, primitive, predicateTruth, operationValue]

@[simp] theorem desc_comparison (a b : Nat) :
    comparison natDesc (nat a) (nat b) = ordering (compareNat b a) := by
  rw [comparison, natDesc_eq, call_dictionary _ _ _ _ (lookup_compare _ _ _ _ rfl)]
  simp [application, primitive, predicateTruth, operationValue]

@[simp] theorem bool_comparison (a b : Bool) :
    comparison boolOrd (boolean a) (boolean b) = ordering (compareNat (boolRank a) (boolRank b)) := by
  rw [comparison, boolOrd_eq, call_dictionary _ _ _ _ (lookup_compare _ _ _ _ rfl)]
  simp [application, primitive, predicateTruth, operationValue]

@[simp] theorem nat_equality (a b : Nat) :
    equality natOrd (nat a) (nat b) = boolean (decide (a = b)) := by
  rw [equality, natOrd_eq, call_dictionary _ _ _ _ (lookup_equal _ _ _ _ rfl)]
  simp [application, primitive, predicateTruth, operationValue]

@[simp] theorem desc_equality (a b : Nat) :
    equality natDesc (nat a) (nat b) = boolean (decide (a = b)) := by
  rw [equality, natDesc_eq, call_dictionary _ _ _ _ (lookup_equal _ _ _ _ rfl)]
  simp [application, primitive, predicateTruth, operationValue]

@[simp] theorem bool_equality (a b : Bool) :
    equality boolOrd (boolean a) (boolean b) = boolean (a == b) := by
  rw [equality, boolOrd_eq, call_dictionary _ _ _ _ (lookup_equal _ _ _ _ rfl)]
  simp [application, primitive, predicateTruth, operationValue]

@[simp] theorem nat_less (a b : Nat) :
    lessThan natOrd (nat a) (nat b) = boolean (decide (a < b)) := by
  rw [lessThan, natOrd_eq, call_dictionary _ _ _ _ (lookup_less _ _ _ _ rfl)]
  simp [application, primitive, predicateTruth, operationValue]

@[simp] theorem desc_less (a b : Nat) :
    lessThan natDesc (nat a) (nat b) = boolean (decide (b < a)) := by
  rw [lessThan, natDesc_eq, call_dictionary _ _ _ _ (lookup_less _ _ _ _ rfl)]
  simp [application, primitive, predicateTruth, operationValue]

@[simp] theorem bool_less (a b : Bool) :
    lessThan boolOrd (boolean a) (boolean b) = boolean (decide (boolRank a < boolRank b)) := by
  rw [lessThan, boolOrd_eq, call_dictionary _ _ _ _ (lookup_less _ _ _ _ rfl)]
  simp [application, primitive, predicateTruth, operationValue]

/-- A common proof discharges both instances via their injective Nat ranks. -/
theorem laws_of_rank {domain : Value → Prop} {dict : Value}
    (comp : ∀ a b, domain a → domain b → comparison dict a b = ordering (compareNat (rank a) (rank b)))
    (eqCorrect : ∀ a b, domain a → domain b → (equality dict a b = boolean true ↔ a = b))
    (lessRank : ∀ a b, domain a → domain b → lessThan dict a b = boolean (decide (rank a < rank b)))
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
  · intro a b ha hb; exact ⟨_, lessRank a b ha hb⟩
  · intro a b ha hb
    rw [lessRank a b ha hb, comp a b ha hb]
    simp [compareNat_lt]

theorem nat_laws : OrdLaws NatDomain natOrd := by
  apply laws_of_rank
  · intro a b ha hb
    rcases ha with ⟨n, rfl⟩; rcases hb with ⟨m, rfl⟩
    exact nat_comparison n m
  · intro a b ha hb
    rcases ha with ⟨n, rfl⟩; rcases hb with ⟨m, rfl⟩
    simp
  · intro a b ha hb
    rcases ha with ⟨n, rfl⟩; rcases hb with ⟨m, rfl⟩
    exact nat_less n m
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
  · intro a b ha hb
    rcases ha with ⟨n, rfl⟩; rcases hb with ⟨m, rfl⟩
    exact bool_less n m
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
  rw [role_operation] at role
  simp [model, Extension.withDictionaryCalls, Extension.lookupPathAs, Extension.atPath,
    Extension.lookupAs, eqDictionary, lookup, role]
  exact extension.invoke_eq _ _

theorem nat_eq_laws : EqLaws NatDomain (extension.dictionary (eqDictionary .natEqual)) := by
  intro a b ha hb
  rcases ha with ⟨n, rfl⟩; rcases hb with ⟨m, rfl⟩
  rw [eq_call _ rfl]
  simp [application, primitive, predicateTruth, operationValue]

theorem bool_eq_laws : EqLaws BoolDomain (extension.dictionary (eqDictionary .boolEqual)) := by
  intro a b ha hb
  rcases ha with ⟨n, rfl⟩; rcases hb with ⟨m, rfl⟩
  rw [eq_call _ rfl]
  cases n <;> cases m <;> simp [application, primitive, predicateTruth, operationValue]

def eqInterface (domain : Value → Prop) : Interface Symbol Value :=
  .mk [(.equal, .operation)] [] (EqLaws domain)

def weakOrdInterface (domain : Value → Prop) : Interface Symbol Value :=
  .mk [(.compare, .operation)] [(.eqModel, eqInterface domain)] (fun _ => True)

def ordInterface (domain : Value → Prop) : Interface Symbol Value :=
  .mk [(.member, .predicate), (.less, .operation)] [(.weakOrd, weakOrdInterface domain)]
    (fun dict => (∀ value, Member dict value ↔ domain value) ∧ OrdLaws domain dict)

theorem nat_implements : Implements extension natOrd (ordInterface NatDomain) := by
  simp only [ordInterface, Implements]
  refine ⟨?_, ?_, nat_member_exact, nat_laws⟩
  · intro field role member
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [natOrd_eq, dictionary, Extension.lookupAs, lookup, predicateTruth]
  · simp [natOrd_eq, dictionary, weakOrdInterface, eqInterface, Implements,
      Extension.subdictionary, Extension.lookupAs, weakDictionary, eqDictionary, lookup, predicateTruth]
    exact nat_eq_laws

theorem bool_implements : Implements extension boolOrd (ordInterface BoolDomain) := by
  simp only [ordInterface, Implements]
  refine ⟨?_, ?_, bool_member_exact, bool_laws⟩
  · intro field role member
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [boolOrd_eq, dictionary, Extension.lookupAs, lookup, predicateTruth]
  · simp [boolOrd_eq, dictionary, weakOrdInterface, eqInterface, Implements,
      Extension.subdictionary, Extension.lookupAs, weakDictionary, eqDictionary, lookup, predicateTruth]
    exact bool_eq_laws

/-- The same untyped term works with either order dictionary. -/
def compareTerm (dict a b : Term Variable Data Symbol) : Term Variable Data Symbol :=
  .dictionaryCall dict [.weakOrd] .compare [a, b]

def equalTerm (dict a b : Term Variable Data Symbol) : Term Variable Data Symbol :=
  .dictionaryCall dict [.weakOrd, .eqModel] .equal [a, b]

def lessTerm (dict a b : Term Variable Data Symbol) : Term Variable Data Symbol :=
  .dictionaryCall dict [] .less [a, b]

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

theorem eval_lessTerm [DecidableEq Variable] (environment : Semantics.Environment Variable Value)
    (dict a b : Term Variable Data Symbol) :
    model.eval environment (lessTerm dict a b) = lessThan
      (model.eval environment dict) (model.eval environment a) (model.eval environment b) := by
  simp [lessTerm, Semantics.Model.eval, lessThan]

end AnthillModKbSpec.OrderDictionaries
