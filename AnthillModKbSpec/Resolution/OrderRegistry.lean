import AnthillModKbSpec.Resolution.DictionaryRegistry
import AnthillModKbSpec.Models.OrderDictionaries

/-! # Nat and Bool order dictionaries in the registry (S13)

The registry over the order model (`OrderDictionaries`): one interface, `Ord`,
with membership symbol `ordDictionary`, three operations (`less`, `compare`
under `weakOrd`, `equal` under `weakOrd.eqModel`), and three generic laws;
three registrations, two of them for the Nat domain (`natOrd` ascending,
`natDesc` descending) and one for Bool (`boolOrd`). Nat and Bool are the order
model's constructor domains (`zero`/`succ`, `boolTrue`/`boolFalse`).

The laws tie the operations together: `less` is asymmetric, `less` is `true`
exactly where `compare` is `lt`, and `equal` is `true` exactly where `compare`
is `eq`. A dictionary whose `less` and `compare` disagree fails the second.

The order model realizes the snapshot (`realized`) and every registration's
evidence is proved (`checked`): each dictionary's member field holds exactly
on its domain, its operations resolve, the laws hold at its value, and its
primitive contracts (`less` and `equal`, total on the domain with Bool
results) hold. The generated clauses are therefore true (`kb_models`) and the
laws valid (`asymmetry_valid`, `lessCompare_valid`, `equalCompare_valid`).
`checked_dictionary` proves the evidence in any snapshot over the same
signature, naming, and interface, so it serves a grown registry too.

The laws compare results with values: `less(d, x, y) = true`, a value
equation, never `less(d, x, y)` read as a formula.

The order model is not a model of the free completion: the literal `2` and
the constructor term `succ(succ(zero))` denote the same value, and
`aliasOrd()` denotes `natOrd`'s value. S13's theorems hold in it; a
closed-world answer, which treats distinct names as distinct, does not
transfer to it. -/

namespace AnthillModKbSpec.OrderRegistry

open Semantics InductiveDomains AdmissionSignature OperationDictionaries DictionaryRegistry OrderDictionaries

abbrev T := Term String Data Symbol

/-! ## The signature -/

/-- Nat and Bool, with `isData` for all data and no registered predicates. -/
def signature : SignatureSnapshot Domain Symbol := ⟨0, ⟨family, membershipSymbol, .isData, fun _ => .isPred, []⟩⟩

theorem contains_iff (domain : Domain) (value : Value) :
    (Range.data [domain]).Contains signature model value ↔ domainOf domain value := by
  constructor
  · rintro ⟨tree, ⟨other, selected, member⟩, rfl⟩
    simp only [List.mem_singleton] at selected
    subst selected
    exact member_denote member
  · intro inside
    obtain ⟨tree, member, same⟩ := (realizes domain value).mp (by
      cases domain
      · exact (holds_isNat value).mpr inside
      · exact (holds_isBool value).mpr inside)
    exact ⟨tree, ⟨domain, List.mem_singleton_self _, member⟩, same⟩

theorem signature_realized : AdmissionSignature.Realizes signature model := by
  refine ⟨realizes, fun value => ?_, fun arity value => ?_⟩
  · change holds (application .isData [value]) ↔ _
    rw [application_primitive (by decide)]
    change NatDomain value ∨ BoolDomain value ↔ _
    constructor
    · rintro (inside | inside)
      · obtain ⟨tree, ⟨domain, selected, member⟩, same⟩ := (contains_iff .nat value).mpr inside
        simp only [List.mem_singleton] at selected
        subst selected
        exact ⟨tree, ⟨.nat, by simp [signature, family], member⟩, same⟩
      · obtain ⟨tree, ⟨domain, selected, member⟩, same⟩ := (contains_iff .bool value).mpr inside
        simp only [List.mem_singleton] at selected
        subst selected
        exact ⟨tree, ⟨.bool, by simp [signature, family], member⟩, same⟩
    · rintro ⟨tree, ⟨domain, _, member⟩, rfl⟩
      cases domain
      · exact Or.inl (member_denote member)
      · exact Or.inr (member_denote member)
  · change holds (application .isPred [value]) ↔ _
    rw [application_primitive (by decide)]
    constructor
    · exact False.elim
    · rintro ⟨_, declared, _⟩
      simp [SignatureSnapshot.Registered, signature] at declared

/-! ## The interface, its laws, and the registrations -/

def trueB : T := .app .boolTrue []
def falseB : T := .app .boolFalse []
def ltT : T := .lit (.ordering .lt)
def eqT : T := .lit (.ordering .eq)
def domainMember (dict value : T) : T := .app .domainMember [dict, value]
def ordGuard (dict : T) : T := .app .ordDictionary [dict]

/-- `∀x. DomainMember(d,x) → ∀y. DomainMember(d,y) → body`. -/
def forMembers (body : T) : T :=
  .forallVar "x" (.imp (domainMember (.var "d") (.var "x"))
    (.forallVar "y" (.imp (domainMember (.var "d") (.var "y")) body)))

/-- Each formula implies the other. -/
def both (left right : T) : T := .conj (.imp left right) (.imp right left)

/-- `less(d,x,y) = true → less(d,y,x) = false`. -/
def asymmetryBody : T :=
  forMembers (.imp (.equal (lessTerm (.var "d") (.var "x") (.var "y")) trueB)
    (.equal (lessTerm (.var "d") (.var "y") (.var "x")) falseB))

/-- `less(d,x,y) = true` exactly when `compare(d,x,y) = lt`. -/
def lessCompareBody : T :=
  forMembers (both (.equal (lessTerm (.var "d") (.var "x") (.var "y")) trueB)
    (.equal (compareTerm (.var "d") (.var "x") (.var "y")) ltT))

/-- `equal(d,x,y) = true` exactly when `compare(d,x,y) = eq`, with `equal`
under `weakOrd.eqModel` and `compare` under `weakOrd`. -/
def equalCompareBody : T :=
  forMembers (both (.equal (equalTerm (.var "d") (.var "x") (.var "y")) trueB)
    (.equal (compareTerm (.var "d") (.var "x") (.var "y")) eqT))

def asymmetry : Law String Data Symbol := ⟨.asymmetric, "d", asymmetryBody⟩
def lessCompare : Law String Data Symbol := ⟨.lessCompare, "d", lessCompareBody⟩
def equalCompare : Law String Data Symbol := ⟨.equalCompare, "d", equalCompareBody⟩

def lessOperation : Operation Symbol := ⟨[], .less, [2]⟩
def compareOperation : Operation Symbol := ⟨[.weakOrd], .compare, [2]⟩
def equalOperation : Operation Symbol := ⟨[.weakOrd, .eqModel], .equal, [2]⟩

def ordDeclaration : Interface String Data Symbol :=
  ⟨.ordDictionary, [lessOperation, compareOperation, equalOperation], [asymmetry, lessCompare, equalCompare]⟩

/-- `less` and `equal` are total on the domain with Bool results; `compare`,
whose results are orderings outside the declared domains, has no contract. -/
def primitives (domain : Domain) : List (Primitive Domain Symbol) :=
  [⟨[], .less, [domain, domain], .bool⟩, ⟨[.weakOrd, .eqModel], .equal, [domain, domain], .bool⟩]

def natRegistration : Registration Domain Symbol := ⟨.natOrd, 1, .ordDictionary, .nat, primitives .nat⟩
def descRegistration : Registration Domain Symbol := ⟨.natDesc, 1, .ordDictionary, .nat, primitives .nat⟩
def boolRegistration : Registration Domain Symbol := ⟨.boolOrd, 1, .ordDictionary, .bool, primitives .bool⟩

def registry : Registry Domain String Data Symbol :=
  ⟨⟨.member, .domainMember⟩, [ordDeclaration], [natRegistration, descRegistration, boolRegistration]⟩

def snapshot : DictionaryRegistry.Snapshot Domain String Data Symbol := ⟨0, signature, registry⟩

theorem wellFormed : snapshot.WellFormed := by decide

/-! ## The interpretation -/

def interp : Interpretation Data Symbol Value .hoApply := ⟨baseModel, extension, .invalid⟩

@[simp] theorem interp_model : interp.model = model := rfl

theorem interp_member (dict value : Value) : interp.Member .member dict value ↔ Member dict value := Iff.rfl

/-- A constant evaluates to the value its name denotes. -/
theorem eval_constant (environment : Environment String Value) (name : Symbol) :
    model.eval environment (.app name [] : T) = interp.value name := by
  simp [Model.eval, Interpretation.value]

theorem values : interp.value .natOrd = natOrd ∧ interp.value .natDesc = natDesc ∧
    interp.value .boolOrd = boolOrd ∧ interp.value .aliasOrd = natOrd := by
  simp [Interpretation.value, model, Extension.withDictionaryCalls, baseModel, application, primitive,
    predicateTruth, operationValue]

@[simp] theorem value_natOrd : interp.value .natOrd = natOrd := values.1
@[simp] theorem value_natDesc : interp.value .natDesc = natDesc := values.2.1
@[simp] theorem value_boolOrd : interp.value .boolOrd = boolOrd := values.2.2.1
@[simp] theorem value_aliasOrd : interp.value .aliasOrd = natOrd := values.2.2.2

theorem realized : snapshot.Realizes interp := by
  refine ⟨signature_realized, ?_, ?_⟩
  · intro interface declared value
    simp only [snapshot, registry, List.mem_singleton] at declared
    subst declared
    change holds (application .ordDictionary [value]) ↔ _
    rw [application_primitive (by decide)]
    change value = natOrd ∨ value = natDesc ∨ value = boolOrd ↔ _
    simp [DictionaryRegistry.Snapshot.InterfaceMember, snapshot, registry, ordDeclaration, natRegistration,
      descRegistration, boolRegistration, eq_comm]
  · intro dict value
    exact domainMember_exact dict value

/-! ## Reading the laws in the model -/

/-- The environment of a law body: the dictionary and two members. -/
def scope (environment : Environment String Value) (dict a b : Value) : Environment String Value :=
  update (update (update environment "d" dict) "x" a) "y" b

@[simp] theorem eval_d (environment : Environment String Value) (dict a b : Value) :
    model.eval (scope environment dict a b) (.var "d" : T) = dict := by
  simp [Model.eval, scope, update, show ("d" : String) ≠ "x" from by decide,
    show ("d" : String) ≠ "y" from by decide]

@[simp] theorem eval_x (environment : Environment String Value) (dict a b : Value) :
    model.eval (scope environment dict a b) (.var "x" : T) = a := by
  simp [Model.eval, scope, update, show ("x" : String) ≠ "y" from by decide]

@[simp] theorem eval_y (environment : Environment String Value) (dict a b : Value) :
    model.eval (scope environment dict a b) (.var "y" : T) = b := by
  simp [Model.eval, scope, update]

@[simp] theorem eval_trueB (environment : Environment String Value) : model.eval environment trueB = boolean true := by
  simp [trueB, Model.eval, model, Extension.withDictionaryCalls, baseModel, application, primitive,
    predicateTruth, operationValue]

@[simp] theorem eval_falseB (environment : Environment String Value) : model.eval environment falseB = boolean false := by
  simp [falseB, Model.eval, model, Extension.withDictionaryCalls, baseModel, application, primitive,
    predicateTruth, operationValue]

@[simp] theorem eval_ltT (environment : Environment String Value) : model.eval environment ltT = ordering .lt := by
  simp [ltT, Model.eval, model, Extension.withDictionaryCalls, baseModel]

@[simp] theorem eval_eqT (environment : Environment String Value) : model.eval environment eqT = ordering .eq := by
  simp [eqT, Model.eval, model, Extension.withDictionaryCalls, baseModel]

theorem satisfies_imp (environment : Environment String Value) (premise conclusion : T) :
    model.Satisfies environment (.imp premise conclusion) ↔
      (model.Satisfies environment premise → model.Satisfies environment conclusion) := by
  simp only [Model.Satisfies, Model.eval, model.holds_implication]

theorem satisfies_both (environment : Environment String Value) (left right : T) :
    model.Satisfies environment (both left right) ↔
      (model.Satisfies environment left ↔ model.Satisfies environment right) := by
  simp only [both, Model.Satisfies, Model.eval, model.holds_conjunction, model.holds_implication]
  exact ⟨fun ⟨forward, backward⟩ => ⟨forward, backward⟩, fun same => ⟨same.mp, same.mpr⟩⟩

theorem satisfies_member (environment : Environment String Value) (name : String) :
    model.Satisfies environment (domainMember (.var "d") (.var name)) ↔ Member (environment "d") (environment name) := by
  simp only [domainMember, Model.Satisfies, Model.eval, List.map_cons, List.map_nil]
  exact domainMember_exact _ _

/-- A law body over two members of the dictionary. -/
theorem satisfies_forMembers (environment : Environment String Value) (dict : Value) (body : T) :
    model.Satisfies (update environment "d" dict) (forMembers body) ↔
      ∀ a, Member dict a → ∀ b, Member dict b → model.Satisfies (scope environment dict a b) body := by
  have dx : ∀ a, update (update environment "d" dict) "x" a "d" = dict := fun a => by
    simp [update, show ("d" : String) ≠ "x" from by decide]
  have xx : ∀ a, update (update environment "d" dict) "x" a "x" = a := fun a => by simp [update]
  have dy : ∀ a b, scope environment dict a b "d" = dict := fun a b => by
    simp [scope, update, show ("d" : String) ≠ "x" from by decide, show ("d" : String) ≠ "y" from by decide]
  have yy : ∀ a b, scope environment dict a b "y" = b := fun a b => by simp [scope, update]
  simp only [forMembers, Model.Satisfies, Model.eval, model.holds_universal, model.holds_implication]
  change (∀ a, model.Satisfies _ (domainMember (.var "d") (.var "x")) →
      ∀ b, model.Satisfies (scope environment dict a b) (domainMember (.var "d") (.var "y")) →
        model.Satisfies (scope environment dict a b) body) ↔ _
  simp only [satisfies_member, dx, xx, dy, yy]
  exact Iff.rfl

theorem satisfies_asymmetry (environment : Environment String Value) (dict : Value) :
    model.Satisfies (update environment "d" dict) asymmetryBody ↔
      ∀ a, Member dict a → ∀ b, Member dict b →
        lessThan dict a b = boolean true → lessThan dict b a = boolean false := by
  rw [asymmetryBody, satisfies_forMembers]
  simp only [satisfies_imp, Model.satisfies_equal, eval_lessTerm, eval_d, eval_x, eval_y, eval_trueB, eval_falseB]

theorem satisfies_lessCompare (environment : Environment String Value) (dict : Value) :
    model.Satisfies (update environment "d" dict) lessCompareBody ↔
      ∀ a, Member dict a → ∀ b, Member dict b →
        (lessThan dict a b = boolean true ↔ comparison dict a b = ordering .lt) := by
  rw [lessCompareBody, satisfies_forMembers]
  simp only [satisfies_both, Model.satisfies_equal, eval_lessTerm, eval_compareTerm, eval_d, eval_x, eval_y,
    eval_trueB, eval_ltT]

theorem satisfies_equalCompare (environment : Environment String Value) (dict : Value) :
    model.Satisfies (update environment "d" dict) equalCompareBody ↔
      ∀ a, Member dict a → ∀ b, Member dict b →
        (OrderDictionaries.equality dict a b = boolean true ↔ comparison dict a b = ordering .eq) := by
  rw [equalCompareBody, satisfies_forMembers]
  simp only [satisfies_both, Model.satisfies_equal, eval_equalTerm, eval_compareTerm, eval_d, eval_x, eval_y,
    eval_trueB, eval_eqT]

/-! ## The evidence of each registration -/

/-- A binary primitive contract over one domain, from totality on its members. -/
theorem binary_holds {dict : Value} {primitive : Primitive Domain Symbol} {domain : Domain}
    (arguments : primitive.arguments = [domain, domain])
    (total : ∀ a b, domainOf domain a → domainOf domain b →
      domainOf primitive.result (model.dictionaryCall dict primitive.path primitive.field [a, b])) :
    primitive.Holds interp signature dict := by
  intro args length inside
  rw [arguments] at length inside
  match args, length with
  | [a, b], _ =>
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at inside
    change (Range.data [primitive.result]).Contains signature model _
    rw [contains_iff]
    exact total a b ((contains_iff _ _).mp inside.1) ((contains_iff _ _).mp inside.2)

/-- The evidence for a dictionary built by `dictionary`, in any snapshot over
this signature and naming that declares its interface as `Ord`. -/
theorem checked_dictionary {current : DictionaryRegistry.Snapshot Domain String Data Symbol}
    (signatureOf : current.signature = signature) (namingOf : current.registry.naming = registry.naming)
    {registration : Registration Domain Symbol}
    (located : current.registry.interface? registration.interface = some ordDeclaration)
    {membership comparison equality order : Symbol}
    (named : interp.value registration.name = extension.dictionary (dictionary membership comparison equality order))
    (primitivesOf : registration.primitives = primitives registration.domain)
    (role : extension.roleOf membership = .predicate) (comparisonRole : extension.roleOf comparison = .operation)
    (equalRole : extension.roleOf equality = .operation) (orderRole : extension.roleOf order = .operation)
    (exact : ∀ value, holds (application membership [value]) ↔ domainOf registration.domain value)
    (asymmetric : ∀ a b, domainOf registration.domain a → domainOf registration.domain b →
      application order [a, b] = boolean true → application order [b, a] = boolean false)
    (lessCompares : ∀ a b, domainOf registration.domain a → domainOf registration.domain b →
      (application order [a, b] = boolean true ↔ application comparison [a, b] = ordering .lt))
    (equalCompares : ∀ a b, domainOf registration.domain a → domainOf registration.domain b →
      (application equality [a, b] = boolean true ↔ application comparison [a, b] = ordering .eq))
    (lessTotal : ∀ a b, domainOf registration.domain a → domainOf registration.domain b →
      BoolDomain (application order [a, b]))
    (equalTotal : ∀ a b, domainOf registration.domain a → domainOf registration.domain b →
      BoolDomain (application equality [a, b])) :
    registration.Checked current interp := by
  have members : ∀ value, Member (interp.value registration.name) value ↔ domainOf registration.domain value := by
    intro value
    rw [named, member_dictionary _ _ _ _ role, exact]
  have lessCall : ∀ a b, lessThan (interp.value registration.name) a b = application order [a, b] := by
    intro a b
    rw [lessThan, named, call_dictionary _ _ _ _ (lookup_less _ _ _ _ orderRole)]
  have compareCall : ∀ a b, OrderDictionaries.comparison (interp.value registration.name) a b =
      application comparison [a, b] := by
    intro a b
    rw [OrderDictionaries.comparison, named, call_dictionary _ _ _ _ (lookup_compare _ _ _ _ comparisonRole)]
  have equalCall : ∀ a b, OrderDictionaries.equality (interp.value registration.name) a b =
      application equality [a, b] := by
    intro a b
    rw [OrderDictionaries.equality, named, call_dictionary _ _ _ _ (lookup_equal _ _ _ _ equalRole)]
  refine ⟨fun value => ?_, ?_, ?_, ?_⟩
  · rw [namingOf, signatureOf]
    change interp.Member .member _ value ↔ (Range.data [registration.domain]).Contains signature model value
    rw [interp_member, members, contains_iff]
  · intro declaration found operation member
    rw [located] at found
    cases found
    simp only [ordDeclaration, List.mem_cons, List.not_mem_nil, or_false] at member
    rw [named]
    rcases member with rfl | rfl | rfl
    · exact ⟨_, lookup_less _ _ _ _ orderRole⟩
    · exact ⟨_, lookup_compare _ _ _ _ comparisonRole⟩
    · exact ⟨_, lookup_equal _ _ _ _ equalRole⟩
  · intro declaration found law stated environment
    rw [located] at found
    cases found
    simp only [ordDeclaration, List.mem_cons, List.not_mem_nil, or_false] at stated
    rw [interp_model]
    rcases stated with rfl | rfl | rfl
    · rw [show asymmetry.dictionary = "d" from rfl, show asymmetry.body = asymmetryBody from rfl,
        satisfies_asymmetry]
      intro a inA b inB
      rw [lessCall, lessCall]
      exact asymmetric a b ((members a).mp inA) ((members b).mp inB)
    · rw [show lessCompare.dictionary = "d" from rfl, show lessCompare.body = lessCompareBody from rfl,
        satisfies_lessCompare]
      intro a inA b inB
      rw [lessCall, compareCall]
      exact lessCompares a b ((members a).mp inA) ((members b).mp inB)
    · rw [show equalCompare.dictionary = "d" from rfl, show equalCompare.body = equalCompareBody from rfl,
        satisfies_equalCompare]
      intro a inA b inB
      rw [equalCall, compareCall]
      exact equalCompares a b ((members a).mp inA) ((members b).mp inB)
  · intro primitive member
    rw [signatureOf]
    rw [primitivesOf] at member
    simp only [primitives, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · apply binary_holds rfl
      intro a b inA inB
      change BoolDomain (lessThan _ a b)
      rw [lessCall]
      exact lessTotal a b inA inB
    · apply binary_holds rfl
      intro a b inA inB
      change BoolDomain (OrderDictionaries.equality _ a b)
      rw [equalCall]
      exact equalTotal a b inA inB

/-- The operations of the three dictionaries, at members of their domains. -/
theorem nat_operations : ∀ a b, NatDomain a → NatDomain b →
    (application .natLess [a, b] = boolean true → application .natLess [b, a] = boolean false) ∧
    (application .natLess [a, b] = boolean true ↔ application .natCompare [a, b] = ordering .lt) ∧
    (application .natEqual [a, b] = boolean true ↔ application .natCompare [a, b] = ordering .eq) ∧
    BoolDomain (application .natLess [a, b]) ∧ BoolDomain (application .natEqual [a, b]) := by
  rintro a b ⟨m, rfl⟩ ⟨n, rfl⟩
  simp only [application_primitive (show Symbol.natLess ≠ .hoApply by decide),
    application_primitive (show Symbol.natEqual ≠ .hoApply by decide),
    application_primitive (show Symbol.natCompare ≠ .hoApply by decide)]
  simp [primitive, predicateTruth, operationValue, BoolDomain, compareNat_lt, compareNat_eq]
  omega

theorem desc_operations : ∀ a b, NatDomain a → NatDomain b →
    (application .natLessDesc [a, b] = boolean true → application .natLessDesc [b, a] = boolean false) ∧
    (application .natLessDesc [a, b] = boolean true ↔ application .natCompareDesc [a, b] = ordering .lt) ∧
    (application .natEqual [a, b] = boolean true ↔ application .natCompareDesc [a, b] = ordering .eq) ∧
    BoolDomain (application .natLessDesc [a, b]) ∧ BoolDomain (application .natEqual [a, b]) := by
  rintro a b ⟨m, rfl⟩ ⟨n, rfl⟩
  simp only [application_primitive (show Symbol.natLessDesc ≠ .hoApply by decide),
    application_primitive (show Symbol.natEqual ≠ .hoApply by decide),
    application_primitive (show Symbol.natCompareDesc ≠ .hoApply by decide)]
  simp [primitive, predicateTruth, operationValue, BoolDomain, compareNat_lt, compareNat_eq]
  omega

theorem bool_operations : ∀ a b, BoolDomain a → BoolDomain b →
    (application .boolLess [a, b] = boolean true → application .boolLess [b, a] = boolean false) ∧
    (application .boolLess [a, b] = boolean true ↔ application .boolCompare [a, b] = ordering .lt) ∧
    (application .boolEqual [a, b] = boolean true ↔ application .boolCompare [a, b] = ordering .eq) ∧
    BoolDomain (application .boolLess [a, b]) ∧ BoolDomain (application .boolEqual [a, b]) := by
  rintro a b ⟨m, rfl⟩ ⟨n, rfl⟩
  simp only [application_primitive (show Symbol.boolLess ≠ .hoApply by decide),
    application_primitive (show Symbol.boolEqual ≠ .hoApply by decide),
    application_primitive (show Symbol.boolCompare ≠ .hoApply by decide)]
  cases m <;> cases n <;> simp [primitive, predicateTruth, operationValue, BoolDomain, compareNat, boolRank]

theorem located_ord : registry.interface? .ordDictionary = some ordDeclaration := rfl

theorem nat_checked : natRegistration.Checked snapshot interp :=
  checked_dictionary rfl rfl located_ord (membership := .isNat) (comparison := .natCompare) (equality := .natEqual)
    (order := .natLess) value_natOrd rfl rfl rfl rfl rfl holds_isNat
    (fun a b x y => (nat_operations a b x y).1) (fun a b x y => (nat_operations a b x y).2.1)
    (fun a b x y => (nat_operations a b x y).2.2.1) (fun a b x y => (nat_operations a b x y).2.2.2.1)
    (fun a b x y => (nat_operations a b x y).2.2.2.2)

theorem desc_checked : descRegistration.Checked snapshot interp :=
  checked_dictionary rfl rfl located_ord (membership := .isNat) (comparison := .natCompareDesc)
    (equality := .natEqual) (order := .natLessDesc) value_natDesc rfl rfl rfl rfl rfl holds_isNat
    (fun a b x y => (desc_operations a b x y).1) (fun a b x y => (desc_operations a b x y).2.1)
    (fun a b x y => (desc_operations a b x y).2.2.1) (fun a b x y => (desc_operations a b x y).2.2.2.1)
    (fun a b x y => (desc_operations a b x y).2.2.2.2)

theorem bool_checked : boolRegistration.Checked snapshot interp :=
  checked_dictionary rfl rfl located_ord (membership := .isBool) (comparison := .boolCompare)
    (equality := .boolEqual) (order := .boolLess) value_boolOrd rfl rfl rfl rfl rfl holds_isBool
    (fun a b x y => (bool_operations a b x y).1) (fun a b x y => (bool_operations a b x y).2.1)
    (fun a b x y => (bool_operations a b x y).2.2.1) (fun a b x y => (bool_operations a b x y).2.2.2.1)
    (fun a b x y => (bool_operations a b x y).2.2.2.2)

theorem checked : snapshot.Checked interp := by
  intro registration registered
  simp only [snapshot, registry, List.mem_cons, List.not_mem_nil, or_false] at registered
  rcases registered with rfl | rfl | rfl
  · exact nat_checked
  · exact desc_checked
  · exact bool_checked

/-! ## What the evidence gives -/

/-- The variable of generated clauses. One name suffices: no constructor has
two fields. -/
def names : Nat → String := fun _ => "n"

theorem distinct : DistinctNames sigma names := by
  rintro rule (rfl | rfl | rfl | rfl) i j _
  all_goals
    apply Fin.ext
    have bound := i.isLt
    have other := j.isLt
    simp only [zeroRule, succRule, trueRule, falseRule, List.length_nil, List.length_cons] at bound other
    omega

theorem kb_models : model.Models (snapshot.kb (Literal := Data) names) :=
  models_kb realized checked wellFormed names

theorem asymmetry_valid (environment : Environment String Value) :
    model.Satisfies environment (asymmetry.formula ordDeclaration) :=
  law_valid realized checked wellFormed (by simp [snapshot, registry]) (by simp [ordDeclaration]) environment

theorem lessCompare_valid (environment : Environment String Value) :
    model.Satisfies environment (lessCompare.formula ordDeclaration) :=
  law_valid realized checked wellFormed (by simp [snapshot, registry]) (by simp [ordDeclaration]) environment

theorem equalCompare_valid (environment : Environment String Value) :
    model.Satisfies environment (equalCompare.formula ordDeclaration) :=
  law_valid realized checked wellFormed (by simp [snapshot, registry]) (by simp [ordDeclaration]) environment

end AnthillModKbSpec.OrderRegistry
