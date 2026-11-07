import AnthillModKbSpec

/-! Regressions for the S13 dictionary registry over the Nat and Bool order
dictionaries (`OrderRegistry`). -/

open AnthillModKbSpec AnthillModKbSpec.Semantics AnthillModKbSpec.InductiveDomains
open AnthillModKbSpec.OperationDictionaries AnthillModKbSpec.DictionaryRegistry
open AnthillModKbSpec.OrderDictionaries AnthillModKbSpec.OrderRegistry

namespace DictionaryRegistryTests

def natOrdT : T := .app .natOrd []
def natDescT : T := .app .natDesc []
def boolOrdT : T := .app .boolOrd []
def aliasT : T := .app .aliasOrd []
def two : T := (natTree 2).toTerm
def three : T := (natTree 3).toTerm

def kb : LogicalKb String Data Symbol := snapshot.kb names

def environment : Environment String Value := fun _ => .invalid

theorem eval_natTree (n : Nat) (environment : Environment String Value) :
    model.eval environment ((natTree n).toTerm : T) = nat n := by
  rw [Tree.eval_toTerm, natTree_denote]

theorem eval_natOrdT : model.eval environment natOrdT = natOrd := (eval_constant _ _).trans value_natOrd
theorem eval_aliasT : model.eval environment aliasT = natOrd := (eval_constant _ _).trans value_aliasOrd
theorem eval_two : model.eval environment two = nat 2 := eval_natTree 2 environment
theorem eval_three : model.eval environment three = nat 3 := eval_natTree 3 environment

/-! ## The access check -/

-- Declared operations, at the root and along a nested path.
example : registry.access? .value natOrdT [] .less 2 = .declared natRegistration lessOperation := by decide
example : registry.access? .value natDescT [.weakOrd] .compare 2 = .declared descRegistration compareOperation := by
  decide
example : registry.access? .value boolOrdT [.weakOrd, .eqModel] .equal 2 =
    .declared boolRegistration equalOperation := by decide

-- Invalid accesses: wrong path, the member predicate called as an operation,
-- an unsupported argument count.
example : registry.access? .value natOrdT [] .compare 2 = .invalid .natOrd .operation := by decide
example : registry.access? .value natOrdT [] .member 1 = .invalid .natOrd .operation := by decide
example : registry.access? .value natOrdT [] .less 3 = .invalid .natOrd (.arity [2]) := by decide

-- An unknown name, an unbound dictionary variable, dictionaries that are no
-- name (a literal, a nested call), and a call standing as a formula.
example : registry.access? .value aliasT [] .less 2 = .unknown .aliasOrd := by decide
example : registry.access? .value (.var "d" : T) [] .less 2 = .unresolved := by decide
example : registry.access? .value (.lit (.nat 3) : T) [] .less 2 = .unnamed := by decide
example : registry.access? .value (lessTerm natOrdT two three) [] .less 2 = .unnamed := by decide
example : registry.access? .formula natOrdT [] .less 2 = .formula := by decide

-- What admission makes of them: only the declared access runs; each other one
-- is blocked with its own reason, a binding for the variable. None is a No.
example : (registry.access? .value natOrdT [] .less 2).verdict (Variable := String) (Literal := Data) = .runs := by
  rw [show registry.access? .value natOrdT [] .less 2 = .declared natRegistration lessOperation by decide]
  rfl
example : (Access.unknown .aliasOrd : Access Domain Symbol).verdict (Variable := String) (Literal := Data) =
    .blocked (.construct (.dictionary .unknown)) := rfl
example : (Access.unresolved : Access Domain Symbol).verdict (Variable := String) (Literal := Data) =
    .blocked .mode := rfl
example : (Access.unnamed : Access Domain Symbol).verdict (Variable := String) (Literal := Data) =
    .blocked (.construct (.dictionary .unnamed)) := rfl
example : (Access.invalid .natOrd (.arity [2]) : Access Domain Symbol).verdict (Variable := String) (Literal := Data) =
    .blocked (.construct (.dictionary .arity)) := rfl
example : (Access.formula : Access Domain Symbol).verdict (Variable := String) (Literal := Data) =
    .blocked (.construct (.dictionary .formula)) := rfl

-- A registration naming an undeclared interface is an inconsistent registry,
-- an invalid input; a well-formed registry has none.
def undeclared : Registry Domain String Data Symbol :=
  { registry with dictionaries := [{ natRegistration with interface := .equal }] }

example : ¬ undeclared.WellFormed := by decide
example : undeclared.access? .value natOrdT [] .less 2 = .inconsistent .natOrd := by decide
example : (Access.inconsistent .natOrd : Access Domain Symbol).verdict (Variable := String) (Literal := Data) =
    .inconsistent := rfl
example (dictionary : T) (path : List Symbol) (field : Symbol) (arity : Nat) (name : Symbol) :
    registry.access? .value dictionary path field arity ≠ .inconsistent name :=
  access?_consistent wellFormed.1 .value dictionary path field arity name

-- A declared access evaluates as direct application of the stored operation.
example : model.eval environment (lessTerm natOrdT two three) = application .natLess [nat 2, nat 3] := by
  obtain ⟨entry, found, evaluates⟩ := access_eval (args := [two, three]) checked
    (show registry.access? .value natOrdT [] .less [two, three].length = .declared natRegistration lessOperation by
      decide)
  have evaluated := evaluates environment
  simp only [interp_model] at evaluated
  rw [show lessTerm natOrdT two three = .dictionaryCall natOrdT [] .less [two, three] from rfl, evaluated]
  have expected : interp.extension.lookupPathAs (interp.value natRegistration.name) [] .less .operation =
      some ⟨.operation, .natLess, []⟩ := by
    rw [show interp.value natRegistration.name = natOrd from value_natOrd, natOrd_eq]
    exact lookup_less _ _ _ _ rfl
  rw [expected] at found
  cases found
  simp only [List.nil_append, List.map_cons, List.map_nil, eval_two, eval_three]
  rfl

/-! ## Consistency -/

example : snapshot.WellFormed := wellFormed

-- Duplicate names are an inconsistent registry, not a missing capability.
example : ¬ ({ registry with dictionaries := [natRegistration, natRegistration] } :
    Registry Domain String Data Symbol).WellFormed := by decide

-- An operation at the member field, where a dictionary holds its domain
-- predicate, could never resolve as an operation.
example : ¬ ({ registry with interfaces := [{ ordDeclaration with operations := [⟨[], .member, [1]⟩] }] } :
    Registry Domain String Data Symbol).WellFormed := by decide

-- An interface symbol that is the signature's D_all would contradict its realization.
def clashing : Registry Domain String Data Symbol :=
  ⟨registry.naming, [{ ordDeclaration with symbol := .isData }], []⟩

example : clashing.WellFormed := by decide
example : ¬ (⟨0, signature, clashing⟩ : DictionaryRegistry.Snapshot Domain String Data Symbol).WellFormed := by
  decide

/-! ## Generated clauses and guards -/

-- The interface fact of each registered dictionary, by lookup on its name.
example : Derives .hoApply kb [] (ordGuard natOrdT) :=
  interface_derives (snapshot := snapshot) (fun _ member => member) (registration := natRegistration) (by decide)

-- Two dictionaries for one domain: both derive DomainMember at the same data.
example : Derives .hoApply kb [] (OrderRegistry.domainMember natOrdT two) :=
  domainMember_derives (snapshot := snapshot) distinct (fun _ member => member)
    (registration := natRegistration) (by decide) (natTree_member 2)

example : Derives .hoApply kb [] (OrderRegistry.domainMember natDescT two) :=
  domainMember_derives (snapshot := snapshot) distinct (fun _ member => member)
    (registration := descRegistration) (by decide) (natTree_member 2)

example : Derives .hoApply kb [] (OrderRegistry.domainMember boolOrdT (boolTree true).toTerm) :=
  domainMember_derives (snapshot := snapshot) distinct (fun _ member => member)
    (registration := boolRegistration) (by decide) (boolTree_member true)

-- An unmet domain guard is not derivable: the clauses are true in the order
-- model, where Bool's `true` is no member of natOrd.
example : ¬ Derives .hoApply kb [] (OrderRegistry.domainMember natOrdT (boolTree true).toTerm) := by
  intro proof
  have truth := model.positive_sound kb_models proof environment (by intro _ member; cases member)
  simp only [OrderRegistry.domainMember, Model.Satisfies, Model.eval, List.map_cons, List.map_nil] at truth
  change holds (application .domainMember [_, _]) at truth
  rw [domainMember_exact, eval_natOrdT, Tree.eval_toTerm, boolTree_denote, nat_member_exact] at truth
  obtain ⟨n, impossible⟩ := truth
  cases impossible

-- The domain connection is a proof: a registration claiming Nat for the Bool
-- dictionary has no evidence.
example : ¬ (⟨.boolOrd, 1, .ordDictionary, .nat, []⟩ : Registration Domain Symbol).Checked snapshot interp := by
  intro checked
  have member := (checked.domain (nat 0)).mpr ((contains_iff .nat _).mpr ⟨0, rfl⟩)
  rw [show interp.value Symbol.boolOrd = boolOrd from value_boolOrd] at member
  obtain ⟨b, impossible⟩ := (bool_member_exact _).mp member
  cases impossible

/-! ## Laws -/

-- The generic laws hold in the realizing model.
example : model.Satisfies environment (asymmetry.formula ordDeclaration) := asymmetry_valid environment
example : model.Satisfies environment (lessCompare.formula ordDeclaration) := lessCompare_valid environment
example : model.Satisfies environment (equalCompare.formula ordDeclaration) := equalCompare_valid environment

-- One law, two Nat dictionaries ordering the same data in opposite directions.
example : lessThan natOrd (nat 2) (nat 3) = boolean true ∧ lessThan natOrd (nat 3) (nat 2) = boolean false := by
  simp
example : lessThan natDesc (nat 3) (nat 2) = boolean true ∧ lessThan natDesc (nat 2) (nat 3) = boolean false := by
  simp

-- A law is evidence, not a table entry: a dictionary whose `less` is Nat
-- equality is not asymmetric, so a registration of it could not be checked.
def equalLess : Value := extension.dictionary (dictionary .isNat .natCompare .natEqual .natEqual)

example : ¬ model.Satisfies (update environment "d" equalLess) asymmetryBody := by
  rw [satisfies_asymmetry]
  intro asymmetric
  have members : Member equalLess (nat 0) := by
    rw [equalLess, member_dictionary _ _ _ _ rfl, holds_isNat]; exact ⟨0, rfl⟩
  have result := asymmetric (nat 0) members (nat 0) members
  rw [lessThan, equalLess, call_dictionary _ _ _ _ (lookup_less _ _ _ _ rfl)] at result
  simp [application, primitive, predicateTruth, operationValue] at result

-- `less` ascending with `compare` descending: asymmetric, yet `less` and
-- `compare` disagree, so the linking law rejects it.
def mixed : Value := extension.dictionary (dictionary .isNat .natCompareDesc .natEqual .natLess)

example : ¬ model.Satisfies (update environment "d" mixed) lessCompareBody := by
  rw [satisfies_lessCompare]
  intro linked
  have members : ∀ n, Member mixed (nat n) := by
    intro n; rw [mixed, member_dictionary _ _ _ _ rfl, holds_isNat]; exact ⟨n, rfl⟩
  have result := (linked (nat 2) (members 2) (nat 3) (members 3)).mp
  rw [lessThan, mixed, call_dictionary _ _ _ _ (lookup_less _ _ _ _ rfl), OrderDictionaries.comparison,
    call_dictionary _ _ _ _ (lookup_compare _ _ _ _ rfl)] at result
  simp [application, primitive, predicateTruth, operationValue, compareNat] at result

-- Primitive contracts: `less` is total on Nat with Bool results.
example (m n : Nat) : BoolDomain (lessThan natOrd (nat m) (nat n)) := by
  have contract := nat_checked.primitives ⟨[], .less, [.nat, .nat], .bool⟩
    (by simp [natRegistration, primitives]) [nat m, nat n] rfl (by
      intro pair member
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact (contains_iff .nat _).mpr ⟨m, rfl⟩
      · exact (contains_iff .nat _).mpr ⟨n, rfl⟩)
  rw [show interp.value natRegistration.name = natOrd from value_natOrd] at contract
  exact (contains_iff .bool _).mp contract

/-! ## Booleans are values, not truth -/

-- `less(natOrd, 2, 3)` returns the Bool value true. As a formula it does not
-- hold; the equation with the constant `true` does.
example : ¬ model.Satisfies environment (lessTerm natOrdT two three) := by
  simp only [Model.Satisfies, eval_lessTerm, eval_natOrdT, eval_two, eval_three, nat_less]
  exact id

example : model.Satisfies environment (.equal (lessTerm natOrdT two three) trueB) := by
  simp [Model.satisfies_equal, eval_lessTerm, eval_natOrdT, eval_two, eval_three]

-- The constant `true` is data: as a formula it does not hold.
example : ¬ model.Satisfies environment trueB := by
  simp only [Model.Satisfies, eval_trueB]
  exact id

-- A `false` result is a true equation, not falsity.
example : model.Satisfies environment (.equal (lessTerm natOrdT three two) falseB) := by
  simp [Model.satisfies_equal, eval_lessTerm, eval_natOrdT, eval_two, eval_three]

/-! ## Unknown dictionaries in the realizing model -/

-- `aliasOrd` is not registered, yet it names natOrd's value: it is an Ord
-- dictionary in the model, with natOrd's members. A closed-world reading,
-- which treats distinct names as distinct, would say otherwise; the order
-- model is not a model of that reading.
example : snapshot.InterfaceMember interp .ordDictionary (interp.value .aliasOrd) :=
  alias_interfaceMember snapshot interp (registration := natRegistration) (by decide)
    (value_aliasOrd.trans value_natOrd.symm)

example : model.Satisfies environment (ordGuard aliasT) := by
  simp only [ordGuard, Model.Satisfies, Model.eval, List.map_cons, List.map_nil]
  change holds (application .ordDictionary [model.eval environment aliasT])
  rw [eval_aliasT, application_primitive (by decide)]
  exact Or.inl rfl

example : model.Satisfies environment (OrderRegistry.domainMember aliasT two) := by
  simp only [OrderRegistry.domainMember, Model.Satisfies, Model.eval, List.map_cons, List.map_nil]
  change holds (application .domainMember [_, _])
  rw [domainMember_exact, eval_aliasT, eval_two, nat_member_exact]
  exact ⟨2, rfl⟩

/-! ## Invalidation -/

-- Registering a new name: the generated clauses grow, old names keep their
-- accesses and their evidence, and the unknown name becomes declared.
def aliasRegistration : Registration Domain Symbol := ⟨.aliasOrd, 1, .ordDictionary, .nat, primitives .nat⟩
def grown : Registry Domain String Data Symbol :=
  { registry with dictionaries := registry.dictionaries ++ [aliasRegistration] }
def grownSnapshot : DictionaryRegistry.Snapshot Domain String Data Symbol := ⟨1, signature, grown⟩

example : registry.Unchanged grown [.natOrd, .boolOrd] := register_unchanged aliasRegistration (by decide)

example : registry.access? .value natOrdT [] .less 2 = grown.access? .value natOrdT [] .less 2 :=
  access_unchanged (register_unchanged aliasRegistration (by decide)) .value [] .less 2

example : registry.access? .value aliasT [] .less 2 = .unknown .aliasOrd ∧
    grown.access? .value aliasT [] .less 2 = .declared aliasRegistration lessOperation := by decide

example : ¬ registry.Unchanged grown [.aliasOrd] := by
  intro unchanged
  have same := (unchanged .aliasOrd (by simp)).1
  revert same
  decide

example (clause : HornClause String Data Symbol) (member : clause ∈ kb) : clause ∈ grownSnapshot.kb names :=
  kb_mono (snapshot := snapshot) (grown := grownSnapshot) rfl rfl
    (fun _ member => List.mem_append_left _ member) names clause member

-- The old evidence transfers; the new registration brings its own.
theorem unchanged_old (name : Symbol) (old : name ≠ .aliasOrd) : snapshot.Unchanged grownSnapshot [name] :=
  ⟨rfl, rfl, register_unchanged aliasRegistration (by simpa [aliasRegistration] using old.symm)⟩

theorem alias_checked : aliasRegistration.Checked grownSnapshot interp :=
  checked_dictionary rfl rfl rfl (membership := .isNat) (comparison := .natCompare) (equality := .natEqual)
    (order := .natLess) (value_aliasOrd.trans natOrd_eq) rfl rfl rfl rfl rfl holds_isNat
    (fun a b x y => (nat_operations a b x y).1) (fun a b x y => (nat_operations a b x y).2.1)
    (fun a b x y => (nat_operations a b x y).2.2.1) (fun a b x y => (nat_operations a b x y).2.2.2.1)
    (fun a b x y => (nat_operations a b x y).2.2.2.2)

theorem grown_checked : grownSnapshot.Checked interp := by
  intro registration registered
  simp only [grownSnapshot, grown, registry, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at registered
  rcases registered with rfl | rfl | rfl | rfl
  · exact nat_checked.transfer (unchanged_old _ (by decide)) (by decide)
  · exact desc_checked.transfer (unchanged_old _ (by decide)) (by decide)
  · exact bool_checked.transfer (unchanged_old _ (by decide)) (by decide)
  · exact alias_checked

-- The same model realizes the grown snapshot: the alias adds no new value.
theorem grown_realized : grownSnapshot.Realizes interp := by
  refine ⟨signature_realized, ?_, fun dict value => domainMember_exact dict value⟩
  intro interface declared value
  simp only [grownSnapshot, grown, registry, List.mem_singleton] at declared
  subst declared
  change holds (application .ordDictionary [value]) ↔ _
  rw [application_primitive (by decide)]
  change value = natOrd ∨ value = natDesc ∨ value = boolOrd ↔ _
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨natRegistration, by decide, rfl, value_natOrd⟩
    · exact ⟨descRegistration, by decide, rfl, value_natDesc⟩
    · exact ⟨boolRegistration, by decide, rfl, value_boolOrd⟩
  · rintro ⟨registration, registered, _, rfl⟩
    simp only [grownSnapshot, grown, registry, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at registered
    rcases registered with rfl | rfl | rfl | rfl <;> simp [natRegistration, descRegistration, boolRegistration,
      aliasRegistration]

example : model.Models (grownSnapshot.kb (Literal := Data) names) :=
  models_kb grown_realized grown_checked (by decide) names

-- A version change of one registration affects only the plans reading it.
def bumped : Registry Domain String Data Symbol :=
  { registry with dictionaries := [{ natRegistration with version := 2 }, descRegistration, boolRegistration] }

example : ¬ registry.Unchanged bumped [.natOrd] := by
  intro unchanged
  have same := (unchanged .natOrd (by simp)).1
  revert same
  decide

example : registry.Unchanged bumped [.natDesc, .boolOrd] := by
  intro name member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact ⟨by decide, fun _ _ => rfl⟩

-- A changed signature changes what every registration's evidence read.
example : ¬ snapshot.Unchanged { snapshot with signature := { signature with revision := 1 } } [.natOrd] := by
  intro unchanged
  have same := congrArg AdmissionSignature.SignatureSnapshot.revision unchanged.1
  simp [snapshot, signature] at same

-- A new revision is a new snapshot.
example : ¬ snapshot.ReusableAt { snapshot with revision := 1 } :=
  DictionaryRegistry.Snapshot.not_reusable_of_revision_ne (by decide)

/-! ## Standard axioms only -/

/-- info: 'AnthillModKbSpec.OrderRegistry.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrderRegistry.checked

/-- info: 'AnthillModKbSpec.OrderRegistry.kb_models' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrderRegistry.kb_models

/-- info: 'AnthillModKbSpec.OrderRegistry.lessCompare_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrderRegistry.lessCompare_valid

/-- info: 'AnthillModKbSpec.DictionaryRegistry.access_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms DictionaryRegistry.access_eval

end DictionaryRegistryTests
