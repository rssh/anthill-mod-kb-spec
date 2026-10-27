import AnthillModKbSpec.Foundation.InductiveDomains
import AnthillModKbSpec.Foundation.OperationDictionaries

namespace AnthillModKbSpec.AdmissionSignature

open Semantics InductiveDomains

/-- A symbol may have several declared arities. Declarations constrain use,
not truth, and do not assert an induction principle or finite data domain. -/
structure PredicateDeclaration (Symbol : Type) where
  symbol : Symbol
  arity : Nat
  deriving DecidableEq, Repr

/-- Membership symbols naming each range: one per data domain, one for the
union of all generated data (D_all), and one per predicate arity (P_n). Guards
are atoms over these symbols; the registry contributes KB facts, not guard syntax. -/
structure Naming (Domain Symbol : Type) where
  membershipSymbol : Domain → Symbol
  dataSymbol : Symbol
  predicateSymbol : Nat → Symbol

/-- Typeless signature over the existing constructor domains and symbol space.
Neither domain names nor predicate declarations imply disjoint semantic ranges. -/
structure Signature (Domain Symbol : Type) where
  data : FiniteFamily Domain Symbol
  membershipSymbol : Domain → Symbol
  dataSymbol : Symbol
  predicateSymbol : Nat → Symbol
  predicates : List (PredicateDeclaration Symbol)

def Signature.naming (signature : Signature Domain Symbol) : Naming Domain Symbol :=
  ⟨signature.membershipSymbol, signature.dataSymbol, signature.predicateSymbol⟩

/-- Evidence refers to the entire immutable snapshot, not just its revision.
Changing declarations with an unchanged revision still changes the snapshot.
This records signature declarations, not KB facts or a local proof context. -/
structure SignatureSnapshot (Domain Symbol : Type) where
  revision : Nat
  signature : Signature Domain Symbol

/-- Only the naming, not the registry, domain definitions, or revision. -/
def SignatureSnapshot.naming (snapshot : SignatureSnapshot Domain Symbol) : Naming Domain Symbol :=
  snapshot.signature.naming

def SignatureSnapshot.Registered (snapshot : SignatureSnapshot Domain Symbol) (symbol : Symbol)
    (arity : Nat) : Prop :=
  ⟨symbol, arity⟩ ∈ snapshot.signature.predicates

instance [DecidableEq Symbol] (snapshot : SignatureSnapshot Domain Symbol) (symbol : Symbol)
    (arity : Nat) : Decidable (snapshot.Registered symbol arity) :=
  inferInstanceAs (Decidable (PredicateDeclaration.mk symbol arity ∈ snapshot.signature.predicates))

/-- Effective declaration lookup needs no equality or decision procedure on
semantic values. Unknown declarations are capability misses, not negative proofs. -/
def SignatureSnapshot.registered? [DecidableEq Symbol] (snapshot : SignatureSnapshot Domain Symbol)
    (symbol : Symbol) (arity : Nat) : Bool :=
  decide (snapshot.Registered symbol arity)

@[simp] theorem SignatureSnapshot.registered?_eq_true [DecidableEq Symbol]
    (snapshot : SignatureSnapshot Domain Symbol) (symbol : Symbol) (arity : Nat) :
    snapshot.registered? symbol arity = true ↔ snapshot.Registered symbol arity := by
  simp [SignatureSnapshot.registered?]

variable {Domain Variable Literal Symbol Value : Type} {hoApplySymbol : Symbol}
  {model : Model Literal Symbol Value hoApplySymbol}
  {snapshot recorded current : SignatureSnapshot Domain Symbol} {arity : Nat} {value : Value}
  {symbol : Symbol} {Field : Type}

/-- These are the concrete-symbol references already represented by `.app s []`
in Term and covered by Model.holds_hoApply. No injectivity is required. -/
def reference (model : Model Literal Symbol Value hoApplySymbol) (symbol : Symbol) : Value :=
  model.application symbol []

/-- P_n contains exactly denotations of declared references of arity n.
Distinct symbols, different arities, and data domains may share values. -/
def SignatureSnapshot.PredicateMember (snapshot : SignatureSnapshot Domain Symbol)
    (model : Model Literal Symbol Value hoApplySymbol) (arity : Nat) (value : Value) : Prop :=
  ∃ symbol, snapshot.Registered symbol arity ∧ reference model symbol = value

/-- A checked representative, indexed by the exact snapshot and range. -/
structure ReferenceEvidence (snapshot : SignatureSnapshot Domain Symbol)
    (model : Model Literal Symbol Value hoApplySymbol) (arity : Nat) (value : Value) where
  symbol : Symbol
  registered : snapshot.Registered symbol arity
  denotes : reference model symbol = value

theorem predicateMember_iff_evidence (snapshot : SignatureSnapshot Domain Symbol)
    (model : Model Literal Symbol Value hoApplySymbol) (arity : Nat) (value : Value) :
    snapshot.PredicateMember model arity value ↔
      Nonempty (ReferenceEvidence snapshot model arity value) := by
  constructor
  · rintro ⟨symbol, declared, denotes⟩
    exact ⟨⟨symbol, declared, denotes⟩⟩
  · rintro ⟨evidence⟩
    exact ⟨evidence.symbol, evidence.registered, evidence.denotes⟩

theorem ReferenceEvidence.hoApply (evidence : ReferenceEvidence snapshot model arity value)
    (args : List Value) (_length : args.length = arity) :
    model.holds (model.application hoApplySymbol (value :: args)) ↔
      model.holds (model.application evidence.symbol args) := by
  rcases evidence with ⟨symbol, declared, rfl⟩
  exact model.holds_hoApply symbol args

/-- Aliased symbol references necessarily agree in predicate truth. This follows
from the existing model law, without assuming reference injectivity. -/
theorem reference_alias (model : Model Literal Symbol Value hoApplySymbol)
    (left right : Symbol) (same : reference model left = reference model right)
    (args : List Value) :
    model.holds (model.application left args) ↔ model.holds (model.application right args) := by
  rw [← model.holds_hoApply left args, ← model.holds_hoApply right args]
  rw [show model.application left [] = model.application right [] from same]

/-- Concrete references in the existing syntax have the same application
meaning. Registry evidence controls range admission, not this raw model law. -/
theorem satisfies_hoApply_reference [DecidableEq Variable]
    (model : Model Literal Symbol Value hoApplySymbol)
    (environment : Environment Variable Value) (symbol : Symbol)
    (args : List (Term Variable Literal Symbol)) :
    model.Satisfies environment (.hoApply hoApplySymbol (.app symbol []) args) ↔
      model.Satisfies environment (.app symbol args) := by
  simp only [Term.hoApply, Model.Satisfies, Model.eval, List.map_cons, List.map_nil]
  exact model.holds_hoApply symbol _

/-- Exclusion requires ruling out every registered representative. An unknown
symbol can still denote the same value as a registered symbol. -/
theorem SignatureSnapshot.not_predicateMember (snapshot : SignatureSnapshot Domain Symbol)
    (model : Model Literal Symbol Value hoApplySymbol) (arity : Nat) (value : Value)
    (excluded : ∀ symbol, snapshot.Registered symbol arity → reference model symbol ≠ value) :
    ¬ snapshot.PredicateMember model arity value := by
  rintro ⟨symbol, declared, same⟩
  exact excluded symbol declared same

/-- Range metadata belongs to binders/machine names, not semantic sorts. No
default range is chosen here; guarded elaboration is S03's responsibility.
`allData` is D_all by name: it means every declared domain, without listing them. -/
inductive Range (Domain : Type) where
  | carrier
  | allData
  | data (domains : List Domain)
  | predicate (arity : Nat)

def Range.Contains (range : Range Domain) (snapshot : SignatureSnapshot Domain Symbol)
    (model : Model Literal Symbol Value hoApplySymbol) (value : Value) : Prop :=
  match range with
  | .carrier => True
  | .allData => ∃ tree, InUnion snapshot.signature.data.definitions snapshot.signature.data.domains tree ∧
      denote model tree = value
  | .data domains => ∃ tree, InUnion snapshot.signature.data.definitions domains tree ∧
      denote model tree = value
  | .predicate arity => snapshot.PredicateMember model arity value

/-- Rigidity is proof-machine metadata. Both roles still refer to ordinary
values in the same carrier; this declaration adds no new Term constructor. -/
inductive NameRole where
  | rigid
  | flexible
  deriving DecidableEq, Repr

structure NameDeclaration (Variable Domain : Type) where
  name : Variable
  role : NameRole
  range : Range Domain

/-- Exact interpretation of every membership symbol is evidence, not a
consequence of registration. P_n membership holds exactly on registered
references; the existing model law supplies their application semantics. -/
structure Realizes (snapshot : SignatureSnapshot Domain Symbol)
    (model : Model Literal Symbol Value hoApplySymbol) : Prop where
  data : InductiveDomains.Realizes model snapshot.signature.data.definitions
    snapshot.signature.membershipSymbol
  allData : ∀ value, model.holds (model.application snapshot.signature.dataSymbol [value]) ↔
    (Range.allData : Range Domain).Contains snapshot model value
  predicates : ∀ arity value,
    model.holds (model.application (snapshot.signature.predicateSymbol arity) [value]) ↔
      snapshot.PredicateMember model arity value

theorem Realizes.data_iff (valid : Realizes snapshot model) (domains : List Domain)
    (value : Value) :
    (Range.data domains).Contains snapshot model value ↔
      ∃ domain ∈ domains,
        model.holds (model.application (snapshot.signature.membershipSymbol domain) [value]) := by
  constructor
  · rintro ⟨tree, ⟨domain, selected, member⟩, same⟩
    exact ⟨domain, selected, (valid.data domain value).mpr ⟨tree, member, same⟩⟩
  · rintro ⟨domain, selected, member⟩
    obtain ⟨tree, member, same⟩ := (valid.data domain value).mp member
    exact ⟨tree, ⟨domain, selected, member⟩, same⟩

/-- Quantification over P_n is over registered reference values, not every
mathematical predicate or every data value. No enumeration algorithm is implied. -/
def SignatureSnapshot.ForallPredicates (snapshot : SignatureSnapshot Domain Symbol)
    (model : Model Literal Symbol Value hoApplySymbol) (arity : Nat)
    (property : Value → Prop) : Prop :=
  ∀ value, snapshot.PredicateMember model arity value → property value

theorem SignatureSnapshot.forallPredicates_iff (snapshot : SignatureSnapshot Domain Symbol)
    (model : Model Literal Symbol Value hoApplySymbol) (arity : Nat) (property : Value → Prop) :
    snapshot.ForallPredicates model arity property ↔
      ∀ symbol, snapshot.Registered symbol arity → property (reference model symbol) := by
  constructor
  · intro all symbol declared
    exact all _ ⟨symbol, declared, rfl⟩
  · rintro all value ⟨symbol, declared, rfl⟩
    exact all symbol declared

/-- Reuse requires equality of full snapshots, even if revisions happen to
coincide. Admission plans must be rechecked when their snapshot changes. -/
def SignatureSnapshot.ReusableAt (recorded current : SignatureSnapshot Domain Symbol) : Prop := recorded = current

theorem SignatureSnapshot.not_reusable_of_revision_ne (recorded current : SignatureSnapshot Domain Symbol)
    (different : recorded.revision ≠ current.revision) : ¬ recorded.ReusableAt current := by
  intro same
  exact different (congrArg SignatureSnapshot.revision same)

theorem SignatureSnapshot.registered_of_reusable (recorded current : SignatureSnapshot Domain Symbol)
    (same : recorded.ReusableAt current) (declared : recorded.Registered symbol arity) :
    current.Registered symbol arity := same ▸ declared

def ReferenceEvidence.rebase (evidence : ReferenceEvidence recorded model arity value)
    (same : recorded.ReusableAt current) : ReferenceEvidence current model arity value :=
  same ▸ evidence

/-- Dictionary extensions can use a distinct reference representation. Connecting
it to Term's concrete-symbol ho_apply requires this explicit compatibility proof. -/
def DictionaryCompatible [DecidableEq Field] (snapshot : SignatureSnapshot Domain Symbol)
    (extension : OperationDictionaries.Extension model Field) : Prop :=
  ∀ symbol arity, snapshot.Registered symbol arity →
    extension.reference symbol = reference model symbol

theorem dictionary_hoApply [DecidableEq Field]
    (extension : OperationDictionaries.Extension model Field)
    (compatible : DictionaryCompatible snapshot extension)
    (declared : snapshot.Registered symbol arity) (args : List Value)
    (_length : args.length = arity) :
    model.holds (model.application hoApplySymbol (extension.reference symbol :: args)) ↔
      model.holds (extension.invoke ⟨.predicate, symbol, []⟩ args) := by
  rw [compatible symbol arity declared, extension.invoke_eq]
  exact model.holds_hoApply symbol args

end AnthillModKbSpec.AdmissionSignature
