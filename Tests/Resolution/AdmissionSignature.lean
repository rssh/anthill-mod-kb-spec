import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Semantics AnthillModKbSpec.InductiveDomains
open AnthillModKbSpec.AdmissionSignature

namespace AdmissionSignatureTests

open AnthillModKbSpec.InductionModel

def snapshot : SignatureSnapshot Domain Symbol :=
  ⟨0, ⟨family, membershipSymbol, [⟨.reachable, 1⟩, ⟨.reachable, 2⟩, ⟨.even, 1⟩]⟩⟩

theorem realized : AdmissionSignature.Realizes snapshot model := ⟨realizes⟩

-- The witness includes the existing nontrivial KB model and exact Nat domain.
theorem modelWitness : ∃ witness : Model Unit Symbol Value .hoApply,
    AdmissionSignature.Realizes snapshot witness ∧ witness.Models kb :=
  ⟨model, realized, kb_models⟩

example : snapshot.registered? .reachable 1 = true := by decide
example : snapshot.registered? .reachable 2 = true := by decide
example : snapshot.registered? .reachable 0 = false := by decide
example : snapshot.registered? .succ 1 = false := by decide

def reachableEvidence : ReferenceEvidence snapshot model 1 (reference model .reachable) :=
  ⟨.reachable, by decide, rfl⟩

theorem reachableApplication (value : Value) :
    model.holds (model.application .hoApply [reference model .reachable, value]) ↔
      model.holds (model.application .reachable [value]) :=
  reachableEvidence.hoApply [value] rfl

example (environment : Environment String Value) :
    model.Satisfies environment (applyP (.app .reachable []) (.var "x")) ↔
      model.Satisfies environment (reachable (.var "x")) :=
  satisfies_hoApply_reference model environment .reachable [.var "x"]

-- Arity ranges can overlap. Registration says nothing about predicate truth.
example : snapshot.PredicateMember model 1 (reference model .reachable) ∧
    snapshot.PredicateMember model 2 (reference model .reachable) :=
  ⟨⟨.reachable, by decide, rfl⟩, ⟨.reachable, by decide, rfl⟩⟩

example : ¬ model.holds (model.application .reachable [natValue 0, natValue 1]) := by
  change ¬ atomTruth .reachable [natValue 0, natValue 1]
  rw [atomTruth_ordinary .reachable (by decide)]
  exact id

theorem referenceNotNat (n : Nat) : reference model .reachable ≠ natValue n := by
  intro same
  have keys := congrArg Prod.fst same
  cases n <;> simp [reference, model, natValue, natKey] at keys

theorem predicateNotData :
    ¬ (Range.data [.nat]).Contains snapshot model (reference model .reachable) := by
  intro member
  obtain ⟨_, _, member⟩ := (realized.data_iff [.nat] _).mp member
  obtain ⟨n, same⟩ := (application_nat _).mp member
  exact referenceNotNat n same

-- Data quantification uses generated Nat values, not predicate references.
theorem dataQuantification (environment : Environment String Value) :
    model.Satisfies environment
      ((family.forallAll "x" (reachable (.var "x"))).toTerm membershipSymbol) := by
  apply (family.forallAll_satisfies_iff model realizes environment "x"
    (reachable (.var "x"))).mpr
  intro ⟨tree, domain, member⟩
  obtain ⟨n, same⟩ := member_denote member
  simp only [reachable, Model.Satisfies, Model.eval, List.map_cons, List.map_nil,
    update, ite_true, same]
  exact reachable_at_nat n

-- P_1 quantifies over the declared reachable/even references. No D_all guard.
theorem predicateQuantification : snapshot.ForallPredicates model 1
    (fun predicate => model.holds (model.application .hoApply [predicate, natValue 0])) := by
  apply (snapshot.forallPredicates_iff model 1
    (fun predicate => model.holds (model.application .hoApply [predicate, natValue 0]))).mpr
  intro symbol declared
  have choices : symbol = .reachable ∨ symbol = .even := by
    simpa [SignatureSnapshot.Registered, snapshot] using declared
  rcases choices with rfl | rfl
  · exact (model.holds_hoApply .reachable _).mpr (reachable_at_nat 0)
  · exact (model.holds_hoApply .even _).mpr ((even_at_nat 0).mpr (by decide))

-- Raw forall still ranges over every semantic value, including a non-Nat.
example (environment : Environment String Value) :
    ¬ model.Satisfies environment (.forallVar "x" (isNat (.var "x"))) := by
  intro all
  have each : ∀ value, model.holds (model.application .isNat [value]) := by
    simpa [Model.Satisfies, Model.eval, isNat, model.holds_universal, update] using all
  obtain ⟨n, same⟩ := (application_nat _).mp (each (reference model .reachable))
  exact referenceNotNat n same

-- Disjointness is not an axiom: zero can be registered as a nullary predicate
-- (always false) while its reference is also the constructor value Nat zero.
def overlapping : SignatureSnapshot Domain Symbol :=
  ⟨0, ⟨family, membershipSymbol, [⟨.zero, 0⟩]⟩⟩

example : AdmissionSignature.Realizes overlapping model := ⟨realizes⟩

example : overlapping.PredicateMember model 0 (natValue 0) ∧
    (Range.data [.nat]).Contains overlapping model (natValue 0) := by
  constructor
  · exact ⟨.zero, by decide, application_zero⟩
  · exact ⟨natTree 0, ⟨.nat, by simp, natTree_member 0⟩, natTree_denote 0⟩

-- Unknown names need not denote unknown values when references alias.
def coarseModel := Model.trueAtoms Unit Symbol .hoApply

example : reference coarseModel .reachable = reference coarseModel .succ := rfl
example : ¬ snapshot.Registered .succ 1 := by decide
example : snapshot.PredicateMember coarseModel 1 (reference coarseModel .succ) :=
  ⟨.reachable, by decide, rfl⟩

example (args : List Bool) :
    coarseModel.holds (coarseModel.application .reachable args) ↔
      coarseModel.holds (coarseModel.application .succ args) :=
  reference_alias coarseModel .reachable .succ rfl args

-- A value with no registered representative really is outside P_1.
example : ¬ snapshot.PredicateMember coarseModel 1 false := by
  apply snapshot.not_predicateMember coarseModel 1 false
  intro symbol _
  exact Bool.noConfusion

-- Dictionary references have their own representation. Explicit agreement
-- connects them to Term references; the dictionary extension alone does not.
def coarseExtension : OperationDictionaries.Extension coarseModel Empty where
  roleOf := fun _ => .predicate
  reference := fun _ => true
  call := fun _ _ => true
  dictionary := fun _ => false
  project := fun _ field => nomatch field
  call_reference := fun _ _ => rfl
  project_dictionary := fun _ field => nomatch field

theorem dictionaryCompatible : DictionaryCompatible snapshot coarseExtension := by
  intro symbol arity declared
  rfl

example : coarseModel.holds
      (coarseModel.application .hoApply [coarseExtension.reference .reachable, false]) ↔
    coarseModel.holds (coarseExtension.invoke ⟨.predicate, .reachable, []⟩ [false]) :=
  dictionary_hoApply coarseExtension dictionaryCompatible
    (show snapshot.Registered .reachable 1 by decide) [false] rfl

def separateExtension : OperationDictionaries.Extension coarseModel Empty :=
  { coarseExtension with reference := fun _ => false }

example : ¬ DictionaryCompatible snapshot separateExtension := by
  intro compatible
  have impossible : false = true := compatible .reachable 1 (by decide)
  exact Bool.noConfusion impossible

def revised : SignatureSnapshot Domain Symbol := { snapshot with revision := 1 }
def removed : SignatureSnapshot Domain Symbol :=
  { snapshot with signature := { snapshot.signature with predicates := [] } }

example : ¬ snapshot.ReusableAt revised :=
  snapshot.not_reusable_of_revision_ne revised (by decide)

-- Reusing a revision number cannot make changed declarations safe to reuse.
example : snapshot.revision = removed.revision := rfl
example : ¬ snapshot.ReusableAt removed := by
  intro same
  have stale := snapshot.registered_of_reusable removed same reachableEvidence.registered
  exact (by decide : ¬ removed.Registered .reachable 1) stale

example : (reachableEvidence.rebase (show snapshot.ReusableAt snapshot from rfl)).symbol =
    .reachable := rfl

-- Roles are name metadata; predicate ranges do not create semantic sorts.
def rigidPredicate : NameDeclaration String Domain := ⟨"P", .rigid, .predicate 1⟩
def flexiblePredicate : NameDeclaration String Domain := ⟨"Q", .flexible, .predicate 1⟩
example : rigidPredicate.role ≠ flexiblePredicate.role := by decide
example : rigidPredicate.range.Contains snapshot model (reference model .reachable) :=
  ⟨.reachable, by decide, rfl⟩

-- Audit the model-backed results and generic contract bridges.
open Lean Meta in
run_meta do
  for declaration in [``modelWitness, ``reachableApplication, ``predicateNotData,
      ``dataQuantification, ``predicateQuantification, ``reference_alias,
      ``satisfies_hoApply_reference, ``dictionaryCompatible, ``dictionary_hoApply] do
    for axiomName in ← collectAxioms declaration do
      unless axiomName ∈ [`propext, `Classical.choice, `Quot.sound] do
        throwError "unexpected axiom in admission signature: {axiomName}"

end AdmissionSignatureTests
