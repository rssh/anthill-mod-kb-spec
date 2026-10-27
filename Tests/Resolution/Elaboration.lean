import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Semantics AnthillModKbSpec.InductiveDomains
open AnthillModKbSpec.AdmissionSignature AnthillModKbSpec.Elaboration
open AnthillModKbSpec.InductionModel

namespace ElaborationTests

-- Nat is the only domain, so isNat also names D_all; isPred n names P_n.
def snapshot : SignatureSnapshot Domain Symbol :=
  ⟨0, ⟨family, membershipSymbol, .isNat, .isPred, [⟨.reachable, 1⟩, ⟨.reachable, 2⟩, ⟨.even, 1⟩]⟩⟩

theorem realized : AdmissionSignature.Realizes snapshot model := by
  refine ⟨realizes, fun value => ?_, fun arity value => ?_⟩
  · constructor
    · intro truth
      obtain ⟨tree, member, same⟩ := (realizes .nat value).mp truth
      exact ⟨tree, ⟨.nat, by simp [snapshot, family], member⟩, same⟩
    · rintro ⟨tree, ⟨domain, _, member⟩, same⟩
      cases domain
      exact (realizes .nat value).mpr ⟨tree, member, same⟩
  · show model.holds (model.application (.isPred arity) [value]) ↔ _
    rw [application_isPred]
    constructor
    · rintro ⟨symbol, member, rfl⟩
      exact ⟨symbol, by simpa [SignatureSnapshot.Registered, snapshot, predicateRegistry] using member, rfl⟩
    · rintro ⟨symbol, declared, rfl⟩
      exact ⟨symbol, by simpa [SignatureSnapshot.Registered, snapshot, predicateRegistry] using declared, rfl⟩

def dataRanges : Ranges Domain := defaultRanges
def predicateRanges : Ranges Domain := fun _ => .predicate 1

-- Default data quantification excludes predicate references and logical values.
theorem defaultForall (environment : Environment String Value) :
    model.Satisfies environment (elaborate snapshot.naming dataRanges (.forallVar "x" (isNat (.var "x")))) := by
  rw [elaborate, forallRange_satisfies snapshot model realized]
  intro value member
  have selected := (realized.data_iff [.nat] value).mp member
  obtain ⟨domain, _, truth⟩ := selected
  cases domain
  simpa [elaborate, elaborateArgs, Model.Satisfies, Model.eval, isNat, update, snapshot, membershipSymbol] using truth

theorem referenceNotData : ¬ (Range.data [.nat]).Contains snapshot model (reference model .reachable) := by
  intro member
  obtain ⟨domain, _, truth⟩ := (realized.data_iff [.nat] _).mp member
  cases domain
  obtain ⟨n, same⟩ := (application_nat _).mp truth
  have keys := congrArg Prod.fst same
  cases n <;> simp [reference, model, natValue, natKey] at keys

theorem rawForallFails (environment : Environment String Value) :
    ¬ model.Satisfies environment (.forallVar "x" (isNat (.var "x"))) := by
  intro all
  have every : ∀ value, model.holds (model.application .isNat [value]) := by
    simpa [Model.Satisfies, Model.eval, isNat, model.holds_universal, update] using all
  apply referenceNotData
  exact (realized.data_iff [.nat] _).mpr ⟨.nat, by simp, every _⟩

theorem dataExists (environment : Environment String Value) :
    model.Satisfies environment (elaborate snapshot.naming dataRanges (.existsVar "x" (isNat (.var "x")))) := by
  rw [elaborate, existsRange_satisfies snapshot model realized]
  refine ⟨natValue 0, ?_, ?_⟩
  · exact (show (Range.data [.nat]).Contains snapshot model (natValue 0) from
      ⟨natTree 0, ⟨.nat, by simp, natTree_member 0⟩, natTree_denote 0⟩)
  · simpa [elaborate, elaborateArgs, Model.Satisfies, Model.eval, isNat, update] using
      (application_nat (natValue 0)).mpr ⟨0, rfl⟩

-- Predicate binders have a reference guard, not a D_all guard.
theorem predicateExists (environment : Environment String Value) :
    model.Satisfies environment (elaborate snapshot.naming predicateRanges
      (.existsVar "P" (.equal (.var "P") (.app .reachable [])))) := by
  rw [elaborate, existsRange_satisfies snapshot model realized]
  refine ⟨reference model .reachable, ⟨.reachable, by decide, rfl⟩, ?_⟩
  apply (model.satisfies_equal _ _ _).mpr
  simp [elaborate, elaborateArgs, Model.eval, update, reference]

theorem carrierExists (environment : Environment String Value) :
    model.Satisfies environment (elaborate snapshot.naming (fun _ => .carrier)
      (.existsVar "x" (.equal (.var "x") (.app .reachable [])))) := by
  rw [elaborate, existsRange_satisfies snapshot model realized]
  refine ⟨reference model .reachable, True.intro, ?_⟩
  apply (model.satisfies_equal _ _ _).mpr
  simp [elaborate, elaborateArgs, Model.eval, update, reference]

theorem noPredicateWitness (environment : Environment String Value) :
    ¬ model.Satisfies environment (elaborate snapshot.naming (fun _ => .predicate 99) (.existsVar "P" .truth)) := by
  rw [elaborate, existsRange_satisfies snapshot model realized]
  rintro ⟨_, ⟨symbol, declared, _⟩, _⟩
  simp [SignatureSnapshot.Registered, snapshot] at declared

theorem predicateForall (environment : Environment String Value) :
    model.Satisfies environment (elaborate snapshot.naming predicateRanges
      (.forallVar "P" (.hoApply .hoApply (.var "P") [.app .zero []]))) := by
  rw [elaborate, forallRange_satisfies snapshot model realized]
  rintro value ⟨symbol, declared, rfl⟩
  have choices : symbol = .reachable ∨ symbol = .even := by
    simpa [SignatureSnapshot.Registered, snapshot] using declared
  simp only [Term.hoApply, elaborate, elaborateArgs, Model.Satisfies, Model.eval,
    List.map_cons, List.map_nil, update, ite_true]
  change model.holds (model.application .hoApply [reference model symbol, model.application .zero []])
  simp only [reference]
  rw [model.holds_hoApply, application_zero]
  rcases choices with rfl | rfl
  · exact reachable_at_nat 0
  · exact (even_at_nat 0).mpr (by decide)

-- Arity overlap does not duplicate or disambiguate reference values.
example (environment : Environment String Value) :
    model.Satisfies environment (rangeGuard snapshot.naming (.predicate 2) (.app .reachable [])) := by
  apply (rangeGuard_satisfies snapshot model realized environment _ _).mpr
  exact ⟨.reachable, by decide, by simp [Model.eval, reference]⟩

-- Outer x is data; inner x is a predicate. Sidecar paths distinguish them.
def shadowRanges : Ranges Domain := fun path =>
  if path = [0] then .predicate 1 else .data [.nat]

theorem shadowing (environment : Environment String Value) :
    model.Satisfies environment (elaborate snapshot.naming shadowRanges
      (.forallVar "x" (.existsVar "x" (.equal (.var "x") (.app .reachable []))))) := by
  rw [elaborate, forallRange_satisfies snapshot model realized]
  intro value _
  rw [elaborate, existsRange_satisfies snapshot model realized]
  refine ⟨reference model .reachable, ?_, ?_⟩
  · exact ⟨.reachable, by decide, rfl⟩
  · apply (model.satisfies_equal _ _ _).mpr
    simp [elaborate, elaborateArgs, Model.eval, update, reference]

-- The eigenvariable must not be captured by the inner binder.
def nested : T := .conj (.var "x") (.forallVar "x" (.existsVar "P" (.equal (.var "x") (.var "P"))))

example : Substitutes (Substitution.single "x" (.var "fresh"))
    (elaborate snapshot.naming shadowRanges nested)
    (elaborate snapshot.naming shadowRanges (nested.openFree "x" "fresh")) :=
  opening_substitutes snapshot.naming shadowRanges nested "x" "fresh" (by simp [nested, Term.binderNames])

example : ¬ ("P" ∉ nested.binderNames) := by simp [nested, Term.binderNames]

example : nested.openFree "x" "fresh" =
    .conj (.var "fresh") (.forallVar "x" (.existsVar "P" (.equal (.var "x") (.var "P")))) := by simp [nested, Term.openFree]

-- Alpha-renaming a binder preserves its range annotation.
def renameBefore : T := .forallVar "y" (.equal (.var "x") (.var "y"))
def renameAfter : T := .forallVar "fresh" (.equal (.var "y") (.var "fresh"))

theorem renamed : Substitutes (Substitution.single "x" (.var "y")) renameBefore renameAfter := by
  apply Substitutes.forallVar
  · intro name member different
    have choices : name = "x" ∨ name = "y" := by simpa [Term.freeVars] using member
    rcases choices with rfl | rfl <;> simp_all [Substitution.single, Substitution.bind, Term.freeVars]
  · apply Substitutes.equal
    · simpa [Substitution.bind, Substitution.single] using
        (Substitutes.var (σ := Substitution.bind (Substitution.single "x" (.var "y")) "y" (.var "fresh"))
          (name := "x"))
    · simpa [Substitution.bind, Substitution.single] using
        (Substitutes.var (σ := Substitution.bind (Substitution.single "x" (.var "y")) "y" (.var "fresh"))
          (name := "y"))

theorem renamedElaboration : Substitutes (Substitution.single "x" (.var "y"))
    (elaborate snapshot.naming dataRanges renameBefore) (elaborate snapshot.naming dataRanges renameAfter) := by
  apply elaboration_substitutes snapshot.naming renamed
  intro name ranges
  simp only [Substitution.single, Substitution.bind]
  split <;> rfl

-- Quantifiers inside operation arguments and dictionary expressions are traversed.
def compound : T := .dictionaryCall
  (.existsVar "d" (.equal (.var "d") (.var "free"))) [.succ] .even
  [.hoApply .hoApply (.var "P") [.forallVar "x" (.equal (.var "x") (.var "free"))]]

example : elaborate snapshot.naming dataRanges compound = .dictionaryCall
    (existsRange snapshot.naming .allData "d" (.equal (.var "d") (.var "free"))) [.succ] .even
    [.hoApply .hoApply (.var "P") [forallRange snapshot.naming .allData "x"
      (.equal (.var "x") (.var "free"))]] := by
  simp [compound, Term.hoApply, elaborate, elaborateArgs, dataRanges, defaultRanges, child]

-- Lowering reads only the naming. Registering another predicate changes the
-- snapshot, and its generated facts, but not one lowered term.
def grown : SignatureSnapshot Domain Symbol :=
  ⟨1, { snapshot.signature with predicates := ⟨.succ, 1⟩ :: snapshot.signature.predicates }⟩

example : ¬ snapshot.ReusableAt grown := snapshot.not_reusable_of_revision_ne grown (by decide)
example : grown.naming = snapshot.naming := rfl
example : elaborate grown.naming dataRanges compound = elaborate snapshot.naming dataRanges compound := rfl

example (name : String) : name ∈ (elaborate snapshot.naming dataRanges compound).freeVars ↔
    name ∈ compound.freeVars := freeVars snapshot.naming compound dataRanges name

example (environment : Environment String Value) :
    model.eval environment (elaborate snapshot.naming dataRanges compound) =
      Elaboration.eval snapshot.naming dataRanges model environment compound :=
  eval_elaborate snapshot.naming model compound dataRanges environment

-- Arbitrary formula-valued substitution happens after lowering; it needs no
-- stability restriction on its images.
example (environment : Environment String Value) (result : T)
    (proof : Substitutes (Substitution.single "free" (.forallVar "q" (.var "q")))
      (elaborate snapshot.naming dataRanges compound) result) :
    model.Satisfies environment result ↔ model.Satisfies
      (fun name => model.eval environment (Substitution.single "free" (.forallVar "q" (.var "q")) name))
      (elaborate snapshot.naming dataRanges compound) :=
  satisfies_substitutes snapshot.naming dataRanges model proof environment

example : ¬ FreshForContext "free" (elaborateContext snapshot.naming dataRanges [compound]) := by
  rw [Elaboration.context_fresh]
  simp [FreshForContext, compound, Term.freeVars, Term.hoApply]

-- Separate assumptions can annotate the same binder name differently.
example : elaborateContext snapshot.naming shadowRanges
    [.existsVar "x" (.equal (.var "x") (.app .reachable [])), .existsVar "x" (isNat (.var "x"))] =
    [existsRange snapshot.naming (.predicate 1) "x" (.equal (.var "x") (.app .reachable [])),
     existsRange snapshot.naming (.data [.nat]) "x" (isNat (.var "x"))] := by
  simp [elaborateContext, elaborateArgs, elaborate, shadowRanges, child, isNat]

-- An actual empty domain in the same nonempty carrier.
-- `succ` applied to one argument is never true, so it names every empty range.
def emptySnapshot : SignatureSnapshot Unit Symbol :=
  ⟨0, ⟨⟨fun _ => False, [()], by intro domain; cases domain; simp⟩, fun _ => .succ, .succ, fun _ => .succ, []⟩⟩

theorem never (value : Value) : ¬ model.holds (model.application .succ [value]) :=
  (atomTruth_ordinary .succ (by decide) [value]).mp

theorem emptyRealized : AdmissionSignature.Realizes emptySnapshot model := by
  refine ⟨fun domain value => ⟨fun truth => (never value truth).elim, ?_⟩,
    fun value => ⟨fun truth => (never value truth).elim, ?_⟩,
    fun arity value => ⟨fun truth => (never value truth).elim, ?_⟩⟩
  · rintro ⟨tree, member, _⟩
    cases member with
    | construct declared _ _ => exact False.elim declared
  · rintro ⟨tree, ⟨_, _, member⟩, _⟩
    cases member with
    | construct declared _ _ => exact False.elim declared
  · rintro ⟨symbol, declared, _⟩
    simp [SignatureSnapshot.Registered, emptySnapshot] at declared

theorem emptyQuantifiers (environment : Environment String Value) :
    model.Satisfies environment (elaborate emptySnapshot.naming defaultRanges (.forallVar "x" .falsity)) ∧
    ¬ model.Satisfies environment (elaborate emptySnapshot.naming defaultRanges (.existsVar "x" .truth)) := by
  have noMember (value : Value) : ¬ (Range.data [()]).Contains emptySnapshot model value := by
    rintro ⟨tree, ⟨domain, _, member⟩, _⟩
    cases member with
    | construct declared _ _ => exact declared
  constructor
  · rw [elaborate, forallRange_satisfies emptySnapshot model emptyRealized]
    intro value member
    exact False.elim (noMember value member)
  · rw [elaborate, existsRange_satisfies emptySnapshot model emptyRealized]
    rintro ⟨value, member, _⟩
    exact noMember value member

-- Two distinct domains both generate Nat. Overlap requires no disjointness axiom.
def aliasZero (domain : Bool) : Rule Bool Symbol := ⟨domain, .zero, []⟩
def aliasSucc (domain : Bool) : Rule Bool Symbol := ⟨domain, .succ, [domain]⟩
def aliasSigma : Definitions Bool Symbol := fun rule =>
  rule = aliasZero false ∨ rule = aliasSucc false ∨ rule = aliasZero true ∨ rule = aliasSucc true

theorem aliasMember {domain : Bool} {tree : Tree Symbol} (member : Member aliasSigma domain tree) :
    Member sigma .nat tree := by
  induction member with
  | construct declared children members ih =>
      rcases declared with rfl | rfl | rfl | rfl
      · exact .construct (rule := zeroRule) (Or.inl rfl) children (fun i => Fin.elim0 i)
      · exact .construct (rule := succRule) (Or.inr rfl) children ih
      · exact .construct (rule := zeroRule) (Or.inl rfl) children (fun i => Fin.elim0 i)
      · exact .construct (rule := succRule) (Or.inr rfl) children ih

theorem aliasTree (domain : Bool) (n : Nat) : Member aliasSigma domain (natTree n) := by
  induction n with
  | zero =>
      apply Member.construct (rule := aliasZero domain) (children := fun i => Fin.elim0 i)
      · cases domain <;> simp [aliasSigma]
      · intro i; exact Fin.elim0 i
  | succ n ih =>
      apply Member.construct (rule := aliasSucc domain) (children := fun _ => natTree n)
      · cases domain <;> simp [aliasSigma]
      · intro i
        simp only [aliasSucc, List.length_cons, List.length_nil] at i ⊢
        have same : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) i 0
        subst i
        exact ih

def aliasSnapshot : SignatureSnapshot Bool Symbol :=
  ⟨0, ⟨⟨aliasSigma, [false, true], by intro domain; cases domain <;> simp⟩, fun _ => .isNat, .isNat,
    fun _ => .succ, []⟩⟩

theorem aliasRealized : AdmissionSignature.Realizes aliasSnapshot model := by
  refine ⟨fun domain value => ⟨?_, ?_⟩, fun value => ⟨?_, ?_⟩,
    fun arity value => ⟨fun truth => (never value truth).elim, ?_⟩⟩
  · intro truth
    obtain ⟨n, rfl⟩ := (application_nat value).mp truth
    exact ⟨natTree n, aliasTree domain n, natTree_denote n⟩
  · rintro ⟨tree, member, same⟩
    obtain ⟨n, denotes⟩ := member_denote (aliasMember member)
    exact (application_nat value).mpr ⟨n, same.symm.trans denotes⟩
  · intro truth
    obtain ⟨n, rfl⟩ := (application_nat value).mp truth
    exact ⟨natTree n, ⟨false, by simp [aliasSnapshot], aliasTree false n⟩, natTree_denote n⟩
  · rintro ⟨tree, ⟨_, _, member⟩, same⟩
    obtain ⟨n, denotes⟩ := member_denote (aliasMember member)
    exact (application_nat value).mpr ⟨n, same.symm.trans denotes⟩
  · rintro ⟨symbol, declared, _⟩
    simp [SignatureSnapshot.Registered, aliasSnapshot] at declared

theorem overlap (environment : Environment String Value) :
    model.Satisfies environment (rangeGuard aliasSnapshot.naming (.data [false]) (.app .zero [])) ∧
    model.Satisfies environment (rangeGuard aliasSnapshot.naming (.data [true]) (.app .zero [])) ∧
    model.Satisfies environment (elaborate aliasSnapshot.naming (fun _ => .data [false, true, false])
      (.existsVar "x" (.equal (.var "x") (.app .zero [])))) := by
  have member (domain : Bool) : (Range.data [domain]).Contains aliasSnapshot model (natValue 0) :=
    ⟨natTree 0, ⟨domain, by simp, aliasTree domain 0⟩, natTree_denote 0⟩
  refine ⟨?_, ?_, ?_⟩
  · apply (rangeGuard_satisfies aliasSnapshot model aliasRealized environment _ _).mpr
    simpa only [Model.eval, List.map_nil, application_zero] using member false
  · apply (rangeGuard_satisfies aliasSnapshot model aliasRealized environment _ _).mpr
    simpa only [Model.eval, List.map_nil, application_zero] using member true
  · rw [elaborate, existsRange_satisfies aliasSnapshot model aliasRealized]
    refine ⟨natValue 0, ⟨natTree 0, ⟨false, by simp, aliasTree false 0⟩, natTree_denote 0⟩, ?_⟩
    apply (model.satisfies_equal _ _ _).mpr
    simp only [elaborate, elaborateArgs, Model.eval, List.map_nil, update, ite_true, application_zero]

-- Clause template P is predicate-valued, x is data. The same substitution
-- must instantiate these guards and the original head/body on each clause use.
def template : HornClause String Unit Symbol :=
  .definite (.hoApply .hoApply (.var "P") [.var "x"]) [isNat (.var "x")]

def templateRanges (name : String) : Range Domain :=
  if name = "P" then .predicate 1 else .data [.nat]

example : Substitutes (Substitution.single "P" (.app Symbol.reachable [] : T))
    (rangeGuard snapshot.naming (.predicate 1) (.var "P"))
    (rangeGuard snapshot.naming (.predicate 1) (.app Symbol.reachable [])) :=
  rangeGuard_substitutes snapshot.naming (.predicate 1) (.singleVar "P" (.app Symbol.reachable []))

example : rangeGuard snapshot.naming (.predicate 1) (.var "P") ∈
    clauseGuards snapshot.naming templateRanges template := by
  simp [clauseGuards, template, templateRanges, HornClause.toFormula, Term.freeVars,
    Term.conjunction, Term.hoApply, isNat, rangeGuard, snapshot, SignatureSnapshot.naming, Signature.naming,
    InductiveDomains.guard]

example : rangeGuard snapshot.naming (.data [.nat]) (.var "P") ∉
    clauseGuards snapshot.naming templateRanges template := by
  simp [clauseGuards, template, templateRanges, HornClause.toFormula, Term.freeVars,
    Term.conjunction, Term.hoApply, isNat, rangeGuard, snapshot, SignatureSnapshot.naming, Signature.naming,
    InductiveDomains.guard]

example : rangeGuard snapshot.naming (.data [.nat]) (.var "x") ∈
    clauseGuards snapshot.naming templateRanges template := by
  simp [clauseGuards, template, templateRanges, HornClause.toFormula, Term.freeVars,
    Term.conjunction, Term.hoApply, isNat, rangeGuard, snapshot, SignatureSnapshot.naming, Signature.naming,
    InductiveDomains.guard]

-- With P := even and x := 1, all guards and the body hold, but the head fails.
-- Lowering therefore does not accidentally validate this false rule template.
def badEnvironment : Environment String Value := fun name =>
  if name = "P" then reference model .even else natValue 1

theorem falseTemplate : ¬ model.Satisfies badEnvironment
    (elaborateClause snapshot.naming dataRanges templateRanges template).toFormula := by
  rw [clause_satisfies snapshot dataRanges model realized]
  intro all
  have guarded : ∀ name ∈ template.toFormula.freeVars,
      (templateRanges name).Contains snapshot model (badEnvironment name) := by
    intro name member
    have names : name = "x" ∨ name = "P" := by
      simpa [template, HornClause.toFormula, Term.freeVars, Term.conjunction, Term.hoApply, isNat, or_left_comm, or_assoc, or_comm] using member
    rcases names with rfl | rfl
    · exact ⟨natTree 1, ⟨.nat, by simp, natTree_member 1⟩, natTree_denote 1⟩
    · exact ⟨.even, by decide, rfl⟩
  have body : ∀ term ∈ elaborateArgs snapshot.naming dataRanges 1 [isNat (.var "x")],
      model.Satisfies badEnvironment term := by
    intro term member
    simp only [elaborateArgs, isNat, elaborate, List.mem_cons, List.not_mem_nil, or_false] at member
    subst term
    simpa [Model.Satisfies, Model.eval, badEnvironment] using (application_nat (natValue 1)).mpr ⟨1, rfl⟩
  have head := all guarded body
  have truth : model.holds (model.application .even [natValue 1]) := by
    apply (model.holds_hoApply .even [natValue 1]).mp
    simpa [template, Term.hoApply, elaborate, elaborateArgs, Model.Satisfies, Model.eval, badEnvironment, reference] using head
  exact (by decide : ¬ 1 % 2 = 0) ((even_at_nat 1).mp truth)

-- A predicate binder left at the D_all default is rejected instead of guarded.
def predicateGoal : T := .forallVar "P" (applyP (.var "P") zero)

example : predicateRanged Symbol.hoApply dataRanges (fun _ => none) predicateGoal = false := by decide
example : elaborate? Symbol.hoApply snapshot.naming dataRanges predicateGoal = none := rfl
example : elaborate? Symbol.hoApply snapshot.naming predicateRanges predicateGoal =
    some (elaborate snapshot.naming predicateRanges predicateGoal) := rfl

-- The arity must match the application; `.carrier` is an explicit opt-out.
example : predicateRanged Symbol.hoApply (fun _ => (.predicate 2 : Range Domain)) (fun _ => none)
    predicateGoal = false := by decide
example : predicateRanged Symbol.hoApply (fun _ => (.carrier : Range Domain)) (fun _ => none)
    predicateGoal = true := by decide

-- The nearest binder decides, at the same paths lowering reads.
def shadowedPredicate : T := .forallVar "P" (.forallVar "P" (applyP (.var "P") zero))
def innerData : Ranges Domain := fun path => if path = [] then .predicate 1 else .data [.nat]
def innerPredicate : Ranges Domain := fun path => if path = [] then .data [.nat] else .predicate 1

example : predicateRanged Symbol.hoApply innerData (fun _ => none) shadowedPredicate = false := by decide
example : predicateRanged Symbol.hoApply innerPredicate (fun _ => none) shadowedPredicate = true := by decide

-- Lowering adds no guard for a fixed parameter, so its declaration governs it.
example : predicateRanged Symbol.hoApply dataRanges (fun _ => none) (applyP (.var "P") zero) = true := by decide

-- Under D_all, the induction rule would need isNat(P) and could never fire.
def dataOf : String → Range Domain := fun _ => .data [.nat]

example : elaborateClause? Symbol.hoApply snapshot.naming dataRanges dataOf inductionRule = none := rfl
example : clausePredicateRanged Symbol.hoApply dataRanges templateRanges inductionRule = true := by decide
example : clausePredicateRanged Symbol.hoApply dataRanges templateRanges template = true := by decide
example : clausePredicateRanged Symbol.hoApply dataRanges dataOf template = false := by decide

-- Guarded introductions reconstruct existing Derives; no new inference rule.
example : Derives Symbol.hoApply (∅ : K) []
    (forallRange snapshot.naming (.data [.nat]) "x" (.equal (.var "x") (.var "x"))) :=
  forallAll_intro snapshot "x" (by intro _ impossible; cases impossible) .equalRefl

-- Guards are derived from the generated signature clauses, not assumed.
def names : Nat → String := fun _ => "x"

theorem distinct : DistinctNames sigma names := by
  rintro rule (rfl | rfl) i j _
  all_goals
    apply Fin.ext
    have bound := i.isLt
    have other := j.isLt
    simp only [zeroRule, succRule, List.length_nil, List.length_cons] at bound other
    omega

def signature : K := signatureKb snapshot names

-- The realizing model satisfies every generated clause.
theorem signatureValid : model.Models signature := models_signatureKb snapshot model realized names

-- The P_1 guard of reachable comes from its generated fact: lookup, not enumeration.
theorem predicateExistsDerived : Derives Symbol.hoApply signature []
    (existsRange snapshot.naming (.predicate 1) "P" (.equal (.var "P") (.var "P"))) :=
  existsRange_intro snapshot.naming (.predicate 1) "P"
    (Substitutes.equal (.singleVar "P" (.app Symbol.reachable [])) (.singleVar "P" (.app Symbol.reachable [])))
    (rangeGuard_derives_predicate snapshot (fun _ member => member) (by decide)) .equalRefl

theorem zeroToTerm : ((natTree 0).toTerm : T) = zero := by simp [natTree, Tree.toTerm, zero]

theorem zeroGuard (kb : K) (contains : ∀ clause, clause ∈ signatureKb snapshot names → clause ∈ kb)
    (context : ProofContext String Unit Symbol) :
    Derives Symbol.hoApply kb context (rangeGuard snapshot.naming (.data [.nat]) zero) := by
  rw [← zeroToTerm]
  exact rangeGuard_derives_data snapshot distinct contains ⟨.nat, by simp, natTree_member 0⟩

-- The D_all default: an existential over all generated data, derived without assumptions.
theorem dataExistsDerived : Derives Symbol.hoApply signature []
    (existsRange snapshot.naming .allData "x" (.equal (.var "x") (.var "x"))) := by
  have guard : Derives Symbol.hoApply signature [] (rangeGuard snapshot.naming .allData zero) := by
    rw [← zeroToTerm]
    exact rangeGuard_derives_allData snapshot distinct (fun _ member => member) (natTree_member 0)
  exact existsRange_intro snapshot.naming .allData "x"
    (Substitutes.equal (.singleVar "x" zero) (.singleVar "x" zero)) guard .equalRefl

-- A lowered rule body starts with its guards; generated clauses discharge them.
def guardedSucc : HornClause String Unit Symbol := elaborateClause snapshot.naming dataRanges dataOf reachableSucc

theorem guardedSucc_eq : guardedSucc = .definite (reachable (succ (.var "x")))
    [rangeGuard snapshot.naming (.data [.nat]) (.var "x"), rangeGuard snapshot.naming (.data [.nat]) (.var "x"),
      reachable (.var "x")] := by
  simp [guardedSucc, elaborateClause, clauseGuards, reachableSucc, HornClause.toFormula, Term.conjunction,
    Term.freeVars, elaborate, elaborateArgs, reachable, succ, dataOf]

def guardedKb : K := insert guardedSucc (insert reachableZero signature)

theorem guardedRule : Derives Symbol.hoApply guardedKb [] (reachable (succ zero)) := by
  have guard := zeroGuard guardedKb (fun _ member => Or.inr (Or.inr member)) []
  have base : Derives Symbol.hoApply guardedKb [] (reachable zero) :=
    .clause (σ := Term.var) (Or.inr (Or.inl rfl)) (Substitutes.identity _) .truth .truth
  have member : HornClause.definite (reachable (succ (.var "x")))
      [rangeGuard snapshot.naming (.data [.nat]) (.var "x"), rangeGuard snapshot.naming (.data [.nat]) (.var "x"),
        reachable (.var "x")] ∈ guardedKb := Or.inl guardedSucc_eq.symm
  have guardInstance := rangeGuard_substitutes snapshot.naming (.data [.nat]) (.singleVar "x" zero)
  have argument : Substitutes (Substitution.single "x" zero) (reachable (.var "x")) (reachable zero) :=
    .app (.cons (.singleVar "x" zero) .nil)
  exact .clause member (.app (.cons (.app (.cons (.singleVar "x" zero) .nil)) .nil))
    (SubstitutesList.conjunction (.cons guardInstance (.cons guardInstance (.cons argument .nil))))
    (.conjIntro guard (.conjIntro guard (.conjIntro base .truth)))

-- All semantic and structural bridges must remain kernel-checked.
open Lean Meta in
run_meta do
  for declaration in [``Elaboration.satisfies, ``eval_elaborate, ``forall_satisfies, ``exists_satisfies,
      ``freeVars, ``elaboration_substitutes, ``opening_substitutes, ``context_fresh,
      ``context_satisfies, ``clause_satisfies, ``forallAll_intro, ``existsRange_intro,
      ``defaultForall, ``rawForallFails, ``predicateForall, ``shadowing, ``falseTemplate,
      ``renamedElaboration, ``emptyQuantifiers, ``overlap, ``carrierExists, ``noPredicateWitness,
      ``elaborate?_eq_some, ``elaborateClause?_eq_some, ``rangeGuard_derives_data,
      ``rangeGuard_derives_predicate, ``rangeGuard_derives_allData, ``models_signatureKb,
      ``signatureValid, ``predicateExistsDerived, ``dataExistsDerived, ``guardedRule] do
    for axiomName in ← collectAxioms declaration do
      unless axiomName ∈ [`propext, `Classical.choice, `Quot.sound] do
        throwError "unexpected axiom in guarded elaboration: {axiomName}"

end ElaborationTests
