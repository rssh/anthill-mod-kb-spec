import AnthillModKbSpec.Resolution.DictionaryRegistry
import AnthillModKbSpec.Resolution.P1.Decision
import AnthillModKbSpec.Foundation.EquationOracle

/-! # Dictionary operations by total evaluators (S14)

An operation of a registered dictionary is computed by an evaluator, not by
laws. An evaluator (`Evaluation`) is registered per dictionary operation: the
dictionary's name and version, the operation's path, field, and argument
count, and a Lean function from argument terms to a value term. It is used
only where S13 admits the call: the access is declared (`Registry.access?`),
and the registration states a primitive contract for the operation
(`Primitive`) at the call's argument count. `Snapshot.evaluate` is the
registry's evaluator: it finds the registration, the contract, and the
evaluation for that count, and runs it.

Its claims are evidence, proved, not trusted:

| Claim | Evidence |
| --- | --- |
| Wherever it answers, the answer is the call's value | `Evaluation.Sound`, per interpretation, for each evaluation the registry uses (`Snapshot.Evaluated`) |
| On member trees of the contract's argument domains it answers | `Evaluation.Total`, syntactic |
| Its answers are member trees of the contract's result domain | `Evaluation.Closed`, syntactic |

The evaluated equations are the equation oracle's (`Snapshot.oracle`): a sound
oracle, so the KB they extend keeps its models (`models_evaluated`). An S08
snapshot that lists the evaluator holds exactly that KB (`P1.Snapshot.kb`), so
an evaluation is reconstructed by the clause rule on an evaluated equation
(`P1.Snapshot.evaluated_derives`), and NAF evidence is checked against that same KB.

The route decides the equation `call = result` (`Snapshot.decision`, a P1
`DecisionContract`): for an admitted call, its arguments member trees of the
contract's domains, and a result that is a member tree of the result domain,
Yes when the evaluator's value is the result, and No otherwise. Yes holds in
every interpretation the answers are about (`Snapshot.Models`): realizing the
snapshot, with checked registrations and evaluations, and separating the
members of each contract's result domain (`Snapshot.Separated`: distinct
member trees denote distinct values). No fails in each of them. The decision is a Lean function, so it
terminates; it is complete because an admitted call is always evaluated
(`evaluate_total`). An operation with no contract, no evaluation, or arguments
outside its domains is not admitted: no decision is made, and nothing is
refuted. -/

namespace AnthillModKbSpec.DictionaryRegistry

open Semantics InductiveDomains AdmissionSignature OperationDictionaries

variable {Domain Variable Literal Symbol Value : Type} {hoApplySymbol : Symbol}

/-! ## Registered evaluators -/

/-- An evaluator registered for one operation of one dictionary: the
dictionary's name and version, the operation's path, field, and argument
count, and a function from argument terms to the value term, `none` where it
does not evaluate. -/
structure Evaluation (Variable Literal Symbol : Type) where
  name : Symbol
  version : Nat
  path : List Symbol
  field : Symbol
  arity : Nat
  run : List (Term Variable Literal Symbol) → Option (Term Variable Literal Symbol)

/-- What an evaluated call reaches: the registration, its primitive contract
for the operation, the registered evaluation, and the arguments. -/
structure Target (Domain Variable Literal Symbol : Type) where
  registration : Registration Domain Symbol
  primitive : Primitive Domain Symbol
  evaluation : Evaluation Variable Literal Symbol
  arguments : List (Term Variable Literal Symbol)

section Lookup

variable [DecidableEq Symbol]

/-- The registration's primitive contract for the operation at this path and
field, with this many arguments. -/
def Registration.primitive? (registration : Registration Domain Symbol) (path : List Symbol) (field : Symbol)
    (arity : Nat) : Option (Primitive Domain Symbol) :=
  registration.primitives.find? fun primitive =>
    decide (primitive.path = path ∧ primitive.field = field ∧ primitive.arguments.length = arity)

/-- An evaluation is registered for the registration's operation: its name,
version, path, field, and argument count. A new version of the registration
needs its own, and so does each contract of one operation. -/
def Evaluation.For (evaluation : Evaluation Variable Literal Symbol) (registration : Registration Domain Symbol)
    (path : List Symbol) (field : Symbol) (arity : Nat) : Prop :=
  evaluation.name = registration.name ∧ evaluation.version = registration.version ∧ evaluation.path = path ∧
    evaluation.field = field ∧ evaluation.arity = arity

instance (evaluation : Evaluation Variable Literal Symbol) (registration : Registration Domain Symbol)
    (path : List Symbol) (field : Symbol) (arity : Nat) : Decidable (evaluation.For registration path field arity) := by
  unfold Evaluation.For; infer_instance

/-- The first evaluation registered for the registration's operation at this
argument count. -/
def evaluation? (evaluations : List (Evaluation Variable Literal Symbol)) (registration : Registration Domain Symbol)
    (path : List Symbol) (field : Symbol) (arity : Nat) : Option (Evaluation Variable Literal Symbol) :=
  evaluations.find? fun evaluation => decide (evaluation.For registration path field arity)

/-- The target of a call S13 declares, on a registration with a primitive
contract for the operation at the call's argument count and a registered
evaluation. Any other term has none: an undeclared access, an operation with
no contract (an ordering `compare` in the Nat registry), or one with no
evaluation. -/
def Snapshot.target? (snapshot : Snapshot Domain Variable Literal Symbol)
    (evaluations : List (Evaluation Variable Literal Symbol)) :
    Term Variable Literal Symbol → Option (Target Domain Variable Literal Symbol)
  | .dictionaryCall dictionary path field args =>
      match snapshot.registry.access? .value dictionary path field args.length with
      | .declared registration _ =>
          match registration.primitive? path field args.length,
              evaluation? evaluations registration path field args.length with
          | some primitive, some evaluation => some ⟨registration, primitive, evaluation, args⟩
          | _, _ => none
      | _ => none
  | _ => none

/-- The registry's evaluator: an admitted call's registered evaluation, run on
its arguments. -/
def Snapshot.evaluate (snapshot : Snapshot Domain Variable Literal Symbol)
    (evaluations : List (Evaluation Variable Literal Symbol)) : P1.Evaluator Variable Literal Symbol := fun call =>
  (snapshot.target? evaluations call).bind fun target => target.evaluation.run target.arguments

/-- What a target establishes: the call is a declared access on the
registration's name, with the contract and the evaluation for its operation. -/
theorem Snapshot.target?_spec {snapshot : Snapshot Domain Variable Literal Symbol}
    {evaluations : List (Evaluation Variable Literal Symbol)} {call : Term Variable Literal Symbol}
    {target : Target Domain Variable Literal Symbol} (found : snapshot.target? evaluations call = some target) :
    call = .dictionaryCall (.app target.registration.name []) target.evaluation.path target.evaluation.field
        target.arguments ∧
      target.registration ∈ snapshot.registry.dictionaries ∧ target.primitive ∈ target.registration.primitives ∧
      target.primitive.path = target.evaluation.path ∧ target.primitive.field = target.evaluation.field ∧
      target.evaluation ∈ evaluations ∧
      target.evaluation.For target.registration target.primitive.path target.primitive.field
        target.primitive.arguments.length ∧
      target.primitive.arguments.length = target.arguments.length ∧
      ∃ operation, snapshot.registry.access? .value (.app target.registration.name []) target.evaluation.path
        target.evaluation.field target.arguments.length = .declared target.registration operation := by
  match call, found with
  | .dictionaryCall dictionary path field args, found =>
      simp only [Snapshot.target?] at found
      split at found
      · rename_i registration operation declared
        split at found
        · rename_i primitive evaluation primitiveFound evaluationFound
          cases found
          obtain ⟨_, named, registered, _⟩ := access?_declared declared
          obtain ⟨primitiveMember, samePath, sameField, length⟩ := find?_sound primitiveFound
          obtain ⟨evaluationMember, sameName, sameVersion, pathEq, fieldEq, arityEq⟩ := find?_sound evaluationFound
          subst named pathEq fieldEq
          exact ⟨rfl, registered, primitiveMember, samePath, sameField, evaluationMember,
            ⟨sameName, sameVersion, samePath.symm, sameField.symm, arityEq.trans length.symm⟩, length, _, declared⟩
        · cases found
      · cases found

end Lookup

/-! ## The evidence -/

section Evidence

variable [DecidableEq Symbol] [DecidableEq Variable]

/-- The evaluation computes the call's value: wherever it answers, under every
environment, the operation at the dictionary's value and the arguments' values
is the answer's value. -/
def Evaluation.Sound (interp : Interpretation Literal Symbol Value hoApplySymbol)
    (evaluation : Evaluation Variable Literal Symbol) : Prop :=
  ∀ args value, evaluation.run args = some value → ∀ environment : Environment Variable Value,
    interp.model.dictionaryCall (interp.value evaluation.name) evaluation.path evaluation.field
      (args.map (interp.model.eval environment)) = interp.model.eval environment value

/-- Every evaluation the registry uses is sound in the interpretation: each
registered for a registration's name, version, and primitive contract (its
path, field, and argument count). An evaluation for another version, or for no
contract, is never used and claims nothing. -/
def Snapshot.Evaluated (snapshot : Snapshot Domain Variable Literal Symbol)
    (evaluations : List (Evaluation Variable Literal Symbol))
    (interp : Interpretation Literal Symbol Value hoApplySymbol) : Prop :=
  ∀ registration ∈ snapshot.registry.dictionaries, ∀ primitive ∈ registration.primitives,
    ∀ evaluation ∈ evaluations, evaluation.For registration primitive.path primitive.field primitive.arguments.length →
      evaluation.Sound interp

/-- The evaluation answers on member trees of the contract's argument domains,
with a member tree of its result domain. It reads only the signature. -/
def Evaluation.Total (signature : SignatureSnapshot Domain Symbol) (primitive : Primitive Domain Symbol)
    (evaluation : Evaluation Variable Literal Symbol) : Prop :=
  ∀ trees : List (Tree Symbol), trees.length = primitive.arguments.length →
    (∀ pair ∈ primitive.arguments.zip trees, InductiveDomains.Member signature.signature.data.definitions pair.1 pair.2) →
    ∃ result, InductiveDomains.Member signature.signature.data.definitions primitive.result result ∧
      evaluation.run (trees.map Tree.toTerm) = some result.toTerm

/-- Every answer of the evaluation is a member tree of the contract's result
domain. -/
def Evaluation.Closed (signature : SignatureSnapshot Domain Symbol) (primitive : Primitive Domain Symbol)
    (evaluation : Evaluation Variable Literal Symbol) : Prop :=
  ∀ args value, evaluation.run args = some value →
    ∃ result, InductiveDomains.Member signature.signature.data.definitions primitive.result result ∧
      value = result.toTerm

/-- The syntactic evidence of an evaluation for a contract. -/
structure Evaluation.Admitted (signature : SignatureSnapshot Domain Symbol) (primitive : Primitive Domain Symbol)
    (evaluation : Evaluation Variable Literal Symbol) : Prop where
  total : evaluation.Total signature primitive
  closed : evaluation.Closed signature primitive

/-- Every evaluation registered for an operation with a contract is total on
the contract's domains and closed in its result domain. -/
def Snapshot.Complete (snapshot : Snapshot Domain Variable Literal Symbol)
    (evaluations : List (Evaluation Variable Literal Symbol)) : Prop :=
  ∀ registration ∈ snapshot.registry.dictionaries, ∀ primitive ∈ registration.primitives,
    ∀ evaluation ∈ evaluations, evaluation.For registration primitive.path primitive.field primitive.arguments.length →
      evaluation.Admitted snapshot.signature primitive

/-- Distinct member trees of a primitive contract's result domain denote
distinct values. Only result domains are asked: a No compares two values there.
The order model separates Bool; a model identifying `true` and `false` would
not, and there `less(natOrd, 2, 3) = false` would hold. -/
def Snapshot.Separated (snapshot : Snapshot Domain Variable Literal Symbol)
    (interp : Interpretation Literal Symbol Value hoApplySymbol) : Prop :=
  ∀ registration ∈ snapshot.registry.dictionaries, ∀ primitive ∈ registration.primitives, ∀ first second,
    InductiveDomains.Member snapshot.signature.signature.data.definitions primitive.result first →
    InductiveDomains.Member snapshot.signature.signature.data.definitions primitive.result second →
    denote interp.model first = denote interp.model second → first = second

/-- The interpretations the route's answers are about: realizing the snapshot,
with checked registrations and evaluations, separating the members of each
contract's result domain. -/
structure Snapshot.Models (snapshot : Snapshot Domain Variable Literal Symbol)
    (evaluations : List (Evaluation Variable Literal Symbol)) (interp : Interpretation Literal Symbol Value hoApplySymbol) :
    Prop where
  realizes : snapshot.Realizes interp
  checked : snapshot.Checked interp
  evaluated : snapshot.Evaluated evaluations interp
  separated : snapshot.Separated interp

end Evidence

/-! ## Soundness and totality -/

section Evaluate

variable [DecidableEq Symbol] [DecidableEq Variable] {snapshot : Snapshot Domain Variable Literal Symbol}
  {evaluations : List (Evaluation Variable Literal Symbol)}

omit [DecidableEq Variable] in
theorem Snapshot.evaluate_some {call value : Term Variable Literal Symbol}
    (found : snapshot.evaluate evaluations call = some value) :
    ∃ target, snapshot.target? evaluations call = some target ∧ target.evaluation.run target.arguments = some value := by
  simp only [Snapshot.evaluate, Option.bind_eq_some_iff] at found
  exact found

theorem eval_name (interp : Interpretation Literal Symbol Value hoApplySymbol) (environment : Environment Variable Value)
    (name : Symbol) : interp.model.eval environment (.app name [] : Term Variable Literal Symbol) = interp.value name := by
  simp [Model.eval, Interpretation.value]

/-- An evaluated call has the evaluation's value, under every environment. -/
theorem Snapshot.evaluate_sound {interp : Interpretation Literal Symbol Value hoApplySymbol}
    (evaluated : snapshot.Evaluated evaluations interp) {call value : Term Variable Literal Symbol}
    (found : snapshot.evaluate evaluations call = some value) (environment : Environment Variable Value) :
    interp.model.eval environment call = interp.model.eval environment value := by
  obtain ⟨target, targeted, ran⟩ := Snapshot.evaluate_some found
  obtain ⟨rfl, registered, primitiveMember, _, _, member, matching, _⟩ := Snapshot.target?_spec targeted
  have named := matching.1
  have sound := evaluated target.registration registered target.primitive primitiveMember target.evaluation member
    matching target.arguments value ran environment
  rw [named] at sound
  simp only [Model.eval, eval_name] at sound ⊢
  exact sound

omit [DecidableEq Variable] in
/-- An evaluated value is a member tree of the contract's result domain. -/
theorem Snapshot.evaluate_member (complete : snapshot.Complete evaluations) {call value : Term Variable Literal Symbol}
    (found : snapshot.evaluate evaluations call = some value) :
    ∃ target result, snapshot.target? evaluations call = some target ∧
      InductiveDomains.Member snapshot.signature.signature.data.definitions target.primitive.result result ∧
      value = result.toTerm := by
  obtain ⟨target, targeted, ran⟩ := Snapshot.evaluate_some found
  obtain ⟨_, registered, primitiveMember, _, _, member, matching, _⟩ := Snapshot.target?_spec targeted
  have admitted := complete target.registration registered target.primitive primitiveMember target.evaluation member
    matching
  obtain ⟨result, inside, rfl⟩ := admitted.closed _ _ ran
  exact ⟨target, result, targeted, inside, rfl⟩

omit [DecidableEq Variable] in
/-- Totality: an admitted call whose arguments are member trees of the
contract's argument domains is evaluated, to a member tree of the result
domain. -/
theorem Snapshot.evaluate_total (complete : snapshot.Complete evaluations) {call : Term Variable Literal Symbol}
    {target : Target Domain Variable Literal Symbol} (targeted : snapshot.target? evaluations call = some target)
    {trees : List (Tree Symbol)} (arguments : target.arguments = trees.map Tree.toTerm)
    (members : ∀ pair ∈ target.primitive.arguments.zip trees,
      InductiveDomains.Member snapshot.signature.signature.data.definitions pair.1 pair.2) :
    ∃ result, InductiveDomains.Member snapshot.signature.signature.data.definitions target.primitive.result result ∧
      snapshot.evaluate evaluations call = some result.toTerm := by
  obtain ⟨_, registered, primitiveMember, _, _, member, matching, length, _⟩ :=
    Snapshot.target?_spec targeted
  have admitted := complete target.registration registered target.primitive primitiveMember target.evaluation member
    matching
  have lengthTrees : trees.length = target.primitive.arguments.length := by
    rw [length, arguments, List.length_map]
  obtain ⟨result, inside, ran⟩ := admitted.total trees lengthTrees members
  refine ⟨result, inside, ?_⟩
  simp only [Snapshot.evaluate, targeted, Option.bind_some, arguments, ran]

end Evaluate

/-! ## The evaluated equations as an equation oracle -/

section Oracle

variable [DecidableEq Symbol] [DecidableEq Variable] (snapshot : Snapshot Domain Variable Literal Symbol)
  (evaluations : List (Evaluation Variable Literal Symbol))

/-- The evaluated equations as a sound equation oracle: unconditional, each an
evaluation of the registry's evaluator. -/
def Snapshot.oracle {interp : Interpretation Literal Symbol Value hoApplySymbol}
    (evaluated : snapshot.Evaluated evaluations interp) :
    EquationOracle interp.model Variable where
  certifies body left right := body = [] ∧ snapshot.evaluate evaluations left = some right
  sound := by
    rintro body left right ⟨rfl, found⟩ environment _
    exact Snapshot.evaluate_sound evaluated found environment

/-- The S08 snapshot over clauses with the registry's evaluator: its KB is the
clauses and the evaluated equations, the oracle's extension. -/
def Snapshot.checkSnapshot (hoApplySymbol : Symbol) (clauses : List (HornClause Variable Literal Symbol)) :
    P1.Snapshot Variable Literal Symbol :=
  ⟨hoApplySymbol, clauses, [snapshot.evaluate evaluations]⟩

theorem Snapshot.checkSnapshot_kb {interp : Interpretation Literal Symbol Value hoApplySymbol}
    (evaluated : snapshot.Evaluated evaluations interp) (clauses : List (HornClause Variable Literal Symbol)) :
    (snapshot.checkSnapshot evaluations hoApplySymbol clauses).kb =
      (snapshot.oracle evaluations evaluated).extend fun clause => clause ∈ clauses := by
  funext clause
  apply propext
  constructor
  · rintro (listed | ⟨call, value, ⟨evaluator, member, found⟩, rfl⟩)
    · exact Or.inl listed
    · simp only [Snapshot.checkSnapshot, List.mem_singleton] at member
      subst member
      exact Or.inr ⟨call, value, [], ⟨rfl, found⟩, rfl⟩
  · rintro (listed | ⟨call, value, body, ⟨rfl, found⟩, rfl⟩)
    · exact Or.inl listed
    · exact Or.inr ⟨call, value, ⟨_, List.mem_singleton_self _, found⟩, rfl⟩

/-- A model of the clauses, with sound evaluations, is a model of the KB with
the evaluated equations. -/
theorem Snapshot.models_evaluated {interp : Interpretation Literal Symbol Value hoApplySymbol}
    (evaluated : snapshot.Evaluated evaluations interp) {clauses : List (HornClause Variable Literal Symbol)}
    (models : interp.model.Models fun clause => clause ∈ clauses) :
    interp.model.Models (snapshot.checkSnapshot evaluations hoApplySymbol clauses).kb := by
  rw [snapshot.checkSnapshot_kb evaluations evaluated]
  exact (snapshot.oracle evaluations evaluated).models_extension models


end Oracle

/-! ## The decision -/

section Decision

variable [DecidableEq Symbol] [DecidableEq Variable] [DecidableEq Literal]

/-- An equation the route decides: an operation term and a value term. -/
structure Equation (Variable Literal Symbol : Type) where
  call : Term Variable Literal Symbol
  result : Term Variable Literal Symbol

/-- An admitted equation: the call has a target, its arguments are member trees
of the contract's argument domains, and the result is a member tree of the
contract's result domain. -/
def Snapshot.Decides (snapshot : Snapshot Domain Variable Literal Symbol)
    (evaluations : List (Evaluation Variable Literal Symbol)) (equation : Equation Variable Literal Symbol) : Prop :=
  ∃ target trees result, snapshot.target? evaluations equation.call = some target ∧
    target.arguments = trees.map Tree.toTerm ∧
    (∀ pair ∈ target.primitive.arguments.zip trees,
      InductiveDomains.Member snapshot.signature.signature.data.definitions pair.1 pair.2) ∧
    InductiveDomains.Member snapshot.signature.signature.data.definitions target.primitive.result result ∧
    equation.result = result.toTerm

/-- The decision: the evaluator's value is the result. -/
def Snapshot.decide (snapshot : Snapshot Domain Variable Literal Symbol)
    (evaluations : List (Evaluation Variable Literal Symbol)) (equation : Equation Variable Literal Symbol) : Bool :=
  match snapshot.evaluate evaluations equation.call with
  | some value => Machine.identical value equation.result
  | none => false

theorem Snapshot.decide_found {snapshot : Snapshot Domain Variable Literal Symbol}
    {evaluations : List (Evaluation Variable Literal Symbol)} {equation : Equation Variable Literal Symbol}
    (decided : snapshot.decide evaluations equation = true) :
    snapshot.evaluate evaluations equation.call = some equation.result := by
  unfold Snapshot.decide at decided
  split at decided
  · rename_i value found
    rw [Machine.identical_iff.mp decided] at found
    exact found
  · cases decided

/-- A Yes: the call's value is the result's, under every environment, in every
interpretation whose evaluations are sound. -/
theorem Snapshot.decide_sound {snapshot : Snapshot Domain Variable Literal Symbol}
    {evaluations : List (Evaluation Variable Literal Symbol)} {equation : Equation Variable Literal Symbol}
    (decided : snapshot.decide evaluations equation = true) {interp : Interpretation Literal Symbol Value hoApplySymbol}
    (evaluated : snapshot.Evaluated evaluations interp) (environment : Environment Variable Value) :
    interp.model.eval environment equation.call = interp.model.eval environment equation.result :=
  Snapshot.evaluate_sound evaluated (Snapshot.decide_found decided) environment

omit [DecidableEq Variable] [DecidableEq Literal] in
/-- Two different member trees of a target's result domain denote different
values: a No compares them. -/
theorem Snapshot.separates {snapshot : Snapshot Domain Variable Literal Symbol}
    {evaluations : List (Evaluation Variable Literal Symbol)} {call : Term Variable Literal Symbol}
    {target : Target Domain Variable Literal Symbol} (targeted : snapshot.target? evaluations call = some target)
    {interp : Interpretation Literal Symbol Value hoApplySymbol} (separated : snapshot.Separated interp)
    {first second : Tree Symbol}
    (firstMember : InductiveDomains.Member snapshot.signature.signature.data.definitions target.primitive.result first)
    (secondMember : InductiveDomains.Member snapshot.signature.signature.data.definitions target.primitive.result second)
    (different : first ≠ second) : denote interp.model first ≠ denote interp.model second := by
  obtain ⟨_, registered, primitiveMember, _⟩ := Snapshot.target?_spec targeted
  exact fun same => different (separated _ registered _ primitiveMember _ _ firstMember secondMember same)

/-- The dictionary operation/equality route as a P1 decision contract, for an
interpretation the answers are about: Yes, the call's value is the result's
under every environment; No, it differs under every environment. The decision
is total and covers every admitted equation (`Snapshot.Decides`): the
evaluator always answers an admitted call (`evaluate_total`). -/
def Snapshot.decision (snapshot : Snapshot Domain Variable Literal Symbol)
    (evaluations : List (Evaluation Variable Literal Symbol)) (complete : snapshot.Complete evaluations)
    (interp : Interpretation Literal Symbol Value hoApplySymbol) (models : snapshot.Models evaluations interp) :
    P1.DecisionContract (Equation Variable Literal Symbol) where
  problem equation := ∀ environment : Environment Variable Value,
    interp.model.eval environment equation.call = interp.model.eval environment equation.result
  negative equation := ∀ environment : Environment Variable Value,
    interp.model.eval environment equation.call ≠ interp.model.eval environment equation.result
  excludes _ negative holds := negative (fun _ => interp.invalid) (holds _)
  conditions := snapshot.Decides evaluations
  decide := snapshot.decide evaluations
  yes _ _ decided := Snapshot.decide_sound decided models.evaluated
  no equation admitted decided environment same := by
    obtain ⟨target, trees, result, targeted, arguments, members, inside, resultEq⟩ := admitted
    obtain ⟨value, valueInside, found⟩ := Snapshot.evaluate_total complete targeted arguments members
    unfold Snapshot.decide at decided
    rw [found] at decided
    simp only at decided
    have different : value ≠ result := fun equal => by
      rw [equal, resultEq, Machine.identical_self] at decided
      cases decided
    rw [Snapshot.evaluate_sound models.evaluated found environment, resultEq, Tree.eval_toTerm,
      Tree.eval_toTerm] at same
    exact Snapshot.separates targeted models.separated valueInside inside different same

/-- A Yes is derived in the KB with the evaluated equations, by the clause
rule: no evaluator callback is trusted beyond its registration in the KB. -/
theorem Snapshot.decide_derives {snapshot : Snapshot Domain Variable Literal Symbol}
    {evaluations : List (Evaluation Variable Literal Symbol)} {equation : Equation Variable Literal Symbol}
    (decided : snapshot.decide evaluations equation = true) (clauses : List (HornClause Variable Literal Symbol))
    (context : ProofContext Variable Literal Symbol) (naf : NafFailure Variable Literal Symbol) :
    Derives hoApplySymbol (snapshot.checkSnapshot evaluations hoApplySymbol clauses).kb context
      (.equal equation.call equation.result) naf :=
  P1.Snapshot.evaluated_derives (snapshot := snapshot.checkSnapshot evaluations hoApplySymbol clauses)
    ⟨_, List.mem_singleton_self _, Snapshot.decide_found decided⟩

/-- A No fails in every interpretation the answers are about. -/
theorem Snapshot.decide_refutes {snapshot : Snapshot Domain Variable Literal Symbol}
    {evaluations : List (Evaluation Variable Literal Symbol)} (complete : snapshot.Complete evaluations)
    {equation : Equation Variable Literal Symbol} (admitted : snapshot.Decides evaluations equation)
    (decided : snapshot.decide evaluations equation = false) {interp : Interpretation Literal Symbol Value hoApplySymbol}
    (models : snapshot.Models evaluations interp) (environment : Environment Variable Value) :
    ¬ interp.model.Satisfies environment (.equal equation.call equation.result) := by
  rw [Model.satisfies_equal]
  exact (snapshot.decision evaluations complete interp models).no equation admitted decided environment

end Decision

end AnthillModKbSpec.DictionaryRegistry
