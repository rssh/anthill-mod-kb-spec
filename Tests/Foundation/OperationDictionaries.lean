import AnthillModKbSpec.Foundation.OperationDictionaries
import AnthillModKbSpec.Foundation.ClauseInstantiation
import AnthillModKbSpec.Resolution.Miller

open AnthillModKbSpec
open AnthillModKbSpec.OperationDictionaries

namespace OperationDictionaryTests

inductive Symbol where
  | zero | succ | member | hoApply | required | nat
  deriving DecidableEq

abbrev Field := Symbol

/-- A free carrier witnesses that references and zero-argument results can differ.
All atomic applications are false in this witness; intended arithmetic is not
needed for testing the dictionary contract. -/
inductive Value where
  | node : Symbol → List Value → Value
  | reference : Symbol → Value
  | callable : Entry Symbol Value → Value
  | dictionary : List (Field × Value) → Value
  | proposition : Prop → Value

def holds : Value → Prop
  | .proposition p => p
  | _ => False

/-- Encoding the finite dictionary tree in the shared value carrier. -/
def encode (node : Node Field Symbol Value) : Value := match node with
  | .callable entry => .callable entry
  | .subdictionary entries =>
    .dictionary (entries.map (fun pair => (pair.1, encode pair.2)))
termination_by sizeOf node
decreasing_by
  have smaller := List.sizeOf_lt_of_mem (by assumption)
  cases pair
  simp_all only [Prod.mk.sizeOf_spec, Node.subdictionary.sizeOf_spec]
  omega

def decode (value : Value) : Node Field Symbol Value := match value with
  | .callable entry => .callable entry
  | .dictionary entries =>
    .subdictionary (entries.map (fun pair => (pair.1, decode pair.2)))
  | _ => .callable ⟨.operation, .zero, []⟩
termination_by sizeOf value
decreasing_by
  have smaller := List.sizeOf_lt_of_mem (by assumption)
  cases pair
  simp_all only [Prod.mk.sizeOf_spec, Value.dictionary.sizeOf_spec]
  omega

theorem decode_encode (node : Node Field Symbol Value) : decode (encode node) = node := by
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

def model : Semantics.Model Unit Symbol Value .hoApply where
  inhabitant := .node .zero []
  literal := fun _ => .node .zero []
  application := Value.node
  holds := holds
  top := .proposition True
  bottom := .proposition False
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
  holds_hoApply := fun _ _ => Iff.rfl

def extension : Extension model Field where
  roleOf := fun | .member => .predicate | _ => .operation
  reference := Value.reference
  call := fun value args => match value with
    | .reference symbol => .node symbol args
    | _ => .node .hoApply (value :: args)
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

@[simp] theorem project_dictionary (entries : Dictionary Field Symbol Value) (field : Field) :
    extension.project (extension.dictionary entries) field = lookup entries field :=
  extension.project_dictionary entries field

@[simp] theorem roleOf (symbol : Symbol) : extension.roleOf symbol =
    (match symbol with | .member => .predicate | _ => .operation) := rfl

def natDictionary : Dictionary Field Symbol Value :=
  [(.zero, .callable ⟨.operation, .zero, []⟩),
   (.succ, .callable ⟨.operation, .succ, []⟩),
   (.member, .callable ⟨.predicate, .member, []⟩)]

example : extension.reference .zero ≠ model.application .zero [] := by
  intro impossible
  cases impossible

example : extension.lookupAs (extension.dictionary natDictionary) .succ .operation =
    some ⟨.operation, .succ, []⟩ := by
  simp [Extension.lookupAs, natDictionary, lookup]

example : extension.lookupAs (extension.dictionary natDictionary) .member .operation = none := by
  simp [Extension.lookupAs, natDictionary, lookup]

-- A forged tag does not turn an operation into a predicate.
example : extension.lookupAs
    (extension.dictionary [(.member, .callable ⟨.predicate, .succ, []⟩)]) .member .predicate = none := by
  simp [Extension.lookupAs, lookup]

-- Captured values are prepended to the explicit arguments.
example (captured argument : Value) :
    extension.invoke ⟨.operation, .succ, [captured]⟩ [argument] =
      model.application .succ [captured, argument] := rfl

-- Equality holds inside data contexts, not merely after taking truth.
example (argument : Value) :
    model.application .member [extension.call (extension.reference .succ) [argument]] =
      model.application .member [model.application .succ [argument]] :=
  extension.call_in_context (fun value => model.application .member [value]) .succ [argument]

-- Duplicate names have a specified, deterministic meaning.
example : lookup ([(.zero, .callable ⟨.operation, .zero, []⟩),
    (.zero, .callable ⟨.operation, .succ, []⟩)] : Dictionary Field Symbol Value) .zero =
      some (.callable ⟨.operation, .zero, []⟩) := rfl

def natInterface : Interface Field Value :=
  .mk [(.zero, .operation), (.succ, .operation), (.member, .predicate)] []
    (fun dictionary =>
    ∃ entry, extension.lookupAs dictionary .zero .operation = some entry ∧
      extension.invoke entry [] = model.application .zero [])

theorem nat_implements : Implements extension (extension.dictionary natDictionary) natInterface := by
  unfold natInterface
  rw [Implements]
  constructor
  · intro field role member
    simp only [List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [Extension.lookupAs, natDictionary, lookup]
  · refine ⟨by simp, ⟨⟨.operation, .zero, []⟩, ?_, rfl⟩⟩
    simp [Extension.lookupAs, natDictionary, lookup]

-- A required-model subtree can itself contain other model dictionaries.
def parentDictionary : Dictionary Field Symbol Value :=
  [(.required, .subdictionary [(.nat, .subdictionary natDictionary)])]

def parentInterface : Interface Field Value :=
  .mk [] [(.required, .mk [] [(.nat, natInterface)] (fun _ => True))] (fun _ => True)

example : extension.atPath (extension.dictionary parentDictionary) [.required, .nat] =
    some (extension.dictionary natDictionary) := by
  simp [Extension.atPath, Extension.subdictionary, parentDictionary, lookup]

example : extension.lookupPathAs (extension.dictionary parentDictionary)
    [.required, .nat] .succ .operation = some ⟨.operation, .succ, []⟩ := by
  simp [Extension.lookupPathAs, Extension.atPath, Extension.subdictionary,
    Extension.lookupAs, parentDictionary, natDictionary, lookup]

-- Calling the projected operation agrees with its direct interpretation.
example (argument : Value) :
    (extension.lookupPathAs (extension.dictionary parentDictionary)
      [.required, .nat] .succ .operation).map (fun entry => extension.invoke entry [argument]) =
      some (model.application .succ [argument]) := by
  simp [Extension.lookupPathAs, Extension.atPath, Extension.subdictionary,
    Extension.lookupAs, parentDictionary, natDictionary, lookup]
  rfl

-- Subdictionaries are not callable leaves, and callable leaves are not models.
example : extension.lookupAs (extension.dictionary parentDictionary) .required .operation = none := by
  simp [Extension.lookupAs, parentDictionary, lookup]

example : extension.subdictionary (extension.dictionary natDictionary) .succ = none := by
  simp [Extension.subdictionary, natDictionary, lookup]

-- Paths fail at missing fields, at callable leaves, and do not search siblings.
example : extension.atPath (extension.dictionary parentDictionary) [.required, .succ] = none := by
  simp [Extension.atPath, Extension.subdictionary, parentDictionary, lookup]

example : extension.atPath (extension.dictionary natDictionary) [.succ] = none := by
  simp [Extension.atPath, Extension.subdictionary, natDictionary, lookup]

-- First-field shadowing applies to subdictionary lookup too.
example : extension.subdictionary (extension.dictionary
    [(.nat, .callable ⟨.operation, .zero, []⟩), (.nat, .subdictionary natDictionary)]) .nat =
      none := by
  simp [Extension.subdictionary, lookup]

example : Implements extension (extension.dictionary parentDictionary) parentInterface := by
  unfold parentInterface
  rw [Implements]
  refine ⟨by simp, ?_, True.intro⟩
  intro field childInterface member
  simp only [List.mem_singleton, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩
  refine ⟨extension.dictionary [(.nat, .subdictionary natDictionary)],
    by simp [Extension.subdictionary, parentDictionary, lookup], ?_⟩
  rw [Implements]
  refine ⟨by simp, ?_, True.intro⟩
  intro field childInterface member
  simp only [List.mem_singleton, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩
  exact ⟨extension.dictionary natDictionary,
    by simp [Extension.subdictionary, lookup], nat_implements⟩

-- A parent fails its interface when a required child has a forged role tag.
example : ¬ Implements extension
    (extension.dictionary [(.nat, .subdictionary
      [(.member, .callable ⟨.predicate, .succ, []⟩)])])
    (.mk [] [(.nat, .mk [(.member, .predicate)] [] (fun _ => True))] (fun _ => True)) := by
  intro valid
  rw [Implements] at valid
  obtain ⟨child, projected, childValid⟩ := valid.2.1 .nat
    (.mk [(.member, .predicate)] [] (fun _ => True)) (by simp)
  simp only [Extension.subdictionary, project_dictionary, lookup, ↓reduceIte,
    bind, Option.bind, Option.some.injEq] at projected
  subst child
  rw [Implements] at childValid
  obtain ⟨entry, found⟩ := childValid.1 .member .predicate (by simp)
  simp [Extension.lookupAs, lookup] at found

-- Required-model validation includes the child's laws, not just its field tags.
example : ¬ Implements extension (extension.dictionary parentDictionary)
    (.mk [] [(.required, .mk [] [] (fun _ => False))] (fun _ => True)) := by
  intro valid
  obtain ⟨child, _, childValid⟩ := Implements.required_model extension valid .required
    (.mk [] [] (fun _ => False)) (by simp)
  rw [Implements] at childValid
  exact childValid.2.2

abbrev T := Term String Unit Symbol

def operationCall : T :=
  .dictionaryCall (.var "D") [.required, .nat] .succ [.var "x"]

def dictionaryModel := extension.withDictionaryCalls model.bottom

def environment : Semantics.Environment String Value := fun name =>
  if name = "D" then extension.dictionary parentDictionary else model.application .zero []

-- A syntactic call evaluates through nested model dictionaries to a data value.
theorem call_evaluates : dictionaryModel.eval environment operationCall =
    model.application .succ [model.application .zero []] := by
  have evaluated := extension.eval_dictionaryCall model.bottom environment
    (.var "D" : T) [.required, .nat] .succ [.var "x"] ⟨.operation, .succ, []⟩
    (by simp [Semantics.Model.eval, environment, Extension.lookupPathAs,
      Extension.atPath, Extension.subdictionary, Extension.lookupAs,
      parentDictionary, natDictionary, lookup])
  simpa [dictionaryModel, operationCall, Semantics.Model.eval, environment] using evaluated

-- The syntax asks for an operation: a predicate leaf yields the chosen invalid value.
example : dictionaryModel.eval environment
    (.dictionaryCall (.var "D") [.required, .nat] .member [] : T) = model.bottom := by
  simp [dictionaryModel, Semantics.Model.eval, Extension.withDictionaryCalls,
    environment, Extension.lookupPathAs, Extension.atPath, Extension.subdictionary,
    Extension.lookupAs, parentDictionary, natDictionary, lookup]

-- The result can occur inside ordinary application arguments.
example : dictionaryModel.eval environment (.app .member [operationCall]) =
    model.application .member [model.application .succ [model.application .zero []]] := by
  rw [Semantics.Model.eval]
  change model.application .member [dictionaryModel.eval environment operationCall] = _
  rw [call_evaluates]

example : operationCall.freeVars = ["D", "x"] := by simp [operationCall, Term.freeVars]

example : (Term.forallVar "x" operationCall).freeVars = ["D"] := by
  simp [operationCall, Term.freeVars]

example : operationCall.openFree "x" "rigid" =
    .dictionaryCall (.var "D") [.required, .nat] .succ [.var "rigid"] := by
  simp [operationCall, Term.openFree]

-- Substitution traverses both the dictionary expression and the arguments.
example : operationCall.instantiate? (fun name => if name = "D" then .var "E" else .app .zero []) =
    some (.dictionaryCall (.var "E") [.required, .nat] .succ [.app .zero []]) := by
  simp [operationCall, Term.instantiate?, List.mapM_cons]

-- Capture checks see dictionary variables under binders too.
example : (Term.forallVar "y" operationCall).instantiate?
    (Substitution.single "D" (.var "y")) = none := by
  simp [operationCall, Term.instantiate?, Term.freeVars, Substitution.single, Substitution.bind]

-- Miller checking reaches inside dictionary expressions and call arguments.
example : ¬ (Term.dictionaryCall (.hoApply .hoApply (.var "P") [.lit ()]) [] .succ [] : T).IsMiller
    .hoApply := by
  simp [Term.IsMiller, Term.MillerHead, Term.hoApply, IsMillerArguments,
    Term.variableName?, List.filterMap]

-- Soundness still covers quantified formulas containing dictionary calls.
def callBody : T := .imp (.app .member [operationCall]) (.app .member [operationCall])

theorem call_reflexivity : Derives .hoApply (∅ : LogicalKb String Unit Symbol) []
    (.forallVar "x" callBody) := by
  apply Derives.forallIntro (eigen := "rigid")
    (opened := callBody.openFree "x" "rigid")
  · intro assumption member; cases member
  · simp [callBody, operationCall, Term.freeVars]
  · exact callBody.openFree_substitutes "x" "rigid" (by
      simp [callBody, operationCall, Term.binderNames])
  · simp only [callBody, Term.openFree]
    exact .impIntro (.assumption (by simp))

example : dictionaryModel.Satisfies environment (.forallVar "x" callBody) :=
  dictionaryModel.positive_sound (by intro clause member; cases member) call_reflexivity
    environment (by intro assumption member; cases member)

end OperationDictionaryTests
