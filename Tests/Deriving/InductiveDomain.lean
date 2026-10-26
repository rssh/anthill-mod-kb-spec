import AnthillModKbSpec.Deriving.InductiveDomain

open AnthillModKbSpec.InductiveDomains

namespace InductiveDomainDerivingTests

inductive Natural where
  | zero
  | succ : Natural → Natural
  deriving InductiveDomain

example (value : Natural) :
    Member (InductiveDomain.family (α := Natural)).definitions
      (InductiveDomain.root (α := Natural)) (InductiveDomain.encode value) :=
  InductiveDomain.encode_member value

-- External fields are included in the finite family, and constructor arity
-- and field order are preserved by the encoding.
inductive Binary where
  | leaf : Nat → Binary
  | branch : Binary → Binary → Binary
  deriving InductiveDomain

example : Binary.inductiveDomain.encode0 (.branch (.leaf 2) (.leaf 3)) =
    .node .c1 [Binary.inductiveDomain.encode0 (.leaf 2),
      Binary.inductiveDomain.encode0 (.leaf 3)] := rfl

example (tree : Tree (InductiveDomain.Symbol (α := Binary))) :
    Member (InductiveDomain.family (α := Binary)).definitions
      (InductiveDomain.root (α := Binary)) tree ↔
      ∃ value : Binary, InductiveDomain.encode value = tree :=
  InductiveDomain.member_iff tree

mutual
  inductive EvenTree where
    | leaf
    | node : OddTree → EvenTree
    deriving InductiveDomain
  inductive OddTree where
    | node : EvenTree → OddTree
    deriving InductiveDomain
end

example : EvenTree.inductiveDomain.encode0 (.node (.node .leaf)) =
    .node .c1 [.node .c2 [.node .c0 []]] := rfl

inductive Void where
  deriving InductiveDomain

example (tree : Tree (InductiveDomain.Symbol (α := Void))) :
    ¬ Member (InductiveDomain.family (α := Void)).definitions
      (InductiveDomain.root (α := Void)) tree := by
  intro member
  obtain ⟨value, _⟩ := InductiveDomain.member_complete tree member
  exact nomatch value

deriving instance InductiveDomain for Bool
deriving instance InductiveDomain for Nat

example (value : Bool) : Bool.inductiveDomain.encode0 value =
    if value then .node .c1 [] else .node .c0 [] := by cases value <;> rfl

example : Nat.inductiveDomain.encode0 2 = .node .c1 [.node .c1 [.node .c0 []]] := rfl

private inductive Hidden where
  | base
  | next : Hidden → Hidden
  deriving InductiveDomain

private abbrev hiddenPresentation : InductiveDomain Hidden := inferInstance

structure Payload where
  number : Nat
  flag : Bool
  deriving InductiveDomain

example : Payload.inductiveDomain.encode0 ⟨2, true⟩ =
    .node .c0 [Payload.inductiveDomain.encode1 2, Payload.inductiveDomain.encode2 true] := rfl

inductive ImplicitField where
  | mk {number : Nat} : ImplicitField
  deriving InductiveDomain

example : ImplicitField.inductiveDomain.encode0 (@ImplicitField.mk 2) =
    .node .c0 [ImplicitField.inductiveDomain.encode1 2] := rfl

structure Triple where
  first : Natural
  second : Natural
  third : Natural
  deriving InductiveDomain

example : Triple.inductiveDomain.encode0 ⟨.zero, .succ .zero, .zero⟩ =
    .node .c0 [.node .c1 [], .node .c2 [.node .c1 []], .node .c1 []] := rfl

-- Exactness excludes both wrong constructor arities and symbols belonging to
-- other domains in the family.
example : ¬ Member Binary.inductiveDomain.definitions .d0 (.node .c1 []) := by
  intro member
  obtain ⟨value, same⟩ := Binary.inductiveDomain.complete member
  cases value <;> simp [Binary.inductiveDomain.encode, Binary.inductiveDomain.encode0] at same

example : ¬ Member Payload.inductiveDomain.definitions .d0 (.node .c1 []) := by
  intro member
  obtain ⟨value, same⟩ := Payload.inductiveDomain.complete member
  cases value <;> simp [Payload.inductiveDomain.encode, Payload.inductiveDomain.encode0] at same

example (property : Tree Natural.inductiveDomain.Symbol → Prop)
    (all : ∀ value : Natural, property (InductiveDomain.encode value)) :
    Holds Natural.inductiveDomain.definitions [.d0] property :=
  (InductiveDomain.holds_iff (α := Natural) property).mpr all

inductive Indexed : Nat → Type where
  | zero : Indexed 0

/-- error: InductiveDomain: InductiveDomainDerivingTests.Indexed must be safe, parameter-free, non-indexed first-order data in Type; nested and function-valued recursion are unsupported -/
#guard_msgs in
deriving instance InductiveDomain for Indexed

inductive Parameterized (α : Type) where
  | mk : α → Parameterized α

/-- error: InductiveDomain: InductiveDomainDerivingTests.Parameterized must be safe, parameter-free, non-indexed first-order data in Type; nested and function-valued recursion are unsupported -/
#guard_msgs in
deriving instance InductiveDomain for Parameterized

inductive HigherOrder where
  | leaf
  | branch : (Nat → HigherOrder) → HigherOrder

/-- error: InductiveDomain: InductiveDomainDerivingTests.HigherOrder must be safe, parameter-free, non-indexed first-order data in Type; nested and function-valued recursion are unsupported -/
#guard_msgs in
deriving instance InductiveDomain for HigherOrder

inductive ContainerPayload where
  | mk : List Nat → ContainerPayload

/-- error: InductiveDomain: constructor InductiveDomainDerivingTests.ContainerPayload.mk has an unsupported field type List Nat; expected a parameter-free inductive data type -/
#guard_msgs (whitespace := lax) in
deriving instance InductiveDomain for ContainerPayload

-- Unsupported dependencies must not leave a partial generated package behind.
open Lean Elab Command in
run_cmd do
  for name in [`InductiveDomainDerivingTests.Indexed,
      `InductiveDomainDerivingTests.Parameterized, `InductiveDomainDerivingTests.HigherOrder,
      `InductiveDomainDerivingTests.ContainerPayload] do
    if (← getEnv).contains (name.str "inductiveDomain" |>.str "Domain") then
      throwError "rejected generation left a partial presentation for {name}"

-- Audit the generated proof objects, including mutual recursion and external
-- fields, rather than trusting the metaprogram that proposed them.
open Lean Meta in
run_meta do
  for declaration in [``Natural.inductiveDomain.instance0,
      ``Binary.inductiveDomain.instance0, ``EvenTree.inductiveDomain.instance0,
      ``EvenTree.inductiveDomain.instance1, ``Void.inductiveDomain.instance0,
      ``Bool.inductiveDomain.instance0, ``Nat.inductiveDomain.instance0,
      ``hiddenPresentation, ``Payload.inductiveDomain.instance0,
      ``ImplicitField.inductiveDomain.instance0, ``Triple.inductiveDomain.instance0,
      ``InductiveDomain.holds_iff] do
    for axiomName in ← collectAxioms declaration do
      unless axiomName ∈ [`propext, `Classical.choice, `Quot.sound] do
        throwError "unexpected axiom in generated inductive domain: {axiomName}"

end InductiveDomainDerivingTests
