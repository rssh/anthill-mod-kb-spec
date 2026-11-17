import AnthillModKbSpec.Resolution.DictionaryRegistry
import AnthillModKbSpec.Resolution.P1.Lemma
import AnthillModKbSpec.Resolution.Machine.Dictionary

/-! # Dictionary laws as checked lemmas (S14)

A law of an interface is a statement: `∀d. I(d) → body` (`Law.formula`),
valid in every realizing interpretation with checked registrations
(`law_valid`). It is not a clause of the executable program and adds no
inference rule. It is used only as a checked lemma (S20), through its
**conditional views**.

**The law in the proof layer.** The law's formula is a fact of the proof
layer's KB (`Law.clause`, a compound head with no body), true where the law is
valid (`models_lawClauses`). The executable program never selects it: compound
heads are matched only when explicitly chosen (S11), and the law is not among
the program's clauses.

**Its views.** A law compiles into conditional views (`Law.views`): its
universal binders, the dictionary's first; its premises in order, the
interface guard `I(d)` first, then the guards and premises of its body; and a
conclusion, one view per conjunct of a conjunctive body. Asymmetry has one
view, read as a conditional rule:

```text
less(d,y,x) = false :- OrdDictionary(d), DomainMember(d,x), DomainMember(d,y), less(d,x,y) = true
```

as the statement `∀d x y. (OrdDictionary(d) ∧ DomainMember(d,x) ∧
DomainMember(d,y) ∧ less(d,x,y) = true ∧ true) → less(d,y,x) = false`. A
symmetric law (`less(d,x,y) = true ↔ compare(d,x,y) = lt`) has two views, one
per direction, each a separate lemma used only if offered: nothing rewrites
with either, and a run offered both may loop and is interrupted, never Yes.

**Its proof.** A view's proof (`View.proof`) introduces its binders at
themselves, assumes its premises, and replays the law: the law's clause, then
universal eliminations at the binders, implication eliminations against the
assumed premises, and conjunct projections. Every step is a shared S08 rule:
compilation keeps the law's own proof and reconstructs each use by
instantiation and implication elimination. The proof is checked by the run's
checker like any lemma (`lemmasFor`), so a view is offered only where the
checker's KB holds the law's clause.

**Use.** S20 backchains on the view (`lemmaRule`): its conclusion is matched
against the goal (structural matching of the dictionary call, dictionary and
arguments assigned as first-order names, no higher-order unification), and its
premises become the run's obligations, in order: `OrdDictionary(d)`, both
`DomainMember` guards, then `less(d,x,y) = true`. The goal closes once they
all succeed; a failed candidate is rolled back.

**What is missing.** For an equation goal on a dictionary operation, the laws
that may conclude it are those with a view whose conclusion applies the same
operation, its other side not a different closed term (`Registry.lawsFor`): a
goal needing such a view with no checked lemma is Undecided, naming the law
(`DictionaryRoute`). A view concludes with the call on the left, as the
registry's laws do; a goal with the call on the right is turned around first. -/

namespace AnthillModKbSpec.DictionaryRegistry

open Semantics InductiveDomains AdmissionSignature P1 Machine

variable {Domain Variable Literal Symbol Value : Type} {hoApplySymbol : Symbol}

/-! ## The law in the proof layer -/

/-- The law as a fact of the proof layer: its guarded formula, a compound head
with no body. -/
def Law.clause (interface : Interface Variable Literal Symbol) (law : Law Variable Literal Symbol) :
    HornClause Variable Literal Symbol :=
  .definite (law.formula interface) []

/-- The facts of every interface's laws. -/
def Registry.lawClauses (registry : Registry Domain Variable Literal Symbol) : List (HornClause Variable Literal Symbol) :=
  registry.interfaces.flatMap fun interface => interface.laws.map (Law.clause interface)

/-- A realizing interpretation with checked registrations satisfies the laws'
facts: each states a valid law. -/
theorem models_lawClauses [DecidableEq Symbol] [DecidableEq Variable] {snapshot : Snapshot Domain Variable Literal Symbol}
    {interp : Interpretation Literal Symbol Value hoApplySymbol} (realizes : snapshot.Realizes interp)
    (checked : snapshot.Checked interp) (wellFormed : snapshot.WellFormed) :
    interp.model.Models fun clause => clause ∈ snapshot.registry.lawClauses := by
  intro clause member environment
  obtain ⟨interface, declared, inside⟩ := List.mem_flatMap.mp member
  obtain ⟨law, stated, rfl⟩ := List.mem_map.mp inside
  simp only [Law.clause, HornClause.toFormula, Term.conjunction, List.foldr_nil, Model.Satisfies, Model.eval,
    interp.model.holds_implication]
  exact fun _ => law_valid realizes checked wellFormed declared stated environment

/-! ## Views -/

/-- A step deriving a view's conclusion from its law: eliminate a universal at
its own binder, discharge an implication's premise by the view's premise at
`index`, or take a conjunct. -/
inductive ViewStep (Variable : Type) where
  | eliminate (binder : Variable)
  | discharge (index : Nat)
  | left
  | right
  deriving DecidableEq, Repr

/-- A conditional view of a law: its binders, its premises in order, its
conclusion, and the steps deriving the conclusion from the law. -/
structure View (Variable Literal Symbol : Type) where
  binders : List Variable
  premises : List (Formula Variable Literal Symbol)
  conclusion : Formula Variable Literal Symbol
  steps : List (ViewStep Variable)

/-- The views of a formula reached after `binders`, `premises`, and `steps`:
a universal adds its binder, an implication its premise, a conjunction one
view per conjunct, and any other formula is a conclusion. -/
def viewsOf : List Variable → List (Formula Variable Literal Symbol) → List (ViewStep Variable) →
    Formula Variable Literal Symbol → List (View Variable Literal Symbol)
  | binders, premises, steps, .forallVar binder body =>
      viewsOf (binders ++ [binder]) premises (steps ++ [.eliminate binder]) body
  | binders, premises, steps, .imp premise rest =>
      viewsOf binders (premises ++ [premise]) (steps ++ [.discharge premises.length]) rest
  | binders, premises, steps, .conj left right =>
      viewsOf binders premises (steps ++ [.left]) left ++ viewsOf binders premises (steps ++ [.right]) right
  | binders, premises, steps, conclusion => [⟨binders, premises, conclusion, steps⟩]

/-- The views of a law: those of its guarded formula. -/
def Law.views (interface : Interface Variable Literal Symbol) (law : Law Variable Literal Symbol) :
    List (View Variable Literal Symbol) :=
  viewsOf [] [] [] (law.formula interface)

/-- The view as a statement: `∀ binders. (premises → conclusion)`. -/
def View.statement (view : View Variable Literal Symbol) : Formula Variable Literal Symbol :=
  view.binders.foldr .forallVar (.imp (.conjunction view.premises) view.conclusion)

/-- The premise at `index` from a proof of the conjunction of `premises`. -/
def premiseProof : List (Formula Variable Literal Symbol) → Nat → Proof Variable Literal Symbol →
    Proof Variable Literal Symbol
  | premise :: _, 0, proof => .node .conjLeft premise [proof]
  | _ :: rest, index + 1, proof => premiseProof rest index (.node .conjRight (.conjunction rest) [proof])
  | [], _, proof => proof

/-- Replay a view's steps from a proof of `formula`. -/
def replay (premises : List (Formula Variable Literal Symbol)) (assumption : Proof Variable Literal Symbol) :
    List (ViewStep Variable) → Formula Variable Literal Symbol → Proof Variable Literal Symbol →
      Proof Variable Literal Symbol
  | .eliminate binder :: steps, .forallVar _ body, proof =>
      replay premises assumption steps body (.node (.forallElim (.var binder)) body [proof])
  | .discharge index :: steps, .imp _ rest, proof =>
      replay premises assumption steps rest (.node .impElim rest [proof, premiseProof premises index assumption])
  | .left :: steps, .conj left _, proof => replay premises assumption steps left (.node .conjLeft left [proof])
  | .right :: steps, .conj _ right, proof => replay premises assumption steps right (.node .conjRight right [proof])
  | _, _, proof => proof

/-- Universal introductions of `binders`, each at itself, over a proof of the
matrix. -/
def introduce (matrix : Formula Variable Literal Symbol) :
    List Variable → Proof Variable Literal Symbol → Proof Variable Literal Symbol
  | [], proof => proof
  | binder :: rest, proof => .node (.forallIntro binder) (.forallVar binder (rest.foldr .forallVar matrix))
      [introduce matrix rest proof]

/-- The view's proof from the law's clause: introduce its binders at
themselves, assume its premises, replay its steps. -/
def View.proof (interface : Interface Variable Literal Symbol) (law : Law Variable Literal Symbol)
    (view : View Variable Literal Symbol) : Proof Variable Literal Symbol :=
  let matrix : Formula Variable Literal Symbol := .imp (.conjunction view.premises) view.conclusion
  let lawProof : Proof Variable Literal Symbol :=
    .node (.clause (Law.clause interface law) []) (law.formula interface) [.node .truth .truth []]
  let assumption : Proof Variable Literal Symbol := .node .assumption (.conjunction view.premises) []
  introduce matrix view.binders
    (.node .impIntro matrix [replay view.premises assumption view.steps (law.formula interface) lawProof])

/-- The view as a lemma entry named `name`, proved under no assumptions. Its
binders range over the carrier: the guards are its premises. -/
def View.lemma (vocab : Vocabulary Symbol) (interface : Interface Variable Literal Symbol)
    (law : Law Variable Literal Symbol) (name : Symbol) (view : View Variable Literal Symbol) :
    Lemma Domain Variable Literal Symbol :=
  ⟨⟨name, [], view.statement, encode vocab (view.proof interface law)⟩, fun _ => .carrier⟩

/-- The lemmas of a law, its `index`-th view named `name index`. -/
def Law.lemmas (vocab : Vocabulary Symbol) (interface : Interface Variable Literal Symbol)
    (law : Law Variable Literal Symbol) (name : Nat → Symbol) : List (Lemma Domain Variable Literal Symbol) :=
  (law.views interface).mapIdx fun index view => view.lemma vocab interface law (name index)

/-! ## The laws a goal may need -/

section Needs

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

/-- Two sides that may be equal: unless both are closed and different. -/
def compatible (side goalSide : Term Variable Literal Symbol) : Bool :=
  !(side.freeVars.isEmpty && goalSide.freeVars.isEmpty) || Machine.identical side goalSide

/-- A view may conclude an equation goal: its conclusion is an equation
applying the same operation on the same side, its other side compatible with
the goal's. It routes the diagnosis and decides nothing. -/
def View.mayConclude (view : View Variable Literal Symbol) (goal : Formula Variable Literal Symbol) : Bool :=
  match view.conclusion, goal with
  | .equal left right, .equal goalLeft goalRight =>
      ((callShape left).isSome && callShape left == callShape goalLeft && compatible right goalRight) ||
        ((callShape right).isSome && callShape right == callShape goalRight && compatible left goalLeft)
  | _, _ => false

/-- The laws with a view that may conclude the goal and is not `offered` as a
lemma, each named once, in the registry's order. -/
def Registry.lawsFor (registry : Registry Domain Variable Literal Symbol) (goal : Formula Variable Literal Symbol)
    (offered : Formula Variable Literal Symbol → Bool) : List Symbol :=
  (registry.interfaces.flatMap fun interface => interface.laws.filterMap fun law =>
    if (law.views interface).any (fun view => view.mayConclude goal && !offered view.statement) then some law.name
    else none).eraseDups

end Needs

end AnthillModKbSpec.DictionaryRegistry
