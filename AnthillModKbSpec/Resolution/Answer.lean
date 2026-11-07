import AnthillModKbSpec.Resolution.P0.Admission
import AnthillModKbSpec.Resolution.Machine.OpenAtoms

/-! # Answers: Yes, No, Unknown, and Undecided (S22)

The KB module either computes an answer or stops and says what it cannot
compute. Its answers keep two unknowns apart:

- **Unknown** is logical: the KB leaves the goal open. It is a decided answer
  about the KB, carried by two witnesses: a model of the completion in which
  the goal holds and one in which it fails.
- **Undecided** is the module's own: it did not decide the goal, and its
  blockers say what is missing, each with its site, path, and formula. It
  says nothing about the KB.

Operational outcomes (fuel, an exhausted or interrupted search, floundering,
an unsupported formula) are never Unknown: they give Undecided.

`Answer` is generic in its evidence. Each route chooses what a Yes, a No, and
a witness carry, and what they mean (`Meaning`); `Answer.Sound` states that
an answer means what it says. Combining two results for the same goal
(`Answer.combine`) keeps a definite Yes or No; otherwise a remaining blocker
gives Undecided, since evidence for it could still give Yes, No, or Unknown;
Unknown only when no blocker remains. Undecided with no blocker is no result,
the unit of the combination. Supplying checked evidence for
an Undecided answer turns it into Yes or No (`Answer.supplyProof`,
`Answer.supplyRefutation`).

P0 reports admission's requests as blockers before anything runs
(`Admission.answer`), and a Ready plan's answer is Yes or No, never Undecided
(`Plan.decision_decided`): a completed P1 decision returns no operational
result, and the logical Unknown would be a decided value. P0 reads a marker
as an atom without clauses, so it reports every formula reaching a marker
atom as a blocker instead of deciding it. -/

namespace AnthillModKbSpec.Answers

open Machine Semantics

/-- A construct the module has no route for. -/
inductive Construct where
  /-- A capability P0 names that is not a proof, a mode, or a termination argument. -/
  | capability (capability : Admission.Capability)
  /-- NAF where the route runs none, as in S12's cases. -/
  | negation
  /-- A range guard on a name no goal of its clause binds. -/
  | waitingGuard
  /-- A run's strategy had no capability for a focus (a machine gap). -/
  | unsupported
  /-- A candidate or a delay broke the machine's name or binding contract. -/
  | contract
  /-- A predicate an induction principle quantifies over is not registered at
  its arity. -/
  | registration
  /-- A carried induction principle's names are not admissible. -/
  | principleNames
  /-- An open predicate's marked case, in a route that reads markers closed
  (P0): the completion route answers it. -/
  | openPredicate
  deriving DecidableEq, Repr

/-- What a blocker lacks. Supplying it may settle the goal. -/
inductive Missing (Variable Literal Symbol : Type) where
  /-- A proof of the formula: a guarded universal over an infinite domain, a
  goal implication, or a goal the search did not prove or refute. A checked
  proof term, a lemma, or a failure certificate settles it. -/
  | proof
  /-- A mode: a name the formula needs bound before it runs, or a goal still
  waiting for a binding when its branch ended (floundering). -/
  | mode
  /-- A termination argument: a dependency cycle, or a run interrupted by its fuel. -/
  | termination
  /-- A construct the module has no route for. -/
  | construct (construct : Construct)
  /-- Open atoms whose two witnesses were not both exhibited: they occur both
  ways (`p(a) ∨ ¬p(a)`), or a denial constrains them. -/
  | witnesses (atoms : List (Term Variable Literal Symbol))

/-- Where a blocker sits: a site admission inspected, before anything runs, or
an obligation a run reached, with its context and its provenance from the
root: each frame's rule, the clause it selected, and the premise position. -/
inductive Place (Variable Literal Symbol : Type) where
  | site (site : Admission.Site)
  | reached (context : ProofContext Variable Literal Symbol) (trail : List (Origin Variable Literal Symbol))

/-- One blocker: the formula at a path under its place, and what it lacks. At
an admission site the path is a term path; at a reached obligation it is the
premise positions along its provenance. -/
structure Blocker (Variable Literal Symbol : Type) where
  place : Place Variable Literal Symbol
  path : List Nat
  formula : Term Variable Literal Symbol
  missing : Missing Variable Literal Symbol

/-- The answers. `yes` carries a proof of the goal, `no` a refutation or a
failure certificate, `unknown` two witnesses, the first making the goal true
and the second false, and `undecided` its blockers. -/
inductive Answer (Proof Refutation Witness Blocker : Type) where
  | yes (proof : Proof)
  | no (refutation : Refutation)
  | unknown (holds fails : Witness)
  | undecided (blockers : List Blocker)

/-- What a route's answers claim about one goal: that it holds (Yes), that it
fails (No), and that it is independent of the KB (Unknown). -/
structure Meaning where
  truth : Prop
  falsity : Prop
  independence : Prop

section Meaning

variable {Variable Literal Symbol : Type} [DecidableEq Variable] {hoApplySymbol : Symbol}

/-- The meaning over a class of models: the goal holds in every model of the
class under every environment satisfying the context (Yes), fails in each
(No), or holds in one and fails in another (Unknown). -/
def Meaning.ofModels (Holds : (Value : Type) → Model Literal Symbol Value hoApplySymbol → Prop)
    (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) : Meaning where
  truth := ∀ (Value : Type) (model : Model Literal Symbol Value hoApplySymbol), Holds Value model →
    ∀ environment, model.ContextHolds environment context → model.Satisfies environment goal
  falsity := ∀ (Value : Type) (model : Model Literal Symbol Value hoApplySymbol), Holds Value model →
    ∀ environment, model.ContextHolds environment context → ¬ model.Satisfies environment goal
  independence :=
    (∃ (Value : Type) (model : Model Literal Symbol Value hoApplySymbol), Holds Value model ∧
      ∃ environment, model.ContextHolds environment context ∧ model.Satisfies environment goal) ∧
    (∃ (Value : Type) (model : Model Literal Symbol Value hoApplySymbol), Holds Value model ∧
      ∃ environment, model.ContextHolds environment context ∧ ¬ model.Satisfies environment goal)

/-- Independence excludes both definite claims once some model satisfies the
context: an Unknown is never also a Yes or a No. -/
theorem Meaning.ofModels_independent {Holds : (Value : Type) → Model Literal Symbol Value hoApplySymbol → Prop}
    {context : ProofContext Variable Literal Symbol} {goal : Formula Variable Literal Symbol}
    (independent : (Meaning.ofModels Holds context goal).independence) :
    ¬ (Meaning.ofModels Holds context goal).truth ∧ ¬ (Meaning.ofModels Holds context goal).falsity := by
  obtain ⟨⟨_, model, holds, environment, context, true⟩, ⟨_, other, otherHolds, otherEnvironment, otherContext, false⟩⟩ :=
    independent
  exact ⟨fun truth => false (truth _ other otherHolds otherEnvironment otherContext),
    fun falsity => falsity _ model holds environment context true⟩

end Meaning

namespace Answer

variable {Proof Refutation Witness Blocker : Type}

/-- An answer means what it says. Undecided claims nothing. -/
def Sound (meaning : Meaning) : Answer Proof Refutation Witness Blocker → Prop
  | .yes _ => meaning.truth
  | .no _ => meaning.falsity
  | .unknown _ _ => meaning.independence
  | .undecided _ => True

/-- A definite answer: Yes or No. -/
def definite : Answer Proof Refutation Witness Blocker → Bool
  | .yes _ | .no _ => true
  | _ => false

/-- An answer that decides the goal: Yes, No, or Unknown. -/
def decided : Answer Proof Refutation Witness Blocker → Bool
  | .undecided _ => false
  | _ => true

/-- The blockers an answer reports. -/
def blockers : Answer Proof Refutation Witness Blocker → List Blocker
  | .undecided blockers => blockers
  | _ => []

/-- Combine two results for the same goal. A definite Yes or No wins, the
first one when both are definite. Otherwise a remaining blocker gives
Undecided with every blocker, since evidence for it could still give Yes, No,
or Unknown. Unknown only when no blocker remains, the first Unknown's
witnesses kept. Undecided with no blocker is no result: it changes nothing. -/
def combine : Answer Proof Refutation Witness Blocker → Answer Proof Refutation Witness Blocker →
    Answer Proof Refutation Witness Blocker
  | .yes proof, _ => .yes proof
  | .no refutation, _ => .no refutation
  | _, .yes proof => .yes proof
  | _, .no refutation => .no refutation
  | .unknown holds fails, .unknown _ _ => .unknown holds fails
  | .unknown holds fails, .undecided blockers => if blockers.isEmpty then .unknown holds fails else .undecided blockers
  | .undecided blockers, .unknown holds fails => if blockers.isEmpty then .unknown holds fails else .undecided blockers
  | .undecided first, .undecided second => .undecided (first ++ second)

/-- Combining keeps soundness: both results are about the same goal. -/
theorem combine_sound {meaning : Meaning} {first second : Answer Proof Refutation Witness Blocker}
    (firstSound : first.Sound meaning) (secondSound : second.Sound meaning) : (first.combine second).Sound meaning := by
  cases first <;> cases second <;> simp only [combine] <;> (try split) <;>
    first | exact firstSound | exact secondSound | trivial

/-- A definite first result is kept. -/
theorem combine_definite {first : Answer Proof Refutation Witness Blocker} (definite : first.definite = true)
    (second : Answer Proof Refutation Witness Blocker) : first.combine second = first := by
  cases first <;> simp_all [Answer.definite, combine]

/-- A definite second result wins over a first that is not definite. -/
theorem combine_definite_right {first second : Answer Proof Refutation Witness Blocker}
    (notDefinite : first.definite = false) (definite : second.definite = true) : first.combine second = second := by
  cases first <;> cases second <;> simp_all [Answer.definite, combine]

/-- Undecided exactly when neither result is definite and a blocker remains,
or both are Undecided; its blockers are both results' blockers. -/
theorem combine_undecided {first second : Answer Proof Refutation Witness Blocker} {blockers : List Blocker} :
    first.combine second = .undecided blockers ↔
      first.definite = false ∧ second.definite = false ∧
        ((first.decided = false ∧ second.decided = false) ∨ first.blockers ++ second.blockers ≠ []) ∧
        blockers = first.blockers ++ second.blockers := by
  cases first <;> cases second <;> simp only [combine] <;> (try split) <;>
    simp_all [Answer.definite, Answer.decided, Answer.blockers, List.isEmpty_iff] <;>
    exact ⟨fun same => same.symm, fun same => same.symm⟩

/-- Unknown only when no blocker remains: neither result is definite or has a
blocker, and one of them is this Unknown. -/
theorem combine_unknown {first second : Answer Proof Refutation Witness Blocker} {holds fails : Witness}
    (combined : first.combine second = .unknown holds fails) :
    first.definite = false ∧ second.definite = false ∧ first.blockers = [] ∧ second.blockers = [] ∧
      (first = .unknown holds fails ∨ second = .unknown holds fails) := by
  cases first <;> cases second <;> simp only [combine] at combined <;> (try split at combined) <;>
    simp_all [Answer.definite, Answer.blockers, List.isEmpty_iff]

/-- No result changes nothing: Undecided with no blocker is the unit. -/
theorem combine_none_left (answer : Answer Proof Refutation Witness Blocker) :
    (Answer.undecided [] : Answer Proof Refutation Witness Blocker).combine answer = answer := by
  cases answer <;> simp [combine]

theorem combine_none_right (answer : Answer Proof Refutation Witness Blocker) :
    answer.combine (.undecided []) = answer := by
  cases answer <;> simp [combine]

/-- The combination of a list of results, in order; no result for none. -/
def combineAll (answers : List (Answer Proof Refutation Witness Blocker)) : Answer Proof Refutation Witness Blocker :=
  answers.foldr combine (.undecided [])

theorem combineAll_sound {meaning : Meaning} :
    ∀ {answers : List (Answer Proof Refutation Witness Blocker)}, (∀ answer ∈ answers, answer.Sound meaning) →
      (combineAll answers).Sound meaning
  | [], _ => trivial
  | answer :: rest, sound =>
      combine_sound (sound answer List.mem_cons_self)
        (combineAll_sound (answers := rest) fun other member => sound other (List.mem_cons_of_mem _ member))

/-- Supplying a proof for an Undecided answer: Yes when the check accepts it.
Any other answer is kept. -/
def supplyProof (check : Proof → Bool) (proof : Proof) : Answer Proof Refutation Witness Blocker →
    Answer Proof Refutation Witness Blocker
  | .undecided blockers => if check proof then .yes proof else .undecided blockers
  | answer => answer

/-- Supplying a refutation or a failure certificate for an Undecided answer:
No when the check accepts it. -/
def supplyRefutation (check : Refutation → Bool) (refutation : Refutation) : Answer Proof Refutation Witness Blocker →
    Answer Proof Refutation Witness Blocker
  | .undecided blockers => if check refutation then .no refutation else .undecided blockers
  | answer => answer

theorem supplyProof_sound {meaning : Meaning} {check : Proof → Bool}
    (checkSound : ∀ proof, check proof = true → meaning.truth) {proof : Proof}
    {answer : Answer Proof Refutation Witness Blocker} (sound : answer.Sound meaning) :
    (answer.supplyProof check proof).Sound meaning := by
  cases answer with
  | undecided blockers =>
      show Sound meaning (if check proof = true then .yes proof else .undecided blockers)
      split
      · rename_i accepted; exact checkSound proof accepted
      · trivial
  | _ => exact sound

theorem supplyRefutation_sound {meaning : Meaning} {check : Refutation → Bool}
    (checkSound : ∀ refutation, check refutation = true → meaning.falsity) {refutation : Refutation}
    {answer : Answer Proof Refutation Witness Blocker} (sound : answer.Sound meaning) :
    (answer.supplyRefutation check refutation).Sound meaning := by
  cases answer with
  | undecided blockers =>
      show Sound meaning (if check refutation = true then .no refutation else .undecided blockers)
      split
      · rename_i accepted; exact checkSound refutation accepted
      · trivial
  | _ => exact sound

/-- A checked proof turns an Undecided answer into Yes. -/
theorem supplyProof_yes {check : Proof → Bool} {proof : Proof} {blockers : List Blocker}
    (accepted : check proof = true) :
    (Answer.undecided blockers : Answer Proof Refutation Witness Blocker).supplyProof check proof = .yes proof := by
  simp [supplyProof, accepted]

/-- A checked refutation turns an Undecided answer into No. -/
theorem supplyRefutation_no {check : Refutation → Bool} {refutation : Refutation} {blockers : List Blocker}
    (accepted : check refutation = true) :
    (Answer.undecided blockers : Answer Proof Refutation Witness Blocker).supplyRefutation check refutation =
      .no refutation := by
  simp [supplyRefutation, accepted]

end Answer

/-! ## Blockers from admission and from runs -/

section Blockers

variable {Variable Literal Symbol : Type}

/-- What a P0 capability lacks: a ground instance is a mode, an acyclic
strategy a termination argument, a scoped proof a proof; the others are
constructs P0 has no route for. -/
def Missing.ofCapability : Admission.Capability → Missing Variable Literal Symbol
  | .groundInstance => .mode
  | .acyclicStrategy => .termination
  | .scopedProof => .proof
  | capability => .construct (.capability capability)

/-- A P0 request as a blocker, at its site and path. -/
def Blocker.ofRequest (request : Admission.Request Variable Literal Symbol) : Blocker Variable Literal Symbol :=
  ⟨.site request.site, request.path, request.formula, .ofCapability request.capability⟩

/-- A machine gap as a blocker, at the obligation it was recorded for: its
context and its provenance are kept. An obligation that met open atoms names
them (`opened`); floundering lacks a mode. -/
def Blocker.ofGap (opened : Term Variable Literal Symbol → List (Term Variable Literal Symbol))
    (gap : Gap Variable Literal Symbol) : Blocker Variable Literal Symbol :=
  ⟨.reached gap.obligation.context gap.trail, gap.trail.map Origin.premise, gap.obligation.goal,
    match gap.reason with
    | .unsupported => .construct .unsupported
    | .contract => .construct .contract
    | .floundered => .mode
    | .opened => .witnesses (opened gap.obligation.goal)⟩

/-- A run interrupted by its fuel: the query's goal, under its context, lacks
a termination argument. -/
def Blocker.interrupted (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    Blocker Variable Literal Symbol :=
  ⟨.reached context [], [], goal, .termination⟩

/-- A goal no route proved or refuted lacks a proof. -/
def Blocker.unproved (goal : Formula Variable Literal Symbol) : Blocker Variable Literal Symbol :=
  ⟨.site .goal, [], goal, .proof⟩

end Blockers

end AnthillModKbSpec.Answers

/-! ## The P0 answer -/

namespace AnthillModKbSpec.Admission

open Answers Machine GroundSearch Semantics

variable {Domain Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  [FreshNames Variable] {hoApplySymbol : Symbol}

/-- What P0 answers carry: a Yes the run's completed proof, a No the root's
negative certificate (a complete-failure witness for the exact program and
context), and no witness: P0 has no open atoms. -/
abbrev P0Answer (Domain Variable Literal Symbol : Type) :=
  Answer (CompletedProof Variable Literal Symbol (P0.Certificate Variable Literal Symbol) (Input Domain Variable Literal Symbol))
    (P0.NegativeCertificate Variable Literal Symbol) Empty (Blocker Variable Literal Symbol)

/-- The root's negative certificate: the run's clauses and context, the goal,
and its failure witness. -/
def Plan.refutation (plan : Plan Domain Variable Literal Symbol hoApplySymbol) : P0.NegativeCertificate Variable Literal Symbol :=
  plan.ground.certify ⟨plan.ground.scope, plan.ground.goal⟩ plan.ground.goal

/-- A Ready plan's answer: the run to the finish, with no fuel. -/
def Plan.decision (plan : Plan Domain Variable Literal Symbol hoApplySymbol) : P0Answer Domain Variable Literal Symbol :=
  match P0.runToEnd plan.ground (plan.ground.init plan.input) (plan.ground.init_inv plan.input) with
  | .success proof _ => .yes proof
  | _ => .no plan.refutation

/-- The formulas of an input that mention a marker atom in goal positions: the
goal, an assumption, or a KB clause's body goal, each at its site. P0 reads a
marker as an atom without clauses, so it decides none of them. -/
def markerBlockers (marker : Symbol → Bool) (input : Input Domain Variable Literal Symbol) :
    List (Blocker Variable Literal Symbol) :=
  let reaches := fun (formula : Term Variable Literal Symbol) => (Completion.goalAtoms formula).any (Completion.markerAtom marker)
  let blocker := fun (site : Site) (formula : Term Variable Literal Symbol) =>
    (⟨.site site, [], formula, .construct .openPredicate⟩ : Blocker Variable Literal Symbol)
  (if reaches input.goal then [blocker .goal input.goal] else []) ++
    (input.context.zipIdx.filterMap fun (assumption, index) =>
      if reaches assumption then some (blocker (.assumption index) assumption) else none) ++
    input.kbClauses.flatMap fun
      | (index, .definite _ body) => body.zipIdx.filterMap fun (goal, position) =>
          if reaches goal then some (blocker (.body index position) goal) else none
      | (index, .goal body) => body.zipIdx.filterMap fun (goal, position) =>
          if reaches goal then some (blocker (.body index position) goal) else none

/-- The P0 answer of an input, with `marker` the open marker. Admission's
requests are its blockers, reported before anything runs, and so is every
formula that mentions a marker atom (`markerBlockers`); a Ready plan with no
marker is decided; an input contradicting its own declarations is invalid,
not an answer. -/
def answer (marker : Symbol → Bool) (hoApplySymbol : Symbol) (input : Input Domain Variable Literal Symbol) :
    Except Diagnostic (P0Answer Domain Variable Literal Symbol) :=
  match check hoApplySymbol input with
  | .invalid diagnostic => .error diagnostic
  | .needsEvidence request more =>
      .ok (.undecided (markerBlockers marker input ++ (request :: more).map Blocker.ofRequest))
  | .ready plan =>
      match markerBlockers marker input with
      | [] => .ok plan.decision
      | blockers => .ok (.undecided blockers)

/-- The meaning of P0's answers: the models completed for the plan's program
and context with complement NAF. The context is part of the completion: its
atoms are the plan's facts. -/
def Plan.meaning (plan : Plan Domain Variable Literal Symbol hoApplySymbol) : Meaning :=
  Meaning.ofModels (Variable := Variable) (hoApplySymbol := hoApplySymbol)
    (fun _ model => model.GroundCompleted plan.ground.program plan.ground.context ∧ model.ComplementNAF) []
    plan.input.goal

/-- Admission's requests are Undecided blockers, at their sites and paths, and
nothing runs for them. -/
theorem answer_needsEvidence {marker : Symbol → Bool} {input : Input Domain Variable Literal Symbol}
    {request : Request Variable Literal Symbol} {more : List (Request Variable Literal Symbol)}
    (needs : check hoApplySymbol input = .needsEvidence request more) :
    answer marker hoApplySymbol input =
      .ok (.undecided (markerBlockers marker input ++ (request :: more).map Blocker.ofRequest)) := by
  simp [answer, needs]

theorem answer_ready {marker : Symbol → Bool} {input : Input Domain Variable Literal Symbol}
    {plan : Plan Domain Variable Literal Symbol hoApplySymbol} (ready : check hoApplySymbol input = .ready plan)
    (unmarked : markerBlockers marker input = []) : answer marker hoApplySymbol input = .ok plan.decision := by
  simp [answer, ready, unmarked]

/-- P0 decides no input that mentions a marker atom: it reads markers closed,
and the logical Unknown is the completion route's. -/
theorem answer_marked {marker : Symbol → Bool} {input : Input Domain Variable Literal Symbol}
    {result : P0Answer Domain Variable Literal Symbol} (marked : markerBlockers marker input ≠ [])
    (answered : answer marker hoApplySymbol input = .ok result) : ∃ blockers, result = .undecided blockers := by
  unfold answer at answered
  split at answered
  · cases answered
  · cases answered; exact ⟨_, rfl⟩
  · split at answered
    · rename_i unmarked; exact absurd unmarked marked
    · cases answered; exact ⟨_, rfl⟩

/-- The P1 contract for P0: a Ready plan's answer is Yes or No, never Unknown
and never Undecided. -/
theorem Plan.decision_decided (plan : Plan Domain Variable Literal Symbol hoApplySymbol) :
    plan.decision.definite = true := by
  unfold Plan.decision
  split <;> rfl

/-- Yes exactly when the query has a success certificate; No carries a valid
complete-failure certificate for the goal. -/
theorem Plan.decision_spec (plan : Plan Domain Variable Literal Symbol hoApplySymbol) :
    (∀ proof, plan.decision = .yes proof → Succeeds plan.ground.program plan.ground.context plan.input.goal) ∧
    (∀ refutation, plan.decision = .no refutation →
      refutation.Valid plan.ground.program plan.ground.context ∧ refutation.operand = plan.input.goal) := by
  rw [← plan.admits.goal]
  unfold Plan.decision
  rcases P0.runToEnd_finished plan.ground (plan.ground.init plan.input) (plan.ground.init_inv plan.input) with
    ⟨⟨proof, resume, ran⟩, proved⟩ | ⟨ran, failed⟩
  · rw [ran]
    exact ⟨fun _ _ => proved, fun _ same => by cases same⟩
  · rw [ran]
    refine ⟨fun _ same => (by cases same), fun refutation same => ?_⟩
    cases same
    obtain ⟨tree, built, checked⟩ := evaluate_failure (context := plan.ground.context) plan.ground.ranked
      plan.ground.valid (Nat.le_refl _) failed
    refine ⟨⟨rfl, rfl, ?_⟩, rfl⟩
    show (match (plan.ground.witness plan.ground.scope.assumptions plan.ground.goal) with
      | some tree => checkFailure hoApplySymbol plan.ground.program.clauses plan.ground.scope.assumptions
          plan.ground.goal tree
      | none => false) = true
    unfold P0.Ground.witness
    rw [show plan.ground.scope.assumptions = plan.ground.context.assumptions from rfl, built]
    exact checked

/-- P0's answers are sound for its completion: Yes makes the goal true and No
false in every model completed for the plan's program and context with
complement NAF. -/
theorem Plan.decision_sound (plan : Plan Domain Variable Literal Symbol hoApplySymbol) :
    plan.decision.Sound plan.meaning := by
  obtain ⟨yes, no⟩ := plan.decision_spec
  cases decided : plan.decision with
  | yes proof =>
      rintro Value model ⟨completed, negation⟩ environment _
      exact (model.ground_certificates_sound completed negation).1 _ (yes proof decided) environment
  | no refutation =>
      rintro Value model ⟨completed, negation⟩ environment _
      obtain ⟨valid, operand⟩ := no refutation decided
      exact (model.ground_certificates_sound completed negation).2 _ (operand ▸ valid.fails) environment
  | unknown holds _ => exact holds.elim
  | undecided _ => trivial

/-- Every P0 answer is sound: Undecided claims nothing, and a Ready plan's
answer is sound for its completion. -/
theorem answer_sound {marker : Symbol → Bool} {input : Input Domain Variable Literal Symbol}
    {result : P0Answer Domain Variable Literal Symbol} (answered : answer marker hoApplySymbol input = .ok result) :
    (∃ plan, check hoApplySymbol input = .ready plan ∧ result = plan.decision ∧ result.Sound plan.meaning) ∨
      ∃ blockers, result = .undecided blockers := by
  unfold answer at answered
  split at answered
  · cases answered
  · cases answered; exact .inr ⟨_, rfl⟩
  · rename_i plan ready
    split at answered
    · cases answered
      exact .inl ⟨plan, ready, rfl, plan.decision_sound⟩
    · cases answered; exact .inr ⟨_, rfl⟩

end AnthillModKbSpec.Admission
