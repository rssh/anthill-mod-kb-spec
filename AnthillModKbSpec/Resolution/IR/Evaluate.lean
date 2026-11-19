import AnthillModKbSpec.Resolution.IR.Extension

/-! # The IR evaluator: exact P1 decisions (S28)

`Program.answer` answers a query of P0 or P1 with S22's results, exactly, with
no fuel ([decision IR](../../../docs/decision-ir.md)); `Program.decideWithin`
(`IR/Budgeted`) adds P2 within the fuel:

1. **The KB-level check** (`Program.kbCheck`, decided with the user,
   2026-11-18): the ground heads of the rules on cycles through NAF that read
   an atom, with the denials, get a relevant program of their own, decided
   once per KB beside the queries. It is split into pieces linked by its rules
   and denials, each searched for one model with early exit
   (`GroundProgram.hasModel`); when the joint query is not P1, the roots whose
   own query is P1 are checked jointly, and each alone when that query is not
   P1 either. A piece with no model shows the KB has none: every query is
   Undecided, naming the piece's atoms.
2. **The instances** (`Program.instances`): a closed query's relevant program,
   or one per instance of the split of its rigid parameters, exact and finite
   (`Program.groundProgram`).
3. **The Kripke–Kleene iteration** on each, then the **enumeration** of the
   completion's models over the atoms it leaves undefined and the markers
   (`GroundProgram.models`): every key fixpoint's restriction agrees with one
   of them (`fixpoint_model`, `models_complete`), and one of them extends to a
   key fixpoint when the rules outside are stratified (`extends_model`).
4. **The combination** (`Program.combine`), over the models satisfying the
   conditions: an instance with no model is the KB's inconsistency
   (Undecided, naming it); the goal true in each model of each instance is
   Yes, false in each is No; otherwise Unknown, with a model where it holds
   and one where it fails, read as S27's `meaning_split` states. A context no
   model satisfies gives Yes: both Yes and No hold then (S26 settles vacuous
   contexts).
5. **Unknown** only from witnesses of instances whose rules outside are
   stratified (`outsideStratified`), so that each witness extends to a model
   of the whole completion (`extends_model`); with no such pair, Undecided,
   naming a rule on a cycle through NAF among the rules outside (decided with
   the user, 2026-11-18).

| Property | Theorem |
| --- | --- |
| Every answer means what it says over the models of the completion realizing the signature, with no hypothesis | `answer_sound` |
| With the rules outside stratified, a P0 or P1 query is Undecided only when the KB has no model | `answer_decided` |
| **Exactness**: then Yes exactly when the goal holds in every model and fails in none, No exactly when it fails in every one and holds in none, Unknown exactly when both occur | `answer_exact` |

The answers and their meaning are S27's (`Program.meaning`); a closed query
is read over the key fixpoints by the Herbrand reduction (`herbrand`), a split
one through its instances (`meaning_classify`). -/

namespace AnthillModKbSpec.IR

open Semantics Completion Tabled Answers

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

attribute [local instance] Machine.termEq

/-! ## The models of a ground program and its query -/

/-- An assignment of the relevant atoms and the markers: those listed true. -/
abbrev Assignment (Variable Literal Symbol : Type) :=
  List (GAtom Variable Literal Symbol) × List (GAtom Variable Literal Symbol)

namespace GroundProgram

variable (ground : GroundProgram Variable Literal Symbol)

/-- The conditions hold under an assignment, decided. -/
def conditionsIn (assignment : Assignment Variable Literal Symbol) : Bool :=
  ground.conditions.holdsIn assignment.1 assignment.2 && ground.conditionsFixed

/-- The goal holds under an assignment, decided. -/
def goalIn (assignment : Assignment Variable Literal Symbol) : Bool :=
  ground.goals.any fun body => body.holdsIn assignment.1 assignment.2

/-- The models satisfying the conditions. -/
def conditioned : List (Assignment Variable Literal Symbol) := ground.models.filter ground.conditionsIn

/-- A model satisfying the conditions in which the goal holds. -/
def trueWitness : Option (Assignment Variable Literal Symbol) := ground.conditioned.find? ground.goalIn

/-- A model satisfying the conditions in which the goal fails. -/
def falseWitness : Option (Assignment Variable Literal Symbol) := ground.conditioned.find? fun assignment => !ground.goalIn assignment

theorem conditionsIn_iff (assignment : Assignment Variable Literal Symbol) :
    ground.conditionsIn assignment = true ↔ ground.ConditionsHold (· ∈ assignment.1) (· ∈ assignment.2) := by
  simp [conditionsIn, ConditionsHold, GroundBody.holdsIn_iff]

theorem goalIn_iff (assignment : Assignment Variable Literal Symbol) :
    ground.goalIn assignment = true ↔ ground.GoalHolds (· ∈ assignment.1) (· ∈ assignment.2) := by
  simp [goalIn, GoalHolds, GroundBody.holdsIn_iff]

/-- Assignments that agree on the atoms and the markers agree on the
conditions and the goal. -/
theorem agree_query (closedProgram : ground.Closed) {closed closed' marked marked' : GAtom Variable Literal Symbol → Prop}
    (atomsAgree : ∀ atom ∈ ground.atoms, closed atom ↔ closed' atom)
    (markersAgree : ∀ atom ∈ ground.markerAtoms, marked atom ↔ marked' atom) :
    (ground.ConditionsHold closed marked ↔ ground.ConditionsHold closed' marked') ∧
      (ground.GoalHolds closed marked ↔ ground.GoalHolds closed' marked') := by
  have bodyAgree : ∀ body ∈ ground.denials ++ ground.conditions :: ground.goals,
      (body.Holds closed marked ↔ body.Holds closed' marked') := fun body member =>
    GroundBody.holds_congr (fun atom inside => atomsAgree atom (closedProgram.2 body member atom inside))
      (fun atom inside => markersAgree atom (ground.markerAtoms_bodies member atom inside))
  refine ⟨?_, ?_⟩
  · unfold ConditionsHold
    rw [bodyAgree _ (List.mem_append_right _ List.mem_cons_self)]
  · unfold GoalHolds
    constructor
    · rintro ⟨body, member, holds⟩
      exact ⟨body, member, (bodyAgree body (List.mem_append_right _ (List.mem_cons_of_mem _ member))).mp holds⟩
    · rintro ⟨body, member, holds⟩
      exact ⟨body, member, (bodyAgree body (List.mem_append_right _ (List.mem_cons_of_mem _ member))).mpr holds⟩

/-- Every model agrees with a model found, which satisfies the conditions and
the goal as it does. -/
theorem models_agree (closedProgram : ground.Closed) {closed marked : GAtom Variable Literal Symbol → Prop}
    (model : ground.Model closed marked) :
    ∃ assignment ∈ ground.models, (ground.ConditionsHold closed marked ↔ ground.conditionsIn assignment = true) ∧
      (ground.GoalHolds closed marked ↔ ground.goalIn assignment = true) := by
  obtain ⟨assignment, member, atomsAgree, markersAgree⟩ := ground.models_complete closedProgram model
  obtain ⟨conditionsAgree, goalAgree⟩ := ground.agree_query closedProgram (fun atom inside => (atomsAgree atom inside).symm)
    (fun atom inside => (markersAgree atom inside).symm)
  exact ⟨assignment, member, conditionsAgree.trans (ground.conditionsIn_iff _).symm, goalAgree.trans (ground.goalIn_iff _).symm⟩

theorem falseWitness_none (none : ground.falseWitness = none) : ∀ assignment ∈ ground.conditioned, ground.goalIn assignment = true := by
  intro assignment member
  have := List.find?_eq_none.mp none assignment member
  simpa using this

theorem trueWitness_none (none : ground.trueWitness = none) : ∀ assignment ∈ ground.conditioned, ground.goalIn assignment = false := by
  intro assignment member
  have := List.find?_eq_none.mp none assignment member
  simpa using this

theorem falseWitness_some {assignment : Assignment Variable Literal Symbol} (found : ground.falseWitness = some assignment) :
    assignment ∈ ground.conditioned ∧ ground.goalIn assignment = false := by
  have spec := List.find?_some found
  simp only [Bool.not_eq_true'] at spec
  exact ⟨List.mem_of_find?_eq_some found, spec⟩

theorem trueWitness_some {assignment : Assignment Variable Literal Symbol} (found : ground.trueWitness = some assignment) :
    assignment ∈ ground.conditioned ∧ ground.goalIn assignment = true :=
  ⟨List.mem_of_find?_eq_some found, List.find?_some found⟩

/-- A model found satisfying the conditions passes the model check and the
conditions. -/
theorem conditioned_parts {assignment : Assignment Variable Literal Symbol} (member : assignment ∈ ground.conditioned) :
    ground.isModel assignment.1 assignment.2 = true ∧ ground.conditionsIn assignment = true :=
  ⟨(List.mem_filter.mp (List.mem_filter.mp member).1).2, (List.mem_filter.mp member).2⟩

end GroundProgram

/-! ## The answer from the instances' ground programs -/

/-- The answers of the IR evaluator. Yes and No are certified by the relevant
programs of the query's instances (one for a closed query), checked by
recomputing them; Unknown by two assignments, each a model of an instance's
relevant program, with the instance's position. -/
abbrev IRAnswer (Variable Literal Symbol : Type) :=
  Answer (List (GroundProgram Variable Literal Symbol)) (List (GroundProgram Variable Literal Symbol))
    (Nat × Assignment Variable Literal Symbol) (Blocker Variable Literal Symbol)

/-- A note of P2 as a blocker: the finiteness evidence is a termination
argument. -/
def Program.Note.blocker (note : Program.Note Variable Literal Symbol) : Blocker Variable Literal Symbol :=
  ⟨.site note.site, note.path, note.formula, .termination⟩

/-- The blockers of a profile that does not decide. -/
def Profile.blockers : Profile Variable Literal Symbol → List (Blocker Variable Literal Symbol)
  | .undecided blockers => blockers
  | .p2 notes => notes.map Program.Note.blocker
  | _ => []

/-- What the combination reads of an instance's ground program, its models
enumerated once: whether it has one, and those satisfying the conditions. -/
structure Summary (Variable Literal Symbol : Type) where
  ground : GroundProgram Variable Literal Symbol
  hasModel : Bool
  conditioned : List (Assignment Variable Literal Symbol)

/-- An instance's summary. -/
def GroundProgram.summary (ground : GroundProgram Variable Literal Symbol) : Summary Variable Literal Symbol :=
  let models := ground.models
  ⟨ground, !models.isEmpty, models.filter ground.conditionsIn⟩

theorem GroundProgram.summary_hasModel (ground : GroundProgram Variable Literal Symbol) :
    ground.summary.hasModel = !ground.models.isEmpty := rfl

/-- The first model of each instance satisfying the conditions in which the
goal fails, with the instance's position and ground program. -/
def falseWitnesses (summaries : List (Summary Variable Literal Symbol)) :
    List (Nat × GroundProgram Variable Literal Symbol × Assignment Variable Literal Symbol) :=
  summaries.zipIdx.filterMap fun entry =>
    (entry.1.conditioned.find? fun assignment => !entry.1.ground.goalIn assignment).map fun assignment =>
      (entry.2, entry.1.ground, assignment)

/-- The first model of each instance satisfying the conditions in which the
goal holds. -/
def trueWitnesses (summaries : List (Summary Variable Literal Symbol)) :
    List (Nat × GroundProgram Variable Literal Symbol × Assignment Variable Literal Symbol) :=
  summaries.zipIdx.filterMap fun entry =>
    (entry.1.conditioned.find? entry.1.ground.goalIn).map fun assignment => (entry.2, entry.1.ground, assignment)

theorem falseWitnesses_nil {grounds : List (GroundProgram Variable Literal Symbol)}
    (none : falseWitnesses (grounds.map GroundProgram.summary) = []) :
    ∀ ground ∈ grounds, ∀ assignment ∈ ground.conditioned, ground.goalIn assignment = true := by
  intro ground member
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  have inZip : (ground.summary, index) ∈ (grounds.map GroundProgram.summary).zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr (by rw [List.getElem?_map, found]; rfl)
  have := (List.filterMap_eq_nil_iff.mp none) _ inZip
  simp only [Option.map_eq_none_iff] at this
  exact ground.falseWitness_none this

theorem trueWitnesses_nil {grounds : List (GroundProgram Variable Literal Symbol)}
    (none : trueWitnesses (grounds.map GroundProgram.summary) = []) :
    ∀ ground ∈ grounds, ∀ assignment ∈ ground.conditioned, ground.goalIn assignment = false := by
  intro ground member
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  have inZip : (ground.summary, index) ∈ (grounds.map GroundProgram.summary).zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr (by rw [List.getElem?_map, found]; rfl)
  have := (List.filterMap_eq_nil_iff.mp none) _ inZip
  simp only [Option.map_eq_none_iff] at this
  exact ground.trueWitness_none this

theorem summaries_ground {grounds : List (GroundProgram Variable Literal Symbol)} {entry : Summary Variable Literal Symbol × Nat}
    (inZip : entry ∈ (grounds.map GroundProgram.summary).zipIdx) : entry.1.ground ∈ grounds ∧ entry.1 = entry.1.ground.summary := by
  obtain ⟨summary, index⟩ := entry
  have found := List.mem_zipIdx_iff_getElem?.mp inZip
  rw [List.getElem?_map] at found
  cases found' : grounds[index]? with
  | none => rw [found'] at found; cases found
  | some ground =>
      rw [found'] at found
      simp only [Option.map_some, Option.some.injEq] at found
      subst found
      exact ⟨List.mem_of_getElem? found', rfl⟩

theorem falseWitnesses_mem {grounds : List (GroundProgram Variable Literal Symbol)}
    {entry : Nat × GroundProgram Variable Literal Symbol × Assignment Variable Literal Symbol}
    (member : entry ∈ falseWitnesses (grounds.map GroundProgram.summary)) :
    entry.2.1 ∈ grounds ∧ entry.2.2 ∈ entry.2.1.conditioned ∧ entry.2.1.goalIn entry.2.2 = false := by
  obtain ⟨summaryEntry, inZip, produced⟩ := List.mem_filterMap.mp member
  obtain ⟨assignment, found, rfl⟩ := Option.map_eq_some_iff.mp produced
  obtain ⟨groundMember, same⟩ := summaries_ground inZip
  rw [same] at found
  exact ⟨groundMember, summaryEntry.1.ground.falseWitness_some found⟩

theorem trueWitnesses_mem {grounds : List (GroundProgram Variable Literal Symbol)}
    {entry : Nat × GroundProgram Variable Literal Symbol × Assignment Variable Literal Symbol}
    (member : entry ∈ trueWitnesses (grounds.map GroundProgram.summary)) :
    entry.2.1 ∈ grounds ∧ entry.2.2 ∈ entry.2.1.conditioned ∧ entry.2.1.goalIn entry.2.2 = true := by
  obtain ⟨summaryEntry, inZip, produced⟩ := List.mem_filterMap.mp member
  obtain ⟨assignment, found, rfl⟩ := Option.map_eq_some_iff.mp produced
  obtain ⟨groundMember, same⟩ := summaries_ground inZip
  rw [same] at found
  exact ⟨groundMember, summaryEntry.1.ground.trueWitness_some found⟩

namespace Program

variable (program : Program Variable Literal Symbol)

/-- The atoms as formulas, for a blocker. -/
def atomTerms (atoms : List (GAtom Variable Literal Symbol)) : List (Term Variable Literal Symbol) :=
  atoms.map fun atom => .app atom.1 atom.2

/-- The blocker of an Unknown that a rule outside an instance's relevant
program may rule out: the rule, at its head, and the instance's atoms and
markers the witnesses assign. -/
def outsideRule (ground : GroundProgram Variable Literal Symbol) : Blocker Variable Literal Symbol :=
  let atoms := atomTerms (ground.undefinedAtoms ++ ground.markerAtoms)
  match program.unstratified ground.atoms with
  | some (index, rule) => ⟨.site (.head index), [], .app rule.head rule.args, .witnesses atoms⟩
  | none => ⟨.site .goal, [], .truth, .witnesses atoms⟩

/-- The blocker of an instance whose relevant program has no model: the KB
has none, and the atoms and markers of that program are named. -/
def inconsistency (formula : Term Variable Literal Symbol) (ground : GroundProgram Variable Literal Symbol) :
    Blocker Variable Literal Symbol :=
  ⟨.site .goal, [], formula, .consistency (atomTerms (ground.atoms ++ ground.markerAtoms))⟩

/-- **The answer from the instances' ground programs**: Undecided when one has
no model (the KB's inconsistency, named); Yes when the goal holds in every
model satisfying the conditions of every instance; No when it fails in each;
otherwise Unknown, with a model where it holds and one where it fails, each
from an instance whose rules outside are stratified, and Undecided naming a
rule outside when no such pair exists. -/
def combine (formula : Term Variable Literal Symbol) (grounds : List (GroundProgram Variable Literal Symbol)) :
    IRAnswer Variable Literal Symbol :=
  let summaries := grounds.map GroundProgram.summary
  match summaries.find? fun summary => !summary.hasModel with
  | some empty => .undecided [inconsistency formula empty.ground]
  | none =>
      match falseWitnesses summaries with
      | [] => .yes grounds
      | falses@(falseFirst :: _) =>
          match trueWitnesses summaries with
          | [] => .no grounds
          | trues@(trueFirst :: _) =>
              match trues.find? (fun entry => program.outsideStratified entry.2.1.atoms),
                  falses.find? (fun entry => program.outsideStratified entry.2.1.atoms) with
              | some (trueIndex, _, holds), some (falseIndex, _, fails) => .unknown (trueIndex, holds) (falseIndex, fails)
              | none, _ => .undecided [program.outsideRule trueFirst.2.1]
              | _, none => .undecided [program.outsideRule falseFirst.2.1]

variable {program}

/-- **The combination is sound** for a meaning that its instances' ground
programs read: truth when the goal holds in each model of each, falsity when
it fails in each, and independence from two extensible witnesses. -/
theorem combine_sound {formula : Term Variable Literal Symbol} {grounds : List (GroundProgram Variable Literal Symbol)}
    {meaning : Meaning} (truth : (∀ ground ∈ grounds, ∀ assignment ∈ ground.conditioned, ground.goalIn assignment = true) → meaning.truth)
    (falsity : (∀ ground ∈ grounds, ∀ assignment ∈ ground.conditioned, ground.goalIn assignment = false) → meaning.falsity)
    (independence : ∀ trueGround ∈ grounds, ∀ holds ∈ trueGround.conditioned, trueGround.goalIn holds = true →
      program.outsideStratified trueGround.atoms = true → ∀ falseGround ∈ grounds, ∀ fails ∈ falseGround.conditioned,
        falseGround.goalIn fails = false → program.outsideStratified falseGround.atoms = true → meaning.independence) :
    (program.combine formula grounds).Sound meaning := by
  unfold combine
  dsimp only
  cases emptyEq : (grounds.map GroundProgram.summary).find? (fun summary => !summary.hasModel) with
  | some empty => dsimp only; trivial
  | none =>
      dsimp only
      cases falseEq : falseWitnesses (grounds.map GroundProgram.summary) with
      | nil => exact truth (falseWitnesses_nil falseEq)
      | cons falseFirst falseRest =>
          dsimp only
          cases trueEq : trueWitnesses (grounds.map GroundProgram.summary) with
          | nil => exact falsity (trueWitnesses_nil trueEq)
          | cons trueFirst trueRest =>
              dsimp only
              cases trueFound : (trueFirst :: trueRest).find? (fun entry => program.outsideStratified entry.2.1.atoms) with
              | none => dsimp only; trivial
              | some trueEntry =>
                  cases falseFound : (falseFirst :: falseRest).find? (fun entry => program.outsideStratified entry.2.1.atoms) with
                  | none => dsimp only; trivial
                  | some falseEntry =>
                      obtain ⟨trueIndex, trueGround, holds⟩ := trueEntry
                      obtain ⟨falseIndex, falseGround, fails⟩ := falseEntry
                      obtain ⟨trueMember, holdsMember, holdsGoal⟩ :=
                        trueWitnesses_mem (trueEq ▸ List.mem_of_find?_eq_some trueFound)
                      obtain ⟨falseMember, failsMember, failsGoal⟩ :=
                        falseWitnesses_mem (falseEq ▸ List.mem_of_find?_eq_some falseFound)
                      have trueStratified := List.find?_some trueFound
                      have falseStratified := List.find?_some falseFound
                      simp only at trueStratified falseStratified
                      exact independence _ trueMember _ holdsMember holdsGoal trueStratified _ falseMember _
                        failsMember failsGoal falseStratified

/-- **The combination decides** when every instance has a model and every
instance's rules outside are stratified. -/
theorem combine_decided {formula : Term Variable Literal Symbol} {grounds : List (GroundProgram Variable Literal Symbol)}
    (models : ∀ ground ∈ grounds, ground.models ≠ [])
    (stratified : ∀ ground ∈ grounds, program.outsideStratified ground.atoms = true) :
    (program.combine formula grounds).decided = true := by
  unfold combine
  dsimp only
  cases emptyEq : (grounds.map GroundProgram.summary).find? (fun summary => !summary.hasModel) with
  | some empty =>
      have spec := List.find?_some emptyEq
      obtain ⟨ground, member, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some emptyEq)
      rw [GroundProgram.summary_hasModel] at spec
      simp only [Bool.not_not, List.isEmpty_iff] at spec
      exact absurd spec (models _ member)
  | none =>
      dsimp only
      cases falseEq : falseWitnesses (grounds.map GroundProgram.summary) with
      | nil => rfl
      | cons falseFirst falseRest =>
          dsimp only
          cases trueEq : trueWitnesses (grounds.map GroundProgram.summary) with
          | nil => rfl
          | cons trueFirst trueRest =>
              dsimp only
              have trueStratified := stratified _ (trueWitnesses_mem (trueEq ▸ List.mem_cons_self)).1
              have falseStratified := stratified _ (falseWitnesses_mem (falseEq ▸ List.mem_cons_self)).1
              cases trueFound : (trueFirst :: trueRest).find? (fun entry => program.outsideStratified entry.2.1.atoms) with
              | none =>
                  rw [List.find?_eq_none] at trueFound
                  exact absurd trueStratified (trueFound _ List.mem_cons_self)
              | some trueEntry =>
                  cases falseFound : (falseFirst :: falseRest).find? (fun entry => program.outsideStratified entry.2.1.atoms) with
                  | none =>
                      rw [List.find?_eq_none] at falseFound
                      exact absurd falseStratified (falseFound _ List.mem_cons_self)
                  | some falseEntry => obtain ⟨_, _, _⟩ := trueEntry; obtain ⟨_, _, _⟩ := falseEntry; rfl

end Program

/-! ## One closed instance over the key fixpoints -/

namespace Program

section Instance

variable {program : Program Variable Literal Symbol}

/-- The goal holding in every model of the relevant program satisfying the
conditions: it holds in every key fixpoint satisfying them. -/
theorem keyTruth_of_goal (wellFormed : program.WellFormed) (guarded : program.Guarded) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) (closed : Closed program query)
    (closes_ : ∃ n, program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) = true)
    (every : ∀ assignment ∈ (program.groundProgram query closes_).conditioned,
      (program.groundProgram query closes_).goalIn assignment = true) : (program.keyMeaning query).truth := by
  intro markers interp fixed environment context
  have conditionsGround := Closed.conditions_ground closed
  have closedProgram := groundProgram_closed wellFormed queryOk evidence closed.parameters conditionsGround closes_
  obtain ⟨assignment, member, conditionsAgree, goalAgree⟩ := (program.groundProgram query closes_).models_agree closedProgram
    (fixpoint_model wellFormed guarded queryOk evidence closed.parameters conditionsGround closes_ fixed)
  have conditioned : assignment ∈ (program.groundProgram query closes_).conditioned :=
    List.mem_filter.mpr ⟨member, conditionsAgree.mp ((context_iff wellFormed queryOk conditionsGround closes_ environment).mp context)⟩
  exact (formula_iff wellFormed guarded queryOk evidence closed closes_ fixed environment).mpr
    (goalAgree.mpr (every assignment conditioned))

/-- The goal failing in every model satisfying the conditions: it fails in
every key fixpoint satisfying them. -/
theorem keyFalsity_of_goal (wellFormed : program.WellFormed) (guarded : program.Guarded) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) (closed : Closed program query)
    (closes_ : ∃ n, program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) = true)
    (every : ∀ assignment ∈ (program.groundProgram query closes_).conditioned,
      (program.groundProgram query closes_).goalIn assignment = false) : (program.keyMeaning query).falsity := by
  intro markers interp fixed environment context holds
  have conditionsGround := Closed.conditions_ground closed
  have closedProgram := groundProgram_closed wellFormed queryOk evidence closed.parameters conditionsGround closes_
  obtain ⟨assignment, member, conditionsAgree, goalAgree⟩ := (program.groundProgram query closes_).models_agree closedProgram
    (fixpoint_model wellFormed guarded queryOk evidence closed.parameters conditionsGround closes_ fixed)
  have conditioned : assignment ∈ (program.groundProgram query closes_).conditioned :=
    List.mem_filter.mpr ⟨member, conditionsAgree.mp ((context_iff wellFormed queryOk conditionsGround closes_ environment).mp context)⟩
  have goal := goalAgree.mp ((formula_iff wellFormed guarded queryOk evidence closed closes_ fixed environment).mp holds)
  rw [every assignment conditioned] at goal
  cases goal

/-- **A witness extends to a key fixpoint**: a model of the relevant program
satisfying the conditions, the rules outside stratified, gives a key fixpoint
satisfying the conditions with the witness's truth of the goal. -/
theorem witness_fixpoint (wellFormed : program.WellFormed) (guarded : program.Guarded) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) (closed : Closed program query)
    (closes_ : ∃ n, program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) = true)
    (stratified : program.outsideStratified (program.groundProgram query closes_).atoms = true)
    {assignment : Assignment Variable Literal Symbol}
    (isModel : (program.groundProgram query closes_).isModel assignment.1 assignment.2 = true)
    (conditionsTrue : (program.groundProgram query closes_).conditionsIn assignment = true) :
    ∃ markers interp, program.KeyFixpoint markers interp ∧ ∀ environment,
      (program.keyModel markers interp).ContextHolds environment query.context ∧
        ((program.keyModel markers interp).Satisfies environment query.formula ↔
          (program.groundProgram query closes_).goalIn assignment = true) := by
  have conditionsGround := Closed.conditions_ground closed
  have closedProgram := groundProgram_closed wellFormed queryOk evidence closed.parameters conditionsGround closes_
  obtain ⟨markers, interp, fixed, atomsAgree, markersAgree⟩ := extends_model wellFormed guarded queryOk evidence
    closed.parameters conditionsGround closes_ stratified (((program.groundProgram query closes_).isModel_iff _ _).mp isModel)
  obtain ⟨conditionsAgree, goalAgree⟩ := (program.groundProgram query closes_).agree_query closedProgram atomsAgree markersAgree
  refine ⟨markers, interp, fixed, fun environment => ⟨?_, ?_⟩⟩
  · exact (context_iff wellFormed queryOk conditionsGround closes_ environment).mpr
      (conditionsAgree.mpr (((program.groundProgram query closes_).conditionsIn_iff _).mp conditionsTrue))
  · rw [formula_iff wellFormed guarded queryOk evidence closed closes_ fixed environment, goalAgree,
      (program.groundProgram query closes_).goalIn_iff]

/-- A relevant program with no model: there is no model of the completion
realizing the signature. -/
theorem no_models_of_empty [FreshNames Variable] (wellFormed : program.WellFormed) (guarded : program.Guarded)
    {query : Query Variable Literal Symbol} (queryOk : QueryOk program query) (evidence : program.notes query = [])
    (closed : Closed program query)
    (closes_ : ∃ n, program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) = true)
    (empty : (program.groundProgram query closes_).models = []) :
    ¬ ∃ (Value : Type) (model : Model Literal Symbol Value program.hoApply), program.Models model := by
  rintro ⟨Value, model, models⟩
  have conditionsGround := Closed.conditions_ground closed
  have closedProgram := groundProgram_closed wellFormed queryOk evidence closed.parameters conditionsGround closes_
  obtain ⟨assignment, member, _, _⟩ := (program.groundProgram query closes_).models_agree closedProgram
    (fixpoint_model wellFormed guarded queryOk evidence closed.parameters conditionsGround closes_
      (herbrand_fixpoint wellFormed guarded models))
  rw [empty] at member
  cases member

end Instance

/-! ## The answer of a query -/

variable (program : Program Variable Literal Symbol)

theorem closes_of_decides {query : Query Variable Literal Symbol} (decided : (program.classifyClosed query).decides = true) :
    ∃ n, program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) = true := by
  obtain ⟨wellFormed, _, queryOk, evidence, _, noParameters⟩ := p1_parts decided
  exact closes wellFormed queryOk evidence noParameters

theorem instance_decides {query : Query Variable Literal Symbol} (some : query.parameters.isEmpty = false)
    (decided : (program.classify query).decides = true) {values : Variable → Term Variable Literal Symbol}
    (member : values ∈ program.splitValues query) : (program.classifyClosed (query.instantiate values)).decides = true :=
  (program.classify_split (by simpa using some) decided).2.2.2 values member

theorem closed_decides {query : Query Variable Literal Symbol} (none : query.parameters.isEmpty = true)
    (decided : (program.classify query).decides = true) : (program.classifyClosed query).decides = true := by
  rwa [program.classify_closed (List.isEmpty_iff.mp none)] at decided

/-- The ground relevant programs of a P0 or P1 query's instances: the query's
own when it is closed, one per instance of its split otherwise. -/
def instances (query : Query Variable Literal Symbol) (decided : (program.classify query).decides = true) :
    List (GroundProgram Variable Literal Symbol) :=
  if none : query.parameters.isEmpty = true then
    [program.groundProgram query (program.closes_of_decides (program.closed_decides none decided))]
  else
    (program.splitValues query).attach.map fun entry =>
      program.groundProgram (query.instantiate entry.1)
        (program.closes_of_decides (program.instance_decides (by simpa using none) decided entry.2))

/-- **A query's answer**: a query of P0 or P1 decided exactly on its
instances' relevant programs, with no fuel; any other query Undecided with its
profile's blockers, before anything runs. -/
def decideQuery (query : Query Variable Literal Symbol) : IRAnswer Variable Literal Symbol :=
  if decided : (program.classify query).decides = true then program.combine query.formula (program.instances query decided)
  else .undecided (program.classify query).blockers

/-! ## The answer's guarantees -/

section Guarantees

variable {program} [FreshNames Variable]

omit [FreshNames Variable] in
/-- The parts P0 or P1 gives an instance. -/
theorem instance_parts {query : Query Variable Literal Symbol} (decided : (program.classifyClosed query).decides = true) :
    program.WellFormed ∧ program.Guarded ∧ QueryOk program query ∧ program.notes query = [] ∧ Closed program query := by
  obtain ⟨wellFormed, guarded, queryOk, evidence, answers, noParameters⟩ := p1_parts decided
  exact ⟨wellFormed, guarded, queryOk, evidence, closed_of_parts queryOk answers noParameters⟩

omit [FreshNames Variable] in
/-- The instances of a P0 or P1 query, read back: a closed query's one
ground program is its own; each ground program of a split is an instance's. -/
theorem instances_cases {query : Query Variable Literal Symbol} (decided : (program.classify query).decides = true) :
    (∃ none : query.parameters.isEmpty = true, program.instances query decided =
        [program.groundProgram query (program.closes_of_decides (program.closed_decides none decided))]) ∨
      ∃ some : query.parameters.isEmpty = false, ∀ ground, ground ∈ program.instances query decided ↔
        ∃ values, ∃ member : values ∈ program.splitValues query, ground = program.groundProgram (query.instantiate values)
          (program.closes_of_decides (program.instance_decides some decided member)) := by
  unfold instances
  split
  · rename_i none
    exact .inl ⟨none, rfl⟩
  · rename_i some
    refine .inr ⟨by simpa using some, fun ground => ⟨fun member => ?_, fun ⟨values, member, same⟩ => ?_⟩⟩
    · obtain ⟨⟨values, valuesMember⟩, _, rfl⟩ := List.mem_map.mp member
      exact ⟨values, valuesMember, rfl⟩
    · subst same
      exact List.mem_map.mpr ⟨⟨values, member⟩, List.mem_attach _ _, rfl⟩

/-- **Yes from the instances**: the goal holding in every model satisfying
the conditions of every instance's relevant program, it holds in every model
of the completion satisfying the query's context. -/
theorem instances_truth {query : Query Variable Literal Symbol} (decided : (program.classify query).decides = true)
    (every : ∀ ground ∈ program.instances query decided, ∀ assignment ∈ ground.conditioned, ground.goalIn assignment = true) :
    (program.meaning query).truth := by
  rcases instances_cases decided with ⟨none, same⟩ | ⟨some, members⟩
  · obtain ⟨wellFormed, guarded, queryOk, evidence, closed⟩ := instance_parts (program.closed_decides none decided)
    rw [same] at every
    exact ((program.herbrand wellFormed guarded closed).1).mpr
      (keyTruth_of_goal wellFormed guarded queryOk evidence closed _ (every _ List.mem_cons_self))
  · refine ((program.meaning_classify (by simpa using some) decided).1).mpr fun values member => ?_
    obtain ⟨wellFormed, guarded, queryOk, evidence, closed⟩ := instance_parts (program.instance_decides some decided member)
    exact ((program.herbrand wellFormed guarded closed).1).mpr
      (keyTruth_of_goal wellFormed guarded queryOk evidence closed _ (every _ ((members _).mpr ⟨values, member, rfl⟩)))

/-- **No from the instances**: the goal failing in every model satisfying the
conditions of every instance's relevant program. -/
theorem instances_falsity {query : Query Variable Literal Symbol} (decided : (program.classify query).decides = true)
    (every : ∀ ground ∈ program.instances query decided, ∀ assignment ∈ ground.conditioned, ground.goalIn assignment = false) :
    (program.meaning query).falsity := by
  rcases instances_cases decided with ⟨none, same⟩ | ⟨some, members⟩
  · obtain ⟨wellFormed, guarded, queryOk, evidence, closed⟩ := instance_parts (program.closed_decides none decided)
    rw [same] at every
    exact ((program.herbrand wellFormed guarded closed).2.1).mpr
      (keyFalsity_of_goal wellFormed guarded queryOk evidence closed _ (every _ List.mem_cons_self))
  · refine ((program.meaning_classify (by simpa using some) decided).2.1).mpr fun values member => ?_
    obtain ⟨wellFormed, guarded, queryOk, evidence, closed⟩ := instance_parts (program.instance_decides some decided member)
    exact ((program.herbrand wellFormed guarded closed).2.1).mpr
      (keyFalsity_of_goal wellFormed guarded queryOk evidence closed _ (every _ ((members _).mpr ⟨values, member, rfl⟩)))

/-- **A witness from an instance**: an assignment that is a model of an
instance's relevant program and satisfies its conditions, the rules outside
stratified, shows the goal's truth at that instance can be its value: with
the goal true, the query is not false; with it false, not true. -/
theorem instances_witness {query : Query Variable Literal Symbol} (decided : (program.classify query).decides = true)
    {ground : GroundProgram Variable Literal Symbol} (member : ground ∈ program.instances query decided)
    (stratified : program.outsideStratified ground.atoms = true) {assignment : Assignment Variable Literal Symbol}
    (isModel : ground.isModel assignment.1 assignment.2 = true) (conditions : ground.conditionsIn assignment = true) :
    (ground.goalIn assignment = true → ¬ (program.meaning query).falsity) ∧
      (ground.goalIn assignment = false → ¬ (program.meaning query).truth) := by
  let anyKey : Environment Variable (Key Literal Symbol) := fun _ => .truth False
  rcases instances_cases decided with ⟨none, same⟩ | ⟨some, members⟩
  · rw [same] at member
    rcases List.mem_singleton.mp member with rfl
    obtain ⟨wellFormed, guarded, queryOk, evidence, closed⟩ := instance_parts (program.closed_decides none decided)
    obtain ⟨markers, interp, fixed, spec⟩ :=
      witness_fixpoint wellFormed guarded queryOk evidence closed _ stratified isModel conditions
    refine ⟨fun holds falsity => ?_, fun fails truth => ?_⟩
    · exact ((program.herbrand wellFormed guarded closed).2.1).mp falsity markers interp fixed anyKey (spec anyKey).1
        ((spec anyKey).2.mpr holds)
    · have satisfied := ((program.herbrand wellFormed guarded closed).1).mp truth markers interp fixed anyKey (spec anyKey).1
      rw [(spec anyKey).2, fails] at satisfied; cases satisfied
  · obtain ⟨values, valuesMember, rfl⟩ := (members _).mp member
    obtain ⟨truthSplit, falsitySplit, _⟩ := program.meaning_classify (by simpa using some) decided
    obtain ⟨wellFormed, guarded, queryOk, evidence, closed⟩ := instance_parts (program.instance_decides some decided valuesMember)
    obtain ⟨markers, interp, fixed, spec⟩ :=
      witness_fixpoint wellFormed guarded queryOk evidence closed _ stratified isModel conditions
    refine ⟨fun holds falsity => ?_, fun fails truth => ?_⟩
    · exact ((program.herbrand wellFormed guarded closed).2.1).mp (falsitySplit.mp falsity values valuesMember) markers interp
        fixed anyKey (spec anyKey).1 ((spec anyKey).2.mpr holds)
    · have satisfied := ((program.herbrand wellFormed guarded closed).1).mp (truthSplit.mp truth values valuesMember) markers
        interp fixed anyKey (spec anyKey).1
      rw [(spec anyKey).2, fails] at satisfied; cases satisfied

/-- **Unknown from the instances**: a witness where the goal holds and one
where it fails, each extensible. -/
theorem instances_independence {query : Query Variable Literal Symbol} (decided : (program.classify query).decides = true)
    {trueGround falseGround : GroundProgram Variable Literal Symbol}
    (trueMember : trueGround ∈ program.instances query decided) (falseMember : falseGround ∈ program.instances query decided)
    (trueStratified : program.outsideStratified trueGround.atoms = true)
    (falseStratified : program.outsideStratified falseGround.atoms = true)
    {holds fails : Assignment Variable Literal Symbol}
    (holdsModel : trueGround.isModel holds.1 holds.2 = true) (holdsConditions : trueGround.conditionsIn holds = true)
    (holdsGoal : trueGround.goalIn holds = true)
    (failsModel : falseGround.isModel fails.1 fails.2 = true) (failsConditions : falseGround.conditionsIn fails = true)
    (failsGoal : falseGround.goalIn fails = false) :
    (program.meaning query).independence := by
  have notFalsity := (instances_witness decided trueMember trueStratified holdsModel holdsConditions).1 holdsGoal
  have notTruth := (instances_witness decided falseMember falseStratified failsModel failsConditions).2 failsGoal
  -- Independence over the models: one satisfying the context with the goal, one without.
  refine ⟨?_, ?_⟩
  · refine Classical.byContradiction fun none => notFalsity fun Value model models environment context holdsGoal' => ?_
    exact none ⟨Value, model, models, environment, context, holdsGoal'⟩
  · refine Classical.byContradiction fun none => notTruth fun Value model models environment context => ?_
    exact Classical.byContradiction fun fails' => none ⟨Value, model, models, environment, context, fails'⟩

/-- **Every answer is sound**: it means what it says over the models of the
completion realizing the signature. No hypothesis: the P1 branch reads its
evidence from the classification, and Unknown checks the rules outside. -/
theorem decideQuery_sound (query : Query Variable Literal Symbol) : (program.decideQuery query).Sound (program.meaning query) := by
  unfold decideQuery
  split
  · rename_i decided
    refine combine_sound (instances_truth decided) (instances_falsity decided) (fun trueGround trueMember holds holdsMember
      holdsGoal trueStratified falseGround falseMember fails failsMember failsGoal falseStratified => ?_)
    obtain ⟨holdsModel, holdsConditions⟩ := trueGround.conditioned_parts holdsMember
    obtain ⟨failsModel, failsConditions⟩ := falseGround.conditioned_parts failsMember
    exact instances_independence decided trueMember falseMember trueStratified falseStratified holdsModel holdsConditions
      holdsGoal failsModel failsConditions failsGoal
  · trivial

/-- Every instance's relevant program has a model when the completion has one
realizing the signature. -/
theorem instances_models {query : Query Variable Literal Symbol} (decided : (program.classify query).decides = true)
    (consistent : ∃ (Value : Type) (model : Model Literal Symbol Value program.hoApply), program.Models model) :
    ∀ ground ∈ program.instances query decided, ground.models ≠ [] := by
  intro ground member empty
  unfold instances at member
  split at member
  · rename_i none
    rcases List.mem_singleton.mp member with rfl
    obtain ⟨wellFormed, guarded, queryOk, evidence, closed⟩ := instance_parts (program.closed_decides none decided)
    exact no_models_of_empty wellFormed guarded queryOk evidence closed _ empty consistent
  · rename_i some
    obtain ⟨⟨values, valuesMember⟩, _, rfl⟩ := List.mem_map.mp member
    obtain ⟨wellFormed, guarded, queryOk, evidence, closed⟩ :=
      instance_parts (program.instance_decides (by simpa using some) decided valuesMember)
    exact no_models_of_empty wellFormed guarded queryOk evidence closed _ empty consistent

/-- **Undecided only for the KB's inconsistency**: a query of P0 or P1 whose
instances' rules outside are stratified answers Yes, No, or Unknown when the
completion has a model realizing the signature. -/
theorem decideQuery_decided {query : Query Variable Literal Symbol} (decided : (program.classify query).decides = true)
    (stratified : ∀ ground ∈ program.instances query decided, program.outsideStratified ground.atoms = true)
    (consistent : ∃ (Value : Type) (model : Model Literal Symbol Value program.hoApply), program.Models model) :
    (program.decideQuery query).decided = true := by
  unfold decideQuery
  split
  · exact combine_decided (instances_models decided consistent) stratified
  · rename_i notDecided
    exact absurd decided notDecided

/-- **Exactness**: a query of P0 or P1, its instances' rules outside
stratified, on a KB with a model: Yes exactly when the goal holds in every
model and fails in none, No exactly when it fails in every model and holds in
none, Unknown exactly when it holds in one and fails in another. -/
theorem decideQuery_exact {query : Query Variable Literal Symbol} (decided : (program.classify query).decides = true)
    (stratified : ∀ ground ∈ program.instances query decided, program.outsideStratified ground.atoms = true)
    (consistent : ∃ (Value : Type) (model : Model Literal Symbol Value program.hoApply), program.Models model) :
    ((program.meaning query).truth ∧ ¬ (program.meaning query).falsity → ∃ grounds, program.decideQuery query = .yes grounds) ∧
      ((program.meaning query).falsity ∧ ¬ (program.meaning query).truth → ∃ grounds, program.decideQuery query = .no grounds) ∧
      ((program.meaning query).independence → ∃ holds fails, program.decideQuery query = .unknown holds fails) := by
  have sound := decideQuery_sound (program := program) query
  have isDecided := decideQuery_decided decided stratified consistent
  cases answered : program.decideQuery query with
  | yes grounds =>
      rw [answered] at sound
      exact ⟨fun _ => ⟨grounds, rfl⟩, fun ⟨_, notTruth⟩ => absurd sound notTruth,
        fun independent => absurd sound (Meaning.ofModels_independent independent).1⟩
  | no grounds =>
      rw [answered] at sound
      exact ⟨fun ⟨_, notFalsity⟩ => absurd sound notFalsity, fun _ => ⟨grounds, rfl⟩,
        fun independent => absurd sound (Meaning.ofModels_independent independent).2⟩
  | unknown holds fails =>
      rw [answered] at sound
      exact ⟨fun ⟨truth, _⟩ => absurd truth (Meaning.ofModels_independent sound).1,
        fun ⟨falsity, _⟩ => absurd falsity (Meaning.ofModels_independent sound).2, fun _ => ⟨holds, fails, rfl⟩⟩
  | undecided blockers =>
      rw [answered] at isDecided
      cases isDecided

end Guarantees

/-! ## The KB-level consistency check, beside the queries -/

/-- The KB-level roots: the ground heads of the rules whose head is on a cycle
through NAF and whose body reads an atom (the rules' bodies may have names of
their own). A fact, or a rule reading no atom, is on no cycle of atoms. -/
def cycleRoots : List (Goal Variable Literal Symbol) :=
  let cyclic := program.nafCycleSymbols program.rules
  ((program.rules.filterMap fun rule =>
    if (namesOf rule.args).isEmpty && cyclic.contains rule.head &&
        rule.body.any (fun | .call _ _ | .naf _ _ => true | _ => false) then
      some (rule.head, rule.args)
    else none).eraseDups).map
    fun atom => .call atom.1 atom.2

/-- The KB-level query: the cycle roots as goals, the denials joining as they
join every query. -/
def consistencyQuery : Query Variable Literal Symbol := ⟨[], program.cycleRoots, []⟩

/-- The pieces of a ground program: its atoms and markers grouped by the
rules and denials that link them, each group closed under the links (a rule's
head with its body's atoms and markers, a denial's atoms and markers with
each other). Each piece is checked at run time before it is used. -/
def pieces (ground : GroundProgram Variable Literal Symbol) : List (List (GAtom Variable Literal Symbol)) :=
  let links := ground.rules.map (fun entry => entry.1 :: entry.2.1 ++ entry.2.2.1 ++ entry.2.2.2) ++
    ground.denials.map fun body => body.1 ++ body.2.1 ++ body.2.2
  links.foldl (fun groups link =>
    let touching := groups.filter fun group => group.any link.contains
    (link ++ touching.flatten).eraseDups :: groups.filter fun group => !group.any link.contains) []

/-- A piece of a ground program, as a ground program: its atoms, every rule
concluding one of them, and every denial touching it. -/
def restrict (ground : GroundProgram Variable Literal Symbol) (piece : List (GAtom Variable Literal Symbol)) :
    GroundProgram Variable Literal Symbol :=
  ⟨ground.atoms.filter piece.contains, ground.rules.filter fun entry => piece.contains entry.1,
    ground.denials.filter (fun body => (body.1 ++ body.2.1 ++ body.2.2).any piece.contains), [], ([], [], []), true⟩

/-- A piece closed under its rules and denials: their calls' and NAF
literals' atoms are its own, and every denial touching it lies within it. -/
def pieceClosed (ground : GroundProgram Variable Literal Symbol) (piece : List (GAtom Variable Literal Symbol)) : Bool :=
  let sub := restrict ground piece
  (sub.rules.all fun entry => sub.atoms.contains entry.1 && (entry.2.1 ++ entry.2.2.1).all sub.atoms.contains) &&
    sub.denials.all fun body => (body.1 ++ body.2.1).all sub.atoms.contains

/-- A denial with no atom and no marker: it holds in every assignment. -/
def _root_.AnthillModKbSpec.IR.GroundProgram.emptyDenial (ground : GroundProgram Variable Literal Symbol) : Bool :=
  ground.denials.any fun body => body.1.isEmpty && body.2.1.isEmpty && body.2.2.isEmpty

/-- The inconsistency a ground program shows, if any: a denial with no atom,
or a closed piece with no model, its atoms and markers named. -/
def inconsistencyOf (formula : Term Variable Literal Symbol) (ground : GroundProgram Variable Literal Symbol) :
    Option (Blocker Variable Literal Symbol) :=
  if ground.emptyDenial then some ⟨.site .goal, [], formula, .consistency []⟩
  else
    ((pieces ground).find? fun piece => pieceClosed ground piece && !(restrict ground piece).hasModel).map fun piece =>
      ⟨.site .goal, [], formula, .consistency (atomTerms piece)⟩

/-- The KB-level query of one root. -/
def rootQuery (root : Goal Variable Literal Symbol) : Query Variable Literal Symbol := ⟨[], [root], []⟩

/-- The inconsistency a KB-level query shows: none when it is not P1. -/
def queryInconsistency (query : Query Variable Literal Symbol) : Option (Blocker Variable Literal Symbol) :=
  if decided : (program.classifyClosed query).decides = true then
    inconsistencyOf query.formula (program.groundProgram query (program.closes_of_decides decided))
  else none

/-- The KB-level roots whose own query is P1. -/
def checkableRoots : List (Goal Variable Literal Symbol) :=
  program.cycleRoots.filter fun root => (program.classifyClosed (rootQuery root)).decides

/-- **The KB-level check** (decided with the user, 2026-11-18): the ground
rules on NAF cycles, with the denials, decided once per KB beside the queries.
Their joint relevant program is split into pieces, each searched for one model.
When the joint query is not P1, the roots whose own query is P1 are checked
jointly, and each alone when that query is not P1 either. A piece with no
model shows that the KB has none: a blocker naming its atoms. -/
def kbCheck : Option (Blocker Variable Literal Symbol) :=
  let joint := program.consistencyQuery
  if decided : (program.classifyClosed joint).decides = true then
    inconsistencyOf joint.formula (program.groundProgram joint (program.closes_of_decides decided))
  else
    let checkable := program.checkableRoots
    let together : Query Variable Literal Symbol := ⟨[], checkable, []⟩
    if decidedTogether : (program.classifyClosed together).decides = true then
      inconsistencyOf together.formula (program.groundProgram together (program.closes_of_decides decidedTogether))
    else checkable.findSome? fun root => program.queryInconsistency (rootQuery root)

/-- **The exact evaluator's answer**: Undecided when the KB-level check finds
the KB inconsistent; otherwise the query's own answer (`decideQuery`), a P2
query's Undecided before anything runs. A host computes the check once per KB
snapshot; `decideWithin` (`IR/Budgeted`) answers P2 within the fuel. -/
def answer (query : Query Variable Literal Symbol) : IRAnswer Variable Literal Symbol :=
  match program.kbCheck with
  | some blocker => .undecided [blocker]
  | none => program.decideQuery query

section KB

variable {program} [FreshNames Variable]

omit [FreshNames Variable] in
/-- A model of a ground program is a model of each of its pieces. -/
theorem restrict_model {ground : GroundProgram Variable Literal Symbol} {piece : List (GAtom Variable Literal Symbol)}
    {closed marked : GAtom Variable Literal Symbol → Prop} (model : ground.Model closed marked) :
    (restrict ground piece).Model closed marked := by
  refine ⟨fun atom member => ?_, fun body member => model.2 body (List.mem_filter.mp member).1⟩
  obtain ⟨inAtoms, inPiece⟩ := List.mem_filter.mp member
  rw [model.1 atom inAtoms]
  constructor
  · rintro ⟨body, bodyMember, holds⟩
    exact ⟨body, List.mem_filter.mpr ⟨bodyMember, inPiece⟩, holds⟩
  · rintro ⟨body, bodyMember, holds⟩
    exact ⟨body, (List.mem_filter.mp bodyMember).1, holds⟩

omit [FreshNames Variable] in
/-- A closed piece is a closed ground program. -/
theorem restrict_closed {ground : GroundProgram Variable Literal Symbol} {piece : List (GAtom Variable Literal Symbol)}
    (closedPiece : pieceClosed ground piece = true) : (restrict ground piece).Closed := by
  simp only [pieceClosed, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, List.mem_append] at closedPiece
  obtain ⟨rulesIn, denialsIn⟩ := closedPiece
  refine ⟨fun entry member => ⟨(rulesIn entry member).1, fun atom inside => (rulesIn entry member).2 atom inside⟩,
    fun body member atom inside => ?_⟩
  rcases List.mem_append.mp member with fromDenials | fromRest
  · exact denialsIn body fromDenials atom inside
  · simp only [restrict, List.mem_cons, List.not_mem_nil, or_false] at fromRest
    subst fromRest
    simp at inside

omit [FreshNames Variable] in
/-- A ground program with a model shows no inconsistency. -/
theorem inconsistencyOf_none {formula : Term Variable Literal Symbol} {ground : GroundProgram Variable Literal Symbol}
    {closed marked : GAtom Variable Literal Symbol → Prop} (model : ground.Model closed marked) :
    inconsistencyOf formula ground = none := by
  unfold inconsistencyOf
  have noEmpty : ground.emptyDenial = false := by
    cases empty : ground.emptyDenial
    · rfl
    · simp only [GroundProgram.emptyDenial, List.any_eq_true, Bool.and_eq_true, List.isEmpty_iff] at empty
      obtain ⟨body, member, ⟨calls, nafs⟩, marks⟩ := empty
      exact absurd ⟨by simp [calls], by simp [nafs], by simp [marks]⟩ (model.2 body member)
  rw [noEmpty]
  simp only [Bool.false_eq_true, ite_false, Option.map_eq_none_iff, List.find?_eq_none, Bool.and_eq_true,
    Bool.not_eq_true', not_and, Bool.not_eq_false]
  intro piece _ closedPiece
  obtain ⟨candidate, member, _, _⟩ := (restrict ground piece).models_complete (restrict_closed closedPiece)
    (restrict_model model)
  obtain ⟨inCandidates, isModel⟩ := List.mem_filter.mp member
  exact (restrict ground piece).hasModel_iff.mpr ⟨candidate, inCandidates, isModel⟩

/-- A KB with a model passes the KB-level check. -/
theorem kbCheck_of_consistent
    (consistent : ∃ (Value : Type) (model : Model Literal Symbol Value program.hoApply), program.Models model) :
    program.kbCheck = none := by
  have decidedNone : ∀ (query : Query Variable Literal Symbol) (decided : (program.classifyClosed query).decides = true),
      inconsistencyOf query.formula (program.groundProgram query (program.closes_of_decides decided)) = none := by
    intro query decided
    obtain ⟨wellFormed, guarded, queryOk, evidence, closed⟩ := instance_parts decided
    obtain ⟨Value, model, models⟩ := consistent
    exact inconsistencyOf_none (fixpoint_model wellFormed guarded queryOk evidence closed.parameters
      (Closed.conditions_ground closed) _ (herbrand_fixpoint wellFormed guarded models))
  have queryNone : ∀ query : Query Variable Literal Symbol, program.queryInconsistency query = none := by
    intro query
    unfold queryInconsistency
    split
    · rename_i decided
      exact decidedNone _ decided
    · rfl
  unfold kbCheck
  dsimp only
  split
  · rename_i decided
    exact decidedNone _ decided
  · split
    · rename_i decided
      exact decidedNone _ decided
    · rw [List.findSome?_eq_none_iff]
      intro root _
      exact queryNone _

/-- **Every answer is sound.** -/
theorem answer_sound (query : Query Variable Literal Symbol) : (program.answer query).Sound (program.meaning query) := by
  unfold answer
  split
  · trivial
  · exact decideQuery_sound query

/-- **Undecided only for the KB's inconsistency**: a query of P0 or P1 whose
instances' rules outside are stratified answers Yes, No, or Unknown when the
completion has a model realizing the signature. -/
theorem answer_decided {query : Query Variable Literal Symbol} (decided : (program.classify query).decides = true)
    (stratified : ∀ ground ∈ program.instances query decided, program.outsideStratified ground.atoms = true)
    (consistent : ∃ (Value : Type) (model : Model Literal Symbol Value program.hoApply), program.Models model) :
    (program.answer query).decided = true := by
  unfold answer
  rw [kbCheck_of_consistent consistent]
  exact decideQuery_decided decided stratified consistent

/-- **Exactness**: a query of P0 or P1, its instances' rules outside
stratified, on a KB with a model: Yes exactly when the goal holds in every
model and fails in none, No exactly when it fails in every model and holds in
none, Unknown exactly when it holds in one and fails in another. -/
theorem answer_exact {query : Query Variable Literal Symbol} (decided : (program.classify query).decides = true)
    (stratified : ∀ ground ∈ program.instances query decided, program.outsideStratified ground.atoms = true)
    (consistent : ∃ (Value : Type) (model : Model Literal Symbol Value program.hoApply), program.Models model) :
    ((program.meaning query).truth ∧ ¬ (program.meaning query).falsity → ∃ grounds, program.answer query = .yes grounds) ∧
      ((program.meaning query).falsity ∧ ¬ (program.meaning query).truth → ∃ grounds, program.answer query = .no grounds) ∧
      ((program.meaning query).independence → ∃ holds fails, program.answer query = .unknown holds fails) := by
  have same : program.answer query = program.decideQuery query := by
    unfold answer; rw [kbCheck_of_consistent consistent]
  rw [same]
  exact decideQuery_exact decided stratified consistent

end KB

/-! ## Certificates and their checks -/

/-- **An Unknown's certificate, checked**: each witness assigns only its
instance's relevant atoms and markers, is a model of the instance's relevant
program, recomputed (a fixpoint of its ground clauses with every denial body
false, as S24's `groundFixpoint` checks a ground program's), satisfies the
conditions, and holds the goal true and false respectively; and the rules
outside both instances' relevant programs are stratified. -/
def checkUnknown (query : Query Variable Literal Symbol) (holds fails : Nat × Assignment Variable Literal Symbol) : Bool :=
  if decided : (program.classify query).decides = true then
    match (program.instances query decided)[holds.1]?, (program.instances query decided)[fails.1]? with
    | some trueGround, some falseGround =>
        (holds.2.1.all trueGround.atoms.contains && holds.2.2.all trueGround.markerAtoms.contains &&
          fails.2.1.all falseGround.atoms.contains && fails.2.2.all falseGround.markerAtoms.contains) &&
        trueGround.isModel holds.2.1 holds.2.2 && trueGround.conditionsIn holds.2 && trueGround.goalIn holds.2 &&
          program.outsideStratified trueGround.atoms &&
        falseGround.isModel fails.2.1 fails.2.2 && falseGround.conditionsIn fails.2 && !falseGround.goalIn fails.2 &&
          program.outsideStratified falseGround.atoms
    | _, _ => false
  else false

attribute [local instance] groundProgramEq in
/-- **A Yes or a No's certificate, checked by recomputation**: the relevant
programs are the query's instances', recomputed, each with a model, the
KB-level check passing, and the goal holds (Yes) or fails (No) in every model
of each that satisfies the conditions. -/
def checkByPrograms (query : Query Variable Literal Symbol) (yes : Bool) (grounds : List (GroundProgram Variable Literal Symbol)) :
    Bool :=
  if decided : (program.classify query).decides = true then
    decide (program.instances query decided = grounds) && program.kbCheck.isNone &&
      grounds.all fun ground =>
        let summary := ground.summary
        summary.hasModel && summary.conditioned.all fun assignment => ground.goalIn assignment == yes
  else false

/-- The certificate of an answer, checked: Yes and No by recomputation,
Unknown by its two witnesses; Undecided has none. -/
def checkAnswer (query : Query Variable Literal Symbol) : IRAnswer Variable Literal Symbol → Bool
  | .yes grounds => program.checkByPrograms query true grounds
  | .no grounds => program.checkByPrograms query false grounds
  | .unknown holds fails => program.checkUnknown query holds fails
  | .undecided _ => false

section Checks

variable {program} [FreshNames Variable]

/-- **An Unknown's checked certificate is sound.** -/
theorem checkUnknown_sound {query : Query Variable Literal Symbol} {holds fails : Nat × Assignment Variable Literal Symbol}
    (checked : program.checkUnknown query holds fails = true) : (program.meaning query).independence := by
  unfold checkUnknown at checked
  split at checked
  · rename_i decided
    split at checked
    · rename_i trueGround falseGround trueFound falseFound
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at checked
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, holdsModel⟩, holdsConditions⟩, holdsGoal⟩, trueStratified⟩, failsModel⟩, failsConditions⟩, failsGoal⟩,
        falseStratified⟩ := checked
      exact instances_independence decided (List.mem_of_getElem? trueFound) (List.mem_of_getElem? falseFound) trueStratified
        falseStratified holdsModel holdsConditions holdsGoal failsModel failsConditions failsGoal
    · cases checked
  · cases checked

attribute [local instance] groundProgramEq in
/-- **A Yes or a No's checked certificate is sound.** -/
theorem checkByPrograms_sound {query : Query Variable Literal Symbol} {yes : Bool}
    {grounds : List (GroundProgram Variable Literal Symbol)} (checked : program.checkByPrograms query yes grounds = true) :
    (yes = true → (program.meaning query).truth) ∧ (yes = false → (program.meaning query).falsity) := by
  unfold checkByPrograms at checked
  split at checked
  · rename_i decided
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at checked
    obtain ⟨⟨same, _⟩, every⟩ := checked
    have same := of_decide_eq_true same
    subst same
    exact ⟨fun isYes => instances_truth decided fun ground member assignment inside =>
        isYes ▸ (every ground member).2 assignment inside,
      fun isNo => instances_falsity decided fun ground member assignment inside =>
        isNo ▸ (every ground member).2 assignment inside⟩
  · cases checked

/-- **A checked certificate is sound**: the answer it certifies means what
it says. -/
theorem checkAnswer_sound {query : Query Variable Literal Symbol} {answer : IRAnswer Variable Literal Symbol}
    (checked : program.checkAnswer query answer = true) : answer.Sound (program.meaning query) := by
  cases answer with
  | yes grounds => exact (checkByPrograms_sound checked).1 rfl
  | no grounds => exact (checkByPrograms_sound checked).2 rfl
  | unknown holds fails => exact checkUnknown_sound checked
  | undecided _ => trivial

end Checks

end Program

end AnthillModKbSpec.IR
