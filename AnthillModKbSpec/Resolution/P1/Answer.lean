import AnthillModKbSpec.Resolution.Answer
import AnthillModKbSpec.Resolution.P0.Open
import AnthillModKbSpec.Resolution.P1.Negation

/-! # The module's answer over the completion (S22)

`Setup.answer` answers a query against a completed program: Yes, No,
Unknown, or Undecided with its blockers. All four are about the models of the
completion with complement NAF that realize the admission signature
(`Setup.meaning`), and each is sound (`Setup.answer_sound`):

1. **The fast run.** The left strategy with evidence-first NAF, with the open
   marker: a goal that reads as a marker atom, or a NAF whose operand reaches
   an open atom through the program's clauses, is reported `opened`, and no
   refutation is searched for it. A success, exported and checked against the completed
   snapshot, is **Yes**.
2. **Witnesses.** A run that ended `opened`, for a query with no assumptions,
   tries candidate assignments of every open atom the goal reaches
   (`openAtomsOf`): all true, all false, each one alone true, each one alone
   false. Two that check (`Open.check`), one making the goal true and one
   false, are **Unknown**; nothing else runs. Their models interpret the
   guard symbols exactly, so they realize the signature (`realizes_guards`);
   the program and the goal mention no guard symbol.
3. **The full run.** Otherwise, after a run that met an open atom (alone or
   beside other gaps), the same run without the open marker, where every
   stable NAF is refuted: a denial may force an open atom, and an operand
   that reaches one may still be refuted. A checked success is Yes.
4. **Refutation.** A refutation of the goal in the completion, within the
   query's fuel, checked, is **No**.
5. Otherwise **Undecided**, with the fast run's blockers: its gaps, the open
   atoms whose witnesses were not both found, a fuel interruption, or the
   goal itself when the search was exhausted.

The run's operational outcomes never give Unknown: Unknown needs both
witnesses, and they are checked models of the completion. -/

namespace AnthillModKbSpec.P1

open Answers Machine Completion Semantics

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  [FreshNames Variable]

attribute [local instance] termEq

/-- What the module's answers carry: a Yes and a No a checked proof term, a
witness the marker atoms it makes true. -/
abbrev ModuleAnswer (Variable Literal Symbol : Type) :=
  Answer (Term Variable Literal Symbol) (Term Variable Literal Symbol) (List (Term Variable Literal Symbol))
    (Blocker Variable Literal Symbol)

/-- A completed program with its open marker, its admission signature, and
the bounds of its runs. The completion is the program's for a signature that
closes no marker and not `ho_apply`, as `complete?`'s is
(`Setup.ofComplete?`); it is built once. The admission signature's guard
symbols are decided by `isGuard` and have one role each (`separated`), so the
exact guard truth realizes it. -/
structure Setup (Domain Variable Literal Symbol : Type) [DecidableEq Variable] [DecidableEq Literal]
    [DecidableEq Symbol] [FreshNames Variable] where
  vocab : Vocabulary Symbol
  hoApplySymbol : Symbol
  marker : Symbol → Bool
  admission : AdmissionSignature.SignatureSnapshot Domain Symbol
  isGuard : Symbol → Bool
  isGuard_iff : ∀ symbol, isGuard symbol = true ↔ Open.IsGuard admission.naming symbol
  separated : Open.Separated admission.naming hoApplySymbol
  clauses : List (HornClause Variable Literal Symbol)
  signature : Signature Literal Symbol
  closed : ∀ key ∈ signature.predicates, marker key.1 = false ∧ key.1 ≠ hoApplySymbol
  completion : Completed Variable Literal Symbol
  completion_eq : completion = Completion.completion clauses signature
  guard : Symbol → Bool := fun _ => false
  select : Selection Variable Literal Symbol := fun _ _ _ _ => []
  /-- The fuel of a run, and of the refutation of the goal. -/
  fuel : Nat
  /-- The fuel of each nested refutation run, for a NAF inside a run. -/
  depth : Nat

namespace Setup

variable {Domain : Type} (setup : Setup Domain Variable Literal Symbol)

/-- The completed snapshot answers are checked against. -/
def snapshot : Snapshot Variable Literal Symbol := ⟨setup.hoApplySymbol, setup.completion.clauses⟩

/-- Evidence-first NAF over the completion; with `fast`, the open marker. -/
def strategy (fast : Bool) : Strategy Variable Literal Symbol (Term Variable Literal Symbol) :=
  nafByRefutation setup.vocab setup.hoApplySymbol setup.completion setup.guard setup.select setup.depth
    (if fast then setup.marker else fun _ => false)

/-- A run from the query, its free names rigid. -/
def run (fast : Bool) (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    Outcome Variable Literal Symbol (Term Variable Literal Symbol) Unit :=
  Machine.run (setup.strategy fast) setup.fuel (State.init () [] context goal)

/-- Check a proof term of the goal under the context against the completed snapshot. -/
def checks (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol)
    (proof : Term Variable Literal Symbol) : Bool :=
  decide (checkProof setup.vocab (refutationChecker setup.vocab setup.snapshot) [] context goal proof = .accept)

/-- A run's success, exported and checked. -/
def proved (outcome : Outcome Variable Literal Symbol (Term Variable Literal Symbol) Unit)
    (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    Option (Term Variable Literal Symbol) :=
  match outcome with
  | .success proof _ => (exportProof setup.vocab id proof).filter (setup.checks context goal)
  | _ => none

/-- A refutation of the goal in the completion, within the query's fuel,
checked: a proof of `goal → false` under the context. -/
def refuted (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    Option (Term Variable Literal Symbol) :=
  (refute setup.vocab (refuter setup.hoApplySymbol setup.completion setup.guard) setup.fuel context goal).filter
    ((refutationCheck setup.vocab setup.snapshot).check context goal)

/-- The open atoms a formula reaches through the program's clauses. -/
def opened (formula : Formula Variable Literal Symbol) : List (Term Variable Literal Symbol) :=
  openAtomsOf setup.marker setup.completion.free setup.clauses formula

/-- The candidate assignments of the open atoms: all true, all false, each one
alone true, each one alone false. -/
def candidates (atoms : List (Term Variable Literal Symbol)) : List (List (Term Variable Literal Symbol)) :=
  [atoms, []] ++ atoms.map (fun atom => [atom]) ++ atoms.map (fun atom => atoms.erase atom)

/-- The candidates that check, each with the goal's value under it. The
program's class, with no guard symbol and no closed guard predicate, is
checked once, and each candidate evaluated once. -/
def valued (atoms : List (Term Variable Literal Symbol)) (goal : Formula Variable Literal Symbol) :
    List (List (Term Variable Literal Symbol) × Bool) :=
  if Open.covers setup.hoApplySymbol setup.isGuard setup.marker setup.clauses &&
      setup.signature.predicates.all (fun key => !setup.isGuard key.1) then
    (candidates atoms).filterMap fun assignment =>
      (Open.witnessValue setup.hoApplySymbol setup.isGuard setup.marker setup.clauses goal assignment).map
        (assignment, ·)
  else []

/-- The two witnesses of a run that ended `opened`, for a query with no
assumptions: candidates over every open atom the goal reaches, one making the
goal true and one false. -/
def witnesses (outcome : Outcome Variable Literal Symbol (Term Variable Literal Symbol) Unit)
    (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    Option (List (Term Variable Literal Symbol) × List (Term Variable Literal Symbol)) :=
  match outcome, context with
  | .opened _, [] =>
      let found := setup.valued (setup.opened goal) goal
      match found.find? (·.2), found.find? (!·.2) with
      | some holds, some fails => some (holds.1, fails.1)
      | _, _ => none
  | _, _ => none

/-- The blockers a run reports: its gaps and the open atoms it met, each with
its scope and provenance; a fuel interruption; or, when the search was
exhausted, the goal itself. -/
def blockers (outcome : Outcome Variable Literal Symbol (Term Variable Literal Symbol) Unit)
    (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    List (Blocker Variable Literal Symbol) :=
  match outcome with
  | .opened gaps | .abandoned gaps => gaps.map (Blocker.ofGap setup.opened)
  | .interrupted _ => [Blocker.interrupted context goal]
  | _ => [Blocker.unproved goal]

/-- A run that met an open atom, alone or beside other gaps. -/
def metOpen : Outcome Variable Literal Symbol (Term Variable Literal Symbol) Unit → Bool
  | .opened _ => true
  | .abandoned gaps => gaps.any Gap.isOpened
  | _ => false

/-- The full run's proof, after a run that met an open atom: every stable NAF
refuted, with no open marker. -/
def full (fast : Outcome Variable Literal Symbol (Term Variable Literal Symbol) Unit)
    (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    Option (Term Variable Literal Symbol) :=
  if metOpen fast then setup.proved (setup.run false context goal) context goal else none

/-- The module's answer to a query. -/
def answer (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    ModuleAnswer Variable Literal Symbol :=
  let fast := setup.run true context goal
  match setup.proved fast context goal with
  | some proof => .yes proof
  | none =>
      match setup.witnesses fast context goal with
      | some (holds, fails) => .unknown holds fails
      | none =>
          match setup.full fast context goal with
          | some proof => .yes proof
          | none =>
              match setup.refuted context goal with
              | some refutation => .no refutation
              | none => .undecided (setup.blockers fast context goal)

/-- What the answers are about: the models of the completed program with
complement NAF that realize the admission signature, under the query's
context. -/
def meaning (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) : Meaning :=
  Meaning.ofModels (Variable := Variable) (hoApplySymbol := setup.hoApplySymbol)
    (fun _ model => model.Models setup.snapshot.kb ∧ model.ComplementNAF ∧
      AdmissionSignature.Realizes setup.admission model) context goal

/-! ## Soundness -/

variable {setup}

/-- A checked proof term is true in every model of the completion. -/
theorem checks_sound {context : ProofContext Variable Literal Symbol} {goal : Formula Variable Literal Symbol}
    {proof : Term Variable Literal Symbol} (checked : setup.checks context goal proof = true) :
    (setup.meaning context goal).truth := by
  intro Value model ⟨validKb, negation, _⟩ environment holds
  exact refutationChecker_sound setup.vocab setup.snapshot model validKb negation
    ((checkProof_accept_iff setup.vocab _).mp (of_decide_eq_true checked)) environment holds

theorem proved_sound {outcome : Outcome Variable Literal Symbol (Term Variable Literal Symbol) Unit}
    {context : ProofContext Variable Literal Symbol} {goal : Formula Variable Literal Symbol}
    {proof : Term Variable Literal Symbol} (found : setup.proved outcome context goal = some proof) :
    (setup.meaning context goal).truth := by
  unfold proved at found
  split at found
  · exact checks_sound (Option.filter_eq_some_iff.mp found).2
  · cases found

theorem full_sound {fast : Outcome Variable Literal Symbol (Term Variable Literal Symbol) Unit}
    {context : ProofContext Variable Literal Symbol} {goal : Formula Variable Literal Symbol}
    {proof : Term Variable Literal Symbol} (found : setup.full fast context goal = some proof) :
    (setup.meaning context goal).truth := by
  unfold full at found
  split at found
  · exact proved_sound found
  · cases found

/-- A checked refutation makes the goal false in every model of the completion. -/
theorem refuted_sound {context : ProofContext Variable Literal Symbol} {goal : Formula Variable Literal Symbol}
    {refutation : Term Variable Literal Symbol} (found : setup.refuted context goal = some refutation) :
    (setup.meaning context goal).falsity := by
  intro Value model ⟨validKb, _, _⟩ environment holds satisfied
  obtain ⟨_, _, derived⟩ := (refutationCheck setup.vocab setup.snapshot).sound context goal refutation
    (Option.filter_eq_some_iff.mp found).2
  have implication := model.positive_sound validKb derived environment holds
  simp only [Model.Satisfies, Model.eval] at implication satisfied
  exact model.holds_bottom ((model.holds_implication _ _).mp implication satisfied)

/-- A candidate that is valued checks as a witness for its value, and the
signature closes no guard predicate. -/
theorem valued_check {atoms : List (Term Variable Literal Symbol)} {goal : Formula Variable Literal Symbol}
    {entry : List (Term Variable Literal Symbol) × Bool} (member : entry ∈ setup.valued atoms goal) :
    Open.check setup.hoApplySymbol setup.isGuard setup.marker setup.clauses goal entry.1 entry.2 = true ∧
      ∀ key ∈ setup.signature.predicates, setup.isGuard key.1 = false := by
  unfold valued at member
  split at member
  · rename_i covering
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at covering
    obtain ⟨assignment, _, produced⟩ := List.mem_filterMap.mp member
    simp only [Option.map_eq_some_iff] at produced
    obtain ⟨value, valueEq, rfl⟩ := produced
    exact ⟨by simp [Open.check, covering.1, valueEq], covering.2⟩
  · cases member

/-- A witness that checks has a model of the completion with complement NAF
that realizes the admission signature, in which the goal has the expected
value: the witness model with the guards interpreted exactly. -/
theorem check_model {goal : Formula Variable Literal Symbol} {expected : Bool}
    {assignment : List (Term Variable Literal Symbol)}
    (checked : Open.check setup.hoApplySymbol setup.isGuard setup.marker setup.clauses goal assignment expected = true)
    (unguarded : ∀ key ∈ setup.signature.predicates, setup.isGuard key.1 = false) :
    ∃ model : Model Literal Symbol (Key Literal Symbol) setup.hoApplySymbol,
      (model.Models setup.snapshot.kb ∧ model.ComplementNAF ∧ AdmissionSignature.Realizes setup.admission model) ∧
        ∀ environment, model.Satisfies environment goal ↔ expected = true := by
  obtain ⟨interpretation, agrees, models, negation, valued⟩ := Open.check_model checked setup.signature
    (fun key member => ⟨(setup.closed key member).1, (setup.closed key member).2, unguarded key member⟩)
    (Open.guardTruth setup.admission setup.hoApplySymbol)
  refine ⟨_, ⟨?_, negation, Open.realizes_guards setup.separated fun symbol guard =>
    agrees symbol ((setup.isGuard_iff symbol).mpr guard)⟩, valued⟩
  rw [show setup.snapshot.kb = (fun clause => clause ∈ setup.completion.clauses : LogicalKb Variable Literal Symbol)
    from rfl, setup.completion_eq]
  exact models

theorem witnesses_sound {outcome : Outcome Variable Literal Symbol (Term Variable Literal Symbol) Unit}
    {context : ProofContext Variable Literal Symbol} {goal : Formula Variable Literal Symbol}
    {holds fails : List (Term Variable Literal Symbol)}
    (found : setup.witnesses outcome context goal = some (holds, fails)) :
    (setup.meaning context goal).independence := by
  unfold witnesses at found
  split at found
  · dsimp only at found
    split at found
    · rename_i trueEntry falseEntry trueFound falseFound
      cases found
      obtain ⟨trueChecked, unguarded⟩ := valued_check (List.mem_of_find?_eq_some trueFound)
      have falseChecked := (valued_check (List.mem_of_find?_eq_some falseFound)).1
      have trueValue : trueEntry.2 = true := by
        have := List.find?_some trueFound; simpa using this
      have falseValue : falseEntry.2 = false := by
        have := List.find?_some falseFound; simpa using this
      rw [trueValue] at trueChecked
      rw [falseValue] at falseChecked
      obtain ⟨trueModel, trueHolds, trueValued⟩ := check_model trueChecked unguarded
      obtain ⟨falseModel, falseHolds, falseValued⟩ := check_model falseChecked unguarded
      let environment : Environment Variable (Key Literal Symbol) := fun _ => .truth False
      exact ⟨⟨_, trueModel, trueHolds, environment, fun _ inside => (by cases inside), (trueValued environment).mpr rfl⟩,
        ⟨_, falseModel, falseHolds, environment, fun _ inside => (by cases inside),
          fun satisfied => Bool.false_ne_true ((falseValued environment).mp satisfied)⟩⟩
    · cases found
  · cases found

/-- `Setup.answer_sound`: every answer is sound for the models of the
completion with complement NAF. Yes makes the goal true in each of them, under
every environment satisfying the context; No makes it false; Unknown exhibits
one in which it holds and one in which it fails; Undecided claims nothing. -/
theorem answer_sound (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    (setup.answer context goal).Sound (setup.meaning context goal) := by
  unfold answer
  dsimp only
  split
  · rename_i proof found; exact proved_sound found
  · split
    · rename_i holds fails found; exact witnesses_sound found
    · split
      · rename_i proof found; exact full_sound found
      · split
        · rename_i refutation found; exact refuted_sound found
        · trivial

/-- Unknown only from two checked witnesses of a run that met open atoms and
recorded no gap: never from an operational outcome. -/
theorem answer_unknown {context : ProofContext Variable Literal Symbol} {goal : Formula Variable Literal Symbol}
    {holds fails : List (Term Variable Literal Symbol)} (answered : setup.answer context goal = .unknown holds fails) :
    ∃ obligations, setup.run true context goal = .opened obligations ∧ context = [] := by
  unfold answer at answered
  dsimp only at answered
  split at answered
  · cases answered
  · split at answered
    · rename_i found
      unfold witnesses at found
      split at found
      · rename_i _ obligations _ ran
        exact ⟨obligations, ran, rfl⟩
      · cases found
    · split at answered
      · cases answered
      · split at answered <;> cases answered

end Setup

/-- The setup of a program `complete?` accepts, with its own signature and the
completion `complete?` built, for an admission signature whose guard symbols
`isGuard` decides and which are separated. -/
def Setup.ofComplete? {Domain : Type} (vocab : Vocabulary Symbol) (hoApplySymbol : Symbol) (marker free : Symbol → Bool)
    (admission : AdmissionSignature.SignatureSnapshot Domain Symbol) (isGuard : Symbol → Bool)
    (isGuard_iff : ∀ symbol, isGuard symbol = true ↔ Open.IsGuard admission.naming symbol)
    (separated : Open.Separated admission.naming hoApplySymbol)
    (clauses : List (HornClause Variable Literal Symbol)) (formulas : List (Term Variable Literal Symbol))
    (fuel depth : Nat) (guard : Symbol → Bool := fun _ => false)
    (select : Selection Variable Literal Symbol := fun _ _ _ _ => []) : Except Nat (Setup Domain Variable Literal Symbol) :=
  match completes : complete? marker hoApplySymbol free clauses formulas with
  | .error index => .error index
  | .ok completion =>
      .ok { vocab, hoApplySymbol, marker, admission, isGuard, isGuard_iff, separated, clauses,
            signature := Signature.of marker hoApplySymbol free clauses formulas
            closed := fun _ member => Signature.of_open member, completion, completion_eq := complete?_ok completes,
            guard, select, fuel, depth }

end AnthillModKbSpec.P1
