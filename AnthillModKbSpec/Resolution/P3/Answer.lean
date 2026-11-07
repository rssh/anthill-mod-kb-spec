import AnthillModKbSpec.Resolution.Answer
import AnthillModKbSpec.Resolution.P3.Induction

/-! # The induction path's answer (S22)

S12's admission reports what the induction path needs before anything runs:
the goal's shape, the predicate's registration, a carried principle, its
names, and each formula a case cannot run (`CaseGap`), at its site and path.
`Induction.answer` reports them as Undecided blockers, and nothing runs
(`answer_needsEvidence`). A Ready plan runs within its fuel: a success is
Yes, true in every model realizing the signature that satisfies the
program's other clauses (`answer_yes`, then `Plan.sound`); an interrupted or
unsuccessful run is Undecided, never Unknown. The induction search is P3: its
failure does not refute the universal, so this route never answers No. -/

namespace AnthillModKbSpec.Induction

open Answers Machine

variable {Domain Variable Literal Symbol : Type} [DecidableEq Domain] [DecidableEq Variable] [DecidableEq Literal]
  [DecidableEq Symbol]

/-- What a case lacks at a formula. -/
def Missing.toMissing : Induction.Missing → Answers.Missing Variable Literal Symbol
  | .capability needed => .ofCapability needed
  | .negation => .construct .negation
  | .waitingGuard => .construct .waitingGuard

/-- A case gap as a blocker, at its site and path. -/
def CaseGap.blocker (gap : CaseGap Variable Literal Symbol) : Blocker Variable Literal Symbol :=
  ⟨.site gap.site, gap.path, gap.formula, gap.missing.toMissing⟩

/-- A need of the induction path as a blocker. The goal's shape and a missing
principle lack a proof of the goal, which a supplied proof or principle
settles. A missing registration names the predicate's reference as its
formula. -/
def Need.blocker (goal : Formula Variable Literal Symbol) : Need Variable Literal Symbol → Blocker Variable Literal Symbol
  | .shape => ⟨.site .goal, [], goal, .proof⟩
  | .registration predicate => ⟨.site .goal, [], .app predicate [], .construct .registration⟩
  | .principle => ⟨.site .goal, [], goal, .proof⟩
  | .names => ⟨.site .goal, [], goal, .construct .principleNames⟩
  | .context gap => gap.blocker
  | .clause gap => gap.blocker

/-- What the induction path's answers carry: a Yes the run's completed proof;
it never answers No or Unknown. -/
abbrev InductionAnswer (Variable Literal Symbol : Type) :=
  Answer (CompletedProof Variable Literal Symbol Unit Unit) Empty Empty (Blocker Variable Literal Symbol)

variable [FreshNames Variable]

/-- The induction path's answer: admission's needs as blockers before anything
runs; for a Ready plan, the run within `fuel`, its gaps as blockers when it
abandoned a path. -/
def answer (hoApplySymbol : Symbol) (input : Admission.Input Domain Variable Literal Symbol) (fuel : Nat) :
    Except Admission.Diagnostic (InductionAnswer Variable Literal Symbol) :=
  match check hoApplySymbol input with
  | .invalid diagnostic => .error diagnostic
  | .needsEvidence needs => .ok (.undecided (needs.map (Need.blocker input.goal)))
  | .ready plan =>
      match plan.run fuel with
      | .success proof _ => .ok (.yes proof)
      | .interrupted _ => .ok (.undecided [Blocker.interrupted input.context input.goal])
      | .opened gaps | .abandoned gaps => .ok (.undecided (gaps.map (Blocker.ofGap fun _ => [])))
      | _ => .ok (.undecided [Blocker.unproved input.goal])

/-- Admission's needs are Undecided blockers, and nothing runs for them. -/
theorem answer_needsEvidence {hoApplySymbol : Symbol} {input : Admission.Input Domain Variable Literal Symbol}
    {needs : List (Need Variable Literal Symbol)} (fuel : Nat)
    (needed : check hoApplySymbol input = .needsEvidence needs) :
    answer hoApplySymbol input fuel = .ok (.undecided (needs.map (Need.blocker input.goal))) := by
  simp [answer, needed]

/-- A Yes is a successful run of the Ready plan, which `Plan.sound` makes true
in every model realizing the signature that satisfies the program's other
clauses. -/
theorem answer_yes {hoApplySymbol : Symbol} {input : Admission.Input Domain Variable Literal Symbol} {fuel : Nat}
    {proof : CompletedProof Variable Literal Symbol Unit Unit}
    (answered : answer hoApplySymbol input fuel = .ok (.yes proof)) :
    ∃ plan resume, check hoApplySymbol input = .ready plan ∧ plan.run fuel = .success proof resume := by
  unfold answer at answered
  split at answered
  · cases answered
  · cases answered
  · rename_i plan ready
    split at answered
    · rename_i found resume ran
      cases answered
      exact ⟨plan, resume, ready, ran⟩
    all_goals cases answered

/-- The induction path never answers Unknown: the open atoms and their
witnesses are the completion's, and an interrupted run is Undecided. -/
theorem answer_decided {hoApplySymbol : Symbol} {input : Admission.Input Domain Variable Literal Symbol} {fuel : Nat}
    {result : InductionAnswer Variable Literal Symbol} (answered : answer hoApplySymbol input fuel = .ok result) :
    (∃ proof, result = .yes proof) ∨ ∃ blockers, result = .undecided blockers := by
  unfold answer at answered
  split at answered
  · cases answered
  · cases answered; exact .inr ⟨_, rfl⟩
  · split at answered <;> (cases answered) <;> first | exact .inl ⟨_, rfl⟩ | exact .inr ⟨_, rfl⟩

end AnthillModKbSpec.Induction
