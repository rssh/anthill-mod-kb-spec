import AnthillModKbSpec.Resolution.P1.Encoding
import AnthillModKbSpec.Foundation.Completion

/-! # Checked refutations as NAF evidence (S10)

NAF evidence by refutation is a supplied proof of `operand → false`, checked by
the S08 checker against the same snapshot with no NAF of its own. For a
completed program (`Completion.completed`) this is the closed-world reading of
NAF: `refutation_adequate` makes it adequate in every model of the completed
program with complement NAF, also for an operand with free parameters.

`refutationCheck` is the known terminating procedure for the evidence, and
`refutationChecker` checks trees whose NAF nodes carry such evidence. Evidence
is checked against the snapshot it is given, so a refutation computed for one
program is rejected for another: adding a clause changes a completion, and
adding a domain or registering a predicate changes the generated clauses that
are completed. -/

namespace AnthillModKbSpec.P1

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

/-- The checker of a refutation itself: the snapshot, positive. -/
def Snapshot.positive (snapshot : Snapshot Variable Literal Symbol) : Checker Variable Literal Symbol :=
  ⟨snapshot, NafFailure.disabled, none, []⟩

/-- NAF evidence is a supplied proof, as a term, of `operand → false` under the
NAF's own context, checked against the snapshot. -/
def refutationCheck (vocab : Vocabulary Symbol) (snapshot : Snapshot Variable Literal Symbol) :
    NafCheck snapshot (refutation snapshot.hoApplySymbol snapshot.kb) where
  check := fun context operand evidence =>
    decide (checkProof vocab snapshot.positive [] context (.imp operand .falsity) evidence = .accept)
  sound _ _ _ accepted :=
    ⟨rfl, rfl, checked_toDerives vocab snapshot.positive
      ((checkProof_accept_iff vocab snapshot.positive).mp (of_decide_eq_true accepted))⟩

/-- The checker for proofs whose NAF evidence is a refutation in the same
snapshot. -/
def refutationChecker (vocab : Vocabulary Symbol) (snapshot : Snapshot Variable Literal Symbol) :
    Checker Variable Literal Symbol :=
  ⟨snapshot, refutation snapshot.hoApplySymbol snapshot.kb, some (refutationCheck vocab snapshot), []⟩

open Semantics in
/-- A proof checked with refutation evidence is sound in every model of the
snapshot's KB with complement NAF: for a completed program, every model of the
completion and the free equality theory. -/
theorem refutationChecker_sound (vocab : Vocabulary Symbol) (snapshot : Snapshot Variable Literal Symbol)
    {Value : Type} (model : Model Literal Symbol Value snapshot.hoApplySymbol) (validKb : model.Models snapshot.kb)
    (negation : model.ComplementNAF) {context : ProofContext Variable Literal Symbol}
    {goal : Formula Variable Literal Symbol} {proof : Term Variable Literal Symbol}
    (checked : CheckedProof vocab (refutationChecker vocab snapshot) [] context goal proof) :
    ∀ environment, model.ContextHolds environment context → model.Satisfies environment goal :=
  model.sound validKb (refutation_adequate model validKb negation)
    (checked_toDerives vocab (refutationChecker vocab snapshot) checked)

end AnthillModKbSpec.P1
