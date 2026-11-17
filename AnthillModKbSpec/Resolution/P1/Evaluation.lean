import AnthillModKbSpec.Resolution.P1.Export
import AnthillModKbSpec.Resolution.Machine.Dictionary

/-! # Evaluations as checked nodes (S14)

An evaluation node of a run (`Machine.Expansion.evaluation`) exports as the
derived rule `name` with the call and the value as parameters and no premise:
`extension name [call, value]` concluding `call = value`. Its procedure
(`evaluationRule`) is the snapshot's own evaluators, run again on the call: a
known terminating check, since an evaluator is a Lean function. Its soundness
is the clause rule on the evaluated equation, which the snapshot's KB contains
(`P1.Snapshot.kb`), so a checked evaluation reconstructs `Derives` in exactly
that KB, with the checker's NAF provider. An evaluator callback is never
trusted: the node is accepted only when an evaluator of the snapshot answers
the call with the value, and the KB is the one whose equations they are.

A call on the right side is turned around by `equalSymm`, a shared rule. A
run's evaluation nodes export as valid nodes (`evaluation_proves`,
`exportNode_evaluation`). -/

namespace AnthillModKbSpec.P1

open Machine

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

/-- An evaluator of the snapshot answers the call with the value. -/
def Snapshot.evaluates (snapshot : Snapshot Variable Literal Symbol) (call value : Term Variable Literal Symbol) : Bool :=
  snapshot.evaluators.any fun evaluator =>
    match evaluator call with
    | some found => identical found value
    | none => false

theorem Snapshot.evaluates_iff {snapshot : Snapshot Variable Literal Symbol} {call value : Term Variable Literal Symbol} :
    snapshot.evaluates call value = true ↔ snapshot.Evaluates call value := by
  simp only [Snapshot.evaluates, List.any_eq_true, Snapshot.Evaluates]
  constructor
  · rintro ⟨evaluator, member, accepted⟩
    split at accepted
    · rename_i found same
      exact ⟨evaluator, member, by rw [same, identical_iff.mp accepted]⟩
    · cases accepted
  · rintro ⟨evaluator, member, found⟩
    exact ⟨evaluator, member, by rw [found]; exact identical_self _⟩

/-- The derived rule of an evaluation: a conclusion `call = value` with the call
and the value as parameters and no premise, accepted when an evaluator of the
snapshot answers the call with the value. -/
def evaluationRule (name : Symbol) (snapshot : Snapshot Variable Literal Symbol)
    (provider : NafFailure Variable Literal Symbol) : RuleCheck snapshot provider where
  name := name
  discharges _ _ _ := []
  check _ conclusion parameters premises :=
    match conclusion, parameters, premises with
    | .equal call value, [call', value'], [] => identical call call' && identical value value' && snapshot.evaluates call value
    | _, _, _ => false
  sound context conclusion parameters premises accepted _ := by
    split at accepted
    · simp only [Bool.and_eq_true] at accepted
      exact Snapshot.evaluated_derives ((Snapshot.evaluates_iff (snapshot := snapshot)).mp accepted.2)
    · cases accepted

/-- The node of an evaluation: `call = value` by the derived rule. -/
def Unfold.evaluation (name : Symbol) (call value : Term Variable Literal Symbol) : Proof Variable Literal Symbol :=
  .node (.extension name [call, value]) (.equal call value) []

/-- An evaluation node proves its equation when the checker registers the
evaluation rule under its name and an evaluator of the snapshot answers the
call with the value. -/
theorem Unfold.evaluation_proves {checker : Checker Variable Literal Symbol}
    {refs : Symbol → ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Prop}
    {context : ProofContext Variable Literal Symbol} {name : Symbol}
    (registered : checker.rule? name = some (evaluationRule name checker.snapshot checker.provider))
    {call value : Term Variable Literal Symbol} (evaluated : checker.snapshot.Evaluates call value) :
    Proves checker refs context (.equal call value) (evaluation name call value) := by
  refine ⟨.node (.extension registered ?_ rfl) (by simp), rfl⟩
  simpa [evaluationRule, identical_self] using Snapshot.evaluates_iff.mpr evaluated

omit [DecidableEq Literal] [DecidableEq Symbol] in
/-- A run's evaluation node exports as the evaluation node of its call and
value, read through the final store. -/
theorem exportNode_evaluation {Certificate : Type} [FreshNames Variable]
    (evidence : Certificate → Term Variable Literal Symbol) (store : Store Variable Literal Symbol) (name : Symbol)
    (call value goal : Term Variable Literal Symbol) :
    exportNode evidence store (.extension name [call, value] none) [] goal [] =
      some (.node (.extension name [store.resolve call, store.resolve value]) goal []) := by
  simp [exportNode, exportRule]

end AnthillModKbSpec.P1
