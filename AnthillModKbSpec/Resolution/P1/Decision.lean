import AnthillModKbSpec.Resolution.P1.Encoding

/-! # P1 decision contracts (S08)

A P1 route decides one stated problem. `DecisionContract` is the interface,
apart from any search procedure: the problem, the declared meaning of No, the
input conditions, and a total decision (a Lean function) whose Yes establishes
the problem and whose No establishes the declared negative, which excludes
the problem. The two answers cover every input meeting the conditions.

Checking a supplied proof is one such route (`proofRoute`): its problem is
the validity of the supplied tree for the stated goal, and its No means only
that this tree is not a valid proof. Rejection proves no negation, NAF, or
non-derivability of the goal: a rejected tree may stand beside a derivable
goal (`reject_says_nothing`). -/

namespace AnthillModKbSpec.P1

variable {Variable Literal Symbol : Type}

/-- A P1 decision contract for a problem over admitted inputs. -/
structure DecisionContract (Input : Type) where
  problem : Input → Prop
  /-- What No means, as the contract states it. -/
  negative : Input → Prop
  excludes : ∀ input, negative input → ¬ problem input
  conditions : Input → Prop
  decide : Input → Bool
  yes : ∀ input, conditions input → decide input = true → problem input
  no : ∀ input, conditions input → decide input = false → negative input

/-- A decided input meets the problem exactly when the decision says Yes. -/
theorem DecisionContract.decide_iff {Input : Type} (contract : DecisionContract Input) {input : Input}
    (admitted : contract.conditions input) : contract.decide input = true ↔ contract.problem input := by
  constructor
  · exact contract.yes input admitted
  · intro holds
    cases decided : contract.decide input
    · exact absurd holds (contract.excludes input (contract.no input admitted decided))
    · rfl

/-- What the proof-checking route is asked: a supplied term for a goal under a
context. -/
structure ProofQuery (Variable Literal Symbol : Type) where
  context : ProofContext Variable Literal Symbol
  goal : Formula Variable Literal Symbol
  proof : Term Variable Literal Symbol

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

/-- Proof checking as a P1 decision of supplied-tree validity: admitted when
the tree needs no capability the checker lacks; Yes is `CheckedProof`; No is
only that this term is not a checked proof of the goal. -/
def proofRoute (vocab : Vocabulary Symbol) (checker : Checker Variable Literal Symbol)
    (imports : List (Import Variable Literal Symbol)) : DecisionContract (ProofQuery Variable Literal Symbol) where
  problem query := CheckedProof vocab checker imports query.context query.goal query.proof
  negative query := ¬ CheckedProof vocab checker imports query.context query.goal query.proof
  excludes _ negative holds := negative holds
  conditions query := ∀ tree, decode vocab query.proof = some tree → missing vocab checker imports tree = []
  decide query := checkProof vocab checker imports query.context query.goal query.proof == .accept
  yes query _ accepted := (checkProof_accept_iff vocab checker).mp (by simpa using accepted)
  no query _ rejected checked := by
    have accepted := (checkProof_accept_iff vocab checker).mpr checked
    simp [accepted] at rejected

/-- A term that is no proof tree is rejected for every goal, derivable or not:
rejection is about the supplied term only. -/
theorem reject_says_nothing (vocab : Vocabulary Symbol) (checker : Checker Variable Literal Symbol)
    (imports : List (Import Variable Literal Symbol)) (context : ProofContext Variable Literal Symbol)
    (goal : Formula Variable Literal Symbol) :
    checkProof vocab checker imports context goal .truth = .reject := by
  simp [checkProof, decode]

end AnthillModKbSpec.P1
