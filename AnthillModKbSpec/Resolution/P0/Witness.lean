import AnthillModKbSpec.Resolution.P0.Rank
import AnthillModKbSpec.Resolution.Machine.Unification

/-! # Finite success and failure witnesses (S07)

A NAF node's certificate must carry evidence S08 can check without searching
again. These are finite trees for the ground judgments: a success tree names the
assumption or the clause and the subtrees, a failure tree lists one failure per
clause with the atom as head, in program order. `checkSuccess` and
`checkFailure` check a tree against a clause list and a context by structural
recursion on the tree, so they terminate; they are sound for
`GroundSearch.Succeeds` and `GroundSearch.Fails` (`checkFailure_sound`).
`evaluate` builds the tree for a ground goal by recursion on the rank's level
bound; under a rank it always answers (`evaluate_total`) and its trees check
(`evaluate_sound`). -/

namespace AnthillModKbSpec.GroundSearch

open Machine

variable {Variable Literal Symbol : Type}

mutual
/-- A finite success witness for a ground goal. -/
inductive SuccessTree (Variable Literal Symbol : Type) where
  /-- The atom is an assumption of the context. -/
  | assumption
  /-- The clause with the atom as head and this body, and the body's witness. -/
  | clause (body : List (Term Variable Literal Symbol)) (proof : SuccessTree Variable Literal Symbol)
  | truth
  | conj (left right : SuccessTree Variable Literal Symbol)
  /-- NAF succeeds by its operand's failure. -/
  | negation (refuted : FailureTree Variable Literal Symbol)

/-- A finite complete-failure witness for a ground goal. -/
inductive FailureTree (Variable Literal Symbol : Type) where
  /-- The atom is not assumed, and each clause with the atom as head has a
  failing body: one witness per clause, in program order. -/
  | atom (bodies : FailureList Variable Literal Symbol)
  | falsity
  | conjLeft (left : FailureTree Variable Literal Symbol)
  | conjRight (right : FailureTree Variable Literal Symbol)
  /-- NAF fails by its operand's success. -/
  | negation (proof : SuccessTree Variable Literal Symbol)

inductive FailureList (Variable Literal Symbol : Type) where
  | nil
  | cons (head : FailureTree Variable Literal Symbol) (tail : FailureList Variable Literal Symbol)
end

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] (hoApplySymbol : Symbol)

attribute [local instance] termEq

mutual
def isData : Term Variable Literal Symbol → Bool
  | .lit _ => true
  | .app _ args => isDataArgs args
  | _ => false

def isDataArgs : List (Term Variable Literal Symbol) → Bool
  | [] => true
  | arg :: args => isData arg && isDataArgs args
end

def isAtom : Term Variable Literal Symbol → Bool
  | .app symbol args => decide (symbol ≠ hoApplySymbol) && isDataArgs args
  | _ => false

def isGoal : Term Variable Literal Symbol → Bool
  | .app symbol args => isAtom hoApplySymbol (.app symbol args)
  | .truth | .falsity => true
  | .conj left right => isGoal left && isGoal right
  | .defaultNeg body => isGoal body
  | _ => false

/-- The bodies of the clauses with exactly this head, in program order. -/
def matchingBodies (clauses : List (HornClause Variable Literal Symbol)) (atom : Term Variable Literal Symbol) :
    List (List (Term Variable Literal Symbol)) :=
  clauses.filterMap fun
    | .definite head body => if head = atom then some body else none
    | .goal _ => none

section Check

variable (clauses : List (HornClause Variable Literal Symbol)) (context : ProofContext Variable Literal Symbol)

mutual
/-- Check a success witness. -/
def checkSuccess : Term Variable Literal Symbol → SuccessTree Variable Literal Symbol → Bool
  | .app symbol args, .assumption => isAtom hoApplySymbol (.app symbol args) && decide (.app symbol args ∈ context)
  | .app symbol args, .clause body proof =>
      isAtom hoApplySymbol (.app symbol args) && decide (body ∈ matchingBodies clauses (.app symbol args)) &&
        checkSuccess (.conjunction body) proof
  | .truth, .truth => true
  | .conj left right, .conj leftProof rightProof => checkSuccess left leftProof && checkSuccess right rightProof
  | .defaultNeg operand, .negation refuted => checkFailure operand refuted
  | _, _ => false

/-- Check a failure witness. -/
def checkFailure : Term Variable Literal Symbol → FailureTree Variable Literal Symbol → Bool
  | .app symbol args, .atom bodies =>
      isAtom hoApplySymbol (.app symbol args) && !decide (.app symbol args ∈ context) &&
        checkFailures (matchingBodies clauses (.app symbol args)) bodies
  | .falsity, .falsity => true
  | .conj left right, .conjLeft refuted => checkFailure left refuted && isGoal hoApplySymbol right
  | .conj left right, .conjRight refuted => isGoal hoApplySymbol left && checkFailure right refuted
  | .defaultNeg operand, .negation proof => checkSuccess operand proof
  | _, _ => false

def checkFailures : List (List (Term Variable Literal Symbol)) → FailureList Variable Literal Symbol → Bool
  | [], .nil => true
  | body :: bodies, .cons refuted rest => checkFailure (.conjunction body) refuted && checkFailures bodies rest
  | _, _ => false
end

end Check

/-! ## The checks decide the ground classes and the judgments -/

section Soundness

variable {hoApplySymbol}

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
mutual
theorem isData_iff : ∀ {term : Term Variable Literal Symbol}, isData term = true ↔ IsData term
  | .lit _ => by simp [isData, IsData.lit]
  | .app _ args => by
      rw [isData, isDataArgs_iff]
      exact ⟨fun each => .app each, fun data => by cases data with | app each => exact each⟩
  | .var _ | .truth | .falsity | .conj _ _ | .disj _ _ | .imp _ _ | .defaultNeg _ | .forallVar _ _
  | .existsVar _ _ | .dictionaryCall _ _ _ _ | .equal _ _ => by simp [isData]; intro data; cases data

theorem isDataArgs_iff : ∀ {args : List (Term Variable Literal Symbol)},
    isDataArgs args = true ↔ ∀ arg ∈ args, IsData arg
  | [] => by simp [isDataArgs]
  | arg :: args => by rw [isDataArgs, Bool.and_eq_true, isData_iff, isDataArgs_iff]; simp
end

omit [DecidableEq Variable] [DecidableEq Literal] in
theorem isAtom_iff {term : Term Variable Literal Symbol} : isAtom hoApplySymbol term = true ↔ IsAtom hoApplySymbol term := by
  cases term with
  | app symbol args =>
      rw [isAtom, Bool.and_eq_true, isDataArgs_iff]
      simp only [decide_eq_true_eq]
      exact ⟨fun ⟨different, each⟩ => .app different each, fun atom => by cases atom with
        | app different each => exact ⟨different, each⟩⟩
  | _ => simp [isAtom]; intro atom; cases atom

omit [DecidableEq Variable] [DecidableEq Literal] in
theorem isGoal_iff : ∀ {term : Term Variable Literal Symbol}, isGoal hoApplySymbol term = true ↔ IsGoal hoApplySymbol term
  | .app symbol args => by
      rw [isGoal, isAtom_iff]
      exact ⟨fun atom => .atom atom, fun goal => by cases goal with | atom atom => exact atom⟩
  | .truth => by simp [isGoal]; exact .truth
  | .falsity => by simp [isGoal]; exact .falsity
  | .conj left right => by
      rw [isGoal, Bool.and_eq_true, isGoal_iff, isGoal_iff]
      exact ⟨fun ⟨first, second⟩ => .conj first second, fun goal => by
        cases goal with
        | atom atom => cases atom
        | conj first second => exact ⟨first, second⟩⟩
  | .defaultNeg body => by
      rw [isGoal, isGoal_iff]
      exact ⟨fun inner => .defaultNeg inner, fun goal => by
        cases goal with
        | atom atom => cases atom
        | defaultNeg inner => exact inner⟩
  | .var _ | .lit _ | .disj _ _ | .imp _ _ | .forallVar _ _ | .existsVar _ _ | .dictionaryCall _ _ _ _
  | .equal _ _ => by simp [isGoal]; intro goal; cases goal with | atom atom => cases atom

theorem mem_matchingBodies {clauses : List (HornClause Variable Literal Symbol)} {atom : Term Variable Literal Symbol}
    {body : List (Term Variable Literal Symbol)} :
    body ∈ matchingBodies clauses atom ↔ HornClause.definite atom body ∈ clauses := by
  simp only [matchingBodies, List.mem_filterMap]
  constructor
  · rintro ⟨clause, member, found⟩
    cases clause with
    | definite head clauseBody =>
        simp only at found
        split at found
        · rename_i same; cases found; rw [same] at member; exact member
        · cases found
    | goal _ => cases found
  · intro member
    exact ⟨_, member, by simp⟩

variable {program : Program Variable Literal Symbol hoApplySymbol} {context : Context Variable Literal Symbol hoApplySymbol}

mutual
theorem checkSuccess_sound : ∀ (goal : Term Variable Literal Symbol) (tree : SuccessTree Variable Literal Symbol),
    checkSuccess hoApplySymbol program.clauses context.assumptions goal tree = true → Succeeds program context goal
  | .app symbol args, .assumption, checked => by
      simp only [checkSuccess, Bool.and_eq_true, decide_eq_true_eq] at checked
      exact .assumption (isAtom_iff.mp checked.1) checked.2
  | .app symbol args, .clause body proof, checked => by
      simp only [checkSuccess, Bool.and_eq_true, decide_eq_true_eq] at checked
      exact .clause (isAtom_iff.mp checked.1.1) (mem_matchingBodies.mp checked.1.2)
        (checkSuccess_sound _ proof checked.2)
  | .truth, .truth, _ => .truth
  | .conj left right, .conj leftProof rightProof, checked => by
      simp only [checkSuccess, Bool.and_eq_true] at checked
      exact .conj (checkSuccess_sound _ _ checked.1) (checkSuccess_sound _ _ checked.2)
  | .defaultNeg operand, .negation refuted, checked => by
      simp only [checkSuccess] at checked
      exact .defaultNeg (checkFailure_sound _ _ checked)
  | .var _, tree, checked | .lit _, tree, checked | .falsity, tree, checked | .disj _ _, tree, checked
  | .imp _ _, tree, checked | .forallVar _ _, tree, checked | .existsVar _ _, tree, checked
  | .dictionaryCall _ _ _ _, tree, checked | .equal _ _, tree, checked => by
      cases tree <;> simp [checkSuccess] at checked
  | .app _ _, .truth, checked | .app _ _, .conj _ _, checked | .app _ _, .negation _, checked
  | .truth, .assumption, checked | .truth, .clause _ _, checked | .truth, .conj _ _, checked
  | .truth, .negation _, checked | .conj _ _, .assumption, checked | .conj _ _, .clause _ _, checked
  | .conj _ _, .truth, checked | .conj _ _, .negation _, checked | .defaultNeg _, .assumption, checked
  | .defaultNeg _, .clause _ _, checked | .defaultNeg _, .truth, checked | .defaultNeg _, .conj _ _, checked => by
      simp [checkSuccess] at checked

theorem checkFailure_sound : ∀ (goal : Term Variable Literal Symbol) (tree : FailureTree Variable Literal Symbol),
    checkFailure hoApplySymbol program.clauses context.assumptions goal tree = true → Fails program context goal
  | .app symbol args, .atom bodies, checked => by
      simp only [checkFailure, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at checked
      exact .atom (isAtom_iff.mp checked.1.1) checked.1.2 fun body member =>
        checkFailures_sound _ bodies checked.2 body (mem_matchingBodies.mpr member)
  | .falsity, .falsity, _ => .falsity
  | .conj left right, .conjLeft refuted, checked => by
      simp only [checkFailure, Bool.and_eq_true] at checked
      exact .conjLeft (checkFailure_sound _ _ checked.1) (isGoal_iff.mp checked.2)
  | .conj left right, .conjRight refuted, checked => by
      simp only [checkFailure, Bool.and_eq_true] at checked
      exact .conjRight (isGoal_iff.mp checked.1) (checkFailure_sound _ _ checked.2)
  | .defaultNeg operand, .negation proof, checked => by
      simp only [checkFailure] at checked
      exact .defaultNeg (checkSuccess_sound _ _ checked)
  | .var _, tree, checked | .lit _, tree, checked | .truth, tree, checked | .disj _ _, tree, checked
  | .imp _ _, tree, checked | .forallVar _ _, tree, checked | .existsVar _ _, tree, checked
  | .dictionaryCall _ _ _ _, tree, checked | .equal _ _, tree, checked => by
      cases tree <;> simp [checkFailure] at checked
  | .app _ _, .falsity, checked | .app _ _, .conjLeft _, checked | .app _ _, .conjRight _, checked
  | .app _ _, .negation _, checked | .falsity, .atom _, checked | .falsity, .conjLeft _, checked
  | .falsity, .conjRight _, checked | .falsity, .negation _, checked | .conj _ _, .atom _, checked
  | .conj _ _, .falsity, checked | .conj _ _, .negation _, checked | .defaultNeg _, .atom _, checked
  | .defaultNeg _, .falsity, checked | .defaultNeg _, .conjLeft _, checked | .defaultNeg _, .conjRight _, checked => by
      simp [checkFailure] at checked

theorem checkFailures_sound : ∀ (bodies : List (List (Term Variable Literal Symbol))) (trees : FailureList Variable Literal Symbol),
    checkFailures hoApplySymbol program.clauses context.assumptions bodies trees = true →
      ∀ body ∈ bodies, Fails program context (.conjunction body)
  | [], _, _ => fun _ member => by cases member
  | body :: bodies, .cons refuted rest, checked => by
      simp only [checkFailures, Bool.and_eq_true] at checked
      intro other member
      rcases List.mem_cons.mp member with rfl | inside
      · exact checkFailure_sound _ _ checked.1
      · exact checkFailures_sound bodies rest checked.2 other inside
  | _ :: _, .nil, checked => by simp [checkFailures] at checked
end

end Soundness

/-! ## Building the witnesses -/

/-- A decision for a ground goal, with its witness. -/
inductive Verdict (Variable Literal Symbol : Type) where
  | success (tree : SuccessTree Variable Literal Symbol)
  | failure (tree : FailureTree Variable Literal Symbol)

/-- The failure witness of a verdict, if it is a failure. -/
def Verdict.failure? : Verdict Variable Literal Symbol → Option (FailureTree Variable Literal Symbol)
  | .failure tree => some tree
  | .success _ => none

/-- Decide an atom's clause bodies in program order: the first success, or a
failure for every one. -/
def combineBodies (evaluateBody : Term Variable Literal Symbol → Option (Verdict Variable Literal Symbol)) :
    List (List (Term Variable Literal Symbol)) → Option (Verdict Variable Literal Symbol)
  | [] => some (.failure (.atom .nil))
  | body :: rest =>
      match evaluateBody (.conjunction body) with
      | some (.success proof) => some (.success (.clause body proof))
      | some (.failure refuted) =>
          match combineBodies evaluateBody rest with
          | some (.failure (.atom refutedRest)) => some (.failure (.atom (.cons refuted refutedRest)))
          | other => other
      | none => none

/-- Decide a ground goal with its witness, at a level bound that decreases into
clause bodies. `none` only when the bound is too small. -/
def evaluate (clauses : List (HornClause Variable Literal Symbol)) (context : ProofContext Variable Literal Symbol) :
    Nat → Term Variable Literal Symbol → Option (Verdict Variable Literal Symbol)
  | _, .truth => some (.success .truth)
  | _, .falsity => some (.failure .falsity)
  | bound, .conj left right =>
      match evaluate clauses context bound left with
      | some (.failure refuted) => some (.failure (.conjLeft refuted))
      | some (.success leftProof) =>
          match evaluate clauses context bound right with
          | some (.success rightProof) => some (.success (.conj leftProof rightProof))
          | some (.failure refuted) => some (.failure (.conjRight refuted))
          | none => none
      | none => none
  | bound, .defaultNeg operand =>
      match evaluate clauses context bound operand with
      | some (.success proof) => some (.failure (.negation proof))
      | some (.failure refuted) => some (.success (.negation refuted))
      | none => none
  | 0, .app _ _ => none
  | bound + 1, .app symbol args =>
      if .app symbol args ∈ context then some (.success .assumption)
      else combineBodies (fun body => evaluate clauses context bound body) (matchingBodies clauses (.app symbol args))
  | _, _ => none
termination_by bound goal => (bound, sizeOf goal)

section Evaluation

variable {hoApplySymbol} {program : Program Variable Literal Symbol hoApplySymbol}
  {context : Context Variable Literal Symbol hoApplySymbol}

/-- A verdict's witness checks for the goal. -/
def Verdict.Checks (program : Program Variable Literal Symbol hoApplySymbol) (context : Context Variable Literal Symbol hoApplySymbol)
    (goal : Term Variable Literal Symbol) : Verdict Variable Literal Symbol → Prop
  | .success tree => checkSuccess hoApplySymbol program.clauses context.assumptions goal tree = true
  | .failure tree => checkFailure hoApplySymbol program.clauses context.assumptions goal tree = true

theorem combineBodies_spec {evaluateBody : Term Variable Literal Symbol → Option (Verdict Variable Literal Symbol)} :
    ∀ {bodies : List (List (Term Variable Literal Symbol))} {verdict : Verdict Variable Literal Symbol},
      (∀ body ∈ bodies, ∀ verdict, evaluateBody (.conjunction body) = some verdict →
        verdict.Checks program context (.conjunction body)) →
      combineBodies evaluateBody bodies = some verdict →
        (∃ body proof, verdict = .success (.clause body proof) ∧ body ∈ bodies ∧
          checkSuccess hoApplySymbol program.clauses context.assumptions (.conjunction body) proof = true) ∨
        ∃ refuted, verdict = .failure (.atom refuted) ∧
          checkFailures hoApplySymbol program.clauses context.assumptions bodies refuted = true
  | [], verdict, _, combined => by
      simp only [combineBodies, Option.some.injEq] at combined
      subst combined
      exact .inr ⟨.nil, rfl, rfl⟩
  | body :: rest, verdict, each, combined => by
      unfold combineBodies at combined
      split at combined
      · rename_i proof bodyEq
        cases combined
        exact .inl ⟨body, proof, rfl, List.mem_cons_self, each body List.mem_cons_self _ bodyEq⟩
      · rename_i refuted bodyEq
        have first : checkFailure hoApplySymbol program.clauses context.assumptions (.conjunction body) refuted = true :=
          each body List.mem_cons_self _ bodyEq
        have later := fun other member => each other (List.mem_cons_of_mem _ member)
        split at combined
        · rename_i refutedRest restEq
          cases combined
          rcases combineBodies_spec later restEq with ⟨_, _, impossible, _⟩ | ⟨refutedRest', same, checked⟩
          · cases impossible
          · cases same
            exact .inr ⟨_, rfl, by simp [checkFailures, first, checked]⟩
        · rename_i other notAtom
          rcases combineBodies_spec later combined with ⟨found, proof, rfl, member, checked⟩ | ⟨refutedRest, rfl, _⟩
          · exact .inl ⟨found, proof, rfl, List.mem_cons_of_mem _ member, checked⟩
          · exact absurd combined (notAtom refutedRest)
      · cases combined

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem combineBodies_total {evaluateBody : Term Variable Literal Symbol → Option (Verdict Variable Literal Symbol)} :
    ∀ {bodies : List (List (Term Variable Literal Symbol))},
      (∀ body ∈ bodies, evaluateBody (.conjunction body) ≠ none) → combineBodies evaluateBody bodies ≠ none
  | [], _ => by simp [combineBodies]
  | body :: rest, each => by
      unfold combineBodies
      split
      · simp
      · split
        · simp
        · exact combineBodies_total (fun other member => each other (List.mem_cons_of_mem _ member))
      · rename_i bodyEq; exact absurd bodyEq (each body List.mem_cons_self)

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem body_isGoal {head : Term Variable Literal Symbol} {body : List (Term Variable Literal Symbol)}
    (member : HornClause.definite head body ∈ program.clauses) : IsGoal hoApplySymbol (.conjunction body) := by
  cases program.wellFormed _ member with
  | definite _ goals => exact conjunction_isGoal goals

/-- The evaluator's witnesses check. -/
theorem evaluate_sound : ∀ (bound : Nat) {goal : Term Variable Literal Symbol}, IsGoal hoApplySymbol goal →
    ∀ {verdict : Verdict Variable Literal Symbol},
      evaluate program.clauses context.assumptions bound goal = some verdict → verdict.Checks program context goal := by
  intro bound
  induction bound with
  | zero =>
      intro goal valid
      induction valid with
      | atom atomic => cases atomic with | app _ _ => intro verdict evaluated; simp [evaluate] at evaluated
      | truth => intro verdict evaluated; rw [evaluate] at evaluated; cases evaluated; rfl
      | falsity => intro verdict evaluated; rw [evaluate] at evaluated; cases evaluated; rfl
      | @conj left right leftValid rightValid ihLeft ihRight =>
          intro verdict evaluated
          rw [evaluate] at evaluated
          split at evaluated
          · rename_i refuted leftEq; cases evaluated
            exact (by simp [Verdict.Checks, checkFailure, isGoal_iff.mpr rightValid]; exact ihLeft leftEq)
          · rename_i leftProof leftEq
            split at evaluated
            · rename_i rightProof rightEq; cases evaluated
              simp only [Verdict.Checks, checkSuccess, Bool.and_eq_true]
              exact ⟨ihLeft leftEq, ihRight rightEq⟩
            · rename_i refuted rightEq; cases evaluated
              simp only [Verdict.Checks, checkFailure, Bool.and_eq_true]
              exact ⟨isGoal_iff.mpr leftValid, ihRight rightEq⟩
            · cases evaluated
          · cases evaluated
      | @defaultNeg operand inner ih =>
          intro verdict evaluated
          rw [evaluate] at evaluated
          split at evaluated
          · rename_i proof operandEq; cases evaluated; exact ih operandEq
          · rename_i refuted operandEq; cases evaluated; exact ih operandEq
          · cases evaluated
  | succ bound outer =>
      intro goal valid
      induction valid with
      | @atom atom atomic =>
          cases atomic with
          | app different dataArgs =>
              rename_i symbol args
              intro verdict evaluated
              rw [evaluate] at evaluated
              have atomCheck : isAtom hoApplySymbol (.app symbol args) = true := isAtom_iff.mpr (.app different dataArgs)
              split at evaluated
              · rename_i present
                cases evaluated
                simp [Verdict.Checks, checkSuccess, atomCheck, present]
              · rename_i absent
                have each : ∀ body ∈ matchingBodies program.clauses (.app symbol args), ∀ verdict,
                    evaluate program.clauses context.assumptions bound (.conjunction body) = some verdict →
                      verdict.Checks program context (.conjunction body) := fun body member _ bodyEq =>
                  outer (body_isGoal (mem_matchingBodies.mp member)) bodyEq
                rcases combineBodies_spec each evaluated with ⟨body, proof, rfl, member, checked⟩ |
                    ⟨refuted, rfl, checked⟩
                · simp [Verdict.Checks, checkSuccess, atomCheck, member, checked]
                · simp [Verdict.Checks, checkFailure, atomCheck, absent, checked]
      | truth => intro verdict evaluated; rw [evaluate] at evaluated; cases evaluated; rfl
      | falsity => intro verdict evaluated; rw [evaluate] at evaluated; cases evaluated; rfl
      | @conj left right leftValid rightValid ihLeft ihRight =>
          intro verdict evaluated
          rw [evaluate] at evaluated
          split at evaluated
          · rename_i refuted leftEq; cases evaluated
            exact (by simp [Verdict.Checks, checkFailure, isGoal_iff.mpr rightValid]; exact ihLeft leftEq)
          · rename_i leftProof leftEq
            split at evaluated
            · rename_i rightProof rightEq; cases evaluated
              simp only [Verdict.Checks, checkSuccess, Bool.and_eq_true]
              exact ⟨ihLeft leftEq, ihRight rightEq⟩
            · rename_i refuted rightEq; cases evaluated
              simp only [Verdict.Checks, checkFailure, Bool.and_eq_true]
              exact ⟨isGoal_iff.mpr leftValid, ihRight rightEq⟩
            · cases evaluated
          · cases evaluated
      | @defaultNeg operand inner ih =>
          intro verdict evaluated
          rw [evaluate] at evaluated
          split at evaluated
          · rename_i proof operandEq; cases evaluated; exact ih operandEq
          · rename_i refuted operandEq; cases evaluated; exact ih operandEq
          · cases evaluated

/-- Under a rank, the evaluator answers every ground goal at a bound covering
its level. -/
theorem evaluate_total {rank : Term Variable Literal Symbol → Nat} (ranked : Ranked rank program.clauses) :
    ∀ (bound : Nat) {goal : Term Variable Literal Symbol}, IsGoal hoApplySymbol goal → level rank goal ≤ bound →
      evaluate program.clauses context.assumptions bound goal ≠ none := by
  intro bound
  induction bound with
  | zero =>
      intro goal valid below
      induction valid with
      | atom atomic => cases atomic with | app _ _ => simp at below
      | truth => rw [evaluate]; simp
      | falsity => rw [evaluate]; simp
      | conj leftValid rightValid ihLeft ihRight =>
          simp only [level_conj, Nat.max_le] at below
          rw [evaluate]
          split
          · simp
          · split
            · simp
            · simp
            · rename_i rightEq; exact absurd rightEq (ihRight below.2)
          · rename_i leftEq; exact absurd leftEq (ihLeft below.1)
      | defaultNeg inner ih =>
          rw [evaluate]
          split
          · simp
          · simp
          · rename_i operandEq; exact absurd operandEq (ih below)
  | succ bound outer =>
      intro goal valid below
      induction valid with
      | atom atomic =>
          cases atomic with
          | app _ _ =>
              rename_i symbol args
              rw [evaluate]
              split
              · simp
              · apply combineBodies_total
                intro body member
                have listed := mem_matchingBodies.mp member
                rw [level_app] at below
                exact outer (body_isGoal listed) (Nat.le_trans (ranked.level_body listed) (by omega))
      | truth => rw [evaluate]; simp
      | falsity => rw [evaluate]; simp
      | conj leftValid rightValid ihLeft ihRight =>
          simp only [level_conj, Nat.max_le] at below
          rw [evaluate]
          split
          · simp
          · split
            · simp
            · simp
            · rename_i rightEq; exact absurd rightEq (ihRight below.2)
          · rename_i leftEq; exact absurd leftEq (ihLeft below.1)
      | defaultNeg inner ih =>
          rw [evaluate]
          split
          · simp
          · simp
          · rename_i operandEq; exact absurd operandEq (ih below)

/-- Under a rank, a failing ground goal gets a failure witness that checks. -/
theorem evaluate_failure {rank : Term Variable Literal Symbol → Nat} (ranked : Ranked rank program.clauses)
    {bound : Nat} {goal : Term Variable Literal Symbol} (valid : IsGoal hoApplySymbol goal)
    (below : level rank goal ≤ bound) (failed : Fails program context goal) :
    ∃ tree, (evaluate program.clauses context.assumptions bound goal).bind Verdict.failure? = some tree ∧
      checkFailure hoApplySymbol program.clauses context.assumptions goal tree = true := by
  cases evaluated : evaluate program.clauses context.assumptions bound goal with
  | none => exact absurd evaluated (evaluate_total ranked bound valid below)
  | some verdict =>
      have checked := evaluate_sound bound valid evaluated
      cases verdict with
      | success tree => exact absurd (checkSuccess_sound _ _ checked) (fails_not_succeeds failed)
      | failure tree => exact ⟨tree, rfl, checked⟩

end Evaluation

end AnthillModKbSpec.GroundSearch
