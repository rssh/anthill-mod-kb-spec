import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Semantics

namespace EquationOracleTests

open OrderDictionaries

abbrev T := Term String Data Symbol
abbrev K := LogicalKb String Data Symbol

def left : T := .app .natCompare [.lit (.nat 2), .lit (.nat 3)]
def right : T := .lit (.ordering .lt)
def conclusion : T := .app .isBool [.lit (.bool true)]
def rule : HornClause String Data Symbol := .definite conclusion [.equal left right]
def kb : K := {rule}
def oracle := EquationOracle.closed model String
def extended := oracle.extend kb

theorem kb_valid : model.Models kb := by
  intro clause member environment
  have same : clause = rule := by simpa [kb] using member
  subst clause
  simp only [rule, HornClause.toFormula, Model.Satisfies, Model.eval]
  apply (model.holds_implication _ _).mpr
  intro _
  simp [conclusion, Model.eval, model, OperationDictionaries.Extension.withDictionaryCalls,
    baseModel, application, primitive, holds]

theorem accepted : oracle.certifies [] left right := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [left, Term.freeVars]
  · simp [right, Term.freeVars]
  · simp [left, right, Model.eval, model, OperationDictionaries.Extension.withDictionaryCalls,
      baseModel, application, primitive, compareNat]

theorem equality_proof {naf : NafFailure String Data Symbol} :
    Derives .hoApply extended [] (.equal left right) naf :=
  oracle.derive kb accepted .truth

theorem predicate_proof {naf : NafFailure String Data Symbol} :
    Derives .hoApply extended [] conclusion naf :=
  .clause (body := [.equal left right]) (σ := Term.var)
    (oracle.base_mem (by simp [kb, rule])) (Substitutes.identity _)
    (Substitutes.identity _) (.conjIntro equality_proof .truth)

-- Accepted computed equality enables a body equation in an ordinary rule.
example (environment : Environment String Value) : model.Satisfies environment conclusion :=
  model.sound_with_equation_oracle oracle kb_valid (model.disabled_adequate extended)
    predicate_proof environment (by intro assumption member; cases member)

example : ¬ Derives .hoApply extended [] .falsity :=
  model.consistent_with_equation_oracle oracle kb_valid (model.disabled_adequate extended)

-- Wrong computations are not accepted by the concrete oracle.
example : ¬ oracle.certifies [] left (.lit (.ordering .gt)) := by
  simp [oracle, EquationOracle.closed, left, Term.freeVars, Model.eval, model,
    OperationDictionaries.Extension.withDictionaryCalls, baseModel, application, primitive, compareNat]

-- A closed-computation oracle can leave even a valid open equality unanswered.
example : ¬ oracle.certifies [] (.var "x") (.var "x") := by
  simp [oracle, EquationOracle.closed, Term.freeVars]

example : Derives .hoApply extended [] (.equal (.var "x") (.var "x")) := .equalRefl

-- Positive oracle assistance and NAF use one exact extended KB.
theorem complement : model.ComplementNAF := by intro value; rfl

example (environment : Environment String Value) :
    model.Satisfies environment (.conj conclusion (.defaultNeg .falsity)) := by
  apply model.sound_with_equation_oracle oracle kb_valid
    (CertifiedRefutation.failureAdequate model complement extended)
    (proof := .conjIntro predicate_proof
      ((CertifiedRefutation.Refutes.falsity (model := model) (kb := extended) (context := [])).toDerives
        (by simp [Term.freeVars]))) environment
  intro assumption member; cases member

-- A conditional oracle can accept any equality under that equality as a premise.
def conditionalOracle : EquationOracle model String where
  certifies body left right := body = [.equal left right]
  sound := by
    intro body left right accepted environment condition
    subst body
    apply (model.satisfies_equal environment left right).mp
    simp only [Model.Satisfies, Term.conjunction, List.foldr_cons, List.foldr_nil, Model.eval]
      at condition ⊢
    exact ((model.holds_conjunction _ _).mp condition).1

def zero : T := .lit (.nat 0)
def one : T := .lit (.nat 1)

example : conditionalOracle.certifies [.equal zero one] zero one := rfl

-- Accepting this guarded claim cannot manufacture a proof of its false premise.
example : ¬ Derives .hoApply (conditionalOracle.extend kb) [] (.equal zero one) := by
  intro proof
  have result := model.sound_with_equation_oracle conditionalOracle kb_valid
    (model.disabled_adequate (conditionalOracle.extend kb)) proof
    (fun _ => .invalid) (by intro assumption member; cases member)
  have equal := (model.satisfies_equal _ zero one).mp result
  simp [zero, one, Model.eval, model, OperationDictionaries.Extension.withDictionaryCalls, baseModel] at equal

end EquationOracleTests

namespace InductiveEquationOracleTests

open InductionModel

private def interpretation : InductiveSoundness.Interpretation family kb Value .hoApply :=
  ⟨model, membershipSymbol, realizes, kb_models, complement⟩

private def oracle := EquationOracle.closed model String
private def extended := oracle.extend kb

private theorem accepted : oracle.certifies [] zero zero :=
  ⟨rfl, by simp [zero, Term.freeVars], by simp [zero, Term.freeVars], rfl⟩

private theorem proof : Derives .hoApply extended [] (.conj (.equal zero zero) (reachable zero))
    (CertifiedRefutation.failureEvidence model extended) :=
  .conjIntro (oracle.derive kb accepted .truth)
    (.clause (body := []) (σ := Term.var)
      (oracle.base_mem (by simp [kb, reachableZero]))
      (Substitutes.identity _) (Substitutes.identity _) .truth)

-- The main packaged theorem retains the nonempty KB's induction and membership.
example (environment : Environment String Value) :
    model.Satisfies environment (.conj (.equal zero zero) (reachable zero)) :=
  InductiveSoundness.declarative_sound_with_equation_oracle interpretation oracle proof
    environment (by intro assumption member; cases member)

example : ¬ Derives .hoApply extended [] .falsity
    (CertifiedRefutation.failureEvidence model extended) :=
  InductiveSoundness.declarative_consistent_with_equation_oracle interpretation oracle

example (environment : Environment String Value) :
    model.Satisfies environment (.conj (.equal zero zero) (reachable zero)) :=
  InductiveSoundness.sound_with_equation_oracle interpretation oracle
    (parameters := []) (.declarative proof)
    environment (by intro assumption member; cases member)

end InductiveEquationOracleTests
