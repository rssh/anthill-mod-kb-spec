import AnthillModKbSpec.Models.OrderDictionaries
import AnthillModKbSpec.Foundation.ClauseInstantiation

open AnthillModKbSpec AnthillModKbSpec.Semantics AnthillModKbSpec.OrderDictionaries

namespace EquationRuleTests

abbrev T := Term String Data Symbol
abbrev K := LogicalKb String Data Symbol

def natEqualSelf (value : T) : T := .app .natEqual [value, value]
def isNat (value : T) : T := .app .isNat [value]
def trueValue : T := .lit (.bool true)
def three : T := .lit (.nat 3)

-- natEqual(x,x) <=> true :- isNat(x).
def natEquation : HornClause String Data Symbol :=
  .equation (natEqualSelf (.var "x")) trueValue [isNat (.var "x")]

-- An equation can also be a goal on the right of an ordinary predicate rule.
-- isBool(natEqual(x,x)) :- natEqual(x,x) <=> true.
def equationBodyRule : HornClause String Data Symbol :=
  .definite (.app .isBool [natEqualSelf (.var "x")])
    [.equal (natEqualSelf (.var "x")) trueValue]

def natFact : HornClause String Data Symbol := .definite (isNat three) []
def kb : K := {natEquation, natFact, equationBodyRule}

theorem equation_valid (environment : Environment String Value) :
    model.Satisfies environment natEquation.toFormula := by
  apply (model.satisfies_equation environment _ _ _).mpr
  intro condition
  simp only [Model.Satisfies, Term.conjunction, List.foldr_cons, List.foldr_nil,
    Model.eval, isNat, List.map_cons, List.map_nil] at condition
  have positive := ((model.holds_conjunction _ _).mp condition).1
  have exactDomain := nat_member_exact (environment "x")
  rw [natOrd, member_dictionary _ _ _ rfl] at exactDomain
  have domain : NatDomain (environment "x") := exactDomain.mp positive
  obtain ⟨n, value⟩ := domain
  simp only [natEqualSelf, trueValue, Model.eval, List.map_cons, List.map_nil]
  change application .natEqual [environment "x", environment "x"] = boolean true
  rw [value]
  simp [application, primitive]

theorem fact_valid (environment : Environment String Value) :
    model.Satisfies environment natFact.toFormula := by
  simp only [natFact, HornClause.toFormula, Model.Satisfies, Model.eval]
  apply (model.holds_implication _ _).mpr
  intro _
  simp [isNat, three, Model.eval, model, OperationDictionaries.Extension.withDictionaryCalls,
    baseModel, application, primitive, holds]

theorem equation_body_valid (environment : Environment String Value) :
    model.Satisfies environment equationBodyRule.toFormula := by
  simp only [equationBodyRule, HornClause.toFormula, Model.Satisfies, Term.conjunction,
    List.foldr_cons, List.foldr_nil, Model.eval]
  apply (model.holds_implication _ _).mpr
  intro condition
  have values := (model.holds_equality _ _).mp (((model.holds_conjunction _ _).mp condition).1)
  simp only [List.map_cons, List.map_nil]
  rw [values]
  simp only [trueValue, Model.eval]
  change holds (application .isBool [boolean true])
  simp [application, primitive, holds]

theorem kb_valid : model.Models kb := by
  intro clause member environment
  simp only [kb, LogicalKb.mem_insert, LogicalKb.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · exact equation_valid environment
  · exact fact_valid environment
  · exact equation_body_valid environment

theorem fact_proof : Derives .hoApply kb [] (isNat three) :=
  .clause (body := []) (σ := Term.var) (by simp [kb, natFact])
    (Substitutes.identity _) (Substitutes.identity _) .truth

def substitution : Substitution String Data Symbol :=
  Substitution.single "x" three

theorem equation_proof : Derives .hoApply kb [] (.equal (natEqualSelf three) trueValue) := by
  apply Derives.equation (left := natEqualSelf (.var "x")) (right := trueValue)
    (body := [isNat (.var "x")]) (σ := substitution)
    (condition := .conj (isNat three) .truth)
  · simp [kb, natEquation]
  · apply Term.instantiate?_sound
    simp [natEqualSelf, substitution, Substitution.single, Substitution.bind, Term.instantiate?, List.mapM_cons]
  · exact .lit
  · apply Term.instantiate?_sound
    simp [Term.conjunction, isNat, substitution, Substitution.single,
      Substitution.bind, Term.instantiate?, List.mapM_cons]
  · exact .conjIntro fact_proof .truth

-- The body equation is proved using natEquation; it enables this predicate head.
theorem equation_body_proof : Derives .hoApply kb [] (.app .isBool [natEqualSelf three]) := by
  apply Derives.clause (head := .app .isBool [natEqualSelf (.var "x")])
    (body := [.equal (natEqualSelf (.var "x")) trueValue]) (σ := substitution)
    (instantiatedBody := .conj (.equal (natEqualSelf three) trueValue) .truth)
  · simp [kb, equationBodyRule]
  · apply Term.instantiate?_sound
    simp [natEqualSelf, substitution, Substitution.single, Substitution.bind,
      Term.instantiate?, List.mapM_cons]
  · apply Term.instantiate?_sound
    simp [Term.conjunction, natEqualSelf, trueValue, substitution, Substitution.single,
      Substitution.bind, Term.instantiate?, List.mapM_cons]
  · exact .conjIntro equation_proof .truth

example (environment : Environment String Value) :
    model.Satisfies environment (.app .isBool [natEqualSelf three]) :=
  model.positive_sound kb_valid equation_body_proof environment (by intro assumption member; cases member)

-- A false body equation does not enable the same rule at a non-Nat argument.
example : ¬ Derives .hoApply kb [] (.app .isBool [natEqualSelf (.lit (.ordering .lt))]) := by
  intro proof
  have result := model.positive_sound kb_valid proof (fun _ => .invalid)
    (by intro assumption member; cases member)
  simp [Model.Satisfies, natEqualSelf, Model.eval, model,
    OperationDictionaries.Extension.withDictionaryCalls, baseModel, application, primitive, holds] at result

-- Use the conditional equation inside a dictionary-operation argument.
def beforeCall : T := compareTerm (.var "D") (natEqualSelf three) (.lit (.bool false))
def afterCall : T := compareTerm (.var "D") trueValue (.lit (.bool false))
def contextTemplate : T :=
  .equal beforeCall (compareTerm (.var "D") (.var "hole") (.lit (.bool false)))

theorem context_rewrite : Derives .hoApply kb [] (.equal beforeCall afterCall) := by
  apply Derives.equalSubst (name := "hole") (a := natEqualSelf three) (b := trueValue)
    (template := contextTemplate) (before := .equal beforeCall beforeCall)
  · exact equation_proof
  · apply Term.instantiate?_sound
    simp [contextTemplate, beforeCall, compareTerm, natEqualSelf, three,
      Substitution.single, Substitution.bind, Term.instantiate?, List.mapM_cons]
  · apply Term.instantiate?_sound
    simp [contextTemplate, beforeCall, afterCall, compareTerm, natEqualSelf, three, trueValue,
      Substitution.single, Substitution.bind, Term.instantiate?, List.mapM_cons]
  · exact .equalRefl

-- Soundness supplies value equality, under every dictionary assignment.
example (environment : Environment String Value) :
    model.eval environment beforeCall = model.eval environment afterCall :=
  (model.satisfies_equal environment _ _).mp
    (model.positive_sound kb_valid context_rewrite environment (by intro assumption member; cases member))

example : ¬ Derives .hoApply kb [] .falsity := model.positive_consistent kb_valid

-- Symmetry and transitivity refer to values, not a choice of rewrite direction.
example : Derives .hoApply kb [] (.equal trueValue (natEqualSelf three)) :=
  .equalSymm equation_proof

example : Derives .hoApply kb [] (.equal (natEqualSelf three) (natEqualSelf three)) :=
  .equalTrans equation_proof (.equalSymm equation_proof)

-- Removing the domain condition makes this equation false on the raw carrier.
example : ¬ model.Satisfies (fun _ : String => .invalid)
    (HornClause.equation (natEqualSelf (.var "x")) trueValue []).toFormula := by
  intro valid
  have condition : model.Satisfies (fun _ : String => .invalid) (.conjunction []) := by
    simpa [Model.Satisfies, Term.conjunction, Model.eval] using model.holds_top
  have equal := (model.satisfies_equation _ _ _ _).mp valid condition
  simp [natEqualSelf, trueValue, Model.eval, model,
    OperationDictionaries.Extension.withDictionaryCalls, baseModel, application, primitive] at equal

-- Logical truth equivalence does not identify distinct formula values.
example : model.holds (boolean true) ∧ model.holds (.proposition True) ∧
    ¬ model.Satisfies (fun _ : String => .invalid)
      (.equal (.lit (.bool true)) .truth) := by
  refine ⟨rfl, True.intro, ?_⟩
  rw [model.satisfies_equal]
  simp [Model.eval, model, OperationDictionaries.Extension.withDictionaryCalls, baseModel]

-- Substitution and binder checks traverse both sides of equality.
example : (Term.forallVar "y" (.equal (.var "x") (.var "y")) : T).instantiate?
    (Substitution.single "x" (.var "y")) = none := by
  simp [Term.instantiate?, Term.freeVars, Substitution.single, Substitution.bind]

end EquationRuleTests
