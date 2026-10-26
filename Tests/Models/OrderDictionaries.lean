import AnthillModKbSpec.Models.OrderDictionaries

open AnthillModKbSpec AnthillModKbSpec.OperationDictionaries
open AnthillModKbSpec.OrderDictionaries

namespace OrderDictionaryTests

abbrev T := Term String Data Symbol

def compareGoal : T := compareTerm (.var "ord") (.var "a") (.var "b")
def equalGoal : T := equalTerm (.var "ord") (.var "a") (.var "b")

def environment (dict a b : Value) : Semantics.Environment String Value := fun name =>
  if name = "ord" then dict else if name = "a" then a else b

theorem compare_evaluates (dict a b : Value) :
    model.eval (environment dict a b) compareGoal = comparison dict a b := by
  rw [compareGoal, eval_compareTerm]
  simp [Semantics.Model.eval, environment]

theorem equal_evaluates (dict a b : Value) :
    model.eval (environment dict a b) equalGoal = equality dict a b := by
  rw [equalGoal, eval_equalTerm]
  simp [Semantics.Model.eval, environment]

-- Shared syntax, two dictionary values, two intended domains.
example : model.eval (environment natOrd (nat 2) (nat 3)) compareGoal = ordering .lt := by
  rw [compare_evaluates, nat_comparison]; rfl

example : model.eval (environment natOrd (nat 9) (nat 2)) compareGoal = ordering .gt := by
  rw [compare_evaluates, nat_comparison]; rfl

example : model.eval (environment natOrd (nat 4) (nat 4)) compareGoal = ordering .eq := by
  rw [compare_evaluates, nat_comparison]; rfl

example : model.eval (environment boolOrd (boolean false) (boolean true)) compareGoal = ordering .lt := by
  rw [compare_evaluates, bool_comparison]; rfl

example : model.eval (environment boolOrd (boolean true) (boolean false)) compareGoal = ordering .gt := by
  rw [compare_evaluates, bool_comparison]; rfl

example : model.eval (environment boolOrd (boolean true) (boolean true)) compareGoal = ordering .eq := by
  rw [compare_evaluates, bool_comparison]; rfl

-- The Eq dictionary is reached one level deeper and produces Boolean values.
example : model.eval (environment natOrd (nat 7) (nat 7)) equalGoal = boolean true := by
  rw [equal_evaluates, nat_equality]; rfl

example : model.eval (environment boolOrd (boolean false) (boolean true)) equalGoal = boolean false := by
  rw [equal_evaluates, bool_equality]; rfl

-- An operation returning Bool can be inspected in formula position.
example : model.Satisfies (environment natOrd (nat 7) (nat 7)) equalGoal := by
  unfold Semantics.Model.Satisfies
  rw [equal_evaluates, nat_equality]
  rfl

example : Implements extension natOrd (ordInterface NatDomain) := nat_implements
example : Implements extension boolOrd (ordInterface BoolDomain) := bool_implements

-- Required models carry their own interface proofs, including Eq's law.
example : ∃ weak, extension.subdictionary natOrd .weakOrd = some weak ∧
    Implements extension weak (weakOrdInterface NatDomain) :=
  Implements.required_model extension nat_implements .weakOrd _ (by simp)

example (a b c : Nat) : LessEq natOrd (nat a) (nat b) → LessEq natOrd (nat b) (nat c) →
    LessEq natOrd (nat a) (nat c) :=
  nat_laws.transitive _ _ _ ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩

example (a b : Bool) : LessEq boolOrd (boolean a) (boolean b) →
    LessEq boolOrd (boolean b) (boolean a) → boolean a = boolean b :=
  bool_laws.antisymmetric _ _ ⟨a, rfl⟩ ⟨b, rfl⟩

-- Domains are separate even though the value carrier and interface are shared.
example : ¬ Implements extension natOrd (ordInterface BoolDomain) := by
  intro valid
  rw [ordInterface, Implements] at valid
  have member := (valid.2.2.1 (boolean false)).mpr ⟨false, rfl⟩
  rw [nat_member_exact] at member
  obtain ⟨n, impossible⟩ := member
  cases impossible

example : comparison natOrd (boolean false) (boolean true) = .invalid := by
  simp only [comparison, model, Extension.withDictionaryCalls, natOrd]
  rw [lookup_compare _ _ _ rfl]
  simp only [Extension.invoke_eq]
  simp [baseModel, application, primitive]

end OrderDictionaryTests
