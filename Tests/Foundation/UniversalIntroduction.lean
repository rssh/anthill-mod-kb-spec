import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Semantics AnthillModKbSpec.InductiveDomains
open AnthillModKbSpec.InductionModel

-- The requested shape: forall x : D_all, g(x) -> p(x), with no
-- conjunction-with-True artifact from the singleton clause body.
private def successorGoal : T :=
  (family.forallAll "x" (.imp (reachable (.var "x")) (reachable (succ (.var "x"))))).toTerm membershipSymbol

example : successorGoal = .forallVar "x" (.imp
    (InductiveDomains.guard membershipSymbol family.domains (.var "x"))
    (.imp (reachable (.var "x")) (reachable (succ (.var "x"))))) := rfl

example : Derives .hoApply kb [] successorGoal :=
  Derives.forallAll_of_single_clause family "x" (by simp [kb, reachableSucc])

example (environment : Environment String Value) : model.Satisfies environment successorGoal :=
  model.forallAll_of_single_clause family "x" kb_models (by simp [kb, reachableSucc]) environment

-- The general clause theorem also handles multiple body goals, scoped steps,
-- and predicate parameters, as in the induction rule itself.
example : Derives .hoApply kb [] ((family.forallAll "x"
    (.imp (.conjunction [isNat (.var "x"), applyP (.var "P") zero, step (.var "P")])
      (applyP (.var "P") (.var "x")))).toTerm membershipSymbol) :=
  Derives.forallAll_of_clause family "x" (by simp [kb, inductionRule])

private theorem advanceEven (context : ProofContext String Unit Symbol) (value : T)
    (proof : Derives .hoApply kb context (even value)) :
    Derives .hoApply kb context (even (succ (succ value))) := by
  apply Derives.clause (head := even (succ (succ (.var "x")))) (body := [even (.var "x")])
    (σ := fun _ => value) (instantiatedBody := .conj (even value) .truth)
  · simp [kb, evenSuccSucc]
  · exact .app (.cons (.app (.cons (.app (.cons .var .nil)) .nil)) .nil)
  · exact .conj (.app (.cons .var .nil)) .truth
  · exact .conjIntro proof .truth

-- This implication is derived by two clause applications, rather than read
-- from one stored clause. It can be universally generalized as well.
private def derivedImplication : T :=
  .imp (even (.var "x")) (even (succ (succ (succ (succ (.var "x"))))))

private theorem derivedProof : Derives .hoApply kb [] derivedImplication := by
  apply Derives.impIntro
  exact advanceEven _ _ (advanceEven _ _ (.assumption (by simp)))

example : Derives .hoApply kb [] (.forallVar "x" derivedImplication) :=
  derivedProof.generalize "x" (by intro assumption impossible; cases impossible)

example (environment : Environment String Value) :
    model.Satisfies environment ((family.forallAll "x" derivedImplication).toTerm membershipSymbol) :=
  model.forallAll_of_derives family "x" kb_models (model.disabled_adequate kb)
    (by intro assumption impossible; cases impossible) derivedProof environment
    (by intro assumption impossible; cases impossible)

-- A fixed local assumption about x cannot become a universal fact about x.
example : ¬ FreshForContext "x" [even (.var "x")] := by
  simp [FreshForContext, even, Term.freeVars]

example : ¬ Derives .hoApply kb [even (.var "x")]
    ((family.forallAll "x" (even (.var "x"))).toTerm membershipSymbol) := by
  intro proof
  let environment : Environment String Value := fun _ => natValue 0
  have assumptions : model.ContextHolds environment [even (.var "x")] := by
    intro assumption member
    simp only [List.mem_singleton] at member
    subst assumption
    simp only [even, Model.Satisfies, Model.eval, List.map_cons, List.map_nil]
    exact (even_at_nat 0).mpr rfl
  have universal := model.positive_sound kb_models proof environment assumptions
  have all := (family.forallAll_satisfies_iff model realizes environment "x" (even (.var "x"))).mp universal
  have one := all ⟨natTree 1, .intro .nat (natTree_member 1)⟩
  simp only [even, Model.Satisfies, Model.eval, List.map_cons, List.map_nil,
    update, ite_true, natTree_denote] at one
  exact (by decide : ¬ 1 % 2 = 0) ((even_at_nat 1).mp one)
