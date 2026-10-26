import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Semantics AnthillModKbSpec.InductiveDomains
open AnthillModKbSpec.InductiveDomains.CounterexampleSearch

namespace FiniteCounterexampleExample

private abbrev T := Term String Nat String
private def yes : Tree String := .node "yes" []
private def no : Tree String := .node "no" []
private def rYes : Rule Unit String := ⟨(), "yes", []⟩
private def rNo : Rule Unit String := ⟨(), "no", []⟩
private def sigma : Definitions Unit String := fun rule => rule = rYes ∨ rule = rNo
private def family : FiniteFamily Unit String := ⟨sigma, [()], by intro domain; cases domain; simp⟩
private def membershipSymbol : Unit → String := fun _ => "isBool"

private theorem yesMember : Member sigma () yes := by
  simpa [rYes, yes] using Member.construct (rule := rYes) (Or.inl rfl)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
private theorem noMember : Member sigma () no := by
  simpa [rNo, no] using Member.construct (rule := rNo) (Or.inr rfl)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

private def cover : Cover sigma () := ⟨[yes, no], by
  intro tree selected; simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with rfl | rfl
  · exact yesMember
  · exact noMember, by
  intro tree member
  cases member with
  | construct declared children members =>
      rcases declared with rfl | rfl
      all_goals dsimp only [rYes, rNo] at children ⊢
      · simp [yes]
      · simp [no]⟩

private def symbolValue (symbol : String) : Bool := symbol != "missing"
private def model : Model Nat String Bool "ho_apply" :=
  { Model.trueAtoms Nat String "ho_apply" with
    application := fun symbol args => symbolValue symbol && args.all id
    holds_hoApply := by intro predicate args; simp [symbolValue, List.all_cons, Model.trueAtoms] }

private theorem memberTrue {tree : Tree String} (member : Member sigma () tree) : denote model tree = true := by
  cases member with
  | construct declared children members =>
      rcases declared with rfl | rfl
      all_goals dsimp only [rYes, rNo] at children ⊢
      all_goals simp [denote, model, symbolValue]

private theorem realizes : Realizes model sigma membershipSymbol := by
  intro domain value
  constructor
  · intro member
    have same : value = true := by simpa [model, Model.trueAtoms, membershipSymbol, symbolValue] using member
    exact ⟨yes, yesMember, (memberTrue yesMember).trans same.symm⟩
  · rintro ⟨tree, member, same⟩
    have valueTrue : value = true := same.symm.trans (memberTrue member)
    simp [model, Model.trueAtoms, membershipSymbol, symbolValue, valueTrue]

private theorem complement : model.ComplementNAF := by
  intro value
  change (!value = true ↔ ¬value = true)
  cases value <;> decide

private def fact (tree : Tree String) : HornClause String Nat String :=
  .definite (.app "p" [tree.toTerm]) []
private def kb : LogicalKb String Nat String := {fact yes, fact no}
private theorem models : model.Models kb := by
  intro clause member environment
  simp only [kb, LogicalKb.mem_insert, LogicalKb.mem_singleton] at member
  rcases member with rfl | rfl
  all_goals
    simp [fact, HornClause.toFormula, Term.conjunction, Tree.toTerm, yes, no,
      Model.Satisfies, Model.eval, model, Model.trueAtoms, symbolValue]

private def goal : Universal Unit String Nat String := family.forallAll "x" (.app "p" [.var "x"])

-- Each inner NAF query fails because its positive constructor instance has a
-- KB proof, not because a generic rigid query happened to fail.
private theorem reject (tree : Tree String) (member : tree ∈ cover.values) : Rejected model [] goal tree := by
  apply Rejected.ofEstablished (instantiated := .app "p" [tree.toTerm])
  · exact .app (.cons (.singleVar "x" tree.toTerm) .nil)
  · apply CertifiedRefutation.Established.ofPositive model models
    apply Derives.clause (head := .app "p" [tree.toTerm]) (body := []) (σ := Term.var)
    · simp only [cover, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [kb, fact]
    · exact Substitutes.identity _
    · exact .truth
    · exact .truth

private theorem failed : Fails model sigma [] goal := by
  apply Fails.ofCovers (covers := fun domain selected => by cases domain; exact cover)
  intro domain selected tree member
  exact reject tree member

example (environment : Environment String Bool) : model.Satisfies environment (goal.toTerm membershipSymbol) :=
  failed.sound realizes environment (by intro assumption member; cases member)

example (environment : Environment String Bool) :
    ¬ model.Satisfies environment (goal.counterexample membershipSymbol) :=
  failed.counterexample_fails realizes environment (by intro assumption member; cases member)

example (environment : Environment String Bool) :
    model.Satisfies environment (.defaultNeg (goal.counterexample membershipSymbol)) :=
  failed.counterexample_naf realizes complement environment (by intro assumption member; cases member)

example (program : ScopedSearch.Program String Nat String "ho_apply") :
    CertifiedScopedSearch.Succeeds model program (⟨[], [], by simp⟩ : ScopedSearch.Context String Nat String "ho_apply")
      (goal.toTerm membershipSymbol) := failed.toSucceeds realizes

-- A finite family is not a license to omit inhabitants from its cover.
example : ¬ (∀ tree, Member sigma () tree → tree ∈ [yes]) := by
  intro complete
  have impossible := complete no noMember
  simp [yes, no] at impossible

private def missingGoal : Universal Unit String Nat String := family.forallAll "x" (.app "missing" [.var "x"])

example : ¬ Fails model sigma [] missingGoal := by
  intro purported
  have check := purported.exhaustive yes ⟨(), by simp [missingGoal, FiniteFamily.forallAll, family], yesMember⟩
  have impossible := check.established (fun _ => true) (by intro assumption member; cases member)
  simp [missingGoal, FiniteFamily.forallAll, Model.Satisfies, Model.eval, model, Model.trueAtoms, symbolValue] at impossible

example (environment : Environment String Bool) :
    model.Satisfies environment (missingGoal.counterexample membershipSymbol) := by
  apply (missingGoal.counterexample_iff model realizes environment).mpr
  refine ⟨yes, ⟨(), by simp [missingGoal, FiniteFamily.forallAll, family], yesMember⟩, ?_⟩
  simp [missingGoal, FiniteFamily.forallAll, Model.Satisfies, Model.eval, model, Model.trueAtoms, symbolValue]

-- No values is an exhaustive cover for the empty union, for any property.
example : Fails model sigma [] (⟨[], "x", .falsity⟩ : Universal Unit String Nat String) := by
  apply Fails.ofCovers (covers := fun domain selected => False.elim (List.not_mem_nil selected))
  intro domain selected; simp at selected

end FiniteCounterexampleExample

namespace InductiveCounterexampleExample

open AnthillModKbSpec.InductionModel

private def goal : Universal Domain String Unit Symbol := family.forallAll "x" (reachable (.var "x"))
private theorem cases : Induction sigma (fun _ tree => ∃ n, denote model tree = natValue n) := by
  constructor
  intro rule declared children members ih
  rcases declared with rfl | rfl
  all_goals dsimp only [zeroRule, succRule] at children members ih ⊢
  · exact ⟨0, by simp [denote]⟩
  · obtain ⟨n, same⟩ := ih 0
    exact ⟨n + 1, by simp [denote, same]⟩

-- Infinite Nat uses an induction certificate, never an asserted finite cover.
private theorem failed : Fails model sigma [] goal := by
  apply Fails.ofInduction cases
  intro domain selected tree ⟨n, same⟩
  constructor
  intro environment assumptions
  simp only [goal, FiniteFamily.forallAll, reachable, Model.Satisfies, Model.eval,
    List.map_cons, List.map_nil, update, ite_true, same]
  exact reachable_at_nat n

example (environment : Environment String Value) : model.Satisfies environment (goal.toTerm membershipSymbol) :=
  failed.sound realizes environment (by intro assumption member; cases member)

example (environment : Environment String Value) :
    model.Satisfies environment (goal.toTerm membershipSymbol) ↔
      ¬ model.Satisfies environment (goal.counterexample membershipSymbol) :=
  goal.satisfies_iff_no_counterexample model realizes complement environment

example (environment : Environment String Value) :
    model.Satisfies environment (goal.toTerm membershipSymbol) ↔
      model.Satisfies environment (.defaultNeg (goal.counterexample membershipSymbol)) :=
  goal.satisfies_iff_counterexample_naf model realizes complement environment

-- A genuine generated counterexample rules out exhaustive failure.
example : ¬ Fails model sigma [] (family.forallAll "x" (even (.var "x"))) := by
  intro purported
  have check := purported.exhaustive (natTree 1)
    ⟨.nat, by simp [FiniteFamily.forallAll, family], natTree_member 1⟩
  have impossible := check.established (fun _ => model.inhabitant) (by intro assumption member; cases member)
  simp only [FiniteFamily.forallAll, even, Model.Satisfies, Model.eval,
    List.map_cons, List.map_nil, update, ite_true, natTree_denote] at impossible
  exact (by decide : ¬ 1 % 2 = 0) ((even_at_nat 1).mp impossible)

end InductiveCounterexampleExample
