import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Semantics AnthillModKbSpec.InductiveDomains
open AnthillModKbSpec.InductionModel

-- Both KB stages contain actual clauses, and use one exact domain model.
example : inductionRule ∈ inductionKb := by simp [inductionKb]
example : inductionRule ∈ kb := by simp [kb]
example : reachableSucc ∈ kb := by simp [kb]
example : evenSuccSucc ∈ kb := by simp [kb]
example : ∃ witness : Model Unit Symbol Value .hoApply,
    Realizes witness sigma membershipSymbol ∧ witness.ComplementNAF ∧
    witness.Models inductionKb ∧ witness.Models kb := model_exists

-- Constructor denotations are distinct, unlike the earlier Bool witness.
example : natValue 0 ≠ natValue 1 := fun same => Nat.zero_ne_add_one 0 (natValue_injective same)
example : denote model (natTree 2) = natValue 2 := natTree_denote 2

-- Membership is exact on whole values: logical values with the same key but
-- different truth are excluded from Nat.
example : ¬ model.holds (model.application .isNat [(natKey 0, True)]) := by
  intro proof
  obtain ⟨n, same⟩ := (application_nat _).mp proof
  have impossible : True = False := congrArg Prod.snd same
  exact Eq.mp impossible True.intro

-- Apply the induction clause with symbolic P; no enumeration is involved.
example : Derives .hoApply kb
    [isNat (.var "x"), applyP (.var "P") zero, step (.var "P")]
    (applyP (.var "P") (.var "x")) :=
  induction_rule_applies _ (.assumption (by simp)) (.assumption (by simp)) (.assumption (by simp))

example (environment : Environment String Value) :
    model.Satisfies environment inductionRule.toFormula := inductionRule_valid environment

-- The recursive predicate clauses can also be used directly in Derives.
private theorem reachesZero : Derives .hoApply kb [] (reachable zero) :=
  .clause (head := reachable zero) (body := []) (σ := Term.var)
    (by simp [kb, reachableZero]) (Substitutes.identity _) .truth .truth

private theorem reachesSucc (value : T) (proof : Derives .hoApply kb [] (reachable value)) :
    Derives .hoApply kb [] (reachable (succ value)) := by
  apply Derives.clause (head := reachable (succ (.var "x"))) (body := [reachable (.var "x")])
    (σ := fun _ => value) (instantiatedBody := .conj (reachable value) .truth)
  · simp [kb, reachableSucc]
  · exact .app (.cons (.app (.cons .var .nil)) .nil)
  · exact .conj (.app (.cons .var .nil)) .truth
  · exact .conjIntro proof .truth

example : Derives .hoApply kb [] (reachable (succ (succ zero))) :=
  reachesSucc _ (reachesSucc _ reachesZero)

example : model.holds (model.application .even [natValue 2]) := (even_at_nat 2).mpr (by decide)
example (value : Value) : model.holds (model.application .reachable [value]) ↔
    ∃ n, value = natValue n ∧ Reachable n := reachable_exact value
example (value : Value) : model.holds (model.application .even [value]) ↔
    ∃ n, value = natValue n ∧ Even n := even_exact value
example (environment : Environment String Value) :
    ¬ model.Satisfies environment (even (succ zero)) := even_one_false environment

-- All-domain quantification now operates over a nonempty KB with induction
-- and recursive predicate definitions, using the same generated Nat universe.
private def allReachable : Universal Domain String Unit Symbol := family.forallAll "x" (reachable (.var "x"))

example (environment : Environment String Value) :
    model.Satisfies environment (allReachable.toTerm membershipSymbol) := by
  apply (family.forallAll_satisfies_iff model realizes environment "x" (reachable (.var "x"))).mpr
  intro ⟨tree, domain, member⟩
  obtain ⟨n, same⟩ := member_denote member
  simp only [reachable, Model.Satisfies, Model.eval, List.map_cons, List.map_nil, update, ite_true, same]
  exact reachable_at_nat n

-- A real generated counterexample refutes the claim that every Nat is even.
private def allEven : Universal Domain String Unit Symbol := family.forallAll "x" (even (.var "x"))
private theorem allEvenRefuted : CertifiedRefutation.Refutes model kb [] (allEven.toTerm membershipSymbol) := by
  apply CertifiedRefutation.Refutes.guarded realizes
  intro environment assumptions
  apply InductiveDomains.Refutes.witness (domain := .nat) (tree := natTree 1)
    (by simp [allEven, FiniteFamily.forallAll, family]) (natTree_member 1)
  simp only [allEven, FiniteFamily.forallAll, even, Model.Satisfies, Model.eval,
    List.map_cons, List.map_nil, update, ite_true, natTree_denote]
  exact fun proof => (by decide : ¬ 1 % 2 = 0) ((even_at_nat 1).mp proof)

example : Derives .hoApply kb [] (.defaultNeg (allEven.toTerm membershipSymbol)) naf :=
  allEvenRefuted.toDerives (by
    simp [allEven, FiniteFamily.forallAll, Universal.toTerm, family, InductiveDomains.guard, membershipSymbol, even, Term.freeVars])

example : ¬ Derives .hoApply kb [] .falsity naf := consistent
example : ¬ Derives .hoApply inductionKb [] .falsity := model.positive_consistent inductionKb_models

-- Soundness rules out deriving the false predicate instance positively.
example : ¬ Derives .hoApply kb [] (even (succ zero)) := by
  intro proof
  exact even_one_false (fun _ => model.inhabitant)
    (model.positive_sound kb_models proof _ (by intro assumption member; cases member))
