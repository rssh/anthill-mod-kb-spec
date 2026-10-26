import AnthillModKbSpec.Archive

open AnthillModKbSpec AnthillModKbSpec.Semantics AnthillModKbSpec.InductiveDomains
open AnthillModKbSpec.InductionModel
open AnthillModKbSpec.MillerCertificates AnthillModKbSpec.MillerResolution
open AnthillModKbSpec.Archive.UnaryMatcher

private def nafBase : HornClause String Unit Symbol := .definite (reachable zero) [.defaultNeg .falsity]
private def database : K := {inductionRule, natZero, natSucc, nafBase, reachableSucc}
private abbrev Proof (rigids : List String) (context : ProofContext String Unit Symbol) (goal : T) :=
  MillerResolution.Proves model database rigids context goal
private def predicate : T := .app .reachable []
private def head : T := applyP (.var "P") (.var "x")
private def body : List T := [isNat (.var "x"), applyP (.var "P") zero, step (.var "P")]
private def query : T := reachable (.var "a")

private def matched : UnaryMatch Symbol.hoApply ["a"] head query :=
  (matchUnary? .hoApply ["a"] head query).get (by decide)

private theorem matchedComputed : matchUnary? Symbol.hoApply ["a"] head query = some matched := rfl

private def instantiatedBody : T :=
  .conj (isNat (.var "a")) (.conj (applyP predicate zero) (.conj (step predicate) .truth))

private theorem instantiated : (Term.conjunction body).instantiate? matched.substitution = some instantiatedBody := by
  simp [Term.instantiate?, body, instantiatedBody, Term.conjunction, step, isNat, applyP,
    Term.hoApply, succ, zero, predicate, Term.freeVars, UnaryMatch.substitution,
    matched, matchUnary?, head, query, reachable, Substitution.bind, List.mapM_cons]

private def expansion : Expansion Symbol.hoApply ["a"] head body query := ⟨matched, instantiatedBody, instantiated⟩

private theorem computed : expandUnary? Symbol.hoApply ["a"] head body query = some expansion := by
  unfold expandUnary?
  rw [matchedComputed]
  dsimp only
  split
  · rename_i impossible
    have contradiction := impossible.symm.trans instantiated
    cases contradiction
  · rename_i result success
    have same : result = instantiatedBody := Option.some.inj (success.symm.trans instantiated)
    subst result
    rfl

-- Both predicate and argument substitution are computed from the ordinary goal.
example : expansion.matched.substitution "P" = predicate := rfl
example : expansion.matched.substitution "x" = .var "a" := rfl
example : expansion.matched.substitution "a" = .var "a" := expansion.matched.rigids_fixed (by simp)
example : head.MillerHead Symbol.hoApply ["x"] := expansion.matched.miller_pattern
example : IsMillerArguments ["a"] [(.var "a" : T)] := expansion.matched.miller_target

-- The *same* computed substitution opens the head and instantiates every body
-- occurrence, including P under the scoped induction step.
private theorem bodyComputed : expansion.instantiatedBody =
    .conj (isNat (.var "a")) (.conj (applyP predicate zero) (.conj (step predicate) .truth)) := rfl

-- The pattern restriction applies to the selected flexible head. In the body,
-- P(succ(n)) becomes concrete before it is searched, so it needs no flexible
-- higher-order match on a compound argument.
example : instantiatedBody.IsMiller Symbol.hoApply ["a"] := by
  simp [instantiatedBody, isNat, applyP, predicate, zero, step, succ,
    Term.hoApply, Term.IsMiller, Term.MillerHead]

private theorem baseCase (rigids : List String) (context : ProofContext String Unit Symbol) :
    Proof rigids context (applyP predicate zero) := by
  apply Proves.hoApplyIntro
  apply Proves.clauseComputed (head := reachable zero) (body := [.defaultNeg .falsity]) (substitution := Term.var)
    (instantiatedBody := .conj (.defaultNeg .falsity) .truth)
  · simp [database, nafBase]
  · simp [Term.instantiate?, reachable, zero, List.mapM_cons]
  · simp [Term.instantiate?, Term.conjunction]
  · exact .conj (.defaultNeg (by simp [Term.freeVars]) .falsity) .truth

private theorem stepCase (context : ProofContext String Unit Symbol) (fresh : FreshForContext "n" context) :
    Proof ["a"] context (step predicate) := by
  apply Proves.generalize (binder := "n") (fresh := fresh)
  apply Proves.impIntro
  apply Proves.impIntro
  apply Proves.hoApplyIntro
  apply Proves.clauseComputed (head := reachable (succ (.var "x"))) (body := [reachable (.var "x")])
    (substitution := Substitution.single "x" (.var "n"))
    (instantiatedBody := .conj (reachable (.var "n")) .truth)
  · simp [database, reachableSucc]
  · simp [Term.instantiate?, reachable, succ, Substitution.single, Substitution.bind, List.mapM_cons]
  · simp [Term.instantiate?, reachable, Term.conjunction, Substitution.single, Substitution.bind, List.mapM_cons]
  · exact .conj (.hoApplyElim (.assumption (by simp [applyP, predicate]))) .truth

-- Backward resolution of reachable(a) selects the ordinary induction clause.
-- There is no Goal wrapper, special InductiveProof constructor, or registry.
private theorem rigidGoal (context : ProofContext String Unit Symbol)
    (domain : Proof ["a"] context (isNat (.var "a"))) (fresh : FreshForContext "n" context) :
    Proof ["a"] context query := by
  apply Proves.certifiedClause (head := head) (body := body)
    (by simp [database, inductionRule, head, body]) expansion
  rw [bodyComputed]
  exact .conj domain (.conj (baseCase _ _) (.conj (stepCase _ fresh) .truth))

private theorem allReachable : Proof [] []
    (.forallVar "x" (.imp (isNat (.var "x")) (reachable (.var "x")))) := by
  apply Proves.forallIntro (eigen := "a")
    (opened := .imp (isNat (.var "a")) (reachable (.var "a")))
  · simp [FreshForContext]
  · simp [isNat, reachable, Term.freeVars]
  · exact .imp (.app (.cons (.singleVar "x" (.var "a")) .nil))
      (.app (.cons (.singleVar "x" (.var "a")) .nil))
  · exact .impIntro (rigidGoal _ (.assumption (by simp)) (by simp [FreshForContext, isNat, Term.freeVars]))

private theorem allData : Proof [] []
    ((family.forallAll "x" (reachable (.var "x"))).toTerm membershipSymbol) := by
  apply Proves.forallIntro (eigen := "a")
    (opened := .imp (.disj (isNat (.var "a")) .falsity) (reachable (.var "a")))
  · simp [FreshForContext]
  · simp [FiniteFamily.forallAll, InductiveDomains.guard, family,
      membershipSymbol, reachable, Term.freeVars]
  · simpa [FiniteFamily.forallAll, InductiveDomains.guard, family,
      membershipSymbol, isNat] using
      (Substitutes.imp
        (Substitutes.disj (Substitutes.app (.cons (.singleVar "x" (.var "a")) .nil)) Substitutes.falsity)
        (Substitutes.app (.cons (.singleVar "x" (.var "a")) .nil)) :
        Substitutes (Substitution.single "x" (.var "a"))
          (.imp (.disj (isNat (.var "x")) .falsity) (reachable (.var "x")))
          (.imp (.disj (isNat (.var "a")) .falsity) (reachable (.var "a"))))
  · apply Proves.impIntro
    apply rigidGoal
    · apply Proves.declarative
      exact .disjElim (a := isNat (.var "a")) (b := .falsity) (.assumption (by simp)) (.assumption (by simp))
        (.falsityElim (.assumption (by simp)))
    · simp [FreshForContext, isNat, Term.freeVars]

private theorem models : model.Models database := by
  intro clause member environment
  simp only [database, LogicalKb.mem_insert, LogicalKb.mem_singleton] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact inductionRule_valid environment
  · exact natZero_valid environment
  · exact natSucc_valid environment
  · simp only [nafBase, HornClause.toFormula, reachable, zero, Model.Satisfies,
      Model.eval, List.map_cons, List.map_nil, model.holds_implication]
    intro _
    exact (application_reachable _).mpr ⟨0, application_zero⟩
  · exact reachableSucc_valid environment

example : Derives .hoApply database []
    (.forallVar "x" (.imp (isNat (.var "x")) (reachable (.var "x"))))
    (CertifiedRefutation.failureEvidence model database) := allReachable.toDerives

private def interpretation : InductiveSoundness.Interpretation family database Value .hoApply :=
  ⟨model, membershipSymbol, realizes, models, complement⟩

example (environment : Environment String Value) : model.Satisfies environment
    (.forallVar "x" (.imp (isNat (.var "x")) (reachable (.var "x")))) :=
  InductiveSoundness.sound interpretation allReachable environment (by intro assumption member; cases member)

example (environment : Environment String Value) : model.Satisfies environment
    ((family.forallAll "x" (reachable (.var "x"))).toTerm membershipSymbol) :=
  InductiveSoundness.sound interpretation allData environment (by intro assumption member; cases member)

example : ¬ Proof [] [] .falsity := InductiveSoundness.consistent interpretation

-- Unsupported/unmatched calls are not converted into NAF certificates.
example : (matchUnary? Symbol.hoApply ["a"] head (reachable zero)).isNone := by decide
example : (matchUnary? Symbol.hoApply [] head query).isNone := by decide
example : (matchUnary? Symbol.hoApply ["P", "a"] head query).isNone := by decide
example : (matchUnary? Symbol.hoApply ["x", "a"] head query).isNone := by decide
example : (matchUnary? Symbol.hoApply ["a"] (applyP (.var "P") (.var "P")) query).isNone := by decide

-- Capture is refused, and a binder shadows the template substitution.
example : ((.forallVar "a" (.var "x") : T).instantiate?
    (Substitution.single "x" (.var "a"))).isNone := by
  simp [Term.instantiate?, Term.freeVars, Substitution.single, Substitution.bind]
example : ((.forallVar "x" (.var "x") : T).instantiate?
    (Substitution.single "x" zero)) = some (.forallVar "x" (.var "x")) := by
  simp [Term.instantiate?, Term.freeVars, Substitution.bind]
