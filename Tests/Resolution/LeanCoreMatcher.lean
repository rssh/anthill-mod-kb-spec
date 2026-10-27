import AnthillModKbSpec
import Lean

open AnthillModKbSpec AnthillModKbSpec.Semantics AnthillModKbSpec.InductiveDomains
open AnthillModKbSpec.InductionModel
open AnthillModKbSpec.MillerCertificates AnthillModKbSpec.MillerResolution
open AnthillModKbSpec.CoreMatcherCertificate

namespace LeanCoreAdapterExample

private def nafBase : HornClause String Unit Symbol := .definite (reachable zero) [.defaultNeg .falsity]
private def database : K := {inductionRule, natZero, natSucc, nafBase, reachableSucc}
private abbrev Proof (rigids : List String) (context : ProofContext String Unit Symbol) (goal : T) :=
  MillerResolution.Proves model database rigids context goal
private def predicate : T := .app .reachable []
private def head : T := applyP (.var "P") (.var "x")
private def body : List T := [isNat (.var "x"), applyP (.var "P") zero, step (.var "P")]
private def query : T := reachable (.var "a")

private def symbolExpr : Symbol → Lean.Expr
  | .zero => Lean.mkConst ``Symbol.zero
  | .succ => Lean.mkConst ``Symbol.succ
  | .isNat => Lean.mkConst ``Symbol.isNat
  | .reachable => Lean.mkConst ``Symbol.reachable
  | .even => Lean.mkConst ``Symbol.even
  | .hoApply => Lean.mkConst ``Symbol.hoApply
  | .isPred arity => Lean.mkApp (Lean.mkConst ``Symbol.isPred) (Lean.mkNatLit arity)

-- Run the actual native solver and publish only its raw proposal as a data
-- definition. All logical facts about it below are reconstructed and checked
-- in the kernel. No native success bit is turned into a theorem.
open Lean Meta in
run_meta do
  let .ok proposal ← LeanCoreMatcher.proposeUnary? Symbol.hoApply head query
    | throwError "native solver did not produce a unary candidate"
  let type := mkApp2 (mkConst ``UnaryCandidate) (mkConst ``String) (mkConst ``Symbol)
  let value := mkAppN (mkConst ``UnaryCandidate.mk)
    #[mkConst ``String, mkConst ``Symbol, symbolExpr proposal.predicate, toExpr proposal.argument]
  addAndCompile (.defnDecl {
    name := `LeanCoreAdapterExample.nativeCandidate
    levelParams := []
    type := type
    value := value
    hints := .abbrev
    safety := .safe })
  enableRealizationsForConst `LeanCoreAdapterExample.nativeCandidate

example : nativeCandidate.predicate = Symbol.reachable := rfl
example : nativeCandidate.argument = "a" := rfl

private def matched : UnaryMatch Symbol.hoApply ["a"] head query :=
  (CoreMatcherCertificate.checkUnary? .hoApply ["a"] head query nativeCandidate).get (by decide)

private theorem matchedComputed :
    CoreMatcherCertificate.checkUnary? Symbol.hoApply ["a"] head query nativeCandidate = some matched := rfl

private def instantiatedBody : T :=
  .conj (isNat (.var "a")) (.conj (applyP predicate zero) (.conj (step predicate) .truth))

private theorem instantiated : (Term.conjunction body).instantiate? matched.substitution = some instantiatedBody := by
  simp [Term.instantiate?, body, instantiatedBody, Term.conjunction, step, isNat, applyP,
    Term.hoApply, succ, zero, predicate, Term.freeVars, UnaryMatch.substitution,
    matched, CoreMatcherCertificate.checkUnary?, nativeCandidate, head, query, reachable, Substitution.bind, List.mapM_cons]

private def expansion : Expansion Symbol.hoApply ["a"] head body query := ⟨matched, instantiatedBody, instantiated⟩

private theorem computed : CoreMatcherCertificate.expandUnary? Symbol.hoApply ["a"] head body query nativeCandidate = some expansion := by
  unfold CoreMatcherCertificate.expandUnary?
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
example : (CoreMatcherCertificate.checkUnary? Symbol.hoApply ["a"] head (reachable zero) nativeCandidate).isNone := by decide
example : (CoreMatcherCertificate.checkUnary? Symbol.hoApply [] head query nativeCandidate).isNone := by decide
example : (CoreMatcherCertificate.checkUnary? Symbol.hoApply ["P", "a"] head query nativeCandidate).isNone := by decide
example : (CoreMatcherCertificate.checkUnary? Symbol.hoApply ["x", "a"] head query nativeCandidate).isNone := by decide
example : (CoreMatcherCertificate.checkUnary? Symbol.hoApply ["a"] (applyP (.var "P") (.var "P")) query nativeCandidate).isNone := by decide

-- Capture is refused, and a binder shadows the template substitution.
example : ((.forallVar "a" (.var "x") : T).instantiate?
    (Substitution.single "x" (.var "a"))).isNone := by
  simp [Term.instantiate?, Term.freeVars, Substitution.single, Substitution.bind]
example : ((.forallVar "x" (.var "x") : T).instantiate?
    (Substitution.single "x" zero)) = some (.forallVar "x" (.var "x")) := by
  simp [Term.instantiate?, Term.freeVars, Substitution.bind]

-- Forged proposal data is independently rejected by the pure checker.
example : (CoreMatcherCertificate.checkUnary? Symbol.hoApply ["a"] head query
    (⟨.even, "a"⟩ : UnaryCandidate String Symbol)).isNone := by decide
example : (CoreMatcherCertificate.checkUnary? Symbol.hoApply ["a"] head query
    (⟨.reachable, "b"⟩ : UnaryCandidate String Symbol)).isNone := by decide

open Lean Meta in
run_meta do
  match ← LeanCoreMatcher.expandUnary? Symbol.hoApply ["a"] head body query with
  | .ok _ => pure ()
  | .error reason => throwError "native expansion failed: {reason}"
  match ← LeanCoreMatcher.expandUnary? Symbol.hoApply [] head body query with
  | .error _ => pure ()
  | .ok _ => throwError "certificate checker accepted an undeclared rigid"
  match ← LeanCoreMatcher.proposeUnary? Symbol.hoApply head (reachable zero) with
  | .error _ => pure ()
  | .ok _ => throwError "adapter accepted an unsupported constructor target"

-- The reusable native solver also solves a nontrivial binary permutation.
-- Its lambda-valued result is deliberately not reflected into our unary AST.
open Lean Meta Sym in
run_meta do
  withLocalDeclD `Carrier (mkSort (.succ .zero)) fun carrier => do
    let functionType ← mkArrow carrier (← mkArrow carrier carrier)
    withLocalDeclD `f functionType fun f => do
      let some answer ← LeanCoreMatcher.solveAbstracted? carrier 2
          (fun args => pure (mkAppN f #[args[1]!, args[0]!]))
        | throwError "native Miller solver did not solve argument permutation"
      let expected := mkLambda `x .default carrier (mkLambda `y .default carrier
        (mkAppN f #[mkBVar 0, mkBVar 1]))
      unless ← isDefEq answer expected do throwError "unexpected permutation answer"
      if etaReduce answer == f then throwError "permutation was incorrectly decoded as a symbol"

-- Solving a candidate must neither assign the caller's metavariables nor
-- return an answer containing unresolved metavariables.
open Lean Meta in
run_meta do
  withLocalDeclD `Carrier (mkSort (.succ .zero)) fun carrier => do
    let functionType ← mkArrow carrier carrier
    let foreign ← mkFreshExprMVar (some functionType)
    let result ← LeanCoreMatcher.solveAbstracted? carrier 1
      (fun args => pure (mkApp foreign args[0]!))
    if ← foreign.mvarId!.isAssigned then throwError "native solver assigned an outer metavariable"
    if result.isSome then throwError "native solver returned an unresolved answer"

-- The emitted proposal is data, not an axiom about the unifier. Audit the
-- actual end-to-end object proof, including its reconstructed certificate.
open Lean Meta in
run_meta do
  for axiomName in ← collectAxioms ``allReachable do
    unless axiomName ∈ [`propext, `Classical.choice, `Quot.sound] do
      throwError "unexpected axiom in native-backed induction proof: {axiomName}"

end LeanCoreAdapterExample
