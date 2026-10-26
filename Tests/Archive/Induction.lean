import AnthillModKbSpec

open AnthillModKbSpec

namespace InductionExample

abbrev T := Term String Nat String
abbrev K := LogicalKb String Nat String
abbrev C := ProofContext String Nat String

def zero : T := .app "zero" []
def succ (n : T) : T := .app "succ" [n]
def nat (n : T) : T := .app "Nat" [n]
def reachable (n : T) : T := .app "reachable" [n]
def predicate : T := .app "reachable" []
def applyP (p n : T) : T := .hoApply "ho_apply" p [n]
def certificate (p : T) : T := .app "Nat.induction" [p]
def step (p : T) : T :=
  .forallVar "n" (.imp (applyP p (.var "n")) (applyP p (succ (.var "n"))))

-- The induction principle is supplied by the object KB, not by Derives.
-- These two clauses expose its base/step obligations and its Nat domain guard.
def inductionRule : HornClause String Nat String :=
  .definite (certificate (.var "P")) [applyP (.var "P") zero, step (.var "P")]
def inductionUse : HornClause String Nat String :=
  .definite (applyP (.var "P") (.var "x"))
    [nat (.var "x"), certificate (.var "P")]

def baseRule : HornClause String Nat String := .definite (reachable zero) []
def stepRule : HornClause String Nat String :=
  .definite (reachable (succ (.var "x"))) [reachable (.var "x")]
def natZero : HornClause String Nat String := .definite (nat zero) []
def natSucc : HornClause String Nat String :=
  .definite (nat (succ (.var "x"))) [nat (.var "x")]
def kb : K := {inductionRule, inductionUse, baseRule, stepRule, natZero, natSucc}
abbrev Proves (context : C) (goal : T) := Derives "ho_apply" kb context goal

-- The concrete property's base case.
theorem baseCase (context : C) : Proves context (reachable zero) :=
  .clause (head := reachable zero) (body := []) (σ := Term.var)
    (by simp [kb, baseRule]) (Substitutes.identity _) .truth .truth

-- The successor case uses the local induction hypothesis, not recursion in Lean.
theorem successorCase (context : C) (value : T)
    (ih : Proves context (reachable value)) : Proves context (reachable (succ value)) := by
  apply Derives.clause (head := reachable (succ (.var "x")))
    (body := [reachable (.var "x")]) (σ := fun _ => value)
    (instantiatedBody := .conj (reachable value) .truth)
  · simp [kb, stepRule]
  · exact .app (.cons (.app (.cons .var .nil)) .nil)
  · exact .conj (.app (.cons .var .nil)) .truth
  · exact .conjIntro ih .truth

-- Concrete predicate application uses the existing ho_apply rules.
theorem stepCase (context : C) (fresh : FreshForContext "e" context) :
    Proves context (step predicate) := by
  apply Derives.forallIntro (eigen := "e")
    (opened := .imp (applyP predicate (.var "e")) (applyP predicate (succ (.var "e"))))
  · exact fresh
  · simp [applyP, predicate, succ, Term.hoApply, Term.freeVars]
  · exact .imp (.app (.cons (.app .nil) (.cons (.singleVar "n" (.var "e")) .nil)))
      (.app (.cons (.app .nil) (.cons (.app (.cons (.singleVar "n" (.var "e")) .nil)) .nil)))
  · exact .impIntro (.hoApplyIntro (successorCase _ _
      (.hoApplyElim (.assumption (by simp [applyP, predicate])))))

-- Substitute the same P in the certificate head, base, and scoped step.
private theorem instantiateStep : Substitutes (Substitution.single "P" predicate)
    (step (.var "P")) (step predicate) := by
  apply Substitutes.forallVar
  · intro name member different
    simp [applyP, succ, Term.hoApply, Term.freeVars] at member
    rcases member with rfl | rfl | rfl | rfl
    · simp [Substitution.single, Substitution.bind, predicate, Term.freeVars]
    · exact False.elim (different rfl)
    · simp [Substitution.single, Substitution.bind, predicate, Term.freeVars]
    · exact False.elim (different rfl)
  · have pSubst : Substitutes (Substitution.bind (Substitution.single "P" predicate) "n" (.var "n"))
        (.var "P") predicate := by
      simpa [Substitution.bind, Substitution.single] using
        (Substitutes.var (σ := Substitution.bind (Substitution.single "P" predicate) "n" (.var "n"))
          (name := "P"))
    have nSubst : Substitutes (Substitution.bind (Substitution.single "P" predicate) "n" (.var "n"))
        (.var "n") (.var "n") := by
      simpa [Substitution.bind] using
        (Substitutes.var (σ := Substitution.bind (Substitution.single "P" predicate) "n" (.var "n"))
          (name := "n"))
    exact .imp (.app (.cons pSubst (.cons nSubst .nil)))
      (.app (.cons pSubst (.cons (.app (.cons nSubst .nil)) .nil)))

-- The local context is preserved while discharging both obligations.
theorem inductionCertificate (context : C) (fresh : FreshForContext "e" context) :
    Proves context (certificate predicate) := by
  apply Derives.clause (head := certificate (.var "P"))
    (body := [applyP (.var "P") zero, step (.var "P")])
    (σ := Substitution.single "P" predicate)
    (instantiatedBody := .conj (applyP predicate zero) (.conj (step predicate) .truth))
  · simp [kb, inductionRule]
  · exact .app (.cons (.singleVar "P" predicate) .nil)
  · exact .conj (.app (.cons (.singleVar "P" predicate) (.cons (.app .nil) .nil)))
      (.conj instantiateStep .truth)
  · exact .conjIntro (.hoApplyIntro (baseCase context)) (.conjIntro (stepCase context fresh) .truth)

-- The universal result uses inductionUse; finite unfolding alone cannot prove it.
theorem allNaturalsReachable : Proves []
    (.forallVar "n" (.imp (nat (.var "n")) (reachable (.var "n")))) := by
  apply Derives.forallIntro (eigen := "z")
    (opened := .imp (nat (.var "z")) (reachable (.var "z")))
  · simp [FreshForContext]
  · simp [nat, reachable, Term.freeVars]
  · exact .imp (.app (.cons (.singleVar "n" (.var "z")) .nil))
      (.app (.cons (.singleVar "n" (.var "z")) .nil))
  · apply Derives.impIntro
    apply Derives.hoApplyElim
    let σ : Substitution String Nat String := fun name =>
      if name = "P" then predicate else .var "z"
    have pSubst : Substitutes σ (.var "P") predicate := by
      simpa [σ] using (Substitutes.var (σ := σ) (name := "P"))
    have xSubst : Substitutes σ (.var "x") (.var "z") := by
      simpa [σ] using (Substitutes.var (σ := σ) (name := "x"))
    apply Derives.clause (head := applyP (.var "P") (.var "x"))
      (body := [nat (.var "x"), certificate (.var "P")]) (σ := σ)
      (instantiatedBody := .conj (nat (.var "z")) (.conj (certificate predicate) .truth))
    · simp [kb, inductionUse]
    · exact .app (.cons pSubst (.cons xSubst .nil))
    · exact .conj (.app (.cons xSubst .nil)) (.conj (.app (.cons pSubst .nil)) .truth)
    · exact .conjIntro (.assumption (by simp))
        (.conjIntro (inductionCertificate _ (by simp [FreshForContext, nat, Term.freeVars])) .truth)

-- The guard can be discharged for concrete constructor naturals.
private theorem natBase : Proves [] (nat zero) :=
  .clause (head := nat zero) (body := []) (σ := Term.var)
    (by simp [kb, natZero]) (Substitutes.identity _) .truth .truth

private theorem natSuccessor (value : T) (proof : Proves [] (nat value)) :
    Proves [] (nat (succ value)) := by
  apply Derives.clause (head := nat (succ (.var "x"))) (body := [nat (.var "x")])
    (σ := fun _ => value) (instantiatedBody := .conj (nat value) .truth)
  · simp [kb, natSucc]
  · exact .app (.cons (.app (.cons .var .nil)) .nil)
  · exact .conj (.app (.cons .var .nil)) .truth
  · exact .conjIntro proof .truth

theorem reachableTwo : Proves [] (reachable (succ (succ zero))) := by
  apply Derives.impElim (premise := nat (succ (succ zero)))
  · exact .forallElim allNaturalsReachable
      (.imp (.app (.cons (.singleVar "n" (succ (succ zero))) .nil))
        (.app (.cons (.singleVar "n" (succ (succ zero))) .nil)))
  · exact natSuccessor _ (natSuccessor _ natBase)

-- First-order search checks the concrete obligations. Generic predicate
-- application remains in Derives, since ScopedSearch excludes ho_apply.
open ScopedSearch

private abbrev P := Program String Nat String "ho_apply"
private abbrev S := Context String Nat String "ho_apply"
private def emptyContext : S := ⟨[], [], by simp⟩
private def obligationProgram : P := ⟨[baseRule, stepRule], by
  intro clause member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .definite (.app (by decide) (by
      intro arg h; simp at h; subst arg; exact .app (by simp))) (.basic .truth)
  · apply IsClause.definite (.app (by decide) (by
      intro arg h; simp at h; subst arg
      exact .app (by intro arg h; simp at h; subst arg; exact .var)))
    apply SafeGoal.conj
    · exact .basic (.atom (.app (by decide) (by
        intro arg h; simp at h; subst arg; exact .var)))
    · exact .basic .truth⟩

private theorem reachableAtom (parameters : List String) (value : T) (valid : IsData parameters value) :
    IsAtom "ho_apply" parameters (reachable value) :=
  .app (by decide) (by intro arg member; simp at member; subst arg; exact valid)

private theorem searchBase : Succeeds obligationProgram emptyContext (reachable zero) := by
  apply Succeeds.clause (body := []) (reachableAtom _ _ (.app (by simp)))
  · exact .intro (head := reachable zero) (body := []) (σ := Term.var)
      (by simp [obligationProgram, baseRule]) (Substitutes.identity _) .nil (by simp)
  · exact .truth

private theorem searchSuccessor (context : S) (value : T) (valid : IsData context.parameters value)
    (ih : Succeeds obligationProgram context (reachable value)) :
    Succeeds obligationProgram context (reachable (succ value)) := by
  apply Succeeds.clause (body := [reachable value])
    (reachableAtom _ _ (.app (by intro arg h; simp at h; subst arg; exact valid)))
  · exact .intro (head := reachable (succ (.var "x"))) (body := [reachable (.var "x")])
      (σ := fun _ => value) (by simp [obligationProgram, stepRule])
      (.app (.cons (.app (.cons .var .nil)) .nil))
      (.cons (.app (.cons .var .nil)) .nil)
      (by intro goal h; simp at h; subst goal; exact .atom (reachableAtom _ _ valid))
  · exact .conj ih .truth

private theorem searchStep : Succeeds obligationProgram emptyContext
    (.forallVar "n" (.imp (reachable (.var "n")) (reachable (succ (.var "n"))))) := by
  apply Succeeds.forallVar
  · exact .forallVar (.imp (.atom (reachableAtom _ _ (.parameter (by simp))))
      (.atom (reachableAtom _ _ (.app (by
        intro arg h; simp at h; subst arg; exact .parameter (by simp))))))
  · simp only [Term.openFree, reachable, succ, List.map_cons, List.map_nil, ↓reduceIte]
    apply Succeeds.imp (.atom (reachableAtom _ _ (.parameter (by simp [Context.extend]))))
      (.atom (reachableAtom _ _ (.app (by
        intro arg h; simp at h; subst arg; exact .parameter (by simp [Context.extend])))))
    apply searchSuccessor _ _ (.parameter (by simp [Context.assume, Context.extend]))
    exact .assumption (reachableAtom _ _ (.parameter (by simp [Context.assume, Context.extend])))
      (by simp [Context.assume, reachable])

-- Both obligations have finite search certificates and declarative derivations.
example : Succeeds obligationProgram emptyContext
    (.conj (reachable zero)
      (.forallVar "n" (.imp (reachable (.var "n")) (reachable (succ (.var "n")))))) :=
  .conj searchBase searchStep

example : Derives "ho_apply" obligationProgram.toKb []
    (.forallVar "n" (.imp (reachable (.var "n")) (reachable (succ (.var "n")))))
    (failureEvidence obligationProgram) := succeeds_toDerives searchStep

-- A concrete model witnesses consistency of this example KB. It validates all
-- atoms, so this result does not claim the intended standard Nat interpretation.
private def consistencyModel := Semantics.Model.trueAtoms Nat String "ho_apply"
private theorem inductionKbModels : consistencyModel.Models kb := by
  intro clause member environment
  simp only [kb, LogicalKb.mem_insert, LogicalKb.mem_singleton] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact Semantics.Model.trueAtoms_definite environment _ _ _

theorem inductionKbConsistent : ¬ Derives "ho_apply" kb [] .falsity :=
  consistencyModel.positive_consistent inductionKbModels

example (environment : Semantics.Environment String Bool) :
    consistencyModel.Satisfies environment
      (.forallVar "n" (.imp (nat (.var "n")) (reachable (.var "n")))) :=
  consistencyModel.positive_sound inductionKbModels allNaturalsReachable environment
    (by intro assumption member; cases member)

end InductionExample
