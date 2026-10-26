import AnthillModKbSpec.Foundation.Derivation

open AnthillModKbSpec

private abbrev T := Term String Nat String
private abbrev K := LogicalKb String Nat String
private abbrev C := ProofContext String Nat String
private abbrev Proves (kb : K) (context : C) (goal : T) :=
  Derives "ho_apply" kb context goal

private def p (x : T) : T := .app "p" [x]
private def q (x : T) : T := .app "q" [x]
private def fact : HornClause String Nat String := .definite (p (.var "x")) []
private def rule : HornClause String Nat String := .definite (q (.var "x")) [p (.var "x")]
private def kb : K := {fact, rule}

-- Each use chooses its own instance; the same template name causes no sharing.
private theorem factAt (value : T) (context : C) : Proves kb context (p value) := by
  apply Derives.clause (head := p (.var "x")) (body := []) (σ := fun _ => value)
    (instantiatedBody := .truth)
  · simp [kb, fact]
  · exact .app (.cons .var .nil)
  · exact .truth
  · exact .truth

example : Proves kb [] (.conj (p (.lit 1)) (p (.lit 2))) :=
  .conjIntro (factAt (.lit 1) []) (factAt (.lit 2) [])

-- Ordinary rule application proves the body with the same head/body instance.
example : Proves kb [] (q (.lit 7)) := by
  apply Derives.clause (head := q (.var "x")) (body := [p (.var "x")])
    (σ := fun _ => .lit 7) (instantiatedBody := .conj (p (.lit 7)) .truth)
  · simp [kb, rule]
  · exact .app (.cons .var .nil)
  · exact .conj (.app (.cons .var .nil)) .truth
  · exact .conjIntro (factAt (.lit 7) []) .truth

-- Universal introduction uses a fresh, fixed eigenvariable.
example : Proves kb [] (.forallVar "x" (p (.var "x"))) := by
  apply Derives.forallIntro (eigen := "e") (opened := p (.var "e"))
  · simp [FreshForContext]
  · simp [Term.freeVars, p]
  · exact .app (.cons (.singleVar "x" (.var "e")) .nil)
  · exact factAt (.var "e") []

-- Universal elimination instantiates only the binder's body.
example : Proves (∅ : K) [.forallVar "x" (p (.var "x"))] (p (.lit 3)) := by
  apply Derives.forallElim (binder := "x") (body := p (.var "x")) (witness := .lit 3)
  · exact .assumption (by simp)
  · exact .app (.cons (.singleVar "x" (.lit 3)) .nil)

-- Nested implications introduce assumptions only in their conclusion subproof.
example : Proves (∅ : K) [] (.imp (p (.lit 0)) (.imp (q (.lit 0)) (p (.lit 0)))) :=
  .impIntro (.impIntro (.assumption (by simp)))

example : Proves (∅ : K) []
    (.imp (.conj (p (.lit 0)) (.imp (p (.lit 0)) (q (.lit 0)))) (q (.lit 0))) := by
  apply Derives.impIntro
  have pair : Proves (∅ : K)
      [.conj (p (.lit 0)) (.imp (p (.lit 0)) (q (.lit 0)))]
      (.conj (p (.lit 0)) (.imp (p (.lit 0)) (q (.lit 0)))) :=
    .assumption (by simp)
  exact .impElim (.conjRight pair) (.conjLeft pair)

-- ho_apply is a proof rule, usable both as a goal and from a hypothesis.
example : Proves kb [] (.hoApply "ho_apply" (.app "p" []) [.lit 1]) :=
  .hoApplyIntro (factAt (.lit 1) [])

example : Proves (∅ : K) [.hoApply "ho_apply" (.app "p" []) [.lit 1]] (p (.lit 1)) :=
  .hoApplyElim (.assumption (by simp))

-- A predicate parameter remains a parameter; it can be used as an assumption
-- without pretending to resolve it to a concrete symbol.
example : Proves (∅ : K) []
    (.imp (.hoApply "ho_apply" (.var "P") [.var "x"])
      (.hoApply "ho_apply" (.var "P") [.var "x"])) :=
  .impIntro (.assumption (by simp))

-- Existential and disjunction introduction use the same positive calculus.
example : Proves kb [] (.existsVar "x" (p (.var "x"))) := by
  apply Derives.existsIntro (witness := .lit 4) (instantiated := p (.lit 4))
  · exact .app (.cons (.singleVar "x" (.lit 4)) .nil)
  · exact factAt (.lit 4) []

example : Proves kb [] (.disj (p (.lit 1)) (q (.lit 2))) :=
  .disjLeft (factAt (.lit 1) [])

-- An inconsistent input is allowed: an empty goal clause derives falsity.
example : Proves ({HornClause.goal []} : K) [] .falsity :=
  .goalClause (body := []) (σ := Term.var) (by simp) Substitutes.truth Derives.truth

-- Capture avoidance: substituting x := y under forall y must rename its binder.
example : Substitutes (Substitution.single "x" (.var "y"))
    (.forallVar "y" (.app "r" [.var "x", .var "y"]) : T)
    (.forallVar "z" (.app "r" [.var "y", .var "z"])) := by
  apply Substitutes.forallVar
  · intro name member different
    simp [Term.freeVars] at member
    rcases member with rfl | rfl
    · simp [Substitution.single, Substitution.bind, Term.freeVars]
    · exact False.elim (different rfl)
  · apply Substitutes.app
    apply SubstitutesList.cons
    · simpa [Substitution.single, Substitution.bind] using
        (Substitutes.var (σ := Substitution.bind
          (Substitution.single "x" (.var "y")) "y" (.var "z")) (name := "x") :
          Substitutes _ (.var "x") _)
    · exact .cons (by simpa [Substitution.bind] using
        (Substitutes.var (σ := Substitution.bind
          (Substitution.single "x" (.var "y")) "y" (.var "z")) (name := "y") :
          Substitutes _ (.var "y") _)) .nil

-- The capture-producing result is not an allowed substitution.
example : ¬ Substitutes (Substitution.single "x" (.var "y"))
    (.forallVar "y" (p (.var "x")) : T) (.forallVar "y" (p (.var "y"))) := by
  intro substitution
  cases substitution with
  | forallVar fresh _ =>
      have bad := fresh "x" (by simp [p, Term.freeVars]) (by decide)
      simp [Substitution.single, Substitution.bind, Term.freeVars] at bad

-- Freshness prohibits generalizing a name already fixed by an assumption.
example : ¬ FreshForContext "e" ([p (.var "e")] : C) := by
  simp [FreshForContext, p, Term.freeVars]

-- Scope and shadowing are respected even inside application arguments.
example : (Term.app "store" [.forallVar "x" (.app "r" [.var "x", .var "y"])] : T).freeVars =
    ["y"] := by simp [Term.freeVars]

-- Universal goals can introduce local assumptions involving their eigenvariable.
example : Proves (∅ : K) [] (.forallVar "x" (.imp (p (.var "x")) (p (.var "x")))) := by
  apply Derives.forallIntro (eigen := "e")
    (opened := .imp (p (.var "e")) (p (.var "e")))
  · simp [FreshForContext]
  · simp [Term.freeVars, p]
  · exact .imp (.app (.cons (.singleVar "x" (.var "e")) .nil))
      (.app (.cons (.singleVar "x" (.var "e")) .nil))
  · exact .impIntro (.assumption (by simp))

-- A binder shadows a clause substitution; only the other variable is replaced.
example : Substitutes (fun _ => .lit 0)
    (.forallVar "x" (.app "r" [.var "x", .var "y"]) : T)
    (.forallVar "x" (.app "r" [.var "x", .lit 0])) := by
  apply Substitutes.forallVar
  · simp [Term.freeVars]
  · apply Substitutes.app
    exact .cons (by simpa [Substitution.bind] using
      (Substitutes.var (σ := Substitution.bind (fun _ => .lit 0) "x" (.var "x"))
        (name := "x") : Substitutes _ (.var "x") _))
      (.cons (by simpa [Substitution.bind] using
        (Substitutes.var (σ := Substitution.bind (fun _ => .lit 0) "x" (.var "x"))
          (name := "y") : Substitutes _ (.var "y") _)) .nil)

-- Substitution enters default negation without changing its connective.
example : Substitutes (Substitution.single "x" (.lit 3))
    (.defaultNeg (p (.var "x")) : T) (.defaultNeg (p (.lit 3))) :=
  .defaultNeg (.app (.cons (.singleVar "x" (.lit 3)) .nil))

-- Binding and freshness include occurrences inside default negation.
example : (Term.defaultNeg (.forallVar "x" (.app "r" [.var "x", .var "y"])) : T).freeVars =
    ["y"] := by simp [Term.freeVars]

example : ¬ FreshForContext "e" ([.defaultNeg (p (.var "e"))] : C) := by
  simp [FreshForContext, p, Term.freeVars]

-- A negative hypothesis can be reused; this introduces no inference from failure.
example : Proves (∅ : K) [.defaultNeg (p (.lit 0))] (.defaultNeg (p (.lit 0))) :=
  .assumption (by simp)

-- Capture avoidance also applies when the captured occurrence is under `not`.
example : ¬ Substitutes (Substitution.single "x" (.var "y"))
    (.forallVar "y" (.defaultNeg (p (.var "x"))) : T)
    (.forallVar "y" (.defaultNeg (p (.var "y")))) := by
  intro substitution
  cases substitution with
  | forallVar fresh _ =>
      have bad := fresh "x" (by simp [p, Term.freeVars]) (by decide)
      simp [Substitution.single, Substitution.bind, Term.freeVars] at bad

-- A deliberately narrow failure-evidence fixture, not a search implementation:
-- an ordinary ground atom with no defining clauses or local assumptions.
private def emptySearchFailure : NafFailure String Nat String :=
  fun applicationSymbol database context goal =>
    applicationSymbol = "ho_apply" ∧ database = (∅ : K) ∧ context = [] ∧ goal = p (.lit 0)

-- Explicit complete-failure evidence introduces default negation.
example : Derives "ho_apply" (∅ : K) [] (.defaultNeg (p (.lit 0))) emptySearchFailure := by
  apply Derives.defaultNegIntro
  · simp [p, Term.freeVars]
  · exact ⟨rfl, rfl, rfl, rfl⟩

-- NAF can discharge a rule body, with the same evidence relation throughout.
private def nafClause : HornClause String Nat String :=
  .definite (q (.lit 0)) [.defaultNeg (p (.lit 0))]

private def ruleSearchFailure : NafFailure String Nat String :=
  fun applicationSymbol database context goal =>
    applicationSymbol = "ho_apply" ∧ database = ({nafClause} : K) ∧
      context = [] ∧ goal = p (.lit 0)

example : Derives "ho_apply" ({nafClause} : K) [] (q (.lit 0)) ruleSearchFailure := by
  apply Derives.clause (head := q (.lit 0)) (body := [.defaultNeg (p (.lit 0))])
    (σ := Term.var) (instantiatedBody := .conj (.defaultNeg (p (.lit 0))) .truth)
  · simp [nafClause]
  · exact .app (.cons .lit .nil)
  · exact .conj (.defaultNeg (.app (.cons .lit .nil))) .truth
  · apply Derives.conjIntro
    · exact .defaultNegIntro (by simp [p, Term.freeVars]) ⟨rfl, rfl, rfl, rfl⟩
    · exact .truth

-- Evidence is tied to the exact KB, local context, and goal. A failure result
-- from the empty context cannot be reused after assuming the failed atom.
example : ¬ emptySearchFailure "ho_apply" (∅ : K) [p (.lit 0)] (p (.lit 0)) := by
  simp [emptySearchFailure]

example : ¬ emptySearchFailure "ho_apply" ({fact} : K) [] (p (.lit 0)) := by
  intro evidence
  have member : fact ∈ ({fact} : K) := by simp
  rw [evidence.2.1] at member
  simp at member

example : ¬ emptySearchFailure "ho_apply" (∅ : K) [] (q (.lit 0)) := by
  simp [emptySearchFailure, p, q]

-- A free parameter blocks NAF even if someone supplies an overly broad oracle.
example : ¬ (p (.var "e") : T).freeVars = [] := by simp [p, Term.freeVars]

-- An unresolved predicate parameter also blocks NAF.
example : ¬ (Term.hoApply "ho_apply" (.var "P") [.lit 0] : T).freeVars = [] := by
  simp [Term.freeVars, Term.hoApply]

-- No evidence is supplied by the default (positive-only) configuration.
example (applicationSymbol : String) (database : K) (context : C) (goal : T) :
    ¬ NafFailure.disabled applicationSymbol database context goal := by
  simp [NafFailure.disabled]
