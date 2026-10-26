import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Semantics

private abbrev T := Term String Nat String
private abbrev K := LogicalKb String Nat String
private def model := Model.trueAtoms Nat String "ho_apply"
private theorem emptyModels : model.Models (∅ : K) := by
  intro clause member; cases member

-- Concrete model existence turns relative consistency into an actual result.
example : ¬ Derives "ho_apply" (∅ : K) [] .falsity := model.positive_consistent emptyModels

-- A bound variable can itself be a formula in the shared-carrier semantics.
private theorem quantifiedIdentity : Derives "ho_apply" (∅ : K) []
    (.forallVar "x" (.imp (.var "x") (.var "x"))) := by
  apply Derives.forallIntro (eigen := "e") (opened := .imp (.var "e") (.var "e"))
  · simp [FreshForContext]
  · simp [Term.freeVars]
  · exact .imp (.singleVar "x" (.var "e")) (.singleVar "x" (.var "e"))
  · exact .impIntro (.assumption (by simp))

example (environment : Environment String Bool) :
    model.Satisfies environment (.forallVar "x" (.imp (.var "x") (.var "x"))) :=
  model.positive_sound emptyModels quantifiedIdentity environment (by intro assumption member; cases member)

-- The witness model distinguishes truth from falsity; not every goal is true.
example : ¬ Derives "ho_apply" (∅ : K) [] (.forallVar "x" (.var "x")) := by
  intro proof
  have impossible := model.positive_sound emptyModels proof (fun _ => false)
    (by intro assumption member; cases member)
  simp [Model.Satisfies, Model.eval, model, Model.trueAtoms, update] at impossible

-- Alpha-renaming preserves meaning under a nontrivial shared-carrier valuation.
example (environment : Environment String Bool) :
    model.eval environment (.forallVar "z" (.imp (.var "y") (.var "z"))) =
      model.eval (fun name => model.eval environment (Substitution.single "x" (.var "y") name))
        (.forallVar "y" (.imp (.var "x") (.var "y"))) := by
  apply model.eval_substitutes
  apply Substitutes.forallVar
  · intro name member different
    simp [Term.freeVars] at member
    rcases member with rfl | rfl
    · simp [Substitution.single, Substitution.bind, Term.freeVars]
    · exact False.elim (different rfl)
  · exact .imp (by simpa [Substitution.bind, Substitution.single] using
        (Substitutes.var (σ := Substitution.bind (Substitution.single "x" (.var "y")) "y" (.var "z"))
          (name := "x")))
      (by simpa [Substitution.bind] using
        (Substitutes.var (σ := Substitution.bind (Substitution.single "x" (.var "y")) "y" (.var "z"))
          (name := "y")))

-- A small, semantically justified failure provider: falsity always fails.
private def falseFailure : NafFailure String Nat String := fun _ _ _ goal => goal = .falsity
private theorem falseFailureAdequate : model.FailureAdequate (∅ : K) falseFailure := by
  intro context goal closed evidence environment valid
  change goal = .falsity at evidence
  subst goal
  simp [Model.Satisfies, Model.eval, model, Model.trueAtoms]

example : ¬ Derives "ho_apply" (∅ : K) [] .falsity falseFailure :=
  model.consistent emptyModels falseFailureAdequate

example (environment : Environment String Bool) : model.Satisfies environment (.defaultNeg (.falsity : T)) :=
  model.sound emptyModels falseFailureAdequate
    (.defaultNegIntro (context := []) (goal := .falsity) (by simp [Term.freeVars]) rfl) environment
    (by intro assumption member; cases member)

example : ¬ Derives "ho_apply" (∅ : K) [] (.defaultNeg .truth) falseFailure :=
  model.not_both emptyModels falseFailureAdequate (fun _ => false)
    (by intro assumption member; cases member) .truth

-- A real finite-failure certificate is not valid in every Horn-clause model.
-- The empty KB allows a model where p holds, despite empty-program search failing p.
private def emptyProgram : GroundSearch.Program String Nat String "ho_apply" := ⟨[], by simp⟩
private def emptyContext : GroundSearch.Context String Nat String "ho_apply" := ⟨[], by simp⟩
private def p : T := .app "p" []
private theorem missingP : GroundSearch.Fails emptyProgram emptyContext p :=
  .atom (.app (by decide) (by simp)) (by simp [emptyContext])
    (by intro body member; simp [emptyProgram] at member)

example : model.Models emptyProgram.toKb := by
  intro clause member
  change clause ∈ emptyProgram.clauses at member
  simp [emptyProgram] at member

example : ¬ model.FailureAdequate emptyProgram.toKb (GroundSearch.failureEvidence emptyProgram emptyContext) := by
  intro adequate
  have impossible := adequate [] p (by simp [p, Term.freeVars]) ⟨rfl, rfl, rfl, missingP⟩
    (fun _ => false) (by intro assumption member; cases member)
  simp [Model.Satisfies, Model.eval, model, Model.trueAtoms, p] at impossible

-- Contradictory KBs have no model; consistency cannot be asserted for them.
example (m : Model Nat String Bool "ho_apply") : ¬ m.Models ({HornClause.goal []} : K) := by
  intro validKb
  apply m.positive_consistent validKb
  exact .goalClause (body := []) (σ := Term.var) (by simp) .truth .truth
