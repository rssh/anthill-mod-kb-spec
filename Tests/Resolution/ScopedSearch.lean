import AnthillModKbSpec.Resolution.ScopedSearch

open AnthillModKbSpec AnthillModKbSpec.ScopedSearch

private abbrev T := Term String Nat String
private abbrev P := Program String Nat String "ho_apply"
private abbrev C := Context String Nat String "ho_apply"
private def p (value : T) : T := .app "p" [value]
private def emptyContext : C := ⟨[], [], by simp⟩
private def emptyProgram : P := ⟨[], by simp⟩
private theorem sourceP : VariableSearch.IsAtom "ho_apply" (p (.var "u")) :=
  .app (by decide) (by intro arg member; simp at member; subst arg; exact .var)

private def allP : P := ⟨[.definite (p (.var "u")) []], by
  intro clause member; simp at member; subst clause; exact .definite sourceP (.basic .truth)⟩

private theorem pParameter (parameters : List String) (name : String) (declared : name ∈ parameters) :
    IsAtom "ho_apply" parameters (p (.var name)) :=
  .app (by decide) (by intro arg member; simp at member; subst arg; exact .parameter declared)

private theorem anyP (context : C) (value : T) (valid : IsData context.parameters value) :
    Succeeds allP context (p value) := by
  apply Succeeds.clause (body := [])
  · exact .app (by decide) (by intro arg member; simp at member; subst arg; exact valid)
  · exact .intro (head := p (.var "u")) (body := []) (σ := fun _ => value)
      (by simp [allP, p]) (.app (.cons .var .nil)) .nil (by simp)
  · exact .truth

-- Universal introduction uses a fresh rigid parameter, not a sampled literal.
private theorem universalP (context : C) : Succeeds allP context (.forallVar "x" (p (.var "x"))) := by
  apply Succeeds.forallVar
  · exact .forallVar (.atom (pParameter _ "x" (by simp)))
  · simpa [Term.openFree, p] using
      anyP (context.extend (context.eigen "x" (p (.var "x"))))
        (.var (context.eigen "x" (p (.var "x")))) (.parameter (by simp [Context.extend]))

example : Derives "ho_apply" allP.toKb emptyContext.assumptions (.forallVar "x" (p (.var "x")))
    (failureEvidence allP) := succeeds_toDerives (universalP emptyContext)

-- Inner occurrences of the same binder shadow the outer binder.
example : (Term.forallVar "x" (p (.var "x")) : T).openFree "x" "e" =
    .forallVar "x" (p (.var "x")) := by simp [Term.openFree]

private theorem shadowedForall : Succeeds allP emptyContext
    (.forallVar "x" (.forallVar "x" (p (.var "x")))) := by
  apply Succeeds.forallVar
  · exact .forallVar (.forallVar (.atom (pParameter _ "x" (by simp))))
  · simpa [Term.openFree] using universalP
      (emptyContext.extend (emptyContext.eigen "x" (.forallVar "x" (p (.var "x")))))

example : ¬ Fails allP emptyContext (.forallVar "x" (.forallVar "x" (p (.var "x")))) :=
  succeeds_not_fails shadowedForall

-- Scope extension preserves assumptions and chooses a different fresh name.
example (context : C) (binder : String) (body : T) :
    (context.extend (context.eigen binder body)).assumptions = context.assumptions := rfl

example (context : C) (binder : String) (body : T) :
    context.eigen binder body ∉ context.parameters := context.eigen_new binder body

example (context : C) (binder : String) (body : T) :
    FreshForContext (context.eigen binder body) context.assumptions := context.eigen_freshContext binder body

example (context : C) (binder : String) (body : T) :
    (context.extend (context.eigen binder body)).eigen binder body ≠ context.eigen binder body := by
  intro equality
  have fresh := (context.extend (context.eigen binder body)).eigen_new binder body
  apply fresh
  change (context.extend (context.eigen binder body)).eigen binder body ∈
    context.eigen binder body :: context.parameters
  rw [equality]
  simp

-- A single concrete fact p(0) does not establish forall x. p(x).
private theorem sourcePZero : VariableSearch.IsAtom "ho_apply" (p (.lit 0)) :=
  .app (by decide) (by intro arg member; simp at member; subst arg; exact .lit)
private def concrete : P := ⟨[.definite (p (.lit 0)) []], by
  intro clause member; simp at member; subst clause; exact .definite sourcePZero (.basic .truth)⟩

private theorem concreteNotParameter (context : C) (empty : context.assumptions = []) (name : String) :
    ¬ Succeeds concrete context (p (.var name)) := by
  intro proof
  cases proof with
  | assumption valid member => simp [empty] at member
  | clause valid inst bodyProof =>
      cases inst with
      | intro member headInstance bodyInstance valid =>
          simp [concrete] at member
          rcases member with ⟨rfl, rfl⟩
          cases headInstance with
          | app args => cases args with | cons first rest => cases first
      | hypothesis member backchain valid => simp [empty] at member

private theorem noParameterFailure (program : P) (context : C) (name : String) :
    ¬ Fails program context (p (.var name)) := by
  intro refuted
  cases refuted with
  | atom valid closed contextClosed absent generator allBodies => simp [Term.freeVars] at closed

private theorem concreteNotUniversal : ¬ Succeeds concrete emptyContext (.forallVar "x" (p (.var "x"))) := by
  intro proof
  cases proof with
  | forallVar valid opened =>
      apply concreteNotParameter (emptyContext.extend (emptyContext.eigen "x" (p (.var "x"))))
        (by rfl) (emptyContext.eigen "x" (p (.var "x")))
      simpa [Term.openFree, p] using opened

-- Missing p(eigen) remains unknown, rather than becoming a negative witness.
private theorem concreteUniversalNotFailed : ¬ Fails concrete emptyContext (.forallVar "x" (p (.var "x"))) := by
  intro refuted
  cases refuted with
  | forallVar valid opened =>
      apply noParameterFailure concrete _ (emptyContext.eigen "x" (p (.var "x")))
      simpa [Term.openFree, p] using opened

example : ¬ Succeeds concrete emptyContext (.forallVar "x" (p (.var "x"))) ∧
    ¬ Fails concrete emptyContext (.forallVar "x" (p (.var "x"))) :=
  ⟨concreteNotUniversal, concreteUniversalNotFailed⟩

-- Both success and failure of NAF are blocked on opaque parameters.
example : ¬ Succeeds emptyProgram emptyContext (.forallVar "x" (.defaultNeg (p (.var "x")))) := by
  intro proof
  cases proof with
  | forallVar valid opened =>
      simp only [Term.openFree, p, List.map_cons, List.map_nil] at opened
      cases opened with
      | defaultNeg closed _ => simp [Term.freeVars] at closed

example : ¬ Fails allP emptyContext (.forallVar "x" (.defaultNeg (p (.var "x")))) := by
  intro refuted
  cases refuted with
  | forallVar valid opened =>
      simp only [Term.openFree, p, List.map_cons, List.map_nil] at opened
      cases opened with
      | defaultNeg closed _ => simp [Term.freeVars] at closed

-- Genuine structural failure can propagate through forall.
private theorem forallFalse : Fails emptyProgram emptyContext (.forallVar "x" .falsity) :=
  .forallVar (.forallVar .falsity) (by simpa [Term.openFree] using
    (Fails.falsity (program := emptyProgram)
      (context := emptyContext.extend (emptyContext.eigen "x" (.falsity : T)))))

example : ¬ Succeeds emptyProgram emptyContext (.forallVar "x" .falsity) := fails_not_succeeds forallFalse

example : Succeeds emptyProgram emptyContext (.defaultNeg (.forallVar "x" .falsity)) :=
  .defaultNeg (by simp [Term.freeVars]) forallFalse

-- A parameter cannot escape and become a free flexible query outside its scope.
example (name : String) : ¬ Succeeds allP emptyContext (p (.var name)) := by
  intro proof
  cases proof with
  | assumption valid member => simp [emptyContext] at member
  | clause valid inst bodyProof =>
      cases valid with
      | app ordinary args =>
          have invalid := args (.var name) (by simp)
          cases invalid with
          | parameter declared => simp [emptyContext] at declared

-- The deterministic opening is still the capture-avoiding relational operation.
example (context : C) (body : T) :
    Substitutes (Substitution.single "x" (.var (context.eigen "x" body))) body
      (body.openFree "x" (context.eigen "x" body)) := context.opening "x" body

-- Closed NAF remains usable inside a universal scope and in its Derives bridge.
private theorem forallNotFalse : Succeeds emptyProgram emptyContext
    (.forallVar "x" (.defaultNeg .falsity)) := by
  apply Succeeds.forallVar
  · exact .forallVar (.defaultNeg .falsity)
  · simpa [Term.openFree] using
      (Succeeds.defaultNeg (program := emptyProgram)
        (context := emptyContext.extend (emptyContext.eigen "x" (.defaultNeg .falsity : T)))
        (goal := .falsity) (by simp [Term.freeVars]) Fails.falsity)

example : Derives "ho_apply" emptyProgram.toKb emptyContext.assumptions
    (.forallVar "x" (.defaultNeg .falsity)) (failureEvidence emptyProgram) :=
  succeeds_toDerives forallNotFalse

-- Forall can actually occur in a source clause body, not just at query roots.
private def allGoal : T := .app "all" []
private theorem sourcePX : VariableSearch.IsAtom "ho_apply" (p (.var "x")) :=
  .app (by decide) (by intro arg member; simp at member; subst arg; exact .var)
private def quantifiedBody : P :=
  ⟨[.definite allGoal [.forallVar "x" (p (.var "x"))], .definite (p (.var "u")) []], by
    intro clause member
    simp at member
    rcases member with rfl | rfl
    · exact .definite (.app (by decide) (by simp))
        (.conj (.forallVar (.basic (.atom sourcePX))) (.basic .truth))
    · exact .definite sourceP (.basic .truth)⟩

private theorem quantifiedBodyAnyP (context : C) (value : T) (valid : IsData context.parameters value) :
    Succeeds quantifiedBody context (p value) := by
  apply Succeeds.clause (body := [])
  · exact .app (by decide) (by intro arg member; simp at member; subst arg; exact valid)
  · exact .intro (head := p (.var "u")) (body := []) (σ := fun _ => value)
      (by simp [quantifiedBody, p]) (.app (.cons .var .nil)) .nil (by simp)
  · exact .truth

private theorem quantifiedBodyForall : Succeeds quantifiedBody emptyContext (.forallVar "x" (p (.var "x"))) := by
  apply Succeeds.forallVar
  · exact .forallVar (.atom (pParameter _ "x" (by simp)))
  · simpa [p, Term.openFree] using
      quantifiedBodyAnyP (emptyContext.extend (emptyContext.eigen "x" (p (.var "x"))))
        (.var (emptyContext.eigen "x" (p (.var "x")))) (.parameter (by simp [Context.extend]))

private theorem quantifiedBodySucceeds : Succeeds quantifiedBody emptyContext allGoal := by
  apply Succeeds.clause (body := [.forallVar "x" (p (.var "x"))])
  · exact .app (by decide) (by simp)
  · exact .intro (head := allGoal) (body := [.forallVar "x" (p (.var "x"))])
      (σ := Term.var) (by simp [quantifiedBody, allGoal]) (.app .nil)
      (.cons (Substitutes.identity _) .nil) (by
        intro goal member; simp at member; subst goal
        exact .forallVar (.atom (pParameter _ "x" (by simp))))
  · exact .conj quantifiedBodyForall .truth

example : Derives "ho_apply" quantifiedBody.toKb emptyContext.assumptions allGoal
    (failureEvidence quantifiedBody) := succeeds_toDerives quantifiedBodySucceeds

-- Scoped query answers still respect the original binder.
example : Answers allP emptyContext (.forallVar "x" (p (.var "x"))) Term.var :=
  .intro (.forallVar (.basic (.atom sourcePX))) (by simp [emptyContext])
    (Substitutes.identity _) (.forallVar (.atom (pParameter _ "x" (by simp)))) (universalP emptyContext)

-- A query substitution cannot rewrite an already-active parameter.
example (name : String) (context : C) (declared : name ∈ context.parameters) :
    ¬ Answers allP context (p (.var name)) (fun _ => .lit 0) := by
  intro answer
  cases answer with
  | intro safe preserves inst valid proof =>
      have impossible := preserves name declared
      cases impossible

-- An outer parameter remains the same parameter under a differently named binder.
example : Succeeds allP emptyContext (.forallVar "x" (.forallVar "y" (p (.var "x")))) := by
  apply Succeeds.forallVar
  · exact .forallVar (.forallVar (.atom (pParameter _ "x" (by simp))))
  · let e := emptyContext.eigen "x" (.forallVar "y" (p (.var "x")))
    have different : e ≠ "y" := by
      intro equality
      apply emptyContext.eigen_not_mem "x" (.forallVar "y" (p (.var "x")))
      change e ∈ _
      rw [equality]
      simp [Context.avoid, Term.binderNames]
    have inner : Succeeds allP (emptyContext.extend e) (.forallVar "y" (p (.var e))) := by
      apply Succeeds.forallVar
      · exact .forallVar (.atom (pParameter _ e (by simp [Context.extend])))
      · simpa [p, Term.openFree, different] using
          anyP ((emptyContext.extend e).extend ((emptyContext.extend e).eigen "y" (p (.var e))))
            (.var e) (.parameter (by simp [Context.extend]))
    simpa [p, Term.openFree, e] using inner

-- Both name supplies satisfy freshness without assumptions or custom axioms.
example (avoid : List Nat) : FreshNames.fresh avoid ∉ avoid := FreshNames.fresh_not_mem avoid
example (avoid : List String) : FreshNames.fresh avoid ∉ avoid := FreshNames.fresh_not_mem avoid
