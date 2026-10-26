import AnthillModKbSpec.Resolution.ScopedSearch

open AnthillModKbSpec AnthillModKbSpec.ScopedSearch

private abbrev T := Term String Nat String
private abbrev P := Program String Nat String "ho_apply"
private abbrev C := Context String Nat String "ho_apply"
private def p : T := .app "p" []
private def q : T := .app "q" []
private def r : T := .app "r" []
private def emptyContext : C := ⟨[], [], by simp⟩
private def emptyProgram : P := ⟨[], by simp⟩
private theorem pAtom (parameters : List String) : IsAtom "ho_apply" parameters p := .app (by decide) (by simp)
private theorem qAtom (parameters : List String) : IsAtom "ho_apply" parameters q := .app (by decide) (by simp)
private theorem rAtom (parameters : List String) : IsAtom "ho_apply" parameters r := .app (by decide) (by simp)
private theorem pLocal (parameters : List String) : IsLocal "ho_apply" parameters p := .atom (pAtom parameters)
private theorem qLocal (parameters : List String) : IsLocal "ho_apply" parameters q := .atom (qAtom parameters)

private theorem useLocal (program : P) (context : C)
    {assumption head body : T} (member : assumption ∈ context.assumptions)
    (valid : IsAtom "ho_apply" context.parameters head)
    (backchain : LocalInstance (hoApplySymbol := "ho_apply") context.parameters assumption head body)
    (bodyValid : IsGoal "ho_apply" context.parameters body)
    (proof : Succeeds program context body) : Succeeds program context head := by
  cases valid with
  | app ordinary args =>
      exact .clause (.app ordinary args) (.hypothesis member backchain bodyValid) (.conj proof .truth)

private theorem identityImplication : Succeeds emptyProgram emptyContext (.imp p p) := by
  apply Succeeds.imp (pLocal []) (.atom (pAtom []))
  exact .assumption (pAtom _) (by simp [Context.assume, p])

example : Derives "ho_apply" emptyProgram.toKb [] (.imp p p) (failureEvidence emptyProgram) :=
  succeeds_toDerives identityImplication

-- Inner scopes can use outer assumptions without leaking into sibling goals.
example : Succeeds emptyProgram emptyContext (.imp p (.imp q p)) := by
  apply Succeeds.imp (pLocal []) (.imp (qLocal []) (.atom (pAtom [])))
  apply Succeeds.imp (qLocal []) (.atom (pAtom []))
  exact .assumption (pAtom _) (by simp [Context.assume, p, q])

-- A conjunctive antecedent is decomposed as local facts/rules.
private theorem conjunctionRule : Succeeds emptyProgram emptyContext
    (.imp (.conj p (.imp p q)) q) := by
  apply Succeeds.imp (.conj (pLocal []) (.imp (.atom (pAtom [])) (qLocal []))) (.atom (qAtom []))
  let context := emptyContext.assume (.conj p (.imp p q))
    (.conj (pLocal []) (.imp (.atom (pAtom [])) (qLocal [])))
  have proveP : Succeeds emptyProgram context p :=
    useLocal emptyProgram context (assumption := .conj p (.imp p q))
      (by simp [context, Context.assume]) (pAtom _)
      (.conjLeft (.fact (pAtom _))) .truth .truth
  apply useLocal emptyProgram context (assumption := .conj p (.imp p q))
    (by simp [context, Context.assume]) (qAtom _)
    (.conjRight (.imp (.fact (qAtom _)))) (.conj (.atom (pAtom _)) .truth)
  exact .conj proveP .truth

example : Derives "ho_apply" emptyProgram.toKb [] (.imp (.conj p (.imp p q)) q)
    (failureEvidence emptyProgram) := succeeds_toDerives conjunctionRule

-- An explicitly universal local fact can be instantiated at a concrete value.
private def px (value : T) : T := .app "px" [value]
private theorem pxAtom (parameters : List String) (value : T) (valid : IsData parameters value) :
    IsAtom "ho_apply" parameters (px value) :=
  .app (by decide) (by intro arg member; simp at member; subst arg; exact valid)

private theorem universalAssumption : Succeeds emptyProgram emptyContext
    (.imp (.forallVar "x" (px (.var "x"))) (px (.lit 0))) := by
  apply Succeeds.imp (.forallVar (.atom (pxAtom _ _ (.parameter (by simp)))))
    (.atom (pxAtom _ _ .lit))
  apply useLocal emptyProgram _ (assumption := .forallVar "x" (px (.var "x")))
    (by simp [Context.assume]) (pxAtom _ _ .lit)
    (.forallVar (.lit (value := 0)) (.app (.cons (.singleVar "x" (.lit 0)) .nil))
      (.fact (pxAtom _ _ .lit))) .truth .truth

example : Derives "ho_apply" emptyProgram.toKb []
    (.imp (.forallVar "x" (px (.var "x"))) (px (.lit 0))) (failureEvidence emptyProgram) :=
  succeeds_toDerives universalAssumption

-- A missing atom has no global or local clause alternatives at the root.
private def noP : ExhaustedInstances emptyProgram emptyContext p :=
  ⟨[], by simp, by
    intro body inst
    cases inst with
    | intro member _ _ _ => simp [emptyProgram] at member
    | hypothesis member _ _ => simp [emptyContext] at member⟩

private theorem pFails : Fails emptyProgram emptyContext p :=
  .atom (pAtom []) (by simp [Term.freeVars]) (by simp [Context.Closed, emptyContext])
    (by simp [emptyContext]) noP (by simp [noP])

private theorem notP : Succeeds emptyProgram emptyContext (.defaultNeg p) :=
  .defaultNeg (by simp [p, Term.freeVars]) pFails

-- Negation sees the hypothetical fact: p -> not p fails in its extended context.
private theorem assumptionRefutesNaf : Fails emptyProgram emptyContext (.imp p (.defaultNeg p)) := by
  apply Fails.imp (pLocal []) (.defaultNeg (.atom (pAtom [])))
  exact .defaultNeg (by simp [p, Term.freeVars])
    (.assumption (pAtom _) (by simp [Context.assume, p]))

example : ¬ Succeeds emptyProgram emptyContext (.imp p (.defaultNeg p)) := fails_not_succeeds assumptionRefutesNaf

-- The negative root result is invalid under a context that assumes p.
example : ¬ failureEvidence emptyProgram "ho_apply" emptyProgram.toKb [p] p := by
  intro evidence
  rcases evidence with ⟨_, _, context, same, refuted⟩
  cases refuted with
  | atom _ _ _ absent _ _ =>
      apply absent
      rw [same]
      simp [p]

-- A local instance cannot be omitted from a claimed exhausted generator.
example : ¬ (∀ body, Instance emptyProgram (emptyContext.assume p (pLocal [])) p body → body ∈ []) := by
  intro complete
  have missing := complete [Term.truth]
    (.hypothesis (by simp [Context.assume]) (.fact (pAtom _)) .truth)
  simp at missing

-- After proving p -> p, the next conjunct still sees the original empty context.
example : Succeeds emptyProgram emptyContext (.conj (.imp p p) (.defaultNeg p)) :=
  .conj identityImplication notP

example : ¬ Succeeds emptyProgram emptyContext (.conj (.imp p p) p) :=
  fails_not_succeeds (.conjRight (.imp (pLocal []) (.atom (pAtom []))) pFails)

-- A quantified goal can introduce a rigid parameter before a hypothetical fact.
private theorem quantifiedIdentity : Succeeds emptyProgram emptyContext
    (.forallVar "x" (.imp (px (.var "x")) (px (.var "x")))) := by
  apply Succeeds.forallVar
  · exact .forallVar (.imp (.atom (pxAtom _ _ (.parameter (by simp))))
      (.atom (pxAtom _ _ (.parameter (by simp)))))
  · simp only [Term.openFree, px, List.map_cons, List.map_nil, ↓reduceIte]
    apply Succeeds.imp (.atom (pxAtom _ _ (.parameter (by simp [Context.extend]))))
      (.atom (pxAtom _ _ (.parameter (by simp [Context.extend]))))
    exact .assumption (pxAtom _ _ (.parameter (by simp [Context.assume, Context.extend])))
      (by simp [Context.assume, px])

example : Derives "ho_apply" emptyProgram.toKb []
    (.forallVar "x" (.imp (px (.var "x")) (px (.var "x")))) (failureEvidence emptyProgram) :=
  succeeds_toDerives quantifiedIdentity

-- Extending a universal scope preserves an earlier universal local clause.
private theorem localUniversalIdentity : Succeeds emptyProgram emptyContext
    (.imp (.forallVar "x" (px (.var "x"))) (.forallVar "x" (px (.var "x")))) := by
  apply Succeeds.imp (.forallVar (.atom (pxAtom _ _ (.parameter (by simp)))))
    (.forallVar (.atom (pxAtom _ _ (.parameter (by simp)))))
  apply Succeeds.forallVar
  · exact .forallVar (.atom (pxAtom _ _ (.parameter (by simp))))
  · simp only [Term.openFree, px, List.map_cons, List.map_nil, ↓reduceIte]
    apply useLocal emptyProgram _ (assumption := .forallVar "x" (px (.var "x")))
      (by simp [Context.extend, Context.assume, emptyContext, px])
      (pxAtom _ _ (.parameter (by simp [Context.extend])))
    · exact .forallVar (.parameter (by simp [Context.extend]))
        (.app (.cons (.singleVar "x" _) .nil))
        (.fact (pxAtom _ _ (.parameter (by simp [Context.extend]))))
    · exact .truth
    · exact .truth

example : Derives "ho_apply" emptyProgram.toKb []
    (.imp (.forallVar "x" (px (.var "x"))) (.forallVar "x" (px (.var "x"))))
    (failureEvidence emptyProgram) := succeeds_toDerives localUniversalIdentity

-- An opaque hypothesis must not become evidence that a concrete atom is absent.
private def opaqueContext : C := ⟨["e"], [px (.var "e")], by
  intro clause member; simp at member; subst clause
  exact .atom (pxAtom _ _ (.parameter (by simp)))⟩

example : Succeeds emptyProgram opaqueContext (px (.var "e")) :=
  .assumption (pxAtom _ _ (.parameter (by simp [opaqueContext]))) (by simp [opaqueContext, px])

private theorem opaqueNoConcreteFailure : ¬ Fails emptyProgram opaqueContext (px (.lit 0)) := by
  intro refuted
  cases refuted with
  | atom _ _ closed _ _ _ =>
      have impossible := closed (px (.var "e")) (by simp [opaqueContext])
      simp [px, Term.freeVars] at impossible

example : ¬ Succeeds emptyProgram opaqueContext (.defaultNeg (px (.lit 0))) := by
  intro proof
  cases proof with
  | defaultNeg _ refuted => exact opaqueNoConcreteFailure refuted

private theorem atomicLocal {parameters : List String} {symbol : String} {args : List T}
    {head body : T}
    (instanceProof : LocalInstance (hoApplySymbol := "ho_apply") parameters (.app symbol args) head body) :
    head = .app symbol args ∧ body = .truth := by
  cases instanceProof with | fact _ => exact ⟨rfl, rfl⟩

-- Exhaustion includes a local rule even when its body fails.
private def deadRuleContext : C := emptyContext.assume (.imp .falsity q) (.imp .falsity (qLocal []))

private def deadRuleInstances : ExhaustedInstances emptyProgram deadRuleContext q :=
  ⟨[[.conj .falsity .truth]], by
    intro body member; simp only [List.mem_singleton] at member; subst body
    exact .hypothesis (assumption := .imp .falsity q) (by simp [deadRuleContext, Context.assume])
      (.imp (.fact (qAtom _))) (.conj .falsity .truth), by
    intro body inst
    cases inst with
    | intro member _ _ _ => simp [emptyProgram] at member
    | hypothesis member backchain valid =>
        simp only [deadRuleContext, Context.assume, emptyContext, List.mem_cons,
          List.not_mem_nil, or_false] at member
        subst_vars
        cases backchain with
        | imp child =>
            have shape := atomicLocal child
            rcases shape with ⟨_, rfl⟩
            simp⟩

private theorem deadRuleFailure : Fails emptyProgram emptyContext (.imp (.imp .falsity q) q) := by
  apply Fails.imp (.imp .falsity (qLocal [])) (.atom (qAtom []))
  exact .atom (qAtom _) (by simp [Term.freeVars])
    (by simp [Context.Closed, Context.assume, emptyContext, q, Term.freeVars])
    (by simp [Context.assume, emptyContext, q]) deadRuleInstances
    (by
      intro body member
      simp only [deadRuleInstances, List.mem_singleton] at member
      subst body
      exact .conjLeft (.conjLeft .falsity .truth) .truth)

example : ¬ Succeeds emptyProgram emptyContext (.imp (.imp .falsity q) q) :=
  fails_not_succeeds deadRuleFailure

-- Hypothetical goals also work inside global clause bodies.
private def hypotheticalProgram : P := ⟨[.definite r [.imp p p]], by
  intro clause member; simp at member; subst clause
  apply IsClause.definite (.app (by decide) (by simp))
  apply SafeGoal.conj
  · exact .imp (pLocal p.freeVars) (by simp [p, Term.freeVars])
      (.basic (.atom (.app (by decide) (by simp))))
  · exact .basic .truth⟩

private theorem hypotheticalBody : Succeeds hypotheticalProgram emptyContext r := by
  apply Succeeds.clause (body := [.imp p p]) (rAtom [])
  · exact .intro (σ := Term.var) (head := r) (body := [.imp p p])
      (by simp [hypotheticalProgram]) (Substitutes.identity r)
      (.cons (Substitutes.identity (.imp p p)) .nil)
      (by intro goal member; simp at member; subst goal; exact .imp (pLocal []) (.atom (pAtom [])))
  · apply Succeeds.conj
    · apply Succeeds.imp (pLocal []) (.atom (pAtom []))
      exact .assumption (pAtom _) (by simp [Context.assume, p])
    · exact .truth

example : Derives "ho_apply" hypotheticalProgram.toKb [] r (failureEvidence hypotheticalProgram) :=
  succeeds_toDerives hypotheticalBody
