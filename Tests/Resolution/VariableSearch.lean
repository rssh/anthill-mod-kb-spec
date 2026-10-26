import AnthillModKbSpec.Resolution.VariableSearch

open AnthillModKbSpec AnthillModKbSpec.VariableSearch

private abbrev T := Term String Nat String
private abbrev P := Program String Nat String "ho_apply"
private abbrev C := Context String Nat String "ho_apply"
private def p (value : T) : T := .app "p" [value]
private def q (value : T) : T := .app "q" [value]
private def r (value : T) : T := .app "r" [value]
private def emptyContext : C := ⟨[], by simp⟩

private theorem pVar : IsAtom "ho_apply" (p (.var "x")) := .app (by decide) (by
  intro arg member; simp at member; subst arg; exact .var)
private theorem qVar : IsAtom "ho_apply" (q (.var "x")) := .app (by decide) (by
  intro arg member; simp at member; subst arg; exact .var)
private theorem qOneTemplate : IsAtom "ho_apply" (q (.lit 1)) := .app (by decide) (by
  intro arg member; simp at member; subst arg; exact .lit)
private theorem groundP (n : Nat) : GroundSearch.IsAtom "ho_apply" (p (.lit n)) := .app (by decide) (by
  intro arg member; simp at member; subst arg; exact .lit)
private theorem groundQ (n : Nat) : GroundSearch.IsAtom "ho_apply" (q (.lit n)) := .app (by decide) (by
  intro arg member; simp at member; subst arg; exact .lit)
private theorem groundR (n : Nat) : GroundSearch.IsAtom "ho_apply" (r (.lit n)) := .app (by decide) (by
  intro arg member; simp at member; subst arg; exact .lit)

-- The source KB contains a variable rule, rather than pre-grounded copies.
private def rules : P :=
  ⟨[.definite (p (.var "x")) [q (.var "x")], .definite (q (.lit 1)) []], by
    intro clause member
    simp at member
    rcases member with rfl | rfl
    · exact .definite pVar (.conj (.atom qVar) .truth)
    · exact .definite qOneTemplate .truth⟩

private theorem qOne : Succeeds rules emptyContext (q (.lit 1)) := by
  apply Succeeds.clause (body := []) (groundQ 1)
  · exact .intro (head := q (.lit 1)) (body := []) (σ := Term.var) (by simp [rules, q])
      (.app (.cons .lit .nil)) .nil (by simp)
  · exact .truth

private theorem pOne : Succeeds rules emptyContext (p (.lit 1)) := by
  apply Succeeds.clause (body := [q (.lit 1)]) (groundP 1)
  · exact .intro (head := p (.var "x")) (body := [q (.var "x")])
      (σ := fun _ => .lit 1) (by simp [rules, p, q])
      (.app (.cons .var .nil)) (.cons (.app (.cons .var .nil)) .nil)
      (by intro goal member; simp at member; subst goal; exact .atom (groundQ 1))
  · exact .conj qOne .truth

example : Derives "ho_apply" rules.toKb emptyContext.assumptions (p (.lit 1))
    (failureEvidence rules emptyContext) := succeeds_toDerives pOne

-- A non-ground query has an explicit answer substitution.
private theorem pAnswer : Answers rules emptyContext (p (.var "x")) (fun _ => .lit 1) :=
  .intro (.atom pVar) (.app (.cons .var .nil)) (.atom (groundP 1)) pOne

example : ∃ grounded, Substitutes (fun _ => .lit 1) (p (.var "x")) grounded ∧
    Derives "ho_apply" rules.toKb emptyContext.assumptions grounded
      (failureEvidence rules emptyContext) := answers_toDerives pAnswer

-- Inversion helpers for checking exhaustion of this rule's ground instances.
private theorem variableValue {σ : Substitution String Nat String}
    (proof : Substitutes σ (.var name) value) : value = σ name := by
  cases proof
  rfl

private theorem sameFunctor {σ : Substitution String Nat String}
    (proof : Substitutes σ (.app source before) (.app target after)) : source = target := by
  cases proof
  rfl

private theorem headValue {σ : Substitution String Nat String}
    (proof : Substitutes σ (p (.var "x")) (p value)) : σ "x" = value := by
  cases proof with
  | app args =>
      cases args with
      | cons first rest => exact (variableValue first).symm

private theorem bodyShape {σ : Substitution String Nat String}
    (proof : SubstitutesList σ [q (.var "x")] body) : body = [q (σ "x")] := by
  cases proof with
  | cons first rest =>
      cases rest
      cases first with
      | app args =>
          cases args with
          | cons value rest =>
              cases rest
              cases value
              rfl

-- No rule defines r, so a generator can be exhausted without enumerating values.
private def noR (n : Nat) : ExhaustedInstances rules (r (.lit n)) :=
  ⟨[], by simp, by
    intro body inst
    cases inst with
    | intro member headInstance bodyInstance valid =>
        simp [rules] at member
        rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          have impossible := sameFunctor headInstance <;> simp at impossible⟩

-- q(2) has no matching clause, even though q(1) is a fact.
private def noQTwo : ExhaustedInstances rules (q (.lit 2)) :=
  ⟨[], by simp, by
    intro body inst
    cases inst with
    | intro member headInstance bodyInstance valid =>
        simp [rules] at member
        rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have impossible := sameFunctor headInstance
          simp at impossible
        · cases headInstance with
          | app args => cases args with | cons first rest => cases first⟩

private theorem qTwoFails : Fails rules emptyContext (q (.lit 2)) :=
  .atom (groundQ 2) (by simp [emptyContext]) noQTwo (by simp [noQTwo])

-- For p(2), head matching fixes x=2; [q(2)] is an exhaustive body generator.
private def pTwoBodies : ExhaustedInstances rules (p (.lit 2)) :=
  ⟨[[q (.lit 2)]], by
    intro body member
    simp at member
    subst body
    exact .intro (head := p (.var "x")) (body := [q (.var "x")])
      (σ := fun _ => .lit 2) (by simp [rules, p, q])
      (.app (.cons .var .nil)) (.cons (.app (.cons .var .nil)) .nil)
      (by intro goal h; simp at h; subst goal; exact .atom (groundQ 2)), by
    intro body inst
    cases inst with
    | intro member headInstance bodyInstance valid =>
        simp [rules] at member
        rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have value := headValue headInstance
          have shape := bodyShape bodyInstance
          simp [shape, value]
        · have impossible := sameFunctor headInstance
          simp at impossible⟩

private theorem pTwoFails : Fails rules emptyContext (p (.lit 2)) :=
  .atom (groundP 2) (by simp [emptyContext]) pTwoBodies (by
    intro body member
    simp [pTwoBodies] at member
    subst body
    exact .conjLeft qTwoFails .truth)

example : Succeeds rules emptyContext (.defaultNeg (p (.lit 2))) := .defaultNeg pTwoFails
example : ¬ Succeeds rules emptyContext (p (.lit 2)) := fails_not_succeeds pTwoFails
example : ¬ Fails rules emptyContext (p (.lit 1)) := succeeds_not_fails pOne

-- Grounding alone must never rescue unbound NAF.
example (σ : Substitution String Nat String) :
    ¬ Answers rules emptyContext (.defaultNeg (p (.var "x"))) σ := by
  intro answer
  cases answer with
  | intro safe grounding valid proof =>
      cases safe with
      | defaultNeg valid bound =>
          have bad := bound "x" (by simp [p, Term.freeVars])
          simp at bad

-- A variable shared by two occurrences cannot independently take two values.
example (σ : Substitution String Nat String) :
    ¬ Substitutes σ (.app "same" [.var "x", .var "x"] : T)
      (.app "same" [.lit 0, .lit 1]) := by
  intro inst
  cases inst with
  | app args =>
      cases args with
      | cons first rest =>
          cases rest with
          | cons second rest =>
              have impossible := (variableValue first).trans (variableValue second).symm
              cases impossible

-- The same clause variable name is instantiated independently on different uses.
private def allP : P := ⟨[.definite (p (.var "x")) []], by
  intro clause member; simp at member; subst clause; exact .definite pVar .truth⟩

private theorem anyP (n : Nat) : Succeeds allP emptyContext (p (.lit n)) := by
  apply Succeeds.clause (body := []) (groundP n)
  · exact .intro (head := p (.var "x")) (body := []) (σ := fun _ => .lit n)
      (by simp [allP, p]) (.app (.cons .var .nil)) .nil (by simp)
  · exact .truth

example : Succeeds allP emptyContext (.conj (p (.lit 0)) (p (.lit 1))) :=
  .conj (anyP 0) (anyP 1)

-- A positive goal supplies a value before that value is used under NAF.
example : Answers rules emptyContext
    (.conj (q (.var "x")) (.defaultNeg (r (.var "x")))) (fun _ => .lit 1) := by
  apply Answers.intro (grounded := .conj (q (.lit 1)) (.defaultNeg (r (.lit 1))))
  · exact .conj (.atom qVar) (.defaultNeg (.atom (.app (by decide) (by
      intro arg member; simp at member; subst arg; exact .var))) (by
      intro name member; simpa [r, q, Term.freeVars] using member))
  · exact .conj (.app (.cons .var .nil)) (.defaultNeg (.app (.cons .var .nil)))
  · exact .conj (.atom (groundQ 1)) (.defaultNeg (.atom (groundR 1)))
  · exact .conj qOne (.defaultNeg (.atom (groundR 1) (by simp [emptyContext])
      (noR 1) (by simp [noR])))

-- Body-local y is a real witness, not an independent name at each occurrence.
-- It must satisfy q(y) and is then available to the following not r(y).
private theorem qY : IsAtom "ho_apply" (q (.var "y")) := .app (by decide) (by
  intro arg member; simp at member; subst arg; exact .var)
private theorem rY : IsAtom "ho_apply" (r (.var "y")) := .app (by decide) (by
  intro arg member; simp at member; subst arg; exact .var)
private theorem pZeroTemplate : IsAtom "ho_apply" (p (.lit 0)) := .app (by decide) (by
  intro arg member; simp at member; subst arg; exact .lit)

private def localWitness : P :=
  ⟨[.definite (p (.lit 0)) [q (.var "y"), .defaultNeg (r (.var "y"))],
    .definite (q (.lit 1)) []], by
    intro clause member
    simp at member
    rcases member with rfl | rfl
    · exact .definite pZeroTemplate (.conj (.atom qY)
        (.conj (.defaultNeg (.atom rY) (by
          intro name member; simpa [r, q, p, Term.freeVars] using member)) .truth))
    · exact .definite qOneTemplate .truth⟩

private theorem witnessOne : Instance localWitness (p (.lit 0))
    [q (.lit 1), .defaultNeg (r (.lit 1))] :=
  .intro (head := p (.lit 0)) (body := [q (.var "y"), .defaultNeg (r (.var "y"))])
    (σ := fun _ => .lit 1) (by simp [localWitness, p, q, r]) (.app (.cons .lit .nil))
    (.cons (.app (.cons .var .nil)) (.cons (.defaultNeg (.app (.cons .var .nil))) .nil))
    (by
      intro goal member; simp at member; rcases member with rfl | rfl
      · exact .atom (groundQ 1)
      · exact .defaultNeg (.atom (groundR 1)))

private theorem localQOne : Succeeds localWitness emptyContext (q (.lit 1)) := by
  apply Succeeds.clause (body := []) (groundQ 1)
  · exact .intro (head := q (.lit 1)) (body := []) (σ := Term.var)
      (by simp [localWitness, q]) (.app (.cons .lit .nil)) .nil (by simp)
  · exact .truth

private def noLocalR : ExhaustedInstances localWitness (r (.lit 1)) :=
  ⟨[], by simp, by
    intro body inst
    cases inst with
    | intro member headInstance bodyInstance valid =>
        simp [localWitness] at member
        rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          have impossible := sameFunctor headInstance <;> simp at impossible⟩

private theorem witnessSucceeds : Succeeds localWitness emptyContext (p (.lit 0)) :=
  .clause (groundP 0) witnessOne (.conj localQOne
    (.conj (.defaultNeg (.atom (groundR 1) (by simp [emptyContext]) noLocalR
      (by simp [noLocalR]))) .truth))

example : Derives "ho_apply" localWitness.toKb emptyContext.assumptions (p (.lit 0))
    (failureEvidence localWitness emptyContext) := succeeds_toDerives witnessSucceeds

-- A generator that tries only y=0 is not exhausted: it omits the y=1 instance.
example : ¬ (∀ body, Instance localWitness (p (.lit 0)) body →
    body ∈ [[q (.lit 0), .defaultNeg (r (.lit 0))]]) := by
  intro complete
  have missing := complete _ witnessOne
  simp [q] at missing

-- The existence of an answer prevents an exhaustive query-failure certificate.
example : ¬ QueryFails rules emptyContext (p (.var "x")) :=
  fun refuted => queryFails_no_answer refuted pAnswer

-- Query generators must cover all answers, not just one sampled literal.
example : ¬ (∀ σ goal, Substitutes σ (p (.var "x")) goal →
    GroundSearch.IsGoal "ho_apply" goal → goal ∈ [p (.lit 0)]) := by
  intro complete
  have missing := complete (fun _ => .lit 1) (p (.lit 1))
    (.app (.cons .var .nil)) (.atom (groundP 1))
  simp [p] at missing

-- A missing predicate's candidate generator is empty even though its argument
-- has infinitely many possible values. Unmatched values need not be enumerated.
private def noQueryR : ExhaustedQueryInstances rules (r (.var "x")) :=
  ⟨[], by simp, by
    intro σ atom body grounding ground inst
    cases grounding with
    | app arguments =>
        cases inst with
        | intro member headInstance bodyInstance valid =>
            simp [rules] at member
            rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
              have impossible := sameFunctor headInstance <;> simp at impossible⟩

private theorem queryRFails : QueryFails rules emptyContext (r (.var "x")) :=
  .atom (.app (by decide) (by intro arg member; simp at member; subst arg; exact .var))
    (by intros; simp [emptyContext]) noQueryR (by simp [noQueryR])

example (σ : Substitution String Nat String) : ¬ Answers rules emptyContext (r (.var "x")) σ :=
  queryFails_no_answer queryRFails

-- Neither success nor failure is inferred for an unbound negative query.
example : ¬ QueryFails rules emptyContext (.defaultNeg (p (.var "x"))) := by
  intro refuted
  cases refuted with
  | intro safe generator allGoals =>
      cases safe with
      | defaultNeg valid bound =>
          have bad := bound "x" (by simp [p, Term.freeVars])
          simp at bad
  | atom valid absent generator allBodies => cases valid
