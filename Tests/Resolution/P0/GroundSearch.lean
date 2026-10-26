import AnthillModKbSpec.Resolution.P0.GroundSearch

open AnthillModKbSpec AnthillModKbSpec.GroundSearch

private abbrev T := Term String Nat String
private abbrev P := Program String Nat String "ho_apply"
private abbrev C := Context String Nat String "ho_apply"
private def p : T := .app "p" []
private def q : T := .app "q" []
private def r : T := .app "r" []

private theorem pAtom : IsAtom "ho_apply" p := .app (by decide) (by simp)
private theorem qAtom : IsAtom "ho_apply" q := .app (by decide) (by simp)
private theorem rAtom : IsAtom "ho_apply" r := .app (by decide) (by simp)
private def emptyContext : C := ⟨[], by simp⟩
private def emptyProgram : P := ⟨[], by simp⟩

private theorem missingP : Fails emptyProgram emptyContext p :=
  .atom pAtom (by simp [emptyContext]) (by intro body member; simp [emptyProgram] at member)

example : Succeeds emptyProgram emptyContext (.defaultNeg p) := .defaultNeg missingP
example : Fails emptyProgram emptyContext (.defaultNeg (.defaultNeg p)) :=
  .defaultNeg (.defaultNeg missingP)

-- Actual failure certificates now supply NAF evidence to the logical calculus.
example : Derives "ho_apply" emptyProgram.toKb emptyContext.assumptions (.defaultNeg p)
    (failureEvidence emptyProgram emptyContext) :=
  succeeds_toDerives (.defaultNeg missingP)

-- Local facts block failure even when the global program has no clauses.
private def localContext : C := ⟨[p], by
  intro atom member
  simp at member
  subst atom
  exact pAtom⟩

private theorem localP : Succeeds emptyProgram localContext p :=
  .assumption pAtom (by simp [localContext, p])

example : ¬ Fails emptyProgram localContext p := succeeds_not_fails localP
example : Fails emptyProgram localContext (.defaultNeg p) := .defaultNeg localP
example : ¬ Succeeds emptyProgram localContext (.defaultNeg p) :=
  fails_not_succeeds (.defaultNeg localP)

-- Both definitions of p must be accounted for in a failure certificate.
private def alternatives : P :=
  ⟨[.definite p [q], .definite p [r]], by
    intro clause member
    simp at member
    rcases member with rfl | rfl
    · exact .definite pAtom (by intro goal h; simp at h; subst goal; exact .atom qAtom)
    · exact .definite pAtom (by intro goal h; simp at h; subst goal; exact .atom rAtom)⟩

private theorem missingQ : Fails alternatives emptyContext q :=
  .atom qAtom (by simp [emptyContext]) (by
    intro body member
    simp [alternatives, p, q] at member)

private theorem missingR : Fails alternatives emptyContext r :=
  .atom rAtom (by simp [emptyContext]) (by
    intro body member
    simp [alternatives, p, r] at member)

private theorem alternativesFail : Fails alternatives emptyContext p := by
  apply Fails.atom pAtom (by simp [emptyContext])
  intro body member
  simp [alternatives, p] at member
  rcases member with rfl | rfl
  · exact .conjLeft missingQ .truth
  · exact .conjLeft missingR .truth

example : ¬ Succeeds alternatives emptyContext p := fails_not_succeeds alternativesFail

-- One successful alternative prevents a failure certificate for the atom.
private def withFact : P :=
  ⟨[.definite p [q], .definite p []], by
    intro clause member
    simp at member
    rcases member with rfl | rfl
    · exact .definite pAtom (by intro goal h; simp at h; subst goal; exact .atom qAtom)
    · exact .definite pAtom (by simp)⟩

private theorem factSucceeds : Succeeds withFact emptyContext p :=
  .clause (body := []) pAtom (by simp [withFact, p]) .truth

example : ¬ Fails withFact emptyContext p := succeeds_not_fails factSucceeds
example : Fails withFact emptyContext (.defaultNeg p) := .defaultNeg factSucceeds

-- Rule application can use a negative body goal without an external oracle.
private def negativeBody : P :=
  ⟨[.definite p [.defaultNeg q]], by
    intro clause member
    simp at member
    subst clause
    exact .definite pAtom (by
      intro goal h; simp at h; subst goal; exact .defaultNeg (.atom qAtom))⟩

private theorem negativeBodySucceeds : Succeeds negativeBody emptyContext p := by
  apply Succeeds.clause pAtom (body := [.defaultNeg q]) (by simp [negativeBody, p])
  apply Succeeds.conj
  · apply Succeeds.defaultNeg
    apply Fails.atom qAtom (by simp [emptyContext])
    intro body member
    simp [negativeBody, p, q] at member
  · exact .truth

example : Derives "ho_apply" negativeBody.toKb emptyContext.assumptions p
    (failureEvidence negativeBody emptyContext) := succeeds_toDerives negativeBodySucceeds

-- Reusing a failure result in a different local context is not permitted.
example : ¬ failureEvidence emptyProgram emptyContext "ho_apply"
    emptyProgram.toKb localContext.assumptions p := by
  simp [failureEvidence, localContext, emptyContext]

-- The fragment excludes variables and reserves higher-order application.
example : ¬ IsAtom "ho_apply" (.app "ho_apply" [] : T) := by
  intro valid
  cases valid with
  | app ordinary _ => exact ordinary rfl

example : ¬ IsAtom "ho_apply" (.app "p" [.var "x"] : T) := by
  intro valid
  cases valid with
  | app _ args =>
      have invalid := args (.var "x") (by simp)
      cases invalid

example : IsData (.app "pair" [.lit 1, .lit 2] : T) := .app (by
  intro arg member
  simp at member
  rcases member with rfl | rfl <;> exact .lit)

-- A negative self-cycle has neither a finite success nor a finite failure.
private def negativeLoop : P :=
  ⟨[.definite p [.defaultNeg p]], by
    intro clause member
    simp at member
    subst clause
    exact .definite pAtom (by
      intro goal h; simp at h; subst goal; exact .defaultNeg (.atom pAtom))⟩

private theorem negativeLoopNoSuccess : ¬ Succeeds negativeLoop emptyContext p := by
  intro proof
  have original := proof
  cases proof with
  | assumption _ member => simp [emptyContext] at member
  | clause ground member bodyProof =>
      simp [negativeLoop, p] at member
      subst member
      cases bodyProof with
      | conj negative _ =>
          cases negative with
          | defaultNeg refuted => exact succeeds_not_fails original refuted

private theorem negativeLoopNoFailure : ¬ Fails negativeLoop emptyContext p := by
  intro refuted
  cases refuted with
  | atom _ _ allClauses =>
      have bodyFailure := allClauses [.defaultNeg p] (by simp [negativeLoop, p])
      cases bodyFailure with
      | conjLeft failed _ =>
          cases failed with
          | defaultNeg proof => exact negativeLoopNoSuccess proof
      | conjRight _ failed => cases failed

example : ¬ Succeeds negativeLoop emptyContext p ∧ ¬ Fails negativeLoop emptyContext p :=
  ⟨negativeLoopNoSuccess, negativeLoopNoFailure⟩

-- A positive self-cycle also has neither certificate. In particular, this
-- finite-failure calculus is deliberately not well-founded loop completion.
private def positiveLoop : P :=
  ⟨[.definite p [p]], by
    intro clause member
    simp at member
    subst clause
    exact .definite pAtom (by intro goal h; simp at h; subst goal; exact .atom pAtom)⟩

private theorem positiveLoopSuccessInvariant (proof : Succeeds positiveLoop emptyContext goal) :
    goal ≠ p ∧ goal ≠ .conj p .truth := by
  refine Succeeds.rec
    (motive_1 := fun goal _ => goal ≠ p ∧ goal ≠ .conj p .truth)
    (motive_2 := fun _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ proof
  · intro symbol args ground member; simp [emptyContext] at member
  · intro symbol args body ground member bodyProof ih
    simp [positiveLoop, p] at member
    rcases member with ⟨headEq, rfl⟩
    exact False.elim (ih.2 rfl)
  · simp [p]
  · intro a b left right ihLeft ihRight
    constructor
    · simp [p]
    · intro equality
      cases equality
      exact ihLeft.1 rfl
  · intro goal refuted ih; simp [p]
  · intros; trivial
  · trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

private theorem positiveLoopFailureInvariant (refuted : Fails positiveLoop emptyContext goal) :
    goal ≠ p ∧ goal ≠ .conj p .truth := by
  refine Fails.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun goal _ => goal ≠ p ∧ goal ≠ .conj p .truth)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ refuted
  · intros; trivial
  · intros; trivial
  · trivial
  · intros; trivial
  · intros; trivial
  · intro symbol args ground absent allClauses ih
    constructor
    · intro equality
      have member : HornClause.definite (.app symbol args) [p] ∈ positiveLoop.clauses := by
        simp [positiveLoop, equality]
      exact (ih [p] member).2 rfl
    · simp
  · simp [p]
  · intro a b failed ground ih
    constructor
    · simp [p]
    · intro equality
      cases equality
      exact ih.1 rfl
  · intro a b ground failed ih
    constructor
    · simp [p]
    · intro equality
      cases equality
      cases failed
  · intro goal proof ih; simp [p]

example : ¬ Succeeds positiveLoop emptyContext p ∧ ¬ Fails positiveLoop emptyContext p :=
  ⟨fun proof => (positiveLoopSuccessInvariant proof).1 rfl,
   fun refuted => (positiveLoopFailureInvariant refuted).1 rfl⟩

example : ¬ Succeeds negativeLoop emptyContext (.defaultNeg p) ∧
    ¬ Fails negativeLoop emptyContext (.defaultNeg p) := by
  constructor
  · intro proof
    cases proof with
    | defaultNeg refuted => exact negativeLoopNoFailure refuted
  · intro refuted
    cases refuted with
    | defaultNeg proof => exact negativeLoopNoSuccess proof

example : ¬ Succeeds positiveLoop emptyContext (.defaultNeg p) := by
  intro proof
  cases proof with
  | defaultNeg refuted => exact (positiveLoopFailureInvariant refuted).1 rfl

-- Unsupported variable goals are not classified as complete failures.
example : ¬ Fails emptyProgram emptyContext (.var "x") := by
  intro refuted
  cases refuted
