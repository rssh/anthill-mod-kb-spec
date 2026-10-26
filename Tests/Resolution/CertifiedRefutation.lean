import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Semantics AnthillModKbSpec.GroundSearch

private abbrev T := Term String Nat String
private abbrev P := Program String Nat String "ho_apply"
private abbrev C := Context String Nat String "ho_apply"
private def p : T := .app "p" []
private def q : T := .app "q" []
private def emptyContext : C := ⟨[], by simp⟩
private theorem pAtom : IsAtom "ho_apply" p := .app (by decide) (by simp)
private theorem qAtom : IsAtom "ho_apply" q := .app (by decide) (by simp)

-- A nonempty program where NAF establishes a positive fact.
private def program : P := ⟨[.definite p [.defaultNeg q]], by
  intro clause member; simp at member; subst clause
  exact .definite pAtom (by intro goal member; simp at member; subst goal; exact .defaultNeg (.atom qAtom))⟩

-- p() is true; all other ordinary ground atoms, including p(nonempty args),
-- are false. Constructor keys preserve the argument distinctions.
private def interpretation (symbol : String) (args : List (DataKey Nat String)) : Prop :=
  symbol = "p" ∧ args = []
private def model := Model.herbrand "ho_apply" interpretation

private theorem completed : model.GroundCompleted program emptyContext := by
  intro atom valid environment
  cases valid with
  | app ordinary argsValid =>
      dsimp only [model]
      rw [Model.herbrand_atom interpretation environment ordinary]
      simp only [interpretation, List.map_eq_nil_iff]
      constructor
      · rintro ⟨rfl, rfl⟩
        refine Or.inr ⟨[.defaultNeg q], by simp [program, p], ?_⟩
        simp only [q, Term.conjunction, List.foldr_cons, List.foldr_nil, Model.Satisfies,
          Model.eval, List.map_nil]
        simp [Model.herbrand, resolveAtom, interpretation]
      · intro alternatives
        rcases alternatives with member | ⟨body, member, bodyTrue⟩
        · simp [emptyContext] at member
        · simp [program, p] at member
          exact member.1

private theorem missingQ : Fails program emptyContext q :=
  .atom qAtom (by simp [emptyContext]) (by intro body member; simp [program, p, q] at member)
private theorem notQ : Succeeds program emptyContext (.defaultNeg q) := .defaultNeg missingQ
private theorem provesP : Succeeds program emptyContext p :=
  .clause (body := [.defaultNeg q]) pAtom (by simp [program, p]) (.conj notQ .truth)

-- Ground NAF can establish p. This provider's adequacy has already been proved.
private theorem pEstablished : CertifiedRefutation.Established model [] p :=
  CertifiedRefutation.Established.ofDerives model (model.ground_completed_models completed)
    (model.ground_failure_adequate completed (Model.herbrand_complement interpretation))
    (succeeds_toDerives provesP)

private theorem qRefuted : CertifiedRefutation.Refutes model program.toKb [] q :=
  .ground rfl completed missingQ
private theorem implicationRefuted : CertifiedRefutation.Refutes model program.toKb [] (.imp p q) :=
  .imp pEstablished qRefuted
private theorem nestedRefuted : CertifiedRefutation.Refutes model program.toKb [] (.imp p (.imp p q)) :=
  .imp pEstablished (.imp pEstablished qRefuted)

example : Derives "ho_apply" program.toKb [] (.defaultNeg (.imp p q))
    (CertifiedRefutation.failureEvidence model program.toKb) :=
  implicationRefuted.toDerives (by simp [p, q, Term.freeVars])

example : Derives "ho_apply" program.toKb [] (.defaultNeg (.imp p (.imp p q)))
    (CertifiedRefutation.failureEvidence model program.toKb) :=
  nestedRefuted.toDerives (by simp [p, q, Term.freeVars])

example : CertifiedRefutation.Refutes model program.toKb [] (.conj (.imp p q) .truth) :=
  .conjLeft implicationRefuted
example : CertifiedRefutation.Refutes model program.toKb [] (.disj q (.imp p q)) :=
  .disj qRefuted implicationRefuted
example : CertifiedRefutation.Refutes model program.toKb [] (.defaultNeg p) :=
  .defaultNeg pEstablished

example : model.FailureAdequate program.toKb (CertifiedRefutation.failureEvidence model program.toKb) :=
  CertifiedRefutation.failureAdequate model (Model.herbrand_complement interpretation) _
example : ¬ Derives "ho_apply" program.toKb [] .falsity
    (CertifiedRefutation.failureEvidence model program.toKb) :=
  CertifiedRefutation.consistent model (model.ground_completed_models completed)
    (Model.herbrand_complement interpretation)

example : ¬ CertifiedRefutation.Refutes model program.toKb [] (.imp q p) := by
  intro refuted
  have implicationTrue : model.Satisfies (fun _ => model.inhabitant) (.imp q p) := by
    simp only [Model.Satisfies, Model.eval]
    apply (model.holds_implication _ _).mpr
    intro premise
    exact pEstablished _ (by intro assumption member; cases member)
  exact refuted.sound (Model.herbrand_complement interpretation) _
    (by intro assumption member; cases member) implicationTrue

-- The original empty-KB example cannot produce a certified implication refutation.
private def emptyProgram : P := ⟨[], by simp⟩
private def falseInterpretation : String → List (DataKey Nat String) → Prop := fun _ _ => False
private def emptyModel := Model.herbrand "ho_apply" falseInterpretation
private theorem emptyCompleted : emptyModel.GroundCompleted emptyProgram emptyContext := by
  intro atom valid environment
  cases valid with
  | app ordinary args =>
      dsimp only [emptyModel]
      rw [Model.herbrand_atom falseInterpretation environment ordinary]
      simp [falseInterpretation, emptyProgram, emptyContext]

private theorem pFalse : ∀ environment, ¬ emptyModel.Satisfies environment p := by
  intro environment
  simp [p, emptyModel, Model.Satisfies, Model.eval, Model.herbrand, resolveAtom, falseInterpretation]

example : ¬ CertifiedRefutation.Established emptyModel [] p := by
  intro established
  exact pFalse _ (established (fun _ => emptyModel.inhabitant) (by intro assumption member; cases member))

example : ¬ CertifiedRefutation.Refutes emptyModel emptyProgram.toKb [] (.imp p q) := by
  intro refuted
  apply refuted.sound (Model.herbrand_complement falseInterpretation) (fun _ => emptyModel.inhabitant)
    (by intro assumption member; cases member)
  simp only [Model.Satisfies, Model.eval]
  exact (emptyModel.holds_implication _ _).mpr (fun yes => False.elim (pFalse _ yes))

-- An assumption can establish p only in its extended context, not at the root.
private theorem assumedP : CertifiedRefutation.Established emptyModel [p] p := by
  intro environment valid
  exact valid p (by simp)
example : CertifiedRefutation.Refutes emptyModel emptyProgram.toKb [p] (.imp p .falsity) :=
  .imp assumedP .falsity
example : ¬ CertifiedRefutation.Refutes emptyModel emptyProgram.toKb [] (.imp p .falsity) := by
  intro refuted
  apply refuted.sound (Model.herbrand_complement falseInterpretation) (fun _ => emptyModel.inhabitant)
    (by intro assumption member; cases member)
  simp only [Model.Satisfies, Model.eval]
  exact (emptyModel.holds_implication _ _).mpr (fun yes => False.elim (pFalse _ yes))

-- NAF still requires a closed operand even when a refutation is available.
example : (Term.imp (.app "p" [.var "x"]) (.falsity : T)).freeVars ≠ [] := by
  simp [Term.freeVars]

-- Established antecedents may themselves be higher-level implications.
private theorem identityEstablished : CertifiedRefutation.Established model [] (.imp p p) :=
  CertifiedRefutation.Established.ofPositive model (model.ground_completed_models completed)
    (.impIntro (.assumption (by simp)))
example : CertifiedRefutation.Refutes model program.toKb [] (.imp (.imp p p) q) :=
  .imp identityEstablished qRefuted
