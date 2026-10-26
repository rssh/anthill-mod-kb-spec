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

-- Adequacy is a theorem about the ACTUAL finite-failure provider.
private theorem adequate : model.FailureAdequate program.toKb (failureEvidence program emptyContext) :=
  model.ground_failure_adequate completed (Model.herbrand_complement interpretation)

example : model.Models program.toKb := model.ground_completed_models completed
example : ¬ Derives "ho_apply" program.toKb [] .falsity (failureEvidence program emptyContext) :=
  model.consistent (model.ground_completed_models completed) adequate
example (environment : Environment String (DataKey Nat String × Prop)) : model.Satisfies environment p :=
  (model.ground_certificates_sound completed (Model.herbrand_complement interpretation)).1 p provesP environment
example (environment : Environment String (DataKey Nat String × Prop)) :
    model.Satisfies environment (.defaultNeg q) :=
  model.ground_completed_sound completed (Model.herbrand_complement interpretation)
    (succeeds_toDerives notQ) environment (by intro assumption member; cases member)

-- Incomplete search is still not complete failure. A positive self-loop has
-- a completed model where p is false, but no finite failure certificate.
private def loop : P := ⟨[.definite p [p]], by
  intro clause member; simp at member; subst clause
  exact .definite pAtom (by intro goal member; simp at member; subst goal; exact .atom pAtom)⟩
private def falseInterpretation : String → List (DataKey Nat String) → Prop := fun _ _ => False
private def loopModel := Model.herbrand "ho_apply" falseInterpretation

private theorem loopCompleted : loopModel.GroundCompleted loop emptyContext := by
  intro atom valid environment
  cases valid with
  | app ordinary argsValid =>
      dsimp only [loopModel]
      rw [Model.herbrand_atom falseInterpretation environment ordinary]
      simp only [falseInterpretation]
      constructor
      · intro impossible; cases impossible
      · intro alternatives
        rcases alternatives with member | ⟨body, member, bodyTrue⟩
        · simp [emptyContext] at member
        · simp [loop, p] at member
          rcases member with ⟨⟨rfl, rfl⟩, rfl⟩
          simp only [Term.conjunction, List.foldr_cons, List.foldr_nil, Model.Satisfies,
            Model.eval, List.map_nil] at bodyTrue
          simp [Model.herbrand, resolveAtom, falseInterpretation] at bodyTrue

example : loopModel.FailureAdequate loop.toKb (failureEvidence loop emptyContext) :=
  loopModel.ground_failure_adequate loopCompleted (Model.herbrand_complement falseInterpretation)

-- Complement completion is deliberately conditional on model existence.
-- The odd negative cycle has no two-valued completed model, although the
-- operational judgments conservatively provide neither root certificate.
private def negativeLoop : P := ⟨[.definite p [.defaultNeg p]], by
  intro clause member; simp at member; subst clause
  exact .definite pAtom (by intro goal member; simp at member; subst goal; exact .defaultNeg (.atom pAtom))⟩

example {Value : Type} (m : Model Nat String Value "ho_apply") (negation : m.ComplementNAF) :
    ¬ m.GroundCompleted negativeLoop emptyContext := by
  intro complete
  let environment : Environment String Value := fun _ => m.inhabitant
  have atomIff := complete p pAtom environment
  have forward : m.Satisfies environment p → ¬ m.Satisfies environment p := by
    intro yes
    rcases atomIff.mp yes with member | ⟨body, member, trueBody⟩
    · simp [emptyContext] at member
    · simp [negativeLoop] at member
      subst body
      simp only [Model.Satisfies, Term.conjunction, List.foldr_cons, List.foldr_nil, Model.eval] at trueBody
      exact (negation _).mp ((m.holds_conjunction _ _).mp trueBody).1
  have reverse : ¬ m.Satisfies environment p → m.Satisfies environment p := by
    intro no
    apply atomIff.mpr
    refine Or.inr ⟨[.defaultNeg p], by simp [negativeLoop], ?_⟩
    simp only [Model.Satisfies, Term.conjunction, List.foldr_cons, List.foldr_nil, Model.eval]
    exact (m.holds_conjunction _ _).mpr ⟨(negation _).mpr no, m.holds_top⟩
  have no : ¬ m.Satisfies environment p := fun yes => forward yes yes
  exact no (reverse no)
