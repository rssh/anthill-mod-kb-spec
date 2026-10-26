import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Semantics AnthillModKbSpec.ScopedSearch

private abbrev T := Term String Nat String
private abbrev P := Program String Nat String "ho_apply"
private abbrev C := Context String Nat String "ho_apply"
private def p : T := .app "p" []
private def q : T := .app "q" []
private def empty : P := ⟨[], by simp⟩
private def scope : C := ⟨[], [], by simp⟩
private def falseAtoms : String → List (DataKey Nat String) → Prop := fun _ _ => False
private def model := Model.herbrand "ho_apply" falseAtoms
private theorem negation : model.ComplementNAF := Model.herbrand_complement falseAtoms
private theorem emptyModels : model.Models empty.toKb := by
  intro clause member; change clause ∈ empty.clauses at member; simp [empty] at member
private theorem pAtom (parameters : List String) : IsAtom "ho_apply" parameters p := .app (by decide) (by simp)
private theorem qAtom (parameters : List String) : IsAtom "ho_apply" parameters q := .app (by decide) (by simp)
private def noP : ExhaustedInstances empty scope p := ⟨[], by simp, by
  intro body instanceProof
  cases instanceProof with
  | intro member _ _ _ => simp [empty] at member
  | hypothesis member _ _ => simp [scope] at member⟩
private theorem pFalse (environment : Environment String (DataKey Nat String × Prop)) :
    ¬ model.Satisfies environment p := by
  simp [model, Model.Satisfies, Model.eval, Model.herbrand, resolveAtom, falseAtoms, p]
private theorem completed : model.ScopedAtomCompleted empty scope p := by
  intro environment valid
  constructor
  · intro impossible; exact False.elim (pFalse environment impossible)
  · intro support
    rcases support with member | ⟨body, instanceProof, bodyTrue⟩
    · simp [scope] at member
    · have impossible := noP.complete body instanceProof
      simp [noP] at impossible
private theorem pRefuted : CertifiedRefutation.Refutes model empty.toKb [] p :=
  .scopedAtom rfl (pAtom []) (by simp [p, Term.freeVars]) (by simp [scope, Context.Closed])
    completed (by simp [scope]) noP (by simp [noP])
private theorem notP : CertifiedScopedSearch.Succeeds model empty scope (.defaultNeg p) :=
  .defaultNeg (by simp [p, Term.freeVars]) pRefuted

-- Complete atomic failure is accepted; hypothetical failure alone is rejected.
example (environment : Environment String (DataKey Nat String × Prop)) :
    model.Satisfies environment (.defaultNeg p) :=
  notP.sound emptyModels negation environment (by intro assumption member; cases member)

private theorem implicationTrue (environment : Environment String (DataKey Nat String × Prop)) :
    model.Satisfies environment (.imp p q) := by
  simp only [Model.Satisfies, Model.eval]
  exact (model.holds_implication _ _).mpr (fun yes => False.elim (pFalse environment yes))

example : ¬ CertifiedScopedSearch.Succeeds model empty scope (.defaultNeg (.imp p q)) := by
  intro proof
  let environment : Environment String (DataKey Nat String × Prop) := fun _ => model.inhabitant
  have impossible := proof.sound emptyModels negation environment (by intro assumption member; cases member)
  exact model.defaultNegation_coherent _
    (by simpa only [Model.Satisfies, Model.eval] using impossible) (implicationTrue environment)

-- Positive hypothetical reasoning and restoration of the original context remain.
private theorem identity : CertifiedScopedSearch.Succeeds model empty scope (.imp p p) := by
  apply CertifiedScopedSearch.Succeeds.imp (.atom (pAtom [])) (.atom (pAtom []))
  exact .assumption (pAtom []) (by simp [Context.assume, p])
example : CertifiedScopedSearch.Succeeds model empty scope (.conj (.imp p p) (.defaultNeg p)) :=
  .conj identity notP
example : CertifiedScopedSearch.Succeeds model empty scope (.imp p (.imp q p)) := by
  apply CertifiedScopedSearch.Succeeds.imp (.atom (pAtom [])) (.imp (.atom (qAtom [])) (.atom (pAtom [])))
  apply CertifiedScopedSearch.Succeeds.imp (.atom (qAtom [])) (.atom (pAtom []))
  exact .assumption (pAtom []) (by simp [Context.assume, p, q])

example : CertifiedScopedSearch.Succeeds model empty scope (.imp p (.defaultNeg .falsity)) := by
  apply CertifiedScopedSearch.Succeeds.imp (.atom (pAtom [])) (.defaultNeg .falsity)
  exact .defaultNeg (by simp [Term.freeVars]) .falsity

-- Rigid universal introduction uses a genuinely fresh name, with a local IH.
private def px (value : T) : T := .app "px" [value]
private theorem pxAtom (parameters : List String) (value : T) (valid : IsData parameters value) :
    IsAtom "ho_apply" parameters (px value) :=
  .app (by decide) (by intro arg member; simp at member; subst arg; exact valid)
example : CertifiedScopedSearch.Succeeds model empty scope
    (.forallVar "x" (.imp (px (.var "x")) (px (.var "x")))) := by
  apply CertifiedScopedSearch.Succeeds.forallVar
  · exact .forallVar (.imp (.atom (pxAtom _ _ (.parameter (by simp))))
      (.atom (pxAtom _ _ (.parameter (by simp)))))
  · simp only [Term.openFree, px, List.map_cons, List.map_nil, ↓reduceIte]
    apply CertifiedScopedSearch.Succeeds.imp
      (.atom (pxAtom _ _ (.parameter (by simp [Context.extend]))))
      (.atom (pxAtom _ _ (.parameter (by simp [Context.extend]))))
    exact .assumption (pxAtom _ _ (.parameter (by simp [Context.assume, Context.extend])))
      (by simp [Context.assume, px])

-- A selected global clause can establish a positive atom using certified NAF.
private def program : P := ⟨[.definite p [.defaultNeg q]], by
  intro clause member; simp at member; subst clause
  apply IsClause.definite (.app (by decide) (by simp))
  apply SafeGoal.conj
  · exact .defaultNeg (.atom (qAtom _)) (by simp [q, Term.freeVars])
  · exact .basic .truth⟩
private def interpretation (symbol : String) (args : List (DataKey Nat String)) : Prop := symbol = "p" ∧ args = []
private def positiveModel := Model.herbrand "ho_apply" interpretation
private theorem positiveNegation : positiveModel.ComplementNAF := Model.herbrand_complement interpretation
private theorem headPreserved {σ : Substitution String Nat String} {s t : String} {a b : List T}
    (substitution : Substitutes σ (.app s a) (.app t b)) : s = t := by
  cases substitution; rfl
private def noQ : ExhaustedInstances program scope q := ⟨[], by simp, by
  intro body instanceProof
  cases instanceProof with
  | intro member headSubst bodySubst valid =>
      simp [program] at member
      rcases member with ⟨rfl, rfl⟩
      have impossible := headPreserved headSubst
      simp at impossible
  | hypothesis member _ _ => simp [scope] at member⟩
private theorem qCompleted : positiveModel.ScopedAtomCompleted program scope q := by
  intro environment valid
  constructor
  · intro impossible
    simp [positiveModel, Model.Satisfies, Model.eval, Model.herbrand, resolveAtom, interpretation, q] at impossible
  · intro support
    rcases support with member | ⟨body, instanceProof, bodyTrue⟩
    · simp [scope] at member
    · have impossible := noQ.complete body instanceProof
      simp [noQ] at impossible
private theorem qRefuted : CertifiedRefutation.Refutes positiveModel program.toKb [] q :=
  .scopedAtom rfl (qAtom []) (by simp [q, Term.freeVars]) (by simp [scope, Context.Closed])
    qCompleted (by simp [scope]) noQ (by simp [noQ])
private theorem positiveP : CertifiedScopedSearch.Succeeds positiveModel program scope p := by
  apply CertifiedScopedSearch.Succeeds.clause (body := [.defaultNeg q]) (pAtom [])
  · exact .intro (σ := Term.var) (head := p) (body := [.defaultNeg q]) (by simp [program, p])
      (Substitutes.identity _) (.cons (Substitutes.identity _) .nil)
      (by intro goal member; simp at member; subst goal; exact .defaultNeg (.atom (qAtom [])))
  · exact .conj (.defaultNeg (by simp [q, Term.freeVars]) qRefuted) .truth

private theorem programModels : positiveModel.Models program.toKb := by
  intro clause member environment
  change clause ∈ program.clauses at member
  simp [program] at member; subst clause
  simp only [Model.Satisfies, HornClause.toFormula, Model.eval]
  apply (positiveModel.holds_implication _ _).mpr
  intro bodyTrue
  simp [positiveModel, Model.eval, Model.herbrand, resolveAtom, interpretation, p]

-- A newly established antecedent can itself feed implication refutation.
private theorem implicationRefuted : CertifiedRefutation.Refutes positiveModel program.toKb [] (.imp p q) :=
  positiveP.refutes_imp programModels positiveNegation qRefuted
example : CertifiedScopedSearch.Succeeds positiveModel program scope (.defaultNeg (.imp p q)) :=
  .defaultNeg (by simp [p, q, Term.freeVars]) implicationRefuted
example : ¬ CertifiedRefutation.Refutes positiveModel program.toKb [] p :=
  positiveP.not_refuted programModels positiveNegation (fun _ => positiveModel.inhabitant)
    (by intro assumption member; cases member)
example : ¬ CertifiedScopedSearch.Succeeds positiveModel program
    (⟨[], [], by simp⟩ : C) .falsity := CertifiedScopedSearch.no_falsity programModels positiveNegation

-- Local definite clauses use the same positive rule as global instances.
example : CertifiedScopedSearch.Succeeds model empty scope (.imp (.conj p (.imp p q)) q) := by
  apply CertifiedScopedSearch.Succeeds.imp
    (.conj (.atom (pAtom [])) (.imp (.atom (pAtom [])) (.atom (qAtom [])))) (.atom (qAtom []))
  apply CertifiedScopedSearch.Succeeds.clause (body := [.conj p .truth]) (qAtom [])
  · exact .hypothesis (assumption := .conj p (.imp p q)) (by simp [Context.assume])
      (.conjRight (.imp (.fact (qAtom [])))) (.conj (.atom (pAtom [])) .truth)
  · apply CertifiedScopedSearch.Succeeds.conj
    · apply CertifiedScopedSearch.Succeeds.conj
      · apply CertifiedScopedSearch.Succeeds.clause (body := [.truth]) (pAtom [])
        · exact .hypothesis (assumption := .conj p (.imp p q)) (by simp [Context.assume])
            (.conjLeft (.fact (pAtom []))) .truth
        · exact .conj .truth .truth
      · exact .truth
    · exact .truth

-- Schematic clauses, rigid instantiation, and flexible query answers also use
-- the certified path; each clause use chooses its own substitution.
private def h (value : T) : T := .app "h" [value]
private def allH : P := ⟨[.definite (h (.var "u")) []], by
  intro clause member; simp at member; subst clause
  exact .definite (.app (by decide) (by intro arg member; simp at member; subst arg; exact .var)) (.basic .truth)⟩
private def factModel := Model.trueAtoms Nat String "ho_apply"
private theorem hAtom (parameters : List String) (value : T) (valid : IsData parameters value) :
    IsAtom "ho_apply" parameters (h value) :=
  .app (by decide) (by intro arg member; simp at member; subst arg; exact valid)
private theorem anyH (context : C) (value : T) (valid : IsData context.parameters value) :
    CertifiedScopedSearch.Succeeds factModel allH context (h value) := by
  apply CertifiedScopedSearch.Succeeds.clause (body := []) (hAtom _ _ valid)
  · exact .intro (head := h (.var "u")) (body := []) (σ := fun _ => value)
      (by simp [allH, h]) (.app (.cons .var .nil)) .nil (by simp)
  · exact .truth
private theorem allHModels : factModel.Models allH.toKb := by
  intro clause member environment
  change clause ∈ allH.clauses at member
  simp [allH] at member; subst clause
  exact Model.trueAtoms_definite environment _ _ _
private theorem factNegation : factModel.ComplementNAF := by
  intro value; change (!value = true ↔ ¬value = true); cases value <;> decide
private theorem answer : CertifiedScopedSearch.Answers factModel allH scope (h (.var "answer"))
    (Substitution.single "answer" (.lit 7)) := by
  apply CertifiedScopedSearch.Answers.intro
  · exact .basic (.atom (.app (by decide) (by intro arg member; simp at member; subst arg; exact .var)))
  · intro name member; simp [scope] at member
  · exact .app (.cons (.singleVar "answer" (.lit 7)) .nil)
  · exact .atom (hAtom [] _ .lit)
  · exact anyH scope (.lit 7) .lit
example : ∃ instantiated, Substitutes (Substitution.single "answer" (.lit 7)) (h (.var "answer")) instantiated ∧
    ∀ environment, factModel.ContextHolds environment scope.assumptions → factModel.Satisfies environment instantiated :=
  answer.sound allHModels factNegation
