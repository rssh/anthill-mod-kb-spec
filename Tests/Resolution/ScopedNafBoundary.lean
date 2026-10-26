import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.ScopedSearch AnthillModKbSpec.Semantics

private abbrev T := Term String Nat String
private abbrev P := Program String Nat String "ho_apply"
private abbrev C := Context String Nat String "ho_apply"
private def p : T := .app "p" []
private def q : T := .app "q" []
private def emptyProgram : P := ⟨[], by simp⟩
private def emptyContext : C := ⟨[], [], by simp⟩
private theorem pAtom (parameters : List String) : IsAtom "ho_apply" parameters p := .app (by decide) (by simp)
private theorem qAtom (parameters : List String) : IsAtom "ho_apply" parameters q := .app (by decide) (by simp)
private def pContext : C := emptyContext.assume p (.atom (pAtom []))

private theorem atomicHead {parameters : List String} {symbol : String} {args : List T} {head body : T}
    (backchain : LocalInstance (hoApplySymbol := "ho_apply") parameters (.app symbol args) head body) :
    head = .app symbol args := by
  cases backchain with | fact _ => rfl

private def noP : ExhaustedInstances emptyProgram emptyContext p := ⟨[], by simp, by
  intro body inst
  cases inst with
  | intro member _ _ _ => simp [emptyProgram] at member
  | hypothesis member _ _ => simp [emptyContext] at member⟩

private def noQ : ExhaustedInstances emptyProgram pContext q := ⟨[], by simp, by
  intro body inst
  cases inst with
  | intro member _ _ _ => simp [emptyProgram] at member
  | hypothesis member backchain _ =>
      simp only [pContext, Context.assume, emptyContext, List.mem_cons, List.not_mem_nil, or_false] at member
      subst_vars
      have same := atomicHead backchain
      simp [q] at same⟩

private theorem pFails : Fails emptyProgram emptyContext p :=
  .atom (pAtom []) (by simp [Term.freeVars]) (by simp [Context.Closed, emptyContext])
    (by simp [emptyContext]) noP (by simp [noP])

private theorem qFailsUnderP : Fails emptyProgram pContext q :=
  .atom (qAtom []) (by simp [Term.freeVars])
    (by simp [Context.Closed, pContext, Context.assume, emptyContext, p, Term.freeVars])
    (by simp [pContext, Context.assume, emptyContext, p]) noQ (by simp [noQ])

private theorem implicationFails : Fails emptyProgram emptyContext (.imp p q) :=
  .imp (.atom (pAtom [])) (.atom (qAtom [])) qFailsUnderP

-- Operational nonprovability of an implication is not its semantic falsity.
-- This is a counterexample to adequacy in ANY Model, not just Boolean models.
example {Value : Type} (model : Model Nat String Value "ho_apply") :
    ¬ model.FailureAdequate emptyProgram.toKb (failureEvidence emptyProgram) := by
  intro adequate
  let environment : Environment String Value := fun _ => model.inhabitant
  have pNegative := adequate [] p (by simp [p, Term.freeVars])
    ⟨rfl, rfl, emptyContext, rfl, pFails⟩ environment (by intro assumption member; cases member)
  have implicationNegative := adequate [] (.imp p q) (by simp [p, q, Term.freeVars])
    ⟨rfl, rfl, emptyContext, rfl, implicationFails⟩ environment (by intro assumption member; cases member)
  have pFalse : ¬ model.holds (model.eval environment p) :=
    model.defaultNegation_coherent _ (by simpa only [Model.Satisfies, Model.eval] using pNegative)
  have implicationTrue : model.holds (model.eval environment (.imp p q)) := by
    simp only [Model.eval]
    exact (model.holds_implication _ _).mpr (fun yes => False.elim (pFalse yes))
  exact model.defaultNegation_coherent _
    (by simpa only [Model.Satisfies, Model.eval] using implicationNegative) implicationTrue
