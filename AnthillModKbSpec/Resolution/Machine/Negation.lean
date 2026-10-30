import AnthillModKbSpec.Resolution.Machine.Positive

namespace AnthillModKbSpec.Machine

/-! # Ground negation as failure (S07)

The command that hands a NAF goal to the machine. When the base strategy has
no answer for a goal written `naf A` (`unsupported`), and the goal is ground
NAF, it answers `Response.negate`: the machine runs `A` in the same run behind
a barrier (`step_negate`). If the operand's search is exhausted with no gap
recorded meanwhile, the barrier proves the goal by `defaultNegIntro` with the
certificate `certify` built; a proved operand fails the goal and discards the
operand's remaining alternatives (`step_refute`).

Ground NAF needs an obligation that is ground as read
(`Store.groundNegation`): neither the operand nor an assumption, read through
the store, names a free name. The operand's search could bind an unbound
flexible name, deciding the NAF for that binding only; a rigid parameter, as
in `∀X. naf p(X)`, stands for every value, and the search failing for the
parameter itself does not cover them. A name bound before the NAF is read
through its binding, so `∃X. r(X) ∧ naf q(X)` decides `naf q(a)` once `r(a)`
binds `X`. The machine checks the same condition and also leaves undecided, as
a gap, every NAF whose operand's search delays a goal. Every other answer of
the base strategy is kept, so its exact candidates (an assumed `naf A`, ex
falso) still come first. Open and scoped NAF are S10's. -/

variable {Variable Literal Symbol Certificate : Type} [DecidableEq Variable] [FreshNames Variable]

/-- `readNames` covers the names of the reading. -/
theorem readNames_cover (bindings : List (Variable × Term Variable Literal Symbol)) (term : Term Variable Literal Symbol) :
    ∀ other ∈ (resolveWith bindings term).freeVars, other ∈ readNames bindings term.freeVars := by
  induction bindings with
  | nil => intro other member; simpa [resolveWith, readNames] using member
  | cons binding rest ih =>
      obtain ⟨name, value⟩ := binding
      intro other member
      rw [resolveWith_cons] at member
      obtain ⟨middle, middleMember, inside⟩ := (Term.instantiate_substitutes _ _).freeVars_cover other member
      simp only [readNames, List.mem_flatMap]
      refine ⟨middle, ih middle middleMember, ?_⟩
      by_cases same : middle = name
      · subst same
        simpa only [Substitution.single, Substitution.bind, ite_true] using inside
      · simpa only [Substitution.single, Substitution.bind, same, ite_false, Term.freeVars] using inside

/-- A term closed as read reads as a closed term. -/
theorem Store.readClosed_resolve {store : Store Variable Literal Symbol} {term : Term Variable Literal Symbol}
    (closed : store.readClosed term = true) : (store.resolve term).freeVars = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name member
  have covered := readNames_cover store.bindings term name member
  simp only [Store.readClosed, List.isEmpty_iff] at closed
  rw [closed] at covered
  cases covered

/-- A NAF obligation ground as read: its operand and every assumption, as the
strategy reads them, are closed. -/
theorem Store.groundNegation_read {store : Store Variable Literal Symbol} {obligation : Obligation Variable Literal Symbol}
    {operand : Formula Variable Literal Symbol} (ground : store.groundNegation obligation operand = true) :
    (store.resolve operand).freeVars = [] ∧ ∀ pair ∈ store.readContext obligation, pair.2.freeVars = [] := by
  simp only [Store.groundNegation, Bool.and_eq_true, List.all_eq_true] at ground
  refine ⟨Store.readClosed_resolve ground.1, fun pair member => ?_⟩
  obtain ⟨assumption, inside, rfl⟩ := List.mem_map.mp member
  exact Store.readClosed_resolve (ground.2 assumption inside)

/-- Ground NAF as the fallback of a base strategy. -/
def Strategy.withNegation (certify : Obligation Variable Literal Symbol → Formula Variable Literal Symbol → Certificate)
    (strategy : Strategy Variable Literal Symbol Certificate) : Strategy Variable Literal Symbol Certificate :=
  fun obligation store =>
    match strategy obligation store with
    | .unsupported =>
        match obligation.goal with
        | .defaultNeg operand =>
            if store.groundNegation obligation operand then .negate (certify obligation operand)
            else .unsupported
        | _ => .unsupported
    | response => response

/-- The combined command is sound when the base strategy is, and when every NAF
node it would build is sound on its own. Reconstruction does not see the
operand's search, so this asks the node to hold whatever the operand does: only
a provider accepting every such node meets it. A NAF node justified by the
exhaustion of its operand needs a run-level argument instead, as P0 has
(`P0.run_correct`); making that generic is S10's. -/
theorem Strategy.withNegation_sound {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol}
    {certify : Obligation Variable Literal Symbol → Formula Variable Literal Symbol → Certificate}
    {strategy : Strategy Variable Literal Symbol Certificate} (sound : Strategy.Sound hoApplySymbol kb naf strategy)
    (negations : ∀ obligation store operand, store.Scoped → obligation.Declared store →
      obligation.goal = .defaultNeg operand →
        CandidateSound hoApplySymbol kb naf store obligation (Expansion.negation (certify obligation operand))) :
    Strategy.Sound hoApplySymbol kb naf (strategy.withNegation certify) := by
  unfold Strategy.Sound
  intro obligation store storeScoped declared expansion member
  unfold Strategy.withNegation at member
  split at member
  · split at member
    · rename_i operand goalEq
      split at member
      · simp only [Response.alternatives, List.mem_singleton] at member
        subst member
        exact negations obligation store operand storeScoped declared goalEq
      · cases member
    · cases member
  · exact sound obligation store storeScoped declared expansion member

end AnthillModKbSpec.Machine
