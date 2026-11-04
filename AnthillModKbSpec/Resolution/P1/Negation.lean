import AnthillModKbSpec.Resolution.P1.Refutation
import AnthillModKbSpec.Resolution.P1.Export
import AnthillModKbSpec.Resolution.Machine.Refutation

/-! # Evidence-first NAF by refutation (S10)

`Strategy.withRefutation` answers a NAF goal `naf G`, as read, in this order:

1. **Evidence first.** If the base strategy has a candidate, such as an assumed
   `naf G` closing the goal by identity, those candidates are the answer and no
   failure search starts.
2. **Flexible names delay.** If `G` or the context, as read, names an unbound
   flexible name, the goal waits until it is bound (`Response.delay`, S18).
   Still waiting when the branch is proved, it runs once more while the branch
   closes (`Store.close`): no name is bound from then on, so it no longer
   waits, and the names it waited on stand for every value.
3. **Refutation.** Otherwise every free name is a rigid parameter, or the
   branch is closing; either way each stands for every value. A bounded run of `refuter` looks for a proof of `G → false`
   in the completed program; its exported tree, if it checks against the
   completed snapshot (`refutationCheck`), is the evidence of a NAF node. A
   run that finds none leaves the base answer, so the goal is a gap or a miss,
   never refuted.

A parameter is never read as a constant that matches nothing: the refutation
holds for every value, through the case split of the completion. The NAF node
is read the same in every later store, since rigid names are never bound and a
closing store binds nothing (`Store.read_stableNegation`), so the evidence
checked for it stays the evidence of the node. `nafByRefutation` puts this together over the left strategy and a
completed program; it is sound for the completed program's KB with refutation
evidence (`nafByRefutation_sound`), so in every model of the completion and the
free equality theory with complement NAF. -/

namespace AnthillModKbSpec

open Machine P1 Completion

namespace Machine

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal]
  [FreshNames Variable]

omit [DecidableEq Symbol] [DecidableEq Literal] in
/-- A term whose free names are all rigid reads the same in every later store. -/
theorem Store.read_rigid {store later : Store Variable Literal Symbol} (valid : store.Scoped)
    (laterScoped : later.Scoped) (refines : store.Refines later) {term read : Term Variable Literal Symbol}
    (reads : store.resolve term = read) (rigid : ∀ name ∈ read.freeVars, store.info? name = some .rigid) :
    later.resolve term = read := by
  rw [valid.read_refines reads refines]
  exact resolveWith_unbound fun name member => laterScoped.unbound fun dependencies flexible => by
    rw [refines.rigid name (rigid name member)] at flexible
    cases flexible

/-- Every free name of the terms is a rigid name of the store. -/
def Store.allRigid (store : Store Variable Literal Symbol) (terms : List (Term Variable Literal Symbol)) : Bool :=
  terms.all fun term => term.freeVars.all fun name => decide (store.info? name = some .rigid)

omit [DecidableEq Symbol] [DecidableEq Literal] [FreshNames Variable] in
theorem Store.allRigid_spec {store : Store Variable Literal Symbol} {terms : List (Term Variable Literal Symbol)}
    (rigid : store.allRigid terms = true) : ∀ term ∈ terms, ∀ name ∈ term.freeVars, store.info? name = some .rigid := by
  intro term inside name member
  simp only [Store.allRigid, List.all_eq_true, decide_eq_true_eq] at rigid
  exact rigid term inside name member

/-- The unbound flexible names of the terms. -/
def Store.waitingNames (store : Store Variable Literal Symbol) (terms : List (Term Variable Literal Symbol)) : List Variable :=
  ((terms.flatMap Term.freeVars).filter store.assignable).eraseDups

omit [DecidableEq Symbol] [DecidableEq Literal] in
/-- A NAF goal and its context read the same in every later store when the
store is closing, or when their free names, as read, are all rigid. -/
theorem Store.read_stableNegation {store later : Store Variable Literal Symbol} (valid : store.Scoped)
    (laterScoped : later.Scoped) (refines : store.Refines later) {goal operand : Formula Variable Literal Symbol}
    {context : ProofContext Variable Literal Symbol} (readGoal : store.resolve goal = .defaultNeg operand)
    (stable : (store.closing || store.allRigid (operand :: context.map store.resolve)) = true) :
    later.resolve goal = .defaultNeg operand ∧ context.map later.resolve = context.map store.resolve := by
  rcases Bool.or_eq_true_iff.mp stable with closing | rigid
  · exact ⟨(refines.resolve_closing closing goal).trans readGoal,
      List.map_congr_left fun assumption _ => refines.resolve_closing closing assumption⟩
  have allRigid := Store.allRigid_spec rigid
  refine ⟨Store.read_rigid valid laterScoped refines readGoal fun name inside =>
    allRigid operand List.mem_cons_self name (by simpa [Term.freeVars] using inside), ?_⟩
  exact List.map_congr_left fun _ inside => Store.read_rigid valid laterScoped refines rfl fun name occurs =>
    allRigid _ (List.mem_cons_of_mem _ (List.mem_map_of_mem inside)) name occurs

/-- The NAF node of a refutation that is found and checks, or else `response`. -/
def refuteOr (check : ProofContext Variable Literal Symbol → Formula Variable Literal Symbol →
      Term Variable Literal Symbol → Bool)
    (refute : ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Option (Term Variable Literal Symbol))
    (reads : ProofContext Variable Literal Symbol) (operand : Formula Variable Literal Symbol)
    (response : Response Variable Literal Symbol (Term Variable Literal Symbol)) :
    Response Variable Literal Symbol (Term Variable Literal Symbol) :=
  match refute reads operand with
  | some evidence => if check reads operand evidence then .candidates [Expansion.negation evidence] else response
  | none => response

omit [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal] [FreshNames Variable] in
theorem mem_refuteOr
    {check : ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Term Variable Literal Symbol → Bool}
    {refute : ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Option (Term Variable Literal Symbol)}
    {reads : ProofContext Variable Literal Symbol} {operand : Formula Variable Literal Symbol}
    {response : Response Variable Literal Symbol (Term Variable Literal Symbol)}
    {expansion : Expansion Variable Literal Symbol (Term Variable Literal Symbol)}
    (member : expansion ∈ (refuteOr check refute reads operand response).alternatives) :
    expansion ∈ response.alternatives ∨
      ∃ evidence, expansion = Expansion.negation evidence ∧ check reads operand evidence = true := by
  unfold refuteOr at member
  split at member
  · rename_i evidence _
    split at member
    · rename_i checked
      simp only [Response.alternatives, List.mem_singleton] at member
      exact .inr ⟨evidence, member, checked⟩
    · exact .inl member
  · exact .inl member

/-- Evidence-first NAF: the base strategy's candidates, then, for a goal whose
free names are all rigid, or while the branch is closing (`Store.close`), a
NAF node whose refutation checks; otherwise a delay on the names the NAF waits
for. While closing no name will be bound, so the names it waited for are
refuted generically, for every value. A waiting name is flexible, so a goal
whose names are all rigid waits for none. -/
def Strategy.withRefutation (check : ProofContext Variable Literal Symbol → Formula Variable Literal Symbol →
      Term Variable Literal Symbol → Bool)
    (refute : ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Option (Term Variable Literal Symbol))
    (base : Strategy Variable Literal Symbol (Term Variable Literal Symbol)) :
    Strategy Variable Literal Symbol (Term Variable Literal Symbol) := fun obligation store =>
  let response := base obligation store
  match store.resolve obligation.goal, response.alternatives with
  | .defaultNeg operand, [] =>
      let reads := obligation.context.map store.resolve
      if store.closing || store.allRigid (operand :: reads) then refuteOr check refute reads operand response
      else
        match store.waitingNames (operand :: reads) with
        | [] => response
        | names => .delay names
  | _, _ => response

omit [DecidableEq Symbol] [DecidableEq Literal] in
/-- What evidence-first NAF offers: the base's candidates, or a NAF node for a
goal read as `naf G` that is stable, with evidence that checks for the context
and operand as read. -/
theorem mem_withRefutation
    {check : ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Term Variable Literal Symbol → Bool}
    {refute : ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Option (Term Variable Literal Symbol)}
    {base : Strategy Variable Literal Symbol (Term Variable Literal Symbol)} {obligation : Obligation Variable Literal Symbol}
    {store : Store Variable Literal Symbol} {expansion : Expansion Variable Literal Symbol (Term Variable Literal Symbol)}
    (member : expansion ∈ (Strategy.withRefutation check refute base obligation store).alternatives) :
    expansion ∈ (base obligation store).alternatives ∨
      ∃ operand evidence, store.resolve obligation.goal = .defaultNeg operand ∧
        (store.closing || store.allRigid (operand :: obligation.context.map store.resolve)) = true ∧
        expansion = Expansion.negation evidence ∧
        check (obligation.context.map store.resolve) operand evidence = true := by
  unfold Strategy.withRefutation at member
  dsimp only at member
  split at member
  · rename_i _ _ operand readGoal _
    split at member
    · rename_i stable
      rcases mem_refuteOr member with inBase | ⟨evidence, rfl, checked⟩
      · exact .inl inBase
      · exact .inr ⟨operand, evidence, readGoal, stable, rfl, checked⟩
    · split at member
      · exact .inl member
      · cases member
  · exact .inl member

omit [DecidableEq Symbol] [DecidableEq Literal] in
/-- Evidence-first NAF is sound when its base is and its check yields evidence
of the NAF provider, for the context and operand as read. -/
theorem Strategy.withRefutation_sound {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol}
    {check : ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Term Variable Literal Symbol → Bool}
    {refute : ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Option (Term Variable Literal Symbol)}
    {base : Strategy Variable Literal Symbol (Term Variable Literal Symbol)} (baseSound : Strategy.Sound hoApplySymbol kb naf base)
    (checkSound : ∀ context operand evidence, check context operand evidence = true → naf hoApplySymbol kb context operand) :
    Strategy.Sound hoApplySymbol kb naf (Strategy.withRefutation check refute base) := by
  intro obligation store valid declared expansion member
  rcases mem_withRefutation member with inBase | ⟨operand, evidence, readGoal, stable, rfl, checked⟩
  · exact baseSound obligation store valid declared expansion inBase
  intro next woken committed later refines laterScoped _
  obtain ⟨goalRead, contextRead⟩ := Store.read_stableNegation valid laterScoped
    ((Store.commit_refines committed).trans refines) readGoal stable
  simp only [ReadDerives, goalRead, contextRead]
  exact .defaultNegIntro (checkSound _ _ _ checked)

omit [DecidableEq Symbol] [DecidableEq Literal] in
/-- Every NAF node evidence-first NAF offers carries evidence that checks for
the context and operand as read, and they read the same in every later store:
the exported node, read through the final store, passes the same check. -/
theorem Strategy.withRefutation_checked
    {check : ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Term Variable Literal Symbol → Bool}
    {refute : ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Option (Term Variable Literal Symbol)}
    {base : Strategy Variable Literal Symbol (Term Variable Literal Symbol)} {obligation : Obligation Variable Literal Symbol}
    {store later : Store Variable Literal Symbol} {operand : Formula Variable Literal Symbol}
    {evidence : Term Variable Literal Symbol} (valid : store.Scoped) (readGoal : store.resolve obligation.goal = .defaultNeg operand)
    (fresh : ∀ expansion ∈ (base obligation store).alternatives, expansion.rule.id ≠ .defaultNegIntro)
    (member : Expansion.negation evidence ∈ (Strategy.withRefutation check refute base obligation store).alternatives)
    (laterScoped : later.Scoped) (refines : store.Refines later) :
    later.resolve obligation.goal = .defaultNeg operand ∧
      check (obligation.context.map later.resolve) operand evidence = true := by
  rcases mem_withRefutation member with inBase | ⟨found, given, foundGoal, stable, same, checked⟩
  · exact absurd rfl (fresh _ inBase)
  rw [readGoal] at foundGoal
  cases foundGoal
  simp only [Expansion.negation, Expansion.mk.injEq, RuleApp.defaultNegIntro.injEq, and_true] at same
  subst same
  obtain ⟨goalRead, contextRead⟩ := Store.read_stableNegation valid laterScoped refines readGoal stable
  exact ⟨goalRead, contextRead ▸ checked⟩

/-! ## Positive witnesses first

A universal negative `∀x̄. g₁ → … → gₙ → naf G` is defeated by a positive
witness of `∃x̄. g₁ ∧ … ∧ gₙ ∧ G`: a fact `p(one)` with `one` in the guarded
domain makes `∀x. naf p(x)` false in every model (`Semantics.Model.defeats`).
`Strategy.withWitness` asks the witness query before the binders are opened as
rigid parameters; a witness found leaves no candidates, so the branch fails
instead of becoming a gap. A refutation could not be found for the opened goal
anyway: the rigid parameter may be `one`. -/

/-- The universal negative `∀x̄. g₁ → … → gₙ → naf G`. -/
def universalNegative (binders : List Variable) (guards : List (Formula Variable Literal Symbol))
    (operand : Formula Variable Literal Symbol) : Formula Variable Literal Symbol :=
  binders.foldr .forallVar (guards.foldr .imp (.defaultNeg operand))

/-- The positive witness query of a universal negative: `∃x̄. g₁ ∧ … ∧ gₙ ∧ G`. -/
def positiveWitness (binders : List Variable) (guards : List (Formula Variable Literal Symbol))
    (operand : Formula Variable Literal Symbol) : Formula Variable Literal Symbol :=
  binders.foldr .existsVar (Term.conjunction (guards ++ [operand]))

/-- The guards and operand of `g₁ → … → gₙ → naf G`. -/
def guardedNegative? : Formula Variable Literal Symbol → Option (List (Formula Variable Literal Symbol) × Formula Variable Literal Symbol)
  | .defaultNeg operand => some ([], operand)
  | .imp guard rest => (guardedNegative? rest).map fun (guards, operand) => (guard :: guards, operand)
  | _ => none

/-- The binders, guards and operand of a universal negative with at least one binder. -/
def universalNegative? : Formula Variable Literal Symbol →
    Option (List Variable × List (Formula Variable Literal Symbol) × Formula Variable Literal Symbol)
  | .forallVar binder body =>
      match universalNegative? body with
      | some (binders, guards, operand) => some (binder :: binders, guards, operand)
      | none => (guardedNegative? body).map fun (guards, operand) => ([binder], guards, operand)
  | _ => none

omit [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal] [FreshNames Variable] in
theorem guardedNegative?_spec : ∀ {formula : Formula Variable Literal Symbol} {guards operand},
    guardedNegative? formula = some (guards, operand) → formula = guards.foldr .imp (.defaultNeg operand)
  | .defaultNeg _, _, _, parsed => by simp only [guardedNegative?, Option.some.injEq, Prod.mk.injEq] at parsed; obtain ⟨rfl, rfl⟩ := parsed; rfl
  | .imp guard rest, guards, operand, parsed => by
      simp only [guardedNegative?, Option.map_eq_some_iff, Prod.mk.injEq, Prod.exists] at parsed
      obtain ⟨others, _, inner, rfl, rfl⟩ := parsed
      rw [guardedNegative?_spec inner]
      rfl

omit [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal] [FreshNames Variable] in
theorem universalNegative?_spec : ∀ {formula : Formula Variable Literal Symbol} {binders guards operand},
    universalNegative? formula = some (binders, guards, operand) → formula = universalNegative binders guards operand
  | .forallVar binder body, binders, guards, operand, parsed => by
      unfold universalNegative? at parsed
      split at parsed
      · rename_i others inner
        simp only [Option.some.injEq, Prod.mk.injEq] at parsed
        obtain ⟨rfl, rfl, rfl⟩ := parsed
        rw [universalNegative?_spec inner]
        rfl
      · simp only [Option.map_eq_some_iff, Prod.mk.injEq, Prod.exists] at parsed
        obtain ⟨_, _, guarded, rfl, rfl, rfl⟩ := parsed
        rw [guardedNegative?_spec guarded]
        rfl

/-- A candidate that closes the goal itself: by an assumption, ex falso, or a
clause concluding it, directly or through its compound head, also through an
`ho_apply` conversion (S11). -/
def Expansion.closes {Certificate : Type} (expansion : Expansion Variable Literal Symbol Certificate) : Bool :=
  [RuleId.assumption, .falsityElim, .clause, .headUse, .headProject].contains expansion.rule.base.id

/-- Positive witnesses first: for a universal negative, the witness query is
asked before the binders are opened; a witness `witnessed` under the context,
as read, leaves no candidates. Evidence the base has for the goal itself (a
candidate that `closes` it, such as an assumed universal negative or an
assumed falsity) comes first; other base candidates, which open the goal or
use other assumptions, do not. Any other goal is the base strategy's. -/
def Strategy.withWitness {Certificate : Type}
    (witnessed : ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Bool)
    (base : Strategy Variable Literal Symbol Certificate) : Strategy Variable Literal Symbol Certificate :=
  fun obligation store =>
    let response := base obligation store
    if response.alternatives.any Expansion.closes then response
    else
      match universalNegative? (store.resolve obligation.goal) with
      | some (binders, guards, operand) =>
          if witnessed (obligation.context.map store.resolve) (positiveWitness binders guards operand) then .candidates []
          else response
      | none => response

omit [DecidableEq Symbol] [DecidableEq Literal] in
/-- A defeat offers nothing, so the witness check keeps the base's soundness. -/
theorem Strategy.withWitness_sound {Certificate : Type} {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol}
    {witnessed : ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Bool}
    {base : Strategy Variable Literal Symbol Certificate} (baseSound : Strategy.Sound hoApplySymbol kb naf base) :
    Strategy.Sound hoApplySymbol kb naf (Strategy.withWitness witnessed base) := by
  intro obligation store valid declared expansion member
  unfold Strategy.withWitness at member
  dsimp only at member
  repeat' split at member
  all_goals first
    | exact baseSound obligation store valid declared expansion member
    | simp [Response.alternatives] at member

end Machine

namespace Semantics

variable {Variable Literal Symbol Value : Type} [DecidableEq Variable] {hoApplySymbol : Symbol}
  (model : Model Literal Symbol Value hoApplySymbol)

theorem Model.satisfies_implications (environment : Environment Variable Value)
    (guards : List (Term Variable Literal Symbol)) (body : Term Variable Literal Symbol) :
    model.Satisfies environment (guards.foldr .imp body) ↔
      ((∀ guard ∈ guards, model.Satisfies environment guard) → model.Satisfies environment body) := by
  induction guards with
  | nil => simp
  | cons guard rest ih =>
      simp only [List.foldr_cons, Model.Satisfies, Model.eval, model.holds_implication] at ih ⊢
      rw [ih]
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨fun holds both => holds both.1 both.2, fun holds first rest => holds ⟨first, rest⟩⟩

/-- A witness of `∃x̄. g₁ ∧ … ∧ gₙ ∧ G` makes `∀x̄. g₁ → … → gₙ → naf G` false. -/
theorem Model.defeats {guards : List (Term Variable Literal Symbol)} {operand : Term Variable Literal Symbol} :
    ∀ (binders : List Variable) {environment : Environment Variable Value},
      model.Satisfies environment (Machine.positiveWitness binders guards operand) →
        ¬ model.Satisfies environment (Machine.universalNegative binders guards operand)
  | [], environment, witness, negative => by
      simp only [Machine.positiveWitness, Machine.universalNegative, List.foldr_nil] at witness negative
      rw [model.satisfies_conjunction] at witness
      rw [model.satisfies_implications] at negative
      have refuted := negative fun guard inside => witness guard (List.mem_append_left _ inside)
      simp only [Model.Satisfies, Model.eval] at refuted
      exact model.defaultNegation_coherent _ refuted (witness operand (List.mem_append_right _ List.mem_cons_self))
  | binder :: binders, environment, witness, negative => by
      simp only [Machine.positiveWitness, Machine.universalNegative, List.foldr_cons, Model.Satisfies, Model.eval,
        model.holds_existential, model.holds_universal] at witness negative
      obtain ⟨value, witnessed⟩ := witness
      exact Model.defeats binders witnessed (negative value)

end Semantics

namespace P1

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal]
  [FreshNames Variable]

/-- A run from `goal` under `context`, its free names rigid, within `fuel`
steps, exported as a supplied proof. A run that is exhausted, unknown or
interrupted exports nothing. -/
def runExport (vocab : Vocabulary Symbol) (strategy : Strategy Variable Literal Symbol Unit) (fuel : Nat)
    (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    Option (Term Variable Literal Symbol) :=
  match run strategy fuel (State.init () [] context goal) with
  | .success proof _ => exportProof vocab (fun _ => .truth) proof
  | _ => none

/-- A refutation of `operand` under `context`: a run of the refutation search
`search` (`refuter`) on `operand → false`, exported. -/
def refute (vocab : Vocabulary Symbol) (search : Strategy Variable Literal Symbol Unit) (fuel : Nat)
    (context : ProofContext Variable Literal Symbol) (operand : Formula Variable Literal Symbol) :
    Option (Term Variable Literal Symbol) :=
  runExport vocab search fuel context (.imp operand .falsity)

/-- The witness query of a universal negative as a positive run in the
program within `fuel` steps; it is found when the run's export checks against
the snapshot as a proof of the query under the context. -/
def witnessSearch (vocab : Vocabulary Symbol) (snapshot : Snapshot Variable Literal Symbol)
    (program : Program Variable Literal Symbol) (select : Selection Variable Literal Symbol) (fuel : Nat)
    (context : ProofContext Variable Literal Symbol) (witness : Formula Variable Literal Symbol) : Bool :=
  (runExport vocab (left snapshot.hoApplySymbol program select) fuel context witness).any
    (snapshot.provesPositively vocab context witness)

/-- A witness found is a positive proof of the witness query in the snapshot. -/
theorem witnessSearch_derives {vocab : Vocabulary Symbol} {snapshot : Snapshot Variable Literal Symbol}
    {program : Program Variable Literal Symbol} {select : Selection Variable Literal Symbol} {fuel : Nat}
    {context : ProofContext Variable Literal Symbol} {witness : Formula Variable Literal Symbol}
    (found : witnessSearch vocab snapshot program select fuel context witness = true) :
    Derives snapshot.hoApplySymbol snapshot.kb context witness NafFailure.disabled := by
  unfold witnessSearch at found
  cases exported : runExport vocab (left snapshot.hoApplySymbol program select) fuel context witness with
  | none => simp [exported] at found
  | some term =>
      simp only [exported, Option.any_some] at found
      exact Snapshot.provesPositively_derives found

open Semantics in
/-- A witness found defeats the universal negative: it is false in every model
of the snapshot's KB satisfying the context. -/
theorem witnessSearch_defeats {vocab : Vocabulary Symbol} {snapshot : Snapshot Variable Literal Symbol}
    {program : Program Variable Literal Symbol} {select : Selection Variable Literal Symbol} {fuel : Nat}
    {context : ProofContext Variable Literal Symbol} {binders : List Variable}
    {guards : List (Formula Variable Literal Symbol)} {operand : Formula Variable Literal Symbol}
    (found : witnessSearch vocab snapshot program select fuel context (positiveWitness binders guards operand) = true)
    {Value : Type} (model : Model Literal Symbol Value snapshot.hoApplySymbol) (validKb : model.Models snapshot.kb)
    (environment : Environment Variable Value) (holds : model.ContextHolds environment context) :
    ¬ model.Satisfies environment (universalNegative binders guards operand) :=
  model.defeats binders (model.sound validKb (model.disabled_adequate _) (witnessSearch_derives found) environment holds)

/-- Evidence-first NAF over the left strategy on a completed program: a NAF
goal the left strategy cannot close is refuted in the same program, and the
refutation is checked against it. The completed clauses and the refutation
search are built once, not per refutation. -/
def nafByRefutation (vocab : Vocabulary Symbol) (hoApplySymbol : Symbol)
    (completion : Completion.Completed Variable Literal Symbol) (guard : Symbol → Bool)
    (select : Selection Variable Literal Symbol) (fuel : Nat) :
    Strategy Variable Literal Symbol (Term Variable Literal Symbol) :=
  let clauses := completion.clauses
  let search := refuter hoApplySymbol completion guard
  Strategy.withRefutation (refutationCheck vocab ⟨hoApplySymbol, clauses⟩).check (refute vocab search fuel)
    (left hoApplySymbol (Program.ofClauses clauses guard) select)

/-- Evidence-first NAF is sound for the completed program with refutation
evidence, so in every model of it with complement NAF (`refutation_adequate`). -/
theorem nafByRefutation_sound (vocab : Vocabulary Symbol) (hoApplySymbol : Symbol)
    (completion : Completion.Completed Variable Literal Symbol) (guard : Symbol → Bool)
    (select : Selection Variable Literal Symbol) (fuel : Nat) :
    Strategy.Sound hoApplySymbol (Snapshot.kb ⟨hoApplySymbol, completion.clauses⟩)
      (refutation hoApplySymbol (Snapshot.kb ⟨hoApplySymbol, completion.clauses⟩))
      (nafByRefutation vocab hoApplySymbol completion guard select fuel) := by
  have base := left_sound (Certificate := Term Variable Literal Symbol) (hoApplySymbol := hoApplySymbol)
    (naf := refutation hoApplySymbol (Snapshot.kb ⟨hoApplySymbol, completion.clauses⟩))
    (Program.ofClauses completion.clauses guard) select
  rw [Program.ofClauses_kb] at base
  exact Strategy.withRefutation_sound base (refutationCheck vocab ⟨hoApplySymbol, completion.clauses⟩).sound

end P1

end AnthillModKbSpec
