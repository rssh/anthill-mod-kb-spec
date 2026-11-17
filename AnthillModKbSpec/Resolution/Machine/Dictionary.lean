import AnthillModKbSpec.Resolution.Machine.Lemma

/-! # Dictionary operations on the machine (S14)

**Evaluation where the value is demanded.** An equation goal demands the
value of an operation term on one of its sides. `Strategy.withEvaluation`
answers it with the registered evaluator before any other strategy: a call
reading as a ground term the evaluator answers, with a ground value, is
matched against its evaluated equation `call = value`
(`Expansion.evaluation`): the S05 matcher compares the other side with the
value, binding a flexible name, closing an identical term, and missing a
different constructor term. A call on the right side is turned around first
(`Expansion.orient`, by `equalSymm`). Either comes with the goal's exact
candidates (an assumption it reads as, ex falso), and with no other: no law is
fired for a goal whose call is evaluated. Any other goal is the inner
strategy's.

The evaluation node is the derived rule `rule` with the call and the value as
its parameters and no premises; its contract is the clause rule on the
evaluated equation, so the strategy is sound in every KB containing the
evaluated equations (`Strategy.withEvaluation_sound`), the equation oracle's
extension (`DictionaryEvaluation`).

**Laws matched structurally.** A law is a checked lemma (S20), stated as a
conditional view `∀x̄. (B → H)` with an equation `H`. The S05 matcher compares
two different dictionary calls as `unsupported`: two different calls may have
the same value, so a mismatch beneath a call would be no refutation. A view is
therefore matched one way (`lawAttempt`): its binders are read off the goal as
read, structurally, the dictionary and the arguments as first-order terms of
the call with the same path and field (`extract`), a binder the conclusion does
not mention at a fresh flexible witness, and the instance must be identical to
the goal. No binder of the goal is assigned and no higher-order
unification is involved. The premise `B` is the one obligation, its
conjuncts proved in order; the goal closes once they succeed, and a failed
candidate is rolled back. `Strategy.withLaws` offers these candidates for an
equation goal with the call on the left, before the inner strategy's
(`Response.prepend`); a goal with the call on the right only is turned around.
It is sound where the lemmas are (`Strategy.withLaws_sound`). -/

namespace AnthillModKbSpec.Machine

variable {Variable Literal Symbol Certificate : Type}

namespace Expansion

/-- The evaluation of a call: the goal matched against the evaluated equation
`call = value`, a node of the derived rule `rule` with the call and the value
as its parameters, and no premises. -/
def evaluation (rule : Symbol) (call value : Term Variable Literal Symbol)
    (bindings : List (Variable × Term Variable Literal Symbol)) : Expansion Variable Literal Symbol Certificate :=
  { rule := .extension rule [call, value] none, bindings := bindings }

/-- An equation goal `left = right`, proved from `right = left`. -/
def orient (left right : Term Variable Literal Symbol) : Expansion Variable Literal Symbol Certificate :=
  { rule := .equalSymm, premises := [{ goal := .equal right left }] }

section Reading

variable [DecidableEq Variable] [FreshNames Variable] {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
  {naf : NafFailure Variable Literal Symbol} {scope : Scope Variable Literal Symbol}
  {store : Store Variable Literal Symbol}

/-- A goal matched against an evaluated equation is derived by the clause rule
on it. -/
theorem evaluation_soundUnder {rule : Symbol} {goal call value : Term Variable Literal Symbol}
    {bindings : List (Variable × Term Variable Literal Symbol)} (member : HornClause.equation call value [] ∈ kb)
    (closedCall : call.freeVars = []) (closedValue : value.freeVars = [])
    (matched : store.resolve goal = store.resolve (.equal call value)) :
    (evaluation (Certificate := Certificate) rule call value bindings).SoundUnder hoApplySymbol kb naf store
      ⟨scope, goal⟩ := fun _ => by
  simp only [ReadDerives, matched, Store.resolve_equal, Store.resolve_closed _ closedCall,
    Store.resolve_closed _ closedValue]
  exact Derives.equation member (Substitutes.identity _) (Substitutes.identity _) (Substitutes.identity _) .truth

theorem orient_soundUnder {goal left right : Term Variable Literal Symbol}
    (read : store.resolve goal = store.resolve (.equal left right)) :
    (orient (Certificate := Certificate) left right).SoundUnder hoApplySymbol kb naf store ⟨scope, goal⟩ :=
  fun proofs => by
    have turned := read_premise.mp (proofs { goal := .equal right left } (by simp [orient]))
    simp only [List.map_nil, List.nil_append, Store.resolve_equal] at turned
    simp only [ReadDerives, read, Store.resolve_equal]
    exact .equalSymm turned

end Reading

end Expansion

section Strategy

variable [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal] [FreshNames Variable]

/-- The value of a term the evaluator answers, when both are ground. -/
def evaluable (evaluator : Term Variable Literal Symbol → Option (Term Variable Literal Symbol))
    (term : Term Variable Literal Symbol) : Option (Term Variable Literal Symbol) :=
  if term.freeVars = [] then (evaluator term).filter fun value => value.freeVars = [] else none

omit [DecidableEq Symbol] [DecidableEq Literal] [FreshNames Variable] in
theorem evaluable_some {evaluator : Term Variable Literal Symbol → Option (Term Variable Literal Symbol)}
    {term value : Term Variable Literal Symbol} (found : evaluable evaluator term = some value) :
    evaluator term = some value ∧ term.freeVars = [] ∧ value.freeVars = [] := by
  unfold evaluable at found
  split at found
  · rename_i closed
    obtain ⟨evaluated, closedValue⟩ := Option.filter_eq_some_iff.mp found
    exact ⟨evaluated, closed, by simpa using closedValue⟩
  · cases found

/-- Evaluation first: an equation goal whose left side, as read, the evaluator
answers is matched against its evaluated equation; one whose right side it
answers is turned around. Either comes with the goal's exact candidates (an
assumption it reads as, ex falso, an exact step from a local rule), and with no
other: no law is fired. Any other goal is `inner`'s. -/
def Strategy.withEvaluation (hoApplySymbol : Symbol) (rule : Symbol)
    (evaluator : Term Variable Literal Symbol → Option (Term Variable Literal Symbol))
    (inner : Strategy Variable Literal Symbol Certificate) : Strategy Variable Literal Symbol Certificate :=
  fun obligation store =>
    match store.resolve obligation.goal with
    | .equal left right =>
        let exact := exactCandidates obligation (.equal left right) (store.readContext obligation)
        match evaluable evaluator left with
        | some value =>
            respond (attempt ((store.prepare obligation [] []).unify obligation.scope hoApplySymbol obligation.goal
              (.equal left value)) (fun bindings => Expansion.evaluation rule left value bindings) ::
                exact.map (some ∘ some))
        | none =>
            match evaluable evaluator right with
            | some _ => .candidates (Expansion.orient left right :: exact)
            | none => inner obligation store
    | _ => inner obligation store

/-- The strategy is sound in every KB containing the evaluated equations in
which the inner strategy is. -/
theorem Strategy.withEvaluation_sound {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol} {rule : Symbol}
    {evaluator : Term Variable Literal Symbol → Option (Term Variable Literal Symbol)}
    (certified : ∀ call value, evaluator call = some value → HornClause.equation call value [] ∈ kb)
    {inner : Strategy Variable Literal Symbol Certificate} (sound : Strategy.Sound hoApplySymbol kb naf inner) :
    Strategy.Sound hoApplySymbol kb naf (Strategy.withEvaluation hoApplySymbol rule evaluator inner) := by
  intro obligation store valid declared expansion member
  unfold Strategy.withEvaluation at member
  split at member
  · rename_i left right reads
    dsimp only at member
    split at member
    · rename_i value found
      obtain ⟨evaluated, closedCall, closedValue⟩ := evaluable_some found
      refine respond_sound (fun candidate inside => ?_) expansion member
      rcases List.mem_cons.mp inside with rfl | exact
      · exact attempt_sound valid (fun _ => ⟨rfl, by simp [Expansion.rigids, Expansion.evaluation], rfl⟩)
          fun _ _ matched => Expansion.evaluation_soundUnder (certified _ _ evaluated) closedCall closedValue matched
      · obtain ⟨exactExpansion, exactMember, rfl⟩ := List.mem_map.mp exact
        intro _ same
        cases same
        exact exactCandidates_sound reads _ exactMember
    · split at member
      · simp only [Response.alternatives] at member
        rcases List.mem_cons.mp member with rfl | exact
        · exact fixed_sound fun later refines => Expansion.orient_soundUnder (valid.read_refines reads refines)
        · exact exactCandidates_sound reads _ exact
      · exact sound obligation store valid declared expansion member
  · exact sound obligation store valid declared expansion member

/-! ### Laws matched structurally -/

/-- The operation a dictionary call applies: its path, field, and argument count. -/
def callShape : Term Variable Literal Symbol → Option (List Symbol × Symbol × Nat)
  | .dictionaryCall _ path field args => some (path, field, args.length)
  | _ => none

/-- The instance of a law view `∀x̄. (B → H)` concluding the goal: the binders
`H` mentions read off the goal by a one-way structural match of `H`, each other
binder at its fresh flexible name in `fresh`; the premise `B'` of the
instance, whose conclusion `H'` is identical to the goal; and the fresh names
used. -/
def lawInstance? (fresh : List Variable) (statement goal : Formula Variable Literal Symbol) :
    Option (List (Term Variable Literal Symbol) × Formula Variable Literal Symbol × List Variable) :=
  let binders := leadingBinders statement
  match stripLeading binders.length statement with
  | .imp _ conclusion =>
      (extract binders conclusion goal []).bind fun found =>
        let chosen := (binders.zip fresh).map fun (binder, name) =>
          match OperationDictionaries.lookup found binder with
          | some witness => (witness, none)
          | none => (.var name, some name)
        match statement.instantiateLeading (chosen.map Prod.fst) with
        | some (.imp premise instantiated) =>
            if identical instantiated goal then some (chosen.map Prod.fst, premise, chosen.filterMap Prod.snd) else none
        | _ => none
  | _ => none

theorem lawInstance?_spec {fresh : List Variable} {statement goal premise : Formula Variable Literal Symbol}
    {witnesses : List (Term Variable Literal Symbol)} {flexibles : List Variable}
    (found : lawInstance? fresh statement goal = some (witnesses, premise, flexibles)) :
    statement.instantiateLeading witnesses = some (.imp premise goal) := by
  unfold lawInstance? at found
  dsimp only at found
  split at found
  · simp only [Option.bind_eq_some_iff] at found
    obtain ⟨_, _, instantiated⟩ := found
    split at instantiated
    · rename_i computed
      split at instantiated
      · rename_i same
        cases instantiated
        rw [computed, identical_iff.mp same]
      · cases instantiated
    · cases instantiated
  · cases found

/-- The candidate of a law view for an equation goal, as read: its instance
concluding the goal (`lawInstance?`), at fresh flexible witnesses for the
binders the conclusion does not mention, then the use-site checks of S20: a gap
where the use site may still change, the candidate where the lemma holds, a
gap where it applies but does not hold, and a miss otherwise. -/
def lawAttempt (lemmas : Lemmas Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (goal : Term Variable Literal Symbol) (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol))
    (name : Symbol) (statement : Formula Variable Literal Symbol) : Attempt Variable Literal Symbol Certificate :=
  match lawInstance? (store.witnessesFor (readAvoid goal context) statement) statement goal with
  | some (witnesses, premise, flexibles) =>
      if store.lemmaSite context statement then
        if lemmas.holds (context.map Prod.snd) name statement then
          some (some (Expansion.lemmaRule name statement witnesses premise flexibles []))
        else if lemmas.applies (context.map Prod.snd) name statement then none
        else some none
      else none
  | none => some none

/-- Candidates offered before a response's own; a gap among them makes the
response incomplete. A delay, an open atom, or a NAF evaluation is passed on
unchanged. -/
def Response.prepend (extra : List (Attempt Variable Literal Symbol Certificate))
    (response : Response Variable Literal Symbol Certificate) : Response Variable Literal Symbol Certificate :=
  let found := extra.filterMap Option.join
  let gap := extra.any Option.isNone
  if extra.isEmpty then response
  else
    match response with
    | .candidates alternatives =>
        if gap then .incomplete (found ++ alternatives) [.unsupported] else .candidates (found ++ alternatives)
    | .incomplete alternatives reasons => .incomplete (found ++ alternatives) (if gap then .unsupported :: reasons else reasons)
    | .unsupported => .incomplete found [.unsupported]
    | response => response

/-- Laws for an equation goal on a dictionary call: on the left, the law
views first, then `inner`'s candidates; on the right only, the goal turned
around, after its exact candidates. Any other goal is `inner`'s. -/
def Strategy.withLaws (lemmas : Lemmas Variable Literal Symbol) (inner : Strategy Variable Literal Symbol Certificate) :
    Strategy Variable Literal Symbol Certificate := fun obligation store =>
  match store.resolve obligation.goal with
  | .equal left right =>
      if (callShape left).isSome then
        Response.prepend (lemmas.statements.map fun entry =>
            lawAttempt lemmas store (.equal left right) (store.readContext obligation) entry.1 entry.2)
          (inner obligation store)
      else if (callShape right).isSome then
        .candidates (Expansion.orient left right :: exactCandidates obligation (.equal left right) (store.readContext obligation))
      else inner obligation store
  | _ => inner obligation store

omit [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal] [FreshNames Variable] in
theorem Response.mem_prepend {extra : List (Attempt Variable Literal Symbol Certificate)}
    {response : Response Variable Literal Symbol Certificate} {expansion : Expansion Variable Literal Symbol Certificate}
    (member : expansion ∈ (Response.prepend extra response).alternatives) :
    expansion ∈ extra.filterMap Option.join ∨ expansion ∈ response.alternatives := by
  unfold Response.prepend at member
  dsimp only at member
  split at member
  · exact .inr member
  · cases response with
    | candidates alternatives =>
        simp only at member
        split at member <;> simpa [Response.alternatives] using member
    | incomplete alternatives reasons => simpa [Response.alternatives] using member
    | unsupported => exact .inl (by simpa [Response.alternatives] using member)
    | _ => exact .inr member

theorem lawAttempt_sound {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol} {lemmas : Lemmas Variable Literal Symbol}
    (sound : lemmas.Sound hoApplySymbol kb naf) {obligation : Obligation Variable Literal Symbol}
    {store : Store Variable Literal Symbol} (valid : store.Scoped) {name : Symbol}
    {statement : Formula Variable Literal Symbol} :
    AttemptSound hoApplySymbol kb naf store obligation
      (lawAttempt (Certificate := Certificate) lemmas store (store.resolve obligation.goal)
        (store.readContext obligation) name statement) := by
  unfold lawAttempt
  split
  · rename_i witnesses premise flexibles found
    split
    · rename_i site
      split
      · rename_i holds
        intro _ produced next woken committed later refines laterScoped
        cases produced
        have refined := (Store.commit_refines committed).trans refines
        exact Expansion.lemmaRule_soundUnder (sound.later valid site holds refined laterScoped)
          (lawInstance?_spec found) (valid.read_refines rfl refined).symm
      · split <;> intro _ found <;> cases found
    · intro _ found; cases found
  · intro _ found; cases found

/-- The law candidates are sound where the lemmas are, and the strategy where
the inner one is too. -/
theorem Strategy.withLaws_sound {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol} {lemmas : Lemmas Variable Literal Symbol}
    (lemmasSound : lemmas.Sound hoApplySymbol kb naf) {inner : Strategy Variable Literal Symbol Certificate}
    (sound : Strategy.Sound hoApplySymbol kb naf inner) :
    Strategy.Sound hoApplySymbol kb naf (Strategy.withLaws lemmas inner) := by
  intro obligation store valid declared expansion member
  unfold Strategy.withLaws at member
  split at member
  · rename_i left right reads
    split at member
    · rcases Response.mem_prepend member with offered | own
      · obtain ⟨candidate, inside, joined⟩ := List.mem_filterMap.mp offered
        obtain ⟨entry, _, rfl⟩ := List.mem_map.mp inside
        have attempt := lawAttempt_sound (Certificate := Certificate) lemmasSound (obligation := obligation) valid
          (name := entry.1) (statement := entry.2)
        rw [reads] at attempt
        exact attempt expansion (Option.join_eq_some_iff.mp joined)
      · exact sound obligation store valid declared expansion own
    · split at member
      · simp only [Response.alternatives] at member
        rcases List.mem_cons.mp member with rfl | exact
        · exact fixed_sound fun later refines => Expansion.orient_soundUnder (valid.read_refines reads refines)
        · exact exactCandidates_sound reads _ exact
      · exact sound obligation store valid declared expansion member
  · exact sound obligation store valid declared expansion member

end Strategy

end AnthillModKbSpec.Machine
