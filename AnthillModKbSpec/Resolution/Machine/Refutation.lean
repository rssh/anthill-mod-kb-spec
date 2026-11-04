import AnthillModKbSpec.Resolution.Machine.LeftStrategy
import AnthillModKbSpec.Resolution.Miller
import AnthillModKbSpec.Foundation.Completion

namespace AnthillModKbSpec.Machine

/-! # Refutation search in the completed program (S10)

NAF evidence by refutation is a proof of `G → false` in the completed program
(`Completion.completed`). `refuter` searches for one on the shared machine. It
is the left strategy with the dual rules of negation:

- **Inversion.** At a falsity goal, an assumed conjunction or existential is
  split first, once per branch, and committed to: the split is invertible and
  does not branch the search.
- **Joins.** Two assumed equations that, oriented, read `s = a` and `s = b`
  give `a = b` (`Expansion.equalJoin`), committed to: a join only adds a
  consequence, and adds no new terms, so a branch has finitely many.
- **Closing candidates** are `left`'s: assumed `false` closes a case, and the
  free equality theory closes a case whose head equations clash, through its
  generated clauses `false :- f(x̄) = g(ȳ)`, offered only for an assumed
  equation between an `f` and a `g` term (`clashRelevant`).
- **One progress step** after them: the first only-if use, replacing an
  assumed atom `p(s̄)` by its cases from `p`'s only-if clause `cases :- p(x̄)`
  (`Expansion.onlyIfUse`), once per atom; else the newest disjunction split.
  Each only adds consequences, so they are taken one at a time and never tried
  in another order, and an unrelated disjunction is split only when nothing
  else is left. Injectivity is not searched.

A rigid name in `G` is never given a value: the cases of `p(a)` keep the
equation `a = t`, and such a case is closed only if it is contradictory with `a`
arbitrary. The search may not terminate (recursive definitions unfold without
end); a run is bounded by its fuel, and an unfinished search is no evidence. -/

variable {Variable Literal Symbol Certificate : Type} [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal]
  [FreshNames Variable]

attribute [local instance] termEq clauseEq

/-! ## The only-if command -/

omit [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal] [FreshNames Variable] in
/-- Arguments that are all bare variables are those variables. -/
theorem mapM_variableName? : ∀ {args : List (Term Variable Literal Symbol)} {names : List Variable},
    args.mapM Term.variableName? = some names → args = names.map .var
  | [], names, found => by simp only [List.mapM_nil, pure, Option.some.injEq] at found; subst found; rfl
  | arg :: rest, names, found => by
      cases arg with
      | var name =>
          cases rested : rest.mapM Term.variableName? with
          | none => simp [List.mapM_cons, Term.variableName?, rested] at found
          | some tail =>
              simp only [List.mapM_cons, Term.variableName?, rested, Option.bind_eq_bind, Option.bind_some, pure,
                Option.some.injEq] at found
              subst found
              simp [mapM_variableName? rested]
      | _ => simp [List.mapM_cons, Term.variableName?] at found

/-- An assumed atom with the only-if clause of its predicate: the goal under
the atom's cases. The clause's head names are bound to the atom's arguments as
read. -/
def Expansion.onlyIfUse (clause : HornClause Variable Literal Symbol) (cases : Formula Variable Literal Symbol)
    (args : List (Term Variable Literal Symbol)) (goal : Formula Variable Literal Symbol) :
    Expansion Variable Literal Symbol Certificate :=
  { rule := .derived (.onlyIfUse clause args)
    premises := [{ discharge := { assumptions := [cases] }, goal := goal }] }

/-- The cases of an atom by an only-if clause, the head names at the atom's
arguments. -/
def onlyIfCases (cases : Formula Variable Literal Symbol) (names : List Variable)
    (args : List (Term Variable Literal Symbol)) : Formula Variable Literal Symbol :=
  cases.instantiate (Substitution.ofPairs (names.zip args))

omit [DecidableEq Symbol] [DecidableEq Literal] in
/-- The only-if contract: the atom is an assumption, read as `p(s̄)`, and the
clause is in the KB; the cases follow by the clause and are discharged from the
continuation by a cut. -/
theorem Expansion.onlyIfUse_soundUnder {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol} {store : Store Variable Literal Symbol} {scope : Scope Variable Literal Symbol}
    {assumption cases goal : Formula Variable Literal Symbol} {symbol : Symbol} {names : List Variable}
    {args : List (Term Variable Literal Symbol)} (member : assumption ∈ scope.assumptions)
    (reads : store.resolve assumption = store.resolve (.app symbol args))
    (clause : HornClause.definite cases [.app symbol (names.map .var)] ∈ kb) (distinct : names.Nodup)
    (lengths : names.length = args.length) :
    (Expansion.onlyIfUse (Certificate := Certificate) (.definite cases [.app symbol (names.map .var)])
      (onlyIfCases cases names args) args goal).SoundUnder hoApplySymbol kb naf store ⟨scope, goal⟩ := fun proofs => by
  have continuation := (show ReadDerives hoApplySymbol kb naf store
      (Obligation.premise ⟨scope, goal⟩ { discharge := { assumptions := [onlyIfCases cases names args] }, goal := goal })
      from proofs _ (by simp [Expansion.onlyIfUse]))
  simp only [ReadDerives, Obligation.premise_context, List.map_cons, List.singleton_append] at continuation
  have bodyInstance := store.resolve_substitutes
    ((Term.conjunction [Term.app symbol (names.map Term.var)]).instantiate_substitutes
      (Substitution.ofPairs (names.zip args)))
  have body : (Term.conjunction [Term.app symbol (names.map Term.var)]).instantiate (Substitution.ofPairs (names.zip args)) =
      .conj (.app symbol args) .truth := by
    simp only [Term.conjunction, List.foldr_cons, List.foldr_nil, Term.instantiate, List.map_map]
    congr
    simpa [Function.comp_def, Term.instantiate] using Substitution.ofPairs_zip distinct lengths
  rw [body] at bodyInstance
  have established : Derives hoApplySymbol kb (scope.assumptions.map store.resolve)
      (store.resolve (.conj (.app symbol args) .truth)) naf := by
    rw [Store.resolve_conj, Store.resolve_truth, ← reads]
    exact .conjIntro (.assumption (List.mem_map_of_mem member)) .truth
  exact Derives.cut (.clause clause (store.resolve_substitutes (cases.instantiate_substitutes _)) bodyInstance established)
    continuation

/-! ## Equations -/

/-- An equation `s = t` as `(s, t)`, or as `(t, s)` when flipped. -/
def orient (flip : Bool) : Term Variable Literal Symbol → Option (Term Variable Literal Symbol × Term Variable Literal Symbol)
  | .equal left right => some (if flip then (right, left) else (left, right))
  | _ => none

/-- Two assumed equations, as read and oriented `s = a` and `s = b`: the goal
under `a = b`. -/
def Expansion.equalJoin (first second : Formula Variable Literal Symbol) (flipFirst flipSecond : Bool)
    (joined goal : Formula Variable Literal Symbol) : Expansion Variable Literal Symbol Certificate :=
  { rule := .derived (.equalJoin first second flipFirst flipSecond)
    premises := [{ discharge := { assumptions := [joined] }, goal := goal }] }

omit [DecidableEq Symbol] [DecidableEq Literal] [FreshNames Variable] in
theorem orient_derives {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol} {context : ProofContext Variable Literal Symbol} {flip : Bool}
    {read shared side : Term Variable Literal Symbol} (oriented : orient flip read = some (shared, side))
    (member : read ∈ context) : Derives hoApplySymbol kb context (.equal shared side) naf := by
  cases read with
  | equal left right =>
      cases flip
      · simp only [orient, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at oriented
        obtain ⟨rfl, rfl⟩ := oriented
        exact .assumption member
      · simp only [orient, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at oriented
        obtain ⟨rfl, rfl⟩ := oriented
        exact .equalSymm (.assumption member)
  | _ => simp [orient] at oriented

omit [DecidableEq Symbol] [DecidableEq Literal] in
/-- Orientation commutes with reading. -/
theorem orient_resolve (store : Store Variable Literal Symbol) {flip : Bool}
    {term shared side : Term Variable Literal Symbol} (oriented : orient flip term = some (shared, side)) :
    orient flip (store.resolve term) = some (store.resolve shared, store.resolve side) := by
  cases term with
  | equal left right =>
      cases flip
      · simp only [orient, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at oriented
        obtain ⟨rfl, rfl⟩ := oriented
        simp [orient]
      · simp only [orient, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at oriented
        obtain ⟨rfl, rfl⟩ := oriented
        simp [orient]
  | _ => simp [orient] at oriented

omit [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal] [FreshNames Variable] in
theorem orient_equal {flip : Bool} {term shared side : Term Variable Literal Symbol}
    (oriented : orient flip term = some (shared, side)) : ∃ left right, term = .equal left right := by
  cases term with
  | equal left right => exact ⟨left, right, rfl⟩
  | _ => simp [orient] at oriented

omit [DecidableEq Symbol] [DecidableEq Literal] in
/-- The join contract: both equations are assumptions, read as equations that,
oriented, share a side; `a = b` follows by symmetry and transitivity and is
discharged from the continuation by a cut. -/
theorem Expansion.equalJoin_soundUnder {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol} {store : Store Variable Literal Symbol}
    {scope : Scope Variable Literal Symbol} {first second goal firstEquation secondEquation : Formula Variable Literal Symbol}
    {flipFirst flipSecond : Bool} {shared a b : Term Variable Literal Symbol}
    (firstMember : first ∈ scope.assumptions) (secondMember : second ∈ scope.assumptions)
    (firstReads : store.resolve first = store.resolve firstEquation)
    (secondReads : store.resolve second = store.resolve secondEquation)
    (firstOriented : orient flipFirst firstEquation = some (shared, a))
    (secondOriented : orient flipSecond secondEquation = some (shared, b)) :
    (Expansion.equalJoin (Certificate := Certificate) first second flipFirst flipSecond (.equal a b) goal).SoundUnder
      hoApplySymbol kb naf store ⟨scope, goal⟩ := fun proofs => by
  have continuation := (show ReadDerives hoApplySymbol kb naf store
      (Obligation.premise ⟨scope, goal⟩ { discharge := { assumptions := [.equal a b] }, goal := goal })
      from proofs _ (by simp [Expansion.equalJoin]))
  simp only [ReadDerives, Obligation.premise_context, List.map_cons, List.singleton_append] at continuation
  rw [Store.resolve_equal] at continuation
  have left := orient_derives (hoApplySymbol := hoApplySymbol) (kb := kb) (naf := naf) (orient_resolve store firstOriented)
    (by rw [← firstReads]; exact List.mem_map_of_mem firstMember)
  have right := orient_derives (hoApplySymbol := hoApplySymbol) (kb := kb) (naf := naf) (orient_resolve store secondOriented)
    (by rw [← secondReads]; exact List.mem_map_of_mem secondMember)
  exact Derives.cut (.equalTrans (.equalSymm left) right) continuation

/-- The first join at a falsity goal: a pair of assumed equations, as read,
with a shared side, oriented either way, unless the joined sides are identical
or their equation is already assumed either way. -/
def equalJoin? (obligation : Obligation Variable Literal Symbol)
    (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    Option (Expansion Variable Literal Symbol Certificate) :=
  let present := fun formula => (context.map Prod.snd).any (identical formula)
  context.findSome? fun (first, firstRead) => context.findSome? fun (second, secondRead) =>
    [(false, false), (false, true), (true, false), (true, true)].findSome? fun (flipFirst, flipSecond) =>
      match orient flipFirst firstRead, orient flipSecond secondRead with
      | some (shared, a), some (other, b) =>
          if identical shared other = true ∧ identical a b = false ∧ present (.equal a b) = false ∧
              present (.equal b a) = false then
            some (Expansion.equalJoin first second flipFirst flipSecond (.equal a b) obligation.goal)
          else none
      | _, _ => none

theorem equalJoin?_sound {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol} {obligation : Obligation Variable Literal Symbol}
    {store : Store Variable Literal Symbol} (valid : store.Scoped) {expansion : Expansion Variable Literal Symbol Certificate}
    (found : equalJoin? obligation (store.readContext obligation) = some expansion) :
    CandidateSound hoApplySymbol kb naf store obligation expansion := by
  obtain ⟨⟨first, firstRead⟩, firstInside, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨⟨second, secondRead⟩, secondInside, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨firstMember, firstEq⟩ := Store.mem_readContext firstInside
  obtain ⟨secondMember, secondEq⟩ := Store.mem_readContext secondInside
  obtain ⟨⟨flipFirst, flipSecond⟩, _, produced⟩ := List.exists_of_findSome?_eq_some found
  dsimp only at produced
  split at produced
  · rename_i shared a other b firstOriented secondOriented
    split at produced
    · rename_i holds
      cases produced
      obtain ⟨sameSide, _⟩ := holds
      rw [identical_iff] at sameSide
      subst sameSide
      refine fixed_sound fun _ refines => ?_
      exact Expansion.equalJoin_soundUnder firstMember secondMember (valid.read_refines firstEq.symm refines)
        (valid.read_refines secondEq.symm refines) firstOriented secondOriented
    · cases produced
  · cases produced

/-! ## The refutation strategy -/

/-- Some reading holds an instance of `pattern` over `binders`. -/
def readsInstance (binders : List Variable) (pattern : Term Variable Literal Symbol)
    (reads : List (Term Variable Literal Symbol)) : Bool :=
  reads.any fun read => (extract binders pattern read []).isSome

/-- Eager inversion: the first assumed conjunction or existential not yet split
on this branch. A conjunction counts as split when both components are
assumed, an existential when an instance of its body is. Neither branches the
search. -/
def inversion? (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    Option (Choice Variable Literal Symbol) :=
  let reads := context.map Prod.snd
  let present := fun formula => reads.any (identical formula)
  context.findSome? fun (assumption, read) =>
    match read with
    | .conj left right => if present left && present right then none else some (.conjUse assumption)
    | .existsVar binder body => if readsInstance [binder] body reads then none else some (.existsOpen assumption)
    | _ => none

/-- The first assumed disjunction not yet split on this branch, newest first: a
disjunction counts as split when a disjunct is assumed. -/
def disjunction? (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    Option (Choice Variable Literal Symbol) :=
  let present := fun formula => (context.map Prod.snd).any (identical formula)
  context.findSome? fun (assumption, read) =>
    match read with
    | .disj left right => if present left || present right then none else some (.disjCases assumption)
    | _ => none

/-- One only-if use: the assumed atom `symbol(args)`, as read, with an only-if
clause of its predicate, unless its cases are already assumed. -/
def onlyIfAttempt (program : Program Variable Literal Symbol) (obligation : Obligation Variable Literal Symbol)
    (reads : List (Term Variable Literal Symbol)) (assumption : Formula Variable Literal Symbol) (symbol : Symbol)
    (args : List (Term Variable Literal Symbol)) :
    HornClause Variable Literal Symbol → Option (Expansion Variable Literal Symbol Certificate)
  | .definite cases [.app closed heads] =>
      match heads.mapM Term.variableName? with
      | some names =>
          if closed = symbol ∧ names.Nodup ∧ names.length = args.length ∧ assumption ∈ obligation.scope.assumptions ∧
              program.has (.definite cases [.app closed heads]) = true ∧
              ¬ reads.any (identical (onlyIfCases cases names args)) = true then
            some (Expansion.onlyIfUse (.definite cases [.app closed heads]) (onlyIfCases cases names args) args
              obligation.goal)
          else none
      | none => none
  | _ => none

/-- The first only-if use at a falsity goal: an assumed atom, as read, newest
first, with an only-if clause of its predicate. -/
def onlyIfAttempt? (program : Program Variable Literal Symbol) (onlyIfs : List (HornClause Variable Literal Symbol))
    (obligation : Obligation Variable Literal Symbol) (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    Option (Expansion Variable Literal Symbol Certificate) :=
  context.findSome? fun (assumption, read) =>
    match read with
    | .app symbol args => onlyIfs.findSome? (onlyIfAttempt program obligation (context.map Prod.snd) assumption symbol args)
    | _ => none

/-- Append candidates to a response, keeping its kind; an unsupported response
with candidates is incomplete. -/
def Response.append : Response Variable Literal Symbol Certificate → List (Expansion Variable Literal Symbol Certificate) →
    Response Variable Literal Symbol Certificate
  | .candidates first, extra => .candidates (first ++ extra)
  | .incomplete first, extra => .incomplete (first ++ extra)
  | .unsupported, [] => .unsupported
  | .unsupported, extra => .incomplete extra
  | response, _ => response

omit [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal] [FreshNames Variable] in
theorem Response.mem_append {response : Response Variable Literal Symbol Certificate}
    {extra : List (Expansion Variable Literal Symbol Certificate)} {expansion : Expansion Variable Literal Symbol Certificate}
    (member : expansion ∈ (response.append extra).alternatives) : expansion ∈ response.alternatives ∨ expansion ∈ extra := by
  cases response <;> cases extra <;>
    simp_all [Response.append, Response.alternatives, List.mem_append]

/-- Keep the candidates of a response that pass `keep`, keeping its kind. -/
def Response.keep (keep : Expansion Variable Literal Symbol Certificate → Bool) :
    Response Variable Literal Symbol Certificate → Response Variable Literal Symbol Certificate
  | .candidates alternatives => .candidates (alternatives.filter keep)
  | .incomplete alternatives => .incomplete (alternatives.filter keep)
  | response => response

omit [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal] [FreshNames Variable] in
theorem Response.mem_keep {keep : Expansion Variable Literal Symbol Certificate → Bool}
    {response : Response Variable Literal Symbol Certificate} {expansion : Expansion Variable Literal Symbol Certificate}
    (member : expansion ∈ (response.keep keep).alternatives) : expansion ∈ response.alternatives := by
  cases response <;> simp_all [Response.keep, Response.alternatives, List.mem_filter]

/-- The same constructor at the head of two data terms: the same literal, or
the same symbol and arity (`sameHead`). -/
def sameConstructor : Term Variable Literal Symbol → Term Variable Literal Symbol → Bool
  | .lit first, .lit second => decide (first = second)
  | first, second => sameHead first second

/-- A clash clause `false :- f(x̄) = g(ȳ)` is worth trying only for an assumed
equation, as read, between an `f` term and a `g` term; other candidates are
kept. -/
def clashRelevant (clashes : List (HornClause Variable Literal Symbol)) (reads : List (Term Variable Literal Symbol))
    (expansion : Expansion Variable Literal Symbol Certificate) : Bool :=
  match expansion.rule with
  | .goalClause clause@(.goal [.equal left right]) _ =>
      !clashes.contains clause || reads.any fun read =>
        match read with
        | .equal first second => sameConstructor left first && sameConstructor right second
        | _ => false
  | _ => true

/-- A committed step by a choice, if it applies. -/
def choiceAttempt (hoApplySymbol : Symbol) (program : Program Variable Literal Symbol)
    (obligation : Obligation Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    Option (Choice Variable Literal Symbol) → Option (Expansion Variable Literal Symbol Certificate)
  | some choice =>
      match choice.attempt hoApplySymbol program obligation store (readAvoid .falsity context) with
      | some (some expansion) => some expansion
      | _ => none
  | none => none

/-- The refutation search: the left strategy with no selection, and at a
falsity goal the dual rules of negation, in this order:

1. a conjunction or existential split, committed;
2. a join of assumed equations, committed: it only adds a consequence, and the
   joins of a branch are finitely many, since they add no new terms;
3. the left strategy's candidates, its clash clauses only for an assumed
   equation with their constructor pair (`clashRelevant`), and after them one
   progress step: the first only-if use, else the newest disjunction split.

Only-if uses and splits only add consequences of the assumptions, so the
search takes one of them at a time and never tries them in another order; a
disjunction is split only when no only-if use is left. -/
def refuter (hoApplySymbol : Symbol) (program : Program Variable Literal Symbol)
    (onlyIfs clashes : List (HornClause Variable Literal Symbol)) : Strategy Variable Literal Symbol Certificate :=
  fun obligation store =>
    match store.resolve obligation.goal with
    | .falsity =>
        let context := store.readContext obligation
        match choiceAttempt hoApplySymbol program obligation store context (inversion? context) with
        | some expansion => .candidates [expansion]
        | none =>
            match equalJoin? obligation context with
            | some join => .candidates [join]
            | none =>
                let progress : Option (Expansion Variable Literal Symbol Certificate) :=
                  match onlyIfAttempt? program onlyIfs obligation context with
                  | some use => some use
                  | none => choiceAttempt hoApplySymbol program obligation store context (disjunction? context)
                ((left hoApplySymbol program (fun _ _ _ _ => []) obligation store).keep
                  (clashRelevant clashes (context.map Prod.snd))).append progress.toList
    | _ => left hoApplySymbol program (fun _ _ _ _ => []) obligation store

theorem onlyIfAttempt?_sound {hoApplySymbol : Symbol} {naf : NafFailure Variable Literal Symbol}
    {program : Program Variable Literal Symbol} {onlyIfs : List (HornClause Variable Literal Symbol)}
    {obligation : Obligation Variable Literal Symbol} {store : Store Variable Literal Symbol} (valid : store.Scoped)
    {expansion : Expansion Variable Literal Symbol Certificate}
    (found : onlyIfAttempt? program onlyIfs obligation (store.readContext obligation) = some expansion) :
    CandidateSound hoApplySymbol program.kb naf store obligation expansion := by
  obtain ⟨⟨assumption, read⟩, inside, produced⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨_, readEq⟩ := Store.mem_readContext inside
  dsimp only at produced
  cases read with
  | app symbol args =>
      obtain ⟨clause, _, produced⟩ := List.exists_of_findSome?_eq_some produced
      unfold onlyIfAttempt at produced
      split at produced
      · rename_i cases closed heads _
        cases mapped : heads.mapM Term.variableName? with
        | none => simp [mapped] at produced
        | some names =>
            simp only [mapped] at produced
            split at produced
            · rename_i holds
              obtain ⟨sameSymbol, distinct, lengths, assumed, has, _⟩ := holds
              cases produced
              have headsEq := mapM_variableName? mapped
              subst sameSymbol headsEq
              refine fixed_sound fun _ refines => ?_
              have reads : store.resolve assumption = store.resolve (.app closed args) := by
                rw [readEq]; exact (valid.resolve_resolve assumption).symm
              exact Expansion.onlyIfUse_soundUnder assumed (refines.resolve_eq reads) (Program.has_kb has) distinct lengths
            · cases produced
      · cases produced
  | _ => simp at produced

theorem choiceAttempt_sound {hoApplySymbol : Symbol} {naf : NafFailure Variable Literal Symbol}
    {program : Program Variable Literal Symbol} {obligation : Obligation Variable Literal Symbol}
    {store : Store Variable Literal Symbol} (valid : store.Scoped) (declared : obligation.Declared store)
    {choice? : Option (Choice Variable Literal Symbol)} {expansion : Expansion Variable Literal Symbol Certificate}
    (found : choiceAttempt hoApplySymbol program obligation store (store.readContext obligation) choice? = some expansion) :
    CandidateSound hoApplySymbol program.kb naf store obligation expansion := by
  cases choice? with
  | none => simp [choiceAttempt] at found
  | some choice =>
      unfold choiceAttempt at found
      cases attempted : choice.attempt (Certificate := Certificate) hoApplySymbol program obligation store
          (readAvoid .falsity (store.readContext obligation)) with
      | none => simp [attempted] at found
      | some inner =>
          cases inner with
          | none => simp [attempted] at found
          | some built =>
              simp only [attempted, Option.some.injEq] at found
              subst found
              exact Choice.attempt_sound valid declared choice _ attempted

/-- The refutation search is sound for its program's KB, whatever the NAF
provider. -/
theorem refuter_sound {hoApplySymbol : Symbol} {naf : NafFailure Variable Literal Symbol}
    (program : Program Variable Literal Symbol) (onlyIfs clashes : List (HornClause Variable Literal Symbol)) :
    Strategy.Sound hoApplySymbol program.kb naf
      (refuter (Certificate := Certificate) hoApplySymbol program onlyIfs clashes) := by
  intro obligation store valid declared expansion member
  have base := left_sound (Certificate := Certificate) (hoApplySymbol := hoApplySymbol) (naf := naf) program
    (fun _ _ _ _ => []) obligation store valid declared
  unfold refuter at member
  split at member
  · dsimp only at member
    split at member
    · rename_i built found
      simp only [Response.alternatives, List.mem_singleton] at member
      subst member
      exact choiceAttempt_sound valid declared found
    · split at member
      · rename_i join found
        simp only [Response.alternatives, List.mem_singleton] at member
        subst member
        exact equalJoin?_sound valid found
      · rcases Response.mem_append member with fromBase | fromProgress
        · exact base expansion (Response.mem_keep fromBase)
        · split at fromProgress
          · rename_i use found
            simp only [Option.toList_some, List.mem_singleton] at fromProgress
            subst fromProgress
            exact onlyIfAttempt?_sound valid found
          · cases split : choiceAttempt (Certificate := Certificate) hoApplySymbol program obligation store
                (store.readContext obligation) (disjunction? (store.readContext obligation)) with
            | none => simp [split] at fromProgress
            | some built =>
                simp only [split, Option.toList_some, List.mem_singleton] at fromProgress
                subst fromProgress
                exact choiceAttempt_sound valid declared split
  · exact base expansion member

end AnthillModKbSpec.Machine
