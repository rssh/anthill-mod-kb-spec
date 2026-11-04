import AnthillModKbSpec.Resolution.Machine.LeftStrategy
import AnthillModKbSpec.Resolution.Miller
import AnthillModKbSpec.Foundation.Completion

namespace AnthillModKbSpec.Machine

/-! # Refutation search in the completed program (S10)

NAF evidence by refutation is a proof of `G → false` in a completed program
(`Completion.Completed`). `refuter` searches for one on the shared machine,
scanning the completion without its clash clauses (`Completed.scanned`) and
using the dual rules of negation at falsity goals; other goals are the left
strategy's.

- **Inversion.** At a falsity goal, an assumed conjunction or existential is
  split first, once per branch, and committed to: the split is invertible and
  does not branch the search.
- **Joins.** Two assumed equations that, oriented, read `s = a` and `s = b`
  give `a = b` (`Expansion.equalJoin`), committed to: a join only adds a
  consequence, and adds no new terms, so a branch has finitely many.
- **Closing candidates** are `atomResponse`'s over the scanned clauses:
  identity, ex falso, and clauses concluding falsity, such as assumed `false`.
  The free equality theory closes a case whose head equations clash, through
  its generated clauses `false :- f(x̄) = g(ȳ)`. The search tries only the
  clash clause that matches an assumed equation, once per constructor pair
  (`clashPairs`, `clashAttempts`).
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

/-- An only-if clause `cases :- p(x̄)`: its cases, its predicate, and its head
names. -/
def onlyIfHead? : HornClause Variable Literal Symbol →
    Option (Formula Variable Literal Symbol × Symbol × List Variable)
  | .definite cases [.app symbol heads] => (heads.mapM Term.variableName?).map fun names => (cases, symbol, names)
  | _ => none

omit [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal] [FreshNames Variable] in
theorem onlyIfHead?_spec {clause : HornClause Variable Literal Symbol} {cases : Formula Variable Literal Symbol}
    {symbol : Symbol} {names : List Variable} (found : onlyIfHead? clause = some (cases, symbol, names)) :
    clause = .definite cases [.app symbol (names.map .var)] := by
  match clause, found with
  | .definite cases' [.app symbol' heads], found =>
      simp only [onlyIfHead?, Option.map_eq_some_iff, Prod.mk.injEq] at found
      obtain ⟨names', mapped, rfl, rfl, rfl⟩ := found
      rw [mapM_variableName? mapped]

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
  have continuation := Expansion.read_premise.mp (proofs _ List.mem_cons_self)
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

omit [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal] [FreshNames Variable] in
/-- An oriented equation is the equation it was oriented from. -/
theorem orient_eq_some {flip : Bool} {term shared side : Term Variable Literal Symbol}
    (oriented : orient flip term = some (shared, side)) :
    term = if flip then .equal side shared else .equal shared side := by
  cases term with
  | equal left right =>
      cases flip <;> simp only [orient, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at oriented ⊢ <;>
        obtain ⟨rfl, rfl⟩ := oriented <;> rfl
  | _ => simp [orient] at oriented

omit [DecidableEq Symbol] [DecidableEq Literal] [FreshNames Variable] in
theorem orient_derives {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol} {context : ProofContext Variable Literal Symbol} {flip : Bool}
    {read shared side : Term Variable Literal Symbol} (oriented : orient flip read = some (shared, side))
    (member : read ∈ context) : Derives hoApplySymbol kb context (.equal shared side) naf := by
  have equation := orient_eq_some oriented
  cases flip <;> simp only [Bool.false_eq_true, ↓reduceIte] at equation <;> subst equation
  · exact .assumption member
  · exact .equalSymm (.assumption member)

omit [DecidableEq Symbol] [DecidableEq Literal] in
/-- Orientation commutes with reading. -/
theorem orient_resolve (store : Store Variable Literal Symbol) {flip : Bool}
    {term shared side : Term Variable Literal Symbol} (oriented : orient flip term = some (shared, side)) :
    orient flip (store.resolve term) = some (store.resolve shared, store.resolve side) := by
  have equation := orient_eq_some oriented
  cases flip <;> simp only [Bool.false_eq_true, ↓reduceIte] at equation <;> subst equation <;> simp [orient]

/-- Two assumed equations, as read and oriented `s = a` and `s = b`: the goal
under `a = b`. -/
def Expansion.equalJoin (first second : Formula Variable Literal Symbol) (flipFirst flipSecond : Bool)
    (joined goal : Formula Variable Literal Symbol) : Expansion Variable Literal Symbol Certificate :=
  { rule := .derived (.equalJoin first second flipFirst flipSecond)
    premises := [{ discharge := { assumptions := [joined] }, goal := goal }] }

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
  have continuation := Expansion.read_premise.mp (proofs _ List.mem_cons_self)
  simp only [List.map_cons, List.map_nil, List.singleton_append, Store.resolve_equal] at continuation
  have left := orient_derives (hoApplySymbol := hoApplySymbol) (kb := kb) (naf := naf) (orient_resolve store firstOriented)
    (by rw [← firstReads]; exact List.mem_map_of_mem firstMember)
  have right := orient_derives (hoApplySymbol := hoApplySymbol) (kb := kb) (naf := naf) (orient_resolve store secondOriented)
    (by rw [← secondReads]; exact List.mem_map_of_mem secondMember)
  exact Derives.cut (.equalTrans (.equalSymm left) right) continuation

/-- A formula already assumed, as read. -/
def assumedIn (reads : List (Term Variable Literal Symbol)) (formula : Term Variable Literal Symbol) : Bool :=
  reads.any (identical formula)

/-- The first join at a falsity goal: a pair of assumed equations, as read,
with a shared side, oriented either way, unless the joined sides are identical
or their equation is already assumed either way. -/
def equalJoin? (obligation : Obligation Variable Literal Symbol) (reads : List (Term Variable Literal Symbol))
    (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    Option (Expansion Variable Literal Symbol Certificate) :=
  context.findSome? fun (first, firstRead) => context.findSome? fun (second, secondRead) =>
    [(false, false), (false, true), (true, false), (true, true)].findSome? fun (flipFirst, flipSecond) =>
      match orient flipFirst firstRead, orient flipSecond secondRead with
      | some (shared, a), some (other, b) =>
          if identical shared other = true ∧ identical a b = false ∧ assumedIn reads (.equal a b) = false ∧
              assumedIn reads (.equal b a) = false then
            some (Expansion.equalJoin first second flipFirst flipSecond (.equal a b) obligation.goal)
          else none
      | _, _ => none

theorem equalJoin?_sound {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol} {obligation : Obligation Variable Literal Symbol}
    {store : Store Variable Literal Symbol} (valid : store.Scoped) {reads : List (Term Variable Literal Symbol)}
    {expansion : Expansion Variable Literal Symbol Certificate}
    (found : equalJoin? obligation reads (store.readContext obligation) = some expansion) :
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
def inversion? (reads : List (Term Variable Literal Symbol))
    (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    Option (Choice Variable Literal Symbol) :=
  context.findSome? fun (assumption, read) =>
    match read with
    | .conj left right => if assumedIn reads left && assumedIn reads right then none else some (.conjUse assumption)
    | .existsVar binder body => if readsInstance [binder] body reads then none else some (.existsOpen assumption)
    | _ => none

/-- The first assumed disjunction not yet split on this branch, newest first: a
disjunction counts as split when a disjunct is assumed. -/
def disjunction? (reads : List (Term Variable Literal Symbol))
    (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    Option (Choice Variable Literal Symbol) :=
  context.findSome? fun (assumption, read) =>
    match read with
    | .disj left right => if assumedIn reads left || assumedIn reads right then none else some (.disjCases assumption)
    | _ => none

/-- One only-if use: an assumed atom `symbol(args)`, as read, with an only-if
clause of its predicate, unless its cases are already assumed. -/
def onlyIfAttempt (obligation : Obligation Variable Literal Symbol) (reads : List (Term Variable Literal Symbol))
    (symbol : Symbol) (args : List (Term Variable Literal Symbol)) (clause : HornClause Variable Literal Symbol) :
    Option (Expansion Variable Literal Symbol Certificate) :=
  match onlyIfHead? clause with
  | some (cases, closed, names) =>
      if closed = symbol ∧ names.length = args.length ∧ names.Nodup then
        let instantiated := onlyIfCases cases names args
        if assumedIn reads instantiated then none else some (Expansion.onlyIfUse clause instantiated args obligation.goal)
      else none
  | none => none

/-- The first only-if use at a falsity goal: an assumed atom, as read, newest
first, with one of the only-if clauses `onlyIfs`. -/
def onlyIfAttempt? (onlyIfs : List (HornClause Variable Literal Symbol)) (obligation : Obligation Variable Literal Symbol)
    (reads : List (Term Variable Literal Symbol)) (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    Option (Expansion Variable Literal Symbol Certificate) :=
  context.findSome? fun (_, read) =>
    match read with
    | .app symbol args => onlyIfs.findSome? (onlyIfAttempt obligation reads symbol args)
    | _ => none

/-- A program of the given clauses, keeping a program's guards. Clause sources
are read only by P0 admission, which completed programs do not enter. -/
def Program.ofClauses (clauses : List (HornClause Variable Literal Symbol)) (guard : Symbol → Bool) :
    Program Variable Literal Symbol :=
  ⟨clauses.map (⟨.signature, ·⟩), guard⟩

omit [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal] [FreshNames Variable] in
theorem Program.ofClauses_kb (clauses : List (HornClause Variable Literal Symbol)) (guard : Symbol → Bool) :
    (Program.ofClauses clauses guard).kb = fun clause => clause ∈ clauses := by
  funext clause
  simp only [Program.kb, Program.ofClauses, List.mem_map, eq_iff_iff]
  constructor
  · rintro ⟨_, ⟨_, member, rfl⟩, rfl⟩
    exact member
  · exact fun member => ⟨_, ⟨_, member, rfl⟩, rfl⟩

omit [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal] [FreshNames Variable] in
theorem Program.mem_ofClauses {clauses : List (HornClause Variable Literal Symbol)} {guard : Symbol → Bool}
    {clause : HornClause Variable Literal Symbol} (member : clause ∈ clauses) :
    ⟨.signature, clause⟩ ∈ (Program.ofClauses clauses guard).clauses :=
  List.mem_map.mpr ⟨clause, member, rfl⟩

/-- A committed step by a choice, if it applies. -/
def choiceAttempt (hoApplySymbol : Symbol) (program : Program Variable Literal Symbol)
    (obligation : Obligation Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol))
    (choice? : Option (Choice Variable Literal Symbol)) : Option (Expansion Variable Literal Symbol Certificate) :=
  choice?.bind fun choice => (choice.attempt hoApplySymbol program obligation store (readAvoid .falsity context)).join

/-- The constructor pairs of the assumed equations, as read, between terms
headed by distinct constructors of the completion, each pair once. -/
def clashPairs (constructors : List (Completion.Constructor Literal Symbol))
    (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    List (Completion.Constructor Literal Symbol × Completion.Constructor Literal Symbol) :=
  (context.filterMap fun (_, read) =>
    match read with
    | .equal left right =>
        match Completion.Constructor.of? left, Completion.Constructor.of? right with
        | some first, some second =>
            if first ∈ constructors ∧ second ∈ constructors ∧ first ≠ second then some (first, second) else none
        | _, _ => none
    | _ => none).eraseDups

omit [DecidableEq Variable] [FreshNames Variable] in
theorem mem_clashPairs {constructors : List (Completion.Constructor Literal Symbol)}
    {context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)}
    {first second : Completion.Constructor Literal Symbol} (member : (first, second) ∈ clashPairs constructors context) :
    first ∈ constructors ∧ second ∈ constructors ∧ first ≠ second := by
  obtain ⟨⟨_, read⟩, _, produced⟩ := List.mem_filterMap.mp (List.mem_eraseDups.mp member)
  dsimp only at produced
  split at produced
  · split at produced
    · split at produced
      · rename_i holds
        cases produced
        exact holds
      · cases produced
    · cases produced
  · cases produced

/-- The clash candidates at a falsity goal: the clash clause of each pair of
`clashPairs`, and no other. -/
def clashAttempts (hoApplySymbol : Symbol) (constructors : List (Completion.Constructor Literal Symbol))
    (obligation : Obligation Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    List (Attempt Variable Literal Symbol Certificate) :=
  let avoid := readAvoid .falsity context
  (clashPairs constructors context).map fun (first, second) =>
    clauseAttempt hoApplySymbol obligation store .falsity avoid ⟨.signature, Completion.clash first second⟩

/-- The one progress step at a falsity goal: the first only-if use, else the
newest disjunction split. -/
def progress (hoApplySymbol : Symbol) (program : Program Variable Literal Symbol)
    (onlyIfs : List (HornClause Variable Literal Symbol)) (obligation : Obligation Variable Literal Symbol)
    (store : Store Variable Literal Symbol) (reads : List (Term Variable Literal Symbol))
    (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    List (Attempt Variable Literal Symbol Certificate) :=
  match onlyIfAttempt? onlyIfs obligation reads context with
  | some use => [some (some use)]
  | none => (choiceAttempt hoApplySymbol program obligation store context (disjunction? reads context)).toList.map
      (some ∘ some)

/-- The refutation search in a completed program: the left strategy with no
selection, and at a falsity goal the dual rules of negation, in this order:

1. a conjunction or existential split, committed;
2. a join of assumed equations, committed: it only adds a consequence, and the
   joins of a branch are finitely many, since they add no new terms;
3. the closing candidates of the completion without its clash clauses
   (`Completed.scanned`), then the clash clause of each pair of distinct
   constructors an assumed equation has (`clashAttempts`), then one progress
   step: the first only-if use, else the newest disjunction split.

Other goals are the left strategy's on the same scanned clauses.

Only-if uses and splits only add consequences of the assumptions, so the
search takes one of them at a time and never tries them in another order; a
disjunction is split only when no only-if use is left. -/
def refuter (hoApplySymbol : Symbol) (completion : Completion.Completed Variable Literal Symbol) (guard : Symbol → Bool) :
    Strategy Variable Literal Symbol Certificate :=
  let full := Program.ofClauses completion.clauses guard
  let scanned := Program.ofClauses completion.scanned guard
  fun obligation store =>
    match store.resolve obligation.goal with
    | .falsity =>
        let context := store.readContext obligation
        let reads := context.map Prod.snd
        match choiceAttempt hoApplySymbol full obligation store context (inversion? reads context) with
        | some expansion => .candidates [expansion]
        | none =>
            match equalJoin? obligation reads context with
            | some join => .candidates [join]
            | none =>
                atomResponse hoApplySymbol scanned obligation store .falsity context true
                  (clashAttempts hoApplySymbol completion.constructors obligation store context ++
                    progress hoApplySymbol full completion.onlyIfs obligation store reads context)
    | _ => left hoApplySymbol scanned (fun _ _ _ _ => []) obligation store

theorem onlyIfAttempt?_sound {hoApplySymbol : Symbol} {naf : NafFailure Variable Literal Symbol}
    {kb : LogicalKb Variable Literal Symbol} {onlyIfs : List (HornClause Variable Literal Symbol)}
    (inKb : ∀ clause ∈ onlyIfs, kb clause) {obligation : Obligation Variable Literal Symbol}
    {store : Store Variable Literal Symbol} (valid : store.Scoped) {reads : List (Term Variable Literal Symbol)}
    {expansion : Expansion Variable Literal Symbol Certificate}
    (found : onlyIfAttempt? onlyIfs obligation reads (store.readContext obligation) = some expansion) :
    CandidateSound hoApplySymbol kb naf store obligation expansion := by
  obtain ⟨⟨assumption, read⟩, inside, produced⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨assumed, readEq⟩ := Store.mem_readContext inside
  dsimp only at produced
  cases read with
  | app symbol args =>
      obtain ⟨clause, clauseMember, produced⟩ := List.exists_of_findSome?_eq_some produced
      unfold onlyIfAttempt at produced
      split at produced
      · rename_i cases closed names headed
        split at produced
        · rename_i holds
          obtain ⟨sameSymbol, lengths, distinct⟩ := holds
          dsimp only at produced
          split at produced
          · cases produced
          · cases produced
            have clauseEq := onlyIfHead?_spec headed
            subst sameSymbol clauseEq
            refine fixed_sound fun _ refines => ?_
            have reads : store.resolve assumption = store.resolve (.app closed args) := by
              rw [readEq]; exact (valid.resolve_resolve assumption).symm
            exact Expansion.onlyIfUse_soundUnder assumed (refines.resolve_eq reads) (inKb _ clauseMember) distinct lengths
        · cases produced
      · cases produced
  | _ => simp at produced

theorem choiceAttempt_sound {hoApplySymbol : Symbol} {naf : NafFailure Variable Literal Symbol}
    {program : Program Variable Literal Symbol} {obligation : Obligation Variable Literal Symbol}
    {store : Store Variable Literal Symbol} (valid : store.Scoped) (declared : obligation.Declared store)
    {choice? : Option (Choice Variable Literal Symbol)} {expansion : Expansion Variable Literal Symbol Certificate}
    (found : choiceAttempt hoApplySymbol program obligation store (store.readContext obligation) choice? = some expansion) :
    CandidateSound hoApplySymbol program.kb naf store obligation expansion := by
  obtain ⟨choice, -, attempted⟩ := Option.bind_eq_some_iff.mp found
  exact Choice.attempt_sound valid declared choice expansion (Option.join_eq_some_iff.mp attempted)

/-- The refutation search is sound for the completed program, whatever the NAF
provider. -/
theorem refuter_sound {hoApplySymbol : Symbol} {naf : NafFailure Variable Literal Symbol}
    (completion : Completion.Completed Variable Literal Symbol) (guard : Symbol → Bool) :
    Strategy.Sound hoApplySymbol (Program.ofClauses completion.clauses guard).kb naf
      (refuter (Certificate := Certificate) hoApplySymbol completion guard) := by
  intro obligation store valid declared expansion member
  have within : ∀ entry ∈ (Program.ofClauses completion.scanned guard).clauses,
      entry ∈ (Program.ofClauses completion.clauses guard).clauses := fun entry inside => by
    simp only [Program.ofClauses, List.mem_map] at inside
    obtain ⟨clause, inside, rfl⟩ := inside
    exact Program.mem_ofClauses (Completion.Completed.mem_clauses_of_scanned inside)
  unfold refuter at member
  dsimp only at member
  split at member
  · rename_i readGoal
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
      · refine atomResponse_sound_within valid readGoal within (fun candidate added => ?_) expansion member
        rcases List.mem_append.mp added with fromClash | fromProgress
        · obtain ⟨⟨first, second⟩, inside, rfl⟩ := List.mem_map.mp fromClash
          obtain ⟨firstMember, secondMember, distinct⟩ := mem_clashPairs inside
          exact clauseAttempt_sound valid readGoal
            (Program.mem_ofClauses (Completion.Completed.clash_mem_clauses firstMember secondMember distinct))
        · unfold progress at fromProgress
          split at fromProgress
          · rename_i use found
            simp only [List.mem_singleton] at fromProgress
            subst fromProgress
            intro built same
            cases same
            exact onlyIfAttempt?_sound (fun clause inside => by
              rw [Program.ofClauses_kb]; exact Completion.Completed.mem_clauses_of_onlyIf inside) valid found
          · cases split : choiceAttempt (Certificate := Certificate) hoApplySymbol
                (Program.ofClauses completion.clauses guard) obligation store (store.readContext obligation)
                (disjunction? ((store.readContext obligation).map Prod.snd) (store.readContext obligation)) with
            | none => simp [split] at fromProgress
            | some built =>
                simp only [split, Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton,
                  Function.comp_apply] at fromProgress
                subst fromProgress
                intro expansion same
                cases same
                exact choiceAttempt_sound valid declared split
  · exact left_sound_within within _ (fun _ _ _ _ candidate inside => by simp [chosenAttempts] at inside)
      obligation store valid declared expansion member

end AnthillModKbSpec.Machine
