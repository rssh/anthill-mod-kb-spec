import AnthillModKbSpec.Resolution.Machine.Instantiation

namespace AnthillModKbSpec.Machine

open OperationDictionaries (lookup)

/-! # Matching against the store

The initial profile matches resolved terms syntactically. A flexible name that
is still unbound may be bound, through `Store.bind`, so the occurs check, the
dependency check, and alias narrowing apply to every binding a match makes.
Rigid names are constants. Two binders of the same kind are compared only when
identical, operation calls only when identical, and an `ho_apply` application
is never compared with an ordinary one. Those comparisons are capabilities the
profile does not admit, reported as `unsupported`: alpha-equivalence and
evaluation are not syntactic clashes, and `ho_apply` conversion is S11's. -/

variable {Variable Literal Symbol : Type}

/-- Outcome of matching two terms. `mismatch` is a candidate miss: a constructor
or rigid-name clash, or a binding the store rejects (occurs check, dependency).
It is never negative evidence about a goal. `unsupported` is a comparison the
initial profile does not admit. `violated` means an input names something the
store does not allow here (an undeclared name, or a rigid name outside the
scope): a breach of the machine's contract. -/
inductive Unification (Variable Literal Symbol : Type) where
  | unified (store : Store Variable Literal Symbol) (bindings : List (Variable × Term Variable Literal Symbol))
  | mismatch
  | unsupported
  | violated

/-- One step on the first pending pair. -/
inductive MatchStep (Variable Literal Symbol : Type) where
  | drop
  | bind (name : Variable) (value : Term Variable Literal Symbol)
  | split (pairs : List (Term Variable Literal Symbol × Term Variable Literal Symbol))
  | mismatch
  | unsupported

/-- Total size of the pending pairs; splitting a pair decreases it. -/
noncomputable def pairsSize : List (Term Variable Literal Symbol × Term Variable Literal Symbol) → Nat
  | [] => 0
  | (left, right) :: rest => sizeOf left + sizeOf right + pairsSize rest

theorem pairsSize_append (first second : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    pairsSize (first ++ second) = pairsSize first + pairsSize second := by
  induction first with
  | nil => simp [pairsSize]
  | cons pair rest ih => obtain ⟨left, right⟩ := pair; simp only [List.cons_append, pairsSize, ih]; omega

theorem term_sizeOf_pos (term : Term Variable Literal Symbol) : 0 < sizeOf term := by
  cases term <;> simp <;> omega

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

mutual
/-- Syntactic identity. -/
def identical : Term Variable Literal Symbol → Term Variable Literal Symbol → Bool
  | .var x, .var y => decide (x = y)
  | .lit x, .lit y => decide (x = y)
  | .app f xs, .app g ys => decide (f = g) && identicalArgs xs ys
  | .truth, .truth => true
  | .falsity, .falsity => true
  | .conj a b, .conj c d => identical a c && identical b d
  | .disj a b, .disj c d => identical a c && identical b d
  | .imp a b, .imp c d => identical a c && identical b d
  | .equal a b, .equal c d => identical a c && identical b d
  | .defaultNeg a, .defaultNeg b => identical a b
  | .forallVar x a, .forallVar y b => decide (x = y) && identical a b
  | .existsVar x a, .existsVar y b => decide (x = y) && identical a b
  | .dictionaryCall d p o xs, .dictionaryCall e q r ys =>
      identical d e && decide (p = q) && decide (o = r) && identicalArgs xs ys
  | _, _ => false

def identicalArgs : List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) → Bool
  | [], [] => true
  | x :: xs, y :: ys => identical x y && identicalArgs xs ys
  | _, _ => false
end

theorem identical_eq (left : Term Variable Literal Symbol) :
    ∀ right, identical left right = true → left = right := by
  refine Term.rec
    (motive_1 := fun left => ∀ right, identical left right = true → left = right)
    (motive_2 := fun lefts => ∀ rights, identicalArgs lefts rights = true → lefts = rights)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ left
  · intro x right same
    cases right <;> first | exact absurd same Bool.false_ne_true | rw [of_decide_eq_true same]
  · intro x right same
    cases right <;> first | exact absurd same Bool.false_ne_true | rw [of_decide_eq_true same]
  · intro f xs ih right same
    cases right <;> first | exact absurd same Bool.false_ne_true | skip
    obtain ⟨first, rest⟩ := Bool.and_eq_true_iff.mp same
    rw [of_decide_eq_true first, ih _ rest]
  · intro right same; cases right <;> first | exact absurd same Bool.false_ne_true | rfl
  · intro right same; cases right <;> first | exact absurd same Bool.false_ne_true | rfl
  · intro a b ihA ihB right same
    cases right <;> first | exact absurd same Bool.false_ne_true | skip
    obtain ⟨first, rest⟩ := Bool.and_eq_true_iff.mp same
    rw [ihA _ first, ihB _ rest]
  · intro a b ihA ihB right same
    cases right <;> first | exact absurd same Bool.false_ne_true | skip
    obtain ⟨first, rest⟩ := Bool.and_eq_true_iff.mp same
    rw [ihA _ first, ihB _ rest]
  · intro a b ihA ihB right same
    cases right <;> first | exact absurd same Bool.false_ne_true | skip
    obtain ⟨first, rest⟩ := Bool.and_eq_true_iff.mp same
    rw [ihA _ first, ihB _ rest]
  · intro a ih right same
    cases right <;> first | exact absurd same Bool.false_ne_true | skip
    rw [ih _ same]
  · intro x a ih right same
    cases right <;> first | exact absurd same Bool.false_ne_true | skip
    obtain ⟨first, rest⟩ := Bool.and_eq_true_iff.mp same
    rw [of_decide_eq_true first, ih _ rest]
  · intro x a ih right same
    cases right <;> first | exact absurd same Bool.false_ne_true | skip
    obtain ⟨first, rest⟩ := Bool.and_eq_true_iff.mp same
    rw [of_decide_eq_true first, ih _ rest]
  · intro d p o xs ihD ihXs right same
    cases right <;> first | exact absurd same Bool.false_ne_true | skip
    obtain ⟨front, rest⟩ := Bool.and_eq_true_iff.mp same
    obtain ⟨front, operation⟩ := Bool.and_eq_true_iff.mp front
    obtain ⟨dictionary, path⟩ := Bool.and_eq_true_iff.mp front
    rw [ihD _ dictionary, of_decide_eq_true path, of_decide_eq_true operation, ihXs _ rest]
  · intro a b ihA ihB right same
    cases right <;> first | exact absurd same Bool.false_ne_true | skip
    obtain ⟨first, rest⟩ := Bool.and_eq_true_iff.mp same
    rw [ihA _ first, ihB _ rest]
  · intro rights same; cases rights <;> first | exact absurd same Bool.false_ne_true | rfl
  · intro x xs ihX ihXs rights same
    cases rights <;> first | exact absurd same Bool.false_ne_true | skip
    obtain ⟨first, rest⟩ := Bool.and_eq_true_iff.mp same
    rw [ihX _ first, ihXs _ rest]

/-- Corresponding immediate parts of two terms with the same structural
constructor. An application splits into its first argument and the application
to the rest, so every split shrinks the problem. -/
def matchParts : Term Variable Literal Symbol → Term Variable Literal Symbol →
    Option (List (Term Variable Literal Symbol × Term Variable Literal Symbol))
  | .app f (x :: xs), .app g (y :: ys) => if f = g then some [(x, y), (.app f xs, .app g ys)] else none
  | .conj a b, .conj c d => some [(a, c), (b, d)]
  | .disj a b, .disj c d => some [(a, c), (b, d)]
  | .imp a b, .imp c d => some [(a, c), (b, d)]
  | .equal a b, .equal c d => some [(a, c), (b, d)]
  | .defaultNeg a, .defaultNeg b => some [(a, b)]
  | _, _ => none

def assignableName? (store : Store Variable Literal Symbol) : Term Variable Literal Symbol → Option Variable
  | .var name => if store.assignable name then some name else none
  | _ => none

/-- Compare two different resolved terms, neither an assignable name. Two
different binders of the same kind would need alpha-equivalence, and an
operation call evaluation: the profile does not admit those comparisons.
Otherwise rigid names are constants, structural constructors are split, and
anything else is a clash. -/
def compareTerms (hoApplySymbol : Symbol) (left right : Term Variable Literal Symbol) : MatchStep Variable Literal Symbol :=
  match left, right with
  | .dictionaryCall _ _ _ _, _ | _, .dictionaryCall _ _ _ _ => .unsupported
  | .forallVar _ _, .forallVar _ _ | .existsVar _ _, .existsVar _ _ => .unsupported
  | .var _, _ | _, .var _ => .mismatch
  | left, right =>
      match matchParts left right with
      | some parts => .split parts
      | none =>
          match left, right with
          | .app f _, .app g _ =>
              if f ≠ g ∧ (f = hoApplySymbol ∨ g = hoApplySymbol) then .unsupported else .mismatch
          | _, _ => .mismatch

/-- Identical terms are dropped; otherwise an assignable name on either side is
bound to the other side; otherwise the terms are compared. -/
def matchStep (hoApplySymbol : Symbol) (store : Store Variable Literal Symbol)
    (left right : Term Variable Literal Symbol) : MatchStep Variable Literal Symbol :=
  if identical left right then .drop
  else
    match assignableName? store left, assignableName? store right with
    | some name, _ => .bind name right
    | none, some name => .bind name left
    | none, none => compareTerms hoApplySymbol left right

/-- The number of declared entries whose name is still assignable. A binding
decreases it. -/
def Store.openCount (store : Store Variable Literal Symbol) : Nat :=
  ((store.names.map Prod.fst).filter store.assignable).length

/-! ### Termination -/

omit [DecidableEq Variable] [DecidableEq Literal] in
theorem matchParts_size {left right : Term Variable Literal Symbol}
    {parts : List (Term Variable Literal Symbol × Term Variable Literal Symbol)}
    (split : matchParts left right = some parts) : pairsSize parts < sizeOf left + sizeOf right := by
  unfold matchParts at split
  split at split
  · split at split
    · cases split; simp only [pairsSize]; simp; omega
    · cases split
  all_goals (cases split; try (simp only [pairsSize]; simp; omega))

omit [DecidableEq Literal] [DecidableEq Symbol] in
/-- A binding leaves its name assigned and every other name as it was. -/
theorem Store.assignable_bind {store : Store Variable Literal Symbol} {name : Variable}
    {value : Term Variable Literal Symbol} {targets allowed : List Variable} (other : Variable) :
    ({ (store.narrow targets allowed) with bindings := (name, value) :: store.bindings } :
      Store Variable Literal Symbol).assignable other = (decide (other ≠ name) && store.assignable other) := by
  have binding : ({ (store.narrow targets allowed) with bindings := (name, value) :: store.bindings } :
      Store Variable Literal Symbol).binding? other = if name = other then some value else store.binding? other := by
    simp only [Store.binding?, lookup]
  unfold Store.assignable
  rw [binding]
  show (match (store.narrow targets allowed).info? other with
    | some (.flexible _) => _ | _ => false) = _
  rw [Store.info?_narrow]
  cases info : store.info? other with
  | none => simp
  | some found =>
      cases found with
      | rigid => simp [narrowInfo]
      | flexible own =>
          obtain ⟨narrowed, narrowedEq⟩ : ∃ narrowed, narrowInfo targets allowed other (.flexible own) =
              .flexible narrowed := by
            simp only [narrowInfo]; split <;> exact ⟨_, rfl⟩
          simp only [Option.map_some, narrowedEq]
          by_cases same : name = other
          · subst same; simp
          · simp [same, Ne.symm same]

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem Store.bind_openCount {store next : Store Variable Literal Symbol} {scope : Scope Variable Literal Symbol}
    {name : Variable} {value : Term Variable Literal Symbol}
    (committed : store.bind scope name value = .bound next) (nontrivial : isName value name = false) :
    next.openCount < store.openCount := by
  obtain ⟨dependencies, infoEq, boundEq, outcome⟩ := Store.bind_committed committed
  rcases outcome with ⟨trivial, _⟩ | ⟨rfl, _, _⟩
  · rw [trivial] at nontrivial; cases nontrivial
  · unfold Store.openCount
    have keys : (({ (store.narrow value.freeVars dependencies) with
        bindings := (name, value) :: store.bindings } : Store Variable Literal Symbol).names.map Prod.fst) =
        store.names.map Prod.fst := by simp [Store.narrow]
    rw [keys]
    apply filter_length_lt
    · intro other _ assignable
      rw [Store.assignable_bind] at assignable
      simp only [Bool.and_eq_true, decide_eq_true_eq] at assignable
      exact assignable.2
    · refine ⟨name, List.mem_map.mpr ⟨_, lookup_mem infoEq, rfl⟩, ?_, ?_⟩
      · simp [Store.assignable, infoEq, boundEq]
      · rw [Store.assignable_bind]; simp

theorem matchStep_bind {hoApplySymbol : Symbol}
    {store : Store Variable Literal Symbol} {left right : Term Variable Literal Symbol} {name : Variable}
    {value : Term Variable Literal Symbol} (step : matchStep hoApplySymbol store left right = .bind name value) :
    ((left = .var name ∧ right = value) ∨ (right = .var name ∧ left = value)) ∧
      store.assignable name = true ∧ isName value name = false := by
  unfold matchStep at step
  split at step
  · cases step
  · rename_i different
    have nameOf : ∀ term found, assignableName? store term = some found →
        term = .var found ∧ store.assignable found = true := by
      intro term found equal
      cases term with
      | var other =>
          simp only [assignableName?] at equal
          split at equal
          · cases equal; rename_i assignable; exact ⟨rfl, assignable⟩
          · cases equal
      | _ => simp [assignableName?] at equal
    have notSelf : ∀ (term : Term Variable Literal Symbol) (found : Variable),
        isName term found = true → identical (.var found) term = true := by
      intro term found self
      cases term with
      | var other => simp only [isName, decide_eq_true_eq] at self; subst self; exact decide_eq_true rfl
      | _ => simp [isName] at self
    split at step
    · rename_i found _ leftName
      cases step
      obtain ⟨rfl, assignable⟩ := nameOf _ _ leftName
      refine ⟨.inl ⟨rfl, rfl⟩, assignable, ?_⟩
      cases self : isName right name
      · rfl
      · exact absurd (notSelf right name self) different
    · rename_i found _ rightName
      cases step
      obtain ⟨rfl, assignable⟩ := nameOf _ _ rightName
      refine ⟨.inr ⟨rfl, rfl⟩, assignable, ?_⟩
      cases self : isName left name
      · rfl
      · have equal := identical_eq _ _ (notSelf left name self)
        subst equal
        exact absurd (decide_eq_true rfl) different
    · unfold compareTerms at step
      repeat (first | split at step | cases step)

theorem matchStep_split {hoApplySymbol : Symbol}
    {store : Store Variable Literal Symbol} {left right : Term Variable Literal Symbol}
    {parts : List (Term Variable Literal Symbol × Term Variable Literal Symbol)}
    (step : matchStep hoApplySymbol store left right = .split parts) : matchParts left right = some parts := by
  unfold matchStep at step
  split at step
  · cases step
  · split at step
    · cases step
    · cases step
    · unfold compareTerms at step
      repeat (first | assumption | split at step | cases step)

variable [FreshNames Variable]

def substPairs (name : Variable) (value : Term Variable Literal Symbol)
    (pairs : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    List (Term Variable Literal Symbol × Term Variable Literal Symbol) :=
  pairs.map fun pair =>
    (pair.1.instantiate (Substitution.single name value), pair.2.instantiate (Substitution.single name value))

/-- Bind assignable names, split structural constructors, and stop at the
first clash, unadmitted comparison, or contract breach. Every pair is resolved
against the current store: a binding is substituted into the remaining pairs. -/
def unifyPairs (hoApplySymbol : Symbol) (scope : Scope Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (pairs : List (Term Variable Literal Symbol × Term Variable Literal Symbol))
    (done : List (Variable × Term Variable Literal Symbol)) : Unification Variable Literal Symbol :=
  match pairs with
  | [] => .unified store done
  | (left, right) :: rest =>
      match _step : matchStep hoApplySymbol store left right with
      | .drop => unifyPairs hoApplySymbol scope store rest done
      | .split parts => unifyPairs hoApplySymbol scope store (parts ++ rest) done
      | .bind name value =>
          match _bound : store.bind scope name value with
          | .bound next => unifyPairs hoApplySymbol scope next (substPairs name value rest) (done ++ [(name, value)])
          | .rejected => .mismatch
          | .violated => .violated
      | .mismatch => .mismatch
      | .unsupported => .unsupported
termination_by (store.openCount, pairsSize pairs)
decreasing_by
  · exact Prod.Lex.right _ (by simp only [pairsSize]; have := term_sizeOf_pos left; omega)
  · exact Prod.Lex.right _ (by
      rw [pairsSize_append]; simp only [pairsSize]
      have := matchParts_size (matchStep_split _step); omega)
  · exact Prod.Lex.left _ _ (Store.bind_openCount _bound (matchStep_bind _step).2.2)

/-- Match two terms read through the store. Readings naming something not
usable here (an undeclared name, or a rigid name outside the scope) break the
machine's contract before any comparison, even when identical. -/
def Store.unify (store : Store Variable Literal Symbol) (scope : Scope Variable Literal Symbol)
    (hoApplySymbol : Symbol) (left right : Term Variable Literal Symbol) : Unification Variable Literal Symbol :=
  if ((store.resolve left).freeVars ++ (store.resolve right).freeVars).all (store.usable scope) then
    unifyPairs hoApplySymbol scope store [(store.resolve left, store.resolve right)] []
  else .violated

/-! ## Correctness

`unifyPairs_bindAll`: the returned bindings, committed in order, give the
returned store, so the machine's commit replays the match. `Store.unify_sound`:
afterwards both sides read the same, in that store and in every refinement of
it. `Store.unify_supported` and `Store.unify_wellScoped`: for ordinary,
well-scoped inputs the only failure is `mismatch`; `Store.unify_violated`: a
contract breach is exactly an unusable name in a reading. -/

section Correctness

variable {hoApplySymbol : Symbol} {scope : Scope Variable Literal Symbol}

theorem unifyPairs_nil (store : Store Variable Literal Symbol) (done : List (Variable × Term Variable Literal Symbol)) :
    unifyPairs hoApplySymbol scope store [] done = .unified store done := by
  rw [unifyPairs]

theorem unifyPairs_cons (store : Store Variable Literal Symbol) (left right : Term Variable Literal Symbol)
    (rest : List (Term Variable Literal Symbol × Term Variable Literal Symbol))
    (done : List (Variable × Term Variable Literal Symbol)) :
    unifyPairs hoApplySymbol scope store ((left, right) :: rest) done =
      match matchStep hoApplySymbol store left right with
      | .drop => unifyPairs hoApplySymbol scope store rest done
      | .split parts => unifyPairs hoApplySymbol scope store (parts ++ rest) done
      | .bind name value =>
          match store.bind scope name value with
          | .bound next => unifyPairs hoApplySymbol scope next (substPairs name value rest) (done ++ [(name, value)])
          | .rejected => .mismatch
          | .violated => .violated
      | .mismatch => .mismatch
      | .unsupported => .unsupported := by
  rw [unifyPairs]
  split
  all_goals (try split)
  all_goals simp_all

omit [FreshNames Variable] in
theorem matchStep_drop {store : Store Variable Literal Symbol} {left right : Term Variable Literal Symbol}
    (step : matchStep hoApplySymbol store left right = .drop) : left = right := by
  unfold matchStep at step
  split at step
  · rename_i same; exact identical_eq _ _ same
  · split at step
    · cases step
    · cases step
    · unfold compareTerms at step
      repeat (first | split at step | cases step)

/-- The returned bindings, committed in order, give the returned store. -/
theorem unifyPairs_bindAll {store : Store Variable Literal Symbol}
    {pairs : List (Term Variable Literal Symbol × Term Variable Literal Symbol)}
    {done : List (Variable × Term Variable Literal Symbol)} :
    ∀ {final : Store Variable Literal Symbol} {bindings : List (Variable × Term Variable Literal Symbol)},
      unifyPairs hoApplySymbol scope store pairs done = .unified final bindings →
        ∃ added, bindings = done ++ added ∧ store.bindAll scope added = .bound final := by
  induction store, pairs, done using unifyPairs.induct hoApplySymbol scope with
  | case1 store done =>
      intro final bindings computed
      simp only [unifyPairs_nil, Unification.unified.injEq] at computed
      obtain ⟨rfl, rfl⟩ := computed
      exact ⟨[], by simp, rfl⟩
  | case2 store done left right rest step ih =>
      intro final bindings computed
      simp only [unifyPairs_cons, step] at computed
      exact ih computed
  | case3 store done left right rest parts step ih =>
      intro final bindings computed
      simp only [unifyPairs_cons, step] at computed
      exact ih computed
  | case4 store done left right rest name value step next bound ih =>
      intro final bindings computed
      simp only [unifyPairs_cons, step, bound] at computed
      obtain ⟨added, rfl, committed⟩ := ih computed
      exact ⟨(name, value) :: added, by simp, by simp only [Store.bindAll, bound]; exact committed⟩
  -- A rejected or broken binding, a mismatch, or an unsupported comparison is not `unified`.
  | _ => intro final bindings computed; simp_all [unifyPairs_cons]

omit [DecidableEq Literal] [FreshNames Variable] in
theorem matchParts_freeVars {left right : Term Variable Literal Symbol}
    {parts : List (Term Variable Literal Symbol × Term Variable Literal Symbol)}
    (split : matchParts left right = some parts) :
    ∀ pair ∈ parts, (∀ name ∈ pair.1.freeVars, name ∈ left.freeVars) ∧
      (∀ name ∈ pair.2.freeVars, name ∈ right.freeVars) := by
  have rest : ∀ (f : Symbol) (x : Term Variable Literal Symbol) (xs : List (Term Variable Literal Symbol)) name,
      name ∈ (Term.app f xs).freeVars → name ∈ (Term.app f (x :: xs)).freeVars := by
    intro f x xs name inside
    simp only [Term.freeVars, List.flatMap_cons, List.mem_append] at inside ⊢
    exact .inr inside
  unfold matchParts at split
  split at split
  next f x xs g y ys =>
    split at split
    · cases split
      intro pair member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨fun n h => by simp [Term.freeVars, h], fun n h => by simp [Term.freeVars, h]⟩
      · exact ⟨rest f x xs, rest g y ys⟩
    · cases split
  all_goals
    cases split
    all_goals
      intro pair member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      first
        | (rcases member with rfl | rfl <;>
            exact ⟨fun n h => by simp [Term.freeVars, h], fun n h => by simp [Term.freeVars, h]⟩)
        | (subst member; exact ⟨fun n h => by simp [Term.freeVars, h], fun n h => by simp [Term.freeVars, h]⟩)

omit [DecidableEq Literal] in
theorem matchParts_resolve {left right : Term Variable Literal Symbol}
    {parts : List (Term Variable Literal Symbol × Term Variable Literal Symbol)}
    (split : matchParts left right = some parts) (bindings : List (Variable × Term Variable Literal Symbol))
    (equal : ∀ pair ∈ parts, resolveWith bindings pair.1 = resolveWith bindings pair.2) :
    resolveWith bindings left = resolveWith bindings right := by
  have first := fun {a b : Term Variable Literal Symbol} {more} (same : parts = (a, b) :: more) =>
    (equal (a, b) (by rw [same]; exact List.mem_cons_self) : resolveWith bindings a = resolveWith bindings b)
  have second := fun {a b c d : Term Variable Literal Symbol} (same : parts = [(a, b), (c, d)]) =>
    (equal (c, d) (by rw [same]; simp) : resolveWith bindings c = resolveWith bindings d)
  unfold matchParts at split
  split at split
  next f x xs g y ys =>
    split at split
    · rename_i same
      cases split; subst same
      have head := first rfl
      have tail := second rfl
      simp only [resolveWith_app, List.map_cons, Term.app.injEq, true_and] at tail ⊢
      rw [head, tail]
    · cases split
  next a b c d =>
    cases split; simp only [resolveWith_conj]; rw [first rfl, second rfl]
  next a b c d =>
    cases split; simp only [resolveWith_disj]; rw [first rfl, second rfl]
  next a b c d =>
    cases split; simp only [resolveWith_imp]; rw [first rfl, second rfl]
  next a b c d =>
    cases split; simp only [resolveWith_equal]; rw [first rfl, second rfl]
  next a b =>
    cases split; simp only [resolveWith_defaultNeg]; rw [first rfl]
  next => cases split

/-- No pending term mentions a name bound in the store. -/
def Resolved (store : Store Variable Literal Symbol)
    (pairs : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) : Prop :=
  ∀ pair ∈ pairs, ∀ name ∈ pair.1.freeVars ++ pair.2.freeVars, name ∉ store.bindings.map Prod.fst

omit [DecidableEq Literal] [DecidableEq Symbol] in
private theorem resolve_bound {final : Store Variable Literal Symbol}
    {added older : List (Variable × Term Variable Literal Symbol)} {name : Variable}
    {value : Term Variable Literal Symbol} (extended : final.bindings = added ++ (name, value) :: older)
    {term : Term Variable Literal Symbol} (unbound : ∀ other ∈ term.freeVars, other ∉ older.map Prod.fst) :
    final.resolve term = resolveWith added (term.instantiate (Substitution.single name value)) := by
  simp only [Store.resolve, extended, resolveWith_append, resolveWith_cons, resolveWith_unbound unbound]

/-- After a successful match, every pending pair reads the same in the returned
store, provided the pairs were resolved against the starting store. -/
theorem unifyPairs_sound {store : Store Variable Literal Symbol}
    {pairs : List (Term Variable Literal Symbol × Term Variable Literal Symbol)}
    {done : List (Variable × Term Variable Literal Symbol)} :
    ∀ {final : Store Variable Literal Symbol} {bindings : List (Variable × Term Variable Literal Symbol)},
      unifyPairs hoApplySymbol scope store pairs done = .unified final bindings → Resolved store pairs →
        ∀ pair ∈ pairs, final.resolve pair.1 = final.resolve pair.2 := by
  induction store, pairs, done using unifyPairs.induct hoApplySymbol scope with
  | case1 store done => intro _ _ _ _ pair member; cases member
  | case2 store done left right rest step ih =>
      intro final bindings computed resolved pair member
      simp only [unifyPairs_cons, step] at computed
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · rw [matchStep_drop step]
      · exact ih computed (fun p m => resolved p (List.mem_cons_of_mem _ m)) pair member
  | case3 store done left right rest parts step ih =>
      intro final bindings computed resolved pair member
      simp only [unifyPairs_cons, step] at computed
      have split := matchStep_split step
      have partsResolved : Resolved store (parts ++ rest) := by
        intro p m name inside
        simp only [List.mem_append] at m
        rcases m with m | m
        · have ⟨fromLeft, fromRight⟩ := matchParts_freeVars split p m
          simp only [List.mem_append] at inside
          exact resolved _ List.mem_cons_self name (List.mem_append.mpr
            (inside.imp (fromLeft name) (fromRight name)))
        · exact resolved p (List.mem_cons_of_mem _ m) name inside
      have all := ih computed partsResolved
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact matchParts_resolve split final.bindings (fun p m => all p (List.mem_append_left _ m))
      · exact all pair (List.mem_append_right _ member)
  | case4 store done left right rest name value step next bound ih =>
      intro final bindings computed resolved pair member
      simp only [unifyPairs_cons, step, bound] at computed
      obtain ⟨sides, _, nontrivial⟩ := matchStep_bind step
      obtain ⟨dependencies, _, _, outcome⟩ := Store.bind_committed bound
      rcases outcome with ⟨trivial, _⟩ | ⟨nextEq, occurs, _⟩
      · rw [trivial] at nontrivial; cases nontrivial
      have nextBindings : next.bindings = (name, value) :: store.bindings := by rw [nextEq]
      obtain ⟨added, _, committed⟩ := unifyPairs_bindAll computed
      obtain ⟨more, moreEq⟩ := (Store.bindAll_refines committed).bindings
      have extended : final.bindings = more ++ (name, value) :: store.bindings := by rw [moreEq, nextBindings]
      have valueUnbound : ∀ other ∈ value.freeVars, other ∉ store.bindings.map Prod.fst := by
        intro other inside
        rcases sides with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact resolved _ List.mem_cons_self other (List.mem_append_right _ inside)
        · exact resolved _ List.mem_cons_self other (List.mem_append_left _ inside)
      have substituted : ∀ term : Term Variable Literal Symbol,
          (∀ other ∈ term.freeVars, other ∉ store.bindings.map Prod.fst) →
          (∀ other ∈ (term.instantiate (Substitution.single name value)).freeVars,
            other ∉ next.bindings.map Prod.fst) ∧
          final.resolve (term.instantiate (Substitution.single name value)) = final.resolve term := by
        intro term unbound
        have outside : ∀ other ∈ (term.instantiate (Substitution.single name value)).freeVars,
            other ≠ name ∧ other ∉ store.bindings.map Prod.fst := by
          intro other inside
          rcases Term.freeVars_instantiate_single inside with ⟨inTerm, different⟩ | ⟨_, inValue⟩
          · exact ⟨different, unbound other inTerm⟩
          · exact ⟨fun same => occurs (same ▸ inValue), valueUnbound other inValue⟩
        refine ⟨fun other inside => by
          rw [nextBindings]; simp [(outside other inside).1, (outside other inside).2], ?_⟩
        rw [resolve_bound extended (fun other inside => (outside other inside).2), resolve_bound extended unbound,
          Term.instantiate_fixed (σ := Substitution.single name value)]
        intro other inside
        simp [Substitution.single, Substitution.bind, (outside other inside).1]
      have restResolved : Resolved next (substPairs name value rest) := by
        intro p m other inside
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp m
        have unbound := resolved original (List.mem_cons_of_mem _ originalMember)
        simp only [List.mem_append] at inside
        rcases inside with inside | inside
        · exact (substituted _ (fun o i => unbound o (List.mem_append_left _ i))).1 other inside
        · exact (substituted _ (fun o i => unbound o (List.mem_append_right _ i))).1 other inside
      have all := ih computed restResolved
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · have nameUnbound : ∀ other ∈ (Term.var name : Term Variable Literal Symbol).freeVars,
            other ∉ store.bindings.map Prod.fst := by
          intro other inside
          simp only [Term.freeVars, List.mem_singleton] at inside
          subst inside
          apply resolved _ List.mem_cons_self
          rcases sides with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [Term.freeVars]
        have nameRead : final.resolve (.var name) = resolveWith more value := by
          rw [resolve_bound extended nameUnbound]
          simp [Term.instantiate, Substitution.single, Substitution.bind]
        have valueRead : final.resolve value = resolveWith more value := by
          rw [resolve_bound extended valueUnbound, Term.instantiate_fixed]
          intro other inside
          have different : other ≠ name := fun same => occurs (same ▸ inside)
          simp [Substitution.single, Substitution.bind, different]
        rcases sides with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact nameRead.trans valueRead.symm
        · exact valueRead.trans nameRead.symm
      · have unbound := resolved pair (List.mem_cons_of_mem _ member)
        have first := substituted pair.1 (fun o i => unbound o (List.mem_append_left _ i))
        have second := substituted pair.2 (fun o i => unbound o (List.mem_append_right _ i))
        rw [← first.2, ← second.2]
        exact all _ (List.mem_map.mpr ⟨pair, member, rfl⟩)
  -- A rejected or broken binding, a mismatch, or an unsupported comparison is not `unified`.
  | _ => intro final bindings computed; simp_all [unifyPairs_cons]

/-! ### What `unsupported` and `violated` mean -/

/-- Terms the initial profile always compares: no binders, no operation calls,
and no `ho_apply` application. -/
inductive Ordinary (hoApplySymbol : Symbol) : Term Variable Literal Symbol → Prop where
  | var {name : Variable} : Ordinary hoApplySymbol (.var name)
  | lit {value : Literal} : Ordinary hoApplySymbol (.lit value)
  | app {symbol : Symbol} {args : List (Term Variable Literal Symbol)} (ordinary : symbol ≠ hoApplySymbol)
      (arguments : ∀ arg ∈ args, Ordinary hoApplySymbol arg) : Ordinary hoApplySymbol (.app symbol args)
  | truth : Ordinary hoApplySymbol .truth
  | falsity : Ordinary hoApplySymbol .falsity
  | conj {left right : Term Variable Literal Symbol} (first : Ordinary hoApplySymbol left)
      (second : Ordinary hoApplySymbol right) : Ordinary hoApplySymbol (.conj left right)
  | disj {left right : Term Variable Literal Symbol} (first : Ordinary hoApplySymbol left)
      (second : Ordinary hoApplySymbol right) : Ordinary hoApplySymbol (.disj left right)
  | imp {left right : Term Variable Literal Symbol} (first : Ordinary hoApplySymbol left)
      (second : Ordinary hoApplySymbol right) : Ordinary hoApplySymbol (.imp left right)
  | equal {left right : Term Variable Literal Symbol} (first : Ordinary hoApplySymbol left)
      (second : Ordinary hoApplySymbol right) : Ordinary hoApplySymbol (.equal left right)
  | defaultNeg {body : Term Variable Literal Symbol} (inner : Ordinary hoApplySymbol body) :
      Ordinary hoApplySymbol (.defaultNeg body)

omit [FreshNames Variable] in
theorem matchStep_ordinary {store : Store Variable Literal Symbol} {left right : Term Variable Literal Symbol}
    (leftOrdinary : Ordinary hoApplySymbol left) (rightOrdinary : Ordinary hoApplySymbol right) :
    matchStep hoApplySymbol store left right ≠ .unsupported := by
  intro step
  unfold matchStep at step
  split at step
  · cases step
  · split at step
    · cases step
    · cases step
    · unfold compareTerms at step
      repeat' split at step
      all_goals first
        | (cases step; done)
        | (cases leftOrdinary; done)
        | (cases rightOrdinary; done)
        | (rename_i clash
           cases leftOrdinary with
           | app leftSymbol _ =>
               cases rightOrdinary with
               | app rightSymbol _ => exact clash.2.elim leftSymbol rightSymbol)

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem matchParts_ordinary {left right : Term Variable Literal Symbol}
    {parts : List (Term Variable Literal Symbol × Term Variable Literal Symbol)}
    (split : matchParts left right = some parts) (leftOrdinary : Ordinary hoApplySymbol left)
    (rightOrdinary : Ordinary hoApplySymbol right) :
    ∀ pair ∈ parts, Ordinary hoApplySymbol pair.1 ∧ Ordinary hoApplySymbol pair.2 := by
  unfold matchParts at split
  split at split
  next f x xs g y ys =>
    split at split
    · cases split
      cases leftOrdinary with
      | app leftSymbol leftArgs =>
          cases rightOrdinary with
          | app rightSymbol rightArgs =>
              intro pair member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl
              · exact ⟨leftArgs x List.mem_cons_self, rightArgs y List.mem_cons_self⟩
              · exact ⟨.app leftSymbol (fun arg m => leftArgs arg (List.mem_cons_of_mem _ m)),
                  .app rightSymbol (fun arg m => rightArgs arg (List.mem_cons_of_mem _ m))⟩
    · cases split
  all_goals
    cases split
    all_goals
      cases leftOrdinary
      cases rightOrdinary
      intro pair member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      first
        | (rcases member with rfl | rfl <;> exact ⟨by assumption, by assumption⟩)
        | (subst member; exact ⟨by assumption, by assumption⟩)

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem Ordinary.instantiate {term : Term Variable Literal Symbol} (ordinary : Ordinary hoApplySymbol term) :
    ∀ {σ : Substitution Variable Literal Symbol}, (∀ name ∈ term.freeVars, Ordinary hoApplySymbol (σ name)) →
      Ordinary hoApplySymbol (term.instantiate σ) := by
  induction ordinary with
  | var => intro σ values; simpa [Term.instantiate] using values _ (by simp [Term.freeVars])
  | lit => intros; simp only [Term.instantiate]; exact .lit
  | app symbolOrdinary arguments ih =>
      intro σ values
      simp only [Term.instantiate]
      refine .app symbolOrdinary (fun arg member => ?_)
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact ih original originalMember (fun name inside => values name
        (by simp only [Term.freeVars, List.mem_flatMap]; exact ⟨original, originalMember, inside⟩))
  | truth => intros; simp only [Term.instantiate]; exact .truth
  | falsity => intros; simp only [Term.instantiate]; exact .falsity
  | conj _ _ ihLeft ihRight =>
      intro σ values; simp only [Term.instantiate]
      exact .conj (ihLeft fun n m => values n (by simp [Term.freeVars, m]))
        (ihRight fun n m => values n (by simp [Term.freeVars, m]))
  | disj _ _ ihLeft ihRight =>
      intro σ values; simp only [Term.instantiate]
      exact .disj (ihLeft fun n m => values n (by simp [Term.freeVars, m]))
        (ihRight fun n m => values n (by simp [Term.freeVars, m]))
  | imp _ _ ihLeft ihRight =>
      intro σ values; simp only [Term.instantiate]
      exact .imp (ihLeft fun n m => values n (by simp [Term.freeVars, m]))
        (ihRight fun n m => values n (by simp [Term.freeVars, m]))
  | equal _ _ ihLeft ihRight =>
      intro σ values; simp only [Term.instantiate]
      exact .equal (ihLeft fun n m => values n (by simp [Term.freeVars, m]))
        (ihRight fun n m => values n (by simp [Term.freeVars, m]))
  | defaultNeg _ ih =>
      intro σ values; simp only [Term.instantiate]
      exact .defaultNeg (ih fun n m => values n (by simpa only [Term.freeVars] using m))

/-- On ordinary terms the profile admits every comparison: matching never
reports `unsupported`, so a failure there is a mismatch or a contract breach. -/
theorem unifyPairs_supported {store : Store Variable Literal Symbol}
    {pairs : List (Term Variable Literal Symbol × Term Variable Literal Symbol)}
    {done : List (Variable × Term Variable Literal Symbol)} :
    (∀ pair ∈ pairs, Ordinary hoApplySymbol pair.1 ∧ Ordinary hoApplySymbol pair.2) →
      unifyPairs hoApplySymbol scope store pairs done ≠ .unsupported := by
  induction store, pairs, done using unifyPairs.induct hoApplySymbol scope with
  | case1 store done => intro _; simp [unifyPairs_nil]
  | case2 store done left right rest step ih =>
      intro ordinary; simp only [unifyPairs_cons, step]
      exact ih (fun p m => ordinary p (List.mem_cons_of_mem _ m))
  | case3 store done left right rest parts step ih =>
      intro ordinary; simp only [unifyPairs_cons, step]
      have here := ordinary _ List.mem_cons_self
      apply ih
      intro p m
      simp only [List.mem_append] at m
      rcases m with m | m
      · exact matchParts_ordinary (matchStep_split step) here.1 here.2 p m
      · exact ordinary p (List.mem_cons_of_mem _ m)
  | case4 store done left right rest name value step next bound ih =>
      intro ordinary; simp only [unifyPairs_cons, step, bound]
      have here := ordinary _ List.mem_cons_self
      have valueOrdinary : Ordinary hoApplySymbol value := by
        rcases (matchStep_bind step).1 with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact here.2
        · exact here.1
      have single : ∀ term : Term Variable Literal Symbol, Ordinary hoApplySymbol term →
          Ordinary hoApplySymbol (term.instantiate (Substitution.single name value)) := by
        intro term termOrdinary
        apply termOrdinary.instantiate
        intro other _
        by_cases same : other = name
        · simpa [Substitution.single, Substitution.bind, same] using valueOrdinary
        · simpa [Substitution.single, Substitution.bind, same] using (Ordinary.var : Ordinary hoApplySymbol (.var other))
      apply ih
      intro p m
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp m
      have both := ordinary original (List.mem_cons_of_mem _ originalMember)
      exact ⟨single _ both.1, single _ both.2⟩
  | case5 store done left right rest name value step bound =>
      intro _; simp [unifyPairs_cons, step, bound]
  | case6 store done left right rest name value step bound =>
      intro _; simp [unifyPairs_cons, step, bound]
  | case7 store done left right rest step => intro _; simp [unifyPairs_cons, step]
  | case8 store done left right rest step =>
      intro ordinary
      have here := ordinary _ List.mem_cons_self
      exact absurd step (matchStep_ordinary here.1 here.2)

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
/-- `Store.bind` breaks the contract only for a name that is not assignable or a
value naming something not usable here. -/
theorem Store.bind_violated {store : Store Variable Literal Symbol} {scope : Scope Variable Literal Symbol}
    {name : Variable} {value : Term Variable Literal Symbol} (assignable : store.assignable name = true)
    (usable : ∀ other ∈ value.freeVars, store.usable scope other = true) :
    store.bind scope name value ≠ .violated := by
  intro violated
  unfold Store.bind at violated
  split at violated
  · split at violated
    · cases violated
    · dsimp only at violated
      split at violated
      · split at violated <;> cases violated
      · rename_i notUsable
        exact notUsable (List.all_eq_true.mpr usable)
  · rename_i notOpen
    unfold Store.assignable at assignable
    split at assignable
    · rename_i dependencies flexible
      simp only [Option.isNone_iff_eq_none] at assignable
      exact notOpen dependencies flexible assignable
    · cases assignable

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
/-- A binding keeps every other name usable as it was. -/
theorem Store.usable_bind {store next : Store Variable Literal Symbol} {scope : Scope Variable Literal Symbol}
    {name : Variable} {value : Term Variable Literal Symbol}
    (committed : store.bind scope name value = .bound next) {other : Variable} (different : other ≠ name) :
    next.usable scope other = store.usable scope other := by
  obtain ⟨dependencies, _, _, outcome⟩ := Store.bind_committed committed
  rcases outcome with ⟨_, rfl⟩ | ⟨rfl, _, _⟩
  · rfl
  · have binding : ({ (store.narrow value.freeVars dependencies) with bindings := (name, value) :: store.bindings } :
        Store Variable Literal Symbol).binding? other = store.binding? other := by
      simp only [Store.binding?, lookup, Ne.symm different, ite_false]
    unfold Store.usable
    rw [binding]
    show (match (store.narrow value.freeVars dependencies).info? other with
      | some .rigid => _ | some (.flexible _) => _ | none => false) = _
    rw [Store.info?_narrow]
    cases info : store.info? other with
    | none => rfl
    | some found =>
        cases found with
        | rigid => rfl
        | flexible own =>
            obtain ⟨narrowed, narrowedEq⟩ : ∃ narrowed, narrowInfo value.freeVars dependencies other
                (.flexible own) = .flexible narrowed := by
              simp only [narrowInfo]; split <;> exact ⟨_, rfl⟩
            simp only [Option.map_some, narrowedEq]

/-- With every pending name usable here, matching never reports `violated`: a
failure is a mismatch or an unadmitted comparison. -/
theorem unifyPairs_wellScoped {store : Store Variable Literal Symbol}
    {pairs : List (Term Variable Literal Symbol × Term Variable Literal Symbol)}
    {done : List (Variable × Term Variable Literal Symbol)} :
    (∀ pair ∈ pairs, ∀ name ∈ pair.1.freeVars ++ pair.2.freeVars, store.usable scope name = true) →
      unifyPairs hoApplySymbol scope store pairs done ≠ .violated := by
  induction store, pairs, done using unifyPairs.induct hoApplySymbol scope with
  | case1 store done => intro _; simp [unifyPairs_nil]
  | case2 store done left right rest step ih =>
      intro usable; simp only [unifyPairs_cons, step]
      exact ih (fun p m => usable p (List.mem_cons_of_mem _ m))
  | case3 store done left right rest parts step ih =>
      intro usable; simp only [unifyPairs_cons, step]
      apply ih
      intro p m name inside
      simp only [List.mem_append] at m
      rcases m with m | m
      · have ⟨fromLeft, fromRight⟩ := matchParts_freeVars (matchStep_split step) p m
        simp only [List.mem_append] at inside
        exact usable _ List.mem_cons_self name (List.mem_append.mpr (inside.imp (fromLeft name) (fromRight name)))
      · exact usable p (List.mem_cons_of_mem _ m) name inside
  | case4 store done left right rest name value step next bound ih =>
      intro usable; simp only [unifyPairs_cons, step, bound]
      obtain ⟨_, _, _, outcome⟩ := Store.bind_committed bound
      have occurs : name ∉ value.freeVars := by
        rcases outcome with ⟨trivial, _⟩ | ⟨_, occurs, _⟩
        · have nontrivial := (matchStep_bind step).2.2
          rw [trivial] at nontrivial; cases nontrivial
        · exact occurs
      have valueUsable : ∀ other ∈ value.freeVars, store.usable scope other = true := by
        intro other inside
        rcases (matchStep_bind step).1 with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact usable _ List.mem_cons_self other (List.mem_append_right _ inside)
        · exact usable _ List.mem_cons_self other (List.mem_append_left _ inside)
      apply ih
      intro p m other inside
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp m
      have names := usable original (List.mem_cons_of_mem _ originalMember)
      have fromOriginal : ∀ term : Term Variable Literal Symbol,
          (∀ n ∈ term.freeVars, store.usable scope n = true) →
          ∀ n ∈ (term.instantiate (Substitution.single name value)).freeVars, next.usable scope n = true := by
        intro term termUsable n member
        rcases Term.freeVars_instantiate_single member with ⟨inTerm, different⟩ | ⟨_, inValue⟩
        · rw [Store.usable_bind bound different]; exact termUsable n inTerm
        · rw [Store.usable_bind bound (fun same => occurs (same ▸ inValue))]; exact valueUsable n inValue
      simp only [List.mem_append] at inside
      rcases inside with inside | inside
      · exact fromOriginal _ (fun n i => names n (List.mem_append_left _ i)) other inside
      · exact fromOriginal _ (fun n i => names n (List.mem_append_right _ i)) other inside
  | case5 store done left right rest name value step bound =>
      intro _; simp [unifyPairs_cons, step, bound]
  | case6 store done left right rest name value step bound =>
      intro usable
      have here := usable _ List.mem_cons_self
      obtain ⟨sides, assignable, _⟩ := matchStep_bind step
      refine absurd bound (Store.bind_violated assignable (fun other inside => ?_))
      rcases sides with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact here other (List.mem_append_right _ inside)
      · exact here other (List.mem_append_left _ inside)
  | case7 store done left right rest step => intro _; simp [unifyPairs_cons, step]
  | case8 store done left right rest step => intro _; simp [unifyPairs_cons, step]

/-! ### Matching against the store -/

/-- Matching two terms read through a scoped store: the bindings commit in
order to the returned store, which refines the original and is scoped, and
both terms read the same there and in every later refinement. -/
theorem Store.unify_sound {store final : Store Variable Literal Symbol} (valid : store.Scoped)
    {left right : Term Variable Literal Symbol} {bindings : List (Variable × Term Variable Literal Symbol)}
    (computed : store.unify scope hoApplySymbol left right = .unified final bindings) :
    store.bindAll scope bindings = .bound final ∧ store.Refines final ∧ final.Scoped ∧
      final.resolve left = final.resolve right := by
  unfold Store.unify at computed
  split at computed
  case isFalse => cases computed
  obtain ⟨added, sameBindings, committed⟩ := unifyPairs_bindAll computed
  simp only [List.nil_append] at sameBindings
  subst sameBindings
  have refines := Store.bindAll_refines committed
  refine ⟨committed, refines, Store.bindAll_scoped valid committed, ?_⟩
  have resolved : Resolved store [(store.resolve left, store.resolve right)] := by
    intro pair member name inside
    simp only [List.mem_singleton] at member
    subst member
    simp only [List.mem_append] at inside
    rcases inside with inside | inside
    · exact valid.triangular.resolve_unbound left name inside
    · exact valid.triangular.resolve_unbound right name inside
  have same := unifyPairs_sound computed resolved _ List.mem_cons_self
  obtain ⟨more, extended⟩ := refines.bindings
  have idempotent : ∀ term : Term Variable Literal Symbol, final.resolve (store.resolve term) = final.resolve term := by
    intro term
    rw [Store.resolve_extends extended, Store.resolve_extends extended]
    congr 1
    exact resolveWith_unbound (valid.triangular.resolve_unbound term)
  rw [← idempotent left, ← idempotent right]
  exact same

/-- Ordinary readings are always compared. -/
theorem Store.unify_supported (store : Store Variable Literal Symbol) {left right : Term Variable Literal Symbol}
    (leftOrdinary : Ordinary hoApplySymbol (store.resolve left))
    (rightOrdinary : Ordinary hoApplySymbol (store.resolve right)) :
    store.unify scope hoApplySymbol left right ≠ .unsupported := by
  unfold Store.unify
  split
  · exact unifyPairs_supported (fun pair member => by
      simp only [List.mem_singleton] at member; subst member; exact ⟨leftOrdinary, rightOrdinary⟩)
  · intro equal; cases equal

/-- Readings naming only usable names never break the contract. -/
theorem Store.unify_wellScoped (store : Store Variable Literal Symbol) {left right : Term Variable Literal Symbol}
    (usable : ∀ name ∈ (store.resolve left).freeVars ++ (store.resolve right).freeVars,
      store.usable scope name = true) :
    store.unify scope hoApplySymbol left right ≠ .violated := by
  unfold Store.unify
  split
  · exact unifyPairs_wellScoped (fun pair member => by
      simp only [List.mem_singleton] at member; subst member; exact usable)
  · rename_i notUsable; exact absurd (List.all_eq_true.mpr usable) notUsable

private theorem exists_of_not_all {α : Type} {items : List α} {p : α → Bool} (notAll : ¬ items.all p = true) :
    ∃ item ∈ items, p item = false := by
  induction items with
  | nil => simp at notAll
  | cons item rest ih =>
      cases holds : p item
      · exact ⟨item, List.mem_cons_self, holds⟩
      · simp only [List.all_cons, holds, Bool.true_and] at notAll
        obtain ⟨found, member, fails⟩ := ih notAll
        exact ⟨found, List.mem_cons_of_mem _ member, fails⟩

/-- `violated` means exactly that a reading names something not usable here. -/
theorem Store.unify_violated (store : Store Variable Literal Symbol) {left right : Term Variable Literal Symbol}
    (violated : store.unify scope hoApplySymbol left right = .violated) :
    ∃ name ∈ (store.resolve left).freeVars ++ (store.resolve right).freeVars, store.usable scope name = false := by
  unfold Store.unify at violated
  split at violated
  · rename_i usable
    exact absurd violated (unifyPairs_wellScoped (fun pair member => by
      simp only [List.mem_singleton] at member; subst member; exact List.all_eq_true.mp usable))
  · rename_i notUsable; exact exists_of_not_all notUsable

/-- A match for a candidate is computed against the store its commit prepares.
When the candidate's names and premises pass the commit's checks, the
machine's commit replays the match exactly and wakes the suspensions waiting on
a name the match bound. -/
theorem Store.commit_unify {store final : Store Variable Literal Symbol} (valid : store.Scoped)
    {obligation : Obligation Variable Literal Symbol} {flexibles rigids : List Variable}
    {premises : List (Premise Variable Literal Symbol)}
    (accepted : store.Accepts obligation flexibles rigids premises)
    {left right : Term Variable Literal Symbol} {bindings : List (Variable × Term Variable Literal Symbol)}
    (computed : (store.prepare obligation flexibles rigids).unify obligation.scope hoApplySymbol left right =
      .unified final bindings) :
    store.commit obligation flexibles rigids premises bindings = .committed final.wake final.woken ∧
      final.resolve left = final.resolve right := by
  have ⟨distinct, fresh, declared, _, _⟩ := accepted
  have ⟨committed, _, _, same⟩ := Store.unify_sound (Store.prepare_scoped valid distinct fresh declared) computed
  exact ⟨Store.commit_prepared accepted committed, same⟩

/-- A commit replaying a match against its prepared store makes the two sides
read the same in the committed store. -/
theorem Store.commit_matched {store final next : Store Variable Literal Symbol} (valid : store.Scoped)
    {obligation : Obligation Variable Literal Symbol} {flexibles rigids : List Variable}
    {premises : List (Premise Variable Literal Symbol)} {left right : Term Variable Literal Symbol}
    {bindings : List (Variable × Term Variable Literal Symbol)} {woken : List (Suspension Variable Literal Symbol)}
    (computed : (store.prepare obligation flexibles rigids).unify obligation.scope hoApplySymbol left right =
      .unified final bindings)
    (committed : store.commit obligation flexibles rigids premises bindings = .committed next woken) :
    next.resolve left = next.resolve right := by
  obtain ⟨replayed, same⟩ := Store.commit_unify valid (Store.commit_checks committed).1 computed
  rw [committed] at replayed
  cases replayed
  exact same

end Correctness

end AnthillModKbSpec.Machine
