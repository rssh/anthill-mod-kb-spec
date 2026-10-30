import AnthillModKbSpec.Resolution.Machine.Reconstruction
import AnthillModKbSpec.Resolution.Machine.Program
import AnthillModKbSpec.Foundation.Monotonicity

namespace AnthillModKbSpec.Machine

open AdmissionSignature InductiveDomains

/-! # Ordinary clause selection and positive execution (S06)

The first executable command set of the machine. `positive` answers truth,
conjunction, disjunction, implication, and quantifier goals by their
introduction rules, closes goals by assumptions, instantiates local rules, and
selects clauses of an effective `Program` for atomic goals and denial clauses
for falsity. A range guard on an unbound flexible name delays instead of
enumerating ahead of the clause body. Matching is the S05 matcher against the
store each candidate's commit prepares: `unsupported` and `violated` matches are
gaps, recorded beside the other candidates (`Response.incomplete`), and
`mismatch` drops the candidate. `positive_sound` proves the command sound, so a
successful run reconstructs `Derives` for its answer instance
(`positive_reconstructs`). -/

variable {Domain Variable Literal Symbol Certificate Snapshot : Type}
  [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal] [FreshNames Variable]

/-! ## The command -/

/-- The index of atomic and falsity goals: the same symbol and arity, or both
falsity. -/
def sameHead : Term Variable Literal Symbol → Term Variable Literal Symbol → Bool
  | .app left leftArgs, .app right rightArgs => decide (left = right) && leftArgs.length == rightArgs.length
  | .falsity, .falsity => true
  | _, _ => false

/-- An application by `ho_apply` against a direct one of the matching arity, or
the reverse: comparing them needs `ho_apply` conversion (S11). -/
def hoMixed (hoApplySymbol : Symbol) : Term Variable Literal Symbol → Term Variable Literal Symbol → Bool
  | .app left leftArgs, .app right rightArgs =>
      (decide (left = hoApplySymbol) && decide (right ≠ hoApplySymbol) && leftArgs.length == rightArgs.length + 1) ||
        (decide (right = hoApplySymbol) && decide (left ≠ hoApplySymbol) && rightArgs.length == leftArgs.length + 1)
  | _, _ => false

/-- A candidate concluding `conclusion` is matched against `goal` when it has the
goal's head, or a head that differs only by `ho_apply`: the matcher reports the
latter as `unsupported`, a gap. -/
def mayMatch (hoApplySymbol : Symbol) (goal conclusion : Term Variable Literal Symbol) : Bool :=
  sameHead goal conclusion || hoMixed hoApplySymbol goal conclusion

/-- The leading universal binders of a local rule. -/
def leadingBinders : Term Variable Literal Symbol → List Variable
  | .forallVar binder body => binder :: leadingBinders body
  | _ => []

/-- The term after `count` leading universal binders, which stay free in it. -/
def stripLeading : Nat → Term Variable Literal Symbol → Term Variable Literal Symbol
  | count + 1, .forallVar _ body => stripLeading count body
  | _, term => term

/-- A formula from which the goal might follow by rules this slice lacks: left
rules on conjunction, disjunction, and existentials, compound or curried
conclusions, or a conclusion bound by the rule itself (`∀P. P`). -/
def mayConclude (hoApplySymbol : Symbol) (goal : Term Variable Literal Symbol) :
    List Variable → Term Variable Literal Symbol → Bool
  | bound, .imp _ conclusion => mayConclude hoApplySymbol goal bound conclusion
  | bound, .forallVar name body | bound, .existsVar name body => mayConclude hoApplySymbol goal (name :: bound) body
  | bound, .conj left right | bound, .disj left right =>
      mayConclude hoApplySymbol goal bound left || mayConclude hoApplySymbol goal bound right
  | bound, .var name => decide (name ∈ bound)
  | _, conclusion => mayMatch hoApplySymbol goal conclusion

/-- The command's reading of the context: each assumption with its reading. -/
def Store.readContext (store : Store Variable Literal Symbol) (obligation : Obligation Variable Literal Symbol) :
    List (Term Variable Literal Symbol × Term Variable Literal Symbol) :=
  obligation.scope.assumptions.map fun assumption => (assumption, store.resolve assumption)

omit [DecidableEq Symbol] [DecidableEq Literal] in
theorem Store.mem_readContext {store : Store Variable Literal Symbol} {obligation : Obligation Variable Literal Symbol}
    {assumption read : Term Variable Literal Symbol} (member : (assumption, read) ∈ store.readContext obligation) :
    assumption ∈ obligation.scope.assumptions ∧ read = store.resolve assumption := by
  obtain ⟨_, inside, same⟩ := List.mem_map.mp member
  cases same
  exact ⟨inside, rfl⟩

/-- The binder names of the goal and context as read: `Store.readBinders`, from
the readings the command already holds. Fresh names avoid them. -/
def readAvoid (goal : Term Variable Literal Symbol) (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    List Variable :=
  (goal :: context.map Prod.snd).flatMap Term.binderNames

/-- Identity: the goal matched against an assumption it can be. -/
def identityAttempts (hoApplySymbol : Symbol) (obligation : Obligation Variable Literal Symbol)
    (store : Store Variable Literal Symbol) (goal : Term Variable Literal Symbol)
    (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    List (Attempt Variable Literal Symbol Certificate) :=
  context.map fun (assumption, read) =>
    if mayMatch hoApplySymbol goal read then
      attempt ((store.prepare obligation [] []).unify obligation.scope hoApplySymbol obligation.goal assumption)
        fun bindings => Expansion.assumption bindings
    else some none

/-- Ex falso: a goal other than falsity, under an assumption reading as falsity. -/
def exFalso (goal : Term Variable Literal Symbol) (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    List (Expansion Variable Literal Symbol Certificate) :=
  match goal with
  | .falsity => []
  | _ => if context.any fun (_, read) => identical read .falsity then [.falsityElim] else []

/-- How a local rule's matrix (the rule after its leading binders) is used: an
implication `B → H` by implication elimination on `H`, an atom or falsity by
universal elimination, and any other shape not at all. -/
inductive Matrix (Variable Literal Symbol : Type) where
  | implication (head : Term Variable Literal Symbol)
  | atomic
  | other

def Matrix.of : Term Variable Literal Symbol → Matrix Variable Literal Symbol
  | .imp _ head => .implication head
  | .app _ _ | .falsity => .atomic
  | _ => .other

/-- An atom or falsity with no leading binder: identity's, not a rule. -/
def isFact (term : Term Variable Literal Symbol) : Bool :=
  match term with
  | .app _ _ | .falsity => true
  | _ => false

/-- Fresh flexible witnesses for a local rule's leading binders: new to the
store, and avoiding the binder names the obligation reads and the rule's own. -/
def Store.witnessesFor (store : Store Variable Literal Symbol) (avoid : List Variable)
    (rule : Term Variable Literal Symbol) : List Variable :=
  (store.freshen (leadingBinders rule) (avoid ++ rule.binderNames)).map Prod.snd

/-- A local rule `∀x̄. (B → H)` with fresh witnesses: `H'` matched against the
goal; the premises are the instance `B' → H'` and `B'`. -/
def ruleUse (hoApplySymbol : Symbol) (obligation : Obligation Variable Literal Symbol)
    (store : Store Variable Literal Symbol) (fresh : List Variable) (rule : Term Variable Literal Symbol) :
    Attempt Variable Literal Symbol Certificate :=
  match rule.instantiateLeading (fresh.map Term.var) with
  | some (.imp condition conclusion) =>
      attempt ((store.prepare obligation fresh []).unify obligation.scope hoApplySymbol conclusion obligation.goal)
        fun bindings => { Expansion.impElim condition conclusion with flexibles := fresh, bindings := bindings }
  | _ => some none

/-- A universal fact `∀x₁…xₙ. H` (n ≥ 1) with fresh witnesses: the instance of
`H` matched against the goal, eliminating the last binder; the premise is the
fact with the other binders instantiated. -/
def factUse (hoApplySymbol : Symbol) (obligation : Obligation Variable Literal Symbol)
    (store : Store Variable Literal Symbol) (fresh : List Variable) (rule : Term Variable Literal Symbol) :
    Attempt Variable Literal Symbol Certificate :=
  match rule.instantiateLeading (fresh.dropLast.map Term.var), fresh.getLast? with
  | some (.forallVar binder body), some witness =>
      attempt ((store.prepare obligation fresh []).unify obligation.scope hoApplySymbol
          (body.instantiate (Substitution.single binder (.var witness))) obligation.goal)
        fun bindings => { Expansion.forallElim binder body (.var witness) with flexibles := fresh, bindings := bindings }
  | _, _ => some none

/-- A local rule `∀x₁…xₙ. M`, given as written and as read, for an atomic or
falsity goal. It is classified and filtered by its reading, and instantiated as
written, so that the exact steps (`exactStep`) find its instances as built. Its
free names are captured parameters and are kept; its leading binders get fresh
witnesses (`Store.witnessesFor`), and only once the read matrix's head may match
the goal. An implication matrix is used by `ruleUse`, an atomic one with n ≥ 1
by `factUse`. An assumption reading as an atom is identity's. Any other shape
from which the goal might follow (`mayConclude`) is a gap: left rules and
compound conclusions are S09's, and so is a rule that only its reading reveals,
written as a flexible name. -/
def localAttempt (hoApplySymbol : Symbol) (obligation : Obligation Variable Literal Symbol)
    (store : Store Variable Literal Symbol) (goal : Term Variable Literal Symbol) (avoid : List Variable)
    (rule read : Term Variable Literal Symbol) : Attempt Variable Literal Symbol Certificate :=
  match Matrix.of (stripLeading (leadingBinders rule).length rule),
      Matrix.of (stripLeading (leadingBinders rule).length read) with
  | .implication _, .implication head =>
      if mayMatch hoApplySymbol goal head then
        ruleUse hoApplySymbol obligation store (store.witnessesFor avoid rule) rule
      else if mayConclude hoApplySymbol goal (leadingBinders read) head then none
      else some none
  | .atomic, .atomic =>
      if !(leadingBinders rule).isEmpty && mayMatch hoApplySymbol goal (stripLeading (leadingBinders rule).length read)
      then factUse hoApplySymbol obligation store (store.witnessesFor avoid rule) rule
      else some none
  | _, _ =>
      if isFact read then some none
      else if mayConclude hoApplySymbol goal (leadingBinders read) (stripLeading (leadingBinders read).length read) then
        none
      else some none

/-- A program clause selected by head symbol and arity: every template name
renamed to a fresh flexible name, the renamed head matched against the goal, and
the renamed body the one premise. A denial clause `⊥ :- body` serves a goal that
reads as falsity, with nothing to match. The head is never assumed. -/
def clauseAttempt (hoApplySymbol : Symbol) (obligation : Obligation Variable Literal Symbol)
    (store : Store Variable Literal Symbol) (goal : Term Variable Literal Symbol) (avoid : List Variable)
    (entry : ProgramClause Variable Literal Symbol) : Attempt Variable Literal Symbol Certificate :=
  match entry.clause with
  | .definite head body =>
      if mayMatch hoApplySymbol goal head then
        let fresh := store.freshen (HornClause.definite head body).templates
          (avoid ++ (head :: body).flatMap Term.binderNames)
        attempt ((store.prepare obligation (fresh.map Prod.snd) []).unify obligation.scope hoApplySymbol
            (head.instantiate (Substitution.rename fresh)) obligation.goal)
          fun bindings => Expansion.clause head body fresh bindings
      else some none
  | .goal body =>
      match goal with
      | .falsity =>
          some (some (Expansion.goalClause body
            (store.freshen (HornClause.goal body).templates (avoid ++ body.flatMap Term.binderNames))))
      | _ => some none

/-- An atomic or falsity goal: identity, ex falso, local rules, then program
clauses, in that order. A gap among them makes the response incomplete. -/
def atomResponse (hoApplySymbol : Symbol) (program : Program Variable Literal Symbol)
    (obligation : Obligation Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (goal : Term Variable Literal Symbol) (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    Response Variable Literal Symbol Certificate :=
  let avoid := readAvoid goal context
  respond (identityAttempts hoApplySymbol obligation store goal context ++
    (exFalso goal context).map (some ∘ some) ++
    context.map (fun (assumption, read) => localAttempt hoApplySymbol obligation store goal avoid assumption read) ++
    program.clauses.map (clauseAttempt hoApplySymbol obligation store goal avoid))

/-- The disjunction a range guard over an explicit domain list ends with:
`m(t) ∨ false`. Its `false` alternative is never tried: a guard is a membership
check, not a request for contradiction search. -/
def guardTail (program : Program Variable Literal Symbol) : Term Variable Literal Symbol → Bool
  | .disj (.app symbol [_]) .falsity => program.guard symbol
  | _ => false

/-- The introduction rules of a connective goal. Other goals (equality, NAF,
calls, rigid names, literals) have none in this slice. -/
def introductions (program : Program Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) (goal : Term Variable Literal Symbol) :
    Option (List (Expansion Variable Literal Symbol Certificate)) :=
  match goal with
  | .truth => some [.truth]
  | .conj left right => some [.conjIntro left right]
  | .disj left right =>
      if guardTail program (.disj left right) then some [.disjLeft left] else some [.disjLeft left, .disjRight right]
  | .imp premise conclusion => some [.impIntro premise conclusion]
  | .forallVar binder body => some [.forallIntro binder body (store.freshFor (readAvoid goal context))]
  | .existsVar binder body => some [.existsIntro binder body (store.freshFor (readAvoid goal context))]
  | _ => none

mutual
/-- Read witnesses for `patterns` off a term: a one-way syntactic match of
`pattern` against it, entering binders of the same name, where the binder
shadows a pattern name. It only proposes; `exactInstance?` accepts a proposal
only when the instance it builds is identical to the goal. -/
def extract (patterns : List Variable) : Term Variable Literal Symbol → Term Variable Literal Symbol →
    List (Variable × Term Variable Literal Symbol) → Option (List (Variable × Term Variable Literal Symbol))
  | .var name, target, found =>
      if name ∈ patterns then
        match OperationDictionaries.lookup found name with
        | some value => if identical value target then some found else none
        | none => some ((name, target) :: found)
      else if identical (.var name) target then some found else none
  | .app f xs, .app g ys, found => if f = g then extractArgs patterns xs ys found else none
  | .conj a b, .conj c d, found | .disj a b, .disj c d, found | .imp a b, .imp c d, found
  | .equal a b, .equal c d, found =>
      match extract patterns a c found with
      | some next => extract patterns b d next
      | none => none
  | .defaultNeg a, .defaultNeg b, found => extract patterns a b found
  | .forallVar x a, .forallVar y b, found | .existsVar x a, .existsVar y b, found =>
      if x = y then extract (patterns.filter (· ≠ x)) a b found else none
  | .dictionaryCall d p o xs, .dictionaryCall e q r ys, found =>
      if p = q ∧ o = r then
        match extract patterns d e found with
        | some next => extractArgs patterns xs ys next
        | none => none
      else none
  | pattern, target, found => if identical pattern target then some found else none

def extractArgs (patterns : List Variable) : List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) →
    List (Variable × Term Variable Literal Symbol) → Option (List (Variable × Term Variable Literal Symbol))
  | [], [], found => some found
  | x :: xs, y :: ys, found =>
      match extract patterns x y found with
      | some next => extractArgs patterns xs ys next
      | none => none
  | _, _, _ => none
end

/-- The universal elimination that makes `goal`, as written, the rule's instance
after `count` binders: its binder, body, and witness. The witnesses are read off
the goal and the instance is checked identical to it. A binder that does not
occur in the rule's matrix gets the closed witness `true`. -/
def exactInstance? (rule : Term Variable Literal Symbol) (count : Nat) (goal : Term Variable Literal Symbol) :
    Option (Variable × Term Variable Literal Symbol × Term Variable Literal Symbol) :=
  let binders := (leadingBinders rule).take count
  match extract binders (stripLeading count rule) goal [] with
  | none => none
  | some found =>
      let witnesses := binders.map fun name => (OperationDictionaries.lookup found name).getD .truth
      match rule.instantiateLeading witnesses.dropLast, witnesses.getLast? with
      | some (.forallVar binder body), some witness =>
          if identical (body.instantiate (Substitution.single binder witness)) goal then some (binder, body, witness)
          else none
      | _, _ => none

/-- The exact steps from `count` binders down close at the rule itself. -/
def exactCloses (rule : Term Variable Literal Symbol) : Nat → Term Variable Literal Symbol → Bool
  | 0, goal => identical goal rule
  | count + 1, goal =>
      match exactInstance? rule (count + 1) goal with
      | some (binder, body, _) => exactCloses rule count (.forallVar binder body)
      | none => false

/-- One universal elimination from a local rule `∀x₁…xₙ. M`, for `count ≤ n`,
when the goal as written is the rule's instance after `count` binders. Its
premise is the rule after `count - 1` binders, which the step for `count - 1`
closes in turn, down to the assumption itself; the step is offered only when
that whole chain closes (`exactCloses`), so a premise never falls back to
introduction. Both sides are compared as written, as `localAttempt` built them,
so a step needs no match under binders. -/
def exactStep (obligation : Obligation Variable Literal Symbol) (rule : Term Variable Literal Symbol) (count : Nat) :
    Option (Expansion Variable Literal Symbol Certificate) :=
  match exactInstance? rule count obligation.goal with
  | some (binder, body, witness) =>
      if exactCloses rule (count - 1) (.forallVar binder body) then some (Expansion.forallElim binder body witness)
      else none
  | none => none

/-- An assumption the goal reads as. -/
def identities (goal : Term Variable Literal Symbol) (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    List (Expansion Variable Literal Symbol Certificate) :=
  context.filterMap fun (_, read) => if identical goal read then some (Expansion.assumption []) else none

/-- Candidates that need no match: an assumption the goal reads as, ex falso,
and exact universal eliminations from local rules. -/
def exactCandidates (obligation : Obligation Variable Literal Symbol) (goal : Term Variable Literal Symbol)
    (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    List (Expansion Variable Literal Symbol Certificate) :=
  identities goal context ++ exFalso goal context ++
    obligation.scope.assumptions.flatMap fun assumption =>
      (List.range (leadingBinders assumption).length).filterMap fun index =>
        exactStep obligation assumption (index + 1)

/-- A non-atomic goal: exact candidates close it without introduction, which
proves a local rule's instance from the rule alone; otherwise its introduction
rules, or a gap. No match compares binders here, so no gap comes from matching. -/
def compositeResponse (program : Program Variable Literal Symbol) (obligation : Obligation Variable Literal Symbol)
    (store : Store Variable Literal Symbol) (goal : Term Variable Literal Symbol)
    (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    Response Variable Literal Symbol Certificate :=
  match exactCandidates obligation goal context with
  | [] =>
      match introductions program store context goal with
      | some intros => .candidates intros
      | none => .unsupported
  | first :: rest => .candidates (first :: rest)

/-- The name a range guard applies to: a guard atom `m(x)`, or a disjunction of
guard atoms on one name ending in falsity, as `InductiveDomains.guard` builds
for an explicit list of domains. -/
def guardSubject? (program : Program Variable Literal Symbol) : Term Variable Literal Symbol → Option Variable
  | .app symbol [.var name] => if program.guard symbol then some name else none
  | .disj first rest =>
      match guardSubject? program first, rest with
      | some name, .falsity => some name
      | some name, _ => if guardSubject? program rest = some name then some name else none
      | none, _ => none
  | _ => none

/-- The name a goal waits on: a goal reading as an unbound flexible name, or a
range guard whose argument does. -/
def waiting? (program : Program Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (goal : Term Variable Literal Symbol) : Option Variable :=
  match assignableName? store goal with
  | some name => some name
  | none => (guardSubject? program goal).filter store.assignable

/-- The response to a goal read as `goal` under the context read as `context`. A
goal that would wait is first closed by an exact candidate, if any. -/
def respondTo (hoApplySymbol : Symbol) (program : Program Variable Literal Symbol)
    (obligation : Obligation Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (goal : Term Variable Literal Symbol) (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    Response Variable Literal Symbol Certificate :=
  match waiting? program store goal with
  | some name =>
      match exactCandidates obligation goal context with
      | [] => .delay [name]
      | first :: rest => .candidates (first :: rest)
  | none =>
      match goal with
      | .app _ _ | .falsity => atomResponse hoApplySymbol program obligation store goal context
      | _ => compositeResponse program obligation store goal context

/-- Ordinary clause selection and positive execution. The command reads the goal
and the context through the store once per focus; the matcher reads the sides
it compares again. A guard on an unbound name delays until a later goal binds
it, and still delayed at the end it flounders. -/
def positive (hoApplySymbol : Symbol) (program : Program Variable Literal Symbol) :
    Command Variable Literal Symbol Certificate := fun obligation store =>
  respondTo hoApplySymbol program obligation store (store.resolve obligation.goal) (store.readContext obligation)

/-! ## Soundness of the command -/

variable {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}
  {obligation : Obligation Variable Literal Symbol} {store : Store Variable Literal Symbol}
  {goal : Term Variable Literal Symbol} {avoid : List Variable}

theorem identityAttempts_sound (valid : store.Scoped) :
    ∀ candidate ∈ identityAttempts (Certificate := Certificate) hoApplySymbol obligation store goal
      (store.readContext obligation), AttemptSound hoApplySymbol kb naf store obligation candidate := by
  intro candidate member
  obtain ⟨⟨assumption, read⟩, inside, rfl⟩ := List.mem_map.mp member
  dsimp only
  split
  · exact attempt_sound valid (fun _ => ⟨rfl, by simp [Expansion.rigids, Expansion.assumption], rfl⟩)
      fun _ _ matched => Expansion.assumption_soundUnder (Store.mem_readContext inside).1 matched
  · intro _ found; cases found

theorem exFalso_sound {context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)} :
    ∀ expansion ∈ exFalso (Certificate := Certificate) goal context,
      CandidateSound hoApplySymbol kb naf store obligation expansion := by
  intro expansion member
  unfold exFalso at member
  split at member
  · cases member
  · split at member
    · simp only [List.mem_singleton] at member
      subst member
      exact fixed_sound fun _ _ => Expansion.falsityElim_soundUnder
    · cases member

theorem ruleUse_sound (valid : store.Scoped) {fresh : List Variable} {rule : Term Variable Literal Symbol} :
    AttemptSound hoApplySymbol kb naf store obligation
      (ruleUse (Certificate := Certificate) hoApplySymbol obligation store fresh rule) := by
  unfold ruleUse
  split
  · exact attempt_sound valid (fun _ => ⟨rfl, by simp [Expansion.rigids, Expansion.impElim], rfl⟩)
      fun _ _ matched => Expansion.impElim_soundUnder_matched (Certificate := Certificate) matched.symm
  · intro _ found; cases found

theorem factUse_sound (valid : store.Scoped) {fresh : List Variable} {rule : Term Variable Literal Symbol} :
    AttemptSound hoApplySymbol kb naf store obligation
      (factUse (Certificate := Certificate) hoApplySymbol obligation store fresh rule) := by
  unfold factUse
  split
  · exact attempt_sound valid (fun _ => ⟨rfl, by simp [Expansion.rigids, Expansion.forallElim], rfl⟩)
      fun _ _ matched => Expansion.forallElim_soundUnder (Certificate := Certificate) matched.symm
  · intro _ found; cases found

theorem localAttempt_sound (valid : store.Scoped) (rule read : Term Variable Literal Symbol) :
    AttemptSound hoApplySymbol kb naf store obligation
      (localAttempt (Certificate := Certificate) hoApplySymbol obligation store goal avoid rule read) := by
  unfold localAttempt
  split
  · split
    · exact ruleUse_sound valid
    · split <;> (intro _ found; cases found)
  · split
    · exact factUse_sound valid
    · intro _ found; cases found
  · split
    · intro _ found; cases found
    · split <;> (intro _ found; cases found)

theorem clauseAttempt_sound (valid : store.Scoped) (reads : store.resolve obligation.goal = goal)
    {program : Program Variable Literal Symbol} {entry : ProgramClause Variable Literal Symbol}
    (inside : entry ∈ program.clauses) :
    AttemptSound hoApplySymbol program.kb naf store obligation
      (clauseAttempt (Certificate := Certificate) hoApplySymbol obligation store goal avoid entry) := by
  unfold clauseAttempt
  split
  · rename_i head body clauseEq
    split
    · exact attempt_sound valid (fun _ => ⟨rfl, by simp [Expansion.rigids, Expansion.clause], rfl⟩)
        fun _ _ matched => Expansion.clause_soundUnder ⟨entry, inside, clauseEq⟩ matched
    · intro _ found; cases found
  · rename_i body clauseEq
    split
    · intro expansion found
      cases found
      exact fixed_sound fun later refines => Expansion.goalClause_soundUnder ⟨entry, inside, clauseEq⟩
        (by rw [valid.read_refines reads refines]; exact Store.resolve_falsity _)
    · intro _ found; cases found

theorem atomResponse_sound (valid : store.Scoped) (reads : store.resolve obligation.goal = goal)
    {program : Program Variable Literal Symbol} :
    ∀ expansion ∈ (atomResponse (Certificate := Certificate) hoApplySymbol program obligation store goal
      (store.readContext obligation)).alternatives,
      CandidateSound hoApplySymbol program.kb naf store obligation expansion := by
  refine respond_sound fun candidate member => ?_
  simp only [List.mem_append] at member
  rcases member with ((identity | falso) | fromRule) | clause
  · exact identityAttempts_sound valid candidate identity
  · obtain ⟨expansion, inside, rfl⟩ := List.mem_map.mp falso
    intro _ same
    cases same
    exact exFalso_sound _ inside
  · obtain ⟨⟨rule, read⟩, _, rfl⟩ := List.mem_map.mp fromRule
    exact localAttempt_sound valid rule read
  · obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp clause
    exact clauseAttempt_sound valid reads entryMember

omit [DecidableEq Symbol] [DecidableEq Literal] in
/-- The introduction rules are sound: the goal reads as their connective in
every later store, and an eigenvariable is fresh for the read obligation there
(`Store.commit_fresh_resolved`). -/
theorem introductions_sound (valid : store.Scoped) (declared : obligation.Declared store)
    (reads : store.resolve obligation.goal = goal) {program : Program Variable Literal Symbol}
    {context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)}
    {intros : List (Expansion Variable Literal Symbol Certificate)}
    (found : introductions program store context goal = some intros) :
    ∀ expansion ∈ intros, CandidateSound hoApplySymbol kb naf store obligation expansion := by
  intro expansion member next woken committed later refines laterScoped
  have read := valid.read_refines reads ((Store.commit_refines committed).trans refines)
  cases goal <;> simp only [introductions, Option.some.injEq, reduceCtorEq] at found
  case disj left right =>
    have choices : expansion = .disjLeft left ∨ expansion = .disjRight right := by
      split at found <;> simp only [Option.some.injEq] at found <;> subst found <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      · exact .inl member
      · exact member
    rcases choices with rfl | rfl
    · exact Expansion.disjLeft_soundUnder read
    · exact Expansion.disjRight_soundUnder read
  all_goals subst found; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; subst member
  · exact Expansion.truth_soundUnder (by rw [read]; exact Store.resolve_truth _)
  · exact Expansion.conjIntro_soundUnder read
  · exact Expansion.impIntro_soundUnder read
  · exact Expansion.forallIntro_soundUnder read
      (Store.commit_fresh_resolved valid declared committed refines laterScoped
        (by simp [Expansion.rigids, Expansion.forallIntro])).1
  · exact Expansion.existsIntro_soundUnder read

theorem exactInstance?_spec {rule : Term Variable Literal Symbol} {count : Nat}
    {binder : Variable} {body witness : Term Variable Literal Symbol}
    (found : exactInstance? rule count goal = some (binder, body, witness)) :
    body.instantiate (Substitution.single binder witness) = goal := by
  unfold exactInstance? at found
  dsimp only at found
  repeat' split at found
  all_goals try cases found
  exact identical_eq _ _ ‹_›

theorem identities_sound (reads : store.resolve obligation.goal = goal) :
    ∀ expansion ∈ identities (Certificate := Certificate) goal (store.readContext obligation),
      CandidateSound hoApplySymbol kb naf store obligation expansion := by
  intro expansion member
  obtain ⟨⟨assumption, read⟩, inside, produced⟩ := List.mem_filterMap.mp member
  obtain ⟨assumed, readEq⟩ := Store.mem_readContext inside
  dsimp only at produced
  split at produced
  · rename_i same
    cases produced
    exact fixed_sound fun later refines =>
      Expansion.assumption_soundUnder assumed (refines.resolve_eq (reads.trans ((identical_eq _ _ same).trans readEq)))
  · cases produced

theorem exactCandidates_sound (reads : store.resolve obligation.goal = goal) :
    ∀ expansion ∈ exactCandidates (Certificate := Certificate) obligation goal (store.readContext obligation),
      CandidateSound hoApplySymbol kb naf store obligation expansion := by
  intro expansion member
  simp only [exactCandidates, List.mem_append, List.mem_flatMap, List.mem_filterMap] at member
  rcases member with (identity | falso) | ⟨_, _, _, _, produced⟩
  · exact identities_sound reads expansion identity
  · exact exFalso_sound expansion falso
  · unfold exactStep at produced
    split at produced
    · rename_i binder body witness found
      split at produced
      · cases produced
        exact fixed_sound fun _ _ => Expansion.forallElim_soundUnder (by rw [exactInstance?_spec found])
      · cases produced
    · cases produced

theorem compositeResponse_sound (valid : store.Scoped) (declared : obligation.Declared store)
    (reads : store.resolve obligation.goal = goal) {program : Program Variable Literal Symbol} :
    ∀ expansion ∈ (compositeResponse (Certificate := Certificate) program obligation store goal
      (store.readContext obligation)).alternatives,
      CandidateSound hoApplySymbol kb naf store obligation expansion := by
  intro expansion member
  unfold compositeResponse at member
  split at member
  · split at member
    · rename_i intros found
      exact introductions_sound valid declared reads found expansion member
    · cases member
  · rename_i first rest foundEq
    rw [Response.alternatives, ← foundEq] at member
    exact exactCandidates_sound reads expansion member

theorem respondTo_sound (valid : store.Scoped) (declared : obligation.Declared store)
    (reads : store.resolve obligation.goal = goal) {program : Program Variable Literal Symbol} :
    ∀ expansion ∈ (respondTo (Certificate := Certificate) hoApplySymbol program obligation store goal
      (store.readContext obligation)).alternatives,
      CandidateSound hoApplySymbol program.kb naf store obligation expansion := by
  intro expansion member
  unfold respondTo at member
  split at member
  · split at member
    · cases member
    · rename_i first rest foundEq
      rw [Response.alternatives, ← foundEq] at member
      exact exactCandidates_sound reads expansion member
  · split at member
    all_goals first
      | exact atomResponse_sound valid reads expansion member
      | exact compositeResponse_sound valid declared reads expansion member

/-- The command is sound for the KB its program denotes, whatever the NAF
provider: it builds no closed-world node. -/
theorem positive_sound (program : Program Variable Literal Symbol) :
    Command.Sound hoApplySymbol program.kb naf (positive (Certificate := Certificate) hoApplySymbol program) :=
  fun _ _ valid declared => respondTo_sound valid declared rfl

/-- A successful run of the command reconstructs `Derives` for its answer
instance: the goal and context read through the final answers. -/
theorem positive_reconstructs (program : Program Variable Literal Symbol) (fuel : Nat) (snapshot : Snapshot)
    (flexibles : List Variable) (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol)
    {resume : State Variable Literal Symbol Certificate Snapshot}
    {proof : CompletedProof Variable Literal Symbol Certificate Snapshot}
    (ran : run (positive hoApplySymbol program) fuel (State.init snapshot flexibles context goal) = .success proof resume) :
    Derives hoApplySymbol program.kb (context.map proof.store.resolve) (proof.store.resolve goal) naf :=
  run_init_reconstructs _ (positive_sound program) fuel snapshot flexibles context goal ran

/-- For a built program, the answer instance is derivable in `E(KB)`, the lowered
KB clauses with the generated signature clauses. -/
theorem positive_reconstructs_elaborated {signature : SignatureSnapshot Domain Symbol} {names : Nat → Variable}
    {rules : List (Rule Domain Symbol)} {sources : List (SourceClause Domain Variable Literal Symbol)}
    {program : Program Variable Literal Symbol}
    (built : Program.build hoApplySymbol signature names rules sources = .ok program)
    (listed : ∀ rule ∈ rules, signature.signature.data.definitions rule) (fuel : Nat) (snapshot : Snapshot)
    (flexibles : List Variable) (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol)
    {resume : State Variable Literal Symbol Certificate Snapshot}
    {proof : CompletedProof Variable Literal Symbol Certificate Snapshot}
    (ran : run (positive hoApplySymbol program) fuel (State.init snapshot flexibles context goal) = .success proof resume) :
    Derives hoApplySymbol (elaboratedKb signature names sources) (context.map proof.store.resolve)
      (proof.store.resolve goal) :=
  (positive_reconstructs (naf := NafFailure.disabled) program fuel snapshot flexibles context goal ran).positive_mono
    (Program.build_sound built listed)

/-! ## Clause selection and guards -/

omit [DecidableEq Symbol] [DecidableEq Literal] [FreshNames Variable] in
theorem waiting?_guard {program : Program Variable Literal Symbol} {name : Variable}
    (subject : guardSubject? program goal = some name) (unbound : store.assignable name = true) :
    waiting? program store goal = some name := by
  have notName : assignableName? store goal = none := by
    cases goal <;> simp_all [assignableName?, guardSubject?]
  simp [waiting?, notName, subject, unbound]

/-- A range guard on an unbound flexible name, an atom or an explicit domain
list's disjunction, delays on it, unless an exact candidate closes it, and the
delay is valid. -/
theorem positive_guard {program : Program Variable Literal Symbol} {name : Variable}
    (reads : store.resolve obligation.goal = goal) (subject : guardSubject? program goal = some name)
    (unbound : store.assignable name = true)
    (unclosed : exactCandidates (Certificate := Certificate) obligation goal (store.readContext obligation) = []) :
    positive (Certificate := Certificate) hoApplySymbol program obligation store = .delay [name] ∧
      store.delayable [name] = true := by
  refine ⟨?_, by simp [Store.delayable, unbound]⟩
  simp only [positive, respondTo, reads, waiting?_guard subject unbound, unclosed]

/-- A clause candidate renames every template name of its clause to a distinct
fresh flexible name, new to the store. -/
theorem clauseAttempt_fresh {entry : ProgramClause Variable Literal Symbol}
    {head : Atom Variable Literal Symbol} {body : List (Term Variable Literal Symbol)}
    (definite : entry.clause = .definite head body) {expansion : Expansion Variable Literal Symbol Certificate}
    (produced : clauseAttempt (Certificate := Certificate) hoApplySymbol obligation store goal avoid entry =
      some (some expansion)) :
    ∃ fresh bindings, expansion = Expansion.clause head body fresh bindings ∧
      fresh.map Prod.fst = (HornClause.definite head body).templates ∧ (fresh.map Prod.snd).Nodup ∧
      ∀ name ∈ fresh.map Prod.snd, store.info? name = none := by
  unfold clauseAttempt at produced
  rw [definite] at produced
  dsimp only at produced
  split at produced
  · unfold attempt at produced
    split at produced
    · rename_i bindings _
      simp only [Option.some.injEq] at produced
      exact ⟨_, bindings, produced.symm, Store.freshen_fst _ _ _, Store.freshen_nodup _ _ _,
        fun name member => (Store.freshen_fresh _ _ _ name member).1⟩
    all_goals cases produced
  · cases produced

omit [DecidableEq Symbol] [DecidableEq Literal] in
/-- Selecting a clause replaces the focus by its instantiated body, under the
obligation's own scope: no head is assumed. The frame above it is the clause's
FinishClause continuation. -/
theorem Expansion.clause_start (head : Atom Variable Literal Symbol) (body : List (Term Variable Literal Symbol))
    (fresh : List (Variable × Variable)) (bindings : List (Variable × Term Variable Literal Symbol))
    (frames : List (Continuation Variable Literal Symbol Certificate)) :
    (Expansion.clause (Certificate := Certificate) head body fresh bindings).start obligation frames =
      (.solve ⟨obligation.scope, (Term.conjunction body).instantiate (Substitution.rename fresh)⟩,
        .frame (Frame.start obligation (.clause (.definite head body) (fresh.map fun pair => (pair.1, .var pair.2)))
          { goal := (Term.conjunction body).instantiate (Substitution.rename fresh) } []) :: frames) := by
  simp [Expansion.start, Expansion.clause, Obligation.premise, Scope.enter]

omit [DecidableEq Symbol] [DecidableEq Literal] in
/-- The FinishClause continuation of `Expansion.clause_start` completes the
clause node on the body's proof: the clause and its renaming, the obligation,
the body premise, and its subproof. The frame is then removed, and a further
subproof would be refused (`Frame.feed_overfull`), so the node is built once. -/
theorem Expansion.clause_finish (head : Atom Variable Literal Symbol) (body : List (Term Variable Literal Symbol))
    (fresh : List (Variable × Variable)) (tree : ProofTree Variable Literal Symbol Certificate) :
    (Frame.start obligation (.clause (.definite head body) (fresh.map fun pair => (pair.1, .var pair.2)))
        { goal := (Term.conjunction body).instantiate (Substitution.rename fresh) } []).receive tree =
      .complete (.node (.clause (.definite head body) (fresh.map fun pair => (pair.1, .var pair.2))) obligation
        [{ goal := (Term.conjunction body).instantiate (Substitution.rename fresh) }] [tree]) := rfl

end AnthillModKbSpec.Machine
