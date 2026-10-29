import AnthillModKbSpec.Resolution.Machine.Reconstruction
import AnthillModKbSpec.Resolution.Machine.Unification
import AnthillModKbSpec.Resolution.Elaboration
import AnthillModKbSpec.Foundation.Monotonicity

namespace AnthillModKbSpec.Machine

open AdmissionSignature InductiveDomains

/-! # Ordinary clause selection and positive execution (S06)

The first executable command set of the machine. `positive` answers truth,
conjunction, disjunction, implication, and quantifier goals by their
introduction rules, closes goals by assumptions, instantiates local rules, and
selects clauses of an effective `Program` for atomic goals and denial clauses
for falsity. A range guard on an unbound flexible name delays instead of
enumerating ahead of the clause body.
Matching is the S05 matcher against the store each candidate's commit prepares;
`unsupported` and `violated` matches make the focus a gap and `mismatch` drops
the candidate. `positive_sound` proves the command sound, so a successful run
reconstructs `Derives` for its answer instance (`positive_reconstructs`). -/

variable {Domain Variable Literal Symbol Certificate Snapshot : Type}

/-! ## The effective program -/

/-- Where a program clause comes from. -/
inductive ClauseSource where
  /-- The KB clause at this index, lowered by `elaborateClause?`. -/
  | lowered (index : Nat)
  /-- A clause generated from the signature (`Elaboration.signatureKb`). -/
  | signature
  deriving DecidableEq, Repr

structure ProgramClause (Variable Literal Symbol : Type) where
  source : ClauseSource
  clause : HornClause Variable Literal Symbol

/-- An effective program: a finite clause list, in selection order, in place of
the set membership of `LogicalKb`. `guard` marks the membership symbols of range
guards: an atom over one of them whose argument reads as an unbound flexible name
delays rather than enumerating its range. Other atoms, including the member goal
a typed head appends after its body, select clauses as usual. -/
structure Program (Variable Literal Symbol : Type) where
  clauses : List (ProgramClause Variable Literal Symbol)
  guard : Symbol → Bool

/-- The KB a program denotes. -/
def Program.kb (program : Program Variable Literal Symbol) : LogicalKb Variable Literal Symbol :=
  fun clause => ∃ entry ∈ program.clauses, entry.clause = clause

/-- A KB clause as the formula generator supplies it: binder ranges and the
ranges of its implicit variables are generated with it, never inferred. -/
structure SourceClause (Domain Variable Literal Symbol : Type) where
  clause : HornClause Variable Literal Symbol
  ranges : Elaboration.Ranges Domain
  rangeOf : Variable → Range Domain

/-- A rejection by `elaborateClause?` (KB clause at an index) or `elaborate?`
(the query goal, or the assumption at an index). It is reported; no default
range replaces the rejected annotation. -/
inductive LoweringError where
  | clause (index : Nat)
  | goal
  | assumption (index : Nat)
  deriving DecidableEq, Repr

variable [DecidableEq Variable] [DecidableEq Symbol]

/-- Lower the KB clauses in order, from `index` on; the first rejection is reported. -/
def lowerClauses (hoApplySymbol : Symbol) (naming : Naming Domain Symbol) :
    Nat → List (SourceClause Domain Variable Literal Symbol) →
      Except LoweringError (List (ProgramClause Variable Literal Symbol))
  | _, [] => .ok []
  | index, source :: rest =>
      match Elaboration.elaborateClause? hoApplySymbol naming source.ranges source.rangeOf source.clause with
      | none => .error (.clause index)
      | some lowered =>
          match lowerClauses hoApplySymbol naming (index + 1) rest with
          | .ok clauses => .ok (⟨.lowered index, lowered⟩ :: clauses)
          | .error error => .error error

/-- The generated signature clauses, listed: one membership clause per listed
constructor rule, `D_all(x) :- member_D(x)` per declared domain, and one fact per
registered predicate. `signatureKb` is a set over every rule of the definitions;
the list is effective when `rules` lists them (`mem_signatureClauses`,
`signatureClauses_complete`). -/
def signatureClauses (snapshot : SignatureSnapshot Domain Symbol) (names : Nat → Variable)
    (rules : List (Rule Domain Symbol)) : List (HornClause Variable Literal Symbol) :=
  rules.map (membershipClause snapshot.signature.membershipSymbol names) ++
    snapshot.signature.data.domains.map (Elaboration.dataClause snapshot.naming (names 0)) ++
    snapshot.signature.predicates.map (Elaboration.predicateFact snapshot.naming)

/-- The membership symbols of the snapshot's guards: D_all, each declared
domain's, and each registered arity's. -/
def guardSymbol (snapshot : SignatureSnapshot Domain Symbol) (symbol : Symbol) : Bool :=
  symbol == snapshot.naming.dataSymbol ||
    snapshot.signature.data.domains.any (fun domain => snapshot.naming.membershipSymbol domain == symbol) ||
    snapshot.signature.predicates.any (fun declaration => snapshot.naming.predicateSymbol declaration.arity == symbol)

/-- The effective program of a KB: the lowered KB clauses, then the generated
signature clauses. A rejected KB clause is reported. -/
def Program.build (hoApplySymbol : Symbol) (snapshot : SignatureSnapshot Domain Symbol) (names : Nat → Variable)
    (rules : List (Rule Domain Symbol)) (sources : List (SourceClause Domain Variable Literal Symbol)) :
    Except LoweringError (Program Variable Literal Symbol) :=
  match lowerClauses hoApplySymbol snapshot.naming 0 sources with
  | .ok lowered => .ok ⟨lowered ++ (signatureClauses snapshot names rules).map (⟨.signature, ·⟩), guardSymbol snapshot⟩
  | .error error => .error error

/-- `E(KB)`: the lowered KB clauses and the generated signature clauses. -/
def elaboratedKb (snapshot : SignatureSnapshot Domain Symbol) (names : Nat → Variable)
    (sources : List (SourceClause Domain Variable Literal Symbol)) : LogicalKb Variable Literal Symbol :=
  fun clause =>
    (∃ source ∈ sources, Elaboration.elaborateClause snapshot.naming source.ranges source.rangeOf source.clause = clause) ∨
      clause ∈ Elaboration.signatureKb snapshot names

/-- Lower a query: each assumption with its own annotation child, as
`elaborateContext` does, then the goal. The first rejection is reported. -/
def lowerContext (hoApplySymbol : Symbol) (naming : Naming Domain Symbol) (ranges : Elaboration.Ranges Domain) :
    Nat → ProofContext Variable Literal Symbol → Except LoweringError (ProofContext Variable Literal Symbol)
  | _, [] => .ok []
  | index, assumption :: rest =>
      match Elaboration.elaborate? hoApplySymbol naming (Elaboration.child ranges index) assumption with
      | none => .error (.assumption index)
      | some lowered =>
          match lowerContext hoApplySymbol naming ranges (index + 1) rest with
          | .ok more => .ok (lowered :: more)
          | .error error => .error error

def lowerQuery (hoApplySymbol : Symbol) (naming : Naming Domain Symbol) (goalRanges contextRanges : Elaboration.Ranges Domain)
    (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    Except LoweringError (ProofContext Variable Literal Symbol × Formula Variable Literal Symbol) :=
  match lowerContext hoApplySymbol naming contextRanges 0 context with
  | .error error => .error error
  | .ok lowered =>
      match Elaboration.elaborate? hoApplySymbol naming goalRanges goal with
      | none => .error .goal
      | some loweredGoal => .ok (lowered, loweredGoal)

section Lowering

variable {hoApplySymbol : Symbol} {naming : Naming Domain Symbol}

/-- Accepted KB clauses are lowered in order, each by `elaborateClause`, and
every one was accepted by `elaborateClause?`. -/
theorem lowerClauses_ok : ∀ {index : Nat} {sources : List (SourceClause Domain Variable Literal Symbol)}
    {lowered : List (ProgramClause Variable Literal Symbol)},
    lowerClauses hoApplySymbol naming index sources = .ok lowered →
      lowered.map ProgramClause.clause =
          sources.map (fun source => Elaboration.elaborateClause naming source.ranges source.rangeOf source.clause) ∧
        ∀ source ∈ sources, Elaboration.clausePredicateRanged hoApplySymbol source.ranges source.rangeOf source.clause
  | _, [], _, lowered => by cases lowered; simp
  | index, source :: rest, result, lowered => by
      unfold lowerClauses at lowered
      split at lowered
      · cases lowered
      · rename_i clause accepted
        split at lowered
        · rename_i clauses restLowered
          cases lowered
          obtain ⟨checked, rfl⟩ := (Elaboration.elaborateClause?_eq_some _ _ _ _ _ _).mp accepted
          obtain ⟨same, restChecked⟩ := lowerClauses_ok restLowered
          refine ⟨by simp [same], fun other member => ?_⟩
          rcases List.mem_cons.mp member with rfl | inside
          · exact checked
          · exact restChecked other inside
        · cases lowered

/-- A rejection is reported at the index of a KB clause `elaborateClause?` rejects. -/
theorem lowerClauses_error : ∀ {index : Nat} {sources : List (SourceClause Domain Variable Literal Symbol)}
    {error : LoweringError},
    lowerClauses (Literal := Literal) hoApplySymbol naming index sources = .error error →
      ∃ offset source, error = .clause (index + offset) ∧ sources[offset]? = some source ∧
        Elaboration.elaborateClause? (Literal := Literal) hoApplySymbol naming source.ranges source.rangeOf
          source.clause = none
  | _, [], _, failed => by cases failed
  | index, source :: rest, error, failed => by
      unfold lowerClauses at failed
      split at failed
      · rename_i rejected
        cases failed
        exact ⟨0, source, rfl, rfl, rejected⟩
      · split at failed
        · cases failed
        · rename_i restError restFailed
          cases failed
          obtain ⟨offset, found, sameError, inside, rejected⟩ := lowerClauses_error restFailed
          exact ⟨offset + 1, found, by rw [sameError]; congr 1; omega, inside, rejected⟩

theorem lowerContext_ok {ranges : Elaboration.Ranges Domain} : ∀ {index : Nat}
    {context lowered : ProofContext Variable Literal Symbol},
    lowerContext hoApplySymbol naming ranges index context = .ok lowered →
      lowered = Elaboration.elaborateArgs naming ranges index context
  | _, [], _, lowered => by cases lowered; rfl
  | index, assumption :: rest, result, lowered => by
      unfold lowerContext at lowered
      split at lowered
      · cases lowered
      · rename_i term accepted
        split at lowered
        · rename_i more restLowered
          cases lowered
          obtain ⟨_, rfl⟩ := (Elaboration.elaborate?_eq_some _ _ _ _ _).mp accepted
          rw [lowerContext_ok restLowered]
          rfl
        · cases lowered

/-- An accepted query is the elaborated goal under the elaborated context. -/
theorem lowerQuery_ok {goalRanges contextRanges : Elaboration.Ranges Domain}
    {context lowered : ProofContext Variable Literal Symbol} {goal loweredGoal : Formula Variable Literal Symbol}
    (accepted : lowerQuery hoApplySymbol naming goalRanges contextRanges context goal = .ok (lowered, loweredGoal)) :
    lowered = Elaboration.elaborateContext naming contextRanges context ∧
      loweredGoal = Elaboration.elaborate naming goalRanges goal := by
  unfold lowerQuery at accepted
  split at accepted
  · cases accepted
  · rename_i contextLowered loweredContext
    split at accepted
    · cases accepted
    · rename_i term goalAccepted
      cases accepted
      exact ⟨lowerContext_ok loweredContext, ((Elaboration.elaborate?_eq_some _ _ _ _ _).mp goalAccepted).2.symm⟩

omit [DecidableEq Variable] [DecidableEq Symbol] in
theorem mem_signatureClauses {snapshot : SignatureSnapshot Domain Symbol} {names : Nat → Variable}
    {rules : List (Rule Domain Symbol)} (listed : ∀ rule ∈ rules, snapshot.signature.data.definitions rule)
    {clause : HornClause Variable Literal Symbol} (member : clause ∈ signatureClauses snapshot names rules) :
    clause ∈ Elaboration.signatureKb snapshot names := by
  simp only [signatureClauses, List.mem_append, List.mem_map] at member
  rcases member with (⟨rule, inside, rfl⟩ | ⟨domain, _, rfl⟩) | ⟨declaration, declared, rfl⟩
  · exact Or.inl ⟨rule, listed rule inside, rfl⟩
  · exact Or.inr (Or.inl ⟨domain, rfl⟩)
  · exact Or.inr (Or.inr ⟨declaration, declared, rfl⟩)

omit [DecidableEq Variable] [DecidableEq Symbol] in
theorem signatureClauses_complete {snapshot : SignatureSnapshot Domain Symbol} {names : Nat → Variable}
    {rules : List (Rule Domain Symbol)} (complete : ∀ rule, snapshot.signature.data.definitions rule → rule ∈ rules)
    {clause : HornClause Variable Literal Symbol} (member : clause ∈ Elaboration.signatureKb snapshot names) :
    clause ∈ signatureClauses snapshot names rules := by
  simp only [signatureClauses, List.mem_append, List.mem_map]
  rcases member with ⟨rule, declared, rfl⟩ | ⟨domain, rfl⟩ | ⟨declaration, declared, rfl⟩
  · exact .inl (.inl ⟨rule, complete rule declared, rfl⟩)
  · exact .inl (.inr ⟨domain, snapshot.signature.data.complete domain, rfl⟩)
  · exact .inr ⟨declaration, declared, rfl⟩

/-- Every clause of a built program is in `E(KB)`, when `rules` lists only
declared constructor rules. -/
theorem Program.build_sound {snapshot : SignatureSnapshot Domain Symbol} {names : Nat → Variable}
    {rules : List (Rule Domain Symbol)} {sources : List (SourceClause Domain Variable Literal Symbol)}
    {program : Program Variable Literal Symbol} (built : Program.build hoApplySymbol snapshot names rules sources = .ok program)
    (listed : ∀ rule ∈ rules, snapshot.signature.data.definitions rule) :
    ∀ clause ∈ program.kb, clause ∈ elaboratedKb snapshot names sources := by
  unfold Program.build at built
  split at built
  · rename_i lowered loweredOk
    cases built
    rintro clause ⟨entry, member, rfl⟩
    rcases List.mem_append.mp member with own | generated
    · left
      have same := (lowerClauses_ok loweredOk).1
      have inside : entry.clause ∈ lowered.map ProgramClause.clause := List.mem_map_of_mem own
      rw [same] at inside
      obtain ⟨source, sourceMember, same⟩ := List.mem_map.mp inside
      exact ⟨source, sourceMember, same⟩
    · right
      obtain ⟨generatedClause, inside, rfl⟩ := List.mem_map.mp generated
      exact mem_signatureClauses listed inside
  · cases built

/-- Every clause of `E(KB)` is in a built program, when `rules` lists every
declared constructor rule. -/
theorem Program.build_complete {snapshot : SignatureSnapshot Domain Symbol} {names : Nat → Variable}
    {rules : List (Rule Domain Symbol)} {sources : List (SourceClause Domain Variable Literal Symbol)}
    {program : Program Variable Literal Symbol} (built : Program.build hoApplySymbol snapshot names rules sources = .ok program)
    (complete : ∀ rule, snapshot.signature.data.definitions rule → rule ∈ rules) :
    ∀ clause ∈ elaboratedKb snapshot names sources, clause ∈ program.kb := by
  unfold Program.build at built
  split at built
  · rename_i lowered loweredOk
    cases built
    rintro clause (⟨source, sourceMember, rfl⟩ | generated)
    · have inside : Elaboration.elaborateClause snapshot.naming source.ranges source.rangeOf source.clause ∈
          lowered.map ProgramClause.clause := by
        rw [(lowerClauses_ok loweredOk).1]
        exact List.mem_map_of_mem sourceMember
      obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp inside
      exact ⟨entry, List.mem_append_left _ entryMember, same⟩
    · exact ⟨⟨.signature, clause⟩, List.mem_append_right _
        (List.mem_map_of_mem (signatureClauses_complete complete generated)), rfl⟩
  · cases built

/-- A KB clause that `elaborateClause?` rejects stops the build with a report;
it is never lowered with a default range. -/
theorem Program.build_rejected {snapshot : SignatureSnapshot Domain Symbol} {names : Nat → Variable}
    {rules : List (Rule Domain Symbol)} {sources : List (SourceClause Domain Variable Literal Symbol)}
    {source : SourceClause Domain Variable Literal Symbol} (member : source ∈ sources)
    (rejected : Elaboration.elaborateClause? (Literal := Literal) hoApplySymbol snapshot.naming source.ranges
      source.rangeOf source.clause = none) :
    ∃ index, Program.build (Literal := Literal) hoApplySymbol snapshot names rules sources = .error (.clause index) := by
  unfold Program.build
  split
  · rename_i lowered loweredOk
    have checked := (lowerClauses_ok loweredOk).2 source member
    have accepted := (Elaboration.elaborateClause?_eq_some hoApplySymbol snapshot.naming source.ranges source.rangeOf
      source.clause _).mpr ⟨checked, rfl⟩
    rw [rejected] at accepted
    cases accepted
  · rename_i error failed
    obtain ⟨offset, _, rfl, _, _⟩ := lowerClauses_error failed
    exact ⟨0 + offset, rfl⟩

end Lowering

/-! ## The command -/

section Command

variable [DecidableEq Literal] [FreshNames Variable]

/-- A computed candidate: `some (some e)` a candidate, `some none` a miss,
`none` a gap (an unsupported or violated match, or a capability this slice
lacks). -/
abbrev Attempt (Variable Literal Symbol Certificate : Type) := Option (Option (Expansion Variable Literal Symbol Certificate))

/-- A match as a candidate. -/
def attempt (result : Unification Variable Literal Symbol)
    (make : List (Variable × Term Variable Literal Symbol) → Expansion Variable Literal Symbol Certificate) :
    Attempt Variable Literal Symbol Certificate :=
  match result with
  | .unified _ bindings => some (some (make bindings))
  | .mismatch => some none
  | .unsupported | .violated => none

/-- The index of atomic and falsity goals: the same symbol and arity, or both
falsity. A candidate is matched only against a goal it can conclude. -/
def sameHead : Term Variable Literal Symbol → Term Variable Literal Symbol → Bool
  | .app left leftArgs, .app right rightArgs => decide (left = right) && leftArgs.length == rightArgs.length
  | .falsity, .falsity => true
  | _, _ => false

/-- An application by `ho_apply` against a direct one of the matching arity, or
the reverse: comparing them needs `ho_apply` conversion (S11), so a candidate
between them is a gap. -/
def hoMixed (hoApplySymbol : Symbol) : Term Variable Literal Symbol → Term Variable Literal Symbol → Bool
  | .app left leftArgs, .app right rightArgs =>
      (decide (left = hoApplySymbol) && decide (right ≠ hoApplySymbol) && leftArgs.length == rightArgs.length + 1) ||
        (decide (right = hoApplySymbol) && decide (left ≠ hoApplySymbol) && rightArgs.length == leftArgs.length + 1)
  | _, _ => false

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
  | _, conclusion => sameHead goal conclusion || hoMixed hoApplySymbol goal conclusion

/-- The command's reading of the context: each assumption with its reading. -/
def Store.readContext (store : Store Variable Literal Symbol) (obligation : Obligation Variable Literal Symbol) :
    List (Term Variable Literal Symbol × Term Variable Literal Symbol) :=
  obligation.scope.assumptions.map fun assumption => (assumption, store.resolve assumption)

omit [DecidableEq Symbol] [DecidableEq Literal] in
theorem Store.mem_readContext {store : Store Variable Literal Symbol} {obligation : Obligation Variable Literal Symbol}
    {pair : Term Variable Literal Symbol × Term Variable Literal Symbol} (member : pair ∈ store.readContext obligation) :
    pair.1 ∈ obligation.scope.assumptions ∧ pair.2 = store.resolve pair.1 := by
  obtain ⟨assumption, inside, rfl⟩ := List.mem_map.mp member
  exact ⟨inside, rfl⟩

/-- The candidates of the attempts; any gap makes the response incomplete. -/
def respond (attempts : List (Attempt Variable Literal Symbol Certificate)) : Response Variable Literal Symbol Certificate :=
  if attempts.any Option.isNone then .incomplete ((attempts.filterMap id).filterMap id)
  else .candidates ((attempts.filterMap id).filterMap id)

/-- Identity: the goal matched against an assumption it can be. -/
def identityAttempts (hoApplySymbol : Symbol) (obligation : Obligation Variable Literal Symbol)
    (store : Store Variable Literal Symbol) (goal : Term Variable Literal Symbol)
    (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    List (Attempt Variable Literal Symbol Certificate) :=
  context.filterMap fun (assumption, read) =>
    if sameHead goal read then
      some (attempt ((store.prepare obligation [] []).unify obligation.scope hoApplySymbol obligation.goal assumption)
        fun bindings => Expansion.assumption bindings)
    else if hoMixed hoApplySymbol goal read then some none
    else none

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

/-- Fresh flexible witnesses for a local rule's leading binders: new to the
store, and avoiding the binder names the obligation reads and the rule's own. -/
def Store.witnessesFor (store : Store Variable Literal Symbol) (avoid : List Variable)
    (rule : Term Variable Literal Symbol) : List Variable :=
  (store.freshen (leadingBinders rule) (avoid ++ rule.binderNames)).map Prod.snd

/-- A local rule `∀x̄. (B → H)` with fresh witnesses: `H'` matched against the
goal; the premises are the instance `B' → H'` and `B'`. -/
def ruleUse (hoApplySymbol : Symbol) (obligation : Obligation Variable Literal Symbol)
    (store : Store Variable Literal Symbol) (fresh : List Variable) (rule : Term Variable Literal Symbol) :
    Option (Attempt Variable Literal Symbol Certificate) :=
  match rule.instantiateLeading (fresh.map Term.var) with
  | some (.imp condition conclusion) =>
      some (attempt ((store.prepare obligation fresh []).unify obligation.scope hoApplySymbol conclusion obligation.goal)
        fun bindings => { Expansion.impElim condition conclusion with flexibles := fresh, bindings := bindings })
  | _ => none

/-- A universal fact `∀x₁…xₙ. H` (n ≥ 1) with fresh witnesses: the instance of
`H` matched against the goal, eliminating the last binder; the premise is the
fact with the other binders instantiated. -/
def factUse (hoApplySymbol : Symbol) (obligation : Obligation Variable Literal Symbol)
    (store : Store Variable Literal Symbol) (goal : Term Variable Literal Symbol) (fresh : List Variable)
    (rule : Term Variable Literal Symbol) : Option (Attempt Variable Literal Symbol Certificate) :=
  match rule.instantiateLeading (fresh.dropLast.map Term.var), fresh.getLast? with
  | some (.forallVar binder body), some witness =>
      if sameHead goal (body.instantiate (Substitution.single binder (.var witness))) then
        some (attempt ((store.prepare obligation fresh []).unify obligation.scope hoApplySymbol
            (body.instantiate (Substitution.single binder (.var witness))) obligation.goal)
          fun bindings => { Expansion.forallElim binder body (.var witness) with flexibles := fresh, bindings := bindings })
      else if hoMixed hoApplySymbol goal (body.instantiate (Substitution.single binder (.var witness))) then some none
      else none
  | _, _ => none

/-- A local rule `∀x₁…xₙ. M`, as written, for an atomic or falsity goal. Its
free names are captured parameters and are kept; its leading binders get fresh
witnesses (`Store.witnessesFor`). An implication matrix is used by `ruleUse`, an
atomic one with n ≥ 1 by `factUse` (n = 0 is identity). Either instance is
proved from the rule by exact steps (`exactStep`). Each shape is filtered by its
head before any name is freshened. A rule or assumption of another shape from
which the goal might follow (`mayConclude`), or whose head differs only by
`ho_apply`, is a gap: left rules and compound conclusions are S09's. -/
def localAttempt (hoApplySymbol : Symbol) (obligation : Obligation Variable Literal Symbol)
    (store : Store Variable Literal Symbol) (goal : Term Variable Literal Symbol) (avoid : List Variable)
    (rule : Term Variable Literal Symbol) : Option (Attempt Variable Literal Symbol Certificate) :=
  match Matrix.of (stripLeading (leadingBinders rule).length rule) with
  | .implication head =>
      if sameHead goal head then ruleUse hoApplySymbol obligation store (store.witnessesFor avoid rule) rule
      else if hoMixed hoApplySymbol goal head || mayConclude hoApplySymbol goal (leadingBinders rule) head then some none
      else none
  | .atomic =>
      if (leadingBinders rule).isEmpty then none
      else factUse hoApplySymbol obligation store goal (store.witnessesFor avoid rule) rule
  | .other =>
      if mayConclude hoApplySymbol goal (leadingBinders rule) (stripLeading (leadingBinders rule).length rule) then
        some none
      else none

def localAttempts (hoApplySymbol : Symbol) (obligation : Obligation Variable Literal Symbol)
    (store : Store Variable Literal Symbol) (goal : Term Variable Literal Symbol) (avoid : List Variable) :
    List (Attempt Variable Literal Symbol Certificate) :=
  obligation.scope.assumptions.filterMap (localAttempt hoApplySymbol obligation store goal avoid)

/-- A program clause, indexed by head symbol and arity: every template name
renamed to a fresh flexible name, the renamed head matched against the goal, and
the renamed body the one premise. A head that differs from the goal only by
`ho_apply` is a gap. A denial clause `⊥ :- body` serves a goal that reads as
falsity, with nothing to match. The head is never assumed. -/
def clauseAttempt (hoApplySymbol : Symbol) (obligation : Obligation Variable Literal Symbol)
    (store : Store Variable Literal Symbol) (goal : Term Variable Literal Symbol) (avoid : List Variable)
    (entry : ProgramClause Variable Literal Symbol) : Option (Attempt Variable Literal Symbol Certificate) :=
  match entry.clause with
  | .definite head body =>
      if sameHead goal head then
        let fresh := store.freshen (HornClause.definite head body).templates
          (avoid ++ (head :: body).flatMap Term.binderNames)
        some (attempt ((store.prepare obligation (fresh.map Prod.snd) []).unify obligation.scope hoApplySymbol
            (head.instantiate (Substitution.rename fresh)) obligation.goal)
          fun bindings => Expansion.clause head body fresh bindings)
      else if hoMixed hoApplySymbol goal head then some none
      else none
  | .goal body =>
      match goal with
      | .falsity =>
          some (some (some (Expansion.goalClause body
            (store.freshen (HornClause.goal body).templates (avoid ++ body.flatMap Term.binderNames)))))
      | _ => none

/-- An atomic or falsity goal: identity, ex falso, local rules, then program
clauses, in that order. A gap among them makes the response incomplete. -/
def atomResponse (hoApplySymbol : Symbol) (program : Program Variable Literal Symbol)
    (obligation : Obligation Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (goal : Term Variable Literal Symbol) (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol))
    (avoid : List Variable) : Response Variable Literal Symbol Certificate :=
  respond (identityAttempts hoApplySymbol obligation store goal context ++
    (exFalso goal context).map (some ∘ some) ++ localAttempts hoApplySymbol obligation store goal avoid ++
    program.clauses.filterMap (clauseAttempt hoApplySymbol obligation store goal avoid))

/-- The disjunction a range guard over an explicit domain list ends with:
`m(t) ∨ false`. Its `false` alternative is never tried: a guard is a membership
check, not a request for contradiction search. -/
def guardTail (program : Program Variable Literal Symbol) : Term Variable Literal Symbol → Bool
  | .disj (.app symbol [_]) .falsity => program.guard symbol
  | _ => false

/-- The introduction rules of a connective goal. Other goals (equality, NAF,
calls, rigid names, literals) have none in this slice. -/
def introductions (program : Program Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (avoid : List Variable) : Term Variable Literal Symbol → Option (List (Expansion Variable Literal Symbol Certificate))
  | .truth => some [.truth]
  | .conj left right => some [.conjIntro left right]
  | .disj left right =>
      if guardTail program (.disj left right) then some [.disjLeft left] else some [.disjLeft left, .disjRight right]
  | .imp premise conclusion => some [.impIntro premise conclusion]
  | .forallVar binder body => some [.forallIntro binder body (store.freshFor avoid)]
  | .existsVar binder body => some [.existsIntro binder body (store.freshFor avoid)]
  | _ => none

/-- The same outermost form, or a pattern name that may stand for anything: a
cheap filter before `extract`. -/
def sameForm (patterns : List Variable) : Term Variable Literal Symbol → Term Variable Literal Symbol → Bool
  | .var name, target => decide (name ∈ patterns) || identical (.var name) target
  | .app left leftArgs, .app right rightArgs => decide (left = right) && leftArgs.length == rightArgs.length
  | .forallVar left _, .forallVar right _ | .existsVar left _, .existsVar right _ => decide (left = right)
  | .lit left, .lit right => decide (left = right)
  | .truth, .truth | .falsity, .falsity | .conj _ _, .conj _ _ | .disj _ _, .disj _ _ | .imp _ _, .imp _ _
  | .equal _ _, .equal _ _ | .defaultNeg _, .defaultNeg _ | .dictionaryCall _ _ _ _, .dictionaryCall _ _ _ _ => true
  | _, _ => false

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
  if sameForm binders (stripLeading count rule) goal then
    match extract binders (stripLeading count rule) goal [] with
    | none => none
    | some found =>
        let witnesses := binders.map fun name => (OperationDictionaries.lookup found name).getD .truth
        match rule.instantiateLeading witnesses.dropLast, witnesses.getLast? with
        | some (.forallVar binder body), some witness =>
            if identical (body.instantiate (Substitution.single binder witness)) goal then some (binder, body, witness)
            else none
        | _, _ => none
  else none

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

/-- Candidates a non-atomic goal needs no match for: an assumption it reads as,
ex falso, and exact universal eliminations from local rules. -/
def exactCandidates (obligation : Obligation Variable Literal Symbol) (goal : Term Variable Literal Symbol)
    (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    List (Expansion Variable Literal Symbol Certificate) :=
  identities goal context ++ exFalso goal context ++
    obligation.scope.assumptions.flatMap fun assumption =>
      (List.range (leadingBinders assumption).length).filterMap fun index =>
        exactStep obligation assumption (index + 1)

/-- A non-atomic goal: an assumption it reads as, ex falso, or an exact instance
of a local rule closes it without introduction; otherwise its introduction
rules, or a gap. A local rule's instance (`B' → H'`, or the rule after some
binders) is therefore proved from the rule alone and never reopened by
introduction. No match is asked to compare binders, so no gap comes from
matching here. -/
def compositeResponse (program : Program Variable Literal Symbol) (obligation : Obligation Variable Literal Symbol)
    (store : Store Variable Literal Symbol) (goal : Term Variable Literal Symbol)
    (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) (avoid : List Variable) :
    Response Variable Literal Symbol Certificate :=
  match exactCandidates obligation goal context with
  | [] =>
      match introductions program store avoid goal with
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
def waiting? (program : Program Variable Literal Symbol) (store : Store Variable Literal Symbol) :
    Term Variable Literal Symbol → Option Variable
  | .var name => if store.assignable name then some name else none
  | goal =>
      match guardSubject? program goal with
      | some name => if store.assignable name then some name else none
      | none => none

/-- The response to a goal read as `goal` under the context read as `context`.
A goal that would wait is first closed by an assumption it reads as, if any. -/
def respondTo (hoApplySymbol : Symbol) (program : Program Variable Literal Symbol)
    (obligation : Obligation Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (goal : Term Variable Literal Symbol) (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) :
    Response Variable Literal Symbol Certificate :=
  let avoid := (goal :: context.map Prod.snd).flatMap Term.binderNames
  match waiting? program store goal with
  | some name =>
      match identities goal context with
      | [] => .delay [name]
      | first :: rest => .candidates (first :: rest)
  | none =>
      match goal with
      | .app _ _ | .falsity => atomResponse hoApplySymbol program obligation store goal context avoid
      | _ => compositeResponse program obligation store goal context avoid

/-- Ordinary clause selection and positive execution. The goal and the context
are read through the store once; a guard on an unbound name delays until a later
goal binds it, and still delayed at the end it flounders. -/
def positive (hoApplySymbol : Symbol) (program : Program Variable Literal Symbol) :
    Command Variable Literal Symbol Certificate := fun obligation store =>
  respondTo hoApplySymbol program obligation store (store.resolve obligation.goal) (store.readContext obligation)

/-! ## Soundness of the command -/

variable {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}
  {obligation : Obligation Variable Literal Symbol} {store : Store Variable Literal Symbol}
  {goal : Term Variable Literal Symbol} {avoid : List Variable}

def AttemptSound (hoApplySymbol : Symbol) (kb : LogicalKb Variable Literal Symbol) (naf : NafFailure Variable Literal Symbol)
    (store : Store Variable Literal Symbol) (obligation : Obligation Variable Literal Symbol)
    (candidate : Attempt Variable Literal Symbol Certificate) : Prop :=
  ∀ expansion, candidate = some (some expansion) → CandidateSound hoApplySymbol kb naf store obligation expansion

/-- A commit replaying a match against its prepared store makes the two sides
read the same. -/
theorem Store.commit_matched {final next : Store Variable Literal Symbol} (valid : store.Scoped)
    {flexibles rigids : List Variable} {premises : List (Premise Variable Literal Symbol)}
    {left right : Term Variable Literal Symbol} {bindings : List (Variable × Term Variable Literal Symbol)}
    {woken : List (Suspension Variable Literal Symbol)}
    (computed : (store.prepare obligation flexibles rigids).unify obligation.scope hoApplySymbol left right =
      .unified final bindings)
    (committed : store.commit obligation flexibles rigids premises bindings = .committed next woken) :
    next.resolve left = next.resolve right := by
  obtain ⟨accepted, _⟩ := Store.commit_checks committed
  obtain ⟨replayed, same⟩ := Store.commit_unify valid accepted computed
  rw [committed] at replayed
  cases replayed
  exact same

omit [DecidableEq Symbol] [DecidableEq Literal] in
/-- A candidate is sound when its contract holds in every refinement of the
store it was computed against. -/
theorem fixed_sound {expansion : Expansion Variable Literal Symbol Certificate}
    (holds : ∀ later : Store Variable Literal Symbol, store.Refines later →
      NodeSound hoApplySymbol kb naf later obligation expansion.premises) :
    CandidateSound hoApplySymbol kb naf store obligation expansion :=
  fun _ _ committed later refines _ => holds later ((Store.commit_refines committed).trans refines)

/-- A match-built candidate is sound when its contract holds wherever the
matched sides read the same. -/
theorem attempt_sound (valid : store.Scoped) {flexibles : List Variable} {left right : Term Variable Literal Symbol}
    {make : List (Variable × Term Variable Literal Symbol) → Expansion Variable Literal Symbol Certificate}
    (shape : ∀ bindings, (make bindings).flexibles = flexibles ∧ (make bindings).rigids = [] ∧
      (make bindings).bindings = bindings)
    (matched : ∀ bindings (later : Store Variable Literal Symbol), later.resolve left = later.resolve right →
      NodeSound hoApplySymbol kb naf later obligation (make bindings).premises) :
    AttemptSound hoApplySymbol kb naf store obligation
      (attempt ((store.prepare obligation flexibles []).unify obligation.scope hoApplySymbol left right) make) := by
  intro expansion found next woken committed later refines _
  unfold attempt at found
  split at found
  · rename_i final bindings computed
    cases found
    obtain ⟨sameFlexibles, noRigids, sameBindings⟩ := shape bindings
    rw [sameFlexibles, noRigids, sameBindings] at committed
    exact matched bindings later (refines.resolve_eq (Store.commit_matched valid computed committed))
  all_goals cases found

omit [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal] [FreshNames Variable] in
theorem mem_found {attempts : List (Attempt Variable Literal Symbol Certificate)}
    {expansion : Expansion Variable Literal Symbol Certificate} (member : expansion ∈ (attempts.filterMap id).filterMap id) :
    some (some expansion) ∈ attempts := by
  simp only [List.mem_filterMap, id_eq] at member
  obtain ⟨_, ⟨_, inside, rfl⟩, rfl⟩ := member
  exact inside

omit [DecidableEq Symbol] [DecidableEq Literal] in
theorem respond_sound {attempts : List (Attempt Variable Literal Symbol Certificate)}
    (attemptsSound : ∀ candidate ∈ attempts, AttemptSound hoApplySymbol kb naf store obligation candidate) :
    ∀ expansion ∈ (respond attempts).alternatives, CandidateSound hoApplySymbol kb naf store obligation expansion := by
  intro expansion member
  unfold respond at member
  split at member <;>
    exact attemptsSound _ (mem_found (by simpa [Response.alternatives] using member)) expansion rfl

theorem identityAttempts_sound (valid : store.Scoped)
    {context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)}
    (reads : context = store.readContext obligation) :
    ∀ candidate ∈ identityAttempts (Certificate := Certificate) hoApplySymbol obligation store goal context,
      AttemptSound hoApplySymbol kb naf store obligation candidate := by
  intro candidate member
  simp only [identityAttempts, List.mem_filterMap] at member
  obtain ⟨pair, inside, produced⟩ := member
  have assumed := (Store.mem_readContext (reads ▸ inside)).1
  split at produced
  · cases produced
    exact attempt_sound valid (fun _ => ⟨rfl, by simp [Expansion.rigids, Expansion.assumption], rfl⟩)
      fun _ _ matched => Expansion.assumption_soundUnder assumed matched
  · split at produced
    · cases produced; intro _ found; cases found
    · cases produced

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

theorem ruleUse_sound (valid : store.Scoped) {fresh : List Variable} {rule : Term Variable Literal Symbol}
    {candidate : Attempt Variable Literal Symbol Certificate}
    (produced : ruleUse hoApplySymbol obligation store fresh rule = some candidate) :
    AttemptSound hoApplySymbol kb naf store obligation candidate := by
  unfold ruleUse at produced
  split at produced
  · cases produced
    exact attempt_sound valid (fun _ => ⟨rfl, by simp [Expansion.rigids, Expansion.impElim], rfl⟩)
      fun _ _ matched => Expansion.impElim_soundUnder_matched (Certificate := Certificate) matched.symm
  · cases produced

theorem factUse_sound (valid : store.Scoped) {fresh : List Variable} {rule : Term Variable Literal Symbol}
    {candidate : Attempt Variable Literal Symbol Certificate}
    (produced : factUse hoApplySymbol obligation store goal fresh rule = some candidate) :
    AttemptSound hoApplySymbol kb naf store obligation candidate := by
  unfold factUse at produced
  split at produced
  · split at produced
    · cases produced
      exact attempt_sound valid (fun _ => ⟨rfl, by simp [Expansion.rigids, Expansion.forallElim], rfl⟩)
        fun _ _ matched => Expansion.forallElim_soundUnder (Certificate := Certificate) matched.symm
    · split at produced
      · cases produced; intro _ found; cases found
      · cases produced
  · cases produced

theorem localAttempts_sound (valid : store.Scoped) :
    ∀ candidate ∈ localAttempts (Certificate := Certificate) hoApplySymbol obligation store goal avoid,
      AttemptSound hoApplySymbol kb naf store obligation candidate := by
  intro candidate member
  simp only [localAttempts, List.mem_filterMap] at member
  obtain ⟨_, _, produced⟩ := member
  unfold localAttempt at produced
  split at produced
  · split at produced
    · exact ruleUse_sound valid produced
    · split at produced
      · cases produced; intro _ found; cases found
      · cases produced
  · split at produced
    · cases produced
    · exact factUse_sound valid produced
  · split at produced
    · cases produced; intro _ found; cases found
    · cases produced

theorem clauseAttempt_sound (valid : store.Scoped) (reads : store.resolve obligation.goal = goal)
    {program : Program Variable Literal Symbol} {entry : ProgramClause Variable Literal Symbol}
    (inside : entry ∈ program.clauses) {candidate : Attempt Variable Literal Symbol Certificate}
    (produced : clauseAttempt hoApplySymbol obligation store goal avoid entry = some candidate) :
    AttemptSound hoApplySymbol program.kb naf store obligation candidate := by
  unfold clauseAttempt at produced
  split at produced
  · rename_i head body clauseEq
    split at produced
    · cases produced
      exact attempt_sound valid (fun _ => ⟨rfl, by simp [Expansion.rigids, Expansion.clause], rfl⟩)
        fun _ _ matched => Expansion.clause_soundUnder ⟨entry, inside, clauseEq⟩ matched
    · split at produced
      · cases produced; intro _ found; cases found
      · cases produced
  · rename_i body clauseEq
    split at produced
    · cases produced
      intro expansion found
      cases found
      exact fixed_sound fun later refines => Expansion.goalClause_soundUnder ⟨entry, inside, clauseEq⟩
        (by rw [valid.read_refines reads refines]; exact Store.resolve_falsity _)
    · cases produced

theorem atomResponse_sound (valid : store.Scoped) (reads : store.resolve obligation.goal = goal)
    {context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)}
    (contextReads : context = store.readContext obligation) {program : Program Variable Literal Symbol} :
    ∀ expansion ∈ (atomResponse (Certificate := Certificate) hoApplySymbol program obligation store goal context
      avoid).alternatives,
      CandidateSound hoApplySymbol program.kb naf store obligation expansion := by
  refine respond_sound fun candidate member => ?_
  simp only [List.mem_append] at member
  rcases member with ((identity | falso) | fromRule) | clause
  · exact identityAttempts_sound valid contextReads candidate identity
  · obtain ⟨expansion, inside, rfl⟩ := List.mem_map.mp falso
    intro _ same
    cases same
    exact exFalso_sound _ inside
  · exact localAttempts_sound valid candidate fromRule
  · obtain ⟨entry, entryMember, produced⟩ := List.mem_filterMap.mp clause
    exact clauseAttempt_sound valid reads entryMember produced

omit [DecidableEq Symbol] [DecidableEq Literal] in
/-- The introduction rules are sound: the goal reads as their connective in
every later store, and an eigenvariable is fresh for the read obligation there
(`Store.commit_fresh_resolved`). -/
theorem introductions_sound (valid : store.Scoped) (declared : obligation.Declared store)
    (reads : store.resolve obligation.goal = goal) {program : Program Variable Literal Symbol}
    {intros : List (Expansion Variable Literal Symbol Certificate)}
    (found : introductions program store avoid goal = some intros) :
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
  split at found
  · split at found
    · cases found
    · split at found
      · split at found
        · rename_i same
          cases found
          exact identical_eq _ _ same
        · cases found
      · cases found
  · cases found

theorem identities_sound {context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)}
    (reads : store.resolve obligation.goal = goal) (contextReads : context = store.readContext obligation) :
    ∀ expansion ∈ identities (Certificate := Certificate) goal context,
      CandidateSound hoApplySymbol kb naf store obligation expansion := by
  intro expansion member
  simp only [identities, List.mem_filterMap] at member
  obtain ⟨pair, inside, produced⟩ := member
  obtain ⟨assumed, readEq⟩ := Store.mem_readContext (contextReads ▸ inside)
  split at produced
  · rename_i same
    cases produced
    exact fixed_sound fun later refines =>
      Expansion.assumption_soundUnder assumed (refines.resolve_eq (reads.trans ((identical_eq _ _ same).trans readEq)))
  · cases produced

theorem exactCandidates_sound {context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)}
    (reads : store.resolve obligation.goal = goal) (contextReads : context = store.readContext obligation) :
    ∀ expansion ∈ exactCandidates (Certificate := Certificate) obligation goal context,
      CandidateSound hoApplySymbol kb naf store obligation expansion := by
  intro expansion member
  simp only [exactCandidates, List.mem_append, List.mem_flatMap, List.mem_filterMap] at member
  rcases member with (identity | falso) | ⟨_, _, _, _, produced⟩
  · exact identities_sound reads contextReads expansion identity
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
    (reads : store.resolve obligation.goal = goal) {context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)}
    (contextReads : context = store.readContext obligation) {program : Program Variable Literal Symbol} :
    ∀ expansion ∈ (compositeResponse (Certificate := Certificate) program obligation store goal context avoid).alternatives,
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
    exact exactCandidates_sound reads contextReads expansion member

theorem respondTo_sound (valid : store.Scoped) (declared : obligation.Declared store)
    (reads : store.resolve obligation.goal = goal) {context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)}
    (contextReads : context = store.readContext obligation) {program : Program Variable Literal Symbol} :
    ∀ expansion ∈ (respondTo (Certificate := Certificate) hoApplySymbol program obligation store goal context).alternatives,
      CandidateSound hoApplySymbol program.kb naf store obligation expansion := by
  intro expansion member
  unfold respondTo at member
  dsimp only at member
  split at member
  · split at member
    · cases member
    · rename_i first rest foundEq
      rw [Response.alternatives, ← foundEq] at member
      exact identities_sound reads contextReads expansion member
  · split at member
    all_goals first
      | exact atomResponse_sound valid reads contextReads expansion member
      | exact compositeResponse_sound valid declared reads contextReads expansion member

/-- The command is sound for the KB its program denotes, whatever the NAF
provider: it builds no closed-world node. -/
theorem positive_sound (program : Program Variable Literal Symbol) :
    Command.Sound hoApplySymbol program.kb naf (positive (Certificate := Certificate) hoApplySymbol program) :=
  fun _ _ valid declared => respondTo_sound valid declared rfl rfl

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
  unfold waiting?
  split
  · simp [guardSubject?] at subject
  · simp [subject, unbound]

/-- A range guard on an unbound flexible name, an atom or an explicit domain
list's disjunction, delays on it, unless an assumption it reads as closes it,
and the delay is valid. -/
theorem positive_guard {program : Program Variable Literal Symbol} {name : Variable}
    (reads : store.resolve obligation.goal = goal) (subject : guardSubject? program goal = some name)
    (unbound : store.assignable name = true)
    (unassumed : identities (Certificate := Certificate) goal (store.readContext obligation) = []) :
    positive (Certificate := Certificate) hoApplySymbol program obligation store = .delay [name] ∧
      store.delayable [name] = true := by
  refine ⟨?_, by simp [Store.delayable, unbound]⟩
  simp only [positive, respondTo, reads, waiting?_guard subject unbound, unassumed]

/-- A clause candidate renames every template name of its clause to a distinct
fresh flexible name, new to the store. -/
theorem clauseAttempt_fresh {entry : ProgramClause Variable Literal Symbol}
    {head : Atom Variable Literal Symbol} {body : List (Term Variable Literal Symbol)}
    (definite : entry.clause = .definite head body) {expansion : Expansion Variable Literal Symbol Certificate}
    (produced : clauseAttempt (Certificate := Certificate) hoApplySymbol obligation store goal avoid entry =
      some (some (some expansion))) :
    ∃ fresh bindings, expansion = Expansion.clause head body fresh bindings ∧
      fresh.map Prod.fst = (HornClause.definite head body).templates ∧ (fresh.map Prod.snd).Nodup ∧
      ∀ name ∈ fresh.map Prod.snd, store.info? name = none := by
  unfold clauseAttempt at produced
  rw [definite] at produced
  dsimp only at produced
  split at produced
  · simp only [Option.some.injEq] at produced
    unfold attempt at produced
    split at produced
    · rename_i bindings _
      simp only [Option.some.injEq] at produced
      exact ⟨_, bindings, produced.symm, Store.freshen_fst _ _ _, Store.freshen_nodup _ _ _,
        fun name member => (Store.freshen_fresh _ _ _ name member).1⟩
    all_goals cases produced
  · split at produced <;> cases produced

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

end Command

end AnthillModKbSpec.Machine
