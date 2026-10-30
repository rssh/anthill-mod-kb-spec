import AnthillModKbSpec.Resolution.Elaboration

namespace AnthillModKbSpec.Machine

open AdmissionSignature InductiveDomains

/-! # Effective programs (S06)

A finite clause list in selection order, in place of the set membership of
`LogicalKb`: the KB clauses lowered by `elaborateClause?` with the generated
signature clauses. Range annotations come from the formula generator; a
rejection by `elaborateClause?` or `elaborate?` is reported (`LoweringError`),
never replaced by a default. `Program.build_sound` and `Program.build_complete`
relate a built program to `E(KB)` (`elaboratedKb`). -/

variable {Domain Variable Literal Symbol : Type}

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
def guardSymbols (snapshot : SignatureSnapshot Domain Symbol) : List Symbol :=
  snapshot.naming.dataSymbol :: snapshot.signature.data.domains.map snapshot.naming.membershipSymbol ++
    snapshot.signature.predicates.map fun declaration => snapshot.naming.predicateSymbol declaration.arity

def guardSymbol (snapshot : SignatureSnapshot Domain Symbol) (symbol : Symbol) : Bool :=
  (guardSymbols snapshot).contains symbol

/-- The effective program of a KB: the lowered KB clauses, then the generated
signature clauses. A rejected KB clause is reported. -/
def Program.build (hoApplySymbol : Symbol) (snapshot : SignatureSnapshot Domain Symbol) (names : Nat → Variable)
    (rules : List (Rule Domain Symbol)) (sources : List (SourceClause Domain Variable Literal Symbol)) :
    Except LoweringError (Program Variable Literal Symbol) :=
  match lowerClauses hoApplySymbol snapshot.naming 0 sources with
  | .ok lowered =>
      let symbols := guardSymbols snapshot
      .ok ⟨lowered ++ (signatureClauses snapshot names rules).map (⟨.signature, ·⟩), fun symbol => symbols.contains symbol⟩
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
      exact List.mem_map.mp inside
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

end AnthillModKbSpec.Machine
