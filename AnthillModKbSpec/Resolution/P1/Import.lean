import AnthillModKbSpec.Resolution.P1.Export

/-! # Proof imports and their admission (S08)

An imported theorem has two checks. Its logical validity is `CheckedProof`
for its own statement, against the imports older than it
(`Imports.Checked`, `ProofImport.checked_sound`). An import keeps its context,
so a proof under assumptions never becomes a global fact, and the binder
ranges its source statement was lowered with, as provenance. Its KB and NAF
provider are those of the checker the table is checked with, which every
check takes explicitly.

Its use in execution is a separate, operational check. Only a closed import
proved under no assumptions yields a clause: a fact, or a rule
`B₁ ∧ … ∧ Bₙ → H` as `H :- B₁, …, Bₙ` (`Import.clause?`). An import whose
clause is outside the P0 classes stays in the proof layer. The imports must be
checked in a KB that contains the executable program (`coversInput`); the
program extended with their clauses then goes through P0 admission like any
program (`admitImports`), and every clause of it is in that KB or derivable in
it (`admitImports_sound`). So a proved recursive theorem whose clauses P0 does
not admit can still contribute its checked instances, and the run answers for
that KB. One admission check also considers supplied proofs of the query
itself, in the query's own program (`admit`). A proof that checks answers the
query without running anything, and the query that needed evidence becomes
`proved` once the evidence is supplied; nothing is searched for. -/

namespace AnthillModKbSpec.P1

open Machine Admission

variable {Domain Variable Literal Symbol : Type}

/-- A proved statement as it is imported, with the binder ranges its source
statement was lowered with. The ranges are provenance: the lowered statement
is what is checked. -/
structure ProofImport (Domain Variable Literal Symbol : Type) where
  entry : Import Variable Literal Symbol
  ranges : Elaboration.Ranges Domain

section Checked

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  (vocab : Vocabulary Symbol) (checker : Checker Variable Literal Symbol)

/-- Every import of the table, newest first, is a checked proof of its own
statement against the imports older than it. -/
def Imports.Checked : List (Import Variable Literal Symbol) → Prop
  | [] => True
  | entry :: older => CheckedProof vocab checker older entry.context entry.goal entry.proof ∧ Imports.Checked older

/-- Decide `Imports.Checked`. -/
def checkImports : List (Import Variable Literal Symbol) → Bool
  | [] => true
  | entry :: older =>
      checkProof vocab checker older entry.context entry.goal entry.proof == .accept && checkImports older

theorem checkImports_iff : ∀ imports : List (Import Variable Literal Symbol),
    checkImports vocab checker imports = true ↔ Imports.Checked vocab checker imports
  | [] => by simp [checkImports, Imports.Checked]
  | entry :: older => by
      simp only [checkImports, Imports.Checked, Bool.and_eq_true, beq_iff_eq, checkImports_iff older,
        checkProof_accept_iff]

omit [DecidableEq Literal] in
/-- Each import of a checked table is derivable under its own context, in the
checker's KB and with its NAF provider. -/
theorem Imports.Checked.sound : ∀ {imports : List (Import Variable Literal Symbol)},
    Imports.Checked vocab checker imports → ∀ entry ∈ imports,
      Derives checker.snapshot.hoApplySymbol checker.snapshot.kb entry.context entry.goal checker.provider
  | [], _, _, member => by cases member
  | first :: older, ⟨checked, rest⟩, entry, member => by
      rcases List.mem_cons.mp member with rfl | inside
      · exact checked_toDerives vocab checker checked
      · exact Imports.Checked.sound rest entry inside

omit [DecidableEq Literal] in
/-- `ProofImport.checked_sound`: a checked import's statement holds under its
own context; it is never weakened to fewer assumptions. -/
theorem ProofImport.checked_sound {imports : List (ProofImport Domain Variable Literal Symbol)}
    (checked : Imports.Checked vocab checker (imports.map ProofImport.entry)) {proved : ProofImport Domain Variable Literal Symbol}
    (member : proved ∈ imports) :
    Derives checker.snapshot.hoApplySymbol checker.snapshot.kb proved.entry.context proved.entry.goal checker.provider :=
  checked.sound vocab checker proved.entry (List.mem_map_of_mem member)

end Checked

/-! ## Operational admission -/

/-- A goal list read off a conjunction ending in `true`. -/
def asConjunction? : Term Variable Literal Symbol → Option (List (Term Variable Literal Symbol))
  | .truth => some []
  | .conj first rest => (asConjunction? rest).map (first :: ·)
  | _ => none

theorem asConjunction?_eq : ∀ {term : Term Variable Literal Symbol} {goals : List (Term Variable Literal Symbol)},
    asConjunction? term = some goals → Term.conjunction goals = term
  | .truth, goals, read => by simp [asConjunction?] at read; subst read; rfl
  | .conj first rest, goals, read => by
      simp only [asConjunction?, Option.map_eq_some_iff] at read
      obtain ⟨tail, tailRead, rfl⟩ := read
      simp [Term.conjunction, ← asConjunction?_eq tailRead]
  | .var _, _, read | .lit _, _, read | .app _ _, _, read | .falsity, _, read | .disj _ _, _, read
  | .imp _ _, _, read | .defaultNeg _, _, read | .forallVar _ _, _, read | .existsVar _ _, _, read
  | .dictionaryCall _ _ _ _, _, read | .equal _ _, _, read => by simp [asConjunction?] at read

section Admit

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

attribute [local instance] termEq clauseEq

/-- The clause an import may add to an executable program: only a closed
statement proved under no assumptions, as a fact, or a rule whose premise is a
conjunction. -/
def Import.clause? (entry : Import Variable Literal Symbol) : Option (HornClause Variable Literal Symbol) :=
  if entry.context = [] ∧ entry.goal.freeVars = [] then
    match entry.goal with
    | .imp body head =>
        match asConjunction? body with
        | some goals => some (.definite head goals)
        | none => some (.definite entry.goal [])
    | goal => some (.definite goal [])
  else none

omit [DecidableEq Literal] [DecidableEq Symbol] in
/-- An import's clause states its goal: the goal as a fact, or the goal is the
rule's formula. Its proof was under no assumptions, and its goal is closed. -/
theorem Import.clause?_spec {entry : Import Variable Literal Symbol} {clause : HornClause Variable Literal Symbol}
    (found : entry.clause? = some clause) :
    entry.context = [] ∧ entry.goal.freeVars = [] ∧
      (clause = .definite entry.goal [] ∨ ∃ head goals, clause = .definite head goals ∧ entry.goal = clause.toFormula) := by
  unfold Import.clause? at found
  split at found
  · rename_i plain
    refine ⟨plain.1, plain.2, ?_⟩
    split at found
    · rename_i body head goalEq
      split at found
      · rename_i goals read
        cases found
        exact .inr ⟨head, goals, rfl, by simp [goalEq, HornClause.toFormula, asConjunction?_eq read]⟩
      · cases found; exact .inl (by rw [goalEq])
    · cases found; exact .inl rfl
  · cases found

variable (vocab : Vocabulary Symbol) (checker : Checker Variable Literal Symbol)

/-- The clauses the accepted imports of a table add, newest first: those of
accepted imports that `admissible` lets into the program. The others stay in
the proof layer. -/
def importedClauses (admissible : HornClause Variable Literal Symbol → Bool) :
    List (Import Variable Literal Symbol) → List (HornClause Variable Literal Symbol)
  | [] => []
  | entry :: older =>
      (if checkProof vocab checker older entry.context entry.goal entry.proof = .accept then
        (entry.clause?.filter admissible).toList
      else []) ++ importedClauses admissible older

/-- Every imported clause states a checked import, proved under no
assumptions in the checker's KB. -/
theorem importedClauses_sound {admissible : HornClause Variable Literal Symbol → Bool} :
    ∀ {imports : List (Import Variable Literal Symbol)} {clause : HornClause Variable Literal Symbol},
      clause ∈ importedClauses vocab checker admissible imports →
        ∃ (entry : Import Variable Literal Symbol) (older : List (Import Variable Literal Symbol)),
          entry.clause? = some clause ∧ CheckedProof vocab checker older [] entry.goal entry.proof
  | [], _, member => by cases member
  | entry :: older, clause, member => by
      simp only [importedClauses, List.mem_append] at member
      rcases member with own | rest
      · split at own
        · rename_i accepted
          have found : entry.clause? = some clause := by
            cases clauseEq : entry.clause? with
            | none => rw [clauseEq] at own; cases own
            | some found =>
                rw [clauseEq] at own
                simp only [Option.filter] at own
                split at own
                · simp at own; rw [own]
                · cases own
          have checked := (checkProof_accept_iff vocab checker).mp accepted
          rw [(Import.clause?_spec found).1] at checked
          exact ⟨entry, older, found, checked⟩
        · cases own
      · exact importedClauses_sound (imports := older) rest

/-- An input with clauses added to its program as KB clauses. -/
def _root_.AnthillModKbSpec.Admission.Input.extend (input : Input Domain Variable Literal Symbol)
    (clauses : List (HornClause Variable Literal Symbol)) : Input Domain Variable Literal Symbol :=
  { input with
    program := ⟨input.program.clauses ++
        clauses.mapIdx fun index clause => ⟨.lowered (input.program.clauses.length + index), clause⟩,
      input.program.guard⟩
    marked := input.marked }

/-- A clause an import may add to an input's program: one in the P0 classes. -/
def _root_.AnthillModKbSpec.Admission.Input.admissible (hoApplySymbol : Symbol)
    (input : Input Domain Variable Literal Symbol) (clause : HornClause Variable Literal Symbol) : Bool :=
  (clauseRequests hoApplySymbol input.guard 0 clause).isEmpty

/-- The checker's KB contains the input's effective program, for its
application symbol: a proof layer over the executable program. -/
def coversInput (hoApplySymbol : Symbol) (input : Input Domain Variable Literal Symbol) : Bool :=
  decide (checker.snapshot.hoApplySymbol = hoApplySymbol) &&
    input.program.clauses.all fun entry => decide (entry.clause ∈ checker.snapshot.clauses)

/-- The checker's KB is exactly the input's effective program, for its
application symbol. -/
def ownChecker (hoApplySymbol : Symbol) (input : Input Domain Variable Literal Symbol) : Bool :=
  decide (checker.snapshot.hoApplySymbol = hoApplySymbol) &&
    decide (checker.snapshot.clauses = input.program.clauses.map ProgramClause.clause)

/-- `admit_import`: the operational check of imports. Imports are checked in
a proof layer whose KB contains the executable program; the clauses of the
accepted imports in the P0 classes join the program, and the result is
admitted by P0 as any program is: the extended program is ranked as a whole.
A checker for another KB is refused. -/
def admitImports (hoApplySymbol : Symbol) (input : Input Domain Variable Literal Symbol)
    (imports : List (Import Variable Literal Symbol)) : Option (Result Domain Variable Literal Symbol hoApplySymbol) :=
  if coversInput checker hoApplySymbol input then
    some (Admission.check hoApplySymbol
      (input.extend (importedClauses vocab checker (input.admissible hoApplySymbol) imports)))
  else none

/-- The admitted program is the input's, which the checker's KB contains, with
clauses that each state a checked import of that KB: every clause of the
extended program is in the checker's KB or derivable in it. -/
theorem admitImports_sound {hoApplySymbol : Symbol} {input : Input Domain Variable Literal Symbol}
    {imports : List (Import Variable Literal Symbol)} {result : Result Domain Variable Literal Symbol hoApplySymbol}
    (admitted : admitImports vocab checker hoApplySymbol input imports = some result) :
    checker.snapshot.hoApplySymbol = hoApplySymbol ∧
      (∀ entry ∈ input.program.clauses, entry.clause ∈ checker.snapshot.clauses) ∧
      ∃ added, result = Admission.check hoApplySymbol (input.extend added) ∧
        ∀ clause ∈ added, ∃ (entry : Import Variable Literal Symbol) (older : List (Import Variable Literal Symbol)),
          entry.clause? = some clause ∧ CheckedProof vocab checker older [] entry.goal entry.proof := by
  unfold admitImports at admitted
  split at admitted
  · rename_i covers
    simp only [coversInput, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at covers
    cases admitted
    exact ⟨covers.1, covers.2, _, rfl, fun clause member => importedClauses_sound vocab checker member⟩
  · cases admitted

/-- One admission check over supplied proofs, imports, and P0. -/
inductive Admitted (Domain Variable Literal Symbol : Type) [DecidableEq Variable] [DecidableEq Literal]
    [DecidableEq Symbol] (hoApplySymbol : Symbol) where
  /-- A supplied term is a checked proof of the query in its own program. -/
  | proved (proof : Term Variable Literal Symbol)
  | plan (plan : Plan Domain Variable Literal Symbol hoApplySymbol)
  /-- P0's requests, and the capabilities the supplied proofs lack. -/
  | needsEvidence (requests : List (Request Variable Literal Symbol)) (missing : List (Capability Symbol))
  | invalid (diagnostic : Diagnostic)

/-- Admit a query. With a checker for the input's own program, a supplied
proof that checks answers the query; otherwise the program extended with the
accepted imports goes to P0. Supplied proofs are checked, never searched for:
supplying the evidence a query lacked turns `needsEvidence` into `proved` with
no proof discovery at run time. A checker for another KB is not used. -/
def admit (hoApplySymbol : Symbol) (imports : List (Import Variable Literal Symbol))
    (input : Input Domain Variable Literal Symbol) (proofs : List (Term Variable Literal Symbol)) :
    Admitted Domain Variable Literal Symbol hoApplySymbol :=
  let own := ownChecker checker hoApplySymbol input
  let accepted := fun proof => checkProof vocab checker imports input.context input.goal proof == .accept
  match (if own then proofs.find? accepted else none) with
  | some proof => .proved proof
  | none =>
      let added := if own then importedClauses vocab checker (input.admissible hoApplySymbol) imports else []
      let needed :=
        if own then
          (proofs.flatMap fun proof =>
            match checkProof vocab checker imports input.context input.goal proof with
            | .needsEvidence missing => missing
            | _ => []).eraseDups
        else []
      match Admission.check hoApplySymbol (input.extend added) with
      | .ready plan => .plan plan
      | .needsEvidence request more => .needsEvidence (request :: more) needed
      | .invalid diagnostic => .invalid diagnostic

/-- A query admitted by a supplied proof is checked in the input's own
program. -/
theorem admit_proved {hoApplySymbol : Symbol} {imports : List (Import Variable Literal Symbol)}
    {input : Input Domain Variable Literal Symbol} {proofs : List (Term Variable Literal Symbol)}
    {proof : Term Variable Literal Symbol} (admitted : admit vocab checker hoApplySymbol imports input proofs = .proved proof) :
    proof ∈ proofs ∧ checker.snapshot.hoApplySymbol = hoApplySymbol ∧
      checker.snapshot.clauses = input.program.clauses.map ProgramClause.clause ∧
      CheckedProof vocab checker imports input.context input.goal proof := by
  unfold admit at admitted
  simp only at admitted
  by_cases own : ownChecker checker hoApplySymbol input = true
  · simp only [own, ↓reduceIte] at admitted
    simp only [ownChecker, Bool.and_eq_true, decide_eq_true_eq] at own
    split at admitted
    · rename_i found foundEq
      cases admitted
      have accepted := List.find?_some foundEq
      simp only [beq_iff_eq] at accepted
      exact ⟨List.mem_of_find?_eq_some foundEq, own.1, own.2, (checkProof_accept_iff vocab checker).mp accepted⟩
    · split at admitted <;> cases admitted
  · simp only [own, Bool.false_eq_true, ↓reduceIte] at admitted
    split at admitted <;> cases admitted

/-- A query admitted by a supplied proof is derivable under its context in its
own effective program, with the checker's NAF provider. -/
theorem admit_proved_derives {hoApplySymbol : Symbol} {imports : List (Import Variable Literal Symbol)}
    {input : Input Domain Variable Literal Symbol} {proofs : List (Term Variable Literal Symbol)}
    {proof : Term Variable Literal Symbol} (admitted : admit vocab checker hoApplySymbol imports input proofs = .proved proof) :
    Derives hoApplySymbol (fun clause => clause ∈ input.program.clauses.map ProgramClause.clause) input.context
      input.goal checker.provider := by
  obtain ⟨_, symbol, clauses, checked⟩ := admit_proved vocab checker admitted
  have derived := checked_toDerives vocab checker checked
  have kb : checker.snapshot.kb = fun clause => clause ∈ input.program.clauses.map ProgramClause.clause := by
    unfold Snapshot.kb; rw [clauses]
  rw [symbol, kb] at derived
  exact derived

/-- A query admitted by a plan is Ready for P0, on its program extended with
clauses that each state a checked import of the input's own program. -/
theorem admit_plan {hoApplySymbol : Symbol} {imports : List (Import Variable Literal Symbol)}
    {input : Input Domain Variable Literal Symbol} {proofs : List (Term Variable Literal Symbol)}
    {plan : Plan Domain Variable Literal Symbol hoApplySymbol}
    (admitted : admit vocab checker hoApplySymbol imports input proofs = .plan plan) :
    ∃ added, Admission.check hoApplySymbol (input.extend added) = .ready plan ∧
      (added = [] ∨ ownChecker checker hoApplySymbol input = true) ∧
      ∀ clause ∈ added, ∃ (entry : Import Variable Literal Symbol) (older : List (Import Variable Literal Symbol)),
        entry.clause? = some clause ∧ CheckedProof vocab checker older [] entry.goal entry.proof := by
  unfold admit at admitted
  simp only at admitted
  by_cases own : ownChecker checker hoApplySymbol input = true
  · simp only [own, ↓reduceIte] at admitted
    split at admitted
    · cases admitted
    · split at admitted
      · rename_i ready
        cases admitted
        exact ⟨_, ready, .inr own, fun clause member => importedClauses_sound vocab checker member⟩
      · cases admitted
      · cases admitted
  · simp only [own, Bool.false_eq_true, ↓reduceIte] at admitted
    split at admitted
    · rename_i ready
      cases admitted
      exact ⟨[], ready, .inl rfl, fun clause member => by cases member⟩
    · cases admitted
    · cases admitted

end Admit

end AnthillModKbSpec.P1
