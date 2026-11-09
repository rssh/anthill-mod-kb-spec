import AnthillModKbSpec.Resolution.P1.Import
import AnthillModKbSpec.Resolution.ProofLayer

/-! # Checked lemmas for machine runs (S20)

A lemma is declared as its own kind of input entry beside the clauses: S08's
`ProofImport`, a name, a statement with its context, its proof term, and the
binder ranges the statement was lowered with. Statements are ordinary formulas:
no citation marker, no new `Term` constructor. Only exported trees mention a
lemma, by `Rule.reference`.

A run sees its lemmas through `lemmasFor`, built for the run's checker and
program:

- nothing unless the checker's KB contains the program, for the run's
  application symbol (`coversProgram`): a proof layer over the executable
  program, as for imports (`coversInput`);
- otherwise each lemma that is the newest with its name and a checked proof of
  its statement against the lemmas older than it (`offered`,
  `lemmasFor_offered`): a lemma not checked against this checker, whether
  unchecked, checked against another snapshot, or stale after the KB changed,
  is never offered, and a lemma that references itself never checks;
- a lemma holds at a use site when its reference resolves there
  (`resolve`): its context is among the use site's assumptions, and its proof
  is checked again under the use site's context, context-indexed NAF evidence
  included (`lemmasFor_holds`). No weakening is assumed. It applies there when
  its own context is there (`stated`): where it applies but does not hold, its
  proof, checked as written, fails under the use site's context, and the
  machine records a gap.

What `lemmasFor` offers is sound for the checker's KB and NAF provider
(`lemmasFor_sound`), so the left strategy with lemmas is sound there
(`withLemmas_sound`) and a successful run reconstructs `Derives`
(`withLemmas_derives`). An exported lemma node is a reference followed by the
eliminations of its instance; it passes checking when the reference resolves
(`Unfold.lemma*_proves`, `Proves.accepted`).

A formula a checked lemma may conclude is a proof-layer capability
(`diagnose`, `diagnose_not_ready`). A lemma enters a P0 program only through
`admitImports`, as a closed clause in the P0 classes proved under no
assumptions (`lemmas_admitImports`). -/

namespace AnthillModKbSpec.P1

open Machine

variable {Domain Variable Literal Symbol Certificate Snapshot : Type}

/-- A lemma, declared beside the clauses: S08's proof import. -/
abbrev Lemma (Domain Variable Literal Symbol : Type) := ProofImport Domain Variable Literal Symbol

section Offered

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  (vocab : Vocabulary Symbol) (checker : Checker Variable Literal Symbol)

attribute [local instance] termEq clauseEq

/-- The entries of a table, newest first, offered to a run: each is the newest
entry with its name (none in `seen`) and a checked proof of its statement
against the entries older than it. -/
def offered (seen : List Symbol) : List (Import Variable Literal Symbol) → List (Import Variable Literal Symbol)
  | [] => []
  | entry :: older =>
      (if entry.name ∉ seen ∧ checkProof vocab checker older entry.context entry.goal entry.proof = .accept then [entry]
        else []) ++ offered (entry.name :: seen) older

/-- The newest entry with the name is stated for the goal, under assumptions
the context has: the conditions of a reference before its proof is checked. -/
def stated : List (Import Variable Literal Symbol) → Symbol → ProofContext Variable Literal Symbol →
    Formula Variable Literal Symbol → Bool
  | [], _, _, _ => false
  | entry :: older, name, context, goal =>
      if entry.name = name then
        decide (entry.goal = goal) && entry.context.all fun assumption => decide (assumption ∈ context)
      else stated older name context goal

/-- The lemmas a run of `program` sees: none unless the checker covers the
program; otherwise the offered lemmas, each holding under a context when its
reference resolves there, and applying there when its own context is there. -/
def lemmasFor (hoApplySymbol : Symbol) (program : Program Variable Literal Symbol)
    (lemmas : List (Lemma Domain Variable Literal Symbol)) : Machine.Lemmas Variable Literal Symbol :=
  let table := lemmas.map ProofImport.entry
  if coversProgram checker hoApplySymbol program then
    ⟨(offered vocab checker [] table).map fun entry => (entry.name, entry.goal),
      fun context name statement => resolve vocab checker table name context statement,
      fun context name statement => stated table name context statement⟩
  else Machine.Lemmas.none

/-- An offered entry is the newest with its name and is checked against the
entries older than it. -/
theorem offered_spec : ∀ {seen : List Symbol} {table : List (Import Variable Literal Symbol)}
    {entry : Import Variable Literal Symbol}, entry ∈ offered vocab checker seen table →
      entry.name ∉ seen ∧ ∃ newer older, table = newer ++ entry :: older ∧ (∀ other ∈ newer, other.name ≠ entry.name) ∧
        CheckedProof vocab checker older entry.context entry.goal entry.proof
  | _, [], _, member => by cases member
  | seen, first :: rest, entry, member => by
      simp only [offered, List.mem_append] at member
      rcases member with here | there
      · split at here
        · rename_i accepted
          rw [List.mem_singleton] at here
          subst here
          exact ⟨accepted.1, [], rest, rfl, (fun _ inside => by cases inside),
            (checkProof_accept_iff vocab checker).mp accepted.2⟩
        · cases here
      · obtain ⟨unseen, newer, older, split, distinct, checked⟩ := offered_spec there
        simp only [List.mem_cons, not_or] at unseen
        refine ⟨unseen.2, first :: newer, older, by rw [split]; rfl, fun other inside => ?_, checked⟩
        rcases List.mem_cons.mp inside with rfl | later
        · exact fun same => unseen.1 same.symm
        · exact distinct other later

/-- Every entry of a checked table with distinct names is offered. -/
theorem offered_checked : ∀ {seen : List Symbol} {table : List (Import Variable Literal Symbol)},
    Imports.Checked vocab checker table → (table.map Import.name).Nodup → (∀ entry ∈ table, entry.name ∉ seen) →
      offered vocab checker seen table = table
  | _, [], _, _, _ => rfl
  | seen, first :: rest, ⟨checked, older⟩, distinct, unseen => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at distinct
      have fresh : first.name ∉ seen := unseen first List.mem_cons_self
      have accepted := (checkProof_accept_iff vocab checker).mpr checked
      simp only [offered, fresh, not_false_eq_true, accepted, and_self, ↓reduceIte, List.singleton_append]
      refine congrArg _ (offered_checked older distinct.2 fun entry inside named => ?_)
      rcases List.mem_cons.mp named with same | before
      · exact distinct.1 ⟨entry, inside, same⟩
      · exact unseen entry (List.mem_cons_of_mem _ inside) before

/-- `lemmasFor_offered`: a lemma is offered only when the checker covers the
program, and it is the newest lemma with its name, checked by the run's
checker against the lemmas older than it. -/
theorem lemmasFor_offered {hoApplySymbol : Symbol} {program : Program Variable Literal Symbol}
    {lemmas : List (Lemma Domain Variable Literal Symbol)} {name : Symbol} {statement : Formula Variable Literal Symbol}
    (member : (name, statement) ∈ (lemmasFor vocab checker hoApplySymbol program lemmas).statements) :
    coversProgram checker hoApplySymbol program = true ∧
      ∃ entry newer older, lemmas.map ProofImport.entry = newer ++ entry :: older ∧ entry.name = name ∧
        entry.goal = statement ∧ (∀ other ∈ newer, other.name ≠ name) ∧
        CheckedProof vocab checker older entry.context statement entry.proof := by
  unfold lemmasFor at member
  split at member
  · rename_i covers
    obtain ⟨entry, inside, same⟩ := List.mem_map.mp member
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    obtain ⟨_, newer, older, split, distinct, checked⟩ := offered_spec vocab checker inside
    exact ⟨covers, entry, newer, older, split, rfl, rfl, distinct, checked⟩
  · cases member

/-- A covered program sees every lemma of a checked table with distinct names. -/
theorem lemmasFor_checked {hoApplySymbol : Symbol} {program : Program Variable Literal Symbol}
    {lemmas : List (Lemma Domain Variable Literal Symbol)}
    (covers : coversProgram checker hoApplySymbol program = true)
    (checked : Imports.Checked vocab checker (lemmas.map ProofImport.entry))
    (distinct : ((lemmas.map ProofImport.entry).map Import.name).Nodup) :
    (lemmasFor vocab checker hoApplySymbol program lemmas).statements =
      lemmas.map fun lemma => (lemma.entry.name, lemma.entry.goal) := by
  have all := offered_checked vocab checker (seen := []) checked distinct (fun _ _ inside => List.not_mem_nil inside)
  simp only [lemmasFor, covers, ↓reduceIte, all, List.map_map]
  rfl

omit [DecidableEq Literal] in
/-- A resolved reference names an entry stated for the goal whose context the
use site's context contains. -/
theorem Resolves.context : ∀ {table : List (Import Variable Literal Symbol)} {name : Symbol}
    {context : ProofContext Variable Literal Symbol} {goal : Formula Variable Literal Symbol},
    Resolves vocab checker table name context goal →
      ∃ entry ∈ table, entry.name = name ∧ entry.goal = goal ∧ ∀ assumption ∈ entry.context, assumption ∈ context
  | [], _, _, _, resolved => by simp [Resolves] at resolved
  | entry :: older, name, context, goal, resolved => by
      unfold Resolves at resolved
      split at resolved
      · rename_i same
        exact ⟨entry, List.mem_cons_self, same, resolved.1, resolved.2.1⟩
      · obtain ⟨found, inside, rest⟩ := Resolves.context resolved
        exact ⟨found, List.mem_cons_of_mem _ inside, rest⟩

/-- `lemmasFor_holds`: a lemma holds at a use site only where its reference
resolves: a lemma with its statement whose context the use site's contains,
its proof checked again under the use site's context. -/
theorem lemmasFor_holds {hoApplySymbol : Symbol} {program : Program Variable Literal Symbol}
    {lemmas : List (Lemma Domain Variable Literal Symbol)} {context : ProofContext Variable Literal Symbol}
    {name : Symbol} {statement : Formula Variable Literal Symbol}
    (holds : (lemmasFor vocab checker hoApplySymbol program lemmas).holds context name statement = true) :
    Resolves vocab checker (lemmas.map ProofImport.entry) name context statement ∧
      ∃ lemma ∈ lemmas, lemma.entry.name = name ∧ lemma.entry.goal = statement ∧
        ∀ assumption ∈ lemma.entry.context, assumption ∈ context := by
  unfold lemmasFor at holds
  split at holds
  · have resolved := (resolve_iff vocab checker _ _ _ _).mp holds
    obtain ⟨entry, inside, rest⟩ := Resolves.context vocab checker resolved
    obtain ⟨lemma, member, rfl⟩ := List.mem_map.mp inside
    exact ⟨resolved, lemma, member, rest⟩
  · cases holds

/-- `lemmasFor_sound`: what the run sees is sound for the checker's KB and NAF
provider: a lemma that holds under a context is derivable under it. -/
theorem lemmasFor_sound (hoApplySymbol : Symbol) (program : Program Variable Literal Symbol)
    (lemmas : List (Lemma Domain Variable Literal Symbol)) :
    (lemmasFor vocab checker hoApplySymbol program lemmas).Sound checker.snapshot.hoApplySymbol checker.snapshot.kb
      checker.provider := by
  intro context name statement holds
  exact (lemmasFor_holds vocab checker holds).1.derives vocab checker

end Offered

/-! ## Runs in the checker's KB -/

section Runs

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable]
  (vocab : Vocabulary Symbol) (checker : Checker Variable Literal Symbol)

/-- The program with the checker's clauses added after its own. -/
def _root_.AnthillModKbSpec.Machine.Program.cover (program : Program Variable Literal Symbol)
    (clauses : List (HornClause Variable Literal Symbol)) : Program Variable Literal Symbol :=
  ⟨program.clauses ++ clauses.map fun clause => ⟨.signature, clause⟩, program.guard⟩

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
/-- A program whose clauses are among `clauses`, covered by them, denotes
exactly their KB. -/
theorem _root_.AnthillModKbSpec.Machine.Program.cover_kb {program : Program Variable Literal Symbol}
    {clauses : List (HornClause Variable Literal Symbol)} (covers : ∀ entry ∈ program.clauses, entry.clause ∈ clauses) :
    (program.cover clauses).kb = fun clause => clause ∈ clauses := by
  funext clause
  apply propext
  constructor
  · rintro ⟨entry, inside, rfl⟩
    rcases List.mem_append.mp inside with own | added
    · exact covers entry own
    · obtain ⟨found, member, rfl⟩ := List.mem_map.mp added
      exact member
  · intro member
    exact ⟨⟨.signature, clause⟩, List.mem_append_right _ (List.mem_map_of_mem member), rfl⟩

omit [FreshNames Variable] in
theorem coversProgram_spec {hoApplySymbol : Symbol} {program : Program Variable Literal Symbol}
    (covers : coversProgram checker hoApplySymbol program = true) :
    checker.snapshot.hoApplySymbol = hoApplySymbol ∧ ∀ entry ∈ program.clauses, entry.clause ∈ checker.snapshot.clauses := by
  simp only [coversProgram, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at covers
  exact covers

/-- `withLemmas_sound`: the left strategy with the lemmas a covered program
sees is sound for the checker's KB and NAF provider. -/
theorem withLemmas_sound {hoApplySymbol : Symbol} {program : Program Variable Literal Symbol}
    (covers : coversProgram checker hoApplySymbol program = true) (lemmas : List (Lemma Domain Variable Literal Symbol))
    (select : Selection Variable Literal Symbol) (cuts : LemmaSelection Variable Literal Symbol) :
    Strategy.Sound checker.snapshot.hoApplySymbol checker.snapshot.kb checker.provider
      (withLemmas (Certificate := Certificate) hoApplySymbol program
        (lemmasFor vocab checker hoApplySymbol program lemmas) select cuts) := by
  obtain ⟨symbol, clauses⟩ := coversProgram_spec checker covers
  have kb : (program.cover checker.snapshot.clauses).kb = checker.snapshot.kb := Program.cover_kb clauses
  have sound := lemmasFor_sound vocab checker hoApplySymbol program lemmas
  rw [← kb] at sound ⊢
  rw [symbol] at sound ⊢
  exact withLemmas_sound_within (fun _ member => List.mem_append_left _ member) sound select cuts

/-- `withLemmas_derives`: a successful run of a covered program with its
lemmas reconstructs `Derives` for its answer instance in the checker's KB,
with its NAF provider. -/
theorem withLemmas_derives {hoApplySymbol : Symbol} {program : Program Variable Literal Symbol}
    (covers : coversProgram checker hoApplySymbol program = true) (lemmas : List (Lemma Domain Variable Literal Symbol))
    (select : Selection Variable Literal Symbol) (cuts : LemmaSelection Variable Literal Symbol) (fuel : Nat)
    (snapshot : Snapshot) (flexibles : List Variable) (context : ProofContext Variable Literal Symbol)
    (goal : Formula Variable Literal Symbol) {resume : State Variable Literal Symbol Certificate Snapshot}
    {proof : CompletedProof Variable Literal Symbol Certificate Snapshot}
    (ran : run (withLemmas hoApplySymbol program (lemmasFor vocab checker hoApplySymbol program lemmas) select cuts) fuel
      (State.init snapshot flexibles context goal) = .success proof resume) :
    Derives checker.snapshot.hoApplySymbol checker.snapshot.kb (context.map proof.store.resolve)
      (proof.store.resolve goal) checker.provider :=
  run_init_reconstructs _ (withLemmas_sound vocab checker covers lemmas select cuts) fuel snapshot flexibles context goal
    ran

end Runs

/-! ## Exported lemma nodes -/

section Export

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  (vocab : Vocabulary Symbol) (checker : Checker Variable Literal Symbol)

/-- A valid tree, with references resolved over the table, is accepted for its
conclusion. -/
theorem Proves.accepted {table : List (Import Variable Literal Symbol)} {context : ProofContext Variable Literal Symbol}
    {goal : Formula Variable Literal Symbol} {tree : Proof Variable Literal Symbol}
    (proves : Proves checker (Resolves vocab checker table) context goal tree) :
    checkProof vocab checker table context goal (encode vocab tree) = .accept :=
  (checkProof_accept_iff vocab checker).mpr ⟨tree, decode_encode vocab tree, proves.2, proves.1⟩

/-- A lemma node passes checking when its reference resolves: its instance by
the eliminations, its rule's conclusion given an accepted premise tree, and a
cut given an accepted continuation. -/
theorem lemmaUse_accepted {table : List (Import Variable Literal Symbol)} {context : ProofContext Variable Literal Symbol}
    {name : Symbol} {statement goal : Formula Variable Literal Symbol}
    {steps : List (Term Variable Literal Symbol × Formula Variable Literal Symbol)}
    (resolved : Resolves vocab checker table name context statement) (instances : Instances statement steps goal) :
    checkProof vocab checker table context goal (encode vocab (Unfold.lemmaUse name statement steps)) = .accept :=
  Proves.accepted vocab checker (Unfold.lemmaUse_proves resolved instances)

end Export

/-! ## Static diagnostics -/

section Diagnostics

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  (vocab : Vocabulary Symbol) (checker : Checker Variable Literal Symbol)

/-- P0's requests that the checked lemmas an input's program sees may conclude. -/
def diagnose (hoApplySymbol : Symbol) (input : Admission.Input Domain Variable Literal Symbol)
    (lemmas : List (Lemma Domain Variable Literal Symbol)) :
    List (Admission.Request Variable Literal Symbol × List (Symbol × RuleId)) :=
  Admission.diagnoseLemmas hoApplySymbol (lemmasFor vocab checker hoApplySymbol input.program lemmas).statements input

/-- A formula usable through a checked lemma is never P0-Ready: it is reported
only for an input P0 does not admit, and only for lemmas the input's program
sees, each checked by the run's checker. -/
theorem diagnose_not_ready {hoApplySymbol : Symbol} {input : Admission.Input Domain Variable Literal Symbol}
    {lemmas : List (Lemma Domain Variable Literal Symbol)}
    {entry : Admission.Request Variable Literal Symbol × List (Symbol × RuleId)}
    (member : entry ∈ diagnose vocab checker hoApplySymbol input lemmas)
    (plan : Admission.Plan Domain Variable Literal Symbol hoApplySymbol) :
    Admission.check hoApplySymbol input ≠ .ready plan :=
  Admission.diagnoseLemmas_not_ready member plan

/-- Lemmas enter a P0 program only as imports: `admitImports` adds the clauses
of closed lemmas proved under no assumptions in the P0 classes, each a checked
lemma of the checker's KB, and P0 admits the extended program as a whole. -/
theorem lemmas_admitImports {hoApplySymbol : Symbol} {input : Admission.Input Domain Variable Literal Symbol}
    {lemmas : List (Lemma Domain Variable Literal Symbol)}
    {result : Admission.Result Domain Variable Literal Symbol hoApplySymbol}
    (admitted : admitImports vocab checker hoApplySymbol input (lemmas.map ProofImport.entry) = some result) :
    ∃ added, result = Admission.check hoApplySymbol (input.extend added) ∧
      ∀ clause ∈ added, ∃ (entry : Import Variable Literal Symbol) (older : List (Import Variable Literal Symbol)),
        entry.clause? = some clause ∧ entry.context = [] ∧
          CheckedProof vocab checker older [] entry.goal entry.proof := by
  obtain ⟨_, _, added, resultEq, clauses⟩ := admitImports_sound vocab checker admitted
  exact ⟨added, resultEq, fun clause member => by
    obtain ⟨entry, older, found, checked⟩ := clauses clause member
    exact ⟨entry, older, found, (Import.clause?_spec found).1, checked⟩⟩

end Diagnostics

end AnthillModKbSpec.P1
