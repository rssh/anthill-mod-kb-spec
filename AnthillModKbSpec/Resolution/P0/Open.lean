import AnthillModKbSpec.Resolution.P0.Witness
import AnthillModKbSpec.Models.KeyModel
import AnthillModKbSpec.Foundation.Completion
import AnthillModKbSpec.Resolution.Machine.OpenAtoms
import AnthillModKbSpec.Resolution.AdmissionSignature

/-! # Witnesses for open atoms in ground programs (S22)

The logical Unknown says that the KB leaves a goal open: the goal holds in one
model of the completion and fails in another. Its evidence is two witnesses.
A witness is a finite assignment of the open atoms, the marker atoms
(`Completion.openAtomsOf`): the atoms it lists are true, and every other marker
atom is false, its canonical extension. It is checked (`check`):

- the program is in the covered class: ground definite clauses with an atomic
  head that is no marker atom and P0 bodies, and denials with P0 bodies;
- the witness program, the definite clauses with the true marker atoms as
  facts, is ranked (acyclic);
- every denial body evaluates false, and the goal to the expected value, by
  the ranked P0 evaluator (`evaluate`); the goal may also use disjunction and
  implication, evaluated by their truth tables.

A checked witness has a model (`check_model`): the constructor-key model in
which an atom holds when the witness program gives it a success certificate.
It satisfies every clause of the completed program for any signature that
closes no marker and not `ho_apply`: the KB's clauses and denials, every
only-if clause, and the free equality theory. NAF is complement, and the goal
has the expected value. So two checked witnesses with opposite values show
that the goal is independent of the completion.

Non-ground or cyclic programs are outside the covered class; there an open
atom gives Undecided. Tabled evaluation (S24) extends the witnesses. -/

namespace AnthillModKbSpec.Open

open GroundSearch Semantics Completion

variable {Variable Literal Symbol : Type}

/-! ## Ground data as keys -/

mutual
/-- The key of a data term. -/
def dataKey : Term Variable Literal Symbol → Key Literal Symbol
  | .lit value => .lit value
  | .app symbol args => .app symbol (dataKeys args)
  | _ => .truth False

def dataKeys : List (Term Variable Literal Symbol) → List (Key Literal Symbol)
  | [] => []
  | term :: rest => dataKey term :: dataKeys rest
end

theorem dataKeys_eq : ∀ args : List (Term Variable Literal Symbol), dataKeys args = args.map dataKey
  | [] => rfl
  | arg :: rest => by rw [dataKeys, dataKeys_eq rest]; rfl

variable [DecidableEq Variable] [DecidableEq Symbol]

/-- A data term evaluates to its key, in every environment. -/
theorem eval_data {hoApplySymbol : Symbol} (interpretation : Symbol → List (Key Literal Symbol) → Prop)
    (environment : Environment Variable (Key Literal Symbol)) {term : Term Variable Literal Symbol} (data : IsData term) :
    (Model.keys hoApplySymbol interpretation).eval environment term = dataKey term := by
  induction data with
  | lit => simp only [Model.eval, dataKey]; rfl
  | app args ih =>
      simp only [Model.eval, dataKey, dataKeys_eq]
      exact congrArg (Key.app _) (List.map_congr_left ih)

omit [DecidableEq Variable] [DecidableEq Symbol] in
theorem keys_injective {args others : List (Term Variable Literal Symbol)}
    (each : ∀ arg ∈ args, ∀ other, IsData other → dataKey arg = dataKey other → arg = other)
    (othersData : ∀ other ∈ others, IsData other) (same : args.map dataKey = others.map dataKey) : args = others := by
  induction args generalizing others with
  | nil => cases others with
    | nil => rfl
    | cons _ _ => cases same
  | cons arg rest ih =>
      cases others with
      | nil => cases same
      | cons other more =>
          simp only [List.map_cons, List.cons.injEq] at same
          rw [each arg List.mem_cons_self other (othersData other List.mem_cons_self) same.1,
            ih (fun inner member => each inner (List.mem_cons_of_mem _ member))
              (fun inner member => othersData inner (List.mem_cons_of_mem _ member)) same.2]

omit [DecidableEq Variable] [DecidableEq Symbol] in
/-- Distinct data terms have distinct keys. -/
theorem dataKey_injective {term : Term Variable Literal Symbol} (data : IsData term) :
    ∀ {other : Term Variable Literal Symbol}, IsData other → dataKey term = dataKey other → term = other := by
  induction data with
  | lit =>
      intro other otherData same
      cases otherData with
      | lit => simp only [dataKey, Key.lit.injEq] at same; rw [same]
      | app _ => cases same
  | app args ih =>
      intro other otherData same
      cases otherData with
      | lit => cases same
      | app othersData =>
          simp only [dataKey, dataKeys_eq, Key.app.injEq] at same
          rw [same.1, keys_injective ih othersData same.2]

omit [DecidableEq Variable] [DecidableEq Symbol] in
theorem eq_of_mem_zip_map {α β γ : Type} {f : α → γ} {g : β → γ} :
    ∀ {left : List α} {right : List β} {a : α} {b : β}, (a, b) ∈ left.zip right → left.map f = right.map g → f a = g b
  | [], _, _, _, member, _ => by simp at member
  | _ :: _, [], _, _, member, _ => by simp at member
  | x :: xs, y :: ys, a, b, member, same => by
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq, List.map_cons, List.cons.injEq] at member same
      rcases member with ⟨rfl, rfl⟩ | member
      · exact same.1
      · exact eq_of_mem_zip_map member same.2

/-! ## The model of a ground program -/

variable (hoApplySymbol : Symbol)

/-- The empty atomic context. -/
def emptyContext : Context Variable Literal Symbol hoApplySymbol := ⟨[], by simp⟩

/-- An atom holds at the keys of ground data when the program gives it a
success certificate. -/
def interpretation (program : Program Variable Literal Symbol hoApplySymbol) :
    Symbol → List (Key Literal Symbol) → Prop :=
  fun symbol keys => ∃ args, (∀ arg ∈ args, IsData arg) ∧ keys = args.map dataKey ∧
    Succeeds program (emptyContext hoApplySymbol) (.app symbol args)

variable (excluded : Symbol → Bool) (outside : Symbol → List (Key Literal Symbol) → Prop)

/-- The interpretation of a witness: `outside` on the excluded symbols (the
signature's guards, which the program never mentions), the program's
elsewhere. -/
def combined (program : Program Variable Literal Symbol hoApplySymbol) : Symbol → List (Key Literal Symbol) → Prop :=
  fun symbol keys => if excluded symbol then outside symbol keys else interpretation hoApplySymbol program symbol keys

/-- The constructor-key model of a ground program. -/
abbrev model (program : Program Variable Literal Symbol hoApplySymbol) :=
  Model.keys hoApplySymbol (combined hoApplySymbol excluded outside program)

variable {hoApplySymbol} {excluded} {outside} {program : Program Variable Literal Symbol hoApplySymbol}

/-- An atom of a symbol that is not excluded holds exactly when it has a
success certificate. -/
theorem atom_iff {symbol : Symbol} {args : List (Term Variable Literal Symbol)}
    (atom : IsAtom hoApplySymbol (.app symbol args)) (clear : excluded symbol = false)
    (environment : Environment Variable (Key Literal Symbol)) :
    (model hoApplySymbol excluded outside program).Satisfies environment (.app symbol args) ↔
      Succeeds program (emptyContext hoApplySymbol) (.app symbol args) := by
  cases atom with
  | app ordinary data =>
      rw [Model.keys_atom _ environment ordinary,
        List.map_congr_left (fun arg member => eval_data _ environment (data arg member))]
      simp only [combined, clear, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro ⟨others, othersData, same, proof⟩
        rwa [keys_injective (fun arg member _ otherData same => dataKey_injective (data arg member) otherData same)
          othersData same]
      · intro proof
        exact ⟨args, data, rfl, proof⟩

theorem satisfies_truth (environment : Environment Variable (Key Literal Symbol)) :
    (model hoApplySymbol excluded outside program).Satisfies environment .truth := by
  simp only [Model.Satisfies, Model.eval]; exact (model hoApplySymbol excluded outside program).holds_top

theorem not_satisfies_falsity (environment : Environment Variable (Key Literal Symbol)) :
    ¬ (model hoApplySymbol excluded outside program).Satisfies environment .falsity := by
  simp only [Model.Satisfies, Model.eval]; exact (model hoApplySymbol excluded outside program).holds_bottom

theorem satisfies_conj (environment : Environment Variable (Key Literal Symbol)) (left right : Term Variable Literal Symbol) :
    (model hoApplySymbol excluded outside program).Satisfies environment (.conj left right) ↔
      (model hoApplySymbol excluded outside program).Satisfies environment left ∧ (model hoApplySymbol excluded outside program).Satisfies environment right := by
  simp only [Model.Satisfies, Model.eval]; exact (model hoApplySymbol excluded outside program).holds_conjunction _ _

theorem satisfies_disj (environment : Environment Variable (Key Literal Symbol)) (left right : Term Variable Literal Symbol) :
    (model hoApplySymbol excluded outside program).Satisfies environment (.disj left right) ↔
      (model hoApplySymbol excluded outside program).Satisfies environment left ∨ (model hoApplySymbol excluded outside program).Satisfies environment right := by
  simp only [Model.Satisfies, Model.eval]; exact (model hoApplySymbol excluded outside program).holds_disjunction _ _

theorem satisfies_imp (environment : Environment Variable (Key Literal Symbol)) (left right : Term Variable Literal Symbol) :
    (model hoApplySymbol excluded outside program).Satisfies environment (.imp left right) ↔
      ((model hoApplySymbol excluded outside program).Satisfies environment left → (model hoApplySymbol excluded outside program).Satisfies environment right) := by
  simp only [Model.Satisfies, Model.eval]; exact (model hoApplySymbol excluded outside program).holds_implication _ _

theorem satisfies_defaultNeg (environment : Environment Variable (Key Literal Symbol)) (body : Term Variable Literal Symbol) :
    (model hoApplySymbol excluded outside program).Satisfies environment (.defaultNeg body) ↔
      ¬ (model hoApplySymbol excluded outside program).Satisfies environment body := by
  simp only [Model.Satisfies, Model.eval]; exact Model.keys_complement _ _

/-- The goal mentions no excluded symbol in its atoms. -/
def Clear (excluded : Symbol → Bool) (goal : Term Variable Literal Symbol) : Prop :=
  ∀ symbol args, Term.app symbol args ∈ atoms goal → excluded symbol = false

/-- Under a rank, a P0 goal with no excluded symbol holds exactly when it has a
success certificate: NAF holds exactly when its operand fails, and a ranked
operand either succeeds or fails (`decided`). -/
theorem goal_iff {rank : Term Variable Literal Symbol → Nat} (ranked : Ranked rank program.clauses) :
    ∀ {goal : Term Variable Literal Symbol}, IsGoal hoApplySymbol goal → Clear excluded goal → ∀ environment,
      (model hoApplySymbol excluded outside program).Satisfies environment goal ↔
        Succeeds program (emptyContext hoApplySymbol) goal := by
  intro goal valid
  induction valid with
  | atom atom =>
      intro clear environment
      cases atom with
      | app ordinary data =>
          exact atom_iff (.app ordinary data) (clear _ _ (by rw [atoms]; exact List.mem_singleton_self _)) environment
  | truth => intro _ environment; exact ⟨fun _ => .truth, fun _ => satisfies_truth environment⟩
  | falsity =>
      intro _ environment
      exact ⟨fun holds => absurd holds (not_satisfies_falsity environment), fun proof => by cases proof⟩
  | conj _ _ ihLeft ihRight =>
      intro clear environment
      rw [satisfies_conj, ihLeft (fun symbol args inside => clear symbol args (by simp [atoms, inside])),
        ihRight (fun symbol args inside => clear symbol args (by simp [atoms, inside]))]
      exact ⟨fun ⟨left, right⟩ => .conj left right, fun proof => by cases proof with | conj left right => exact ⟨left, right⟩⟩
  | defaultNeg body ih =>
      intro clear environment
      rw [satisfies_defaultNeg, ih (fun symbol args inside => clear symbol args (by simpa [atoms] using inside))]
      exact ⟨fun missing => .defaultNeg (fails_of_not_succeeds ranked body missing),
        fun proof => by cases proof with | defaultNeg refuted => exact fails_not_succeeds refuted⟩

theorem satisfies_conjunction (environment : Environment Variable (Key Literal Symbol)) (goals : List (Term Variable Literal Symbol)) :
    (model hoApplySymbol excluded outside program).Satisfies environment (.conjunction goals) ↔
      ∀ goal ∈ goals, (model hoApplySymbol excluded outside program).Satisfies environment goal :=
  (model hoApplySymbol excluded outside program).satisfies_conjunction environment goals

/-! ## Evaluating goals -/

variable [DecidableEq Literal] (hoApplySymbol)

attribute [local instance] Machine.termEq

/-- A verdict's truth value. -/
def Verdict.value : Verdict Variable Literal Symbol → Bool
  | .success _ => true
  | .failure _ => false

/-- The value of a ground goal in a clause list: atoms of symbols not excluded
by the P0 evaluator at the bound, connectives by their truth tables. `none`
for anything else, or when the bound is too small. -/
def value (excluded : Symbol → Bool) (clauses : List (HornClause Variable Literal Symbol)) (bound : Nat) :
    Term Variable Literal Symbol → Option Bool
  | .truth => some true
  | .falsity => some false
  | .conj left right =>
      match value excluded clauses bound left, value excluded clauses bound right with
      | some first, some second => some (first && second)
      | _, _ => none
  | .disj left right =>
      match value excluded clauses bound left, value excluded clauses bound right with
      | some first, some second => some (first || second)
      | _, _ => none
  | .imp left right =>
      match value excluded clauses bound left, value excluded clauses bound right with
      | some first, some second => some (!first || second)
      | _, _ => none
  | .defaultNeg body => (value excluded clauses bound body).map (!·)
  | .app symbol args =>
      if isAtom hoApplySymbol (.app symbol args) && !excluded symbol then
        (evaluate clauses [] bound (.app symbol args)).map Verdict.value
      else none
  | _ => none

variable {hoApplySymbol}

/-- A value is the goal's truth in the model of the program, in every
environment. -/
theorem value_sound {bound : Nat} :
    ∀ {goal : Term Variable Literal Symbol} {result : Bool},
      value hoApplySymbol excluded program.clauses bound goal = some result →
      ∀ environment, (model hoApplySymbol excluded outside program).Satisfies environment goal ↔ result = true
  | .truth, result, valued, environment => by
      cases valued; exact iff_of_true (satisfies_truth environment) rfl
  | .falsity, result, valued, environment => by
      cases valued; exact iff_of_false (not_satisfies_falsity environment) (by simp)
  | .conj left right, result, valued, environment => by
      simp only [value] at valued
      split at valued
      · rename_i first second leftEq rightEq
        cases valued
        rw [satisfies_conj, value_sound leftEq environment, value_sound rightEq environment]
        simp
      · cases valued
  | .disj left right, result, valued, environment => by
      simp only [value] at valued
      split at valued
      · rename_i first second leftEq rightEq
        cases valued
        rw [satisfies_disj, value_sound leftEq environment, value_sound rightEq environment]
        simp
      · cases valued
  | .imp left right, result, valued, environment => by
      simp only [value] at valued
      split at valued
      · rename_i first second leftEq rightEq
        cases valued
        rw [satisfies_imp, value_sound leftEq environment, value_sound rightEq environment]
        cases first <;> cases second <;> simp
      · cases valued
  | .defaultNeg body, result, valued, environment => by
      simp only [value, Option.map_eq_some_iff] at valued
      obtain ⟨inner, innerEq, rfl⟩ := valued
      rw [satisfies_defaultNeg, value_sound innerEq environment]
      cases inner <;> simp
  | .app symbol args, result, valued, environment => by
      simp only [value] at valued
      split at valued
      · rename_i atomic
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at atomic
        simp only [Option.map_eq_some_iff] at valued
        obtain ⟨verdict, evaluated, rfl⟩ := valued
        have atom := isAtom_iff.mp atomic.1
        have checked := evaluate_sound (program := program) (context := emptyContext hoApplySymbol) bound (.atom atom)
          evaluated
        rw [atom_iff atom atomic.2 environment]
        cases verdict with
        | success tree => exact iff_of_true (checkSuccess_sound _ _ checked) rfl
        | failure tree => exact iff_of_false (fails_not_succeeds (checkFailure_sound _ _ checked)) (by simp [Verdict.value])
      · cases valued
  | .var _, _, valued, _ | .lit _, _, valued, _ | .forallVar _ _, _, valued, _ | .existsVar _ _, _, valued, _
  | .dictionaryCall _ _ _ _, _, valued, _ | .equal _ _, _, valued, _ => by cases valued

/-! ## The check -/

variable (hoApplySymbol)

/-- No atom of the goal is of an excluded symbol. -/
def clear (excluded : Symbol → Bool) (goal : Term Variable Literal Symbol) : Bool :=
  (atoms goal).all fun
    | .app symbol _ => !excluded symbol
    | _ => true

/-- A clause the witness check covers: a ground definite clause whose head is
an atom and no marker atom, with a P0 body, or a denial with a P0 body; no
atom of an excluded symbol (a guard) anywhere. -/
def covered (excluded unknownMarker : Symbol → Bool) : HornClause Variable Literal Symbol → Bool
  | .definite head body =>
      isAtom hoApplySymbol head && !unknownMarkerAtom unknownMarker head && clear excluded head &&
        body.all (fun goal => isGoal hoApplySymbol goal && clear excluded goal)
  | .goal body => body.all (fun goal => isGoal hoApplySymbol goal && clear excluded goal)

/-- A definite clause. -/
def definite : HornClause Variable Literal Symbol → Bool
  | .definite _ _ => true
  | .goal _ => false

/-- The program's denial bodies. -/
def denials (clauses : List (HornClause Variable Literal Symbol)) : List (List (Term Variable Literal Symbol)) :=
  clauses.filterMap fun
    | .goal body => some body
    | .definite _ _ => none

/-- The witness program: the definite clauses, and the true marker atoms as facts. -/
def witnessClauses (clauses : List (HornClause Variable Literal Symbol)) (assignment : List (Term Variable Literal Symbol)) :
    List (HornClause Variable Literal Symbol) :=
  clauses.filter definite ++ assignment.map fun atom => .definite atom []

/-- The rank computed for a clause list, by peeling its dependency graph. -/
def rank (clauses : List (HornClause Variable Literal Symbol)) : Term Variable Literal Symbol → Nat :=
  rankOf (topoRank (edges clauses) ((edges clauses).flatMap fun edge => [edge.1, edge.2]))

/-- The rank decreases along every edge. -/
def ranked? (rank : Term Variable Literal Symbol → Nat) (clauses : List (HornClause Variable Literal Symbol)) : Bool :=
  (edges clauses).all fun edge => decide (rank edge.2 < rank edge.1)

/-- A level bound covering every atom of the graph. -/
def bound (rank : Term Variable Literal Symbol → Nat) (clauses : List (HornClause Variable Literal Symbol)) : Nat :=
  ((edges clauses).flatMap fun edge => [rank edge.1, rank edge.2]).foldr max 0 + 1

/-- The program is in the covered class. -/
def covers (excluded unknownMarker : Symbol → Bool) (clauses : List (HornClause Variable Literal Symbol)) : Bool :=
  clauses.all (covered hoApplySymbol excluded unknownMarker)

/-- The goal's value under a witness: when the assignment lists marker atoms
of symbols not excluded, the witness program is ranked, and every denial body
is false, the goal's value in the witness program; `none` otherwise. -/
def witnessValue (excluded unknownMarker : Symbol → Bool) (clauses : List (HornClause Variable Literal Symbol))
    (goal : Term Variable Literal Symbol) (assignment : List (Term Variable Literal Symbol)) : Option Bool :=
  let run := witnessClauses clauses assignment
  let rank := rank run
  let bound := bound rank run
  if assignment.all (fun atom => isAtom hoApplySymbol atom && unknownMarkerAtom unknownMarker atom && clear excluded atom) &&
      ranked? rank run &&
      (denials clauses).all (fun body => value hoApplySymbol excluded run bound (.conjunction body) == some false) then
    value hoApplySymbol excluded run bound goal
  else none

/-- Check a witness for a goal: the program is covered, and the goal has the
expected value under the witness. -/
def check (excluded unknownMarker : Symbol → Bool) (clauses : List (HornClause Variable Literal Symbol))
    (goal : Term Variable Literal Symbol) (assignment : List (Term Variable Literal Symbol)) (expected : Bool) : Bool :=
  covers hoApplySymbol excluded unknownMarker clauses &&
    witnessValue hoApplySymbol excluded unknownMarker clauses goal assignment == some expected

/-! ## A checked witness has a model -/

variable {hoApplySymbol}

omit [DecidableEq Symbol] [DecidableEq Literal] in
theorem satisfies_foldr_disj {model : Model Literal Symbol (Key Literal Symbol) hoApplySymbol}
    (environment : Environment Variable (Key Literal Symbol)) :
    ∀ cases : List (Term Variable Literal Symbol),
      model.Satisfies environment (cases.foldr .disj .falsity) ↔ ∃ case ∈ cases, model.Satisfies environment case
  | [] => by simp only [List.foldr_nil, List.not_mem_nil, false_and, exists_false, iff_false, Model.Satisfies,
      Model.eval]; exact model.holds_bottom
  | case :: rest => by
      simp only [List.foldr_cons, Model.Satisfies, Model.eval, model.holds_disjunction, List.mem_cons,
        exists_eq_or_imp] at ⊢
      rw [show model.holds (model.eval environment (rest.foldr .disj .falsity)) ↔
        model.Satisfies environment (rest.foldr .disj .falsity) from Iff.rfl, satisfies_foldr_disj environment rest]
      rfl

omit [DecidableEq Symbol] [DecidableEq Literal] in
theorem freeVars_conjunction : ∀ {terms : List (Term Variable Literal Symbol)},
    (∀ term ∈ terms, term.freeVars = []) → (Term.conjunction terms).freeVars = []
  | [], _ => by simp [Term.conjunction, Term.freeVars]
  | term :: rest, closed => by
      simp only [Term.conjunction, List.foldr_cons, Term.freeVars] at closed ⊢
      rw [closed term List.mem_cons_self]
      exact freeVars_conjunction (fun other member => closed other (List.mem_cons_of_mem _ member))

omit [DecidableEq Symbol] [DecidableEq Literal] in
/-- A ground case has no own names: it is the conjunction of its head
equations and its body. -/
theorem case_ground {heads : List Variable} {args body : List (Term Variable Literal Symbol)}
    (data : ∀ arg ∈ args, IsData arg) (goals : ∀ goal ∈ body, IsGoal hoApplySymbol goal) :
    case heads args body =
      Term.conjunction ((heads.zip args).map (fun pair => Term.equal (.var pair.1) pair.2) ++ body) := by
  have closed : caseNames args body = [] := by
    unfold caseNames
    rw [freeVars_conjunction]
    · rfl
    · intro term member
      rcases List.mem_append.mp member with inArgs | inBody
      · exact (data term inArgs).closed
      · exact (goals term inBody).closed
  unfold case
  rw [closed]
  rfl

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem clear_spec {excluded : Symbol → Bool} {goal : Term Variable Literal Symbol}
    (cleared : clear excluded goal = true) : Clear excluded goal := by
  intro symbol args inside
  simp only [clear, List.all_eq_true] at cleared
  simpa using cleared _ inside

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem mem_atoms_conjunction {atom : Term Variable Literal Symbol} :
    ∀ {goals : List (Term Variable Literal Symbol)}, atom ∈ atoms (.conjunction goals) → ∃ goal ∈ goals, atom ∈ atoms goal
  | [], inside => by simp [Term.conjunction, atoms] at inside
  | goal :: rest, inside => by
      simp only [Term.conjunction, List.foldr_cons, atoms, List.mem_append] at inside
      rcases inside with first | later
      · exact ⟨goal, List.mem_cons_self, first⟩
      · obtain ⟨other, member, inner⟩ := mem_atoms_conjunction (goals := rest) later
        exact ⟨other, List.mem_cons_of_mem _ member, inner⟩

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem clear_conjunction {excluded : Symbol → Bool} {goals : List (Term Variable Literal Symbol)}
    (each : ∀ goal ∈ goals, clear excluded goal = true) : Clear excluded (.conjunction goals) := by
  intro symbol args inside
  obtain ⟨goal, member, inner⟩ := mem_atoms_conjunction inside
  exact clear_spec (each goal member) symbol args inner

variable [FreshNames Variable]

omit [FreshNames Variable] in
theorem check_parts {excluded unknownMarker : Symbol → Bool} {clauses : List (HornClause Variable Literal Symbol)}
    {goal : Term Variable Literal Symbol} {assignment : List (Term Variable Literal Symbol)} {expected : Bool}
    (checked : check hoApplySymbol excluded unknownMarker clauses goal assignment expected = true) :
    (∀ clause ∈ clauses, covered hoApplySymbol excluded unknownMarker clause = true) ∧
    (∀ atom ∈ assignment, (isAtom hoApplySymbol atom = true ∧ unknownMarkerAtom unknownMarker atom = true) ∧
      clear excluded atom = true) ∧
    ranked? (rank (witnessClauses clauses assignment)) (witnessClauses clauses assignment) = true ∧
    (∀ body ∈ denials clauses, value hoApplySymbol excluded (witnessClauses clauses assignment)
      (bound (rank (witnessClauses clauses assignment)) (witnessClauses clauses assignment)) (.conjunction body) =
        some false) ∧
    value hoApplySymbol excluded (witnessClauses clauses assignment)
      (bound (rank (witnessClauses clauses assignment)) (witnessClauses clauses assignment)) goal = some expected := by
  simp only [check, covers, witnessValue, Bool.and_eq_true, beq_iff_eq] at checked
  obtain ⟨coveredAll, valued⟩ := checked
  split at valued
  · rename_i ok
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at ok coveredAll
    obtain ⟨⟨unknownMarkers, ranked⟩, denied⟩ := ok
    exact ⟨coveredAll, unknownMarkers, ranked, denied, valued⟩
  · cases valued

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
/-- The witness program is well formed: every clause has a ground atomic head
and a P0 body. -/
theorem witnessClauses_ok {excluded unknownMarker : Symbol → Bool} {clauses : List (HornClause Variable Literal Symbol)}
    {assignment : List (Term Variable Literal Symbol)}
    (coveredAll : ∀ clause ∈ clauses, covered hoApplySymbol excluded unknownMarker clause = true)
    (unknownMarkers : ∀ atom ∈ assignment, (isAtom hoApplySymbol atom = true ∧ unknownMarkerAtom unknownMarker atom = true) ∧
      clear excluded atom = true) :
    ∀ clause ∈ witnessClauses clauses assignment, IsClause hoApplySymbol clause := by
  intro clause member
  rcases List.mem_append.mp member with inProgram | inFacts
  · obtain ⟨inClauses, isDefinite⟩ := List.mem_filter.mp inProgram
    cases clause with
    | definite head body =>
        have ok := coveredAll _ inClauses
        simp only [covered, Bool.and_eq_true, List.all_eq_true] at ok
        exact .definite (isAtom_iff.mp ok.1.1.1) fun goal inside => isGoal_iff.mp (ok.2 goal inside).1
    | goal body => cases isDefinite
  · obtain ⟨atom, inAssignment, rfl⟩ := List.mem_map.mp inFacts
    exact .definite (isAtom_iff.mp (unknownMarkers atom inAssignment).1.1) (by simp)

/-- The witness program as a ground program. -/
def witnessProgram {excluded unknownMarker : Symbol → Bool} {clauses : List (HornClause Variable Literal Symbol)}
    {assignment : List (Term Variable Literal Symbol)}
    (coveredAll : ∀ clause ∈ clauses, covered hoApplySymbol excluded unknownMarker clause = true)
    (unknownMarkers : ∀ atom ∈ assignment, (isAtom hoApplySymbol atom = true ∧ unknownMarkerAtom unknownMarker atom = true) ∧
      clear excluded atom = true) :
    Program Variable Literal Symbol hoApplySymbol :=
  ⟨witnessClauses clauses assignment, witnessClauses_ok coveredAll unknownMarkers⟩

/-- `check_model`: a checked witness has a model. The constructor-key model of
the witness program, with the excluded symbols interpreted by `outside`,
satisfies every clause of the program's completion, for any signature that
closes no marker, not `ho_apply`, and no excluded symbol; its NAF is
complement; the goal has the expected value in every environment; and on the
excluded symbols the interpretation is `outside`. -/
theorem check_model {excluded unknownMarker : Symbol → Bool} {clauses : List (HornClause Variable Literal Symbol)}
    {goal : Term Variable Literal Symbol} {assignment : List (Term Variable Literal Symbol)} {expected : Bool}
    (checked : check hoApplySymbol excluded unknownMarker clauses goal assignment expected = true)
    (signature : Signature Literal Symbol)
    (closed : ∀ key ∈ signature.predicates, unknownMarker key.1 = false ∧ key.1 ≠ hoApplySymbol ∧ excluded key.1 = false)
    (outside : Symbol → List (Key Literal Symbol) → Prop) :
    ∃ interpretation : Symbol → List (Key Literal Symbol) → Prop,
      (∀ symbol, excluded symbol = true → ∀ keys, interpretation symbol keys ↔ outside symbol keys) ∧
      (Model.keys hoApplySymbol interpretation).Models
        (fun clause => clause ∈ (completion clauses signature).clauses : LogicalKb Variable Literal Symbol) ∧
      (Model.keys hoApplySymbol interpretation).ComplementNAF ∧
      ∀ environment, (Model.keys hoApplySymbol interpretation).Satisfies environment goal ↔ expected = true := by
  obtain ⟨coveredAll, unknownMarkers, rankedB, denied, valued⟩ := check_parts checked
  let program := witnessProgram coveredAll unknownMarkers
  have ranked : Ranked (rank (witnessClauses clauses assignment)) program.clauses :=
    ranked_iff_edges.mpr fun edge member => by
      simp only [ranked?, List.all_eq_true, decide_eq_true_eq] at rankedB
      exact rankedB edge member
  refine ⟨combined hoApplySymbol excluded outside program, fun symbol isExcluded keys => by
      simp [combined, isExcluded], ?_, Model.keys_complement _,
    value_sound (outside := outside) valued⟩
  intro clause member environment
  have member : clause ∈ clauses ++ signature.predicates.map (fun key => onlyIf clauses key.1 key.2) ++
      (clashes signature.constructors ++ injections signature.constructors) := member
  rcases List.mem_append.mp member with inFirst | inEquality
  rcases List.mem_append.mp inFirst with inProgram | inOnlyIfs
  -- The program's clauses and denials.
  · have ok := coveredAll clause inProgram
    cases clause with
    | definite head body =>
        simp only [covered, Bool.and_eq_true, List.all_eq_true] at ok
        have atom := isAtom_iff.mp ok.1.1.1
        have bodyGoal : IsGoal hoApplySymbol (.conjunction body) :=
          conjunction_isGoal fun goal inside => isGoal_iff.mp (ok.2 goal inside).1
        have bodyClear : Clear excluded (.conjunction body) := clear_conjunction fun goal inside => (ok.2 goal inside).2
        have inRun : HornClause.definite head body ∈ program.clauses :=
          List.mem_append_left _ (List.mem_filter.mpr ⟨inProgram, rfl⟩)
        cases atom with
        | app ordinary data =>
            have headClear := clear_spec ok.1.2 _ _ (by rw [atoms]; exact List.mem_singleton_self _)
            show (model hoApplySymbol excluded outside program).Satisfies environment (.imp (.conjunction body) _)
            rw [satisfies_imp, goal_iff ranked bodyGoal bodyClear, atom_iff (.app ordinary data) headClear]
            exact fun proof => .clause (.app ordinary data) inRun proof
    | goal body =>
        show (model hoApplySymbol excluded outside program).Satisfies environment (.imp (.conjunction body) .falsity)
        rw [satisfies_imp]
        intro holds
        have refuted := value_sound (program := program) (outside := outside)
          (denied body (List.mem_filterMap.mpr ⟨_, inProgram, rfl⟩)) environment
        exact absurd (refuted.mp holds) (by simp)
  -- The only-if clauses.
  · obtain ⟨⟨symbol, arity⟩, key, rfl⟩ := List.mem_map.mp inOnlyIfs
    obtain ⟨notUnknownMarker, ordinary, notExcluded⟩ := closed _ key
    simp only at notUnknownMarker ordinary notExcluded
    show (model hoApplySymbol excluded outside program).Satisfies environment (.imp (.conjunction [_]) _)
    rw [satisfies_imp, satisfies_conjunction]
    intro holds
    have atomHolds := holds _ List.mem_cons_self
    rw [Model.keys_atom _ environment ordinary] at atomHolds
    simp only [combined, notExcluded, Bool.false_eq_true, ↓reduceIte] at atomHolds
    obtain ⟨args, data, keysEq, proof⟩ := atomHolds
    cases proof with
    | assumption _ inContext => cases inContext
    | clause ground inRun bodyProof =>
        rename_i body
        have inClauses : HornClause.definite (.app symbol args) body ∈ clauses := by
          rcases List.mem_append.mp inRun with inDefinite | inFacts
          · exact (List.mem_filter.mp inDefinite).1
          · obtain ⟨atom, inAssignment, same⟩ := List.mem_map.mp inFacts
            cases same
            have isUnknownMarker := (unknownMarkers _ inAssignment).1.2
            simp only [unknownMarkerAtom] at isUnknownMarker
            rw [isUnknownMarker] at notUnknownMarker
            cases notUnknownMarker
        have ok := coveredAll _ inClauses
        simp only [covered, Bool.and_eq_true, List.all_eq_true] at ok
        have bodyGoals : ∀ goal ∈ body, IsGoal hoApplySymbol goal := fun goal inside => isGoal_iff.mp (ok.2 goal inside).1
        have bodyClear : Clear excluded (.conjunction body) := clear_conjunction fun goal inside => (ok.2 goal inside).2
        rw [List.map_map] at keysEq
        have lengths := congrArg List.length keysEq
        simp only [List.length_map, freshNames_length] at lengths
        rw [satisfies_foldr_disj]
        refine ⟨case _ args body, List.mem_map.mpr ⟨(args, body), ?_, rfl⟩, ?_⟩
        · exact List.mem_filterMap.mpr ⟨_, inClauses, by simp [lengths]⟩
        rw [case_ground data bodyGoals, satisfies_conjunction]
        intro conjunct inside
        rcases List.mem_append.mp inside with inEquations | inBody
        · obtain ⟨⟨head, arg⟩, inZip, rfl⟩ := List.mem_map.mp inEquations
          rw [Model.satisfies_equal]
          have argData := data arg (List.of_mem_zip inZip).2
          rw [eval_data _ environment argData]
          exact eq_of_mem_zip_map (f := (model hoApplySymbol excluded outside program).eval environment ∘ Term.var) (g := dataKey)
            inZip keysEq
        · exact (goal_iff ranked (conjunction_isGoal bodyGoals) bodyClear environment).mpr bodyProof
            |> (satisfies_conjunction environment body).mp |> fun each => each conjunct inBody
  -- The free equality theory.
  · rcases List.mem_append.mp inEquality with inClashes | inInjections
    · simp only [clashes, List.mem_flatMap, List.mem_filterMap] at inClashes
      obtain ⟨first, _, second, _, produced⟩ := inClashes
      split at produced
      · cases produced
      rename_i distinct
      cases produced
      show (model hoApplySymbol excluded outside program).Satisfies environment (.imp (.conjunction [_]) .falsity)
      rw [satisfies_imp, satisfies_conjunction]
      intro holds
      have equal := holds _ List.mem_cons_self
      rw [Model.satisfies_equal] at equal
      have names := freshNames_length (Variable := Variable) [] (first.arity + second.arity)
      exfalso
      cases first with
      | literal value =>
          cases second with
          | literal other =>
              simp only [Constructor.pattern, Model.eval] at equal
              change Key.lit _ = Key.lit _ at equal
              exact distinct (by cases equal; rfl)
          | application _ _ =>
              simp only [Constructor.pattern, Model.eval] at equal
              change Key.lit _ = Key.app _ _ at equal
              cases equal
      | application symbol count =>
          cases second with
          | literal _ =>
              simp only [Constructor.pattern, Model.eval] at equal
              change Key.app _ _ = Key.lit _ at equal
              cases equal
          | application other otherCount =>
              simp only [Constructor.pattern, Model.eval, Constructor.arity] at equal names
              change Key.app _ _ = Key.app _ _ at equal
              simp only [Key.app.injEq] at equal
              obtain ⟨sameSymbol, sameArgs⟩ := equal
              have counts := congrArg List.length sameArgs
              simp only [List.length_map, List.length_take, List.length_drop, names] at counts
              exact distinct (by rw [sameSymbol]; congr 1; omega)
    · simp only [injections, List.mem_flatMap] at inInjections
      obtain ⟨constructor, _, produced⟩ := inInjections
      cases constructor with
      | literal _ => cases produced
      | application symbol count =>
          simp only [injective, List.mem_map] at produced
          obtain ⟨⟨left, right⟩, inZip, rfl⟩ := produced
          show (model hoApplySymbol excluded outside program).Satisfies environment (.imp (.conjunction [_]) (.equal _ _))
          rw [satisfies_imp, satisfies_conjunction, Model.satisfies_equal]
          intro holds
          have equal := holds _ List.mem_cons_self
          rw [Model.satisfies_equal] at equal
          simp only [Model.eval, List.map_map] at equal
          change Key.app _ _ = Key.app _ _ at equal
          simp only [Key.app.injEq] at equal
          exact eq_of_mem_zip_map (f := (model hoApplySymbol excluded outside program).eval environment ∘ Term.var)
            (g := (model hoApplySymbol excluded outside program).eval environment ∘ Term.var) inZip equal.2

/-! ## Witnesses that realize an admission signature

A witness program mentions no guard symbol, so the witness model may interpret
the guards exactly as the admission signature declares them: a domain's
membership holds of its members' keys, `D_all` of every domain's, and `P_n`
of the registered references of arity `n` (`guardTruth`). When each guard
symbol has one role and none is `ho_apply` (`Separated`), that interpretation
realizes the signature (`realizes_guards`). -/

open AdmissionSignature InductiveDomains

variable {Domain : Type}

/-- A symbol the signature's guards use: a domain's membership, `D_all`, or a
predicate range `P_n`. -/
def IsGuard (naming : Naming Domain Symbol) (symbol : Symbol) : Prop :=
  (∃ domain, symbol = naming.membershipSymbol domain) ∨ symbol = naming.dataSymbol ∨
    ∃ arity, symbol = naming.predicateSymbol arity

/-- Guard symbols with one role each, none of them `ho_apply`. -/
structure Separated (naming : Naming Domain Symbol) (hoApplySymbol : Symbol) : Prop where
  membership : ∀ first second, naming.membershipSymbol first = naming.membershipSymbol second → first = second
  predicate : ∀ first second, naming.predicateSymbol first = naming.predicateSymbol second → first = second
  dataMembership : ∀ domain, naming.dataSymbol ≠ naming.membershipSymbol domain
  predicateMembership : ∀ arity domain, naming.predicateSymbol arity ≠ naming.membershipSymbol domain
  predicateData : ∀ arity, naming.predicateSymbol arity ≠ naming.dataSymbol
  hoApply : ¬ IsGuard naming hoApplySymbol

omit [DecidableEq Variable] [DecidableEq Literal] in
/-- A tree has the same key in every constructor-key model. -/
theorem denote_keys (first second : Symbol → List (Key Literal Symbol) → Prop) (tree : Tree Symbol) :
    denote (Model.keys hoApplySymbol first) tree = denote (Model.keys hoApplySymbol second) tree := by
  refine Tree.rec
    (motive_1 := fun tree => denote (Model.keys hoApplySymbol first) tree = denote (Model.keys hoApplySymbol second) tree)
    (motive_2 := fun children => children.map (denote (Model.keys hoApplySymbol first)) =
      children.map (denote (Model.keys hoApplySymbol second))) ?_ rfl ?_ tree
  · intro symbol children ih
    simp only [denote]
    exact congrArg (Key.app symbol) ih
  · intro head tail ihHead ihTail
    simp only [List.map_cons, ihHead, ihTail]

/-- The exact truth of guard atoms over keys: a domain's membership holds of
its members, `D_all` of every domain's, `P_n` of the registered references of
arity `n`; nothing else. -/
def guardTruth (snapshot : SignatureSnapshot Domain Symbol) (hoApplySymbol : Symbol) :
    Symbol → List (Key Literal Symbol) → Prop
  | symbol, [value] =>
      (∃ domain, symbol = snapshot.naming.membershipSymbol domain ∧
        ∃ tree, Member snapshot.signature.data.definitions domain tree ∧
          denote (Model.keys hoApplySymbol (fun _ _ => False)) tree = value) ∨
      (symbol = snapshot.naming.dataSymbol ∧
        ∃ tree, InUnion snapshot.signature.data.definitions snapshot.signature.data.domains tree ∧
          denote (Model.keys hoApplySymbol (fun _ _ => False)) tree = value) ∨
      (∃ arity, symbol = snapshot.naming.predicateSymbol arity ∧
        ∃ registered, snapshot.Registered registered arity ∧ (Key.app registered [] : Key Literal Symbol) = value)
  | _, _ => False

omit [DecidableEq Variable] [DecidableEq Literal] in
/-- `realizes_guards`: an interpretation that agrees with the exact guard
truth on the guard symbols realizes a separated signature. -/
theorem realizes_guards {snapshot : SignatureSnapshot Domain Symbol} (separated : Separated snapshot.naming hoApplySymbol)
    {interpretation : Symbol → List (Key Literal Symbol) → Prop}
    (agree : ∀ symbol, IsGuard snapshot.naming symbol → ∀ keys,
      interpretation symbol keys ↔ guardTruth snapshot hoApplySymbol symbol keys) :
    Realizes snapshot (Model.keys hoApplySymbol interpretation) := by
  have ordinary : ∀ symbol, IsGuard snapshot.naming symbol → symbol ≠ hoApplySymbol :=
    fun symbol guard same => separated.hoApply (same ▸ guard)
  have keys := denote_keys (hoApplySymbol := hoApplySymbol) (fun _ _ => False) interpretation
  refine ⟨?_, ?_, ?_⟩
  · intro domain value
    have guard : IsGuard snapshot.naming (snapshot.naming.membershipSymbol domain) := .inl ⟨domain, rfl⟩
    show resolveKey hoApplySymbol interpretation (snapshot.naming.membershipSymbol domain) [value] ↔ _
    rw [resolveKey_ordinary interpretation (ordinary _ guard), agree _ guard]
    simp only [guardTruth]
    constructor
    · rintro (⟨other, same, tree, member, denotes⟩ | ⟨same, _⟩ | ⟨arity, same, _⟩)
      · rw [separated.membership _ _ same]
        exact ⟨tree, member, (keys tree).symm.trans denotes⟩
      · exact absurd same.symm (separated.dataMembership domain)
      · exact absurd same.symm (separated.predicateMembership arity domain)
    · rintro ⟨tree, member, denotes⟩
      exact .inl ⟨domain, rfl, tree, member, (keys tree).trans denotes⟩
  · intro value
    have guard : IsGuard snapshot.naming snapshot.naming.dataSymbol := .inr (.inl rfl)
    show resolveKey hoApplySymbol interpretation snapshot.naming.dataSymbol [value] ↔ _
    rw [resolveKey_ordinary interpretation (ordinary _ guard), agree _ guard]
    simp only [guardTruth, Range.Contains]
    constructor
    · rintro (⟨domain, same, _⟩ | ⟨_, tree, member, denotes⟩ | ⟨arity, same, _⟩)
      · exact absurd same (separated.dataMembership domain)
      · exact ⟨tree, member, (keys tree).symm.trans denotes⟩
      · exact absurd same.symm (separated.predicateData arity)
    · rintro ⟨tree, member, denotes⟩
      exact .inr (.inl ⟨trivial, tree, member, (keys tree).trans denotes⟩)
  · intro arity value
    have guard : IsGuard snapshot.naming (snapshot.naming.predicateSymbol arity) := .inr (.inr ⟨arity, rfl⟩)
    show resolveKey hoApplySymbol interpretation (snapshot.naming.predicateSymbol arity) [value] ↔ _
    rw [resolveKey_ordinary interpretation (ordinary _ guard), agree _ guard]
    simp only [guardTruth, SignatureSnapshot.PredicateMember, reference]
    constructor
    · rintro (⟨domain, same, _⟩ | ⟨same, _⟩ | ⟨other, same, registered, declared, denotes⟩)
      · exact absurd same (separated.predicateMembership arity domain)
      · exact absurd same (separated.predicateData arity)
      · rw [separated.predicate _ _ same]
        exact ⟨registered, declared, denotes⟩
    · rintro ⟨registered, declared, denotes⟩
      exact .inr (.inr ⟨arity, rfl, registered, declared, denotes⟩)

end AnthillModKbSpec.Open
