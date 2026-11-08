import AnthillModKbSpec.Resolution.Tabled.Calls

/-! # What the classification decides (S23)

Each condition of the fast fragment's admission is decided by a total
function, and these theorems state what it decides:

- **Data-term outputs** are the greatest post-fixpoint of the local check
  (`dataOutputs_post`, `dataOutputs_greatest`), since `flow` is monotone.
- **Complete** is the conjunction of the local conditions over the dependency
  closure (`complete_iff`), and a predicate is budgeted exactly when a growth
  note in its closure names the growing call or answer
  (`complete_iff_growth`).
- **Profiles** (`profile_p1`, `profile_p2`, `profile_undecided`): P1 has no
  blocker and no note, and is complete (`p1_complete`).
- **Locality** (`mem_blockers`, `mem_notes`, `complete_iff`, `degree_le`): a
  predicate's class follows from its own clauses, the denials over it, and the
  classes of the predicates it calls; a query's from those it uses
  (`mem_queryBlockers`).
- **Determinism** (`deterministic_unique`): no input values match two of a
  deterministic predicate's clauses. -/

namespace AnthillModKbSpec.Tabled

open Admission Answers

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

attribute [local instance] Machine.termEq

/-! ## Monotonicity of the data-term analysis -/

theorem Frame.small_mono (frame : Frame Variable Literal Symbol) {small small' : List Variable}
    (sub : ∀ name ∈ small, name ∈ small') {term : Term Variable Literal Symbol} (accepted : frame.small small term = true) :
    frame.small small' term = true := by
  unfold Frame.small at accepted ⊢
  simp only [Bool.or_eq_true] at accepted ⊢
  rcases accepted with first | named
  · exact .inl first
  · refine .inr ?_
    cases term with
    | var name => simp only [List.contains_eq_mem, decide_eq_true_eq] at named ⊢; exact sub name named
    | _ => simp at named

namespace Program

variable (program : Program Variable Literal Symbol)

/-- `flow` keeps more names for more predicates with data-term outputs and
more names before. -/
theorem flow_mono {info info' : Symbol → Bool} (more : ∀ predicate, info predicate = true → info' predicate = true) :
    ∀ (frame : Frame Variable Literal Symbol) (goal : Term Variable Literal Symbol) {small small' : List Variable},
      (∀ name ∈ small, name ∈ small') →
        ∀ name ∈ program.flow info frame small goal, name ∈ program.flow info' frame small' goal
  | frame, .conj left right, small, small', sub => by
      simp only [flow]
      exact flow_mono more frame right (flow_mono more frame left sub)
  | frame, .disj left right, small, small', sub => by
      simp only [flow]
      intro name member
      simp only [List.mem_filter, List.contains_eq_mem, decide_eq_true_eq] at member ⊢
      exact ⟨flow_mono more frame left sub name member.1, flow_mono more frame right sub name member.2⟩
  | frame, .equal left right, small, small', sub => by
      simp only [flow]
      intro name member
      simp only [List.mem_append] at member ⊢
      rcases member with (old | fromLeft) | fromRight
      · exact .inl (.inl (sub name old))
      · split at fromLeft
        · rename_i accepted
          exact .inl (.inr (by rw [ite_eq_left (frame.small_mono sub accepted)]; exact fromLeft))
        · cases fromLeft
      · split at fromRight
        · rename_i accepted
          exact .inr (by rw [ite_eq_left (frame.small_mono sub accepted)]; exact fromRight)
        · cases fromRight
  | frame, .existsVar name body, small, small', sub => by
      simp only [flow]
      intro other member
      simp only [List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at member ⊢
      rcases member with ⟨inside, different⟩ | back
      · refine .inl ⟨flow_mono more (frame.enter name) body (fun x inner => ?_) other inside, different⟩
        simp only [List.mem_filter, bne_iff_ne, ne_eq] at inner ⊢
        exact ⟨sub x inner.1, inner.2⟩
      · split at back
        · rename_i present
          simp only [List.mem_singleton] at back
          subst back
          have : small'.contains other = true := by simpa using sub other (by simpa using present)
          exact .inr (by rw [ite_eq_left this]; exact List.mem_singleton_self _)
        · cases back
  | frame, .forallVar name body, small, small', sub => by
      simp only [flow]
      intro other member
      simp only [List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at member ⊢
      rcases member with ⟨inside, different⟩ | back
      · refine .inl ⟨flow_mono more (frame.enter name) body (fun x inner => ?_) other inside, different⟩
        simp only [List.mem_filter, bne_iff_ne, ne_eq] at inner ⊢
        exact ⟨sub x inner.1, inner.2⟩
      · split at back
        · rename_i present
          simp only [List.mem_singleton] at back
          subst back
          have : small'.contains other = true := by simpa using sub other (by simpa using present)
          exact .inr (by rw [ite_eq_left this]; exact List.mem_singleton_self _)
        · cases back
  | frame, .imp _ conclusion, small, small', sub => by
      simp only [flow]
      exact flow_mono more frame conclusion sub
  | frame, .app symbol args, small, small', sub => by
      rw [flow_app, flow_app]
      intro name member
      cases callEq : program.callOf? (.app symbol args) with
      | none => rw [callEq] at member; exact sub name member
      | some call =>
          obtain ⟨predicate, callArgs⟩ := call
          rw [callEq] at member
          dsimp only at member ⊢
          cases ioEq : program.io? predicate callArgs with
          | none => rw [ioEq] at member; exact sub name member
          | some io =>
              obtain ⟨inputs, outputs⟩ := io
              rw [ioEq] at member
              dsimp only at member ⊢
              by_cases accepted : (info predicate && inputs.all (frame.small small)) = true
              · rw [ite_eq_left accepted] at member
                simp only [Bool.and_eq_true, List.all_eq_true] at accepted
                rw [ite_eq_left (by
                  simp only [Bool.and_eq_true, List.all_eq_true]
                  exact ⟨more predicate accepted.1, fun term inside => frame.small_mono sub (accepted.2 term inside)⟩)]
                rcases List.mem_append.mp member with old | new
                · exact List.mem_append_left _ (sub name old)
                · exact List.mem_append_right _ new
              · rw [ite_eq_right accepted] at member
                split
                · exact List.mem_append_left _ (sub name member)
                · exact sub name member
  | _, .var _, _, _, sub | _, .lit _, _, _, sub | _, .truth, _, _, sub | _, .falsity, _, _, sub
  | _, .defaultNeg _, _, _, sub | _, .dictionaryCall _ _ _ _, _, _, sub => by
      simp only [flow, callOf?]; exact sub

theorem flowBody_mono {info info' : Symbol → Bool} (more : ∀ predicate, info predicate = true → info' predicate = true)
    (frame : Frame Variable Literal Symbol) :
    ∀ (body : List (Term Variable Literal Symbol)) {small small' : List Variable}, (∀ name ∈ small, name ∈ small') →
      ∀ name ∈ program.flowBody info frame small body, name ∈ program.flowBody info' frame small' body
  | [], _, _, sub => sub
  | goal :: rest, _, _, sub => flowBody_mono more frame rest (program.flow_mono more frame goal sub)

theorem outputsOk_mono {small large : List Symbol} (sub : ∀ predicate ∈ small, predicate ∈ large)
    {predicate : Symbol} (ok : program.outputsOk small predicate = true) : program.outputsOk large predicate = true := by
  simp only [outputsOk, List.all_eq_true] at ok ⊢
  intro clause member
  have clauseOk := ok clause member
  simp only [clauseOutputs] at clauseOk ⊢
  split at clauseOk
  · rename_i inputs outputs ioEq
    simp only [List.all_eq_true] at clauseOk ⊢
    intro output inside
    exact Frame.small_mono _ (program.flowBody_mono (fun other found => by
      simp only [List.contains_eq_mem, decide_eq_true_eq] at found ⊢; exact sub other found) _ _ fun _ member => member)
      (clauseOk output inside)
  · simp

/-! ## Data-term outputs: the greatest post-fixpoint -/

/-- Every predicate with data-term outputs gives them, given the others. -/
theorem dataOutputs_post {predicate : Symbol} (member : predicate ∈ program.dataOutputs) :
    program.outputsOk program.dataOutputs predicate = true :=
  greatest_post _ member

/-- Every set of predicates that gives data-term outputs, given itself, has
data-term outputs: `dataOutputs` is the greatest such set. -/
theorem dataOutputs_greatest {post : List Symbol} (inside : ∀ predicate ∈ post, predicate ∈ program.vertices)
    (accepted : ∀ predicate ∈ post, program.outputsOk post predicate = true) :
    ∀ predicate ∈ post, predicate ∈ program.dataOutputs :=
  greatest_ge (ok := program.outputsOk) (fun _ _ sub _ ok => program.outputsOk_mono sub ok) inside accepted

end Program

/-- A vertex deflation drops was rejected given a superset of the result. -/
theorem deflate_rejects {α : Type} {ok : List α → α → Bool} {vertex : α} :
    ∀ (fuel : Nat) (set : List α), vertex ∈ set → vertex ∉ deflate ok fuel set →
      ∃ stage : List α, (∀ other ∈ deflate ok fuel set, other ∈ stage) ∧ ok stage vertex = false
  | 0, _, member, missing => absurd member missing
  | fuel + 1, set, member, missing => by
      simp only [deflate] at missing ⊢
      split at missing
      · exact absurd member missing
      · rename_i different
        rw [ite_eq_right different]
        by_cases kept : vertex ∈ set.filter (ok set)
        · exact deflate_rejects fuel _ kept missing
        · refine ⟨set, fun other inside => (List.mem_filter.mp (deflate_sub fuel _ other inside)).1, ?_⟩
          simp only [List.mem_filter, not_and] at kept
          cases okEq : ok set vertex
          · rfl
          · exact absurd okEq (kept member)

namespace Program

variable (program : Program Variable Literal Symbol)

/-- A vertex without data-term outputs fails the check given `dataOutputs`. -/
theorem not_dataOutputs {predicate : Symbol} (vertex : predicate ∈ program.vertices)
    (missing : predicate ∉ program.dataOutputs) : program.outputsOk program.dataOutputs predicate = false := by
  obtain ⟨stage, sub, rejected⟩ := deflate_rejects (ok := program.outputsOk) _ _ vertex missing
  cases okEq : program.outputsOk program.dataOutputs predicate
  · rfl
  · have := program.outputsOk_mono sub okEq
    rw [rejected] at this
    cases this

/-! ## Components -/

omit [DecidableEq Variable] [DecidableEq Literal] in
/-- The members of a member's component are the component's. -/
theorem component_same {predicate member : Symbol} (inside : member ∈ program.component predicate) (other : Symbol) :
    other ∈ program.component member ↔ other ∈ program.component predicate := by
  rcases program.mem_component.mp inside with rfl | ⟨there, back⟩
  · exact Iff.rfl
  · constructor
    · intro found
      rcases program.mem_component.mp found with rfl | ⟨reached, returns⟩
      · exact inside
      · exact program.mem_component.mpr (.inr ⟨program.reach_trans there reached, program.reach_trans returns back⟩)
    · intro found
      rcases program.mem_component.mp found with rfl | ⟨reached, returns⟩
      · exact program.mem_component.mpr (.inr ⟨back, there⟩)
      · exact program.mem_component.mpr (.inr ⟨program.reach_trans back reached, program.reach_trans returns there⟩)

theorem all_congr {α : Type} {first second : List α} (same : ∀ item, item ∈ first ↔ item ∈ second) (test : α → Bool) :
    first.all test = second.all test := by
  cases firstEq : first.all test <;> cases secondEq : second.all test
  · rfl
  · simp only [List.all_eq_false, List.all_eq_true] at firstEq secondEq
    obtain ⟨item, member, failed⟩ := firstEq
    exact absurd (secondEq item ((same item).mp member)) (by simpa using failed)
  · simp only [List.all_eq_false, List.all_eq_true] at firstEq secondEq
    obtain ⟨item, member, failed⟩ := secondEq
    exact absurd (firstEq item ((same item).mpr member)) (by simpa using failed)
  · rfl

/-- Members of a component settle together. -/
theorem settles_same {predicate member : Symbol} (inside : member ∈ program.component predicate) :
    program.settles member = program.settles predicate := by
  simp only [settles, all_congr (program.component_same inside)]

/-! ## Complete, and the growth notes -/

omit [DecidableEq Variable] [DecidableEq Literal] in
theorem mem_closure_self (predicate : Symbol) : predicate ∈ program.closure predicate :=
  program.mem_closure.mpr (.inl rfl)

omit [DecidableEq Variable] [DecidableEq Literal] in
/-- What a predicate's closure holds: itself and its callees' closures. -/
theorem closure_step {predicate other : Symbol} :
    other ∈ program.closure predicate ↔ other = predicate ∨
      ∃ callee, (predicate, callee) ∈ program.edges ∧ other ∈ program.closure callee := by
  rw [program.mem_closure, program.reach_step]
  constructor
  · rintro (same | ⟨callee, edge, rfl | inside⟩)
    · exact .inl same
    · exact .inr ⟨_, edge, program.mem_closure_self _⟩
    · exact .inr ⟨callee, edge, program.mem_closure.mpr (.inr inside)⟩
  · rintro (same | ⟨callee, edge, inside⟩)
    · exact .inl same
    · rcases program.mem_closure.mp inside with rfl | deeper
      · exact .inr ⟨other, edge, .inl rfl⟩
      · exact .inr ⟨callee, edge, .inr deeper⟩

/-- **Locality of the cost class.** Complete exactly when locally complete
with every callee complete. -/
theorem complete_iff {predicate : Symbol} :
    program.complete predicate = true ↔
      program.localComplete predicate = true ∧ ∀ callee, (predicate, callee) ∈ program.edges → program.complete callee = true := by
  simp only [complete, List.all_eq_true]
  constructor
  · intro every
    refine ⟨every predicate (program.mem_closure_self predicate), fun callee edge member inside => ?_⟩
    exact every member (program.closure_step.mpr (.inr ⟨callee, edge, inside⟩))
  · rintro ⟨own, callees⟩ member inside
    rcases program.closure_step.mp inside with rfl | ⟨callee, edge, deeper⟩
    · exact own
    · exact callees callee edge member deeper

/-! ## The growth notes name what makes a predicate budgeted -/

omit [DecidableEq Literal] in
/-- The notes a scan finds are generic universal goals and hypotheses. -/
theorem scan_notes {site : Site} :
    ∀ {rigid bound : List Variable} {path : List Nat} {goal : Term Variable Literal Symbol} {note : Note Variable Literal Symbol},
      note ∈ (program.scan site rigid bound path goal).found.notes → note.reason = .universal ∨ note.reason = .hypothesis
  | _, _, _, .conj _ _, _, member => by
      simp only [scan] at member
      rcases List.mem_append.mp member with here | there
      · exact scan_notes here
      · exact scan_notes there
  | _, _, _, .disj _ _, _, member => by
      simp only [scan] at member
      rcases List.mem_append.mp member with here | there
      · exact scan_notes here
      · exact scan_notes there
  | _, _, _, .defaultNeg _, _, member => by
      simp only [scan] at member
      rcases List.mem_append.mp member with here | there
      · exact scan_notes here
      · cases there
  | _, _, _, .existsVar _ _, _, member => by
      simp only [scan] at member
      rcases List.mem_append.mp member with here | there
      · exact scan_notes here
      · cases there
  | _, _, _, .forallVar _ _, _, member => by
      simp only [scan] at member
      rcases List.mem_append.mp member with here | there
      · exact scan_notes here
      · simp only [List.mem_singleton] at there; subst there; exact .inl rfl
  | _, _, _, .imp antecedent _, _, member => by
      simp only [scan] at member
      rcases List.mem_append.mp member with here | there
      · by_cases decided : (harrop antecedent && !(atomic antecedent && antecedent.freeVars.isEmpty)) = true
        · rw [ite_eq_left decided] at here
          simp only [List.mem_singleton] at here
          rw [here]
          exact .inr rfl
        · rw [ite_eq_right decided] at here
          cases here
      · exact scan_notes there
  | _, _, _, .equal _ _, _, member => by
      simp only [scan] at member
      split at member <;> simp [Found.ofBlockers] at member
  | _, _, _, .app _ _, _, member => by
      simp only [scan] at member
      split at member
      · split at member
        · split at member
          · simp [Found.ofBlockers] at member
          · simp only [scanCall] at member
            split at member <;> simp [Found.ofBlockers] at member
        · simp [Found.ofBlockers] at member
      · split at member
        · simp [Found.ofBlockers] at member
        · split at member
          · simp [Found.ofBlockers] at member
          · simp only [scanCall] at member
            split at member <;> simp [Found.ofBlockers] at member
  | _, _, _, .var _, _, member | _, _, _, .lit _, _, member | _, _, _, .truth, _, member
  | _, _, _, .falsity, _, member | _, _, _, .dictionaryCall _ _ _ _, _, member => by
      simp [scan, Found.ofBlockers, Found.empty] at member

omit [DecidableEq Literal] in
theorem scanBody_notes {index : Nat} {rigid : List Variable} :
    ∀ {position : Nat} {bound : List Variable} {body : List (Term Variable Literal Symbol)} {note : Note Variable Literal Symbol},
      note ∈ (program.scanBody index rigid position bound body).1.notes → note.reason = .universal ∨ note.reason = .hypothesis
  | _, _, [], _, member => by simp [scanBody, Found.empty] at member
  | position, bound, goal :: rest, note, member => by
      simp only [scanBody] at member
      rcases List.mem_append.mp member with here | there
      · exact program.scan_notes here
      · exact scanBody_notes there

omit [DecidableEq Literal] in
/-- The notes of a predicate's clauses are generic universal goals and hypotheses. -/
theorem found_notes {predicate : Symbol} {note : Note Variable Literal Symbol}
    (member : note ∈ (program.found predicate).notes) : note.reason = .universal ∨ note.reason = .hypothesis := by
  unfold found at member
  generalize program.definitions predicate = clauses at member
  induction clauses with
  | nil => simp [Found.empty] at member
  | cons clause rest ih =>
      obtain ⟨index, args, body⟩ := clause
      simp only [List.foldr_cons] at member
      rcases List.mem_append.mp (show note ∈ (program.clauseFound predicate index args body).notes ++ _ from member)
        with here | there
      · simp only [clauseFound] at here
        split at here
        · split at here
          · rcases List.mem_append.mp here with first | second
            · rcases List.mem_append.mp first with head | body
              · simp [Found.ofBlockers] at head
              · exact program.scanBody_notes body
            · simp [Found.ofBlockers] at second
          · simp [Found.ofBlockers] at here
        · simp [Found.ofBlockers] at here
      · exact ih there

omit [DecidableEq Variable] [DecidableEq Literal] in
theorem negationNotes_reason {negations : List (Negation Variable Literal Symbol)} {note : Note Variable Literal Symbol}
    (member : note ∈ program.negationNotes negations) : note.reason = .cyclicNegation := by
  simp only [negationNotes, List.mem_filterMap] at member
  obtain ⟨negation, _, produced⟩ := member
  split at produced
  · cases produced; rfl
  · cases produced

/-- A growth note of a predicate's own clauses comes from a recursive call
whose inputs are not data terms, a component that does not settle, or a
hypothesis. -/
theorem growth_of_ownNotes {predicate : Symbol} {note : Note Variable Literal Symbol}
    (member : note ∈ program.ownNotes predicate) (growth : note.reason.growth = true) :
    (∃ pair ∈ program.recursiveSites predicate, pair.2.small = false) ∨ program.settles predicate = false ∨
      ∃ other ∈ (program.found predicate).notes, other.reason = .hypothesis := by
  simp only [ownNotes, List.mem_append] at member
  rcases member with (growthNote | foundNote) | negationNote
  · simp only [growthNotes, List.mem_append, List.mem_map, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at growthNote
    rcases growthNote with ⟨pair, ⟨inside, notSmall⟩, _⟩ | answer
    · exact .inl ⟨pair, inside, notSmall⟩
    · split at answer
      · cases answer
      · rename_i unsettled
        exact .inr (.inl (by simpa using unsettled))
  · rcases program.found_notes foundNote with universal | hypothesis
    · rw [universal] at growth; cases growth
    · exact .inr (.inr ⟨note, foundNote, hypothesis⟩)
  · rw [program.negationNotes_reason negationNote] at growth; cases growth

omit [DecidableEq Variable] [DecidableEq Literal] in
theorem reach_vertices {predicate other : Symbol} (member : other ∈ program.reach predicate) : other ∈ program.vertices := by
  have path := program.reach_iff.mp member
  induction path with
  | single edge => exact program.edges_targets _ edge
  | tail _ edge => exact program.edges_targets _ edge

omit [DecidableEq Variable] [DecidableEq Literal] in
theorem edges_sources : ∀ edge ∈ program.edges, edge.1 ∈ program.vertices := by
  intro edge member
  simp only [vertices, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
  exact .inr ⟨edge, member, by simp⟩

omit [DecidableEq Variable] [DecidableEq Literal] in
theorem definitions_vertex {predicate : Symbol}
    {entry : Nat × List (Term Variable Literal Symbol) × List (Term Variable Literal Symbol)}
    (member : entry ∈ program.definitions predicate) : predicate ∈ program.vertices := by
  obtain ⟨head, clause, headEq⟩ := program.mem_definitions.mp member
  simp only [vertices, List.mem_eraseDups, List.mem_append]
  refine .inl ?_
  simp only [heads, List.mem_filterMap]
  exact ⟨(entry.1, .definite head entry.2.2), clause, by simp [headEq]⟩

/-- An argument at a position of a mode is in the indexed arguments with that mode. -/
theorem mem_select_zip {α : Type} {mode : Mode} {arg : α} :
    ∀ {modes : List Mode} {args : List α} {start : Nat}, modes.length = args.length → arg ∈ select mode modes args →
      ∃ position, ((arg, position), mode) ∈ (args.zipIdx start).zip modes
  | [], _, _, _, member => by simp [select] at member
  | _ :: _, [], _, lengths, _ => by simp at lengths
  | first :: modes, other :: args, start, lengths, member => by
      simp only [select] at member
      simp only [List.zipIdx_cons, List.zip_cons_cons, List.mem_cons]
      split at member
      · rename_i same
        rcases List.mem_cons.mp member with rfl | inside
        · exact ⟨start, .inl (by rw [same])⟩
        · obtain ⟨position, found⟩ := mem_select_zip (start := start + 1) (by simpa using lengths) inside
          exact ⟨position, .inr found⟩
      · obtain ⟨position, found⟩ := mem_select_zip (start := start + 1) (by simpa using lengths) member
        exact ⟨position, .inr found⟩

/-- A component that does not settle has a member in the closure with a
growing answer. -/
theorem growingAnswer_of_unsettled {predicate member : Symbol} (inside : member ∈ program.closure predicate)
    (unsettled : program.settles member = false) :
    ∃ other ∈ program.closure predicate, ∃ note ∈ program.growthNotes other, note.reason = .growingAnswer := by
  simp only [settles, Bool.or_eq_false_iff, List.all_eq_false] at unsettled
  obtain ⟨⟨other, otherMember, noData⟩, ⟨decreasing, decreasingMember, notDecreasing⟩⟩ := unsettled
  have vertex : other ∈ program.vertices := by
    rcases program.mem_component.mp otherMember with rfl | ⟨reached, _⟩
    · by_cases present : other ∈ program.vertices
      · exact present
      · have reachEmpty : ∀ found, found ∉ program.reach other := fun found reached => by
          obtain ⟨callee, edge, _⟩ := program.reach_step.mp reached
          exact present (program.edges_sources _ edge)
        rcases program.mem_component.mp decreasingMember with rfl | ⟨reached, _⟩
        · obtain ⟨pair, pairMember, _⟩ := List.all_eq_false.mp (Bool.eq_false_iff.mpr notDecreasing)
          have inSites := (List.mem_filter.mp pairMember).1
          simp only [callSites, List.mem_flatMap] at inSites
          obtain ⟨entry, definition, _⟩ := inSites
          exact absurd (program.definitions_vertex definition) present
        · exact absurd reached (reachEmpty _)
    · exact program.reach_vertices reached
  have missing : other ∉ program.dataOutputs := by
    simpa [dataInfo] using noData
  have rejected := program.not_dataOutputs vertex missing
  simp only [outputsOk, List.all_eq_false] at rejected
  obtain ⟨⟨index, args, body⟩, definition, failed⟩ := rejected
  simp only [clauseOutputs] at failed
  split at failed
  · rename_i inputs outputs ioEq
    simp only [Bool.not_eq_true, List.all_eq_false] at failed
    obtain ⟨output, outputMember, notSmall⟩ := failed
    unfold io? at ioEq
    split at ioEq
    · rename_i modes modesEq
      split at ioEq
      · rename_i lengths
        cases ioEq
        obtain ⟨position, zipped⟩ := mem_select_zip (start := 0) lengths outputMember
        refine ⟨other, program.closure_trans inside (program.component_closure otherMember), ?_⟩
        have settled : program.settles other = false := by
          rw [program.settles_same otherMember]
          simp only [settles, Bool.or_eq_false_iff, List.all_eq_false]
          exact ⟨⟨other, otherMember, noData⟩, ⟨decreasing, decreasingMember, notDecreasing⟩⟩
        refine ⟨⟨.head index, [position], output, .growingAnswer⟩, ?_, rfl⟩
        simp only [growthNotes, settled, Bool.false_eq_true, ite_false, List.mem_append, List.mem_flatMap]
        refine .inr ⟨(index, args, body), definition, ?_⟩
        rw [modesEq]
        simp only [lengths, ite_true, List.mem_filterMap]
        refine ⟨((output, position), .output), zipped, ?_⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true, true_and]
        rw [ite_eq_left]
        have info : program.dataInfo = fun found => decide (found ∈ program.dataOutputs) := by
          funext found; simp [dataInfo]
        rw [info]
        simpa using notSmall
      · cases ioEq
    · cases ioEq
  · exact absurd rfl failed

theorem mem_ownNotes {predicate : Symbol} {note : Note Variable Literal Symbol} :
    note ∈ program.ownNotes predicate ↔ note ∈ program.growthNotes predicate ∨ note ∈ (program.found predicate).notes ∨
      note ∈ program.negationNotes (program.found predicate).negations := by
  simp [ownNotes]

/-- **Budgeted exactly when a growth note names it.** A predicate is complete
exactly when no clause of its dependency closure has a growth note: a
recursive call whose inputs are not data terms, a growing answer in a
component that does not settle, or an undecided hypothesis. -/
theorem complete_iff_growth {predicate : Symbol} :
    program.complete predicate = true ↔
      ∀ member ∈ program.closure predicate, ∀ note ∈ program.ownNotes member, note.reason.growth = false := by
  constructor
  · intro complete member inside note noteMember
    have own := List.all_eq_true.mp complete member inside
    simp only [localComplete, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at own
    obtain ⟨⟨small, settled⟩, noHypothesis⟩ := own
    cases growth : note.reason.growth
    · rfl
    · rcases program.growth_of_ownNotes noteMember growth with ⟨pair, pairMember, notSmall⟩ | unsettled | ⟨other, otherMember, hypothesis⟩
      · rw [small pair pairMember] at notSmall; cases notSmall
      · rw [settled] at unsettled; cases unsettled
      · exact absurd hypothesis (noHypothesis other otherMember)
  · intro noGrowth
    simp only [complete, List.all_eq_true]
    intro member inside
    simp only [localComplete, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq]
    refine ⟨⟨fun pair pairMember => ?_, ?_⟩, fun other otherMember hypothesis => ?_⟩
    · cases small : pair.2.small
      · have note := noGrowth member inside ⟨pair.1, pair.2.path, pair.2.formula, .growingCall⟩
          (program.mem_ownNotes.mpr (.inl (by
            simp only [growthNotes, List.mem_append, List.mem_map, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true]
            exact .inl ⟨pair, ⟨pairMember, small⟩, rfl⟩)))
        cases note
      · rfl
    · cases settled : program.settles member
      · obtain ⟨other, otherInside, note, noteMember, reason⟩ := program.growingAnswer_of_unsettled inside settled
        have := noGrowth other otherInside note (program.mem_ownNotes.mpr (.inl noteMember))
        rw [reason] at this; cases this
      · rfl
    · have := noGrowth member inside other (program.mem_ownNotes.mpr (.inr (.inl otherMember)))
      rw [hypothesis] at this; cases this

/-! ## Profiles -/

end Program

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem profile_p1 {found : Class Variable Literal Symbol} :
    found.profile = .p1 ↔ found.blockers = [] ∧ found.notes = [] := by
  unfold Class.profile
  split <;> simp_all

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem profile_p2 {found : Class Variable Literal Symbol} {notes : List (Note Variable Literal Symbol)} :
    found.profile = .p2 notes ↔ found.blockers = [] ∧ found.notes = notes ∧ notes ≠ [] := by
  unfold Class.profile
  split
  · simp_all
  · rename_i blockers foundNotes noBlockers someNotes
    simp only [Profile.p2.injEq, noBlockers, true_and]
    constructor
    · rintro rfl; exact ⟨rfl, by cases foundNotes <;> simp_all⟩
    · rintro ⟨rfl, _⟩; rfl
  · simp_all

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem profile_undecided {found : Class Variable Literal Symbol} {blockers : List (Blocker Variable Literal Symbol)} :
    found.profile = .undecided blockers ↔ found.blockers = blockers ∧ blockers ≠ [] := by
  unfold Class.profile
  split
  · simp_all
  · simp_all
  · rename_i foundBlockers _ someBlockers
    simp only [Profile.undecided.injEq]
    constructor
    · rintro rfl; exact ⟨rfl, by cases foundBlockers <;> simp_all⟩
    · rintro ⟨rfl, _⟩; rfl

namespace Program

variable (program : Program Variable Literal Symbol)

/-- **P1 is complete.** A P1 predicate has no blocker and no note, so no
growth note: it is complete, and its run ends without fuel. -/
theorem p1_complete {predicate : Symbol} (p1 : (program.classOf predicate).profile = .p1) :
    program.complete predicate = true := by
  obtain ⟨_, noNotes⟩ := profile_p1.mp p1
  apply program.complete_iff_growth.mpr
  intro member inside note noteMember
  have : note ∈ program.notes predicate := by
    simp only [notes, notesOf, List.mem_append, List.mem_flatMap]
    exact .inl ⟨member, inside, noteMember⟩
  simp only [classOf] at noNotes
  rw [noNotes] at this
  cases this

/-- A P1 predicate's closure has no NAF over a predicate on a cycle, no
denial over one, no generic universal goal, and no undecided hypothesis: it
has no note at all. -/
theorem p1_notes {predicate : Symbol} (p1 : (program.classOf predicate).profile = .p1) :
    program.notes predicate = [] :=
  (profile_p1.mp p1).2

/-! ## Locality -/

/-- **Locality of blockers.** A predicate's blockers are its own clauses',
the shared ones (the global ones and every denial's), and its callees'. -/
theorem mem_blockers {predicate : Symbol} {found : Blocker Variable Literal Symbol} :
    found ∈ program.blockers predicate ↔
      found ∈ program.ownBlockers predicate ∨ found ∈ program.sharedBlockers ∨
        ∃ callee, (predicate, callee) ∈ program.edges ∧ found ∈ program.blockers callee := by
  simp only [blockers, blockersOf, List.mem_append, List.mem_flatMap]
  constructor
  · rintro (⟨member, inside, own⟩ | shared)
    · rcases program.closure_step.mp inside with rfl | ⟨callee, edge, deeper⟩
      · exact .inl own
      · exact .inr (.inr ⟨callee, edge, .inl ⟨member, deeper, own⟩⟩)
    · exact .inr (.inl shared)
  · rintro (own | shared | ⟨callee, edge, ⟨member, inside, own⟩ | shared⟩)
    · exact .inl ⟨predicate, program.mem_closure_self predicate, own⟩
    · exact .inr shared
    · exact .inl ⟨member, program.closure_trans
        (program.closure_step.mpr (.inr ⟨callee, edge, program.mem_closure_self callee⟩)) inside, own⟩
    · exact .inr shared

/-- **Locality of notes.** A predicate's notes are its own clauses', those of
the denials over it, and its callees'. -/
theorem mem_notes {predicate : Symbol} {found : Note Variable Literal Symbol} :
    found ∈ program.notes predicate ↔
      found ∈ program.ownNotes predicate ∨
        (∃ denial ∈ program.denials, predicate ∈ program.denialScope denial.2 ∧ found ∈ program.denialNotes denial.1 denial.2) ∨
        ∃ callee, (predicate, callee) ∈ program.edges ∧ found ∈ program.notes callee := by
  simp only [notes, notesOf, denialsOver, List.mem_append, List.mem_flatMap, List.mem_filter, List.any_eq_true,
    List.contains_eq_mem, decide_eq_true_eq]
  constructor
  · rintro (⟨member, inside, own⟩ | ⟨denial, ⟨denialMember, meets, meetsScope, meetsClosure⟩, denialFound⟩)
    · rcases program.closure_step.mp inside with rfl | ⟨callee, edge, deeper⟩
      · exact .inl own
      · exact .inr (.inr ⟨callee, edge, .inl ⟨member, deeper, own⟩⟩)
    · rcases program.closure_step.mp meetsClosure with rfl | ⟨callee, edge, deeper⟩
      · exact .inr (.inl ⟨denial, denialMember, meetsScope, denialFound⟩)
      · exact .inr (.inr ⟨callee, edge, .inr ⟨denial, ⟨denialMember, meets, meetsScope, deeper⟩, denialFound⟩⟩)
  · rintro (own | ⟨denial, denialMember, meets, denialFound⟩ | ⟨callee, edge, calleeFound⟩)
    · exact .inl ⟨predicate, program.mem_closure_self predicate, own⟩
    · exact .inr ⟨denial, ⟨denialMember, predicate, meets, program.mem_closure_self predicate⟩, denialFound⟩
    · have calleeInside : callee ∈ program.closure predicate :=
        program.closure_step.mpr (.inr ⟨callee, edge, program.mem_closure_self callee⟩)
      rcases calleeFound with ⟨member, inside, own⟩ | ⟨denial, ⟨denialMember, meets, meetsScope, meetsClosure⟩, denialFound⟩
      · exact .inl ⟨member, program.closure_trans calleeInside inside, own⟩
      · exact .inr ⟨denial, ⟨denialMember, meets, meetsScope, program.closure_trans calleeInside meetsClosure⟩, denialFound⟩

theorem foldr_max_le {α : Type} (measure : α → Nat) (bound : Nat) :
    ∀ items : List α, items.foldr (fun item best => max (measure item) best) 0 ≤ bound ↔ ∀ item ∈ items, measure item ≤ bound
  | [] => by simp
  | item :: rest => by
      simp only [List.foldr_cons, Nat.max_le, List.mem_cons, forall_eq_or_imp]
      rw [foldr_max_le measure bound rest]

omit [DecidableEq Literal] in
/-- **Locality of the degree.** The degree is the widest clause of the
dependency closure: at most a bound exactly when the predicate's own clauses
and its callees' degrees are. -/
theorem degree_le {predicate : Symbol} {bound : Nat} :
    program.degree predicate ≤ bound ↔
      program.width predicate ≤ bound ∧ ∀ callee, (predicate, callee) ∈ program.edges → program.degree callee ≤ bound := by
  simp only [degree, foldr_max_le]
  constructor
  · intro every
    refine ⟨every predicate (program.mem_closure_self predicate), fun callee edge member inside => ?_⟩
    exact every member (program.closure_step.mpr (.inr ⟨callee, edge, inside⟩))
  · rintro ⟨own, callees⟩ member inside
    rcases program.closure_step.mp inside with rfl | ⟨callee, edge, deeper⟩
    · exact own
    · exact callees callee edge member deeper

/-- **A query's profile follows the predicates it uses.** Its blockers are
its own, the shared ones, and those of the predicates it uses. -/
theorem mem_queryBlockers {query : Query Variable Literal Symbol} {found : Blocker Variable Literal Symbol} :
    found ∈ (program.queryClass query).blockers ↔
      found ∈ (program.queryFound query).blockers ∨
        found ∈ program.negationBlockers (program.queryFound query).negations ∨ found ∈ program.sharedBlockers ∨
          ∃ used ∈ program.used query, found ∈ program.blockers used := by
  simp only [queryClass, blockers, blockersOf, List.mem_append, List.mem_flatMap, List.mem_eraseDups]
  constructor
  · rintro ((own | negation) | (⟨member, ⟨used, usedMember, inside⟩, memberFound⟩ | shared))
    · exact .inl own
    · exact .inr (.inl negation)
    · exact .inr (.inr (.inr ⟨used, usedMember, .inl ⟨member, inside, memberFound⟩⟩))
    · exact .inr (.inr (.inl shared))
  · rintro (own | negation | shared | ⟨used, usedMember, ⟨member, inside, memberFound⟩ | shared⟩)
    · exact .inl (.inl own)
    · exact .inl (.inr negation)
    · exact .inr (.inr shared)
    · exact .inr (.inl ⟨member, ⟨used, usedMember, inside⟩, memberFound⟩)
    · exact .inr (.inr shared)

/-- An admission that is not Undecided has no blocker; S22's Undecided
answer comes before anything runs, with exactly the query's blockers. -/
theorem answer?_undecided {Proof Refutation Witness : Type} {query : Query Variable Literal Symbol}
    {blockers : List (Blocker Variable Literal Symbol)} :
    program.answer? (Proof := Proof) (Refutation := Refutation) (Witness := Witness) query = some (.undecided blockers) ↔
      program.admit query = .undecided blockers := by
  unfold answer?
  split <;> simp_all

end Program

/-! ## Determinism -/

omit [DecidableEq Variable] in
mutual
/-- Terms `mayMatch` separates have no common value: a literal or declared
constructor clash. -/
theorem mayMatch_sound (free : Symbol → Nat → Bool) {first second : Env Variable Literal Symbol} :
    ∀ {left right value : Term Variable Literal Symbol}, Completion.mayMatch free left right = false →
      inst first left = some value → inst second right = some value → False
  | .var _, _, _, clash, _, _ => by simp [Completion.mayMatch] at clash
  | .lit _, .var _, _, clash, _, _ | .app _ _, .var _, _, clash, _, _ => by simp [Completion.mayMatch] at clash
  | .lit a, .lit b, value, clash, leftInst, rightInst => by
      simp only [inst, Option.some.injEq] at leftInst rightInst
      subst leftInst
      cases rightInst
      simp [Completion.mayMatch] at clash
  | .lit _, .app symbol args, value, clash, leftInst, rightInst => by
      simp only [inst, Option.some.injEq] at leftInst
      subst leftInst
      simp only [inst] at rightInst
      cases instAll second args <;> simp at rightInst
  | .app symbol args, .lit _, value, clash, leftInst, rightInst => by
      simp only [inst, Option.some.injEq] at rightInst
      subst rightInst
      simp only [inst] at leftInst
      cases instAll first args <;> simp at leftInst
  | .app symbol args, .app other otherArgs, value, clash, leftInst, rightInst => by
      simp only [inst] at leftInst rightInst
      cases leftValues : instAll first args with
      | none => rw [leftValues] at leftInst; cases leftInst
      | some values =>
          cases rightValues : instAll second otherArgs with
          | none => rw [rightValues] at rightInst; cases rightInst
          | some otherValues =>
              rw [leftValues] at leftInst
              rw [rightValues] at rightInst
              simp only [Option.map_some, Option.some.injEq] at leftInst rightInst
              subst leftInst
              simp only [Term.app.injEq] at rightInst
              obtain ⟨sameSymbol, sameValues⟩ := rightInst
              subst sameSymbol
              subst sameValues
              simp only [Completion.mayMatch, beq_self_eq_true, Bool.true_and] at clash
              split at clash
              · exact mayMatchAll_sound free clash leftValues rightValues
              · cases clash
  | .lit _, .truth, _, _, _, rightInst | .app _ _, .truth, _, _, _, rightInst => by simp [inst] at rightInst
  | .lit _, .falsity, _, _, _, rightInst | .app _ _, .falsity, _, _, _, rightInst => by simp [inst] at rightInst
  | .lit _, .conj _ _, _, _, _, rightInst | .app _ _, .conj _ _, _, _, _, rightInst => by simp [inst] at rightInst
  | .lit _, .disj _ _, _, _, _, rightInst | .app _ _, .disj _ _, _, _, _, rightInst => by simp [inst] at rightInst
  | .lit _, .imp _ _, _, _, _, rightInst | .app _ _, .imp _ _, _, _, _, rightInst => by simp [inst] at rightInst
  | .lit _, .defaultNeg _, _, _, _, rightInst | .app _ _, .defaultNeg _, _, _, _, rightInst => by simp [inst] at rightInst
  | .lit _, .forallVar _ _, _, _, _, rightInst | .app _ _, .forallVar _ _, _, _, _, rightInst => by simp [inst] at rightInst
  | .lit _, .existsVar _ _, _, _, _, rightInst | .app _ _, .existsVar _ _, _, _, _, rightInst => by simp [inst] at rightInst
  | .lit _, .dictionaryCall _ _ _ _, _, _, _, rightInst | .app _ _, .dictionaryCall _ _ _ _, _, _, _, rightInst => by simp [inst] at rightInst
  | .lit _, .equal _ _, _, _, _, rightInst | .app _ _, .equal _ _, _, _, _, rightInst => by simp [inst] at rightInst
  | .truth, _, _, _, leftInst, _ => by simp [inst] at leftInst
  | .falsity, _, _, _, leftInst, _ => by simp [inst] at leftInst
  | .conj _ _, _, _, _, leftInst, _ => by simp [inst] at leftInst
  | .disj _ _, _, _, _, leftInst, _ => by simp [inst] at leftInst
  | .imp _ _, _, _, _, leftInst, _ => by simp [inst] at leftInst
  | .defaultNeg _, _, _, _, leftInst, _ => by simp [inst] at leftInst
  | .forallVar _ _, _, _, _, leftInst, _ => by simp [inst] at leftInst
  | .existsVar _ _, _, _, _, leftInst, _ => by simp [inst] at leftInst
  | .dictionaryCall _ _ _ _, _, _, _, leftInst, _ => by simp [inst] at leftInst
  | .equal _ _, _, _, _, leftInst, _ => by simp [inst] at leftInst

theorem mayMatchAll_sound (free : Symbol → Nat → Bool) {first second : Env Variable Literal Symbol} :
    ∀ {left right values : List (Term Variable Literal Symbol)}, Completion.mayMatchAll free left right = false →
      instAll first left = some values → instAll second right = some values → False
  | [], [], _, clash, _, _ => by simp [Completion.mayMatchAll] at clash
  | [], _ :: _, values, _, leftInst, rightInst => by
      simp only [instAll, Option.some.injEq] at leftInst
      subst leftInst
      simp only [instAll] at rightInst
      split at rightInst <;> simp at rightInst
  | _ :: _, [], values, _, leftInst, rightInst => by
      simp only [instAll, Option.some.injEq] at rightInst
      subst rightInst
      simp only [instAll] at leftInst
      split at leftInst <;> simp at leftInst
  | term :: rest, other :: otherRest, values, clash, leftInst, rightInst => by
      simp only [instAll] at leftInst rightInst
      cases termInst : inst first term with
      | none => rw [termInst] at leftInst; cases leftInst
      | some value =>
          cases restInst : instAll first rest with
          | none => rw [termInst, restInst] at leftInst; cases leftInst
          | some more =>
              cases otherInst : inst second other with
              | none => rw [otherInst] at rightInst; cases rightInst
              | some otherValue =>
                  cases otherRestInst : instAll second otherRest with
                  | none => rw [otherInst, otherRestInst] at rightInst; cases rightInst
                  | some otherMore =>
                      rw [termInst, restInst] at leftInst
                      rw [otherInst, otherRestInst] at rightInst
                      cases leftInst
                      simp only [Option.some.injEq, List.cons.injEq] at rightInst
                      obtain ⟨rfl, rfl⟩ := rightInst
                      simp only [Completion.mayMatchAll, Bool.and_eq_false_iff] at clash
                      rcases clash with headClash | restClash
                      · exact mayMatch_sound free headClash termInst otherInst
                      · exact mayMatchAll_sound free restClash restInst otherRestInst
end

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem instAll_zip {first second : Env Variable Literal Symbol} :
    ∀ {left right values : List (Term Variable Literal Symbol)}, instAll first left = some values →
      instAll second right = some values → ∀ pair ∈ left.zip right,
        ∃ value, inst first pair.1 = some value ∧ inst second pair.2 = some value
  | [], _, _, _, _, _, member => by simp at member
  | _ :: _, [], _, _, _, _, member => by simp at member
  | term :: rest, other :: otherRest, values, leftInst, rightInst, pair, member => by
      simp only [instAll] at leftInst rightInst
      cases termInst : inst first term with
      | none => rw [termInst] at leftInst; cases leftInst
      | some value =>
          cases restInst : instAll first rest with
          | none => rw [termInst, restInst] at leftInst; cases leftInst
          | some more =>
              cases otherInst : inst second other with
              | none => rw [otherInst] at rightInst; cases rightInst
              | some otherValue =>
                  cases otherRestInst : instAll second otherRest with
                  | none => rw [otherInst, otherRestInst] at rightInst; cases rightInst
                  | some otherMore =>
                      rw [termInst, restInst] at leftInst
                      rw [otherInst, otherRestInst] at rightInst
                      cases leftInst
                      simp only [Option.some.injEq, List.cons.injEq] at rightInst
                      obtain ⟨rfl, rfl⟩ := rightInst
                      simp only [List.zip_cons_cons, List.mem_cons] at member
                      rcases member with rfl | inside
                      · exact ⟨_, termInst, otherInst⟩
                      · exact instAll_zip restInst otherRestInst pair inside

namespace Program

variable (program : Program Variable Literal Symbol)

omit [DecidableEq Variable] in
/-- **Determinism.** No input values match the input patterns of two
defining clauses of a deterministic predicate: at most one clause applies to
each call, so the run has no choice point there. -/
theorem deterministic_unique {predicate : Symbol} (deterministic : program.deterministic predicate = true)
    {first second : Nat × List (Term Variable Literal Symbol) × List (Term Variable Literal Symbol)}
    (pair : (first, second) ∈ pairs (program.definitions predicate))
    {firstInputs firstOutputs secondInputs secondOutputs : List (Term Variable Literal Symbol)}
    (firstIo : program.io? predicate first.2.1 = some (firstInputs, firstOutputs))
    (secondIo : program.io? predicate second.2.1 = some (secondInputs, secondOutputs))
    {env env' : Env Variable Literal Symbol} {values : List (Term Variable Literal Symbol)}
    (firstMatch : instAll env firstInputs = some values) (secondMatch : instAll env' secondInputs = some values) : False := by
  have apart := List.all_eq_true.mp deterministic (first, second) pair
  simp only [Program.apart, firstIo, secondIo, List.any_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at apart
  obtain ⟨terms, termsMember, clash⟩ := apart
  obtain ⟨value, leftInst, rightInst⟩ := instAll_zip firstMatch secondMatch terms termsMember
  exact mayMatch_sound program.free clash leftInst rightInst

end Program

end AnthillModKbSpec.Tabled
