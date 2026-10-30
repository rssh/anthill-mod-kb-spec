import AnthillModKbSpec.Resolution.P0.GroundSearch

namespace AnthillModKbSpec.GroundSearch

/-! # Dependency ranks of ground programs (S07)

P0 admits a finite ground program whose whole dependency graph is acyclic. An
edge goes from a clause head to every atomic goal of its body, including atoms
under any number of NAF constructors; data arguments are not goals. A rank is a
natural number per atom that every edge decreases. Under a rank every ground
goal has a success or a complete-failure certificate (`decided`), by induction
on the goal's level: an atom's level is its rank plus one, and a compound goal's
level is the largest level of its atoms. -/

variable {Variable Literal Symbol : Type} {hoApplySymbol : Symbol}

/-- The atomic goal occurrences of a goal, including those under NAF. -/
def atoms : Term Variable Literal Symbol → List (Term Variable Literal Symbol)
  | .app symbol args => [.app symbol args]
  | .conj left right => atoms left ++ atoms right
  | .defaultNeg body => atoms body
  | _ => []

/-- Every dependency edge of a clause list: each head to each atom of its body. -/
def edges (clauses : List (HornClause Variable Literal Symbol)) :
    List (Term Variable Literal Symbol × Term Variable Literal Symbol) :=
  clauses.flatMap fun
    | .definite head body => (atoms (.conjunction body)).map (head, ·)
    | .goal _ => []

/-- A rank witness for a clause list: every dependency edge decreases it. -/
def Ranked (rank : Term Variable Literal Symbol → Nat) (clauses : List (HornClause Variable Literal Symbol)) : Prop :=
  ∀ head body, HornClause.definite head body ∈ clauses → ∀ atom ∈ atoms (.conjunction body), rank atom < rank head

theorem mem_edges {clauses : List (HornClause Variable Literal Symbol)} {head atom : Term Variable Literal Symbol} :
    (head, atom) ∈ edges clauses ↔ ∃ body, HornClause.definite head body ∈ clauses ∧ atom ∈ atoms (.conjunction body) := by
  simp only [edges, List.mem_flatMap]
  constructor
  · rintro ⟨clause, member, inside⟩
    cases clause with
    | definite clauseHead body =>
        obtain ⟨found, foundMember, same⟩ := List.mem_map.mp inside
        cases same
        exact ⟨body, member, foundMember⟩
    | goal body => cases inside
  · rintro ⟨body, member, inside⟩
    exact ⟨.definite head body, member, List.mem_map.mpr ⟨atom, inside, rfl⟩⟩

/-- A rank is a witness exactly when it decreases along every edge. -/
theorem ranked_iff_edges {rank : Term Variable Literal Symbol → Nat} {clauses : List (HornClause Variable Literal Symbol)} :
    Ranked rank clauses ↔ ∀ edge ∈ edges clauses, rank edge.2 < rank edge.1 := by
  constructor
  · rintro ranked ⟨head, atom⟩ member
    obtain ⟨body, clause, inside⟩ := mem_edges.mp member
    exact ranked head body clause atom inside
  · intro decreasing head body clause atom inside
    exact decreasing (head, atom) (mem_edges.mpr ⟨body, clause, inside⟩)

/-- The level of a goal: one more than the largest rank of its atoms, or zero. -/
def level (rank : Term Variable Literal Symbol → Nat) (goal : Term Variable Literal Symbol) : Nat :=
  (atoms goal).foldr (fun atom bound => max (rank atom + 1) bound) 0

theorem level_le {rank : Term Variable Literal Symbol → Nat} {goal : Term Variable Literal Symbol} {bound : Nat} :
    level rank goal ≤ bound ↔ ∀ atom ∈ atoms goal, rank atom + 1 ≤ bound := by
  unfold level
  induction atoms goal with
  | nil => simp
  | cons atom rest ih => rw [List.foldr_cons, Nat.max_le, ih]; simp

@[simp] theorem level_app (rank : Term Variable Literal Symbol → Nat) (symbol : Symbol)
    (args : List (Term Variable Literal Symbol)) : level rank (.app symbol args) = rank (.app symbol args) + 1 := by
  simp [level, atoms]

@[simp] theorem level_conj (rank : Term Variable Literal Symbol → Nat) (left right : Term Variable Literal Symbol) :
    level rank (.conj left right) = max (level rank left) (level rank right) := by
  unfold level
  simp only [atoms, List.foldr_append]
  generalize atoms right = rest
  induction atoms left with
  | nil => simp
  | cons atom more ih => simp only [List.foldr_cons, ih]; omega

@[simp] theorem level_defaultNeg (rank : Term Variable Literal Symbol → Nat) (body : Term Variable Literal Symbol) :
    level rank (.defaultNeg body) = level rank body := rfl

/-- A clause body is below its head. -/
theorem Ranked.level_body {rank : Term Variable Literal Symbol → Nat} {clauses : List (HornClause Variable Literal Symbol)}
    (ranked : Ranked rank clauses) {head : Term Variable Literal Symbol} {body : List (Term Variable Literal Symbol)}
    (member : HornClause.definite head body ∈ clauses) : level rank (.conjunction body) ≤ rank head :=
  level_le.mpr fun atom inside => ranked head body member atom inside

variable {program : Program Variable Literal Symbol hoApplySymbol} {context : Context Variable Literal Symbol hoApplySymbol}

/-- Totality of the certificates under a rank: every ground goal has a success
or a complete-failure certificate. This is a statement about the judgments
for a ranked program; the machine's evaluation and its termination are
separate (`P0.run_correct`, `P0.run_total`). -/
theorem decided {rank : Term Variable Literal Symbol → Nat} (ranked : Ranked rank program.clauses) :
    ∀ goal, IsGoal hoApplySymbol goal → Succeeds program context goal ∨ Fails program context goal := by
  suffices bounded : ∀ bound goal, level rank goal ≤ bound → IsGoal hoApplySymbol goal →
      Succeeds program context goal ∨ Fails program context goal from
    fun goal valid => bounded _ goal (Nat.le_refl _) valid
  intro bound
  induction bound with
  | zero =>
      intro goal below valid
      induction valid with
      | atom ground =>
          cases ground with
          | app => simp at below
      | truth => exact .inl .truth
      | falsity => exact .inr .falsity
      | conj left right ihLeft ihRight =>
          simp only [level_conj, Nat.max_le] at below
          rcases ihLeft below.1 with leftOk | leftFails
          · rcases ihRight below.2 with rightOk | rightFails
            · exact .inl (.conj leftOk rightOk)
            · exact .inr (.conjRight left rightFails)
          · exact .inr (.conjLeft leftFails right)
      | defaultNeg body ih =>
          rcases ih below with ok | failed
          · exact .inr (.defaultNeg ok)
          · exact .inl (.defaultNeg failed)
  | succ bound outer =>
      intro goal below valid
      induction valid with
      | @atom atom ground =>
          cases ground with
          | app ordinary dataArgs =>
              rename_i symbol args
              have atomGround : IsAtom hoApplySymbol (.app symbol args) := .app ordinary dataArgs
              rw [level_app] at below
              have bodies : ∀ body, HornClause.definite (.app symbol args) body ∈ program.clauses →
                  Succeeds program context (.conjunction body) ∨ Fails program context (.conjunction body) := by
                intro body member
                have bodyValid : IsGoal hoApplySymbol (.conjunction body) := by
                  cases program.wellFormed _ member with
                  | definite _ goals => exact conjunction_isGoal goals
                exact outer _ (Nat.le_trans (ranked.level_body member) (Nat.le_of_succ_le_succ below)) bodyValid
              by_cases present : Term.app symbol args ∈ context.assumptions
              · exact .inl (.assumption atomGround present)
              · by_cases some : ∃ body, HornClause.definite (.app symbol args) body ∈ program.clauses ∧
                    Succeeds program context (.conjunction body)
                · obtain ⟨body, member, proof⟩ := some
                  exact .inl (.clause atomGround member proof)
                · refine .inr (.atom atomGround present fun body member => ?_)
                  exact (bodies body member).resolve_left fun proof => some ⟨body, member, proof⟩
      | truth => exact .inl .truth
      | falsity => exact .inr .falsity
      | conj left right ihLeft ihRight =>
          simp only [level_conj, Nat.max_le] at below
          rcases ihLeft below.1 with leftOk | leftFails
          · rcases ihRight below.2 with rightOk | rightFails
            · exact .inl (.conj leftOk rightOk)
            · exact .inr (.conjRight left rightFails)
          · exact .inr (.conjLeft leftFails right)
      | defaultNeg body ih =>
          rcases ih below with ok | failed
          · exact .inr (.defaultNeg ok)
          · exact .inl (.defaultNeg failed)

/-- Under a rank, a ground goal without a success certificate has a
complete-failure certificate. -/
theorem fails_of_not_succeeds {rank : Term Variable Literal Symbol → Nat} (ranked : Ranked rank program.clauses)
    {goal : Term Variable Literal Symbol} (valid : IsGoal hoApplySymbol goal)
    (missing : ¬ Succeeds program context goal) : Fails program context goal :=
  (decided ranked goal valid).resolve_left missing

/-! ## Constructing a rank

Kahn's peeling: round by round, rank every remaining vertex whose successors
are all ranked, with the round number. If some rank witness exists, every
round ranks at least one remaining vertex (one of least witness rank), so all
vertices are ranked within as many rounds as there are vertices, and the
computed rank decreases along every edge (`topoRank_decreases`). The checker
verifies the computed rank anyway; this theorem is what makes it complete. -/

section Peeling

variable {α : Type} [DecidableEq α]

/-- The rank a ranking assigns: its first entry for the vertex, or zero. -/
def rankOf (ranked : List (α × Nat)) (vertex : α) : Nat :=
  match ranked.find? (·.1 == vertex) with
  | some entry => entry.2
  | none => 0

/-- Peel rounds of vertices whose successors are all ranked. -/
def peel (edges : List (α × α)) : Nat → Nat → List α → List (α × Nat) → List (α × Nat) × List α
  | 0, _, remaining, ranked => (ranked, remaining)
  | fuel + 1, round, remaining, ranked =>
      let keys := ranked.map Prod.fst
      let ready := remaining.filter fun vertex =>
        edges.all fun edge => edge.1 != vertex || keys.contains edge.2
      if ready.isEmpty then (ranked, remaining)
      else peel edges fuel (round + 1) (remaining.filter fun vertex => !ready.contains vertex)
        (ranked ++ ready.map (·, round))

/-- A topological rank of a finite graph, when it has one. -/
def topoRank (edges : List (α × α)) (vertices : List α) : List (α × Nat) :=
  (peel edges vertices.length 0 vertices []).1

/-- What holds between peeling rounds. -/
structure PeelInv (edges : List (α × α)) (vertices : List α) (round : Nat) (remaining : List α)
    (ranked : List (α × Nat)) : Prop where
  below : ∀ entry ∈ ranked, entry.2 < round
  disjoint : ∀ entry ∈ ranked, entry.1 ∉ remaining
  covered : ∀ vertex ∈ vertices, vertex ∈ remaining ∨ vertex ∈ ranked.map Prod.fst
  consistent : ∀ entry ∈ ranked, ∀ other ∈ ranked, entry.1 = other.1 → entry.2 = other.2
  closed : ∀ entry ∈ ranked, ∀ edge ∈ edges, edge.1 = entry.1 → ∃ other ∈ ranked, other.1 = edge.2 ∧ other.2 < entry.2

theorem rankOf_eq {ranked : List (α × Nat)} {entry : α × Nat} (member : entry ∈ ranked)
    (consistent : ∀ first ∈ ranked, ∀ other ∈ ranked, first.1 = other.1 → first.2 = other.2) :
    rankOf ranked entry.1 = entry.2 := by
  unfold rankOf
  split
  · rename_i found foundEq
    have inside := List.mem_of_find?_eq_some foundEq
    have same := List.find?_some foundEq
    simp only [beq_iff_eq] at same
    exact consistent found inside entry member same
  · rename_i none
    have := List.find?_eq_none.mp none entry member
    simp at this

omit [DecidableEq α] in
private theorem filter_length_lt {items : List α} {keep : α → Bool} {item : α} (member : item ∈ items)
    (dropped : keep item = false) : (items.filter keep).length < items.length := by
  induction items with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | inside
      · simp only [List.filter_cons, dropped, Bool.false_eq_true, ↓reduceIte, List.length_cons]
        exact Nat.lt_succ_of_le (List.length_filter_le _ _)
      · simp only [List.filter_cons, List.length_cons]
        split
        · simp only [List.length_cons]; exact Nat.succ_lt_succ (ih inside)
        · exact Nat.lt_succ_of_lt (ih inside)

omit [DecidableEq α] in
private theorem exists_least (rank : α → Nat) : ∀ {items : List α}, items ≠ [] →
    ∃ item ∈ items, ∀ other ∈ items, rank item ≤ rank other
  | [], empty => absurd rfl empty
  | [item], _ => ⟨item, List.mem_singleton_self _, fun other member => by
      rw [List.mem_singleton.mp member]; exact Nat.le_refl _⟩
  | item :: next :: rest, _ => by
      obtain ⟨least, member, smallest⟩ := exists_least rank (items := next :: rest) (by simp)
      by_cases smaller : rank item ≤ rank least
      · exact ⟨item, List.mem_cons_self, fun other inside => by
          rcases List.mem_cons.mp inside with rfl | inside
          · exact Nat.le_refl _
          · exact Nat.le_trans smaller (smallest other inside)⟩
      · exact ⟨least, List.mem_cons_of_mem _ member, fun other inside => by
          rcases List.mem_cons.mp inside with rfl | inside
          · omega
          · exact smallest other inside⟩

/-- Under a rank witness, peeling ranks every vertex and keeps its invariant. -/
theorem peel_spec {edges : List (α × α)} {vertices : List α} {witness : α → Nat}
    (decreasing : ∀ edge ∈ edges, witness edge.2 < witness edge.1)
    (endpoints : ∀ edge ∈ edges, edge.2 ∈ vertices) :
    ∀ (fuel round : Nat) (remaining : List α) (ranked : List (α × Nat)), remaining.length ≤ fuel →
      PeelInv edges vertices round remaining ranked →
        (∃ round', PeelInv edges vertices round' (peel edges fuel round remaining ranked).2
          (peel edges fuel round remaining ranked).1) ∧ (peel edges fuel round remaining ranked).2 = []
  | 0, round, remaining, ranked, small, inv => by
      have empty : remaining = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp small)
      exact ⟨⟨round, by simpa [peel] using inv⟩, by simp [peel, empty]⟩
  | fuel + 1, round, remaining, ranked, small, inv => by
      by_cases empty : remaining = []
      · subst empty
        exact ⟨⟨round, by simpa [peel] using inv⟩, by simp [peel]⟩
      obtain ⟨least, leastMember, smallest⟩ := exists_least witness empty
      let ready := remaining.filter fun vertex =>
        edges.all fun edge => edge.1 != vertex || (ranked.map Prod.fst).contains edge.2
      have leastReady : least ∈ ready := by
        refine List.mem_filter.mpr ⟨leastMember, List.all_eq_true.mpr fun edge member => ?_⟩
        by_cases from_least : edge.1 = least
        · have lower := decreasing edge member
          rw [from_least] at lower
          rcases inv.covered edge.2 (endpoints edge member) with stillThere | rankedThere
          · exact absurd (smallest _ stillThere) (by omega)
          · simp [rankedThere]
        · simp [from_least]
      have notEmpty : ready.isEmpty = false := by
        cases readyEq : ready with
        | nil => rw [readyEq] at leastReady; cases leastReady
        | cons _ _ => rfl
      have step : peel edges (fuel + 1) round remaining ranked =
          peel edges fuel (round + 1) (remaining.filter fun vertex => !ready.contains vertex)
            (ranked ++ ready.map (·, round)) := by
        simp only [ready] at notEmpty
        simp only [peel, notEmpty, Bool.false_eq_true, ↓reduceIte]
        rfl
      rw [step]
      apply peel_spec decreasing endpoints
      · have shorter := filter_length_lt (keep := fun vertex => !ready.contains vertex) leastMember
          (by simp [leastReady])
        omega
      · have readyRemaining : ∀ vertex ∈ ready, vertex ∈ remaining := fun vertex member =>
          (List.mem_filter.mp member).1
        refine ⟨fun entry member => ?_, fun entry member => ?_, fun vertex member => ?_,
          fun entry member other inside same => ?_, fun entry member edge inside same => ?_⟩
        · rcases List.mem_append.mp member with old | new
          · exact Nat.lt_succ_of_lt (inv.below entry old)
          · obtain ⟨vertex, _, rfl⟩ := List.mem_map.mp new
            exact Nat.lt_succ_self _
        · rcases List.mem_append.mp member with old | new
          · exact fun there => inv.disjoint entry old (List.mem_filter.mp there).1
          · obtain ⟨vertex, readyMember, rfl⟩ := List.mem_map.mp new
            intro there
            have := (List.mem_filter.mp there).2
            simp [readyMember] at this
        · rcases inv.covered vertex member with stillThere | rankedThere
          · by_cases isReady : vertex ∈ ready
            · exact .inr (by simp [List.mem_map]; exact .inr isReady)
            · exact .inl (List.mem_filter.mpr ⟨stillThere, by simp [isReady]⟩)
          · exact .inr (by simp only [List.map_append, List.mem_append]; exact .inl rankedThere)
        · rcases List.mem_append.mp member with old | new <;> rcases List.mem_append.mp inside with old' | new'
          · exact inv.consistent entry old other old' same
          · obtain ⟨vertex, readyMember, rfl⟩ := List.mem_map.mp new'
            exact (inv.disjoint entry old (by rw [same]; exact readyRemaining vertex readyMember)).elim
          · obtain ⟨vertex, readyMember, rfl⟩ := List.mem_map.mp new
            exact (inv.disjoint other old' (by rw [← same]; exact readyRemaining vertex readyMember)).elim
          · obtain ⟨vertex, _, rfl⟩ := List.mem_map.mp new
            obtain ⟨vertex', _, rfl⟩ := List.mem_map.mp new'
            rfl
        · rcases List.mem_append.mp member with old | new
          · obtain ⟨found, foundMember, foundKey, foundBelow⟩ := inv.closed entry old edge inside same
            exact ⟨found, List.mem_append_left _ foundMember, foundKey, foundBelow⟩
          · obtain ⟨vertex, readyMember, rfl⟩ := List.mem_map.mp new
            have allReady := (List.mem_filter.mp readyMember).2
            have edgeOk := List.all_eq_true.mp allReady edge inside
            simp only [same, bne_self_eq_false, Bool.false_or, List.contains_iff_mem] at edgeOk
            obtain ⟨found, foundMember, foundKey⟩ := List.mem_map.mp edgeOk
            exact ⟨found, List.mem_append_left _ foundMember, foundKey, inv.below found foundMember⟩

/-- If any rank witness exists, the computed rank decreases along every edge. -/
theorem topoRank_decreases {edges : List (α × α)} {vertices : List α}
    (acyclic : ∃ witness : α → Nat, ∀ edge ∈ edges, witness edge.2 < witness edge.1)
    (endpoints : ∀ edge ∈ edges, edge.1 ∈ vertices ∧ edge.2 ∈ vertices) :
    ∀ edge ∈ edges, rankOf (topoRank edges vertices) edge.2 < rankOf (topoRank edges vertices) edge.1 := by
  obtain ⟨witness, decreasing⟩ := acyclic
  have initial : PeelInv edges vertices 0 vertices [] :=
    ⟨by simp, by simp, fun vertex member => .inl member, by simp, by simp⟩
  obtain ⟨⟨_, inv⟩, done⟩ := peel_spec decreasing (fun edge member => (endpoints edge member).2) vertices.length 0
    vertices [] (Nat.le_refl _) initial
  intro edge member
  unfold topoRank
  rcases inv.covered edge.1 (endpoints edge member).1 with stillThere | rankedThere
  · rw [done] at stillThere; cases stillThere
  · obtain ⟨entry, entryMember, entryKey⟩ := List.mem_map.mp rankedThere
    obtain ⟨other, otherMember, otherKey, lower⟩ := inv.closed entry entryMember edge member entryKey.symm
    rw [← entryKey, ← otherKey, rankOf_eq entryMember inv.consistent, rankOf_eq otherMember inv.consistent]
    exact lower

/-- The vertices reachable from `found` along at most `fuel` edges, `found`
included. It stops early once a round adds nothing. -/
def reach (edges : List (α × α)) : Nat → List α → List α
  | 0, found => found
  | fuel + 1, found =>
      let next := (found ++ edges.filterMap fun edge => if found.contains edge.1 then some edge.2 else none).eraseDups
      if next.length = found.length then found else reach edges fuel next

end Peeling

end AnthillModKbSpec.GroundSearch
