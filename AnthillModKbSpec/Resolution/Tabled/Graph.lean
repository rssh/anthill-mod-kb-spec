namespace AnthillModKbSpec.Tabled

/-! # Finite graphs: reachability and greatest post-fixpoints (S23)

The fast fragment's admission (S23) classifies predicates by their dependency
graph: which predicates a predicate reaches, which lie on a cycle, and which
belong to its strongly connected component. `reach` computes the vertices
reachable along at least one edge by saturation inside a finite universe, and
`reach_iff` proves it is the transitive closure of the edges. `greatest`
computes the greatest post-fixpoint of a monotone check by deflation
(`greatest_post`, `greatest_ge`). -/

section Graph

variable {α : Type} [DecidableEq α]

/-! ## Two facts about filters -/

section Filters

variable {β : Type}

theorem filter_length_le_of {p q : β → Bool} :
    ∀ {items : List β}, (∀ x ∈ items, p x = true → q x = true) → (items.filter p).length ≤ (items.filter q).length
  | [], _ => by simp
  | first :: rest, weaker => by
      have rest' := filter_length_le_of (p := p) (q := q) (items := rest)
        (fun y inside => weaker y (List.mem_cons_of_mem _ inside))
      have here := weaker first List.mem_cons_self
      simp only [List.filter_cons]
      cases hp : p first <;> cases hq : q first <;> simp_all <;> omega

/-- A filter that keeps as many elements as a weaker one keeps the same elements. -/
theorem filter_length_eq {p q : β → Bool} :
    ∀ {items : List β}, (∀ x ∈ items, p x = true → q x = true) →
      (items.filter p).length = (items.filter q).length → ∀ x ∈ items, q x = true → p x = true
  | [], _, _, _, member, _ => by cases member
  | first :: rest, weaker, same, x, member, holds => by
      have restWeaker : ∀ y ∈ rest, p y = true → q y = true := fun y inside => weaker y (List.mem_cons_of_mem _ inside)
      have restLe := filter_length_le_of restWeaker
      by_cases pFirst : p first = true
      · have qFirst := weaker first List.mem_cons_self pFirst
        simp only [List.filter_cons, pFirst, qFirst, ite_true, List.length_cons, Nat.add_right_cancel_iff] at same
        rcases List.mem_cons.mp member with rfl | inside
        · exact pFirst
        · exact filter_length_eq restWeaker same x inside holds
      · cases qFirst : q first
        · simp only [List.filter_cons, pFirst, qFirst, Bool.false_eq_true, ite_false] at same
          rcases List.mem_cons.mp member with rfl | inside
          · rw [qFirst] at holds; cases holds
          · exact filter_length_eq restWeaker same x inside holds
        · simp only [List.filter_cons, pFirst, qFirst, Bool.false_eq_true, ite_false, ite_true,
            List.length_cons] at same
          omega

end Filters

/-! ## Reachability by saturation -/

/-- Kept by a round: found, or a successor of a found vertex. -/
def growKeep (edges : List (α × α)) (found : List α) (vertex : α) : Bool :=
  found.contains vertex || edges.any fun edge => edge.2 == vertex && found.contains edge.1

/-- One round: the vertices of `vertices` already found, or a successor of a
found vertex. -/
def grow (edges : List (α × α)) (vertices found : List α) : List α :=
  vertices.filter (growKeep edges found)

/-- Rounds of `grow` until a round adds nothing, within `fuel` rounds. -/
def saturate (edges : List (α × α)) (vertices : List α) : Nat → List α → List α
  | 0, found => found
  | fuel + 1, found =>
      let next := grow edges vertices found
      if next.length = found.length then found else saturate edges vertices fuel next

/-- The vertices reachable from `start` along at least one edge. The universe
must hold every edge's target; one round per vertex of the universe suffices
(`reach_iff`). -/
def reach (edges : List (α × α)) (vertices : List α) (start : α) : List α :=
  saturate edges vertices (vertices.length + 1) (vertices.filter fun vertex => edges.contains (start, vertex))

/-- The edge relation of an edge list. -/
def Edge (edges : List (α × α)) (source target : α) : Prop := (source, target) ∈ edges

theorem mem_grow {edges : List (α × α)} {vertices found : List α} {vertex : α} :
    vertex ∈ grow edges vertices found ↔
      vertex ∈ vertices ∧ (vertex ∈ found ∨ ∃ edge ∈ edges, edge.2 = vertex ∧ edge.1 ∈ found) := by
  simp [grow, growKeep]

theorem grow_filter (edges : List (α × α)) (vertices found : List α) :
    ∃ keep : α → Bool, grow edges vertices found = vertices.filter keep := ⟨_, rfl⟩

/-- Every vertex `saturate` finds is found initially or reached from a found one. -/
theorem saturate_sound {edges : List (α × α)} {vertices : List α} {Good : α → Prop}
    (step : ∀ edge ∈ edges, Good edge.1 → Good edge.2) :
    ∀ (fuel : Nat) (found : List α), (∀ vertex ∈ found, Good vertex) →
      ∀ vertex ∈ saturate edges vertices fuel found, Good vertex
  | 0, _, good => good
  | fuel + 1, found, good => by
      simp only [saturate]
      split
      · exact good
      · apply saturate_sound step fuel
        intro vertex member
        obtain ⟨_, old | ⟨edge, inside, target, source⟩⟩ := mem_grow.mp member
        · exact good vertex old
        · exact target ▸ step edge inside (good _ source)

/-- With enough fuel, `saturate` ends closed under the edges into the vertices,
and keeps what it found. -/
theorem saturate_closed {edges : List (α × α)} {vertices : List α} (targets : ∀ edge ∈ edges, edge.2 ∈ vertices) :
    ∀ (fuel : Nat) (keep : α → Bool), vertices.length < fuel + (vertices.filter keep).length →
      (∀ vertex ∈ vertices.filter keep, vertex ∈ saturate edges vertices fuel (vertices.filter keep)) ∧
      ∀ edge ∈ edges, edge.1 ∈ saturate edges vertices fuel (vertices.filter keep) →
        edge.2 ∈ saturate edges vertices fuel (vertices.filter keep)
  | 0, keep, enough => by
      have := List.length_filter_le keep vertices
      omega
  | fuel + 1, keep, enough => by
      simp only [saturate]
      have inVertices : ∀ vertex ∈ vertices.filter keep, vertex ∈ vertices := fun vertex member =>
        (List.mem_filter.mp member).1
      have weaker : ∀ vertex ∈ vertices, keep vertex = true → growKeep edges (vertices.filter keep) vertex = true := by
        intro vertex inside kept
        have : vertex ∈ vertices.filter keep := List.mem_filter.mpr ⟨inside, kept⟩
        simp [growKeep, this]
      split
      · rename_i same
        refine ⟨fun _ member => member, fun edge inside source => ?_⟩
        rw [grow] at same
        have back := filter_length_eq weaker same.symm edge.2 (targets edge inside)
          (by simp only [growKeep, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
                List.contains_iff_mem]
              exact .inr ⟨edge, inside, rfl, source⟩)
        exact List.mem_filter.mpr ⟨targets edge inside, back⟩
      · rename_i different
        have grows : (vertices.filter keep).length < (grow edges vertices (vertices.filter keep)).length := by
          have le : (vertices.filter keep).length ≤ (grow edges vertices (vertices.filter keep)).length :=
            filter_length_le_of weaker
          omega
        obtain ⟨kept, closed⟩ := saturate_closed targets fuel (growKeep edges (vertices.filter keep)) (by
          simp only [grow] at grows; omega)
        exact ⟨fun vertex member => kept vertex (mem_grow.mpr ⟨inVertices vertex member, .inl member⟩), closed⟩

omit [DecidableEq α] in
/-- Steps of a transitive closure: a first edge, then the rest. -/
theorem transGen_head {r : α → α → Prop} {first last : α} :
    Relation.TransGen r first last ↔ ∃ next, r first next ∧ (next = last ∨ Relation.TransGen r next last) := by
  constructor
  · intro path
    induction path with
    | single edge => exact ⟨_, edge, .inl rfl⟩
    | tail _ edge ih =>
        obtain ⟨next, firstEdge, rfl | rest⟩ := ih
        · exact ⟨next, firstEdge, .inr (.single edge)⟩
        · exact ⟨next, firstEdge, .inr (.tail rest edge)⟩
  · rintro ⟨next, edge, rfl | rest⟩
    · exact .single edge
    · exact .trans (.single edge) rest

/-- `reach` is the transitive closure of the edges. -/
theorem reach_iff {edges : List (α × α)} {vertices : List α} (targets : ∀ edge ∈ edges, edge.2 ∈ vertices)
    {start vertex : α} : vertex ∈ reach edges vertices start ↔ Relation.TransGen (Edge edges) start vertex := by
  constructor
  · intro member
    refine saturate_sound (Good := Relation.TransGen (Edge edges) start) (fun edge _ good => ?_) _ _ ?_ vertex member
    · exact .tail good (by assumption)
    · intro found inside
      have := (List.mem_filter.mp inside).2
      simp only [List.contains_iff_mem] at this
      exact .single this
  · obtain ⟨kept, closed⟩ := saturate_closed targets (vertices.length + 1)
      (fun vertex => edges.contains (start, vertex)) (by omega)
    intro path
    induction path with
    | single edge =>
        exact kept _ (List.mem_filter.mpr ⟨targets _ edge, by simpa [Edge] using edge⟩)
    | tail _ edge ih => exact closed _ edge ih

theorem reach_trans {edges : List (α × α)} {vertices : List α} (targets : ∀ edge ∈ edges, edge.2 ∈ vertices)
    {first middle last : α} (left : middle ∈ reach edges vertices first) (right : last ∈ reach edges vertices middle) :
    last ∈ reach edges vertices first :=
  (reach_iff targets).mpr (.trans ((reach_iff targets).mp left) ((reach_iff targets).mp right))

/-- A target of an edge from `start` is reached. -/
theorem reach_edge {edges : List (α × α)} {vertices : List α} (targets : ∀ edge ∈ edges, edge.2 ∈ vertices)
    {start target : α} (edge : (start, target) ∈ edges) : target ∈ reach edges vertices start :=
  (reach_iff targets).mpr (.single edge)

/-- What `start` reaches: its successors and what they reach. -/
theorem reach_step {edges : List (α × α)} {vertices : List α} (targets : ∀ edge ∈ edges, edge.2 ∈ vertices)
    {start vertex : α} : vertex ∈ reach edges vertices start ↔
      ∃ next, (start, next) ∈ edges ∧ (next = vertex ∨ vertex ∈ reach edges vertices next) := by
  rw [reach_iff targets, transGen_head]
  simp only [reach_iff targets, Edge]

/-! ## Greatest post-fixpoints by deflation -/

/-- Drop the vertices `ok` rejects, given the remaining set, until nothing changes. -/
def deflate (ok : List α → α → Bool) : Nat → List α → List α
  | 0, set => set
  | fuel + 1, set =>
      let next := set.filter (ok set)
      if next.length = set.length then set else deflate ok fuel next

/-- The greatest set inside `vertices` all of whose vertices `ok` accepts,
given the set. -/
def greatest (ok : List α → α → Bool) (vertices : List α) : List α :=
  deflate ok (vertices.length + 1) vertices

omit [DecidableEq α] in
theorem deflate_sub {ok : List α → α → Bool} :
    ∀ (fuel : Nat) (set : List α), ∀ vertex ∈ deflate ok fuel set, vertex ∈ set
  | 0, _, _, member => member
  | fuel + 1, set, vertex, member => by
      simp only [deflate] at member
      split at member
      · exact member
      · exact (List.mem_filter.mp (deflate_sub fuel _ vertex member)).1

omit [DecidableEq α] in
theorem deflate_post {ok : List α → α → Bool} :
    ∀ (fuel : Nat) (set : List α), set.length < fuel → ∀ vertex ∈ deflate ok fuel set, ok (deflate ok fuel set) vertex = true
  | 0, _, small => absurd small (Nat.not_lt_zero _)
  | fuel + 1, set, small => by
      simp only [deflate]
      split
      · rename_i same
        intro vertex member
        exact List.length_filter_eq_length_iff.mp same vertex member
      · rename_i different
        have shorter : (set.filter (ok set)).length < set.length := by
          have := List.length_filter_le (ok set) set
          omega
        exact deflate_post fuel _ (by omega)

omit [DecidableEq α] in
/-- Every vertex `greatest` keeps is accepted given the result: a post-fixpoint. -/
theorem greatest_post {ok : List α → α → Bool} {vertices : List α} :
    ∀ vertex ∈ greatest ok vertices, ok (greatest ok vertices) vertex = true :=
  deflate_post _ _ (Nat.lt_succ_self _)

omit [DecidableEq α] in
theorem greatest_sub {ok : List α → α → Bool} {vertices : List α} :
    ∀ vertex ∈ greatest ok vertices, vertex ∈ vertices :=
  deflate_sub _ _

omit [DecidableEq α] in
/-- For a monotone check, every post-fixpoint inside the universe is kept. -/
theorem greatest_ge {ok : List α → α → Bool}
    (monotone : ∀ (small large : List α), (∀ vertex ∈ small, vertex ∈ large) → ∀ vertex, ok small vertex = true →
      ok large vertex = true)
    {vertices post : List α} (inside : ∀ vertex ∈ post, vertex ∈ vertices)
    (accepted : ∀ vertex ∈ post, ok post vertex = true) : ∀ vertex ∈ post, vertex ∈ greatest ok vertices := by
  suffices keep : ∀ (fuel : Nat) (set : List α), (∀ vertex ∈ post, vertex ∈ set) →
      ∀ vertex ∈ post, vertex ∈ deflate ok fuel set from keep _ _ inside
  intro fuel
  induction fuel with
  | zero => intro set sub; exact sub
  | succ fuel ih =>
      intro set sub
      simp only [deflate]
      split
      · exact sub
      · apply ih
        intro vertex member
        exact List.mem_filter.mpr ⟨sub vertex member, monotone post set sub vertex (accepted vertex member)⟩

end Graph

end AnthillModKbSpec.Tabled
