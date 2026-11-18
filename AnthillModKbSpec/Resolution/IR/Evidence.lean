import AnthillModKbSpec.Resolution.IR.Check
import AnthillModKbSpec.Resolution.Tabled.Graph
import AnthillModKbSpec.Resolution.Tabled.AbstractSound
import AnthillModKbSpec.Resolution.P0.Rank

/-! # The IR's evidence classes: P0, P1, P2 (S27)

A well-formed IR program and query (`Program.check`) are classified before
anything runs ([decision IR](../../../docs/decision-ir.md)). **P1** is a
program with the *finiteness evidence*: the query's relevant program, the
ground rule instances its calls and the denials' can use (`IR/Relevance`), is
finite, both for the answers a call derives and for the answers it may have
in some model (`IR/RelevantProgram`). **P2** is a well-formed program without
it, run by the same evaluator with fuel (S28). **P0** is S07's ground acyclic
case, and has the evidence too; S07's ground inputs classify P0 where the IR
expresses them (`IR/Ground`).

**Call patterns.** The evidence is read per call pattern, not per declared
mode: a call binds some of its arguments before it runs (all its inputs, and
any output a name already bound gives), and leaves the others free. The query
`path(a, c)` calls `path` with both arguments bound, `∃Y. path(a, Y)` with the
second free. A *vertex* is a predicate with a pattern; reading a rule of
`p` with the arguments of pattern `β` bound gives the patterns of its calls
(`Program.successors`). The vertices the query and the denials reach form a
finite graph (`Program.vertices`, closed under successors within its bound:
`Program.closed_vertices`);
the denials join every query's graph (decided with the user, 2026-11-18).
Each vertex gets a level (`Program.levelTable`, the vertices it reaches
outside its component), computed once with the data-term outputs.

**The evidence** (decided with the user, 2026-11-17, from S23's analyses):

1. *Bounded calls*: every call at its caller's level has bound arguments that
   are data terms of its caller's bound arguments (`Program.growingIn` finds
   none); no call goes to a higher level (`Program.levelIn_le`). Data
   terms are S23's: subterms of the head's bound arguments, ground terms, and
   the free outputs of a call to a vertex with data-term outputs
   (`Program.dataOutputs`, the greatest post-fixpoint), called with data-term
   arguments. Across levels a body may construct a lower vertex's input
   (`p(X) :- q(succ(X))`): the bound composes along the levels, and term
   growth is bounded by the bodies, since each rule instance is finite.
2. *Finitely many possible answers*: from a vertex that leaves an output
   free, every call that leaves one free lowers the rank: it goes to a lower
   level, or its bound arguments decrease (subterms of its caller's, one
   strictly). A self-supporting cycle holds of unboundedly many values in the
   greatest fixpoint: `path(X, Y) :- edge(X, Z), path(Z, Y)` over a cycle,
   with `Y` free, holds of every `Y` (`Program.freeOutputsIn` finds the
   recursive call).
3. *Guards*: every name of a rule and of a denial is guarded by a guard
   literal of its body, and every answer name by one of the query's goals
   (`Program.unguarded` finds none), so the Herbrand reduction applies
   (`IR/Herbrand`). An unguarded name ranges over the carrier: P2 (decided
   with the user, 2026-11-18).
4. *Rigid parameters* (decided with the user, 2026-11-18): each is guarded by
   a finite guard among the query's conditions (`Program.unsplit` finds none),
   and the query is P1 when every instance of the split (`Program.splitValues`)
   is P0 or P1 (`IR/Parameters`).

**P0**, S07's class: ground rules whose bodies are calls and NAF, no denial,
no derived rule, no opened predicate, a ground query of calls and NAF, and no
atom depending on itself (`Program.ground`; S07 ranks atoms, so
`p(a) :- p(b). p(b).` is P0). A query is P0 only with no note.

Derived rules (checked lemmas) are checked as rules, and stay outside the
completion, the vertex graph, and the relevant program: a decision that
derives with them (S28's certificates, S31) bounds them itself. -/

namespace AnthillModKbSpec.IR

open Completion Tabled Admission Answers

variable {Variable Literal Symbol : Type}

/-! ## Call patterns -/

/-- A call pattern: for each argument, whether it is bound when the call runs. -/
abbrev Pattern := List Bool

/-- A predicate called with a pattern. -/
abbrev Vertex (Symbol : Type) := Symbol × Pattern

/-- Every argument bound. -/
def full (arity : Nat) : Pattern := List.replicate arity true

/-- The arguments a pattern binds. -/
def boundArgs {α : Type} (pattern : Pattern) (args : List α) : List α :=
  (args.zip pattern).filterMap fun (arg, bound) => if bound then some arg else none

theorem mem_of_mem_boundArgs {α : Type} {pattern : Pattern} {args : List α} {arg : α}
    (member : arg ∈ boundArgs pattern args) : arg ∈ args := by
  simp only [boundArgs, List.mem_filterMap] at member
  obtain ⟨⟨original, flag⟩, inZip, produced⟩ := member
  cases flag <;> simp at produced
  subst produced; exact (List.of_mem_zip inZip).1

/-- A pattern leaves some argument free. -/
def Pattern.free (pattern : Pattern) : Bool := pattern.any (· == false)

/-! ## Counting -/

/-- A literal's site: a call's or a NAF's predicate with its arity. -/
def Goal.site? : Goal Variable Literal Symbol → Option (Symbol × Nat)
  | .call predicate args | .naf predicate args => some (predicate, args.length)
  | _ => none

theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] : ∀ (items : List α), items.eraseDups.Nodup
  | [] => List.nodup_nil
  | first :: rest => by
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr ⟨?_, nodup_eraseDups _⟩
      simp [List.mem_eraseDups, List.mem_filter]
termination_by items => items.length
decreasing_by exact Nat.lt_add_one_of_le (List.length_filter_le _ _)

theorem sum_map_const {α : Type} (value : Nat) : ∀ items : List α, (items.map fun _ => value).sum = items.length * value
  | [] => by simp
  | _ :: rest => by
      simp only [List.map_cons, List.sum_cons, List.length_cons, sum_map_const value rest, Nat.succ_mul]
      omega

theorem length_tuples {α : Type} (choices : List α) :
    ∀ n, (Tabled.tuples choices n).length = choices.length ^ n
  | 0 => rfl
  | n + 1 => by
      simp only [Tabled.tuples, List.length_flatMap, List.length_map]
      rw [sum_map_const, length_tuples choices n, Nat.pow_succ]

theorem le_foldr_max : ∀ (items : List Nat) (init : Nat), init ≤ items.foldr max init ∧ ∀ item ∈ items, item ≤ items.foldr max init
  | [], init => ⟨Nat.le_refl _, fun _ member => by cases member⟩
  | first :: rest, init => by
      obtain ⟨initLe, restLe⟩ := le_foldr_max rest init
      simp only [List.foldr_cons]
      refine ⟨Nat.le_trans initLe (Nat.le_max_right _ _), fun item member => ?_⟩
      rcases List.mem_cons.mp member with rfl | inside
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (restLe item inside) (Nat.le_max_right _ _)

section Patterns

variable [DecidableEq Variable]

/-- The pattern of a call with these names bound before it: an argument is
bound when all its names are. -/
def patternOf (bound : List Variable) (args : List (Term Variable Literal Symbol)) : Pattern :=
  args.map fun arg => available bound arg.freeVars

/-- The names a rule starts from under a pattern: those of the bound head
arguments. -/
def startNames (pattern : Pattern) (args : List (Term Variable Literal Symbol)) : List Variable :=
  namesOf (boundArgs pattern args)

/-- A vertex reached from a body literal: a call with its pattern, a NAF with
every argument bound. -/
def Goal.vertex? (bound : List Variable) : Goal Variable Literal Symbol → Option (Vertex Symbol)
  | .call predicate args => some (predicate, patternOf bound args)
  | .naf predicate args => some (predicate, full args.length)
  | _ => none

/-- The calls of a body read left to right from the names bound before it:
each literal's position, the literal, the names bound before it, and its
vertex. -/
def bodyCalls : Nat → List Variable → List (Goal Variable Literal Symbol) →
    List (Nat × Goal Variable Literal Symbol × List Variable × Vertex Symbol)
  | _, _, [] => []
  | position, bound, goal :: rest =>
      (match goal.vertex? bound with
        | some vertex => [(position, goal, bound, vertex)]
        | none => []) ++ bodyCalls (position + 1) (after bound goal) rest

theorem site_of_vertex? {goal : Goal Variable Literal Symbol} {bound : List Variable} {vertex : Vertex Symbol}
    (found : goal.vertex? bound = some vertex) : goal.site? = some (vertex.1, vertex.2.length) := by
  cases goal with
  | call predicate args =>
      simp only [Goal.vertex?, Option.some.injEq] at found; subst found
      simp [Goal.site?, patternOf]
  | naf predicate args =>
      simp only [Goal.vertex?, Option.some.injEq] at found; subst found
      simp [Goal.site?, full]
  | _ => simp [Goal.vertex?] at found

theorem mem_bodyCalls : ∀ {position : Nat} {bound : List Variable} {body : List (Goal Variable Literal Symbol)}
    {call : Nat × Goal Variable Literal Symbol × List Variable × Vertex Symbol}, call ∈ bodyCalls position bound body →
      call.2.1 ∈ body ∧ call.2.1.vertex? call.2.2.1 = some call.2.2.2
  | _, _, [], _, member => by cases member
  | position, bound, goal :: rest, call, member => by
      simp only [bodyCalls, List.mem_append] at member
      rcases member with here | there
      · cases found : goal.vertex? bound with
        | none => rw [found] at here; cases here
        | some vertex =>
            rw [found] at here
            simp only [List.mem_singleton] at here
            subst here
            exact ⟨List.mem_cons_self, found⟩
      · obtain ⟨inRest, found⟩ := mem_bodyCalls there
        exact ⟨List.mem_cons_of_mem _ inRest, found⟩

end Patterns

/-- The vertices a query starts from: its conditions' and its goals' calls,
read from its rigid parameters. -/
def queryVertices [DecidableEq Variable] (query : Query Variable Literal Symbol) : List (Vertex Symbol) :=
  (query.conditions.flatMap fun condition => (bodyCalls 0 query.parameters [condition]).map (·.2.2.2)) ++
    (bodyCalls 0 query.parameters query.goals).map (·.2.2.2)

namespace Program

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] (program : Program Variable Literal Symbol)

/-! ## The graph of call patterns -/

/-- The rules a vertex reads: those of its predicate at its arity, with their
indices. -/
def rulesAt (vertex : Vertex Symbol) : List (Nat × Rule Variable Literal Symbol) :=
  (program.rulesOf vertex.1).filter fun entry => entry.2.args.length == vertex.2.length

/-- The calls of a vertex's rules, each with its rule's index and the rule. -/
def callsAt (vertex : Vertex Symbol) :
    List (Nat × Rule Variable Literal Symbol × Nat × Goal Variable Literal Symbol × List Variable × Vertex Symbol) :=
  (program.rulesAt vertex).flatMap fun (index, rule) =>
    (bodyCalls 0 (startNames vertex.2 rule.args) rule.body).map fun call => (index, rule, call)

/-- The vertices a vertex's rules call. -/
def successors (vertex : Vertex Symbol) : List (Vertex Symbol) :=
  (program.callsAt vertex).map fun call => call.2.2.2.2.2

/-- The vertices the denials start from: their bodies' calls, read from no
bound name. Denials join every query's graph (decided with the user,
2026-11-18): their instances that the relevant atoms meet are decided with
the query. -/
def denialVertices : List (Vertex Symbol) :=
  program.denials.flatMap fun body => (bodyCalls 0 [] body).map (·.2.2.2)

/-- One round of the vertex closure: the vertices found and their successors. -/
def growVertices (found : List (Vertex Symbol)) : List (Vertex Symbol) :=
  (found ++ found.flatMap program.successors).eraseDups

/-- Rounds until a round adds nothing, within `fuel` rounds (S24's
`untilStable`). -/
def closeVertices (fuel : Nat) (found : List (Vertex Symbol)) : List (Vertex Symbol) :=
  Tabled.untilStable (fun next found => next.length == found.length) program.growVertices fuel found

/-- The number of literals of the rules, the denials, and the query. -/
def literalCount (query : Query Variable Literal Symbol) : Nat :=
  (program.rules.map fun rule => rule.body.length).sum + (program.denials.map List.length).sum + query.goals.length +
    query.conditions.length

/-- The widest literal's arity. -/
def widest (query : Query Variable Literal Symbol) : Nat :=
  ((program.rules.map (·.body) ++ program.denials).flatMap fun body => body.map fun goal => goal.args.length).foldr
    max ((query.conditions ++ query.goals).map (fun goal => goal.args.length) |>.foldr max 0)

/-- A bound on the number of vertices: each is a called symbol with a pattern
of a call's length (`length_allVertices_lt`). -/
def vertexBound (query : Query Variable Literal Symbol) : Nat :=
  (program.literalCount query + 1) * 2 ^ program.widest query + 1

/-- The vertices the query and the denials reach. -/
def vertices (query : Query Variable Literal Symbol) : List (Vertex Symbol) :=
  program.closeVertices (program.vertexBound query) (queryVertices query ++ program.denialVertices).eraseDups

/-- The vertices are closed under successors. -/
def closedIn (found : List (Vertex Symbol)) : Bool :=
  found.all fun vertex => (program.successors vertex).all found.contains

/-- The query's vertices are closed under successors: the closure reached its
end, as it always does within its bound (`closed_vertices`). -/
def closed (query : Query Variable Literal Symbol) : Bool := program.closedIn (program.vertices query)

/-! ## The vertex closure ends within its bound -/

/-- The sites of the program's rules and denials and of the query. -/
def sites (query : Query Variable Literal Symbol) : List (Symbol × Nat) :=
  program.rules.flatMap (fun rule => rule.body.filterMap Goal.site?) ++
    program.denials.flatMap (fun body => body.filterMap Goal.site?) ++
    query.goals.filterMap Goal.site? ++ query.conditions.filterMap Goal.site?

/-- Every vertex a site can have: its predicate with each pattern of its
arity. The vertex closure stays inside it. -/
def allVertices (query : Query Variable Literal Symbol) : List (Vertex Symbol) :=
  (program.sites query).flatMap fun site => (Tabled.tuples [true, false] site.2).map (site.1, ·)

section Closure

variable {program}

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem mem_allVertices {query : Query Variable Literal Symbol} {symbol : Symbol} {pattern : Pattern}
    (site : (symbol, pattern.length) ∈ program.sites query) : (symbol, pattern) ∈ program.allVertices query := by
  refine List.mem_flatMap.mpr ⟨_, site, List.mem_map.mpr ⟨pattern, ?_, rfl⟩⟩
  exact Tabled.mem_tuples fun flag _ => by cases flag <;> simp

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem vertex_allVertices {query : Query Variable Literal Symbol} {goal : Goal Variable Literal Symbol} {bound : List Variable}
    {vertex : Vertex Symbol} (found : goal.vertex? bound = some vertex)
    (inSites : ∀ site, goal.site? = some site → site ∈ program.sites query) : vertex ∈ program.allVertices query :=
  mem_allVertices (inSites _ (site_of_vertex? found))

omit [DecidableEq Literal] in
theorem successors_allVertices {query : Query Variable Literal Symbol} {vertex callee : Vertex Symbol}
    (successor : callee ∈ program.successors vertex) : callee ∈ program.allVertices query := by
  obtain ⟨⟨index, rule, call⟩, inCalls, rfl⟩ := List.mem_map.mp successor
  obtain ⟨⟨index', rule'⟩, atVertex, inMap⟩ := List.mem_flatMap.mp inCalls
  obtain ⟨call', callMember, same⟩ := List.mem_map.mp inMap
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, rfl, rfl⟩ := same
  obtain ⟨goalMember, found⟩ := mem_bodyCalls callMember
  refine vertex_allVertices found fun site siteEq => ?_
  have ruleMember := rulesOf_mem (List.mem_filter.mp atVertex).1
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨rule', ruleMember, List.mem_filterMap.mpr ⟨_, goalMember, siteEq⟩⟩)))

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem start_allVertices {query : Query Variable Literal Symbol} {vertex : Vertex Symbol}
    (member : vertex ∈ queryVertices query ++ program.denialVertices) : vertex ∈ program.allVertices query := by
  rcases List.mem_append.mp member with fromQuery | fromDenials
  · simp only [queryVertices, List.mem_append, List.mem_flatMap, List.mem_map] at fromQuery
    rcases fromQuery with ⟨condition, conditionMember, call, inCalls, rfl⟩ | ⟨call, inCalls, rfl⟩
    · obtain ⟨goalMember, found⟩ := mem_bodyCalls inCalls
      simp only [List.mem_singleton] at goalMember
      subst goalMember
      exact vertex_allVertices found fun site siteEq =>
        List.mem_append_right _ (List.mem_filterMap.mpr ⟨_, conditionMember, siteEq⟩)
    · obtain ⟨goalMember, found⟩ := mem_bodyCalls inCalls
      exact vertex_allVertices found fun site siteEq =>
        List.mem_append_left _ (List.mem_append_right _ (List.mem_filterMap.mpr ⟨_, goalMember, siteEq⟩))
  · simp only [denialVertices, List.mem_flatMap, List.mem_map] at fromDenials
    obtain ⟨body, bodyMember, call, inCalls, rfl⟩ := fromDenials
    obtain ⟨goalMember, found⟩ := mem_bodyCalls inCalls
    exact vertex_allVertices found fun site siteEq =>
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨body, bodyMember, List.mem_filterMap.mpr ⟨_, goalMember, siteEq⟩⟩)))

omit [DecidableEq Literal] in
/-- A round that adds no vertex leaves the vertices closed; otherwise it adds
one, inside the allVertices. -/
theorem closeVertices_closed {query : Query Variable Literal Symbol} :
    ∀ (fuel : Nat) (found : List (Vertex Symbol)), found.Nodup → (∀ vertex ∈ found, vertex ∈ program.allVertices query) →
      (program.allVertices query).length < found.length + fuel → program.closedIn (program.closeVertices fuel found) = true
  | 0, found, nodup, inside, bound => by
      have := List.Nodup.length_le_of_subset nodup inside
      omega
  | fuel + 1, found, nodup, inside, bound => by
      have grownNodup : (program.growVertices found).Nodup := nodup_eraseDups _
      have grownInside : ∀ vertex ∈ program.growVertices found, vertex ∈ program.allVertices query := by
        intro vertex member
        simp only [growVertices, List.mem_eraseDups, List.mem_append, List.mem_flatMap] at member
        rcases member with old | ⟨source, _, successor⟩
        · exact inside vertex old
        · exact successors_allVertices successor
      have kept : ∀ vertex ∈ found, vertex ∈ program.growVertices found := fun vertex member => by
        simp [growVertices, List.mem_eraseDups, member]
      have grows := List.Nodup.length_le_of_subset nodup kept
      unfold closeVertices Tabled.untilStable
      split
      · rename_i same
        have sameLength : (program.growVertices found).length = found.length := by simpa using same
        unfold closedIn
        refine List.all_eq_true.mpr fun vertex member => List.all_eq_true.mpr fun callee successor => ?_
        refine List.contains_iff_mem.mpr (Classical.byContradiction fun outside => ?_)
        have longer := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨outside, nodup⟩) (l₂ := program.growVertices found)
          (fun other inside' => by
            rcases List.mem_cons.mp inside' with rfl | old
            · simp only [growVertices, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
              exact .inr ⟨vertex, member, successor⟩
            · exact kept other old)
        simp only [List.length_cons] at longer
        omega
      · rename_i different
        have differ : (program.growVertices found).length ≠ found.length := by simpa using different
        exact closeVertices_closed fuel _ grownNodup grownInside (by omega)

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem length_flatMap_filterMap_le {α β γ : Type} (f : α → List β) (g : β → Option γ) :
    ∀ items : List α, (items.flatMap fun item => (f item).filterMap g).length ≤ (items.map fun item => (f item).length).sum
  | [] => by simp
  | first :: rest => by
      simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
      have := length_flatMap_filterMap_le f g rest
      have := List.length_filterMap_le g (f first)
      omega

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem sum_le_length_mul {α : Type} (f : α → Nat) (bound : Nat) :
    ∀ items : List α, (∀ item ∈ items, f item ≤ bound) → (items.map f).sum ≤ items.length * bound
  | [], _ => by simp
  | first :: rest, each => by
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      have := sum_le_length_mul f bound rest fun item member => each item (List.mem_cons_of_mem _ member)
      have := each first List.mem_cons_self
      omega

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem site_arity {query : Query Variable Literal Symbol} : ∀ site ∈ program.sites query, site.2 ≤ program.widest query := by
  intro site member
  obtain ⟨initLe, inner⟩ := le_foldr_max ((program.rules.map (·.body) ++ program.denials).flatMap fun body =>
    body.map fun goal => goal.args.length) ((query.conditions ++ query.goals).map (fun goal => goal.args.length) |>.foldr max 0)
  obtain ⟨_, outer⟩ := le_foldr_max ((query.conditions ++ query.goals).map (fun goal => goal.args.length)) 0
  have ofGoal : ∀ {goal : Goal Variable Literal Symbol}, goal.site? = some site → site.2 = goal.args.length := by
    intro goal siteEq
    cases goal <;> simp [Goal.site?] at siteEq <;> (subst siteEq; simp [Goal.args])
  unfold widest
  simp only [sites, List.mem_append, List.mem_flatMap, List.mem_filterMap] at member
  rcases member with ((⟨rule, ruleMember, goal, goalMember, siteEq⟩ | ⟨body, bodyMember, goal, goalMember, siteEq⟩) |
    ⟨goal, goalMember, siteEq⟩) | ⟨goal, goalMember, siteEq⟩
  · rw [ofGoal siteEq]
    exact inner _ (List.mem_flatMap.mpr ⟨rule.body, List.mem_append_left _ (List.mem_map.mpr ⟨rule, ruleMember, rfl⟩),
      List.mem_map.mpr ⟨goal, goalMember, rfl⟩⟩)
  · rw [ofGoal siteEq]
    exact inner _ (List.mem_flatMap.mpr ⟨body, List.mem_append_right _ bodyMember, List.mem_map.mpr ⟨goal, goalMember, rfl⟩⟩)
  · rw [ofGoal siteEq]
    exact Nat.le_trans (outer _ (List.mem_map.mpr ⟨goal, List.mem_append_right _ goalMember, rfl⟩)) initLe
  · rw [ofGoal siteEq]
    exact Nat.le_trans (outer _ (List.mem_map.mpr ⟨goal, List.mem_append_left _ goalMember, rfl⟩)) initLe

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem length_sites_le (query : Query Variable Literal Symbol) : (program.sites query).length ≤ program.literalCount query := by
  have rules := length_flatMap_filterMap_le (fun rule : Rule Variable Literal Symbol => rule.body) Goal.site? program.rules
  have denials := length_flatMap_filterMap_le (fun body : List (Goal Variable Literal Symbol) => body) Goal.site? program.denials
  have goals := List.length_filterMap_le Goal.site? query.goals
  have conditions := List.length_filterMap_le Goal.site? query.conditions
  have denialsEq : (program.denials.map fun body => body.length) = program.denials.map List.length := rfl
  rw [denialsEq] at denials
  simp only [sites, literalCount, List.length_append]
  omega

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
/-- **The universe is smaller than the closure's bound**: its vertices are
the sites' predicates with every pattern of their arities, at most one site
per literal and at most `2 ^ widest` patterns per site. -/
theorem length_allVertices_lt (query : Query Variable Literal Symbol) :
    (program.allVertices query).length < program.vertexBound query := by
  have total : (program.allVertices query).length ≤ (program.sites query).length * 2 ^ program.widest query := by
    simp only [allVertices, List.length_flatMap, List.length_map, length_tuples, List.length_cons, List.length_nil]
    exact sum_le_length_mul _ _ _ fun site member => Nat.pow_le_pow_right (by decide) (site_arity site member)
  have count := Nat.mul_le_mul_right (2 ^ program.widest query) (length_sites_le (program := program) query)
  rw [vertexBound, Nat.add_mul, Nat.one_mul]
  generalize 2 ^ program.widest query = patterns at total count ⊢
  omega

omit [DecidableEq Literal] in
/-- **The vertex closure ends within its bound**: the query's vertices are
closed under successors. -/
theorem closed_vertices (query : Query Variable Literal Symbol) : program.closed query = true :=
  closeVertices_closed _ _ (nodup_eraseDups _) (fun _ member => start_allVertices (List.mem_eraseDups.mp member))
    (by have := length_allVertices_lt (program := program) query; omega)

end Closure


/-- Each vertex's level: the vertices it reaches that do not reach it back,
those outside its component. Computed once for the graph. A call to another
component goes to a lower level, one inside the component stays at the
level: in a closed graph no call goes to a higher one (`levelIn_le`). -/
def levelTable (found : List (Vertex Symbol)) : List (Vertex Symbol × Nat) :=
  let edgeList := found.flatMap fun vertex => (program.successors vertex).map (vertex, ·)
  let reaches := found.map fun vertex => (vertex, Tabled.reach edgeList found vertex)
  let reachOf := fun vertex => ((reaches.find? (·.1 == vertex)).map (·.2)).getD []
  found.map fun vertex =>
    (vertex, (found.filter fun other => (reachOf vertex).contains other && !(reachOf other).contains vertex).length)

/-- A vertex's level in a table. -/
def levelIn (table : List (Vertex Symbol × Nat)) (vertex : Vertex Symbol) : Nat :=
  ((table.find? (·.1 == vertex)).map (·.2)).getD 0

/-- The levels of the query's vertices. -/
def levels (query : Query Variable Literal Symbol) (vertex : Vertex Symbol) : Nat :=
  levelIn (program.levelTable (program.vertices query)) vertex

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
/-- A table of a list's elements, looked up at a member: the member's entry. -/
theorem lookup_map {α β : Type} [BEq α] [LawfulBEq α] (f : α → β) {items : List α} {item : α} (member : item ∈ items) :
    ((items.map fun x => (x, f x)).find? (·.1 == item)).map (·.2) = some (f item) := by
  rw [List.find?_map]
  cases found : items.find? ((fun entry : α × β => entry.1 == item) ∘ fun x => (x, f x)) with
  | none =>
      have := List.find?_eq_none.mp found item member
      simp at this
  | some other =>
      have := List.find?_some found
      simp only [Function.comp_apply, beq_iff_eq] at this
      subst this
      rfl

omit [DecidableEq Literal] in
theorem levelIn_table {found : List (Vertex Symbol)} {vertex : Vertex Symbol} (member : vertex ∈ found) :
    levelIn (program.levelTable found) vertex =
      (found.filter fun other =>
        (Tabled.reach (found.flatMap fun vertex => (program.successors vertex).map (vertex, ·)) found vertex).contains other &&
          !(Tabled.reach (found.flatMap fun vertex => (program.successors vertex).map (vertex, ·)) found other).contains vertex).length := by
  unfold levelIn levelTable
  simp only
  rw [lookup_map _ member]
  simp only [Option.getD_some]
  congr 1
  apply List.filter_congr
  intro other otherMember
  rw [lookup_map _ member, lookup_map _ otherMember]
  rfl

omit [DecidableEq Literal] in
/-- **Levels never rise along a call**: in a closed graph, a call goes to a
level no higher than its caller's, since what it reaches outside its own
component its caller reaches outside its own. -/
theorem levelIn_le {found : List (Vertex Symbol)} (closed : program.closedIn found = true) {vertex callee : Vertex Symbol}
    (member : vertex ∈ found) (successor : callee ∈ program.successors vertex) :
    levelIn (program.levelTable found) callee ≤ levelIn (program.levelTable found) vertex := by
  have calleeMember : callee ∈ found :=
    List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp closed vertex member) callee successor)
  have targets : ∀ edge ∈ found.flatMap (fun vertex => (program.successors vertex).map (vertex, ·)), edge.2 ∈ found := by
    intro edge inside
    obtain ⟨source, sourceMember, inMap⟩ := List.mem_flatMap.mp inside
    obtain ⟨target, targetMember, rfl⟩ := List.mem_map.mp inMap
    exact List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp closed source sourceMember) target targetMember)
  have reached : callee ∈ Tabled.reach (found.flatMap fun vertex => (program.successors vertex).map (vertex, ·)) found vertex :=
    Tabled.reach_edge targets (List.mem_flatMap.mpr ⟨vertex, member, List.mem_map.mpr ⟨callee, successor, rfl⟩⟩)
  rw [program.levelIn_table member, program.levelIn_table calleeMember]
  apply Tabled.filter_length_le_of
  intro other _ holds
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at holds ⊢
  obtain ⟨fromCallee, notBack⟩ := holds
  refine ⟨Tabled.reach_trans targets reached fromCallee, ?_⟩
  cases back : (Tabled.reach (found.flatMap fun vertex => (program.successors vertex).map (vertex, ·)) found other).contains vertex with
  | false => rfl
  | true =>
      have backToCallee := List.contains_iff_mem.mpr (Tabled.reach_trans targets (List.contains_iff_mem.mp back) reached)
      rw [backToCallee] at notBack
      cases notBack

omit [DecidableEq Literal] in
/-- In the query's graph, no call goes to a higher level. -/
theorem levels_le {query : Query Variable Literal Symbol} {vertex callee : Vertex Symbol}
    (member : vertex ∈ program.vertices query) (successor : callee ∈ program.successors vertex) :
    program.levels query callee ≤ program.levels query vertex :=
  program.levelIn_le (closed_vertices query) member successor

/-! ## Data terms and decrease -/

/-- The frame of a rule read under a pattern: its bound head arguments. -/
def frameAt (pattern : Pattern) (rule : Rule Variable Literal Symbol) : Frame Variable Literal Symbol :=
  ⟨boundArgs pattern rule.args, []⟩

/-- The names holding data terms after a literal, from those before it. `info`
says which vertices have data-term outputs: a call with data-term bound
arguments to such a vertex makes its names data terms; an equation with a
data-term side makes the other side's names data terms; a guard binding its
argument over a finite domain makes its names data terms, its members being
ground terms of the program. -/
def flowGoal (info : Vertex Symbol → Bool) (frame : Frame Variable Literal Symbol) (bound small : List Variable) :
    Goal Variable Literal Symbol → List Variable
  | .call predicate args =>
      let pattern := patternOf bound args
      if info (predicate, pattern) && (boundArgs pattern args).all (frame.small small) then small ++ namesOf args
      else small
  | .equal left right =>
      small ++ (if frame.small small left then right.freeVars else []) ++ (if frame.small small right then left.freeVars else [])
  | .guard symbol arg => if program.finite symbol && !available bound arg.freeVars then small ++ arg.freeVars else small
  | _ => small

/-- `flowGoal` through a body. -/
def flowBody (info : Vertex Symbol → Bool) (frame : Frame Variable Literal Symbol) :
    List Variable → List Variable → List (Goal Variable Literal Symbol) → List Variable
  | _, small, [] => small
  | bound, small, goal :: rest => flowBody info frame (after bound goal) (program.flowGoal info frame bound small goal) rest

/-- A vertex's rules give data-term outputs, given the set of vertices that
do: every argument the pattern leaves free is a data term at the end of the
body. -/
def outputsOk (set : List (Vertex Symbol)) (vertex : Vertex Symbol) : Bool :=
  (program.rulesAt vertex).all fun (_, rule) =>
    let frame := frameAt vertex.2 rule
    let small := program.flowBody (set.contains ·) frame (startNames vertex.2 rule.args) [] rule.body
    (rule.args.zip vertex.2).all fun (arg, bound) => bound || frame.small small arg

/-- The vertices with data-term outputs: the greatest post-fixpoint. -/
def dataOutputs (query : Query Variable Literal Symbol) : List (Vertex Symbol) :=
  greatest program.outputsOk (program.vertices query)

/-- Whether a vertex has data-term outputs. -/
def dataInfo (query : Query Variable Literal Symbol) (vertex : Vertex Symbol) : Bool :=
  (program.dataOutputs query).contains vertex

/-- A call of a rule read under a vertex's pattern decreases: its bound
arguments are subterms of the rule's bound head arguments at their positions,
one strictly. -/
def decreases (vertex : Vertex Symbol) (rule : Rule Variable Literal Symbol) (goal : Goal Variable Literal Symbol)
    (callee : Vertex Symbol) : Bool :=
  (frameAt vertex.2 rule).decreasing (boundArgs callee.2 goal.args)

/-- A call that leaves an output free lowers the rank: it goes to a lower
level, or it decreases. -/
def lowersWith (levelOf : Vertex Symbol → Nat) (vertex : Vertex Symbol) (rule : Rule Variable Literal Symbol)
    (goal : Goal Variable Literal Symbol) (callee : Vertex Symbol) : Bool :=
  decide (levelOf callee < levelOf vertex) || decreases vertex rule goal callee

/-! ## Notes: why a program is P2 -/

/-- Why a well-formed program is P2 rather than P1. -/
inductive Reason where
  /-- A call at its caller's level whose bound arguments are not data terms of
  its caller's: its terms may grow. -/
  | growingCall
  /-- A call that leaves an output free, from a vertex that leaves one free,
  at a level no lower and not decreasing: a self-supporting cycle may hold of
  unboundedly many values. -/
  | freeOutput
  /-- A name no guard literal guards: it ranges over the carrier, outside the
  Herbrand reduction. -/
  | unguarded
  /-- A rigid parameter no finite guard among the conditions splits. -/
  | parameter
  deriving DecidableEq, Repr

/-- One reason, at its site and path. -/
structure Note (Variable Literal Symbol : Type) where
  site : Site
  path : List Nat
  formula : Term Variable Literal Symbol
  reason : Reason

/-- The calls of a body read left to right, each with its position, the names
bound before it, the names holding data terms before it, and its vertex. -/
def flowCalls (info : Vertex Symbol → Bool) (frame : Frame Variable Literal Symbol) :
    Nat → List Variable → List Variable → List (Goal Variable Literal Symbol) →
      List (Nat × Goal Variable Literal Symbol × List Variable × List Variable × Vertex Symbol)
  | _, _, _, [] => []
  | position, bound, small, goal :: rest =>
      (match goal.vertex? bound with
        | some vertex => [(position, goal, bound, small, vertex)]
        | none => []) ++
        flowCalls info frame (position + 1) (after bound goal) (program.flowGoal info frame bound small goal) rest

/-- A vertex binds its predicate's declared inputs: every vertex of a checked
query does (`Program.covering_of_check`). -/
def covering (vertex : Vertex Symbol) : Bool :=
  match program.predicate? vertex.1 with
  | some declared => (select .input declared.modes vertex.2).all id
  | none => true

/-- Calls at their caller's level whose bound arguments are not data terms of
the caller's: their terms may grow. -/
def growingIn (found : List (Vertex Symbol)) (levelOf : Vertex Symbol → Nat) (info : Vertex Symbol → Bool) :
    List (Note Variable Literal Symbol) :=
  found.flatMap fun vertex =>
    (program.rulesAt vertex).flatMap fun (index, rule) =>
      ((program.flowCalls info (frameAt vertex.2 rule) 0 (startNames vertex.2 rule.args) [] rule.body).filter
          fun (_, goal, _, small, callee) =>
            levelOf callee == levelOf vertex && !(boundArgs callee.2 goal.args).all ((frameAt vertex.2 rule).small small)).map
        fun (position, goal, _, _, _) => ⟨.body index position, [], goal.toTerm, .growingCall⟩

/-- Calls that leave an output free, from a vertex that leaves one free, and
do not lower the rank: at a level no lower, without decreasing. A
self-supporting cycle may hold of unboundedly many outputs. -/
def freeOutputsIn (found : List (Vertex Symbol)) (levelOf : Vertex Symbol → Nat) : List (Note Variable Literal Symbol) :=
  (found.filter (·.2.free)).flatMap fun vertex =>
    ((program.callsAt vertex).filter fun (_, rule, _, goal, _, callee) =>
        callee.2.free && !lowersWith levelOf vertex rule goal callee).map
      fun (index, _, position, goal, _, _) => ⟨.body index position, [], goal.toTerm, .freeOutput⟩

/-- A name is guarded by a guard literal of the body. -/
def guarded (body : List (Goal Variable Literal Symbol)) (name : Variable) : Bool :=
  body.any fun
    | .guard symbol (.var other) => program.kindAt .guard symbol 1 && other == name
    | _ => false

/-- Names of rules, denials, and the query's goals that no guard literal
guards. -/
def unguarded (query : Query Variable Literal Symbol) : List (Note Variable Literal Symbol) :=
  (program.rules.zipIdx.flatMap fun (rule, index) =>
    (rule.names.eraseDups.filter fun name => !program.guarded rule.body name).map fun name =>
      ⟨.head index, [], .var name, .unguarded⟩) ++
  (program.denials.zipIdx.flatMap fun (body, index) =>
    ((bodyNames body).eraseDups.filter fun name => !program.guarded body name).map fun name =>
      ⟨.head (program.rules.length + index), [], .var name, .unguarded⟩) ++
  ((query.answers.eraseDups.filter fun name => !program.guarded query.goals name).map fun name =>
      ⟨.goal, [], .var name, .unguarded⟩)

/-- A parameter is split by a finite guard among the conditions. -/
def splits (query : Query Variable Literal Symbol) (name : Variable) : Bool :=
  query.conditions.any fun
    | .guard symbol (.var other) => program.kindAt .guard symbol 1 && program.finite symbol && other == name
    | _ => false

/-- Rigid parameters no finite guard among the conditions splits. -/
def unsplit (query : Query Variable Literal Symbol) : List (Note Variable Literal Symbol) :=
  (query.parameters.filter fun name => !program.splits query name).map fun name =>
    ⟨.goal, [], .var name, .parameter⟩

/-- Every reason a closed query is P2 rather than P1, read on one computation
of the graph, its levels, and its data-term outputs. -/
def notesWith (found : List (Vertex Symbol)) (levelOf : Vertex Symbol → Nat) (info : Vertex Symbol → Bool)
    (query : Query Variable Literal Symbol) : List (Note Variable Literal Symbol) :=
  program.growingIn found levelOf info ++ program.freeOutputsIn found levelOf ++ program.unguarded query ++
    program.unsplit query

/-- Every reason the query is P2 rather than P1: the graph, its levels, and
its data-term outputs computed once. -/
def notes (query : Query Variable Literal Symbol) : List (Note Variable Literal Symbol) :=
  let found := program.vertices query
  let table := program.levelTable found
  let data := greatest program.outputsOk found
  program.notesWith found (levelIn table) (fun vertex => data.contains vertex) query

theorem notes_eq (query : Query Variable Literal Symbol) :
    program.notes query = program.notesWith (program.vertices query) (program.levels query) (program.dataInfo query) query := rfl

/-! ## P0: S07's ground acyclic case -/

/-- A literal S07's ground fragment runs: a call or a NAF. -/
def Goal.groundRun : Goal Variable Literal Symbol → Bool
  | .call _ _ | .naf _ _ => true
  | _ => false

/-- The atom of a call or a NAF. -/
def Goal.atom? : Goal Variable Literal Symbol → Option (Symbol × List (Term Variable Literal Symbol))
  | .call predicate args | .naf predicate args => some (predicate, args)
  | _ => none

attribute [local instance] Machine.termEq in
/-- The ground acyclic case, S07's class: ground rules whose bodies are calls
and NAF, no denial and no derived rule, no opened predicate, a ground query of
calls and NAF with no condition and no answer name, and the program's atoms
ranked: S07's topological rank (`GroundSearch.topoRank`) lowers every call of
every rule. It does exactly when some rank does (`topoRank_decreases`): S07
ranks atoms, not predicates. -/
def ground (query : Query Variable Literal Symbol) : Bool :=
  let atoms := (program.rules.map fun rule => (rule.head, rule.args)) ++
    program.rules.flatMap fun rule => rule.body.filterMap Goal.atom?
  let edges := program.rules.flatMap fun rule => (rule.body.filterMap Goal.atom?).map ((rule.head, rule.args), ·)
  let rank := GroundSearch.topoRank edges atoms
  program.rules.all (fun rule => rule.names.isEmpty && rule.body.all Goal.groundRun) &&
    program.denials.isEmpty && program.derived.isEmpty && query.conditions.isEmpty && query.answers.isEmpty &&
    (bodyNames query.goals).isEmpty && query.goals.all Goal.groundRun &&
    program.predicates.all (fun predicate => predicate.kind != .opened) &&
    edges.all fun edge => decide (GroundSearch.rankOf rank edge.2 < GroundSearch.rankOf rank edge.1)

/-! ## Rigid parameters: the split -/

attribute [local instance] Machine.termEq in
/-- The members a parameter takes: those of every finite guard among the
conditions that guards it. -/
def splitChoices (query : Query Variable Literal Symbol) (name : Variable) : List (Term Variable Literal Symbol) :=
  (query.conditions.flatMap fun
    | .guard symbol (.var other) =>
        if program.kindAt .guard symbol 1 && program.finite symbol && other == name then (program.members symbol).getD [] else []
    | _ => []).eraseDups

/-- Every assignment of members to the names. -/
def assignments (choices : Variable → List (Term Variable Literal Symbol)) :
    List Variable → List (Variable → Term Variable Literal Symbol)
  | [] => [fun name => .var name]
  | name :: rest => (choices name).flatMap fun value =>
      (assignments choices rest).map fun values other => if other = name then value else values other

/-- The split's assignments of the rigid parameters. -/
def splitValues (query : Query Variable Literal Symbol) : List (Variable → Term Variable Literal Symbol) :=
  assignments (program.splitChoices query) query.parameters

end Program

/-! ## Profiles -/

/-- An IR program's profile for a query: the ground acyclic case, the
finiteness evidence, a well-formed program without it with the reasons, or
Undecided with the checker's blockers. P0 ⊂ P1 ⊂ P2 are evidence classes of
one IR and one evaluator: P0 needs every note P1 needs, and none. -/
inductive Profile (Variable Literal Symbol : Type) where
  | p0
  | p1
  | p2 (notes : List (Program.Note Variable Literal Symbol))
  | undecided (blockers : List (Blocker Variable Literal Symbol))

/-- P0 or P1. -/
def Profile.decides : Profile Variable Literal Symbol → Bool
  | .p0 | .p1 => true
  | _ => false

/-- The profiles of a split's instances combined: P1 when every instance is
P0 or P1; Undecided with every instance's blockers when one is Undecided; P2
with every instance's notes otherwise. -/
def Profile.combine (profiles : List (Profile Variable Literal Symbol)) : Profile Variable Literal Symbol :=
  if profiles.all Profile.decides then .p1
  else
    let blockers := profiles.flatMap fun | .undecided blockers => blockers | _ => []
    if blockers.isEmpty then .p2 (profiles.flatMap fun | .p2 notes => notes | _ => []) else .undecided blockers

namespace Program

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] (program : Program Variable Literal Symbol)

/-- The profile of a closed query: the checker's blockers first, then the
notes, then the ground acyclic case. A query with a rigid parameter left is
P2. -/
def classifyClosed (query : Query Variable Literal Symbol) : Profile Variable Literal Symbol :=
  match program.check query with
  | [] =>
      if query.parameters.isEmpty then
        match program.notes query with
        | [] => if program.ground query then .p0 else .p1
        | notes => .p2 notes
      else .p2 (query.parameters.map fun name => ⟨.goal, [], .var name, .parameter⟩)
  | blockers => .undecided blockers

/-- The profile, before anything runs. A closed query is classified on its
own; a query with rigid parameters is P1 when each of them is split by a
finite guard and every instance of the split is P0 or P1 (decided with the
user, 2026-11-18). Its notes are read once, on the query with its parameters
bound, the unsplit parameters among them: an instance reaches the same
vertices, so a note the query has its instances have, and a split with no
instance is P1 only without one. -/
def classify (query : Query Variable Literal Symbol) : Profile Variable Literal Symbol :=
  if query.parameters.isEmpty then program.classifyClosed query
  else
    match program.check query with
    | [] =>
        match program.notes query with
        | [] => Profile.combine ((program.splitValues query).map fun values => program.classifyClosed (query.instantiate values))
        | notes => .p2 notes
    | blockers => .undecided blockers

/-! ## What a profile gives -/

theorem classifyClosed_decides {query : Query Variable Literal Symbol}
    (decided : (program.classifyClosed query).decides = true) :
    program.check query = [] ∧ query.parameters = [] ∧ program.notes query = [] := by
  unfold classifyClosed at decided
  repeat' split at decided
  all_goals simp_all [Profile.decides]

theorem classifyClosed_p0 {query : Query Variable Literal Symbol} (classified : program.classifyClosed query = .p0) :
    program.check query = [] ∧ query.parameters = [] ∧ program.notes query = [] ∧ program.ground query = true := by
  unfold classifyClosed at classified
  repeat' split at classified
  all_goals simp_all

theorem classify_closed {query : Query Variable Literal Symbol} (none : query.parameters = []) :
    program.classify query = program.classifyClosed query := by
  simp [classify, none]

theorem classify_undecided {query : Query Variable Literal Symbol} {blockers : List (Blocker Variable Literal Symbol)}
    (none : query.parameters = []) (classified : program.classify query = .undecided blockers) :
    blockers = program.check query ∧ blockers ≠ [] := by
  rw [program.classify_closed none] at classified
  unfold classifyClosed at classified
  repeat' split at classified
  all_goals simp_all

/-- **What P1 or P0 gives a query with rigid parameters**: no note, each
parameter split, and every instance of the split P0 or P1. -/
theorem classify_split {query : Query Variable Literal Symbol} (some : query.parameters ≠ [])
    (decided : (program.classify query).decides = true) :
    program.check query = [] ∧ program.notes query = [] ∧ program.unsplit query = [] ∧
      ∀ values ∈ program.splitValues query, (program.classifyClosed (query.instantiate values)).decides = true := by
  have notEmpty : query.parameters.isEmpty = false := by
    cases parameters : query.parameters with
    | nil => exact absurd parameters some
    | cons _ _ => rfl
  unfold classify at decided
  simp only [notEmpty, Bool.false_eq_true, ite_false] at decided
  cases clean : program.check query with
  | cons _ _ => rw [clean] at decided; simp [Profile.decides] at decided
  | nil =>
      rw [clean] at decided
      cases notesEq : program.notes query with
      | cons _ _ => rw [notesEq] at decided; simp [Profile.decides] at decided
      | nil =>
          rw [notesEq] at decided
          have unsplitNil : program.unsplit query = [] := by
            have parts := notesEq
            rw [notes_eq] at parts
            unfold notesWith at parts
            simp only [List.append_eq_nil_iff] at parts
            exact parts.2
          refine ⟨rfl, rfl, unsplitNil, fun values member => ?_⟩
          unfold Profile.combine at decided
          by_cases all : ((program.splitValues query).map fun values =>
              program.classifyClosed (query.instantiate values)).all Profile.decides = true
          · exact List.all_eq_true.mp all _ (List.mem_map.mpr ⟨values, member, rfl⟩)
          · simp only [all, Bool.false_eq_true, ite_false] at decided
            split at decided <;> simp [Profile.decides] at decided

end Program

end AnthillModKbSpec.IR
