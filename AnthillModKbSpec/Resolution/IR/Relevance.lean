import AnthillModKbSpec.Resolution.IR.Herbrand
import AnthillModKbSpec.Resolution.Tabled.Calls

/-! # The relevant program of a query (S27)

A query's **relevant program** is the set of ground rule instances its calls
can use, both for the answers a call derives and for the answers it may have
in some model of the completion ([decision IR](../../../docs/decision-ir.md)).
It is read per call pattern (`IR/Evidence`):

- **Possible answers** (`Ans`): an atom is a possible answer of a vertex when
  an instance of one of the vertex's rules has it as its head and *passes*
  (`Passes`): its fixed literals (equations, disequalities, guards,
  primitives) are true, and every call that leaves an output free has a
  possible answer of its own vertex there. Calls with every argument bound,
  NAF, and marker atoms are not pruned: their atoms are relevant, whatever
  their truth.
- **Relevant calls** (`Relevant`): the calls of the query's passing
  instances, and of every passing instance of a relevant atom.
- **Relevant atoms and instances** (`Entry`, `Instance`): an atom is relevant
  at a vertex when the vertex is called with its bound arguments and, if the
  vertex leaves an output free, it is a possible answer there.

The denials' passing instances are relevant too (decided with the user,
2026-11-18): their calls are roots of the relevant calls and of the evidence
graph. Relevance is read on closed queries; a query with rigid parameters is
read through its split's instances.

With the finiteness evidence, the pruning is sound: in every interpretation
supported by its rules (a post-fixpoint), every atom a free vertex may answer
is a possible answer (`ans_complete`), by induction on the call's rank (its
vertex's level, then the size of its bound arguments). So the relevant atoms
form a **splitting set** of the completion: a key fixpoint satisfies the
relevant program's completion at every relevant atom
(`relevant_of_fixpoint`), and an interpretation that satisfies it there, the
completion at every other closed atom, and every denial, is a key fixpoint
(`fixpoint_of_relevant`); the denials hold exactly when every passing denial
instance has a false body (`denied_iff`). A model of the relevant program's
completion is a restriction of a model of the whole only when the rest of the
KB extends it: a rule outside it can still rule it out
(`r(a) :- p(a), naf r(a)` forces `p(a)` false), which S28 checks before
answering Unknown (decided with the user, 2026-11-18). -/

namespace AnthillModKbSpec.IR

open Semantics Completion Tabled Answers

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  [FreshNames Variable]

/-! ## Ground instances -/

/-- A substitution gives every name of the list a ground data term over the
declared constructors. -/
def GroundOn (constructors : List (Constructor Literal Symbol)) (σ : Variable → Term Variable Literal Symbol)
    (names : List Variable) : Prop :=
  ∀ name ∈ names, groundIn constructors (σ name) = true

/-- An atom over keys. -/
def keyArgs (atom : GAtom Variable Literal Symbol) : List (Key Literal Symbol) := atom.2.map Open.dataKey

namespace Program

variable (program : Program Variable Literal Symbol)

/-- The truth of a fixed literal under a substitution: an equation, a
disequality, a guard, a primitive. Calls, NAF, and markers are not fixed. -/
def fixedAt (σ : Variable → Term Variable Literal Symbol) : Goal Variable Literal Symbol → Prop
  | .equal left right => subst σ left = subst σ right
  | .differ left right => subst σ left ≠ subst σ right
  | .guard symbol arg => program.guardHolds symbol (subst σ arg) = true
  | .primitive symbol inputs output => program.evaluate symbol (inputs.map (subst σ)) = some (subst σ output)
  | _ => True

/-! ## Possible answers -/

mutual
/-- The possible answers of a call pattern: the heads of the passing
instances of the vertex's rules. -/
inductive Ans (program : Program Variable Literal Symbol) : Vertex Symbol → GAtom Variable Literal Symbol → Prop
  | rule {vertex : Vertex Symbol} {index : Nat} {rule : Rule Variable Literal Symbol}
      {σ : Variable → Term Variable Literal Symbol} :
      (index, rule) ∈ program.rulesAt vertex → GroundOn program.constructors σ rule.names →
      Passes program σ (startNames vertex.2 rule.args) rule.body →
      Ans program vertex (rule.head, rule.args.map (subst σ))

/-- An instance passes a body read from the names bound before it: its fixed
literals are true, and every call leaving an output free has a possible answer
of its vertex at the instance. -/
inductive Passes (program : Program Variable Literal Symbol) :
    (Variable → Term Variable Literal Symbol) → List Variable → List (Goal Variable Literal Symbol) → Prop
  | nil {σ : Variable → Term Variable Literal Symbol} {bound : List Variable} : Passes program σ bound []
  | free {σ : Variable → Term Variable Literal Symbol} {bound : List Variable} {goal : Goal Variable Literal Symbol}
      {rest : List (Goal Variable Literal Symbol)} {vertex : Vertex Symbol} :
      goal.vertex? bound = some vertex → vertex.2.free = true → Ans program vertex (vertex.1, goal.args.map (subst σ)) →
      Passes program σ (after bound goal) rest → Passes program σ bound (goal :: rest)
  | fixed {σ : Variable → Term Variable Literal Symbol} {bound : List Variable} {goal : Goal Variable Literal Symbol}
      {rest : List (Goal Variable Literal Symbol)} :
      (∀ vertex, goal.vertex? bound = some vertex → vertex.2.free = false) → program.fixedAt σ goal →
      Passes program σ (after bound goal) rest → Passes program σ bound (goal :: rest)
end

/-! ## Relevant calls, atoms, and instances -/

/-- The query's passing instances: ground on its names, its goals passing
from its rigid parameters. -/
def QueryPasses (query : Query Variable Literal Symbol) (σ : Variable → Term Variable Literal Symbol) : Prop :=
  GroundOn program.constructors σ (bodyNames query.goals) ∧ Passes program σ query.parameters query.goals

/-- The relevant calls of a query, each a vertex with its bound arguments'
values: the calls of the query's passing instances and of its conditions, the
calls of the denials' passing instances (decided with the user, 2026-11-18:
denials join the relevant program), and the calls of every passing instance
of a relevant atom. A query with rigid parameters is read through its split's
instances, each closed (`IR/Parameters`). -/
inductive Relevant (program : Program Variable Literal Symbol) (query : Query Variable Literal Symbol) :
    Vertex Symbol → List (Term Variable Literal Symbol) → Prop
  | goal {σ : Variable → Term Variable Literal Symbol} {position : Nat} {goal : Goal Variable Literal Symbol}
      {bound : List Variable} {vertex : Vertex Symbol} :
      program.QueryPasses query σ → (position, goal, bound, vertex) ∈ bodyCalls 0 query.parameters query.goals →
      Relevant program query vertex (boundArgs vertex.2 (goal.args.map (subst σ)))
  | condition {goal : Goal Variable Literal Symbol} {vertex : Vertex Symbol} :
      goal ∈ query.conditions → goal.vertex? query.parameters = some vertex →
      Relevant program query vertex (boundArgs vertex.2 goal.args)
  | denial {body : List (Goal Variable Literal Symbol)} {σ : Variable → Term Variable Literal Symbol} {position : Nat}
      {goal : Goal Variable Literal Symbol} {bound : List Variable} {vertex : Vertex Symbol} :
      body ∈ program.denials → GroundOn program.constructors σ (bodyNames body) → Passes program σ [] body →
      (position, goal, bound, vertex) ∈ bodyCalls 0 [] body →
      Relevant program query vertex (boundArgs vertex.2 (goal.args.map (subst σ)))
  | rule {vertex : Vertex Symbol} {atom : GAtom Variable Literal Symbol} {index : Nat} {rule : Rule Variable Literal Symbol}
      {σ : Variable → Term Variable Literal Symbol} {position : Nat} {goal : Goal Variable Literal Symbol}
      {bound : List Variable} {callee : Vertex Symbol} :
      Relevant program query vertex (boundArgs vertex.2 atom.2) → atom.1 = vertex.1 →
      (vertex.2.free = false ∨ Ans program vertex atom) →
      (index, rule) ∈ program.rulesAt vertex → GroundOn program.constructors σ rule.names →
      rule.args.map (subst σ) = atom.2 → Passes program σ (startNames vertex.2 rule.args) rule.body →
      (position, goal, bound, callee) ∈ bodyCalls 0 (startNames vertex.2 rule.args) rule.body →
      Relevant program query callee (boundArgs callee.2 (goal.args.map (subst σ)))

/-- A relevant atom at a vertex: the vertex is called with the atom's bound
arguments, and, if it leaves an output free, the atom is a possible answer. -/
def Entry (query : Query Variable Literal Symbol) (vertex : Vertex Symbol) (atom : GAtom Variable Literal Symbol) : Prop :=
  program.Relevant query vertex (boundArgs vertex.2 atom.2) ∧ atom.1 = vertex.1 ∧ atom.2.length = vertex.2.length ∧
    (∀ term ∈ atom.2, groundIn program.constructors term = true) ∧ (vertex.2.free = false ∨ program.Ans vertex atom)

/-- A relevant atom: relevant at some vertex. -/
def RelevantAtom (query : Query Variable Literal Symbol) (atom : GAtom Variable Literal Symbol) : Prop :=
  ∃ vertex, program.Entry query vertex atom

/-- A relevant instance: a passing instance of a rule of a vertex, at an atom
relevant there. The relevant program is the set of them. -/
def Instance (query : Query Variable Literal Symbol) (atom : GAtom Variable Literal Symbol) (rule : Rule Variable Literal Symbol)
    (σ : Variable → Term Variable Literal Symbol) : Prop :=
  ∃ vertex index, program.Entry query vertex atom ∧ (index, rule) ∈ program.rulesAt vertex ∧
    GroundOn program.constructors σ rule.names ∧ rule.args.map (subst σ) = atom.2 ∧
    Passes program σ (startNames vertex.2 rule.args) rule.body

/-! ## Sizes under substitutions -/

section Sizes

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem sizeAll_eq_sum : ∀ args : List (Term Variable Literal Symbol), sizeAll args = (args.map size).sum
  | [] => rfl
  | arg :: rest => by rw [sizeAll, sizeAll_eq_sum rest]; simp

omit [FreshNames Variable] in
mutual
/-- A subterm's substitution is no larger than the term's. -/
theorem size_subst_occurs {σ : Variable → Term Variable Literal Symbol} {part : Term Variable Literal Symbol} :
    ∀ term : Term Variable Literal Symbol, occurs part term = true → size (subst σ part) ≤ size (subst σ term)
  | .app symbol args, inside => by
      simp only [occurs, Bool.or_eq_true, decide_eq_true_eq] at inside
      rcases inside with same | deeper
      · subst same; exact Nat.le_refl _
      · have := size_subst_occursIn (σ := σ) args deeper
        simp only [subst, size]
        rw [sizeAll_eq_sum (substAll σ args)] at *
        omega
  | .var name, inside | .lit name, inside | .truth, inside | .falsity, inside => by
      simp only [occurs, decide_eq_true_eq] at inside; subst inside; exact Nat.le_refl _
  | .conj _ _, inside | .disj _ _, inside | .imp _ _, inside | .defaultNeg _, inside | .forallVar _ _, inside
  | .existsVar _ _, inside | .dictionaryCall _ _ _ _, inside | .equal _ _, inside => by
      simp only [occurs, decide_eq_true_eq] at inside; subst inside; exact Nat.le_refl _

/-- A subterm of an argument's substitution is smaller than the application's. -/
theorem size_subst_occursIn {σ : Variable → Term Variable Literal Symbol} {part : Term Variable Literal Symbol} :
    ∀ args : List (Term Variable Literal Symbol), occursIn part args = true → size (subst σ part) ≤ sizeAll (substAll σ args)
  | [], inside => by simp [occursIn] at inside
  | arg :: rest, inside => by
      simp only [occursIn, Bool.or_eq_true] at inside
      simp only [substAll, sizeAll]
      rcases inside with here | there
      · have := size_subst_occurs (σ := σ) arg here; omega
      · have := size_subst_occursIn (σ := σ) rest there; omega
end

omit [FreshNames Variable] in
theorem size_subst_inside {σ : Variable → Term Variable Literal Symbol} {part term : Term Variable Literal Symbol}
    (inside_ : inside part term = true) : size (subst σ part) < size (subst σ term) := by
  cases term with
  | app symbol args =>
      simp only [inside] at inside_
      have := size_subst_occursIn (σ := σ) args inside_
      simp only [subst, size]
      omega
  | _ => simp [inside] at inside_

omit [FreshNames Variable] in
/-- Inputs each a subterm of the head input at their position have a total
size no larger, under every substitution. -/
theorem occurs_sizeAll {σ : Variable → Term Variable Literal Symbol} :
    ∀ {inputs heads : List (Term Variable Literal Symbol)}, inputs.length ≤ heads.length →
      (∀ pair ∈ inputs.zip heads, occurs pair.1 pair.2 = true) → sizeAll (inputs.map (subst σ)) ≤ sizeAll (heads.map (subst σ))
  | [], _, _, _ => by simp [sizeAll]
  | _ :: _, [], lengths, _ => by simp at lengths
  | input :: inputs, head :: heads, lengths, each => by
      simp only [List.map_cons, sizeAll]
      have first : size (subst σ input) ≤ size (subst σ head) :=
        size_subst_occurs head (each (input, head) (by rw [List.zip_cons_cons]; exact List.mem_cons_self))
      have rest := occurs_sizeAll (σ := σ) (inputs := inputs) (heads := heads) (by simp at lengths; omega)
        fun pair member => each pair (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ member)
      omega

omit [FreshNames Variable] in
/-- Inputs that decrease against the head's (each a subterm of the head input
at its position, one strictly) have a smaller total size under every
substitution. -/
theorem decreasing_size {σ : Variable → Term Variable Literal Symbol} :
    ∀ {inputs heads : List (Term Variable Literal Symbol)}, inputs.length ≤ heads.length →
      (∀ pair ∈ inputs.zip heads, occurs pair.1 pair.2 = true) → (∃ pair ∈ inputs.zip heads, inside pair.1 pair.2 = true) →
        sizeAll (inputs.map (subst σ)) < sizeAll (heads.map (subst σ))
  | [], _, _, _, strict => by obtain ⟨_, member, _⟩ := strict; cases member
  | _ :: _, [], lengths, _, _ => by simp at lengths
  | input :: inputs, head :: heads, lengths, each, strict => by
      simp only [List.map_cons, sizeAll]
      have restLengths : inputs.length ≤ heads.length := by simp at lengths; omega
      have restEach : ∀ pair ∈ inputs.zip heads, occurs pair.1 pair.2 = true :=
        fun pair member => each pair (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ member)
      have first : size (subst σ input) ≤ size (subst σ head) :=
        size_subst_occurs head (each (input, head) (by rw [List.zip_cons_cons]; exact List.mem_cons_self))
      obtain ⟨pair, member, strictPair⟩ := strict
      rw [List.zip_cons_cons] at member
      rcases List.mem_cons.mp member with same | later
      · subst same
        have strictFirst : size (subst σ input) < size (subst σ head) := size_subst_inside strictPair
        have rest := occurs_sizeAll (σ := σ) restLengths restEach
        omega
      · have rest := decreasing_size (σ := σ) restLengths restEach ⟨pair, later, strictPair⟩
        omega

end Sizes

/-! ## The truth of instances in key models -/

section KeyTruth

variable {program}

omit [FreshNames Variable] in
/-- A closed atom at an instance holds in a key model exactly when the
interpretation makes its keys true. -/
theorem key_closed_iff (wellFormed : program.WellFormed) {markers interp : Interp Literal Symbol} {symbol : Symbol}
    {args : List (Term Variable Literal Symbol)} (closed : program.closedAt symbol args.length = true)
    (data : ∀ arg ∈ args, dataIn program.constructors arg = true) (σ : Variable → Term Variable Literal Symbol) :
    (program.keyModel markers interp).Satisfies (fun name => Open.dataKey (σ name)) (.app symbol args) ↔
      interp symbol ((args.map (subst σ)).map Open.dataKey) := by
  have keysEq : args.map ((program.keyModel markers interp).eval fun name => Open.dataKey (σ name)) =
      (args.map (subst σ)).map Open.dataKey := by
    rw [keys_evalAll_subst _ σ args (dataInAll_of data), List.map_map]
  obtain ⟨found, foundEq, _, _⟩ := closedAt_declared closed
  simp only [Model.Satisfies, Model.eval]
  rw [keysEq]
  show resolveKey program.hoApply _ symbol _ ↔ _
  rw [resolveKey_ordinary _ (ordinary_of_declared wellFormed.reserved foundEq)]
  exact join_closed (by rw [List.length_map, List.length_map]; exact closedAt_mem closed)

omit [FreshNames Variable] in
/-- A fixed literal at a ground instance holds in a key model exactly when it
is true at the instance. -/
theorem key_fixed_iff (wellFormed : program.WellFormed) {markers interp : Interp Literal Symbol}
    {goal : Goal Variable Literal Symbol} (declared : program.declares goal = true) (data : program.data goal = true)
    {σ : Variable → Term Variable Literal Symbol} (ground : GroundOn program.constructors σ goal.names)
    (fixed : goal.vertex? [] = none) (notMarker : ∀ symbol args, goal ≠ .marker symbol args) :
    (program.keyModel markers interp).Satisfies (fun name => Open.dataKey (σ name)) goal.toTerm ↔ program.fixedAt σ goal := by
  have allData : ∀ arg ∈ goal.args, dataIn program.constructors arg = true := List.all_eq_true.mp data
  cases goal with
  | call _ _ => simp [Goal.vertex?] at fixed
  | naf _ _ => simp [Goal.vertex?] at fixed
  | marker symbol args => exact absurd rfl (notMarker symbol args)
  | equal left right =>
      have leftData := allData left (by simp [Goal.args])
      have rightData := allData right (by simp [Goal.args])
      have leftGround := groundIn_subst left leftData fun name occurs =>
        ground name (by simp [Goal.names, Goal.args, namesOf, occurs])
      have rightGround := groundIn_subst right rightData fun name occurs =>
        ground name (by simp [Goal.names, Goal.args, namesOf, occurs])
      simp only [Goal.toTerm, fixedAt]
      rw [Model.satisfies_equal, keys_eval_subst _ σ left leftData, keys_eval_subst _ σ right rightData]
      exact ⟨fun same => dataKey_injective program.hoApply leftGround rightGround same, fun same => by rw [same]⟩
  | differ left right =>
      have leftData := allData left (by simp [Goal.args])
      have rightData := allData right (by simp [Goal.args])
      have leftGround := groundIn_subst left leftData fun name occurs =>
        ground name (by simp [Goal.names, Goal.args, namesOf, occurs])
      have rightGround := groundIn_subst right rightData fun name occurs =>
        ground name (by simp [Goal.names, Goal.args, namesOf, occurs])
      simp only [Goal.toTerm, fixedAt]
      rw [sat_neg _ _ (Model.keys_complement _), Model.satisfies_equal, keys_eval_subst _ σ left leftData,
        keys_eval_subst _ σ right rightData]
      exact ⟨fun different same => different (by rw [same]),
        fun different same => different (dataKey_injective program.hoApply leftGround rightGround same)⟩
  | guard symbol arg =>
      obtain ⟨found, foundEq, kind, _⟩ := kindAt_declared declared
      have argData := allData arg (by simp [Goal.args])
      have argGround := groundIn_subst arg argData fun name occurs =>
        ground name (by simpa [Goal.names, Goal.args, namesOf] using occurs)
      simp only [Goal.toTerm, fixedAt, Model.Satisfies, Model.eval, List.map_cons, List.map_nil]
      change (program.keyModel markers interp).holds ((program.keyModel markers interp).application symbol _) ↔ _
      rw [program.keyModel_base wellFormed foundEq (by simp [Predicate.closed, kind]), keys_eval_subst _ σ arg argData]
      simp only [base, foundEq, kind]
      constructor
      · rintro ⟨term, termGround, holds, same⟩
        rw [dataKey_injective program.hoApply argGround termGround (by simpa using same)]; exact holds
      · intro holds
        exact ⟨_, argGround, holds, rfl⟩
  | primitive symbol inputs output =>
      obtain ⟨found, foundEq, kind, _⟩ := kindAt_declared declared
      have argsData : ∀ arg ∈ inputs ++ [output], dataIn program.constructors arg = true := fun arg member => allData arg member
      have argsGround := groundIn_substs argsData fun name occurs => ground name occurs
      have outputGround : groundIn program.constructors (subst σ output) = true :=
        argsGround _ (List.mem_map.mpr ⟨output, by simp, rfl⟩)
      have inputsGround : ∀ input ∈ inputs.map (subst σ), groundIn program.constructors input = true :=
        fun input member => argsGround input (by
          obtain ⟨arg, argMember, rfl⟩ := List.mem_map.mp member
          exact List.mem_map.mpr ⟨arg, List.mem_append_left _ argMember, rfl⟩)
      simp only [Goal.toTerm, fixedAt, Model.Satisfies, Model.eval]
      change (program.keyModel markers interp).holds ((program.keyModel markers interp).application symbol _) ↔ _
      rw [program.keyModel_base wellFormed foundEq (by simp [Predicate.closed, kind]),
        keys_evalAll_subst _ σ _ (dataInAll_of argsData)]
      simp only [base, foundEq, kind]
      have groundAll : ∀ {firsts : List (Term Variable Literal Symbol)} {last : Term Variable Literal Symbol},
          (∀ term ∈ firsts, groundIn program.constructors term = true) → groundIn program.constructors last = true →
            ∀ term ∈ firsts ++ [last], groundIn program.constructors term = true := by
        intro firsts last firstsGround lastGround term member
        rcases List.mem_append.mp member with inside | inside
        · exact firstsGround term inside
        · rcases List.mem_singleton.mp inside with rfl; exact lastGround
      constructor
      · rintro ⟨firsts, last, firstsGround, lastGround, evaluated, same⟩
        rw [← List.map_map] at same
        have equal := dataKeys_injective_of program.hoApply argsGround (groundAll firstsGround lastGround) same
        rw [List.map_append, List.map_singleton] at equal
        obtain ⟨firstsEq, lastEq⟩ := List.append_inj' equal (by simp)
        simp only [List.cons.injEq, and_true] at lastEq
        rw [firstsEq, lastEq]; exact evaluated
      · intro evaluated
        refine ⟨_, _, inputsGround, outputGround, evaluated, ?_⟩
        simp [List.map_append, List.map_map]

end KeyTruth

/-! ## Possible answers are complete -/

/-- An interpretation supported by its rules: every closed atom it makes
true has a rule instance whose body holds (a post-fixpoint). -/
def Supported (markers interp : Interp Literal Symbol) : Prop :=
  ∀ symbol keys, (symbol, keys.length) ∈ program.signature.predicates → interp symbol keys →
    consequence program.hoApply program.signature program.clauses (program.base markers) interp symbol keys

section Completeness

variable {program}

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem mem_rulesAt {vertex : Vertex Symbol} {entry : Nat × Rule Variable Literal Symbol} :
    entry ∈ program.rulesAt vertex ↔ entry ∈ program.rulesOf vertex.1 ∧ entry.2.args.length = vertex.2.length := by
  simp [rulesAt]

omit [DecidableEq Literal] [FreshNames Variable] in
theorem mem_callsAt {vertex : Vertex Symbol} {index : Nat} {rule : Rule Variable Literal Symbol}
    {call : Nat × Goal Variable Literal Symbol × List Variable × Vertex Symbol} (ruleMember : (index, rule) ∈ program.rulesAt vertex)
    (callMember : call ∈ bodyCalls 0 (startNames vertex.2 rule.args) rule.body) : (index, rule, call) ∈ program.callsAt vertex :=
  List.mem_flatMap.mpr ⟨(index, rule), ruleMember, List.mem_map.mpr ⟨call, callMember, rfl⟩⟩

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem mem_bodyCalls_head {position : Nat} {bound : List Variable} {goal : Goal Variable Literal Symbol}
    {rest : List (Goal Variable Literal Symbol)} {vertex : Vertex Symbol} (found : goal.vertex? bound = some vertex) :
    (position, goal, bound, vertex) ∈ bodyCalls position bound (goal :: rest) := by
  simp [bodyCalls, found]

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem mem_bodyCalls_tail {position : Nat} {bound : List Variable} {goal : Goal Variable Literal Symbol}
    {rest : List (Goal Variable Literal Symbol)} {call : Nat × Goal Variable Literal Symbol × List Variable × Vertex Symbol}
    (member : call ∈ bodyCalls (position + 1) (after bound goal) rest) : call ∈ bodyCalls position bound (goal :: rest) := by
  simp only [bodyCalls]
  exact List.mem_append_right _ member

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem full_not_free (arity : Nat) : (full arity).free = false := by
  simp [full, Pattern.free]

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem length_patternOf (bound : List Variable) (args : List (Term Variable Literal Symbol)) :
    (patternOf bound args).length = args.length := by
  simp [patternOf]

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem boundArgs_map {α β : Type} (f : α → β) : ∀ (pattern : Pattern) (args : List α),
    boundArgs pattern (args.map f) = (boundArgs pattern args).map f
  | [], args => by cases args <;> simp [boundArgs]
  | _ :: _, [] => by simp [boundArgs]
  | bound :: pattern, arg :: args => by
      have rest := boundArgs_map f pattern args
      simp only [boundArgs] at rest ⊢
      cases bound <;> simp [rest]

omit [FreshNames Variable] in
/-- **The finiteness evidence**, what no note gives a closed query: every call
that leaves an output free,
from a vertex that leaves one free, lowers the rank; every call at its
caller's level keeps to the data terms (no `growingCall`); every name is
guarded; every rigid parameter is split. -/
structure Evidence (program : Program Variable Literal Symbol) (query : Query Variable Literal Symbol) : Prop where
  lowering : ∀ vertex ∈ program.vertices query, vertex.2.free = true → ∀ call ∈ program.callsAt vertex,
    call.2.2.2.2.2.2.free = true → lowersWith (program.levels query) vertex call.2.1 call.2.2.2.1 call.2.2.2.2.2 = true
  bounded : program.growingIn (program.vertices query) (program.levels query) (program.dataInfo query) = []
  guarded : program.unguarded query = []
  split : program.unsplit query = []

omit [FreshNames Variable] in
theorem evidence_of_notes {query : Query Variable Literal Symbol} (evidence : program.notes query = []) :
    program.Evidence query := by
  rw [notes_eq] at evidence
  unfold notesWith at evidence
  simp only [List.append_eq_nil_iff] at evidence
  obtain ⟨⟨⟨growingPart, freePart⟩, unguardedPart⟩, unsplitPart⟩ := evidence
  refine ⟨?_, growingPart, unguardedPart, unsplitPart⟩
  · intro vertex member free call callMember calleeFree
    simp only [freeOutputsIn, List.flatMap_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff, List.mem_filter] at freePart
    have := freePart vertex ⟨member, free⟩ call callMember
    simp only [calleeFree, Bool.true_and, Bool.not_eq_true'] at this
    cases lowersEq : lowersWith (program.levels query) vertex call.2.1 call.2.2.2.1 call.2.2.2.2.2
    · rw [lowersEq] at this; simp at this
    · rfl

omit [DecidableEq Literal] [FreshNames Variable] in
theorem successor_mem {query : Query Variable Literal Symbol} {vertex : Vertex Symbol}
    (member : vertex ∈ program.vertices query) {call : Nat × Rule Variable Literal Symbol × Nat × Goal Variable Literal Symbol ×
      List Variable × Vertex Symbol} (callMember : call ∈ program.callsAt vertex) :
    call.2.2.2.2.2 ∈ program.vertices query := by
  have closed := program.closed_vertices query
  unfold Program.closed Program.closedIn at closed
  have := List.all_eq_true.mp closed vertex member
  exact List.contains_iff_mem.mp (List.all_eq_true.mp this _ (List.mem_map.mpr ⟨call, callMember, rfl⟩))

omit [FreshNames Variable] in
/-- A decreasing call's bound arguments are smaller than the head's at every
ground instance. -/
theorem decreases_size {vertex callee : Vertex Symbol} {rule : Rule Variable Literal Symbol}
    {goal : Goal Variable Literal Symbol} (decreasing : decreases vertex rule goal callee = true)
    (σ : Variable → Term Variable Literal Symbol) :
    sizeAll ((boundArgs callee.2 goal.args).map (subst σ)) < sizeAll ((boundArgs vertex.2 rule.args).map (subst σ)) := by
  simp only [decreases, Frame.decreasing, frameAt, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at decreasing
  obtain ⟨⟨lengths, each⟩, strict⟩ := decreasing
  exact decreasing_size (of_decide_eq_true lengths) (fun pair member => (each pair member).1) strict

omit [FreshNames Variable] in
/-- **The rank step**: with the evidence, a call that leaves an output free,
made by a rule of a vertex that leaves one free, goes to a vertex of the graph
at a lower level, or at the same level with smaller bound values at every
instance. -/
theorem call_rank {query : Query Variable Literal Symbol} (parts : program.Evidence query) {vertex : Vertex Symbol}
    (member : vertex ∈ program.vertices query) (free : vertex.2.free = true) {index : Nat}
    {rule : Rule Variable Literal Symbol} (atVertex : (index, rule) ∈ program.rulesAt vertex)
    {call : Nat × Goal Variable Literal Symbol × List Variable × Vertex Symbol}
    (inCalls : call ∈ bodyCalls 0 (startNames vertex.2 rule.args) rule.body) (calleeFree : call.2.2.2.2.free = true)
    (σ : Variable → Term Variable Literal Symbol) :
    call.2.2.2 ∈ program.vertices query ∧
      (program.levels query call.2.2.2 < program.levels query vertex ∨
        program.levels query call.2.2.2 = program.levels query vertex ∧
          sizeAll ((boundArgs call.2.2.2.2 call.2.1.args).map (subst σ)) <
            sizeAll ((boundArgs vertex.2 rule.args).map (subst σ))) := by
  have inCallsAt := mem_callsAt atVertex inCalls
  refine ⟨successor_mem member inCallsAt, ?_⟩
  have lowered := parts.lowering vertex member free _ inCallsAt calleeFree
  have levelLe := program.levels_le member (List.mem_map.mpr ⟨_, inCallsAt, rfl⟩)
  simp only [lowersWith, Bool.or_eq_true, decide_eq_true_eq] at lowered
  rcases lowered with lower | decreasing
  · exact .inl lower
  · rcases Nat.lt_or_eq_of_le levelLe with lower | same
    · exact .inl lower
    · exact .inr ⟨same, decreases_size decreasing σ⟩

omit [FreshNames Variable] in
/-- A rule instance whose body holds in a key model passes, given possible
answers for the atoms of its calls that leave an output free. -/
theorem passes_of_holds (wellFormed : program.WellFormed) {markers interp : Interp Literal Symbol}
    {body : List (Goal Variable Literal Symbol)} (ok : ∀ goal ∈ body, program.declares goal = true ∧ program.data goal = true)
    {σ : Variable → Term Variable Literal Symbol}
    (groundBody : GroundOn program.constructors σ (bodyNames body)) (start : List Variable)
    (keyBody : (program.keyModel markers interp).Satisfies (fun name => Open.dataKey (σ name)) (bodyTerm body))
    (answer : ∀ position bound predicate args,
      (position, Goal.call predicate args, bound, (predicate, patternOf bound args)) ∈ bodyCalls 0 start body →
      (patternOf bound args).free = true → program.closedAt predicate args.length = true →
      (∀ term ∈ args.map (subst σ), groundIn program.constructors term = true) →
      interp predicate ((args.map (subst σ)).map Open.dataKey) →
      program.Ans (predicate, patternOf bound args) (predicate, args.map (subst σ))) :
    program.Passes σ start body := by
  suffices walk : ∀ (position : Nat) (bound : List Variable) (rest : List (Goal Variable Literal Symbol)),
      (∀ goal ∈ rest, goal ∈ body) → (∀ call ∈ bodyCalls position bound rest, call ∈ bodyCalls 0 start body) →
        program.Passes σ bound rest from
    walk 0 start body (fun _ inside => inside) (fun _ inside => inside)
  intro position bound rest
  induction rest generalizing position bound with
  | nil => intro _ _; exact .nil
  | cons goal rest ih =>
      intro inBody calls
      have goalMember := inBody goal List.mem_cons_self
      obtain ⟨declared, data⟩ := ok goal goalMember
      have goalHolds := satisfies_of_mem keyBody goalMember
      have goalGround : GroundOn program.constructors σ goal.names := fun name occurs =>
        groundBody name (List.mem_flatMap.mpr ⟨goal, goalMember, occurs⟩)
      have restPasses := ih (position + 1) (after bound goal) (fun other inside => inBody other (List.mem_cons_of_mem _ inside))
        (fun call inside => calls call (mem_bodyCalls_tail inside))
      cases goal with
      | call predicate args =>
          cases calleeFree : (patternOf bound args).free with
          | false =>
              exact .fixed (fun other otherEq => by
                simp only [Goal.vertex?, Option.some.injEq] at otherEq; rw [← otherEq]; exact calleeFree) trivial restPasses
          | true =>
              have closedCall : program.closedAt predicate args.length = true := declared
              have argsData : ∀ arg ∈ args, dataIn program.constructors arg = true := List.all_eq_true.mp data
              have atomHolds := (key_closed_iff wellFormed closedCall argsData σ).mp goalHolds
              have callMember := calls _ (mem_bodyCalls_head (rest := rest) (position := position)
                (show (Goal.call predicate args).vertex? bound = some (predicate, patternOf bound args) from rfl))
              exact .free rfl calleeFree (answer position bound predicate args callMember calleeFree closedCall
                (groundIn_substs argsData goalGround) atomHolds) restPasses
      | naf predicate args =>
          exact .fixed (fun other otherEq => by
            simp only [Goal.vertex?, Option.some.injEq] at otherEq; rw [← otherEq]; exact full_not_free _) trivial restPasses
      | marker _ _ => exact .fixed (fun other otherEq => by cases otherEq) trivial restPasses
      | equal _ _ | differ _ _ | guard _ _ | primitive _ _ _ =>
          exact .fixed (fun other otherEq => by cases otherEq)
            ((key_fixed_iff wellFormed declared data goalGround rfl (by intro _ _ same; cases same)).mp goalHolds) restPasses

omit [FreshNames Variable] in
/-- A rule instance making a closed atom true: the rule, at an index of the
program, and a ground substitution for its names under which the head is the
atom and the body holds. -/
theorem instance_of_consequence (wellFormed : program.WellFormed) (guarded : program.Guarded)
    {markers interp : Interp Literal Symbol} {symbol : Symbol} {values : List (Term Variable Literal Symbol)}
    (ground : ∀ term ∈ values, groundIn program.constructors term = true)
    (derived : consequence program.hoApply program.signature program.clauses (program.base markers) interp symbol
      (values.map Open.dataKey)) :
    ∃ (index : Nat) (rule : Rule Variable Literal Symbol) (σ : Variable → Term Variable Literal Symbol),
      program.rules[index]? = some rule ∧ rule.head = symbol ∧ rule.args.length = values.length ∧
      GroundOn program.constructors σ rule.names ∧ rule.args.map (subst σ) = values ∧
        (program.keyModel markers interp).Satisfies (fun name => Open.dataKey (σ name)) (bodyTerm rule.body) := by
  obtain ⟨_, args, body, inClauses, environment, argsEq, bodyHolds⟩ := derived
  obtain ⟨rule, ruleMember, headEq, rfl, rfl⟩ := rule_of_clause inClauses
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp ruleMember
  have ruleOk := wellFormed.rules rule ruleMember
  have bodyHolds' : (program.keyModel markers interp).Satisfies environment (bodyTerm rule.body) := bodyHolds
  have spec : ∀ name ∈ rule.names, groundIn program.constructors (program.groundsOfKeys environment name) = true ∧
      Open.dataKey (program.groundsOfKeys environment name) = environment name :=
    fun name inside => program.groundsOfKeys_spec (key_of_guarded wellFormed bodyHolds' (guarded.rules rule ruleMember name inside))
  refine ⟨index, rule, program.groundsOfKeys environment, found, headEq, ?_, fun name inside => (spec name inside).1, ?_, ?_⟩
  · have := congrArg List.length argsEq
    simpa using this
  · have keysEq : (rule.args.map (subst (program.groundsOfKeys environment))).map Open.dataKey = values.map Open.dataKey := by
      rw [List.map_map, ← keys_evalAll_subst (hoApplySymbol := program.hoApply)
        (join program.signature (program.base markers) interp) _ rule.args (dataInAll_of ruleOk.data), ← argsEq]
      refine List.map_congr_left fun arg argMember => ?_
      exact Model.eval_congr _ arg fun name occurs => (spec name (head_names_of_rule argMember occurs)).2
    exact dataKeys_injective_of program.hoApply (groundIn_substs ruleOk.data fun name occurs =>
      (spec name (List.mem_append_left _ occurs)).1) ground keysEq
  · unfold Model.Satisfies
    rw [Model.eval_congr _ (bodyTerm rule.body) (right := environment)
      fun name occurs => (spec name (List.mem_append_right _ (bodyNames_of_freeVars occurs))).2]
    exact bodyHolds'

omit [FreshNames Variable] in
/-- **Possible answers are complete.** With the finiteness evidence, in every
interpretation supported by its rules, every atom that a vertex leaving an
output free may answer, and the interpretation makes true, is a possible
answer: by induction on the call's rank, its vertex's level and then the size
of its bound arguments. -/
theorem ans_complete (wellFormed : program.WellFormed) (guarded : program.Guarded) {query : Query Variable Literal Symbol}
    (evidence : program.notes query = []) {markers interp : Interp Literal Symbol}
    (supported : program.Supported markers interp) :
    ∀ vertex ∈ program.vertices query, vertex.2.free = true → program.closedAt vertex.1 vertex.2.length = true →
      ∀ values : List (Term Variable Literal Symbol), values.length = vertex.2.length →
        (∀ term ∈ values, groundIn program.constructors term = true) → interp vertex.1 (values.map Open.dataKey) →
          program.Ans vertex (vertex.1, values) := by
  have parts := evidence_of_notes evidence
  suffices main : ∀ n m, ∀ vertex ∈ program.vertices query, vertex.2.free = true →
      program.closedAt vertex.1 vertex.2.length = true → ∀ values : List (Term Variable Literal Symbol),
        values.length = vertex.2.length → (∀ term ∈ values, groundIn program.constructors term = true) →
          interp vertex.1 (values.map Open.dataKey) → program.levels query vertex = n →
            sizeAll (boundArgs vertex.2 values) = m → program.Ans vertex (vertex.1, values) from
    fun vertex member free closed values lengths ground holds =>
      main _ _ vertex member free closed values lengths ground holds rfl rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihLevel =>
  intro m
  induction m using Nat.strongRecOn with
  | ind m ihSize =>
  intro vertex member free closedVertex values lengths ground holds levelEq sizeEq
  have closedKey : (vertex.1, (values.map Open.dataKey).length) ∈ program.signature.predicates := by
    rw [List.length_map, lengths]; exact closedAt_mem closedVertex
  obtain ⟨index, rule, σ, found, headEq, argLengths, groundRule, headValues, keyBody⟩ :=
    instance_of_consequence wellFormed guarded ground (supported _ _ closedKey holds)
  have ruleMember : rule ∈ program.rules := List.mem_of_getElem? found
  have atVertex : (index, rule) ∈ program.rulesAt vertex :=
    mem_rulesAt.mpr ⟨mem_rulesOf.mpr ⟨found, headEq⟩, by rw [argLengths, lengths]⟩
  have bodyPasses := passes_of_holds wellFormed (Scans.goals (wellFormed.rules rule ruleMember).scans)
    (fun name occurs => groundRule name (List.mem_append_right _ occurs)) (startNames vertex.2 rule.args) keyBody
    fun position bound predicate args callMember calleeFree closedCall argsGround atomHolds => by
      obtain ⟨calleeMember, rank⟩ := call_rank parts member free atVertex callMember calleeFree σ
      have closedCallee : program.closedAt (predicate, patternOf bound args).1 (predicate, patternOf bound args).2.length = true := by
        simp only [length_patternOf]; exact closedCall
      have lengthsCall : (args.map (subst σ)).length = (predicate, patternOf bound args).2.length := by
        simp [length_patternOf]
      generalize hLevel : program.levels query (predicate, patternOf bound args) = calleeLevel at rank
      generalize hVertexLevel : program.levels query vertex = vertexLevel at rank levelEq
      subst levelEq
      rcases rank with lower | ⟨same, smaller⟩
      · exact ihLevel calleeLevel lower _ _ calleeMember calleeFree closedCallee _ lengthsCall argsGround atomHolds hLevel rfl
      · subst same
        rw [← boundArgs_map, ← boundArgs_map, headValues] at smaller
        exact ihSize _ (by rw [← sizeEq]; exact smaller) _ calleeMember calleeFree closedCallee _ lengthsCall argsGround
          atomHolds hLevel rfl
  have answer := Ans.rule (program := program) atVertex groundRule bodyPasses
  rw [headEq, headValues] at answer
  exact answer

end Completeness

/-! ## The relevant program splits the completion -/

section Splitting

variable {program}

omit [DecidableEq Literal] [FreshNames Variable] in
theorem vertex?_closed {goal : Goal Variable Literal Symbol} (declared : program.declares goal = true) {bound : List Variable}
    {vertex : Vertex Symbol} (found : goal.vertex? bound = some vertex) : program.closedAt vertex.1 vertex.2.length = true := by
  cases goal with
  | call predicate args =>
      simp only [Goal.vertex?, Option.some.injEq] at found; subst found
      show program.closedAt predicate (patternOf bound args).length = true
      rw [length_patternOf]; exact declared
  | naf predicate args =>
      simp only [Goal.vertex?, Option.some.injEq] at found; subst found
      show program.closedAt predicate (full args.length).length = true
      rw [full, List.length_replicate]; exact declared
  | _ => simp [Goal.vertex?] at found

omit [DecidableEq Literal] [FreshNames Variable] in
theorem closeVertices_sup : ∀ (fuel : Nat) (found : List (Vertex Symbol)), ∀ vertex ∈ found, vertex ∈ program.closeVertices fuel found
  | 0, _, _, member => member
  | fuel + 1, found, vertex, member => by
      unfold closeVertices Tabled.untilStable
      split
      · exact member
      · exact closeVertices_sup fuel _ vertex (by simp [growVertices, List.mem_eraseDups, member])

omit [DecidableEq Literal] [FreshNames Variable] in
theorem queryVertices_mem {query : Query Variable Literal Symbol} {vertex : Vertex Symbol} (member : vertex ∈ queryVertices query) :
    vertex ∈ program.vertices query :=
  closeVertices_sup _ _ vertex (List.mem_eraseDups.mpr (List.mem_append_left _ member))

omit [DecidableEq Literal] [FreshNames Variable] in
theorem denialVertices_mem {query : Query Variable Literal Symbol} {vertex : Vertex Symbol}
    (member : vertex ∈ program.denialVertices) : vertex ∈ program.vertices query :=
  closeVertices_sup _ _ vertex (List.mem_eraseDups.mpr (List.mem_append_right _ member))

omit [FreshNames Variable] in
/-- A relevant call's vertex is in the graph, and names a closed predicate at
its arity. -/
theorem relevant_vertex (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol} (queryOk : QueryOk program query)
    {vertex : Vertex Symbol} {values : List (Term Variable Literal Symbol)}
    (relevant : program.Relevant query vertex values) :
    vertex ∈ program.vertices query ∧ program.closedAt vertex.1 vertex.2.length = true := by
  induction relevant with
  | goal _ inCalls =>
      obtain ⟨goalMember, found⟩ := mem_bodyCalls inCalls
      refine ⟨queryVertices_mem (List.mem_append_right _ (List.mem_map.mpr ⟨_, inCalls, rfl⟩)), ?_⟩
      exact vertex?_closed (Scans.goals queryOk.goals _ goalMember).1 found
  | @condition goal vertex member found =>
      refine ⟨queryVertices_mem (List.mem_append_left _ (List.mem_flatMap.mpr ⟨goal, member, ?_⟩)), ?_⟩
      · exact List.mem_map.mpr ⟨(0, goal, query.parameters, vertex), by simp [bodyCalls, found], rfl⟩
      · exact vertex?_closed (queryOk.conditions goal member).1 found
  | @denial body σ position goal bound vertex denialMember _ _ inCalls =>
      obtain ⟨goalMember, found⟩ := mem_bodyCalls inCalls
      refine ⟨denialVertices_mem (List.mem_flatMap.mpr ⟨body, denialMember, List.mem_map.mpr ⟨_, inCalls, rfl⟩⟩), ?_⟩
      exact vertex?_closed (Scans.goals (wellFormed.denials body denialMember) _ goalMember).1 found
  | rule _ _ _ atVertex _ _ _ inCalls ih =>
      have calleeMember := successor_mem ih.1 (mem_callsAt atVertex inCalls)
      obtain ⟨goalMember, found⟩ := mem_bodyCalls inCalls
      refine ⟨calleeMember, vertex?_closed ?_ found⟩
      exact (Scans.goals (wellFormed.rules _ (rulesOf_mem (mem_rulesAt.mp atVertex).1)).scans _ goalMember).1

omit [FreshNames Variable] in
/-- A rule instance whose body holds makes its head's atom a consequence. -/
theorem consequence_of_instance (wellFormed : program.WellFormed) {markers interp : Interp Literal Symbol}
    {rule : Rule Variable Literal Symbol} (ruleMember : rule ∈ program.rules) {σ : Variable → Term Variable Literal Symbol}
    (bodyHolds : (program.keyModel markers interp).Satisfies (fun name => Open.dataKey (σ name)) (bodyTerm rule.body)) :
    consequence program.hoApply program.signature program.clauses (program.base markers) interp rule.head
      ((rule.args.map (subst σ)).map Open.dataKey) := by
  have ruleOk := wellFormed.rules rule ruleMember
  refine ⟨by rw [List.length_map, List.length_map]; exact closedAt_mem ruleOk.closed, rule.args, rule.body.map Goal.toTerm,
    List.mem_append_left _ (List.mem_map.mpr ⟨rule, ruleMember, rfl⟩), fun name => Open.dataKey (σ name), ?_, bodyHolds⟩
  rw [keys_evalAll_subst _ σ rule.args (dataInAll_of ruleOk.data), List.map_map]

omit [FreshNames Variable] in
/-- A relevant atom's instance whose body holds passes, in an interpretation
supported by its rules. -/
theorem entry_passes (wellFormed : program.WellFormed) (guarded : program.Guarded) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) {markers interp : Interp Literal Symbol}
    (supported : program.Supported markers interp) {vertex : Vertex Symbol} {atom : GAtom Variable Literal Symbol}
    (entry : program.Entry query vertex atom) {index : Nat} {rule : Rule Variable Literal Symbol}
    (atVertex : (index, rule) ∈ program.rulesAt vertex) {σ : Variable → Term Variable Literal Symbol}
    (groundRule : GroundOn program.constructors σ rule.names)
    (bodyHolds : (program.keyModel markers interp).Satisfies (fun name => Open.dataKey (σ name)) (bodyTerm rule.body)) :
    program.Passes σ (startNames vertex.2 rule.args) rule.body := by
  have vertexMember := (relevant_vertex wellFormed queryOk entry.1).1
  have ruleMember := rulesOf_mem (mem_rulesAt.mp atVertex).1
  refine passes_of_holds wellFormed (Scans.goals (wellFormed.rules rule ruleMember).scans)
    (fun name occurs => groundRule name (List.mem_append_right _ occurs)) _ bodyHolds
    fun position bound predicate args callMember calleeFree closedCall argsGround atomHolds => ?_
  have calleeMember := successor_mem vertexMember (mem_callsAt atVertex callMember)
  exact ans_complete wellFormed guarded evidence supported _ calleeMember calleeFree (by simpa [length_patternOf] using closedCall)
    _ (by simp [length_patternOf]) argsGround atomHolds

/-- The relevant program's completion at a relevant atom: it holds exactly
when a relevant instance of it has a body that holds. -/
def RelevantHolds (query : Query Variable Literal Symbol) (markers interp : Interp Literal Symbol)
    (atom : GAtom Variable Literal Symbol) : Prop :=
  interp atom.1 (keyArgs atom) ↔ ∃ rule σ, program.Instance query atom rule σ ∧
    (program.keyModel markers interp).Satisfies (fun name => Open.dataKey (σ name)) (bodyTerm rule.body)

omit [FreshNames Variable] in
/-- **A key fixpoint satisfies the relevant program's completion**: every
relevant atom holds exactly when a relevant instance of it has a body that
holds. -/
theorem relevant_of_fixpoint (wellFormed : program.WellFormed) (guarded : program.Guarded) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) {markers interp : Interp Literal Symbol}
    (fixed : program.KeyFixpoint markers interp) {atom : GAtom Variable Literal Symbol} (relevant : program.RelevantAtom query atom) :
    program.RelevantHolds query markers interp atom := by
  obtain ⟨vertex, entry⟩ := relevant
  have supported : program.Supported markers interp := fun symbol keys closed holds => (fixed.1 symbol keys closed).mp holds
  have closedVertex := (relevant_vertex wellFormed queryOk entry.1).2
  obtain ⟨_, symbolEq, lengths, ground, _⟩ := id entry
  obtain ⟨symbol, values⟩ := atom
  simp only at symbolEq lengths ground
  constructor
  · intro holds
    have closedKey : (symbol, (values.map Open.dataKey).length) ∈ program.signature.predicates := by
      rw [List.length_map, lengths, symbolEq]; exact closedAt_mem closedVertex
    obtain ⟨index, rule, σ, found, headEq, argLengths, groundRule, headValues, keyBody⟩ :=
      instance_of_consequence wellFormed guarded ground ((fixed.1 _ _ closedKey).mp holds)
    have atVertex : (index, rule) ∈ program.rulesAt vertex :=
      mem_rulesAt.mpr ⟨mem_rulesOf.mpr ⟨found, by rw [headEq, symbolEq]⟩, by rw [argLengths, lengths]⟩
    exact ⟨rule, σ, ⟨vertex, index, entry, atVertex, groundRule, headValues,
      entry_passes wellFormed guarded queryOk evidence supported entry atVertex groundRule keyBody⟩, keyBody⟩
  · rintro ⟨rule, σ, ⟨other, index, otherEntry, atVertex, _, headValues, _⟩, bodyHolds⟩
    obtain ⟨found, headEq⟩ := mem_rulesOf.mp (mem_rulesAt.mp atVertex).1
    have derived := consequence_of_instance wellFormed (List.mem_of_getElem? found) bodyHolds
    rw [headValues, headEq, ← otherEntry.2.1] at derived
    exact (fixed.1 _ _ derived.1).mpr derived

omit [FreshNames Variable] in
/-- **The relevant program splits the completion.** A key interpretation is a
key fixpoint when its relevant atoms satisfy the relevant program's
completion, every other closed atom satisfies the completion, and every
denial's body is false. With `relevant_of_fixpoint`: the completion's models
restricted to the relevant atoms are the models of the relevant program's
completion, given a model of the rest of the KB. -/
theorem fixpoint_of_relevant (wellFormed : program.WellFormed) (guarded : program.Guarded) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) {markers interp : Interp Literal Symbol}
    (inside : ∀ atom, program.RelevantAtom query atom → program.RelevantHolds query markers interp atom)
    (outside : ∀ symbol keys, (symbol, keys.length) ∈ program.signature.predicates →
      (¬ ∃ atom, program.RelevantAtom query atom ∧ atom.1 = symbol ∧ keyArgs atom = keys) →
        (interp symbol keys ↔ consequence program.hoApply program.signature program.clauses (program.base markers) interp
          symbol keys))
    (denied : Denied program.hoApply program.signature program.clauses (program.base markers) interp) :
    program.KeyFixpoint markers interp := by
  -- Supported by the rules: inside by the relevant instances, outside by the completion.
  have supported : program.Supported markers interp := by
    intro symbol keys closed holds
    by_cases isRelevant : ∃ atom, program.RelevantAtom query atom ∧ atom.1 = symbol ∧ keyArgs atom = keys
    · obtain ⟨atom, relevant, rfl, rfl⟩ := isRelevant
      obtain ⟨rule, σ, ⟨other, index, otherEntry, atVertex, _, headValues, _⟩, bodyHolds⟩ := (inside atom relevant).mp holds
      obtain ⟨found, headEq⟩ := mem_rulesOf.mp (mem_rulesAt.mp atVertex).1
      have derived := consequence_of_instance wellFormed (List.mem_of_getElem? found) bodyHolds
      rw [headValues, headEq, ← otherEntry.2.1] at derived
      exact derived
    · exact (outside symbol keys closed isRelevant).mp holds
  refine ⟨fun symbol keys closed => ⟨supported symbol keys closed, fun derived => ?_⟩, denied⟩
  by_cases isRelevant : ∃ atom, program.RelevantAtom query atom ∧ atom.1 = symbol ∧ keyArgs atom = keys
  · obtain ⟨atom, relevant, rfl, rfl⟩ := isRelevant
    obtain ⟨vertex, entry⟩ := relevant
    obtain ⟨_, symbolEq, lengths, ground, _⟩ := id entry
    obtain ⟨index, rule, σ, found, headEq, argLengths, groundRule, headValues, keyBody⟩ :=
      instance_of_consequence wellFormed guarded ground derived
    have atVertex : (index, rule) ∈ program.rulesAt vertex :=
      mem_rulesAt.mpr ⟨mem_rulesOf.mpr ⟨found, by rw [headEq, symbolEq]⟩, by rw [argLengths, lengths]⟩
    exact (inside atom ⟨vertex, entry⟩).mpr ⟨rule, σ, ⟨vertex, index, entry, atVertex, groundRule, headValues,
      entry_passes wellFormed guarded queryOk evidence supported entry atVertex groundRule keyBody⟩, keyBody⟩
  · exact (outside symbol keys closed isRelevant).mpr derived

omit [FreshNames Variable] in
/-- A denial's guarded names hold ground terms where its body holds in a key
model. -/
theorem denial_instance (wellFormed : program.WellFormed) (guarded : program.Guarded) {markers interp : Interp Literal Symbol}
    {body : List (Goal Variable Literal Symbol)} (member : body ∈ program.denials) {environment : Environment Variable (Key Literal Symbol)}
    (holds : (program.keyModel markers interp).Satisfies environment (bodyTerm body)) :
    GroundOn program.constructors (program.groundsOfKeys environment) (bodyNames body) ∧
      (program.keyModel markers interp).Satisfies (fun name => Open.dataKey (program.groundsOfKeys environment name))
        (bodyTerm body) := by
  have spec : ∀ name ∈ bodyNames body, groundIn program.constructors (program.groundsOfKeys environment name) = true ∧
      Open.dataKey (program.groundsOfKeys environment name) = environment name :=
    fun name inside => program.groundsOfKeys_spec (key_of_guarded wellFormed holds (guarded.denials body member name inside))
  refine ⟨fun name inside => (spec name inside).1, ?_⟩
  unfold Model.Satisfies
  rw [Model.eval_congr _ (bodyTerm body) (right := environment) fun name occurs => (spec name (bodyNames_of_freeVars occurs)).2]
  exact holds

omit [FreshNames Variable] in
/-- **Denials are read on their passing instances** (decided with the user,
2026-11-18: denials join the relevant program). In an interpretation
supported by its rules, every denial's body is false exactly when it is false
at every passing ground instance of it, whose calls are relevant. -/
theorem denied_iff (wellFormed : program.WellFormed) (guarded : program.Guarded) {query : Query Variable Literal Symbol}
    (evidence : program.notes query = []) {markers interp : Interp Literal Symbol} (supported : program.Supported markers interp) :
    Denied program.hoApply program.signature program.clauses (program.base markers) interp ↔
      ∀ body ∈ program.denials, ∀ σ : Variable → Term Variable Literal Symbol,
        GroundOn program.constructors σ (bodyNames body) → program.Passes σ [] body →
          ¬ (program.keyModel markers interp).Satisfies (fun name => Open.dataKey (σ name)) (bodyTerm body) := by
  constructor
  · intro denied body member σ _ _ holds
    exact denied (body.map Goal.toTerm) (List.mem_append_right _ (List.mem_map.mpr ⟨body, member, rfl⟩)) _ holds
  · intro falseAt clauseBody clauseMember environment holds
    rcases List.mem_append.mp clauseMember with inRules | inDenials
    · obtain ⟨_, _, same⟩ := List.mem_map.mp inRules
      cases same
    · obtain ⟨body, member, same⟩ := List.mem_map.mp inDenials
      simp only [denialClause, HornClause.goal.injEq] at same
      subst same
      have holds' : (program.keyModel markers interp).Satisfies environment (bodyTerm body) := holds
      obtain ⟨ground, keyBody⟩ := denial_instance wellFormed guarded member holds'
      refine falseAt body member _ ground ?_ keyBody
      refine passes_of_holds wellFormed (Scans.goals (wellFormed.denials body member)) ground [] keyBody
        fun position bound predicate args callMember calleeFree closedCall argsGround atomHolds => ?_
      have calleeMember : (predicate, patternOf bound args) ∈ program.vertices query :=
        denialVertices_mem (List.mem_flatMap.mpr ⟨body, member, List.mem_map.mpr ⟨_, callMember, rfl⟩⟩)
      exact ans_complete wellFormed guarded evidence supported _ calleeMember calleeFree
        (by simpa [length_patternOf] using closedCall) _ (by simp [length_patternOf]) argsGround atomHolds

end Splitting

end Program

end AnthillModKbSpec.IR
