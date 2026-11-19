import AnthillModKbSpec.Resolution.IR.RelevantProgram

/-! # Possible answers and passing instances, computed and checked (S28)

The evaluator of the [decision IR](../../../docs/decision-ir.md) runs on the
exact relevant program of a query (S27's `Relevant`, `Instance`). This module
computes its two ingredients without fuel:

- **Possible answers** (`Program.answersOf`): the answers a call that leaves
  an output free may have in some model (S27's `Ans`), by recursion on the
  call's rank (its vertex's level, then the size of its bound values). Each
  recursive call is made only when the callee's rank is lower, a check made
  at run time (`lowerRank`); with the finiteness evidence it always passes
  (S27's `call_rank`), so the recursion is exact.
- **Passing instances** (`Program.instancesAt`): the instances of a vertex's
  rules at the values of its bound arguments, enumerated by S27's
  `bodyEnvs`, each **checked** before it is kept (`Program.checked`): its
  names hold ground data terms, its head's bound arguments are the call's
  values, and it passes (`Program.passesWith`: fixed literals true, every
  call that leaves an output free at a listed answer).

Soundness is by the checks alone, whatever the enumeration computes: every
computed answer is a possible answer, with no hypothesis (`answersOf_sound`),
and every kept instance passed the check (`instancesAt_sound`), so it passes
when its answer lists are sound (`passesWith_sound`; with an evaluation's
lists, `instancesAt_passes`). Completeness is by S27's enumeration
(`walk_at`) and the evidence: every possible answer is computed
(`answersOf_complete`), and every passing instance the enumeration reaches is
kept (`instancesAt_complete`; at a call of the graph, `instance_kept`). -/

namespace AnthillModKbSpec.IR

open Semantics Completion Tabled Answers

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  [FreshNames Variable]

attribute [local instance] Machine.termEq

/-! ## Substitutions of computed values -/

/-- A partial substitution as a total one: a name without a value stays a
name, which no ground term is. -/
def envSubst (env : Env Variable Literal Symbol) : Variable → Term Variable Literal Symbol :=
  fun name => (env name).getD (.var name)

/-- The substitution giving listed names their listed values, the first
listing winning, and every other name itself. -/
def substOf (names : List Variable) (values : List (Term Variable Literal Symbol)) :
    Variable → Term Variable Literal Symbol :=
  fun name => (((names.zip values).find? fun pair => pair.1 == name).map (·.2)).getD (.var name)

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
/-- Listing a substitution's values on a list of names keeps them. -/
theorem substOf_map (σ : Variable → Term Variable Literal Symbol) :
    ∀ {names : List Variable} {name : Variable}, name ∈ names → substOf names (names.map σ) name = σ name
  | [], _, member => by cases member
  | first :: rest, name, member => by
      by_cases same : first = name
      · subst same
        simp [substOf]
      · have inRest : name ∈ rest := by
          rcases List.mem_cons.mp member with here | there
          · exact absurd here.symm same
          · exact there
        have := substOf_map σ inRest
        have different : (first == name) = false := by simpa using same
        unfold substOf at this ⊢
        simp only [List.map_cons, List.zip_cons_cons, List.find?_cons, different]
        exact this

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
mutual
/-- A term's substitution reads only its own names. -/
theorem subst_congr {σ τ : Variable → Term Variable Literal Symbol} :
    ∀ term : Term Variable Literal Symbol, (∀ name ∈ term.freeVars, σ name = τ name) → subst σ term = subst τ term
  | .var name, agree => by simp only [subst]; exact agree name (by simp [Term.freeVars])
  | .app symbol args, agree => by
      simp only [subst]
      rw [substAll_congr args fun name inside => agree name (by simpa [Term.freeVars] using inside)]
  | .lit _, _ | .truth, _ | .falsity, _ | .conj _ _, _ | .disj _ _, _ | .imp _ _, _ | .defaultNeg _, _
  | .forallVar _ _, _ | .existsVar _ _, _ | .dictionaryCall _ _ _ _, _ | .equal _ _, _ => by simp [subst]

theorem substAll_congr {σ τ : Variable → Term Variable Literal Symbol} :
    ∀ args : List (Term Variable Literal Symbol), (∀ name ∈ args.flatMap Term.freeVars, σ name = τ name) →
      substAll σ args = substAll τ args
  | [], _ => rfl
  | arg :: rest, agree => by
      simp only [substAll]
      rw [subst_congr arg fun name inside => agree name (by simp [inside]),
        substAll_congr rest fun name inside => agree name (by simp only [List.flatMap_cons, List.mem_append]; exact .inr inside)]
end

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem map_subst_congr {σ τ : Variable → Term Variable Literal Symbol} {args : List (Term Variable Literal Symbol)}
    (agree : ∀ name ∈ namesOf args, σ name = τ name) : args.map (subst σ) = args.map (subst τ) := by
  rw [← substAll_eq, ← substAll_eq]
  exact substAll_congr args agree

namespace Program

variable (program : Program Variable Literal Symbol)

/-! ## Checking an instance -/

/-- A fixed literal's truth at an instance, decided (`fixedB_iff`): an
equation, a disequality, a guard, a primitive. Every other literal is not
fixed and passes. -/
def fixedB (σ : Variable → Term Variable Literal Symbol) : Goal Variable Literal Symbol → Bool
  | .equal left right => decide (subst σ left = subst σ right)
  | .differ left right => !decide (subst σ left = subst σ right)
  | .guard symbol arg => program.guardHolds symbol (subst σ arg)
  | .primitive symbol inputs output => decide (program.evaluate symbol (inputs.map (subst σ)) = some (subst σ output))
  | _ => true

/-- An instance passes a body read from the names bound before it, decided
against answer lists: fixed literals true, and every call that leaves an
output free at an answer listed for its vertex and bound values. -/
def passesWith (answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol))
    (σ : Variable → Term Variable Literal Symbol) : List Variable → List (Goal Variable Literal Symbol) → Bool
  | _, [] => true
  | bound, goal :: rest =>
      (match goal.vertex? bound with
        | some vertex =>
            if vertex.2.free then
              decide ((vertex.1, goal.args.map (subst σ)) ∈ answers vertex (boundArgs vertex.2 (goal.args.map (subst σ))))
            else program.fixedB σ goal
        | none => program.fixedB σ goal) &&
        passesWith answers σ (after bound goal) rest

/-- An instance of a rule read under a vertex, checked: its names hold ground
data terms, its head's bound arguments have the call's values, and it passes
against the answer lists. -/
def checked (answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol))
    (vertex : Vertex Symbol) (rule : Rule Variable Literal Symbol) (values : List (Term Variable Literal Symbol))
    (σ : Variable → Term Variable Literal Symbol) : Bool :=
  rule.names.all (fun name => groundIn program.constructors (σ name)) &&
    decide ((boundArgs vertex.2 rule.args).map (subst σ) = values) &&
    program.passesWith answers σ (startNames vertex.2 rule.args) rule.body

/-- The checked passing instances of a vertex's rules at the values of its
bound arguments: each by its rule's index and its rule's names' values, in
the order of `Rule.names`. -/
def instancesAt (answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol))
    (vertex : Vertex Symbol) (values : List (Term Variable Literal Symbol)) :
    List (Nat × List (Term Variable Literal Symbol)) :=
  ((program.rulesAt vertex).flatMap fun (index, rule) =>
    match startEnv vertex rule values with
    | some start => (program.bodyEnvs answers (startNames vertex.2 rule.args) [start] rule.body).filterMap fun env =>
        let nameValues := rule.names.map (envSubst env)
        if program.checked answers vertex rule values (substOf rule.names nameValues) then some (index, nameValues) else none
    | none => []).eraseDups

/-- The head of a listed instance of a rule. -/
def headOf (entry : Nat × List (Term Variable Literal Symbol)) : Option (GAtom Variable Literal Symbol) :=
  (program.rules[entry.1]?).map fun rule => (rule.head, rule.args.map (subst (substOf rule.names entry.2)))

/-! ## Possible answers by rank -/

/-- A callee's rank is lower than its caller's: a lower level, or the same
level and smaller bound values. -/
def lowerRank (levelOf : Vertex Symbol → Nat) (callee : Vertex Symbol) (calleeValues : List (Term Variable Literal Symbol))
    (vertex : Vertex Symbol) (values : List (Term Variable Literal Symbol)) : Prop :=
  levelOf callee < levelOf vertex ∨ (levelOf callee = levelOf vertex ∧ sizeAll calleeValues < sizeAll values)

instance (levelOf : Vertex Symbol → Nat) (callee : Vertex Symbol) (calleeValues : List (Term Variable Literal Symbol))
    (vertex : Vertex Symbol) (values : List (Term Variable Literal Symbol)) :
    Decidable (lowerRank levelOf callee calleeValues vertex values) := by
  unfold lowerRank; infer_instance

/-- **The possible answers of a call**, computed: the heads of the checked
passing instances of its vertex's rules, the calls they make that leave an
output free answered by recursion when their rank is lower, and by nothing
otherwise. Total, with no fuel: the recursion descends the rank. -/
def answersOf (levelOf : Vertex Symbol → Nat) (vertex : Vertex Symbol) (values : List (Term Variable Literal Symbol)) :
    List (GAtom Variable Literal Symbol) :=
  ((program.instancesAt
      (fun callee calleeValues =>
        if _lower : lowerRank levelOf callee calleeValues vertex values then answersOf levelOf callee calleeValues else [])
      vertex values).filterMap program.headOf).eraseDups
termination_by (levelOf vertex, sizeAll values)
decreasing_by
  rcases _lower with lower | ⟨same, smaller⟩
  · exact Prod.Lex.left _ _ lower
  · rw [same]; exact Prod.Lex.right _ smaller

/-- The answer lists `answersOf` reads inside a call: the recursive ones
below its rank, and none at or above it. -/
def answersBelow (levelOf : Vertex Symbol → Nat) (vertex : Vertex Symbol) (values : List (Term Variable Literal Symbol)) :
    Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol) :=
  fun callee calleeValues =>
    if lowerRank levelOf callee calleeValues vertex values then program.answersOf levelOf callee calleeValues else []

omit [FreshNames Variable] in
theorem answersOf_eq (levelOf : Vertex Symbol → Nat) (vertex : Vertex Symbol) (values : List (Term Variable Literal Symbol)) :
    program.answersOf levelOf vertex values =
      ((program.instancesAt (program.answersBelow levelOf vertex values) vertex values).filterMap program.headOf).eraseDups := by
  rw [answersOf]
  rfl

/-! ## The checks are sound -/

variable {program}

omit [FreshNames Variable] in
theorem fixedB_iff {σ : Variable → Term Variable Literal Symbol} {goal : Goal Variable Literal Symbol} :
    program.fixedB σ goal = true ↔ program.fixedAt σ goal := by
  cases goal <;> simp [fixedB, fixedAt]

omit [FreshNames Variable] in
/-- An instance the check passes against sound answer lists passes. -/
theorem passesWith_sound
    {answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)}
    (sound : ∀ vertex values atom, atom ∈ answers vertex values → program.Ans vertex atom)
    {σ : Variable → Term Variable Literal Symbol} :
    ∀ {bound : List Variable} {body : List (Goal Variable Literal Symbol)},
      program.passesWith answers σ bound body = true → program.Passes σ bound body
  | _, [], _ => .nil
  | bound, goal :: rest, ok => by
      simp only [passesWith, Bool.and_eq_true] at ok
      obtain ⟨here, restOk⟩ := ok
      have restPasses := passesWith_sound sound restOk
      cases found : goal.vertex? bound with
      | none =>
          rw [found] at here
          exact .fixed (fun _ same => by rw [found] at same; cases same) (fixedB_iff.mp here) restPasses
      | some vertex =>
          rw [found] at here
          cases free : vertex.2.free with
          | true =>
              simp only [free, ite_true, decide_eq_true_eq] at here
              exact .free found free (sound _ _ _ here) restPasses
          | false =>
              simp only [free, Bool.false_eq_true, ite_false] at here
              refine .fixed (fun other same => ?_) (fixedB_iff.mp here) restPasses
              rw [found] at same; cases same; exact free

omit [FreshNames Variable] in
/-- A passing instance passes the check, when the answer lists hold the
possible answers of its calls that leave an output free. -/
theorem passesWith_complete
    {answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)}
    {σ : Variable → Term Variable Literal Symbol} :
    ∀ {position : Nat} {bound : List Variable} {body : List (Goal Variable Literal Symbol)},
      program.Passes σ bound body →
      (∀ call ∈ bodyCalls position bound body, call.2.2.2.2.free = true →
        program.Ans call.2.2.2 (call.2.2.2.1, call.2.1.args.map (subst σ)) →
          (call.2.2.2.1, call.2.1.args.map (subst σ)) ∈ answers call.2.2.2 (boundArgs call.2.2.2.2 (call.2.1.args.map (subst σ)))) →
      program.passesWith answers σ bound body = true
  | _, _, [], _, _ => rfl
  | position, bound, goal :: rest, passes, covered => by
      have split : ((∃ vertex, goal.vertex? bound = some vertex ∧ vertex.2.free = true ∧
            program.Ans vertex (vertex.1, goal.args.map (subst σ))) ∨
          ((∀ vertex, goal.vertex? bound = some vertex → vertex.2.free = false) ∧ program.fixedAt σ goal)) ∧
          program.Passes σ (after bound goal) rest := by
        cases passes with
        | free found free answer restPasses => exact ⟨.inl ⟨_, found, free, answer⟩, restPasses⟩
        | fixed notFree fixed restPasses => exact ⟨.inr ⟨notFree, fixed⟩, restPasses⟩
      simp only [passesWith, Bool.and_eq_true]
      refine ⟨?_, passesWith_complete (position := position + 1) split.2
        fun call inside => covered call (mem_bodyCalls_tail inside)⟩
      rcases split.1 with ⟨vertex, found, free, answer⟩ | ⟨notFree, fixed⟩
      · rw [found]
        simp only [free, ite_true, decide_eq_true_eq]
        exact covered _ (mem_bodyCalls_head (rest := rest) (position := position) found) free answer
      · cases found : goal.vertex? bound with
        | none => exact fixedB_iff.mpr fixed
        | some vertex =>
            simp only [notFree vertex found, Bool.false_eq_true, ite_false]
            exact fixedB_iff.mpr fixed

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem names_args_sub {goal : Goal Variable Literal Symbol} {arg : Term Variable Literal Symbol} (member : arg ∈ goal.args)
    {name : Variable} (occurs : name ∈ arg.freeVars) : name ∈ goal.names :=
  List.mem_flatMap.mpr ⟨arg, member, occurs⟩

omit [FreshNames Variable] in
theorem fixedB_congr {σ τ : Variable → Term Variable Literal Symbol} {goal : Goal Variable Literal Symbol}
    (agree : ∀ name ∈ goal.names, σ name = τ name) : program.fixedB σ goal = program.fixedB τ goal := by
  have each : ∀ arg ∈ goal.args, subst σ arg = subst τ arg :=
    fun arg member => subst_congr arg fun name occurs => agree name (names_args_sub member occurs)
  cases goal with
  | equal left right =>
      simp only [fixedB, each left (by simp [Goal.args]), each right (by simp [Goal.args])]
  | differ left right =>
      simp only [fixedB, each left (by simp [Goal.args]), each right (by simp [Goal.args])]
  | guard symbol arg => simp only [fixedB, each arg (by simp [Goal.args])]
  | primitive symbol inputs output =>
      simp only [fixedB, each output (by simp [Goal.args])]
      rw [List.map_congr_left fun input member => each input (List.mem_append_left _ member)]
  | call _ _ | naf _ _ | marker _ _ => rfl

omit [FreshNames Variable] in
/-- The check reads an instance only on its body's names. -/
theorem passesWith_congr
    {answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)}
    {σ τ : Variable → Term Variable Literal Symbol} :
    ∀ {bound : List Variable} {body : List (Goal Variable Literal Symbol)}, (∀ name ∈ bodyNames body, σ name = τ name) →
      program.passesWith answers σ bound body = program.passesWith answers τ bound body
  | _, [], _ => rfl
  | bound, goal :: rest, agree => by
      have here : ∀ name ∈ goal.names, σ name = τ name :=
        fun name inside => agree name (List.mem_flatMap.mpr ⟨goal, List.mem_cons_self, inside⟩)
      have there : ∀ name ∈ bodyNames rest, σ name = τ name :=
        fun name inside => agree name (by simp only [bodyNames, List.flatMap_cons, List.mem_append]; exact .inr inside)
      have argsEq : goal.args.map (subst σ) = goal.args.map (subst τ) :=
        List.map_congr_left fun arg member => subst_congr arg fun name occurs => here name (names_args_sub member occurs)
      simp only [passesWith, argsEq, fixedB_congr here, passesWith_congr there]

omit [FreshNames Variable] in
theorem checked_parts
    {answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)}
    {vertex : Vertex Symbol} {rule : Rule Variable Literal Symbol} {values : List (Term Variable Literal Symbol)}
    {σ : Variable → Term Variable Literal Symbol} (ok : program.checked answers vertex rule values σ = true) :
    GroundOn program.constructors σ rule.names ∧ (boundArgs vertex.2 rule.args).map (subst σ) = values ∧
      program.passesWith answers σ (startNames vertex.2 rule.args) rule.body = true := by
  simp only [checked, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ok
  exact ⟨ok.1.1, ok.1.2, ok.2⟩

omit [FreshNames Variable] in
theorem checked_congr
    {answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)}
    {vertex : Vertex Symbol} {rule : Rule Variable Literal Symbol} {values : List (Term Variable Literal Symbol)}
    {σ τ : Variable → Term Variable Literal Symbol} (agree : ∀ name ∈ rule.names, σ name = τ name) :
    program.checked answers vertex rule values σ = program.checked answers vertex rule values τ := by
  have grounds : rule.names.all (fun name => groundIn program.constructors (σ name)) =
      rule.names.all (fun name => groundIn program.constructors (τ name)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor <;> intro each name inside
    · rw [← agree name inside]; exact each name inside
    · rw [agree name inside]; exact each name inside
  have heads : (boundArgs vertex.2 rule.args).map (subst σ) = (boundArgs vertex.2 rule.args).map (subst τ) :=
    map_subst_congr fun name inside => agree name (by
      obtain ⟨arg, argMember, occurs⟩ := List.mem_flatMap.mp inside
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨arg, mem_of_mem_boundArgs argMember, occurs⟩))
  have bodies := passesWith_congr (program := program) (answers := answers) (bound := startNames vertex.2 rule.args)
    (body := rule.body) fun name inside => agree name (List.mem_append_right _ inside)
  simp only [checked, grounds, heads, bodies]

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
/-- Listed values give their names a substitution that lists them again. -/
theorem map_substOf {names : List Variable} {f : Variable → Term Variable Literal Symbol} :
    names.map (substOf names (names.map f)) = names.map f :=
  List.map_congr_left fun _ inside => substOf_map f inside

omit [FreshNames Variable] in
/-- **A kept instance is checked**: its rule is the vertex's, its values list
its names' values, and the check passes at them. -/
theorem instancesAt_sound
    {answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)}
    {vertex : Vertex Symbol} {values : List (Term Variable Literal Symbol)} {entry : Nat × List (Term Variable Literal Symbol)}
    (member : entry ∈ program.instancesAt answers vertex values) :
    ∃ rule, (entry.1, rule) ∈ program.rulesAt vertex ∧ entry.2 = rule.names.map (substOf rule.names entry.2) ∧
      program.checked answers vertex rule values (substOf rule.names entry.2) = true := by
  unfold instancesAt at member
  rw [List.mem_eraseDups] at member
  obtain ⟨⟨index, rule⟩, atVertex, inside⟩ := List.mem_flatMap.mp member
  cases started : startEnv vertex rule values with
  | none => simp only [started] at inside; cases inside
  | some start =>
      simp only [started] at inside
      obtain ⟨env, _, produced⟩ := List.mem_filterMap.mp inside
      split at produced
      · rename_i ok
        cases produced
        exact ⟨rule, atVertex, map_substOf.symm, ok⟩
      · cases produced

omit [FreshNames Variable] in
/-- **A passing instance is kept**, once the enumeration reaches it with
answer lists holding the possible answers of its free calls. -/
theorem instancesAt_complete
    {answers : Vertex Symbol → List (Term Variable Literal Symbol) → List (GAtom Variable Literal Symbol)}
    {vertex : Vertex Symbol} {index : Nat} {rule : Rule Variable Literal Symbol} (atVertex : (index, rule) ∈ program.rulesAt vertex)
    {σ : Variable → Term Variable Literal Symbol} (groundRule : GroundOn program.constructors σ rule.names)
    (passes : program.Passes σ (startNames vertex.2 rule.args) rule.body)
    (covered : ∀ call ∈ bodyCalls 0 (startNames vertex.2 rule.args) rule.body, call.2.2.2.2.free = true →
      program.Ans call.2.2.2 (call.2.2.2.1, call.2.1.args.map (subst σ)) →
        (call.2.2.2.1, call.2.1.args.map (subst σ)) ∈ answers call.2.2.2 (boundArgs call.2.2.2.2 (call.2.1.args.map (subst σ))))
    {start : Env Variable Literal Symbol}
    (started : startEnv vertex rule ((boundArgs vertex.2 rule.args).map (subst σ)) = some start)
    {next : Env Variable Literal Symbol} (nextMember : next ∈ program.bodyEnvs answers (startNames vertex.2 rule.args) [start] rule.body)
    (gives : ∀ name ∈ rule.names, next name = some (σ name)) :
    (index, rule.names.map σ) ∈ program.instancesAt answers vertex ((boundArgs vertex.2 rule.args).map (subst σ)) := by
  have valuesEq : rule.names.map (envSubst next) = rule.names.map σ :=
    List.map_congr_left fun name inside => by simp [envSubst, gives name inside]
  have agree : ∀ name ∈ rule.names, substOf rule.names (rule.names.map σ) name = σ name :=
    fun _ inside => substOf_map σ inside
  have ok : program.checked answers vertex rule ((boundArgs vertex.2 rule.args).map (subst σ))
      (substOf rule.names (rule.names.map σ)) = true := by
    rw [checked_congr agree]
    simp only [checked, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact ⟨⟨groundRule, by trivial⟩, passesWith_complete (position := 0) passes covered⟩
  unfold instancesAt
  rw [List.mem_eraseDups]
  refine List.mem_flatMap.mpr ⟨(index, rule), atVertex, ?_⟩
  simp only [started]
  refine List.mem_filterMap.mpr ⟨next, nextMember, ?_⟩
  simp only [valuesEq, ok, ite_true]

omit [DecidableEq Literal] [FreshNames Variable] in
theorem headOf_rule {vertex : Vertex Symbol} {index : Nat} {rule : Rule Variable Literal Symbol}
    (atVertex : (index, rule) ∈ program.rulesAt vertex) (nameValues : List (Term Variable Literal Symbol)) :
    program.headOf (index, nameValues) = some (rule.head, rule.args.map (subst (substOf rule.names nameValues))) := by
  simp [headOf, (mem_rulesOf.mp (mem_rulesAt.mp atVertex).1).1]

/-! ## Possible answers: sound, and complete with the evidence -/

omit [FreshNames Variable] in
/-- **Every computed answer is a possible answer** of its call, with no
hypothesis: by the checks. -/
theorem answersOf_sound (levelOf : Vertex Symbol → Nat) :
    ∀ vertex values atom, atom ∈ program.answersOf levelOf vertex values →
      program.Ans vertex atom ∧ boundArgs vertex.2 atom.2 = values := by
  suffices main : ∀ n m vertex values, levelOf vertex = n → sizeAll values = m → ∀ atom,
      atom ∈ program.answersOf levelOf vertex values → program.Ans vertex atom ∧ boundArgs vertex.2 atom.2 = values from
    fun vertex values atom => main _ _ vertex values rfl rfl atom
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihLevel =>
  intro m
  induction m using Nat.strongRecOn with
  | ind m ihSize =>
  intro vertex values levelEq sizeEq atom member
  have below : ∀ callee calleeValues found, found ∈ program.answersBelow levelOf vertex values callee calleeValues →
      program.Ans callee found := by
    intro callee calleeValues found inside
    unfold answersBelow at inside
    split at inside
    · rename_i lower
      rcases lower with lower | ⟨same, smaller⟩
      · exact (ihLevel _ (levelEq ▸ lower) _ callee calleeValues rfl rfl found inside).1
      · exact (ihSize _ (sizeEq ▸ smaller) callee calleeValues (same.trans levelEq) rfl found inside).1
    · cases inside
  rw [answersOf_eq, List.mem_eraseDups] at member
  obtain ⟨entry, entryMember, headEq⟩ := List.mem_filterMap.mp member
  obtain ⟨rule, atVertex, _, ok⟩ := instancesAt_sound entryMember
  obtain ⟨ground, boundEq, passes⟩ := checked_parts ok
  rw [headOf_rule atVertex, Option.some.injEq] at headEq
  subst headEq
  exact ⟨.rule atVertex ground (passesWith_sound below passes), by rw [boundArgs_map]; exact boundEq⟩

/-- The level function `answersOf` runs with for a query: the levels of its
vertices, read from their table (`answersFor` computes the table once). -/
def levelsOf (program : Program Variable Literal Symbol) (query : Query Variable Literal Symbol) : Vertex Symbol → Nat :=
  levelIn (program.levelTable (program.vertices query))

omit [DecidableEq Literal] [FreshNames Variable] in
theorem levelsOf_eq (query : Query Variable Literal Symbol) : program.levelsOf query = program.levels query := rfl

omit [FreshNames Variable] in
/-- **Every possible answer is computed**: with the finiteness evidence, a call
of the graph that leaves an output free has each of its possible answers
among `answersOf`'s, by induction on its rank. -/
theorem answersOf_complete (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) :
    ∀ vertex ∈ program.vertices query, vertex.2.free = true → ∀ atom, program.Ans vertex atom →
      atom ∈ program.answersOf (program.levelsOf query) vertex (boundArgs vertex.2 atom.2) := by
  have parts := evidence_of_notes evidence
  suffices main : ∀ n m, ∀ vertex ∈ program.vertices query, vertex.2.free = true → ∀ atom, program.Ans vertex atom →
      program.levels query vertex = n → sizeAll (boundArgs vertex.2 atom.2) = m →
        atom ∈ program.answersOf (program.levelsOf query) vertex (boundArgs vertex.2 atom.2) from
    fun vertex member free atom answer => main _ _ vertex member free atom answer rfl rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihLevel =>
  intro m
  induction m using Nat.strongRecOn with
  | ind m ihSize =>
  intro vertex member free atom answer levelEq sizeEq
  cases answer with
  | @rule _ index rule σ atVertex groundRule passes =>
      have valuesEq : boundArgs vertex.2 (rule.args.map (subst σ)) = (boundArgs vertex.2 rule.args).map (subst σ) :=
        boundArgs_map _ _ _
      rw [valuesEq] at sizeEq ⊢
      have covered : ∀ call ∈ bodyCalls 0 (startNames vertex.2 rule.args) rule.body, call.2.2.2.2.free = true →
          program.Ans call.2.2.2 (call.2.2.2.1, call.2.1.args.map (subst σ)) →
            (call.2.2.2.1, call.2.1.args.map (subst σ)) ∈ program.answersBelow (program.levelsOf query) vertex
              ((boundArgs vertex.2 rule.args).map (subst σ)) call.2.2.2 (boundArgs call.2.2.2.2 (call.2.1.args.map (subst σ))) := by
        intro call inside calleeFree calleeAnswer
        obtain ⟨calleeMember, rank⟩ := call_rank parts member free atVertex inside calleeFree σ
        obtain ⟨_, goal, bound, callee⟩ := call
        simp only at calleeFree calleeAnswer calleeMember rank ⊢
        rw [← boundArgs_map] at rank
        unfold answersBelow
        rw [levelsOf_eq] at ⊢
        rcases rank with lower | ⟨same, smaller⟩
        · rw [ite_eq_left_iff.mpr (fun no => absurd (.inl lower) no)]
          exact ihLevel _ (levelEq ▸ lower) _ callee calleeMember calleeFree _ calleeAnswer rfl rfl
        · rw [ite_eq_left_iff.mpr (fun no => absurd (.inr ⟨same, smaller⟩) no)]
          exact ihSize _ (sizeEq ▸ smaller) callee calleeMember calleeFree _ calleeAnswer (same.trans levelEq) rfl
      obtain ⟨_, start, started, next, nextMember, gives⟩ := walk_at (Recorded := fun _ => True) wellFormed queryOk member
        atVertex groundRule passes (fun call inside calleeFree _ calleeAnswer => covered call inside calleeFree calleeAnswer)
        (fun _ _ => trivial)
      have entryMember := instancesAt_complete atVertex groundRule passes covered started nextMember gives
      rw [answersOf_eq, List.mem_eraseDups]
      refine List.mem_filterMap.mpr ⟨_, entryMember, ?_⟩
      rw [headOf_rule atVertex]
      congr 2
      exact map_subst_congr fun name inside => substOf_map σ (List.mem_append_left _ inside)

end Program

end AnthillModKbSpec.IR
