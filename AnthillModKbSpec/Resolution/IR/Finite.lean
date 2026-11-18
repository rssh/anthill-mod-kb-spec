import AnthillModKbSpec.Resolution.IR.Enumerate

/-! # Finitely many possible answers (S27)

With the finiteness evidence, a call that leaves an output free has finitely
many possible answers at each value of its bound arguments (`ans_finite`): by
induction on its rank, its vertex's level and then the size of its bound
arguments. A rule's passing instances at those values extend the partial
substitutions the enumeration computes (`bodyEnvs_complete`), given the lists
of the lower-rank calls' answers from the induction, and their heads are
those substitutions' instances of the rule's head. -/

namespace AnthillModKbSpec.IR

open Semantics Completion Tabled Answers

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  [FreshNames Variable]

attribute [local instance] Machine.termEq
attribute [local irreducible] Program.levels Program.vertices

namespace Program

variable {program : Program Variable Literal Symbol}

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem select_covered {α : Type} : ∀ (modes : List Mode) (args : List α) (pattern : Pattern),
    modes.length = args.length → args.length = pattern.length → (select .input modes pattern).all id = true →
      ∀ arg ∈ select .input modes args, arg ∈ boundArgs pattern args
  | [], _, _, _, _, _, _, member => by simp [select] at member
  | _ :: _, [], _, lengths, _, _, _, _ => by simp at lengths
  | _ :: _, _ :: _, [], _, lengths, _, _, _ => by simp at lengths
  | mode :: modes, arg :: args, bound :: pattern, modesLength, patternLength, covered, other, member => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at modesLength patternLength
      have rest := select_covered modes args pattern modesLength patternLength
      simp only [select] at member covered
      cases mode with
      | input =>
          simp only [ite_true, List.all_cons, Bool.and_eq_true, id] at covered member
          obtain ⟨boundTrue, restCovered⟩ := covered
          subst boundTrue
          rcases List.mem_cons.mp member with rfl | later
          · simp [boundArgs]
          · simp only [boundArgs, List.zip_cons_cons, List.filterMap_cons, ite_true]
            exact List.mem_cons_of_mem _ (rest restCovered other later)
      | output =>
          simp only [reduceCtorEq, ite_false] at covered member
          have inside := rest covered other member
          simp only [boundArgs, List.zip_cons_cons, List.filterMap_cons]
          cases bound
          · exact inside
          · exact List.mem_cons_of_mem _ inside

omit [FreshNames Variable] in
/-- A covering vertex's rules start from names that include their inputs'. -/
theorem start_covers (wellFormed : program.WellFormed) {vertex : Vertex Symbol} (covered : program.covering vertex = true)
    {index : Nat} {rule : Rule Variable Literal Symbol} (atVertex : (index, rule) ∈ program.rulesAt vertex) :
    ∀ name ∈ namesOf (program.inputsOf rule.head rule.args), name ∈ startNames vertex.2 rule.args := by
  obtain ⟨inRules, lengths⟩ := mem_rulesAt.mp atVertex
  obtain ⟨found, headEq⟩ := mem_rulesOf.mp inRules
  have ruleOk := wellFormed.rules rule (List.mem_of_getElem? found)
  obtain ⟨declared, declaredEq, _, arity⟩ := closedAt_declared ruleOk.closed
  intro name member
  obtain ⟨arg, argMember, occurs⟩ := List.mem_flatMap.mp member
  simp only [inputsOf, declaredEq] at argMember
  unfold Program.covering at covered
  rw [← headEq, declaredEq] at covered
  exact List.mem_flatMap.mpr ⟨arg, select_covered declared.modes rule.args vertex.2 arity lengths covered arg argMember, occurs⟩

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem select_map {α β : Type} (mode : Mode) (f : α → β) :
    ∀ (modes : List Mode) (args : List α), select mode modes (args.map f) = (select mode modes args).map f
  | [], _ => by simp [select]
  | _ :: _, [] => by simp [select]
  | first :: modes, arg :: args => by
      simp only [List.map_cons, select]
      split <;> simp [select_map mode f modes args]

omit [DecidableEq Literal] [FreshNames Variable] in
/-- A literal that has what it needs bound is called at a covering vertex. -/
theorem covering_of_needs {bound : List Variable} {goal : Goal Variable Literal Symbol} {vertex : Vertex Symbol}
    (needed : program.needs bound goal = true) (found : goal.vertex? bound = some vertex) : program.covering vertex = true := by
  cases goal with
  | call predicate args =>
      simp only [Goal.vertex?, Option.some.injEq] at found
      subst found
      unfold covering
      simp only
      cases declaredEq : program.predicate? predicate with
      | none => rfl
      | some declared =>
          simp only [needs, inputsOf, declaredEq] at needed
          simp only [patternOf, select_map, List.all_map, List.all_eq_true, Function.comp_apply, id]
          intro arg member
          exact available_iff.mpr fun name occurs =>
            available_iff.mp needed name (List.mem_flatMap.mpr ⟨arg, member, occurs⟩)
  | naf predicate args =>
      simp only [Goal.vertex?, Option.some.injEq] at found
      subst found
      unfold covering
      simp only
      cases program.predicate? predicate with
      | none => rfl
      | some declared =>
          simp only [List.all_eq_true, id]
          intro flag member
          have := Tabled.Program.select_sub _ _ _ flag member
          simp only [full, List.mem_replicate] at this
          exact this.2
  | _ => simp [Goal.vertex?] at found

omit [FreshNames Variable] in
/-- The calls of a body that scans are at covering vertices. -/
theorem bodyCalls_covering : ∀ {position : Nat} {bound : List Variable} {body : List (Goal Variable Literal Symbol)},
    Scans program bound body → ∀ call ∈ bodyCalls position bound body, program.covering call.2.2.2 = true
  | _, _, [], _, _, member => by cases member
  | position, bound, goal :: rest, .cons _ _ needed restScans, call, member => by
      simp only [bodyCalls, List.mem_append] at member
      rcases member with here | there
      · cases found : goal.vertex? bound with
        | none => rw [found] at here; cases here
        | some vertex =>
            rw [found] at here
            simp only [List.mem_singleton] at here
            subst here
            exact covering_of_needs needed found
      · exact bodyCalls_covering restScans call there

omit [FreshNames Variable] in
/-- A covering vertex's successors cover. -/
theorem successors_covering (wellFormed : program.WellFormed) {vertex : Vertex Symbol} (covered : program.covering vertex = true) :
    ∀ callee ∈ program.successors vertex, program.covering callee = true := by
  intro callee member
  obtain ⟨⟨index, rule, call⟩, inCalls, rfl⟩ := List.mem_map.mp member
  obtain ⟨⟨index', rule'⟩, atVertex, inMap⟩ := List.mem_flatMap.mp inCalls
  obtain ⟨call', callMember, same⟩ := List.mem_map.mp inMap
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, rfl, rfl⟩ := same
  have ruleOk := wellFormed.rules rule' (rulesOf_mem (mem_rulesAt.mp atVertex).1)
  exact bodyCalls_covering (Scans.mono ruleOk.scans (start_covers wellFormed covered atVertex)) call' callMember

omit [DecidableEq Literal] [FreshNames Variable] in
/-- What holds of the vertices a closure starts from and of every successor
of a vertex it holds of holds of the closure. -/
theorem closeVertices_all {Good : Vertex Symbol → Prop}
    (step : ∀ vertex, Good vertex → ∀ callee ∈ program.successors vertex, Good callee) :
    ∀ (fuel : Nat) (found : List (Vertex Symbol)), (∀ vertex ∈ found, Good vertex) →
      ∀ vertex ∈ program.closeVertices fuel found, Good vertex
  | 0, _, good, vertex, member => good vertex member
  | fuel + 1, found, good, vertex, member => by
      unfold closeVertices Tabled.untilStable at member
      split at member
      · exact good vertex member
      · refine closeVertices_all step fuel _ (fun other inside => ?_) vertex member
        simp only [growVertices, List.mem_eraseDups, List.mem_append, List.mem_flatMap] at inside
        rcases inside with old | ⟨source, sourceMember, successor⟩
        · exact good other old
        · exact step source (good source sourceMember) other successor

omit [FreshNames Variable] in
/-- **A checked query's vertices cover**: every vertex the query and the
denials reach binds its predicate's declared inputs, since every call of a
body that scans has its inputs bound. -/
theorem covering_of_check (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol} (queryOk : QueryOk program query) :
    ∀ vertex ∈ program.vertices query, program.covering vertex = true := by
  unfold Program.vertices
  refine closeVertices_all (fun vertex covered => successors_covering wellFormed covered) _ _ ?_
  intro vertex member
  simp only [List.mem_eraseDups, List.mem_append] at member
  rcases member with fromQuery | fromDenials
  · simp only [queryVertices, List.mem_append, List.mem_flatMap, List.mem_map] at fromQuery
    rcases fromQuery with ⟨condition, conditionMember, call, inCalls, rfl⟩ | ⟨call, inCalls, rfl⟩
    · obtain ⟨declared, data, needed⟩ := queryOk.conditions condition conditionMember
      exact bodyCalls_covering (.cons declared data needed .nil) call inCalls
    · exact bodyCalls_covering queryOk.goals call inCalls
  · simp only [denialVertices, List.mem_flatMap, List.mem_map] at fromDenials
    obtain ⟨body, bodyMember, call, inCalls, rfl⟩ := fromDenials
    exact bodyCalls_covering (wellFormed.denials body bodyMember) call inCalls

open Classical in
/-- The possible answers' lists the induction supplies: a list holding every
possible answer of a vertex at these bound arguments, where one exists. -/
noncomputable def answerList (program : Program Variable Literal Symbol) (vertex : Vertex Symbol)
    (values : List (Term Variable Literal Symbol)) : List (GAtom Variable Literal Symbol) :=
  if found : ∃ answers : List (GAtom Variable Literal Symbol),
      ∀ atom, program.Ans vertex atom → boundArgs vertex.2 atom.2 = values → atom ∈ answers then
    Classical.choose found else []

omit [FreshNames Variable] in
theorem answerList_spec {vertex : Vertex Symbol} {values : List (Term Variable Literal Symbol)}
    (found : ∃ answers : List (GAtom Variable Literal Symbol),
      ∀ atom, program.Ans vertex atom → boundArgs vertex.2 atom.2 = values → atom ∈ answers) :
    ∀ atom, program.Ans vertex atom → boundArgs vertex.2 atom.2 = values → atom ∈ answerList program vertex values := by
  unfold answerList
  rw [dite_eq_left found]
  exact Classical.choose_spec found

omit [FreshNames Variable] in
/-- **Finitely many possible answers.** With the finiteness evidence and
finite guards listing their members exactly, a vertex that leaves an output
free has finitely many possible answers at each value of its bound
arguments. -/
theorem ans_finite (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol} (queryOk : QueryOk program query)
    (evidence : program.notes query = []) (enumerates : program.Enumerates) :
    ∀ vertex ∈ program.vertices query, vertex.2.free = true → ∀ values : List (Term Variable Literal Symbol),
      ∃ answers : List (GAtom Variable Literal Symbol),
        ∀ atom, program.Ans vertex atom → boundArgs vertex.2 atom.2 = values → atom ∈ answers := by
  have parts := evidence_of_notes evidence
  have covers := covering_of_check wellFormed queryOk
  suffices main : ∀ n m, ∀ vertex ∈ program.vertices query, vertex.2.free = true → ∀ values : List (Term Variable Literal Symbol),
      program.levels query vertex = n → sizeAll values = m →
        ∃ answers : List (GAtom Variable Literal Symbol),
          ∀ atom, program.Ans vertex atom → boundArgs vertex.2 atom.2 = values → atom ∈ answers from
    fun vertex member free values => main _ _ vertex member free values rfl rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihLevel =>
  intro m
  induction m using Nat.strongRecOn with
  | ind m ihSize =>
  intro vertex member free values levelEq sizeEq
  -- The candidates: every rule's enumerated instances at the bound arguments, their heads instantiated.
  let candidates : Nat × Rule Variable Literal Symbol → List (GAtom Variable Literal Symbol) := fun (_, rule) =>
    match matchAll (fun _ => none) (boundArgs vertex.2 rule.args) values with
    | some start =>
        (program.bodyEnvs (answerList program) (startNames vertex.2 rule.args) [start] rule.body).filterMap fun env =>
          (instAll env rule.args).map fun args => (rule.head, args)
    | none => []
  refine ⟨(program.rulesAt vertex).flatMap candidates, ?_⟩
  intro atom answer boundEq
  cases answer with
  | @rule _ index rule σ atVertex groundRule passes =>
      have ruleMember := rulesOf_mem (mem_rulesAt.mp atVertex).1
      have ruleOk := wellFormed.rules rule ruleMember
      refine List.mem_flatMap.mpr ⟨(index, rule), atVertex, ?_⟩
      -- The head's bound arguments match the values.
      have headData : ∀ arg ∈ boundArgs vertex.2 rule.args, dataIn program.constructors arg = true :=
        fun arg inside => ruleOk.data _ (mem_of_mem_boundArgs inside)
      obtain ⟨start, matched, startFaithful, startGives, _⟩ := matchAll_complete (σ := σ) (env := fun _ => none)
        (boundArgs vertex.2 rule.args) ((dataInAll_iff _).mpr headData) (fun _ _ none => by cases none)
      have valuesEq : (boundArgs vertex.2 rule.args).map (subst σ) = values := by
        rw [← boundArgs_map]; exact boundEq
      rw [valuesEq] at matched
      -- The body's instances, the lower-rank answers from the induction.
      have scans : Scans program (startNames vertex.2 rule.args) rule.body :=
        Scans.mono ruleOk.scans (start_covers wellFormed (covers vertex member) atVertex)
      have bodyGround : GroundOn program.constructors σ (bodyNames rule.body) := fun name occurs =>
        groundRule name (List.mem_append_right _ occurs)
      obtain ⟨next, nextMember, nextFaithful, nextGives⟩ := bodyEnvs_complete (answers := answerList program) (position := 0)
        enumerates (fun call inside calleeFree calleeAnswer => by
          obtain ⟨calleeMember, rank⟩ := call_rank parts member free atVertex inside calleeFree σ
          obtain ⟨_, goal, bound, callee⟩ := call
          simp only at calleeFree calleeAnswer calleeMember rank ⊢
          refine answerList_spec ?_ _ calleeAnswer rfl
          generalize hLevel : program.levels query callee = calleeLevel at rank
          generalize hVertexLevel : program.levels query vertex = vertexLevel at rank levelEq
          subst levelEq
          rcases rank with lower | ⟨same, smaller⟩
          · exact ihLevel calleeLevel lower _ _ calleeMember calleeFree _ hLevel rfl
          · subst same
            rw [← boundArgs_map, ← boundArgs_map, boundEq] at smaller
            exact ihSize _ (by rw [← sizeEq]; exact smaller) _ calleeMember calleeFree _ hLevel rfl)
        (List.mem_singleton.mpr rfl) startFaithful startGives scans bodyGround passes
      -- Its head is the atom.
      have headGives : Gives next σ (namesOf rule.args) := by
        intro name inside
        have bound := ruleOk.bound _ (List.mem_flatMap.mp inside).choose_spec.1 name (List.mem_flatMap.mp inside).choose_spec.2
        refine nextGives name ?_
        rcases (boundAfter_append_names _ rule.body name).mp bound with fromInputs | fromBody
        · exact (boundAfter_append_names _ rule.body name).mpr
            (.inl (start_covers wellFormed (covers vertex member) atVertex name fromInputs))
        · exact (boundAfter_append_names _ rule.body name).mpr (.inr fromBody)
      have headInst := instAll_gives (σ := σ) (env := next) rule.args ((dataInAll_iff _).mpr ruleOk.data) headGives
      simp only [candidates, matched]
      exact List.mem_filterMap.mpr ⟨next, nextMember, by simp [headInst]⟩

/-! ## Data terms -/

variable (program) in
/-- The program's ground terms: the closed data subterms of its rules, and the
members of its finite guards. -/
def groundTerms : List (Term Variable Literal Symbol) :=
  (program.rules.flatMap fun rule => groundsAll (rule.args ++ rule.body.flatMap Goal.args)) ++
    program.predicates.flatMap fun declared => (program.members declared.symbol).getD []

omit [FreshNames Variable] in
mutual
/-- A pattern's subterm stays a subterm under a substitution. -/
theorem subterm_subst_occurs {σ : Variable → Term Variable Literal Symbol} {part : Term Variable Literal Symbol} :
    ∀ term : Term Variable Literal Symbol, occurs part term = true → Subterm (subst σ part) (subst σ term)
  | .app symbol args, inside => by
      simp only [occurs, Bool.or_eq_true, decide_eq_true_eq] at inside
      rcases inside with same | deeper
      · subst same; exact .refl _
      · obtain ⟨arg, argMember, sub⟩ := subterm_subst_occursIn args deeper
        simp only [subst, substAll_eq]
        exact .arg (List.mem_map.mpr ⟨arg, argMember, rfl⟩) sub
  | .var _, inside | .lit _, inside | .truth, inside | .falsity, inside | .conj _ _, inside | .disj _ _, inside
  | .imp _ _, inside | .defaultNeg _, inside | .forallVar _ _, inside | .existsVar _ _, inside
  | .dictionaryCall _ _ _ _, inside | .equal _ _, inside => by
      simp only [occurs, decide_eq_true_eq] at inside; subst inside; exact .refl _

theorem subterm_subst_occursIn {σ : Variable → Term Variable Literal Symbol} {part : Term Variable Literal Symbol} :
    ∀ args : List (Term Variable Literal Symbol), occursIn part args = true →
      ∃ arg ∈ args, Subterm (subst σ part) (subst σ arg)
  | [], inside => by simp [occursIn] at inside
  | arg :: rest, inside => by
      simp only [occursIn, Bool.or_eq_true] at inside
      rcases inside with here | there
      · exact ⟨arg, List.mem_cons_self, subterm_subst_occurs arg here⟩
      · obtain ⟨other, member, sub⟩ := subterm_subst_occursIn rest there
        exact ⟨other, List.mem_cons_of_mem _ member, sub⟩
end

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
mutual
theorem subst_closed {σ : Variable → Term Variable Literal Symbol} :
    ∀ {term : Term Variable Literal Symbol}, closedData term = true → subst σ term = term
  | .lit _, _ => rfl
  | .app symbol args, closed => by
      simp only [closedData] at closed
      simp only [subst, substAll_closed closed]
  | .var _, closed | .truth, closed | .falsity, closed | .conj _ _, closed | .disj _ _, closed | .imp _ _, closed
  | .defaultNeg _, closed | .forallVar _ _, closed | .existsVar _ _, closed | .dictionaryCall _ _ _ _, closed
  | .equal _ _, closed => by simp [closedData] at closed

theorem substAll_closed {σ : Variable → Term Variable Literal Symbol} :
    ∀ {args : List (Term Variable Literal Symbol)}, closedDataIn args = true → substAll σ args = args
  | [], _ => rfl
  | arg :: rest, closed => by
      simp only [closedDataIn, Bool.and_eq_true] at closed
      simp only [substAll, subst_closed closed.1, substAll_closed closed.2]
end

omit [FreshNames Variable] in
mutual
/-- A name's value is a subterm of a data term's substitution. -/
theorem subterm_name {constructors : List (Constructor Literal Symbol)} {σ : Variable → Term Variable Literal Symbol}
    {name : Variable} : ∀ term : Term Variable Literal Symbol, dataIn constructors term = true → name ∈ term.freeVars →
      Subterm (σ name) (subst σ term)
  | .var other, _, occurs => by
      simp only [Term.freeVars, List.mem_singleton] at occurs; subst occurs; exact .refl _
  | .lit _, _, occurs => by simp [Term.freeVars] at occurs
  | .app symbol args, data, occurs => by
      simp only [dataIn, Bool.and_eq_true] at data
      obtain ⟨arg, argMember, sub⟩ := subterm_nameAll args data.2 (by simpa [Term.freeVars] using occurs)
      simp only [subst, substAll_eq]
      exact .arg (List.mem_map.mpr ⟨arg, argMember, rfl⟩) sub
  | .truth, data, _ | .falsity, data, _ | .conj _ _, data, _ | .disj _ _, data, _ | .imp _ _, data, _
  | .defaultNeg _, data, _ | .forallVar _ _, data, _ | .existsVar _ _, data, _ | .dictionaryCall _ _ _ _, data, _
  | .equal _ _, data, _ => by simp [dataIn] at data

theorem subterm_nameAll {constructors : List (Constructor Literal Symbol)} {σ : Variable → Term Variable Literal Symbol}
    {name : Variable} : ∀ args : List (Term Variable Literal Symbol), dataInAll constructors args = true →
      name ∈ args.flatMap Term.freeVars → ∃ arg ∈ args, Subterm (σ name) (subst σ arg)
  | [], _, occurs => by simp at occurs
  | arg :: rest, data, occurs => by
      simp only [dataInAll, Bool.and_eq_true] at data
      simp only [List.flatMap_cons, List.mem_append] at occurs
      rcases occurs with here | there
      · exact ⟨arg, List.mem_cons_self, subterm_name arg data.1 here⟩
      · obtain ⟨other, member, sub⟩ := subterm_nameAll rest data.2 there
        exact ⟨other, List.mem_cons_of_mem _ member, sub⟩
end

/-- Every name of `small` holds, at the instance, a data term of the head's
bound values and the program's ground terms. -/
def Holds (program : Program Variable Literal Symbol) (heads : List (Term Variable Literal Symbol))
    (σ : Variable → Term Variable Literal Symbol) (small : List Variable) : Prop :=
  ∀ name ∈ small, InData program.groundTerms heads (σ name)

omit [FreshNames Variable] in
/-- A term the analysis accepts holds a data term of the head's bound values
and the ground terms, at an instance. -/
theorem small_sound {frame : Frame Variable Literal Symbol}
    {σ : Variable → Term Variable Literal Symbol} {small : List Variable} (holds : Holds program (frame.heads.map (subst σ)) σ small)
    {term : Term Variable Literal Symbol} (accepted : frame.small small term = true)
    (grounded : ∀ part ∈ grounds term, part ∈ program.groundTerms) :
    InData program.groundTerms (frame.heads.map (subst σ)) (subst σ term) := by
  simp only [Frame.small, Frame.headTerm, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true] at accepted
  rcases accepted with (⟨⟨head, headMember, inside⟩, _⟩ | closed) | named
  · exact .inl ⟨subst σ head, List.mem_map.mpr ⟨head, headMember, rfl⟩, subterm_subst_occurs head inside⟩
  · rw [subst_closed closed]
    exact .inr ⟨term, grounded term (mem_grounds_self closed), .refl _⟩
  · cases term with
    | var name =>
        simp only [List.contains_iff_mem] at named
        exact holds name named
    | _ => simp at named

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem mem_zip_of_mem {α β : Type} : ∀ {first : List α} {second : List β} {item : α}, item ∈ first →
    first.length = second.length → ∃ other, (item, other) ∈ first.zip second
  | [], _, _, member, _ => by cases member
  | _ :: _, [], _, _, lengths => by simp at lengths
  | head :: rest, other :: more, item, member, lengths => by
      rcases List.mem_cons.mp member with rfl | inside
      · exact ⟨other, by simp⟩
      · obtain ⟨found, inZip⟩ := mem_zip_of_mem inside (by simpa using lengths)
        exact ⟨found, by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ inZip⟩

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem boundArgs_all {α : Type} : ∀ {pattern : Pattern} {args : List α}, (∀ flag ∈ pattern, flag = true) →
    pattern.length = args.length → boundArgs pattern args = args
  | [], [], _, _ => rfl
  | [], _ :: _, _, lengths => by simp at lengths
  | _ :: _, [], _, lengths => by simp at lengths
  | flag :: pattern, arg :: args, all, lengths => by
      have rest := boundArgs_all (pattern := pattern) (args := args) (fun other inside => all other (List.mem_cons_of_mem _ inside))
        (by simpa using lengths)
      simp only [boundArgs, List.zip_cons_cons, List.filterMap_cons, all flag List.mem_cons_self, ite_true] at rest ⊢
      rw [rest]

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem mem_boundArgs_of {α : Type} {pattern : Pattern} {args : List α} {arg : α} (member : (arg, true) ∈ args.zip pattern) :
    arg ∈ boundArgs pattern args :=
  List.mem_filterMap.mpr ⟨(arg, true), member, rfl⟩

omit [FreshNames Variable] in
/-- A name of a term the analysis accepts holds a data term. -/
theorem names_sound {σ : Variable → Term Variable Literal Symbol} {heads : List (Term Variable Literal Symbol)}
    {term : Term Variable Literal Symbol} (data : dataIn program.constructors term = true)
    (inData : InData program.groundTerms heads (subst σ term)) : ∀ name ∈ term.freeVars, InData program.groundTerms heads (σ name) :=
  fun _ occurs => inData.sub (subterm_name term data occurs)

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem guard_member {goal : Goal Variable Literal Symbol} {symbol : Symbol} {arg : Term Variable Literal Symbol}
    (same : goal = .guard symbol arg) (declared : program.declares goal = true) {members : List (Term Variable Literal Symbol)}
    (found : program.members symbol = some members) {term : Term Variable Literal Symbol} (member : term ∈ members) :
    term ∈ program.groundTerms := by
  subst same
  obtain ⟨declaredPredicate, declaredEq, _, _⟩ := kindAt_declared declared
  obtain ⟨inPredicates, symbolEq⟩ := predicate?_mem declaredEq
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨declaredPredicate, inPredicates, ?_⟩)
  rw [symbolEq, found]; exact member

/-- The flow property of a passing body: the flow keeps its names data terms. -/
def FlowSound (program : Program Variable Literal Symbol) (query : Query Variable Literal Symbol)
    (σ : Variable → Term Variable Literal Symbol) (bound : List Variable) (body : List (Goal Variable Literal Symbol)) : Prop :=
  ∀ (frame : Frame Variable Literal Symbol) (small : List Variable), frame.shadow = [] →
    (∀ goal ∈ body, ∀ arg ∈ goal.args, ∀ part ∈ grounds arg, part ∈ program.groundTerms) →
    (∀ goal ∈ body, program.declares goal = true ∧ program.data goal = true) →
    GroundOn program.constructors σ (bodyNames body) →
    Holds program (frame.heads.map (subst σ)) σ small →
    Holds program (frame.heads.map (subst σ)) σ (program.flowBody (program.dataInfo query) frame bound small body)

/-- The data property of a possible answer. -/
def AnsSound (program : Program Variable Literal Symbol) (query : Query Variable Literal Symbol) (vertex : Vertex Symbol)
    (atom : GAtom Variable Literal Symbol) : Prop :=
  (program.dataInfo query) vertex = true → ∀ arg ∈ atom.2, InData program.groundTerms (boundArgs vertex.2 atom.2) arg

omit [FreshNames Variable] in
/-- The flow through a call that leaves an output free. -/
theorem flow_free {query : Query Variable Literal Symbol} {σ : Variable → Term Variable Literal Symbol} {bound : List Variable}
    {goal : Goal Variable Literal Symbol} {rest : List (Goal Variable Literal Symbol)} {vertex : Vertex Symbol}
    (found : goal.vertex? bound = some vertex) (free : vertex.2.free = true)
    (answerSound : AnsSound program query vertex (vertex.1, goal.args.map (subst σ)))
    (restFlow : FlowSound program query σ (after bound goal) rest) : FlowSound program query σ bound (goal :: rest) := by
  intro frame small noShadow grounded ok ground holds
  simp only [flowBody]
  have restGrounded := fun other inside => grounded other (List.mem_cons_of_mem _ inside)
  have restOk := fun other inside => ok other (List.mem_cons_of_mem _ inside)
  have restGround : GroundOn program.constructors σ (bodyNames rest) := fun name occurs =>
    ground name (by simp only [bodyNames, List.flatMap_cons, List.mem_append]; exact .inr occurs)
  apply restFlow frame _ noShadow restGrounded restOk restGround
  cases goal with
  | call predicate args =>
      simp only [Goal.vertex?, Option.some.injEq] at found
      subst found
      simp only [flowGoal]
      split
      · rename_i accepted
        simp only [Bool.and_eq_true, List.all_eq_true] at accepted
        have argsData : ∀ arg ∈ args, dataIn program.constructors arg = true :=
          List.all_eq_true.mp (ok _ List.mem_cons_self).2
        have answerData := answerSound accepted.1
        intro name member
        rcases List.mem_append.mp member with old | new
        · exact holds name old
        · obtain ⟨arg, argMember, occurs⟩ := List.mem_flatMap.mp new
          have argInData := answerData (subst σ arg) (List.mem_map.mpr ⟨arg, argMember, rfl⟩)
          have boundInData : ∀ value ∈ boundArgs (patternOf bound args) (args.map (subst σ)),
              InData program.groundTerms (frame.heads.map (subst σ)) value := by
            intro value valueMember
            rw [boundArgs_map] at valueMember
            obtain ⟨boundArg, boundMember, rfl⟩ := List.mem_map.mp valueMember
            exact small_sound holds (accepted.2 boundArg boundMember) fun part partMember =>
              grounded _ List.mem_cons_self boundArg (mem_of_mem_boundArgs boundMember) part partMember
          exact (argInData.trans boundInData).sub (subterm_name arg (argsData arg argMember) occurs)
      · exact holds
  | naf predicate args =>
      simp only [Goal.vertex?, Option.some.injEq] at found
      subst found
      rw [full_not_free] at free; cases free
  | equal _ _ | differ _ _ | guard _ _ | primitive _ _ _ | marker _ _ => simp [Goal.vertex?] at found

omit [FreshNames Variable] in
/-- The flow through a literal that leaves no output free. -/
theorem flow_fixed (enumerates : program.Enumerates) {query : Query Variable Literal Symbol}
    {σ : Variable → Term Variable Literal Symbol} {bound : List Variable} {goal : Goal Variable Literal Symbol}
    {rest : List (Goal Variable Literal Symbol)} (notFree : ∀ vertex, goal.vertex? bound = some vertex → vertex.2.free = false)
    (fixed : program.fixedAt σ goal) (restFlow : FlowSound program query σ (after bound goal) rest) :
    FlowSound program query σ bound (goal :: rest) := by
  intro frame small noShadow grounded ok ground holds
  simp only [flowBody]
  have restGrounded := fun other inside => grounded other (List.mem_cons_of_mem _ inside)
  have restOk := fun other inside => ok other (List.mem_cons_of_mem _ inside)
  have restGround : GroundOn program.constructors σ (bodyNames rest) := fun name occurs =>
    ground name (by simp only [bodyNames, List.flatMap_cons, List.mem_append]; exact .inr occurs)
  apply restFlow frame _ noShadow restGrounded restOk restGround
  have goalData : ∀ arg ∈ goal.args, dataIn program.constructors arg = true :=
    List.all_eq_true.mp (ok goal List.mem_cons_self).2
  have argSound : ∀ arg ∈ goal.args, frame.small small arg = true →
      InData program.groundTerms (frame.heads.map (subst σ)) (subst σ arg) := fun arg member accepted =>
    small_sound holds accepted (grounded goal List.mem_cons_self arg member)
  cases goal with
  | call predicate args =>
      simp only [flowGoal]
      split
      · rename_i accepted
        simp only [Bool.and_eq_true, List.all_eq_true] at accepted
        have notFreePattern := notFree _ rfl
        have allBound : boundArgs (patternOf bound args) args = args := by
          simp only [Pattern.free, List.any_eq_false, beq_iff_eq] at notFreePattern
          exact boundArgs_all (fun flag inside => by
            cases flag
            · exact absurd rfl (notFreePattern false inside)
            · rfl) (length_patternOf bound args)
        intro name member
        rcases List.mem_append.mp member with old | new
        · exact holds name old
        · obtain ⟨arg, argMember, occurs⟩ := List.mem_flatMap.mp new
          exact names_sound (goalData arg argMember)
            (argSound arg argMember (accepted.2 arg (by rw [allBound]; exact argMember))) name occurs
      · exact holds
  | equal left right =>
      simp only [fixedAt] at fixed
      simp only [flowGoal]
      intro name member
      simp only [List.mem_append] at member
      rcases member with (old | fromLeft) | fromRight
      · exact holds name old
      · split at fromLeft
        · rename_i accepted
          have leftData := goalData left (by simp [Goal.args])
          have rightData := goalData right (by simp [Goal.args])
          have leftInData := argSound left (by simp [Goal.args]) accepted
          rw [fixed] at leftInData
          exact names_sound rightData leftInData name fromLeft
        · cases fromLeft
      · split at fromRight
        · rename_i accepted
          have leftData := goalData left (by simp [Goal.args])
          have rightInData := argSound right (by simp [Goal.args]) accepted
          rw [← fixed] at rightInData
          exact names_sound leftData rightInData name fromRight
        · cases fromRight
  | guard symbol arg =>
      simp only [fixedAt] at fixed
      simp only [flowGoal]
      split
      · rename_i binding
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at binding
        obtain ⟨members, membersEq⟩ := Option.isSome_iff_exists.mp binding.1
        have argData := goalData arg (by simp [Goal.args])
        have argGround := groundIn_subst arg argData fun name occurs =>
          ground name (by simpa [bodyNames, Goal.names, Goal.args, namesOf] using Or.inl occurs)
        have member := ((enumerates symbol members (ok _ List.mem_cons_self).1 membersEq).2 _).mp fixed
        have constant := guard_member rfl (ok _ List.mem_cons_self).1 membersEq member
        intro name inside
        rcases List.mem_append.mp inside with old | new
        · exact holds name old
        · exact names_sound argData (.inr ⟨_, constant, .refl _⟩) name new
      · exact holds
  | naf _ _ | differ _ _ | primitive _ _ _ | marker _ _ => exact holds

omit [FreshNames Variable] in
/-- **Data-term outputs are sound for possible answers**: a possible answer of
a vertex with data-term outputs has every argument a data term of its bound
arguments and the program's ground terms. -/
theorem ans_data {query : Query Variable Literal Symbol} (wellFormed : program.WellFormed) (enumerates : program.Enumerates)
    {vertex : Vertex Symbol} {atom : GAtom Variable Literal Symbol} (answer : program.Ans vertex atom) :
    AnsSound program query vertex atom := by
  refine Ans.rec (motive_1 := fun vertex atom _ => AnsSound program query vertex atom)
    (motive_2 := fun σ bound body _ => FlowSound program query σ bound body) ?_ ?_ ?_ ?_ answer
  · intro vertex index rule σ atVertex groundRule passes bodyFlow isData
    have ruleMember := rulesOf_mem (mem_rulesAt.mp atVertex).1
    have ruleOk := wellFormed.rules rule ruleMember
    have lengths := (mem_rulesAt.mp atVertex).2
    have post := greatest_post (ok := program.outputsOk) (vertices := program.vertices query) vertex
      (List.contains_iff_mem.mp isData)
    simp only [outputsOk, List.all_eq_true] at post
    have ruleOutputs := post (index, rule) atVertex
    have flowEnd := bodyFlow (frameAt vertex.2 rule) [] rfl
      (fun goal inside arg argMember part partMember => List.mem_append_left _ (List.mem_flatMap.mpr ⟨rule, ruleMember,
        groundsAll_sub (List.mem_append_right _ (List.mem_flatMap.mpr ⟨goal, inside, argMember⟩)) part partMember⟩))
      (Scans.goals ruleOk.scans) (fun name occurs => groundRule name (List.mem_append_right _ occurs))
      (fun _ none => by cases none)
    intro arg argMember
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp argMember
    obtain ⟨flag, inZip⟩ := mem_zip_of_mem originalMember lengths
    have headsEq : (frameAt vertex.2 rule).heads.map (subst σ) = boundArgs vertex.2 (rule.args.map (subst σ)) := by
      simp [frameAt, boundArgs_map]
    cases flag with
    | true =>
        exact .inl ⟨subst σ original, by rw [boundArgs_map]; exact List.mem_map.mpr ⟨original, mem_boundArgs_of inZip, rfl⟩,
          .refl _⟩
    | false =>
        have accepted := ruleOutputs (original, false) inZip
        simp only [Bool.false_or] at accepted
        rw [← headsEq]
        exact small_sound flowEnd accepted fun part partMember => List.mem_append_left _ (List.mem_flatMap.mpr
          ⟨rule, ruleMember, groundsAll_sub (List.mem_append_left _ originalMember) part partMember⟩)

  · intro σ bound frame small _ _ _ _ holds; exact holds
  · intro σ bound goal rest vertex found free _ _ answerSound restFlow
    exact flow_free found free answerSound restFlow
  · intro σ bound goal rest notFree fixed _ restFlow
    exact flow_fixed enumerates notFree fixed restFlow

omit [FreshNames Variable] in
/-- The flow keeps its names data terms along a passing instance. -/
theorem passes_flow {query : Query Variable Literal Symbol} (wellFormed : program.WellFormed) (enumerates : program.Enumerates)
    {σ : Variable → Term Variable Literal Symbol} {bound : List Variable} {body : List (Goal Variable Literal Symbol)}
    (passes : program.Passes σ bound body) : FlowSound program query σ bound body := by
  refine Passes.rec (motive_1 := fun _ _ _ => True) (motive_2 := fun σ bound body _ => FlowSound program query σ bound body)
    (fun _ _ _ _ => trivial) ?_ ?_ ?_ passes
  · intro σ bound frame small _ _ _ _ holds; exact holds
  · intro σ bound goal rest vertex found free answer _ _ restFlow
    exact flow_free found free (ans_data wellFormed enumerates answer) restFlow
  · intro σ bound goal rest notFree fixed _ restFlow
    exact flow_fixed enumerates notFree fixed restFlow

omit [FreshNames Variable] in
/-- One literal of a passing instance keeps the flow's names data terms. -/
theorem flow_step {query : Query Variable Literal Symbol} (wellFormed : program.WellFormed) (enumerates : program.Enumerates)
    {σ : Variable → Term Variable Literal Symbol} {bound : List Variable} {goal : Goal Variable Literal Symbol}
    {rest : List (Goal Variable Literal Symbol)} (passes : program.Passes σ bound (goal :: rest))
    (frame : Frame Variable Literal Symbol) (small : List Variable) (noShadow : frame.shadow = [])
    (grounded : ∀ arg ∈ goal.args, ∀ part ∈ grounds arg, part ∈ program.groundTerms)
    (ok : program.declares goal = true ∧ program.data goal = true) (ground : GroundOn program.constructors σ goal.names)
    (holds : Holds program (frame.heads.map (subst σ)) σ small) :
    Holds program (frame.heads.map (subst σ)) σ (program.flowGoal (program.dataInfo query) frame bound small goal) := by
  have nilFlow : FlowSound program query σ (after bound goal) [] := fun _ _ _ _ _ _ holds => holds
  have single : FlowSound program query σ bound [goal] := by
    cases passes with
    | free found free answer _ => exact flow_free found free (ans_data wellFormed enumerates answer) nilFlow
    | fixed notFree fixed _ => exact flow_fixed enumerates notFree fixed nilFlow
  exact single frame small noShadow (fun other inside => by rcases List.mem_singleton.mp inside with rfl; exact grounded)
    (fun other inside => by rcases List.mem_singleton.mp inside with rfl; exact ok)
    (fun name occurs => ground name (by simpa [bodyNames] using occurs)) holds

omit [FreshNames Variable] in
/-- Every call of a passing instance is in the flow's calls, with names that
hold data terms. -/
theorem flowCalls_of_bodyCalls {query : Query Variable Literal Symbol} (wellFormed : program.WellFormed)
    (enumerates : program.Enumerates) {σ : Variable → Term Variable Literal Symbol} (frame : Frame Variable Literal Symbol)
    (noShadow : frame.shadow = []) :
    ∀ {position : Nat} {bound small : List Variable} {body : List (Goal Variable Literal Symbol)},
      program.Passes σ bound body →
      (∀ goal ∈ body, ∀ arg ∈ goal.args, ∀ part ∈ grounds arg, part ∈ program.groundTerms) →
      (∀ goal ∈ body, program.declares goal = true ∧ program.data goal = true) →
      GroundOn program.constructors σ (bodyNames body) → Holds program (frame.heads.map (subst σ)) σ small →
      ∀ call ∈ bodyCalls position bound body, ∃ small', Holds program (frame.heads.map (subst σ)) σ small' ∧
        (call.1, call.2.1, call.2.2.1, small', call.2.2.2) ∈
          program.flowCalls (program.dataInfo query) frame position bound small body
  | _, _, _, [], _, _, _, _, _, _, member => by cases member
  | position, bound, small, goal :: rest, passes, grounded, ok, ground, holds, call, member => by
      simp only [bodyCalls, List.mem_append] at member
      rcases member with here | there
      · cases found : goal.vertex? bound with
        | none => rw [found] at here; cases here
        | some vertex =>
            rw [found] at here
            rcases List.mem_singleton.mp here with rfl
            exact ⟨small, holds, by simp [flowCalls, found]⟩
      · have restPasses : program.Passes σ (after bound goal) rest := by
          cases passes with
          | free _ _ _ restPasses => exact restPasses
          | fixed _ _ restPasses => exact restPasses
        have stepHolds := flow_step (query := query) wellFormed enumerates passes frame small noShadow
          (grounded goal List.mem_cons_self) (ok goal List.mem_cons_self)
          (fun name occurs => ground name (List.mem_flatMap.mpr ⟨goal, List.mem_cons_self, occurs⟩)) holds
        obtain ⟨small', holds', inFlow⟩ := flowCalls_of_bodyCalls (query := query) wellFormed enumerates frame noShadow
          restPasses (fun other inside => grounded other (List.mem_cons_of_mem _ inside))
          (fun other inside => ok other (List.mem_cons_of_mem _ inside))
          (fun name occurs => ground name (by simp only [bodyNames, List.flatMap_cons, List.mem_append]; exact .inr occurs))
          stepHolds call there
        exact ⟨small', holds', by simp only [flowCalls, List.mem_append]; exact .inr inFlow⟩

omit [FreshNames Variable] in
/-- **Calls at their caller's level keep to the data terms.** With the
evidence, a call a passing instance of a vertex makes at the vertex's level
has bound values that are data terms of the instance's bound head values and
the program's ground terms. -/
theorem same_level_data {query : Query Variable Literal Symbol} (wellFormed : program.WellFormed)
    (evidence : program.notes query = []) (enumerates : program.Enumerates) {vertex : Vertex Symbol}
    (member : vertex ∈ program.vertices query) {index : Nat} {rule : Rule Variable Literal Symbol}
    (atVertex : (index, rule) ∈ program.rulesAt vertex) {σ : Variable → Term Variable Literal Symbol}
    (groundRule : GroundOn program.constructors σ rule.names)
    (passes : program.Passes σ (startNames vertex.2 rule.args) rule.body)
    {call : Nat × Goal Variable Literal Symbol × List Variable × Vertex Symbol}
    (inCalls : call ∈ bodyCalls 0 (startNames vertex.2 rule.args) rule.body)
    (sameLevel : program.levels query call.2.2.2 = program.levels query vertex) :
    ∀ value ∈ boundArgs call.2.2.2.2 (call.2.1.args.map (subst σ)),
      InData program.groundTerms (boundArgs vertex.2 (rule.args.map (subst σ))) value := by
  have growingClean := (evidence_of_notes evidence).bounded
  have ruleMember := rulesOf_mem (mem_rulesAt.mp atVertex).1
  have ruleOk := wellFormed.rules rule ruleMember
  have groundedBody : ∀ goal ∈ rule.body, ∀ arg ∈ goal.args, ∀ part ∈ grounds arg, part ∈ program.groundTerms :=
    fun goal inside arg argMember part partMember => List.mem_append_left _ (List.mem_flatMap.mpr ⟨rule, ruleMember,
      groundsAll_sub (List.mem_append_right _ (List.mem_flatMap.mpr ⟨goal, inside, argMember⟩)) part partMember⟩)
  obtain ⟨small, holds, inFlow⟩ := flowCalls_of_bodyCalls (query := query) wellFormed enumerates (frameAt vertex.2 rule) rfl
    (position := 0) (small := []) passes groundedBody (Scans.goals ruleOk.scans) (fun name occurs => groundRule name (List.mem_append_right _ occurs))
    (fun _ none => by cases none) call inCalls
  obtain ⟨position, goal, bound, callee⟩ := call
  simp only at sameLevel inFlow ⊢
  have accepted : (boundArgs callee.2 goal.args).all ((frameAt vertex.2 rule).small small) = true := by
    unfold growingIn at growingClean
    simp only [List.flatMap_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff] at growingClean
    have := growingClean vertex member (index, rule) atVertex _ inFlow
    simp only [sameLevel, beq_self_eq_true, Bool.true_and, Bool.not_eq_true'] at this
    cases allSmall : (boundArgs callee.2 goal.args).all ((frameAt vertex.2 rule).small small)
    · rw [allSmall] at this; exact absurd rfl this
    · rfl
  have goalMember := (mem_bodyCalls inCalls).1
  intro value valueMember
  rw [boundArgs_map] at valueMember
  obtain ⟨arg, argMember, rfl⟩ := List.mem_map.mp valueMember
  have headsEq : (frameAt vertex.2 rule).heads.map (subst σ) = boundArgs vertex.2 (rule.args.map (subst σ)) := by
    simp [frameAt, boundArgs_map]
  rw [← headsEq]
  exact small_sound holds (List.all_eq_true.mp accepted arg argMember) fun part partMember =>
    groundedBody goal goalMember arg (mem_of_mem_boundArgs argMember) part partMember

end Program

end AnthillModKbSpec.IR
