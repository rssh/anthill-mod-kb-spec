import AnthillModKbSpec.Resolution.IR.RelevantProgram
import AnthillModKbSpec.Resolution.P0.Strategy

/-! # S07's ground programs in the IR (S27)

S07's `P0.Ground` embeds as the IR's ground acyclic case: each clause becomes
a rule, each context atom a fact, the goal the query's literals, every
predicate declared defined at its arity, every constructor of the data
declared (`Program.ofGround`, `Query.ofGround`). An atom is a call, the NAF of
an atom a NAF literal; conjunctions and truth flatten. A rule's body holds
exactly when its clause's body does, in every model (`satisfies_ofBody`), and
a clause of atoms and NAF of atoms renders back to itself
(`ofClause_toClause`). The embedding passes the checker, has no note, and
S07's rank witness makes it acyclic (`ofGround_p0`).

`embedGround` embeds only where the IR keeps the input's meaning
(`P0Ground.faithful`): NAF of a compound goal and `falsity` have no IR literal
(they lower to auxiliary predicates, S30); the KB's unknown markers, which S07
reads closed, are free atoms in the IR; and IR declarations are keyed by
symbol, so each predicate symbol has one arity (S29's translation renames the
others). An embedded input classifies P0 (`embedGround_p0`). S07 reads its
context as atoms added to the program, and so does the embedding; which
reading a context gets is S26's to settle. -/

namespace AnthillModKbSpec.IR

open Completion Tabled Admission Answers GroundSearch

variable {Variable Literal Symbol : Type}

/-! ## The translation -/

/-- A goal the IR's literals express: atoms, truth, conjunctions, and the NAF
of an atom. -/
def atomicGoal : Term Variable Literal Symbol → Bool
  | .app _ _ | .truth => true
  | .conj left right => atomicGoal left && atomicGoal right
  | .defaultNeg (.app _ _) => true
  | _ => false

/-- A ground goal as IR literals: an atom is a call, the NAF of an atom a NAF
literal, a conjunction its parts, truth nothing. -/
def ofGoal : Term Variable Literal Symbol → List (Goal Variable Literal Symbol)
  | .app symbol args => [.call symbol args]
  | .conj left right => ofGoal left ++ ofGoal right
  | .defaultNeg (.app symbol args) => [.naf symbol args]
  | _ => []

/-- A clause as a rule. -/
def ofClause : HornClause Variable Literal Symbol → Option (Rule Variable Literal Symbol)
  | .definite (.app symbol args) body => some ⟨symbol, args, body.flatMap ofGoal⟩
  | _ => none

/-- A context atom as a fact. -/
def ofFact : Term Variable Literal Symbol → Option (Rule Variable Literal Symbol)
  | .app symbol args => some ⟨symbol, args, []⟩
  | _ => none


variable {hoApplySymbol : Symbol}

namespace P0Ground

variable (ground : P0.Ground Variable Literal Symbol hoApplySymbol)

/-- The rules: the clauses' and the context's facts. -/
def rules : List (Rule Variable Literal Symbol) :=
  ground.program.clauses.filterMap ofClause ++ ground.context.assumptions.filterMap ofFact

/-- The query's literals. -/
def goals : List (Goal Variable Literal Symbol) := ofGoal ground.goal

/-- Each atom's predicate with its arity. -/
def sites : List (Symbol × Nat) :=
  ((rules ground).flatMap fun rule => (rule.head, rule.args.length) :: rule.body.filterMap Goal.site?) ++
    (goals ground).filterMap Goal.site?

/-- The constructors of every atom's arguments. -/
def constructors : List (Constructor Literal Symbol) :=
  ((rules ground).flatMap fun rule => dataConstructorsOf rule.args ++ rule.body.flatMap fun goal => dataConstructorsOf goal.args) ++
    (goals ground).flatMap fun goal => dataConstructorsOf goal.args

end P0Ground

variable [DecidableEq Symbol]

/-- **The IR program of a ground input**: its rules, every predicate defined
at its arity with input modes, every constructor of its data, no denial, no
derived rule, no guard or primitive. It keeps the input's meaning only where
`P0Ground.faithful` says so; `embedGround` checks it. -/
def Program.ofGround (ground : P0.Ground Variable Literal Symbol hoApplySymbol) : Program Variable Literal Symbol :=
  ⟨(P0Ground.sites ground).eraseDups.map fun site => ⟨site.1, List.replicate site.2 .input, .defined⟩,
    P0Ground.constructors ground, P0Ground.rules ground, [], [], fun _ _ => false, fun _ => none, fun _ _ => none, hoApplySymbol⟩

/-- The query of a ground input: its goal's literals, no condition, no answer
name. -/
def Query.ofGround (ground : P0.Ground Variable Literal Symbol hoApplySymbol) : Query Variable Literal Symbol :=
  ⟨[], P0Ground.goals ground, []⟩

/-! ## Faithfulness -/

/-- An atom or the NAF of an atom. -/
def flatLiteral : Term Variable Literal Symbol → Bool
  | .app _ _ | .defaultNeg (.app _ _) => true
  | _ => false

omit [DecidableEq Symbol] in
theorem ofGoal_flat {goal : Term Variable Literal Symbol} (flat : flatLiteral goal = true) :
    (ofGoal goal).map Goal.toTerm = [goal] := by
  match goal, flat with
  | .app _ _, _ => rfl
  | .defaultNeg (.app _ _), _ => rfl

omit [DecidableEq Symbol] in
/-- **A clause of atoms and NAF of atoms renders back to itself.** -/
theorem ofClause_toClause {symbol : Symbol} {args : List (Term Variable Literal Symbol)} {body : List (Term Variable Literal Symbol)}
    (flat : ∀ goal ∈ body, flatLiteral goal = true) :
    (ofClause (.definite (.app symbol args) body)).map Rule.toClause = some (.definite (.app symbol args) body) := by
  simp only [ofClause, Option.map_some, Rule.toClause, Option.some.injEq, HornClause.definite.injEq, true_and]
  induction body with
  | nil => rfl
  | cons goal rest ih =>
      rw [List.flatMap_cons, List.map_append, ofGoal_flat (flat goal List.mem_cons_self),
        ih fun other inside => flat other (List.mem_cons_of_mem _ inside)]
      rfl

/-! ## Ground data -/

section Data

variable [DecidableEq Variable] [DecidableEq Literal]

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem freeVars_of_isData {term : Term Variable Literal Symbol} (data : IsData term) : term.freeVars = [] := by
  induction data with
  | lit => simp [Term.freeVars]
  | app _ ih => simp only [Term.freeVars, List.flatMap_eq_nil_iff]; exact ih

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem closedDataIn_of {args : List (Term Variable Literal Symbol)} :
    (∀ arg ∈ args, closedData arg = true) → closedDataIn args = true := by
  induction args with
  | nil => intro; rfl
  | cons arg rest ih =>
      intro each
      simp only [closedDataIn, Bool.and_eq_true]
      exact ⟨each arg List.mem_cons_self, ih fun other inside => each other (List.mem_cons_of_mem _ inside)⟩

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem closedData_of_isData {term : Term Variable Literal Symbol} (data : IsData term) : closedData term = true := by
  induction data with
  | lit => rfl
  | app _ ih => simp only [closedData]; exact closedDataIn_of ih

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem mem_dataConstructorsOf {constructor : Constructor Literal Symbol} {arg : Term Variable Literal Symbol} :
    ∀ {args : List (Term Variable Literal Symbol)}, arg ∈ args → constructor ∈ dataConstructors arg → constructor ∈ dataConstructorsOf args
  | [], member, _ => by cases member
  | first :: rest, member, inside => by
      simp only [dataConstructorsOf, List.mem_append]
      rcases List.mem_cons.mp member with rfl | later
      · exact .inl inside
      · exact .inr (mem_dataConstructorsOf later inside)

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem mem_dataConstructorsOf_iff {constructor : Constructor Literal Symbol} :
    ∀ {args : List (Term Variable Literal Symbol)},
      constructor ∈ dataConstructorsOf args ↔ ∃ arg ∈ args, constructor ∈ dataConstructors arg
  | [] => by simp [dataConstructorsOf]
  | first :: rest => by
      simp only [dataConstructorsOf, List.mem_append, List.mem_cons, exists_eq_or_imp, mem_dataConstructorsOf_iff (args := rest)]

omit [DecidableEq Variable] in
theorem argsBlockers_nil_of {program : Program Variable Literal Symbol} {site : Site} {path : List Nat} :
    ∀ {index : Nat} {args : List (Term Variable Literal Symbol)},
      (∀ arg ∈ args, ∀ path, program.dataBlockers site path arg = []) → program.argsBlockers site path index args = []
  | _, [], _ => by simp [Program.argsBlockers]
  | index, arg :: rest, each => by
      simp only [Program.argsBlockers, List.append_eq_nil_iff]
      exact ⟨each arg List.mem_cons_self _, argsBlockers_nil_of fun other inside => each other (List.mem_cons_of_mem _ inside)⟩

omit [DecidableEq Variable] in
/-- An ordinary ground data term whose constructors are declared has no
blocker. -/
theorem dataBlockers_ground {program : Program Variable Literal Symbol} {term : Term Variable Literal Symbol}
    (data : IsData term) (ordinary : Machine.Ordinary program.hoApply term)
    (declared : ∀ constructor ∈ dataConstructors term, constructor ∈ program.constructors) :
    ∀ site path, program.dataBlockers site path term = [] := by
  induction data with
  | @lit value =>
      intro site path
      have inside := declared (.literal value) (by simp [dataConstructors])
      simp [Program.dataBlockers, inside]
  | @app args symbol _ ih =>
      intro site path
      cases ordinary with
      | app different argsOrdinary =>
          have inside := declared (.application symbol args.length) (by simp [dataConstructors])
          simp only [Program.dataBlockers, different, ite_false, inside, ite_true]
          exact argsBlockers_nil_of fun arg member path => ih arg member (argsOrdinary arg member)
            (fun constructor found => declared constructor (by
              simp only [dataConstructors, List.mem_cons]; exact .inr (mem_dataConstructorsOf member found))) site path

end Data

/-! ## The embedding's literals and rules -/

/-- A literal of the embedding: a call or the NAF of an atom of an ordinary
predicate, over ordinary ground data. -/
def GroundLiteral (hoApplySymbol : Symbol) (goal : Goal Variable Literal Symbol) : Prop :=
  ∃ symbol args, (goal = .call symbol args ∨ goal = .naf symbol args) ∧ symbol ≠ hoApplySymbol ∧
    ∀ arg ∈ args, IsData arg ∧ Machine.Ordinary hoApplySymbol arg

omit [DecidableEq Symbol] in
theorem ofGoal_literal {goal : Term Variable Literal Symbol} (valid : IsGoal hoApplySymbol goal)
    (ordinary : Machine.Ordinary hoApplySymbol goal) : ∀ literal ∈ ofGoal goal, GroundLiteral hoApplySymbol literal := by
  induction valid with
  | @atom atom ground =>
      cases ground with
      | app different data =>
          intro literal member
          simp only [ofGoal, List.mem_singleton] at member
          subst member
          cases ordinary with
          | app _ argsOrdinary => exact ⟨_, _, .inl rfl, different, fun arg inside => ⟨data arg inside, argsOrdinary arg inside⟩⟩
  | truth => intro _ member; simp [ofGoal] at member
  | falsity => intro _ member; simp [ofGoal] at member
  | conj _ _ leftIh rightIh =>
      cases ordinary with
      | conj first second =>
          intro literal member
          simp only [ofGoal, List.mem_append] at member
          rcases member with inLeft | inRight
          · exact leftIh first literal inLeft
          · exact rightIh second literal inRight
  | @defaultNeg body inner _ =>
      cases ordinary with
      | defaultNeg innerOrdinary =>
          intro literal member
          cases inner with
          | atom ground =>
              cases ground with
              | app different data =>
                  simp only [ofGoal, List.mem_singleton] at member
                  subst member
                  cases innerOrdinary with
                  | app _ argsOrdinary =>
                      exact ⟨_, _, .inr rfl, different, fun arg inside => ⟨data arg inside, argsOrdinary arg inside⟩⟩
          | truth | falsity | conj _ _ | defaultNeg _ => simp [ofGoal] at member

namespace P0Ground

variable (ground : P0.Ground Variable Literal Symbol hoApplySymbol)

omit [DecidableEq Symbol] in
/-- The embedding's rules: ordinary ground heads, and bodies of its literals. -/
theorem rules_ground {rule : Rule Variable Literal Symbol} (member : rule ∈ rules ground) :
    rule.head ≠ hoApplySymbol ∧ (∀ arg ∈ rule.args, IsData arg ∧ Machine.Ordinary hoApplySymbol arg) ∧
      ∀ literal ∈ rule.body, GroundLiteral hoApplySymbol literal := by
  rcases List.mem_append.mp member with fromClauses | fromFacts
  · obtain ⟨clause, clauseMember, translated⟩ := List.mem_filterMap.mp fromClauses
    have valid := ground.program.wellFormed clause clauseMember
    have ordinary := ground.clausesOrdinary clause clauseMember
    cases valid with
    | @definite atom goals head body =>
        cases head with
        | app different data =>
            simp only [ofClause, Option.some.injEq] at translated
            subst translated
            obtain ⟨headOrdinary, bodyOrdinary⟩ := ordinary
            cases headOrdinary with
            | app _ argsOrdinary =>
                refine ⟨different, fun arg inside => ⟨data arg inside, argsOrdinary arg inside⟩, fun literal inside => ?_⟩
                obtain ⟨goal, goalMember, literalMember⟩ := List.mem_flatMap.mp inside
                exact ofGoal_literal (body goal goalMember) (bodyOrdinary goal goalMember) literal literalMember
  · obtain ⟨atom, atomMember, translated⟩ := List.mem_filterMap.mp fromFacts
    have valid := ground.context.wellFormed atom atomMember
    have ordinary := ground.contextOrdinary atom atomMember
    cases valid with
    | app different data =>
        simp only [ofFact, Option.some.injEq] at translated
        subst translated
        cases ordinary with
        | app _ argsOrdinary =>
            exact ⟨different, fun arg inside => ⟨data arg inside, argsOrdinary arg inside⟩, fun _ inside => by cases inside⟩

omit [DecidableEq Symbol] in
theorem goals_ground : ∀ literal ∈ goals ground, GroundLiteral hoApplySymbol literal :=
  ofGoal_literal ground.valid ground.ordinary

end P0Ground

/-! ## The embedding classifies P0 -/

section Classify

variable [DecidableEq Variable] [DecidableEq Literal] (ground : P0.Ground Variable Literal Symbol hoApplySymbol)

attribute [local instance] Machine.termEq

namespace P0Ground

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem literal_names {literal : Goal Variable Literal Symbol} (ground : GroundLiteral hoApplySymbol literal) :
    ∀ arg ∈ literal.args, arg.freeVars = [] := by
  obtain ⟨_, _, form, _, args⟩ := ground
  rcases form with rfl | rfl <;> exact fun arg inside => freeVars_of_isData (args arg inside).1

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem namesOf_nil {terms : List (Term Variable Literal Symbol)} [DecidableEq Variable]
    (each : ∀ term ∈ terms, term.freeVars = []) : namesOf terms = [] :=
  List.flatMap_eq_nil_iff.mpr each

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem rule_names {rule : Rule Variable Literal Symbol} (member : rule ∈ rules ground) : rule.names = [] := by
  obtain ⟨_, args, body⟩ := rules_ground ground member
  simp only [Rule.names, List.append_eq_nil_iff]
  refine ⟨namesOf_nil fun arg inside => freeVars_of_isData (args arg inside).1, List.flatMap_eq_nil_iff.mpr fun literal inside => ?_⟩
  exact namesOf_nil (literal_names (body literal inside))

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem goals_names : bodyNames (goals ground) = [] :=
  List.flatMap_eq_nil_iff.mpr fun literal inside => namesOf_nil (literal_names (goals_ground ground literal inside))

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem literal_site {literal : Goal Variable Literal Symbol} (ground : GroundLiteral hoApplySymbol literal) :
    ∃ symbol, symbol ≠ hoApplySymbol ∧ literal.site? = some (symbol, literal.args.length) := by
  obtain ⟨symbol, _, form, different, _⟩ := ground
  rcases form with rfl | rfl <;> exact ⟨symbol, different, rfl⟩

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem head_site {rule : Rule Variable Literal Symbol} (member : rule ∈ rules ground) :
    (rule.head, rule.args.length) ∈ sites ground :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨rule, member, List.mem_cons_self⟩)

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem body_site {rule : Rule Variable Literal Symbol} (member : rule ∈ rules ground) {literal : Goal Variable Literal Symbol}
    (inside : literal ∈ rule.body) {site : Symbol × Nat} (found : literal.site? = some site) : site ∈ sites ground :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨rule, member, List.mem_cons_of_mem _ (List.mem_filterMap.mpr ⟨literal, inside, found⟩)⟩)

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem goal_site {literal : Goal Variable Literal Symbol} (inside : literal ∈ goals ground) {site : Symbol × Nat}
    (found : literal.site? = some site) : site ∈ sites ground :=
  List.mem_append_right _ (List.mem_filterMap.mpr ⟨literal, inside, found⟩)

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
/-- Every site's symbol is an ordinary predicate's. -/
theorem site_ordinary {site : Symbol × Nat} (member : site ∈ sites ground) : site.1 ≠ hoApplySymbol := by
  rcases List.mem_append.mp member with fromRules | fromGoals
  · obtain ⟨rule, ruleMember, inside⟩ := List.mem_flatMap.mp fromRules
    obtain ⟨different, _, body⟩ := rules_ground ground ruleMember
    rcases List.mem_cons.mp inside with rfl | fromBody
    · exact different
    · obtain ⟨literal, literalMember, found⟩ := List.mem_filterMap.mp fromBody
      obtain ⟨symbol, symbolDifferent, siteEq⟩ := literal_site (body literal literalMember)
      rw [siteEq] at found
      cases found
      exact symbolDifferent
  · obtain ⟨literal, literalMember, found⟩ := List.mem_filterMap.mp fromGoals
    obtain ⟨symbol, symbolDifferent, siteEq⟩ := literal_site (goals_ground ground literal literalMember)
    rw [siteEq] at found
    cases found
    exact symbolDifferent

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem rule_constructors {rule : Rule Variable Literal Symbol} (member : rule ∈ rules ground) :
    (∀ arg ∈ rule.args, ∀ constructor ∈ dataConstructors arg, constructor ∈ constructors ground) ∧
      ∀ literal ∈ rule.body, ∀ arg ∈ literal.args, ∀ constructor ∈ dataConstructors arg, constructor ∈ constructors ground := by
  refine ⟨fun arg inside constructor found => List.mem_append_left _ (List.mem_flatMap.mpr ⟨rule, member,
    List.mem_append_left _ (mem_dataConstructorsOf inside found)⟩), fun literal literalMember arg inside constructor found => ?_⟩
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨rule, member, List.mem_append_right _
    (List.mem_flatMap.mpr ⟨literal, literalMember, mem_dataConstructorsOf inside found⟩)⟩)

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem goal_constructors {literal : Goal Variable Literal Symbol} (member : literal ∈ goals ground) :
    ∀ arg ∈ literal.args, ∀ constructor ∈ dataConstructors arg, constructor ∈ constructors ground :=
  fun _ inside _ found => List.mem_append_right _ (List.mem_flatMap.mpr ⟨literal, member, mem_dataConstructorsOf inside found⟩)

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem dataConstructors_ordinary {term : Term Variable Literal Symbol} (data : IsData term)
    (ordinary : Machine.Ordinary hoApplySymbol term) : ∀ arity, Constructor.application hoApplySymbol arity ∉ dataConstructors term := by
  induction data with
  | lit => intro _ inside; simp [dataConstructors] at inside
  | @app args symbol _ ih =>
      intro arity inside
      cases ordinary with
      | app different argsOrdinary =>
          simp only [dataConstructors, List.mem_cons, Constructor.application.injEq] at inside
          rcases inside with ⟨same, _⟩ | later
          · exact different same.symm
          · obtain ⟨arg, argMember, found⟩ := mem_dataConstructorsOf_iff.mp later
            exact ih arg argMember (argsOrdinary arg argMember) arity found

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
/-- The embedding declares no application of the reserved symbol: S07's data
is ordinary. -/
theorem constructors_ordinary {constructor : Constructor Literal Symbol} (member : constructor ∈ constructors ground) :
    ∀ arity, constructor ≠ .application hoApplySymbol arity := by
  intro arity same
  subst same
  have fromArgs : ∀ {args : List (Term Variable Literal Symbol)}, (∀ arg ∈ args, IsData arg ∧ Machine.Ordinary hoApplySymbol arg) →
      Constructor.application hoApplySymbol arity ∉ dataConstructorsOf args := by
    intro args each inside
    obtain ⟨arg, argMember, found⟩ := mem_dataConstructorsOf_iff.mp inside
    exact dataConstructors_ordinary (each arg argMember).1 (each arg argMember).2 arity found
  have literalArgs : ∀ {literal : Goal Variable Literal Symbol}, GroundLiteral hoApplySymbol literal →
      ∀ arg ∈ literal.args, IsData arg ∧ Machine.Ordinary hoApplySymbol arg := by
    intro literal literalGround
    obtain ⟨_, _, form, _, args⟩ := literalGround
    rcases form with rfl | rfl <;> exact args
  rcases List.mem_append.mp member with fromRules | fromGoals
  · obtain ⟨rule, ruleMember, inside⟩ := List.mem_flatMap.mp fromRules
    obtain ⟨_, args, body⟩ := rules_ground ground ruleMember
    rcases List.mem_append.mp inside with fromHead | fromBody
    · exact fromArgs args fromHead
    · obtain ⟨literal, literalMember, found⟩ := List.mem_flatMap.mp fromBody
      exact fromArgs (literalArgs (body literal literalMember)) found
  · obtain ⟨literal, literalMember, found⟩ := List.mem_flatMap.mp fromGoals
    exact fromArgs (literalArgs (goals_ground ground literal literalMember)) found

end P0Ground

omit [DecidableEq Variable] [DecidableEq Literal] in
/-- With one arity per symbol, a site's predicate is declared defined at its
arity. -/
theorem predicate?_ofGround (arities : ((P0Ground.sites ground).eraseDups.map (·.1)).Nodup) {symbol : Symbol} {arity : Nat}
    (site : (symbol, arity) ∈ P0Ground.sites ground) :
    (Program.ofGround ground).predicate? symbol = some ⟨symbol, List.replicate arity .input, .defined⟩ := by
  have member : (symbol, arity) ∈ (P0Ground.sites ground).eraseDups := List.mem_eraseDups.mpr site
  unfold Program.predicate? Program.ofGround
  simp only
  rw [List.find?_map]
  cases found : (P0Ground.sites ground).eraseDups.find? ((fun predicate : Predicate Symbol => decide (predicate.symbol = symbol)) ∘
      fun site => (⟨site.1, List.replicate site.2 .input, .defined⟩ : Predicate Symbol)) with
  | none =>
      have := List.find?_eq_none.mp found _ member
      simp at this
  | some other =>
      have holds := List.find?_some found
      have otherMember := List.mem_of_find?_eq_some found
      simp only [Function.comp_apply, decide_eq_true_eq] at holds
      have same : other = (symbol, arity) := Machine.nodup_map_inj arities otherMember member holds
      subst same
      rfl

omit [DecidableEq Variable] [DecidableEq Literal] in
theorem closedAt_ofGround (arities : ((P0Ground.sites ground).eraseDups.map (·.1)).Nodup) {symbol : Symbol} {arity : Nat}
    (site : (symbol, arity) ∈ P0Ground.sites ground) : (Program.ofGround ground).closedAt symbol arity = true := by
  simp [Program.closedAt, predicate?_ofGround ground arities site, Predicate.closed, Predicate.arity]

theorem goalBlockers_ofGround (arities : ((P0Ground.sites ground).eraseDups.map (·.1)).Nodup)
    {literal : Goal Variable Literal Symbol} (literalGround : GroundLiteral hoApplySymbol literal)
    (site : ∀ found, literal.site? = some found → found ∈ P0Ground.sites ground)
    (declared : ∀ arg ∈ literal.args, ∀ constructor ∈ dataConstructors arg, constructor ∈ P0Ground.constructors ground)
    (at_ : Site) (path : List Nat) (bound : List Variable) :
    (Program.ofGround ground).goalBlockers at_ path bound literal = [] := by
  have names := P0Ground.literal_names literalGround
  obtain ⟨symbol, args, form, _, argsGround⟩ := literalGround
  have data : ∀ argsPath, (Program.ofGround ground).argsBlockers at_ argsPath 0 literal.args = [] := fun _ =>
    argsBlockers_nil_of fun arg inside path => dataBlockers_ground (argsGround arg (by rcases form with rfl | rfl <;> exact inside)).1
      (argsGround arg (by rcases form with rfl | rfl <;> exact inside)).2 (declared arg inside) at_ path
  have siteMember : (symbol, args.length) ∈ P0Ground.sites ground := site _ (by rcases form with rfl | rfl <;> rfl)
  have closed := closedAt_ofGround ground arities siteMember
  have noNames : ∀ terms : List (Term Variable Literal Symbol), (∀ term ∈ terms, term ∈ args) → namesOf terms = [] :=
    fun terms sub => P0Ground.namesOf_nil fun term inside => names term (by rcases form with rfl | rfl <;> exact sub term inside)
  unfold Program.goalBlockers
  rcases form with rfl | rfl
  · have inputs : namesOf ((Program.ofGround ground).inputsOf symbol args) = [] := by
      refine noNames _ fun term inside => ?_
      unfold Program.inputsOf at inside
      split at inside
      · exact Tabled.Program.select_sub _ _ _ term inside
      · exact inside
    simp [Program.declares, closed, data, Program.needs, inputs, available]
  · simp [Program.declares, closed, data, Program.needs, noNames args (fun _ inside => inside), available]

theorem bodyBlockers_ofGround (arities : ((P0Ground.sites ground).eraseDups.map (·.1)).Nodup) {at_ : Nat → Site}
    {path : Nat → List Nat} :
    ∀ {position : Nat} {bound : List Variable} {body : List (Goal Variable Literal Symbol)},
      (∀ literal ∈ body, GroundLiteral hoApplySymbol literal ∧ (∀ found, literal.site? = some found → found ∈ P0Ground.sites ground) ∧
        ∀ arg ∈ literal.args, ∀ constructor ∈ dataConstructors arg, constructor ∈ P0Ground.constructors ground) →
      (Program.ofGround ground).bodyBlockers at_ path position bound body = []
  | _, _, [], _ => rfl
  | position, bound, literal :: rest, each => by
      obtain ⟨literalGround, site, declared⟩ := each literal List.mem_cons_self
      simp only [Program.bodyBlockers, List.append_eq_nil_iff]
      exact ⟨goalBlockers_ofGround ground arities literalGround site declared _ _ _,
        bodyBlockers_ofGround arities fun other inside => each other (List.mem_cons_of_mem _ inside)⟩

/-- **The checker passes the embedding.** -/
theorem check_ofGround (arities : ((P0Ground.sites ground).eraseDups.map (·.1)).Nodup) :
    (Program.ofGround ground).check (Query.ofGround ground) = [] := by
  have ruleParts : ∀ rule ∈ P0Ground.rules ground, ∀ literal ∈ rule.body, GroundLiteral hoApplySymbol literal ∧
      (∀ found, literal.site? = some found → found ∈ P0Ground.sites ground) ∧
        ∀ arg ∈ literal.args, ∀ constructor ∈ dataConstructors arg, constructor ∈ P0Ground.constructors ground :=
    fun rule member literal inside => ⟨(P0Ground.rules_ground ground member).2.2 literal inside,
      fun _ found => P0Ground.body_site ground member inside found, (P0Ground.rule_constructors ground member).2 literal inside⟩
  have goalParts : ∀ literal ∈ P0Ground.goals ground, GroundLiteral hoApplySymbol literal ∧
      (∀ found, literal.site? = some found → found ∈ P0Ground.sites ground) ∧
        ∀ arg ∈ literal.args, ∀ constructor ∈ dataConstructors arg, constructor ∈ P0Ground.constructors ground :=
    fun literal inside => ⟨P0Ground.goals_ground ground literal inside, fun _ found => P0Ground.goal_site ground inside found,
      P0Ground.goal_constructors ground inside⟩
  have symbolsEq : (Program.ofGround ground).predicates.map (·.symbol) = (P0Ground.sites ground).eraseDups.map (·.1) := by
    simp [Program.ofGround, List.map_map, Function.comp_def]
  have declarations : (Program.ofGround ground).declarationBlockers = [] := by
    unfold Program.declarationBlockers
    simp only [symbolsEq, arities, ite_true, List.nil_append, List.append_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff,
      List.flatMap_eq_nil_iff]
    refine ⟨⟨fun symbol member same => ?_, fun constructor member => ?_⟩, fun declared member => ?_⟩
    · obtain ⟨site, siteMember, rfl⟩ := List.mem_map.mp member
      exact P0Ground.site_ordinary ground (List.mem_eraseDups.mp siteMember) (by simpa [Program.ofGround] using same)
    · cases constructor with
      | literal _ => simp
      | application symbol arity =>
          have := P0Ground.constructors_ordinary ground member
          simpa [Program.ofGround] using this
    · simp only [Program.ofGround, List.mem_map] at member
      obtain ⟨_, _, rfl⟩ := member
      simp
  have ruleClean : ∀ rule ∈ P0Ground.rules ground, ∀ index, (Program.ofGround ground).ruleBlockers index rule = [] := by
    intro rule member index
    obtain ⟨_, args, _⟩ := P0Ground.rules_ground ground member
    have closed := closedAt_ofGround ground arities (P0Ground.head_site ground member)
    unfold Program.ruleBlockers
    simp only [closed, ite_true, List.nil_append, List.append_eq_nil_iff, List.filterMap_eq_nil_iff]
    refine ⟨⟨argsBlockers_nil_of fun arg inside path => dataBlockers_ground (args arg inside).1 (args arg inside).2
      ((P0Ground.rule_constructors ground member).1 arg inside) _ path, bodyBlockers_ofGround ground arities (ruleParts rule member)⟩,
      fun ⟨arg, position⟩ inside => ?_⟩
    have argMember : arg ∈ rule.args := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp inside)
    simp [freeVars_of_isData (args arg argMember).1, available]
  unfold Program.check
  rw [List.append_eq_nil_iff]
  constructor
  · unfold Program.programBlockers
    simp only [declarations, List.nil_append, List.append_eq_nil_iff, List.flatMap_eq_nil_iff]
    refine ⟨⟨fun ⟨rule, index⟩ inside => ruleClean rule (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp inside)) index, ?_⟩, ?_⟩
    · intro entry inside; simp [Program.ofGround] at inside
    · intro entry inside; simp [Program.ofGround] at inside
  · unfold Program.queryBlockers
    simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff]
    refine ⟨⟨?_, bodyBlockers_ofGround ground arities goalParts⟩, ?_⟩
    · intro entry inside; simp [Query.ofGround] at inside
    · intro name inside; simp [Query.ofGround] at inside

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem vertex?_full {literal : Goal Variable Literal Symbol} (literalGround : GroundLiteral hoApplySymbol literal)
    {bound : List Variable} {vertex : Vertex Symbol} (found : literal.vertex? bound = some vertex) : vertex.2.free = false := by
  obtain ⟨symbol, args, form, _, argsGround⟩ := literalGround
  rcases form with rfl | rfl
  · simp only [Goal.vertex?, Option.some.injEq] at found
    subst found
    simp only [Pattern.free, patternOf, List.any_map, List.any_eq_false, Function.comp_apply, beq_iff_eq]
    intro arg inside
    simp [freeVars_of_isData (argsGround arg inside).1, available]
  · simp only [Goal.vertex?, Option.some.injEq] at found
    subst found
    exact Program.full_not_free _

omit [DecidableEq Literal] in
/-- Every vertex of the embedding binds every argument. -/
theorem vertices_full : ∀ vertex ∈ (Program.ofGround ground).vertices (Query.ofGround ground), vertex.2.free = false := by
  unfold Program.vertices
  refine Program.closeVertices_all (fun vertex _ callee successor => ?_) _ _ ?_
  · obtain ⟨⟨index, rule, call⟩, inCalls, rfl⟩ := List.mem_map.mp successor
    obtain ⟨⟨index', rule'⟩, atVertex, inMap⟩ := List.mem_flatMap.mp inCalls
    obtain ⟨call', callMember, same⟩ := List.mem_map.mp inMap
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl, rfl⟩ := same
    obtain ⟨goalMember, found⟩ := mem_bodyCalls callMember
    have ruleMember : rule' ∈ P0Ground.rules ground := rulesOf_mem (Program.mem_rulesAt.mp atVertex).1
    exact vertex?_full ((P0Ground.rules_ground ground ruleMember).2.2 _ goalMember) found
  · intro vertex member
    simp only [List.mem_eraseDups, List.mem_append] at member
    rcases member with fromQuery | fromDenials
    · simp only [queryVertices, List.mem_append, List.mem_flatMap, List.mem_map] at fromQuery
      rcases fromQuery with ⟨condition, conditionMember, _, _, _⟩ | ⟨call, inCalls, rfl⟩
      · simp [Query.ofGround] at conditionMember
      · obtain ⟨goalMember, found⟩ := mem_bodyCalls inCalls
        exact vertex?_full (P0Ground.goals_ground ground _ goalMember) found
    · simp [Program.denialVertices, Program.ofGround] at fromDenials

theorem mem_flowCalls {program : Program Variable Literal Symbol}
    {info : Vertex Symbol → Bool} {frame : Frame Variable Literal Symbol} :
    ∀ {position : Nat} {bound small : List Variable} {body : List (Goal Variable Literal Symbol)}
      {entry : Nat × Goal Variable Literal Symbol × List Variable × List Variable × Vertex Symbol},
      entry ∈ program.flowCalls info frame position bound small body → entry.2.1 ∈ body
  | _, _, _, [], _, member => by cases member
  | position, bound, small, goal :: rest, entry, member => by
      simp only [Program.flowCalls, List.mem_append] at member
      rcases member with here | there
      · cases found : goal.vertex? bound with
        | none => rw [found] at here; cases here
        | some vertex =>
            rw [found] at here
            simp only [List.mem_singleton] at here
            subst here
            exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_flowCalls there)

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem parameters_ofGround : (Query.ofGround ground).parameters = [] := by
  unfold Query.parameters
  have goalsNames := P0Ground.goals_names ground
  simp only [Query.ofGround]
  rw [goalsNames]
  rfl

/-- **The embedding has no note.** -/
theorem notes_ofGround : (Program.ofGround ground).notes (Query.ofGround ground) = [] := by
  rw [Program.notes_eq]
  unfold Program.notesWith
  simp only [List.append_eq_nil_iff]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · unfold Program.growingIn
    simp only [List.flatMap_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro vertex _ entry atVertex call inCalls
    obtain ⟨index, rule⟩ := entry
    have ruleMember : rule ∈ P0Ground.rules ground := rulesOf_mem (Program.mem_rulesAt.mp atVertex).1
    obtain ⟨position, goal, bound, small, callee⟩ := call
    have goalMember := mem_flowCalls inCalls
    obtain ⟨symbol, args, form, _, argsGround⟩ := (P0Ground.rules_ground ground ruleMember).2.2 goal goalMember
    have accepted : (boundArgs callee.2 goal.args).all ((Program.frameAt vertex.2 rule).small small) = true := by
      refine List.all_eq_true.mpr fun arg inside => ?_
      have argMember : arg ∈ args := by
        have := mem_of_mem_boundArgs inside
        rcases form with rfl | rfl <;> exact this
      simp [Frame.small, closedData_of_isData (argsGround arg argMember).1]
    simp [accepted]
  · unfold Program.freeOutputsIn
    have none : ((Program.ofGround ground).vertices (Query.ofGround ground)).filter (·.2.free) = [] :=
      List.filter_eq_nil_iff.mpr fun vertex member => by simp [vertices_full ground vertex member]
    rw [none]
    rfl
  · unfold Program.unguarded
    simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    refine ⟨⟨fun ⟨rule, index⟩ inside name nameMember => ?_, fun _ inside => by simp [Program.ofGround] at inside⟩,
      fun name inside => by simp [Query.ofGround] at inside⟩
    have ruleMember : rule ∈ P0Ground.rules ground := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp inside)
    rw [P0Ground.rule_names ground ruleMember] at nameMember
    simp at nameMember
  · unfold Program.unsplit
    simp [parameters_ofGround ground]

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem ofGoal_atom {atom : Symbol × List (Term Variable Literal Symbol)} :
    ∀ {goal : Term Variable Literal Symbol} {literal : Goal Variable Literal Symbol}, literal ∈ ofGoal goal →
      Program.Goal.atom? literal = some atom → Term.app atom.1 atom.2 ∈ GroundSearch.atoms goal
  | .app symbol args, literal, member, found => by
      simp only [ofGoal, List.mem_singleton] at member
      subst member
      simp only [Program.Goal.atom?, Option.some.injEq] at found
      subst found
      simp [GroundSearch.atoms]
  | .conj left right, literal, member, found => by
      simp only [ofGoal, List.mem_append] at member
      simp only [GroundSearch.atoms, List.mem_append]
      rcases member with inLeft | inRight
      · exact .inl (ofGoal_atom inLeft found)
      · exact .inr (ofGoal_atom inRight found)
  | .defaultNeg (.app symbol args), literal, member, found => by
      simp only [ofGoal, List.mem_singleton] at member
      subst member
      simp only [Program.Goal.atom?, Option.some.injEq] at found
      subst found
      simp [GroundSearch.atoms]
  | .var _, _, member, _ | .lit _, _, member, _ | .truth, _, member, _ | .falsity, _, member, _
  | .disj _ _, _, member, _ | .imp _ _, _, member, _ | .forallVar _ _, _, member, _ | .existsVar _ _, _, member, _
  | .dictionaryCall _ _ _ _, _, member, _ | .equal _ _, _, member, _ => by simp [ofGoal] at member
  | .defaultNeg (.var _), _, member, _ | .defaultNeg (.lit _), _, member, _ | .defaultNeg .truth, _, member, _
  | .defaultNeg .falsity, _, member, _ | .defaultNeg (.conj _ _), _, member, _ | .defaultNeg (.disj _ _), _, member, _
  | .defaultNeg (.imp _ _), _, member, _ | .defaultNeg (.defaultNeg _), _, member, _
  | .defaultNeg (.forallVar _ _), _, member, _ | .defaultNeg (.existsVar _ _), _, member, _
  | .defaultNeg (.dictionaryCall _ _ _ _), _, member, _ | .defaultNeg (.equal _ _), _, member, _ => by
      simp [ofGoal] at member

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem atoms_conjunction_of {atom goal : Term Variable Literal Symbol} :
    ∀ {goals : List (Term Variable Literal Symbol)}, goal ∈ goals → atom ∈ GroundSearch.atoms goal →
      atom ∈ GroundSearch.atoms (Term.conjunction goals)
  | [], member, _ => by cases member
  | first :: rest, member, inside => by
      simp only [Term.conjunction, List.foldr_cons, GroundSearch.atoms, List.mem_append]
      rcases List.mem_cons.mp member with rfl | later
      · exact .inl inside
      · exact .inr (atoms_conjunction_of later inside)

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
/-- A rule's calls go to lower ranks: S07's rank witness, on the clause the
rule comes from; a fact calls nothing. -/
theorem edge_rank {rule : Rule Variable Literal Symbol} (member : rule ∈ P0Ground.rules ground)
    {literal : Goal Variable Literal Symbol} (inside : literal ∈ rule.body) {atom : Symbol × List (Term Variable Literal Symbol)}
    (found : Program.Goal.atom? literal = some atom) : ground.rank (.app atom.1 atom.2) < ground.rank (.app rule.head rule.args) := by
  rcases List.mem_append.mp member with fromClauses | fromFacts
  · obtain ⟨clause, clauseMember, translated⟩ := List.mem_filterMap.mp fromClauses
    match clause, translated with
    | .definite (.app symbol args) body, translated =>
        simp only [ofClause, Option.some.injEq] at translated
        subst translated
        obtain ⟨goal, goalMember, literalMember⟩ := List.mem_flatMap.mp inside
        exact ground.ranked _ body clauseMember _ (atoms_conjunction_of goalMember (ofGoal_atom literalMember found))
  · obtain ⟨atom', _, translated⟩ := List.mem_filterMap.mp fromFacts
    match atom', translated with
    | .app symbol args, translated =>
        simp only [ofFact, Option.some.injEq] at translated
        subst translated
        cases inside

/-- **The embedding is ground and acyclic.** -/
theorem ground_ofGround : (Program.ofGround ground).ground (Query.ofGround ground) = true := by
  have literalRun : ∀ {literal : Goal Variable Literal Symbol}, GroundLiteral hoApplySymbol literal → Program.Goal.groundRun literal = true := by
    intro literal literalGround
    obtain ⟨_, _, form, _, _⟩ := literalGround
    rcases form with rfl | rfl <;> rfl
  unfold Program.ground
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨fun rule member => ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, fun literal member => literalRun (P0Ground.goals_ground ground literal member)⟩,
    fun predicate member => ?_⟩, fun edge _ => ?_⟩
  · refine ⟨?_, fun literal inside => literalRun ((P0Ground.rules_ground ground member).2.2 literal inside)⟩
    rw [P0Ground.rule_names ground member]
    rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [Query.ofGround, P0Ground.goals_names ground]
  · simp only [Program.ofGround, List.mem_map] at member
    obtain ⟨_, _, rfl⟩ := member
    rfl
  · simp only [decide_eq_true_eq]
    refine GroundSearch.topoRank_decreases ⟨fun atom => ground.rank (.app atom.1 atom.2), fun edge inside => ?_⟩
      (fun edge inside => ?_) edge (by assumption)
    · obtain ⟨rule, ruleMember, inMap⟩ := List.mem_flatMap.mp inside
      obtain ⟨target, targetMember, rfl⟩ := List.mem_map.mp inMap
      obtain ⟨literal, literalMember, found⟩ := List.mem_filterMap.mp targetMember
      exact edge_rank ground ruleMember literalMember found
    · obtain ⟨rule, ruleMember, inMap⟩ := List.mem_flatMap.mp inside
      obtain ⟨target, targetMember, rfl⟩ := List.mem_map.mp inMap
      exact ⟨List.mem_append_left _ (List.mem_map.mpr ⟨rule, ruleMember, rfl⟩),
        List.mem_append_right _ (List.mem_flatMap.mpr ⟨rule, ruleMember, targetMember⟩)⟩

/-- **S07's ground programs classify P0**: with one arity per predicate
symbol, the embedding of a `P0.Ground` passes the checker, has no note, and is
ground and acyclic. -/
theorem ofGround_p0 (arities : ((P0Ground.sites ground).eraseDups.map (·.1)).Nodup) :
    (Program.ofGround ground).classify (Query.ofGround ground) = .p0 := by
  rw [(Program.ofGround ground).classify_closed (parameters_ofGround ground)]
  unfold Program.classifyClosed
  rw [check_ofGround ground arities]
  simp only [parameters_ofGround ground, List.isEmpty_nil, ite_true]
  rw [notes_ofGround ground]
  simp [ground_ofGround ground]

/-! ## The faithful embedding -/

/-- The embedding keeps the input's meaning: every clause's body and the goal
atomic (no `falsity`, no NAF of a compound goal), no atom of an unknown marker
(the IR's markers are free, S07 reads them closed), and one arity per
predicate symbol (IR declarations are keyed by symbol). -/
def P0Ground.faithful (markers : Symbol → Bool) : Bool :=
  ground.program.clauses.all (fun clause => match clause with
    | .definite _ body => body.all atomicGoal
    | .goal _ => true) &&
    atomicGoal ground.goal && (P0Ground.sites ground).all (fun site => !markers site.1) &&
    decide ((P0Ground.sites ground).eraseDups.map (·.1)).Nodup

/-- **The embedding of a ground input**, when it keeps its meaning
(`P0Ground.faithful`): the IR program and query, or none. -/
def embedGround (markers : Symbol → Bool) : Option (Program Variable Literal Symbol × Query Variable Literal Symbol) :=
  if P0Ground.faithful ground markers then some (Program.ofGround ground, Query.ofGround ground) else none

variable {ground} in
/-- **S07's ground inputs classify P0**: an embedded input is P0. -/
theorem embedGround_p0 {markers : Symbol → Bool} {program : Program Variable Literal Symbol}
    {query : Query Variable Literal Symbol} (embedded : embedGround ground markers = some (program, query)) :
    program.classify query = .p0 := by
  unfold embedGround at embedded
  split at embedded
  · rename_i faithful
    simp only [Option.some.injEq, Prod.mk.injEq] at embedded
    obtain ⟨rfl, rfl⟩ := embedded
    simp only [P0Ground.faithful, Bool.and_eq_true, decide_eq_true_eq] at faithful
    exact ofGround_p0 ground faithful.2
  · cases embedded

omit [DecidableEq Literal] [DecidableEq Symbol] in
/-- **The embedding keeps an atomic goal's meaning**: its literals hold
exactly when the goal does, in every model. -/
theorem satisfies_ofGoal {Value : Type} {hoApply : Symbol} (model : Semantics.Model Literal Symbol Value hoApply)
    (environment : Semantics.Environment Variable Value) :
    ∀ {goal : Term Variable Literal Symbol}, atomicGoal goal = true →
      ((∀ literal ∈ ofGoal goal, model.Satisfies environment literal.toTerm) ↔ model.Satisfies environment goal)
  | .app symbol args, _ => by simp [ofGoal, Goal.toTerm]
  | .truth, _ => by simp [ofGoal, Semantics.Model.Satisfies, Semantics.Model.eval, model.holds_top]
  | .conj left right, atomic => by
      simp only [atomicGoal, Bool.and_eq_true] at atomic
      simp only [ofGoal, List.mem_append, or_imp, forall_and, satisfies_ofGoal model environment atomic.1,
        satisfies_ofGoal model environment atomic.2]
      simp only [Semantics.Model.Satisfies, Semantics.Model.eval, model.holds_conjunction]
  | .defaultNeg (.app symbol args), _ => by simp [ofGoal, Goal.toTerm]
  | .var _, atomic | .lit _, atomic | .falsity, atomic | .disj _ _, atomic | .imp _ _, atomic
  | .forallVar _ _, atomic | .existsVar _ _, atomic | .dictionaryCall _ _ _ _, atomic | .equal _ _, atomic => by
      simp [atomicGoal] at atomic
  | .defaultNeg (.var _), atomic | .defaultNeg (.lit _), atomic | .defaultNeg .truth, atomic
  | .defaultNeg .falsity, atomic | .defaultNeg (.conj _ _), atomic | .defaultNeg (.disj _ _), atomic
  | .defaultNeg (.imp _ _), atomic | .defaultNeg (.defaultNeg _), atomic
  | .defaultNeg (.forallVar _ _), atomic | .defaultNeg (.existsVar _ _), atomic
  | .defaultNeg (.dictionaryCall _ _ _ _), atomic | .defaultNeg (.equal _ _), atomic => by
      simp [atomicGoal] at atomic

omit [DecidableEq Literal] [DecidableEq Symbol] in
/-- **A rule's body holds exactly when its clause's body does**, in every
model, for atomic goals. -/
theorem satisfies_ofBody {Value : Type} {hoApply : Symbol} (model : Semantics.Model Literal Symbol Value hoApply)
    (environment : Semantics.Environment Variable Value) {body : List (Term Variable Literal Symbol)}
    (atomic : ∀ goal ∈ body, atomicGoal goal = true) :
    model.Satisfies environment (bodyTerm (body.flatMap ofGoal)) ↔ model.Satisfies environment (Term.conjunction body) := by
  rw [bodyTerm, model.satisfies_conjunction, model.satisfies_conjunction]
  simp only [List.mem_map, List.mem_flatMap, forall_exists_index, and_imp]
  constructor
  · intro each goal member
    exact (satisfies_ofGoal model environment (atomic goal member)).mp fun literal inside =>
      each _ literal goal member inside rfl
  · rintro each _ literal goal member inside rfl
    exact (satisfies_ofGoal model environment (atomic goal member)).mpr (each goal member) literal inside

end Classify


end AnthillModKbSpec.IR
