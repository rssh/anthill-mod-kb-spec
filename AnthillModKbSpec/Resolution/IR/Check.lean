import AnthillModKbSpec.Resolution.IR.Syntax

/-! # The IR checker: declarations, data, and the binding scan (S27)

`Program.check` decides whether an IR program and a query are well formed,
and reports every violation as an Undecided blocker (S22) at its site and
path, before anything runs:

- **Declarations.** A call or a NAF names a closed (defined or opened)
  predicate at its declared arity; a guard a guard predicate of arity one; a
  primitive a primitive predicate, its output last; a marker atom no declared
  predicate. A rule's head is a closed predicate at its arity.
- **Data.** Every argument is a data term over the declared free constructors
  (`Tabled.dataIn`): a defined operation, a formula, or a dictionary call
  inside data is outside the IR.
- **Binding, read left to right** (S23's scan on the IR). Each literal needs
  some names bound before it (`Program.needs`) and binds its own after it
  (`after`): a call its inputs, by the declared modes; NAF, disequality, and a
  marker atom every name; an equation one side; a primitive its inputs; a
  guard its argument, unless the guard's domain is finite, when it binds the
  argument over its members. A rule starts from the names of its head's
  inputs, and its head's outputs must be bound at its end; a denial starts
  from no name; a query from its rigid parameters, and its answer names must
  be bound by the end of its goals.

The translator (S29) orders a conjunction's literals so that names are bound
from finite sources first; conjunction commutes in the completion, so the
order changes no meaning. Sites are those of the rendering (`Program.clauses`):
rule `i` is clause `i`, its head `.head i` and its body literal `j`
`.body i j`; denial `j` is clause `rules.length + j`. A query's condition `i`
is `.assumption i`, and its goal `i` is `.goal` at path `[i]`. -/

namespace AnthillModKbSpec.IR

open Completion Tabled Admission Answers

variable {Variable Literal Symbol : Type}

/-! ## Binding -/

section Binding

variable [DecidableEq Variable]

/-- The names bound after a literal: those before it and the literal's own.
A literal that binds nothing (NAF, disequality, a marker) needs all its names
bound before it, so the set is the same. -/
def after (bound : List Variable) (goal : Goal Variable Literal Symbol) : List Variable := bound ++ goal.names

/-- The names bound after a body, literal by literal. -/
def boundAfter : List Variable → List (Goal Variable Literal Symbol) → List Variable
  | bound, [] => bound
  | bound, goal :: rest => boundAfter (after bound goal) rest

theorem boundAfter_append_names :
    ∀ (bound : List Variable) (body : List (Goal Variable Literal Symbol)),
      ∀ name, name ∈ boundAfter bound body ↔ name ∈ bound ∨ name ∈ bodyNames body
  | bound, [], name => by simp [boundAfter, bodyNames]
  | bound, goal :: rest, name => by
      rw [boundAfter, boundAfter_append_names (after bound goal) rest name]
      simp only [after, List.mem_append, bodyNames, List.flatMap_cons]
      constructor
      · rintro ((here | own) | later)
        · exact .inl here
        · exact .inr (.inl own)
        · exact .inr (.inr later)
      · rintro (here | own | later)
        · exact .inl (.inl here)
        · exact .inl (.inr own)
        · exact .inr later

/-- Every name of the list is bound. -/
def available (bound names : List Variable) : Bool := names.all bound.contains

theorem available_iff {bound names : List Variable} : available bound names = true ↔ ∀ name ∈ names, name ∈ bound := by
  simp [available]

end Binding

namespace Program

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] (program : Program Variable Literal Symbol)

/-! ## What a literal needs -/

/-- The arguments of a call at the positions of one mode, by the callee's
declared modes; all of them when the callee is not declared. -/
def inputsOf (predicate : Symbol) (args : List (Term Variable Literal Symbol)) : List (Term Variable Literal Symbol) :=
  match program.predicate? predicate with
  | some declared => select .input declared.modes args
  | none => args

/-- A guard binds its argument over a finite domain: one with listed members. -/
def finite (symbol : Symbol) : Bool := (program.members symbol).isSome

/-- The literal can run with these names bound: a call's inputs, an equation's
one side, a primitive's inputs, and every name of NAF, a disequality, and a
marker atom are bound; a guard's argument is bound, or its domain is finite. -/
def needs (bound : List Variable) : Goal Variable Literal Symbol → Bool
  | .call predicate args => available bound (namesOf (program.inputsOf predicate args))
  | .naf _ args | .marker _ args => available bound (namesOf args)
  | .equal left right => available bound left.freeVars || available bound right.freeVars
  | .differ left right => available bound (left.freeVars ++ right.freeVars)
  | .guard symbol arg => available bound arg.freeVars || program.finite symbol
  | .primitive _ inputs _ => available bound (namesOf inputs)

/-! ## Declarations and data -/

/-- The declaration of a closed predicate at this arity. -/
def closedAt (symbol : Symbol) (arity : Nat) : Bool :=
  match program.predicate? symbol with
  | some declared => declared.closed && declared.arity == arity
  | none => false

/-- A declared predicate of this kind at this arity. -/
def kindAt (kind : Kind) (symbol : Symbol) (arity : Nat) : Bool :=
  match program.predicate? symbol with
  | some declared => declared.kind == kind && declared.arity == arity
  | none => false

/-- The literal names a predicate of the right kind at its arity. -/
def declares : Goal Variable Literal Symbol → Bool
  | .call predicate args | .naf predicate args => program.closedAt predicate args.length
  | .guard symbol _ => program.kindAt .guard symbol 1
  | .primitive symbol inputs _ => program.kindAt .primitive symbol (inputs.length + 1)
  | .marker symbol _ => (program.predicate? symbol).isNone && symbol != program.hoApply
  | .equal _ _ | .differ _ _ => true

/-- The literal's arguments are data over the declared constructors. -/
def data (goal : Goal Variable Literal Symbol) : Bool := goal.args.all (dataIn program.constructors)

/-! ## Blockers -/

mutual
/-- The blockers of a data position (S23's kinds): data are names, declared
literals, and applications of declared constructors; an application by
`ho_apply`, a defined operation, a dictionary call, or a formula is outside
the IR. -/
def dataBlockers (site : Site) (path : List Nat) : Term Variable Literal Symbol → List (Blocker Variable Literal Symbol)
  | .var _ => []
  | .lit value =>
      if Constructor.literal value ∈ program.constructors then [] else [Tabled.blocker site path (.lit value) (.construct .operation)]
  | .app symbol args =>
      if symbol = program.hoApply then [Tabled.outside site path (.app symbol args) .hoApplyConversion]
      else if Constructor.application symbol args.length ∈ program.constructors then argsBlockers site path 0 args
      else [Tabled.blocker site path (.app symbol args) (.construct .operation)]
  | .dictionaryCall dictionary selectors operation args =>
      [Tabled.outside site path (.dictionaryCall dictionary selectors operation args) .dictionaryLaw]
  | term => [Tabled.outside site path term .termKind]

def argsBlockers (site : Site) (path : List Nat) : Nat → List (Term Variable Literal Symbol) → List (Blocker Variable Literal Symbol)
  | _, [] => []
  | index, arg :: rest => dataBlockers site (path ++ [index]) arg ++ argsBlockers site path (index + 1) rest
end

/-- What a literal naming the wrong symbol lacks: `ho_apply` conversion for
the reserved symbol, its kind for a predicate of another kind, a mode for an
undeclared predicate or another arity. -/
def declarationBlocker (site : Site) (path : List Nat) (goal : Goal Variable Literal Symbol) : Blocker Variable Literal Symbol :=
  let formula := goal.toTerm
  let symbol := match goal with
    | .call predicate _ | .naf predicate _ | .marker predicate _ => some predicate
    | .guard symbol _ | .primitive symbol _ _ => some symbol
    | _ => none
  match symbol with
  | some symbol =>
      if symbol = program.hoApply then Tabled.outside site path formula .hoApplyConversion
      else
        match goal, program.predicate? symbol with
        | .marker _ _, _ => Tabled.outside site path formula .termKind
        | _, some _ => Tabled.outside site path formula .termKind
        | _, none => Tabled.blocker site path formula .mode
  | none => Tabled.blocker site path formula .mode

/-- The blockers of a literal at its site and path, with these names bound
before it: a symbol of the wrong kind or undeclared, an argument that is not
data, at its argument path, and a name it needs unbound. -/
def goalBlockers (site : Site) (path : List Nat) (bound : List Variable) (goal : Goal Variable Literal Symbol) :
    List (Blocker Variable Literal Symbol) :=
  (if program.declares goal then [] else [program.declarationBlocker site path goal]) ++
    program.argsBlockers site path 0 goal.args ++
    (if program.needs bound goal then [] else [Tabled.blocker site path goal.toTerm .mode])

/-- The blockers of a body read left to right from the names bound before it,
literal `j` at `site j` and `path j`. -/
def bodyBlockers (site : Nat → Site) (path : Nat → List Nat) : Nat → List Variable → List (Goal Variable Literal Symbol) →
    List (Blocker Variable Literal Symbol)
  | _, _, [] => []
  | position, bound, goal :: rest =>
      program.goalBlockers (site position) (path position) bound goal ++
        bodyBlockers site path (position + 1) (after bound goal) rest

/-- What a rule's head lacks when it is not a closed predicate at its arity:
`ho_apply` conversion, a guard definition, its kind, or a mode. -/
def headBlocker (index : Nat) (rule : Rule Variable Literal Symbol) : Blocker Variable Literal Symbol :=
  let head := Term.app rule.head rule.args
  if rule.head = program.hoApply then Tabled.outside (.head index) [] head .hoApplyConversion
  else
    match program.predicate? rule.head with
    | some declared =>
        if declared.kind = .guard then Tabled.outside (.head index) [] head .guardDefinition
        else if declared.closed then Tabled.blocker (.head index) [] head .mode
        else Tabled.outside (.head index) [] head .termKind
    | none => Tabled.blocker (.head index) [] head .mode

/-- The blockers of a rule: its head not a closed predicate at its arity, an
argument of it not data, its body's, and a head argument not bound at the end
of the body. The body starts from the names of the head's inputs. -/
def ruleBlockers (index : Nat) (rule : Rule Variable Literal Symbol) : List (Blocker Variable Literal Symbol) :=
  let declared := if program.closedAt rule.head rule.args.length then [] else [program.headBlocker index rule]
  let data := program.argsBlockers (.head index) [] 0 rule.args
  let start := namesOf (program.inputsOf rule.head rule.args)
  let body := program.bodyBlockers (.body index) (fun _ => []) 0 start rule.body
  let finish := boundAfter start rule.body
  let unbound := rule.args.zipIdx.filterMap fun (arg, position) =>
    if available finish arg.freeVars then none else some (Tabled.blocker (.head index) [position] arg .mode)
  declared ++ data ++ body ++ unbound

/-- The blockers of a denial, read from no bound name. -/
def denialBlockers (index : Nat) (body : List (Goal Variable Literal Symbol)) : List (Blocker Variable Literal Symbol) :=
  program.bodyBlockers (.body index) (fun _ => []) 0 [] body

/-- The blockers of the declarations: each symbol declared twice, a
predicate named by the reserved `ho_apply` symbol, and a finite guard's
listed member that is not a ground data term over the declared
constructors. -/
def declarationBlockers : List (Blocker Variable Literal Symbol) :=
  let symbols := program.predicates.map (·.symbol)
  let duplicates := symbols.eraseDups.filter fun symbol => symbols.count symbol > 1
  (if symbols.Nodup then []
    else duplicates.map (fun symbol => Tabled.outside .goal [] (.app symbol []) .termKind) ++
      if duplicates.isEmpty then [Tabled.outside .goal [] (.app program.hoApply []) .termKind] else []) ++
    (symbols.filter (· == program.hoApply)).map (fun symbol => Tabled.outside .goal [] (.app symbol []) .hoApplyConversion) ++
    program.predicates.flatMap fun declared =>
      if declared.kind = .guard then
        match program.members declared.symbol with
        | some members => (members.filter fun member => !groundIn program.constructors member).map fun member =>
            Tabled.outside .goal [] member .termKind
        | none => []
      else []

/-- The blockers of the program: its declarations', every rule's, and every
denial's. Derived rules are checked as rules, at the sites after the
denials. -/
def programBlockers : List (Blocker Variable Literal Symbol) :=
  program.declarationBlockers ++
  program.rules.zipIdx.flatMap (fun (rule, index) => program.ruleBlockers index rule) ++
    program.denials.zipIdx.flatMap (fun (body, index) => program.denialBlockers (program.rules.length + index) body) ++
    program.derived.zipIdx.flatMap fun (rule, index) =>
      program.ruleBlockers (program.rules.length + program.denials.length + index) rule

/-- The blockers of a query: each condition read from the rigid parameters,
an answer name in a condition, the goals read from the rigid parameters, goal
`i` at path `[i]`, and an answer name not bound by their end. -/
def queryBlockers (query : Query Variable Literal Symbol) : List (Blocker Variable Literal Symbol) :=
  let parameters := query.parameters
  let conditions := query.conditions.zipIdx.flatMap fun (condition, index) =>
    program.goalBlockers (.assumption index) [] parameters condition ++
      (condition.names.filter query.answers.contains).map fun name => Tabled.blocker (.assumption index) [] (.var name) .mode
  let goals := program.bodyBlockers (fun _ => .goal) (fun position => [position]) 0 parameters query.goals
  let finish := boundAfter parameters query.goals
  let unbound := query.answers.filterMap fun name =>
    if finish.contains name then none else some (Tabled.blocker .goal [] (.var name) .mode)
  conditions ++ goals ++ unbound

/-- The checker: every blocker of the program and the query. Empty exactly
when they are well formed. -/
def check (query : Query Variable Literal Symbol) : List (Blocker Variable Literal Symbol) :=
  program.programBlockers ++ program.queryBlockers query

end Program

/-! ## What a passed check gives -/

namespace Program

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] {program : Program Variable Literal Symbol}

omit [DecidableEq Variable] in
mutual
theorem dataBlockers_nil {site : Site} :
    ∀ {path : List Nat} {term : Term Variable Literal Symbol}, program.dataBlockers site path term = [] →
      dataIn program.constructors term = true
  | _, .var _, _ => rfl
  | _, .lit value, clean => by
      simp only [dataBlockers] at clean
      by_cases declared : Constructor.literal value ∈ program.constructors
      · simp [dataIn, declared]
      · simp [declared] at clean
  | path, .app symbol args, clean => by
      simp only [dataBlockers] at clean
      by_cases reserved : symbol = program.hoApply
      · simp [reserved] at clean
      · by_cases declared : Constructor.application symbol args.length ∈ program.constructors
        · simp only [reserved, declared, ite_true, ite_false] at clean
          simp only [dataIn, declared, decide_true, Bool.true_and]
          exact argsBlockers_nil clean
        · simp [reserved, declared] at clean
  | _, .truth, clean | _, .falsity, clean | _, .conj _ _, clean | _, .disj _ _, clean | _, .imp _ _, clean
  | _, .defaultNeg _, clean | _, .forallVar _ _, clean | _, .existsVar _ _, clean | _, .equal _ _, clean
  | _, .dictionaryCall _ _ _ _, clean => by simp [dataBlockers] at clean

theorem argsBlockers_nil {site : Site} :
    ∀ {path : List Nat} {index : Nat} {args : List (Term Variable Literal Symbol)}, program.argsBlockers site path index args = [] →
      dataInAll program.constructors args = true
  | _, _, [], _ => rfl
  | path, index, arg :: rest, clean => by
      simp only [argsBlockers, List.append_eq_nil_iff] at clean
      simp only [dataInAll, dataBlockers_nil clean.1, argsBlockers_nil clean.2, Bool.and_self]
end

theorem goalBlockers_nil {site : Site} {path : List Nat} {bound : List Variable} {goal : Goal Variable Literal Symbol}
    (clean : program.goalBlockers site path bound goal = []) :
    program.declares goal = true ∧ program.data goal = true ∧ program.needs bound goal = true := by
  unfold goalBlockers at clean
  simp only [List.append_eq_nil_iff] at clean
  obtain ⟨⟨declared, data⟩, needs⟩ := clean
  refine ⟨?_, ?_, ?_⟩
  · cases wrong : program.declares goal
    · simp [wrong] at declared
    · rfl
  · exact (dataInAll_iff program.constructors).mp (argsBlockers_nil data) |> fun all => List.all_eq_true.mpr all
  · cases wrong : program.needs bound goal
    · simp [wrong] at needs
    · rfl

/-- A body that passes the scan: every literal is declared, data, and has what
it needs bound by the names before it. -/
inductive Scans (program : Program Variable Literal Symbol) : List Variable → List (Goal Variable Literal Symbol) → Prop
  | nil {bound : List Variable} : Scans program bound []
  | cons {bound : List Variable} {goal : Goal Variable Literal Symbol} {rest : List (Goal Variable Literal Symbol)} :
      program.declares goal = true → program.data goal = true → program.needs bound goal = true →
      Scans program (after bound goal) rest → Scans program bound (goal :: rest)

theorem bodyBlockers_nil {site : Nat → Site} {path : Nat → List Nat} :
    ∀ {position : Nat} {bound : List Variable} {body : List (Goal Variable Literal Symbol)},
      program.bodyBlockers site path position bound body = [] → Scans program bound body
  | _, _, [], _ => .nil
  | position, bound, goal :: rest, clean => by
      simp only [bodyBlockers, List.append_eq_nil_iff] at clean
      obtain ⟨declared, data, needs⟩ := goalBlockers_nil clean.1
      exact .cons declared data needs (bodyBlockers_nil clean.2)

/-- A rule with no blocker: its head is a closed predicate at its arity, its
arguments data, its body scans from the head's inputs, and every head
argument is bound at the end of the body. -/
structure RuleOk (program : Program Variable Literal Symbol) (rule : Rule Variable Literal Symbol) : Prop where
  closed : program.closedAt rule.head rule.args.length = true
  data : ∀ arg ∈ rule.args, dataIn program.constructors arg = true
  scans : Scans program (namesOf (program.inputsOf rule.head rule.args)) rule.body
  bound : ∀ arg ∈ rule.args, ∀ name ∈ arg.freeVars,
    name ∈ boundAfter (namesOf (program.inputsOf rule.head rule.args)) rule.body

theorem ruleBlockers_nil {index : Nat} {rule : Rule Variable Literal Symbol}
    (clean : program.ruleBlockers index rule = []) : RuleOk program rule := by
  unfold ruleBlockers at clean
  simp only [List.append_eq_nil_iff] at clean
  obtain ⟨⟨⟨declared, data⟩, body⟩, unbound⟩ := clean
  refine ⟨?_, ?_, bodyBlockers_nil body, ?_⟩
  · cases wrong : program.closedAt rule.head rule.args.length
    · simp [wrong] at declared
    · rfl
  · exact (dataInAll_iff program.constructors).mp (argsBlockers_nil data)
  · intro arg member name occurs
    obtain ⟨position, inZip⟩ : ∃ position, (arg, position) ∈ rule.args.zipIdx := by
      obtain ⟨position, found⟩ := List.mem_iff_getElem?.mp member
      exact ⟨position, List.mem_zipIdx_iff_getElem?.mpr found⟩
    have none := List.filterMap_eq_nil_iff.mp unbound (arg, position) inZip
    by_cases avail : available (boundAfter (namesOf (program.inputsOf rule.head rule.args)) rule.body) arg.freeVars = true
    · exact available_iff.mp avail name occurs
    · simp [avail] at none

theorem programBlockers_parts (clean : program.programBlockers = []) :
    program.declarationBlockers = [] ∧ (∀ rule ∈ program.rules, RuleOk program rule) ∧
      (∀ body ∈ program.denials, Scans program [] body) ∧ ∀ rule ∈ program.derived, RuleOk program rule := by
  unfold programBlockers at clean
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at clean
  obtain ⟨⟨⟨declarations, rules⟩, denials⟩, derived⟩ := clean
  refine ⟨declarations, fun rule member => ?_, fun body member => ?_, fun rule member => ?_⟩
  · obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    exact ruleBlockers_nil (rules (rule, index) (List.mem_zipIdx_iff_getElem?.mpr found))
  · obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    exact bodyBlockers_nil (denials (body, index) (List.mem_zipIdx_iff_getElem?.mpr found))
  · obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    exact ruleBlockers_nil (derived (rule, index) (List.mem_zipIdx_iff_getElem?.mpr found))

omit [DecidableEq Variable] in
theorem declarationBlockers_nil (clean : program.declarationBlockers = []) :
    (program.predicates.map (·.symbol)).Nodup ∧ (∀ predicate ∈ program.predicates, predicate.symbol ≠ program.hoApply) ∧
      ∀ declared ∈ program.predicates, declared.kind = .guard → ∀ members, program.members declared.symbol = some members →
        ∀ member ∈ members, groundIn program.constructors member = true := by
  unfold declarationBlockers at clean
  simp only [List.append_eq_nil_iff] at clean
  obtain ⟨⟨nodupPart, reservedPart⟩, membersPart⟩ := clean
  refine ⟨?_, fun predicate member same => ?_, fun declared member kind members found term inside => ?_⟩
  · by_cases nodup : (program.predicates.map (·.symbol)).Nodup
    · exact nodup
    · simp only [nodup, ite_false, List.append_eq_nil_iff, List.map_eq_nil_iff] at nodupPart
      obtain ⟨duplicatesNil, genericPart⟩ := nodupPart
      simp [duplicatesNil] at genericPart
  · simp only [List.map_eq_nil_iff] at reservedPart
    have inside : predicate.symbol ∈ (program.predicates.map (·.symbol)).filter (· == program.hoApply) :=
      List.mem_filter.mpr ⟨List.mem_map.mpr ⟨predicate, member, rfl⟩, by simp [same]⟩
    rw [reservedPart] at inside
    cases inside
  · simp only [List.flatMap_eq_nil_iff] at membersPart
    have this := membersPart declared member
    simp only [kind, ite_true, found, List.map_eq_nil_iff, List.filter_eq_nil_iff] at this
    simpa using this term inside

/-- What the semantics reads of a program the checker passed: every rule and
derived rule is well formed, every denial scans, every symbol is declared
once, no predicate is the reserved `ho_apply` symbol, and a finite guard's
members are ground data terms over the declared constructors. -/
structure WellFormed (program : Program Variable Literal Symbol) : Prop where
  rules : ∀ rule ∈ program.rules, RuleOk program rule
  derived : ∀ rule ∈ program.derived, RuleOk program rule
  denials : ∀ body ∈ program.denials, Scans program [] body
  unique : (program.predicates.map (·.symbol)).Nodup
  reserved : ∀ predicate ∈ program.predicates, predicate.symbol ≠ program.hoApply
  members : ∀ declared ∈ program.predicates, declared.kind = .guard → ∀ members,
    program.members declared.symbol = some members → ∀ member ∈ members, groundIn program.constructors member = true

theorem wellFormed_of_check {query : Query Variable Literal Symbol} (clean : program.check query = []) :
    program.WellFormed := by
  have programClean : program.programBlockers = [] := (List.append_eq_nil_iff.mp clean).1
  obtain ⟨declarations, rules, denials, derived⟩ := programBlockers_parts programClean
  obtain ⟨unique, reserved, members⟩ := declarationBlockers_nil declarations
  exact ⟨rules, derived, denials, unique, reserved, members⟩

/-- A query with no blocker: its conditions are declared and data and read
from its rigid parameters, no answer name is in a condition, its goals scan
from its rigid parameters, and its answer names are bound by their end. -/
structure QueryOk (program : Program Variable Literal Symbol) (query : Query Variable Literal Symbol) : Prop where
  conditions : ∀ goal ∈ query.conditions, program.declares goal = true ∧ program.data goal = true ∧
    program.needs query.parameters goal = true
  apart : ∀ goal ∈ query.conditions, ∀ name ∈ goal.names, name ∉ query.answers
  goals : Scans program query.parameters query.goals
  answers : ∀ name ∈ query.answers, name ∈ boundAfter query.parameters query.goals

theorem queryOk_of_check {query : Query Variable Literal Symbol} (clean : program.check query = []) : QueryOk program query := by
  have queryClean : program.queryBlockers query = [] := (List.append_eq_nil_iff.mp clean).2
  unfold queryBlockers at queryClean
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff] at queryClean
  obtain ⟨⟨conditionsClean, goalsClean⟩, unboundClean⟩ := queryClean
  refine ⟨?_, ?_, bodyBlockers_nil goalsClean, ?_⟩
  · intro goal member
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    have clean := (conditionsClean (goal, index) (List.mem_zipIdx_iff_getElem?.mpr found)).1
    exact goalBlockers_nil clean
  · intro goal member name occurs answer
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    have clean := (conditionsClean (goal, index) (List.mem_zipIdx_iff_getElem?.mpr found)).2
    simp only [List.map_eq_nil_iff, List.filter_eq_nil_iff] at clean
    have := clean name occurs
    simp [answer] at this
  · intro name member
    have := unboundClean name member
    cases bound : (boundAfter query.parameters query.goals).contains name
    · rw [bound] at this; simp at this
    · exact List.contains_iff_mem.mp bound

end Program

end AnthillModKbSpec.IR
