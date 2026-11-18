import AnthillModKbSpec.Resolution.Tabled.Abstract
import AnthillModKbSpec.Resolution.Tabled.Fragment

/-! # The decision IR: the programs decisions run on (S27)

Decisions run on an intermediate representation of their own
([decision IR](../../../docs/decision-ir.md), decided with the user,
2026-11-17): admission translates the KB and the query into it (S29), and its
evaluator decides it (S28). `Term` stays the representation of the KB, the
queries, and the proofs; the IR is a type for admitted programs, in which only
decidable constructs are expressible. Connectives, quantifiers, and compound
NAF operands are compiled into rules of auxiliary predicates before they reach
the IR.

| Element | Lean |
| --- | --- |
| Predicate | `Predicate`: a symbol, its declared modes (its arity), and its `Kind` |
| Kind | *defined* (the completion closes it), *opened* (closed, and kept open by a marker case among its rules), *guard* (a domain's membership, exact), *primitive* (a registered total evaluator: its last argument is the value of the others) |
| Literal | `Goal`: a call; NAF of an atom; data equality and disequality; a guard; a primitive; a marker atom |
| Rule | `Rule`: a definition `p(args) :- body`; the completion is over the rules |
| Derived rule | The same form, from a checked lemma: used to derive, never part of the completion |
| Denial | A body: `⊥ :- body` |
| Query | `Query`: the context's conditions, the goals to decide, the answer names |

A program also carries what its kinds need: the declared free constructors
(data terms are built from them), the decision of each guard on ground data and
the members of the finite ones, and the primitives' evaluators.

Every element renders as `Term` (`Goal.toTerm`, `Rule.toClause`,
`Program.clauses`), and the program's meaning is the Clark completion of its
rendering for the signature that closes its defined and opened predicates
(`Program.completion`). Its semantics, the Herbrand reduction, and relevance
are in `IR/Semantics`, `IR/Herbrand`, and `IR/Relevance`; the checker and the
evidence classes in `IR/Check` and `IR/Evidence`. -/

namespace AnthillModKbSpec.IR

open Completion Tabled

variable {Variable Literal Symbol : Type}

/-! ## Predicates -/

/-- How the completion and the models read a predicate. -/
inductive Kind where
  /-- Defined by its rules: the completion closes it. -/
  | defined
  /-- Defined by its rules, among which a marker case keeps it open
  (`p(x̄) :- D(x̄), marker(x̄)`): the completion closes it, and the marker
  case is never refuted. -/
  | opened
  /-- A domain's membership, interpreted exactly: decided by the constructors
  of its argument, or binding it over a finite domain. -/
  | guard
  /-- A registered total evaluator (S14): the atom `f(inputs, output)` holds
  exactly when the evaluator gives `output` for `inputs`. -/
  | primitive
  deriving DecidableEq, Repr

/-- A predicate declaration: its symbol, the mode of each argument position,
and its kind. Its arity is the number of modes. -/
structure Predicate (Symbol : Type) where
  symbol : Symbol
  modes : List Mode
  kind : Kind
  deriving DecidableEq, Repr

namespace Predicate

def arity (predicate : Predicate Symbol) : Nat := predicate.modes.length

/-- Closed by the completion: a defined or an opened predicate. -/
def closed (predicate : Predicate Symbol) : Bool :=
  match predicate.kind with
  | .defined | .opened => true
  | _ => false

end Predicate

/-! ## Literals, rules, programs, queries -/

/-- A literal of a rule body, a denial, or a query. Its arguments are data
terms: names, literals, and applications of declared constructors. -/
inductive Goal (Variable Literal Symbol : Type) where
  /-- A call of a defined or opened predicate: the arguments at its input
  positions are bound before it, those at its output positions after it. -/
  | call (predicate : Symbol) (args : List (Term Variable Literal Symbol))
  /-- NAF of an atom with every name bound. -/
  | naf (predicate : Symbol) (args : List (Term Variable Literal Symbol))
  /-- Data equality: one side bound, the other bound after it. -/
  | equal (left right : Term Variable Literal Symbol)
  /-- Data disequality, both sides bound. -/
  | differ (left right : Term Variable Literal Symbol)
  /-- A guard `D(t)`: decided when `t` is bound, binding it over a finite
  domain otherwise. -/
  | guard (symbol : Symbol) (arg : Term Variable Literal Symbol)
  /-- A primitive `f(inputs) = output`: the inputs bound, the output bound
  after it. -/
  | primitive (symbol : Symbol) (inputs : List (Term Variable Literal Symbol)) (output : Term Variable Literal Symbol)
  /-- A marker atom with every name bound: free in the models. -/
  | marker (symbol : Symbol) (args : List (Term Variable Literal Symbol))
  deriving Repr

/-- A rule `head(args) :- body`. -/
structure Rule (Variable Literal Symbol : Type) where
  head : Symbol
  args : List (Term Variable Literal Symbol)
  body : List (Goal Variable Literal Symbol)
  deriving Repr

/-- A program of the IR: predicate declarations, the declared free
constructors, the rules (definitions), the derived rules (from checked
lemmas, never in the completion), the denials, and what the kinds need: the
members of each finite guard (`members`), the decision of every other guard
on a ground data term (`holdsOf`), and each primitive's evaluator
(`evaluate`). A finite guard holds exactly of its listed members
(`Program.guardHolds`), so the translator lists them exactly. The `ho_apply`
symbol is reserved: no IR predicate is it. -/
structure Program (Variable Literal Symbol : Type) where
  predicates : List (Predicate Symbol)
  constructors : List (Constructor Literal Symbol)
  rules : List (Rule Variable Literal Symbol)
  derived : List (Rule Variable Literal Symbol)
  denials : List (List (Goal Variable Literal Symbol))
  holdsOf : Symbol → Term Variable Literal Symbol → Bool
  members : Symbol → Option (List (Term Variable Literal Symbol))
  evaluate : Symbol → List (Term Variable Literal Symbol) → Option (Term Variable Literal Symbol)
  hoApply : Symbol

/-- A query: conditions on the models (the context), the goals to decide, and
the answer names, declared and never inferred. Its other names are rigid
parameters. -/
structure Query (Variable Literal Symbol : Type) where
  conditions : List (Goal Variable Literal Symbol)
  goals : List (Goal Variable Literal Symbol)
  answers : List Variable
  deriving Repr

/-! ## Names and arguments -/

section Names

variable [DecidableEq Variable]

/-- The data arguments of a literal. -/
def Goal.args : Goal Variable Literal Symbol → List (Term Variable Literal Symbol)
  | .call _ args | .naf _ args | .marker _ args => args
  | .equal left right | .differ left right => [left, right]
  | .guard _ arg => [arg]
  | .primitive _ inputs output => inputs ++ [output]

/-- The names a list of terms mentions. -/
def namesOf (terms : List (Term Variable Literal Symbol)) : List Variable := terms.flatMap Term.freeVars

/-- The names of a literal. -/
def Goal.names (goal : Goal Variable Literal Symbol) : List Variable := namesOf goal.args

/-- The names of a body. -/
def bodyNames (body : List (Goal Variable Literal Symbol)) : List Variable := body.flatMap Goal.names

/-- The names of a rule: its head's and its body's. -/
def Rule.names (rule : Rule Variable Literal Symbol) : List Variable := namesOf rule.args ++ bodyNames rule.body

/-- The query's rigid parameters: its names other than the answer names. -/
def Query.parameters (query : Query Variable Literal Symbol) : List Variable :=
  (bodyNames query.conditions ++ bodyNames query.goals).eraseDups.filter fun name => !query.answers.contains name

end Names

/-! ## Rendering as `Term` -/

/-- A literal as a formula: a call, a guard, a primitive, and a marker are
atoms (a primitive's output last); NAF and disequality are default negations. -/
def Goal.toTerm : Goal Variable Literal Symbol → Term Variable Literal Symbol
  | .call predicate args => .app predicate args
  | .naf predicate args => .defaultNeg (.app predicate args)
  | .equal left right => .equal left right
  | .differ left right => .defaultNeg (.equal left right)
  | .guard symbol arg => .app symbol [arg]
  | .primitive symbol inputs output => .app symbol (inputs ++ [output])
  | .marker symbol args => .app symbol args

/-- A body as the conjunction of its literals. -/
def bodyTerm (body : List (Goal Variable Literal Symbol)) : Term Variable Literal Symbol :=
  Term.conjunction (body.map Goal.toTerm)

/-- A rule as a definite clause. -/
def Rule.toClause (rule : Rule Variable Literal Symbol) : HornClause Variable Literal Symbol :=
  .definite (.app rule.head rule.args) (rule.body.map Goal.toTerm)

/-- A denial as a goal clause. -/
def denialClause (body : List (Goal Variable Literal Symbol)) : HornClause Variable Literal Symbol :=
  .goal (body.map Goal.toTerm)

namespace Program

variable (program : Program Variable Literal Symbol)

/-- The KB clauses of the program: its rules and its denials. Derived rules
are not among them. -/
def clauses : List (HornClause Variable Literal Symbol) :=
  program.rules.map Rule.toClause ++ program.denials.map denialClause

/-- The derived rules as clauses: valid in every model of the completion,
never part of it. -/
def derivedClauses : List (HornClause Variable Literal Symbol) := program.derived.map Rule.toClause

/-- The predicates the completion closes, at their arities. -/
def closedKeys : List (Symbol × Nat) :=
  program.predicates.filterMap fun predicate => if predicate.closed then some (predicate.symbol, predicate.arity) else none

/-- The signature of the completion: the closed predicates, and the declared
free constructors its equality theory separates. -/
def signature : Signature Literal Symbol := ⟨program.closedKeys, program.constructors⟩

/-- The program's completion: its clauses, the only-if half of every closed
predicate, and the free equality theory of its constructors. -/
def completion [DecidableEq Variable] [FreshNames Variable] [DecidableEq Symbol] : Completed Variable Literal Symbol :=
  Completion.completion program.clauses program.signature

variable [DecidableEq Symbol]

/-- The declaration of a symbol, the first one listed. -/
def predicate? (symbol : Symbol) : Option (Predicate Symbol) :=
  program.predicates.find? fun predicate => predicate.symbol = symbol

attribute [local instance] Machine.termEq in
/-- A guard's decision on a ground data term: a finite guard holds exactly of
its listed members, any other guard by its decision. -/
def guardHolds (symbol : Symbol) (term : Term Variable Literal Symbol) [DecidableEq Variable] [DecidableEq Literal] : Bool :=
  match program.members symbol with
  | some members => members.contains term
  | none => program.holdsOf symbol term

/-- The rules defining a predicate, with their indices. -/
def rulesOf (symbol : Symbol) : List (Nat × Rule Variable Literal Symbol) :=
  program.rules.zipIdx.filterMap fun (rule, index) => if rule.head = symbol then some (index, rule) else none

end Program

namespace Query

variable [DecidableEq Variable] (query : Query Variable Literal Symbol)

/-- The conditions as a proof context. -/
def context : ProofContext Variable Literal Symbol := query.conditions.map Goal.toTerm

/-- The goals as one formula, the answer names existentially closed. -/
def formula : Formula Variable Literal Symbol := query.answers.foldr Term.existsVar (bodyTerm query.goals)

end Query

/-! ## Substitutions -/

section Substitution

mutual
/-- A data term with its names replaced. -/
def subst (σ : Variable → Term Variable Literal Symbol) : Term Variable Literal Symbol → Term Variable Literal Symbol
  | .var name => σ name
  | .app symbol args => .app symbol (substAll σ args)
  | term => term

def substAll (σ : Variable → Term Variable Literal Symbol) : List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol)
  | [] => []
  | arg :: rest => subst σ arg :: substAll σ rest
end

theorem substAll_eq (σ : Variable → Term Variable Literal Symbol) :
    ∀ args : List (Term Variable Literal Symbol), substAll σ args = args.map (subst σ)
  | [] => rfl
  | arg :: rest => by rw [substAll, substAll_eq σ rest]; rfl

variable [DecidableEq Variable]

/-- A literal with its names replaced. -/
def Goal.subst (σ : Variable → Term Variable Literal Symbol) : Goal Variable Literal Symbol → Goal Variable Literal Symbol
  | .call predicate args => .call predicate (args.map (IR.subst σ))
  | .naf predicate args => .naf predicate (args.map (IR.subst σ))
  | .equal left right => .equal (IR.subst σ left) (IR.subst σ right)
  | .differ left right => .differ (IR.subst σ left) (IR.subst σ right)
  | .guard symbol arg => .guard symbol (IR.subst σ arg)
  | .primitive symbol inputs output => .primitive symbol (inputs.map (IR.subst σ)) (IR.subst σ output)
  | .marker symbol args => .marker symbol (args.map (IR.subst σ))

/-- The substitution of an instance: a rigid parameter by its value, every
other name kept. -/
def Query.instanceSubst (query : Query Variable Literal Symbol) (values : Variable → Term Variable Literal Symbol) :
    Variable → Term Variable Literal Symbol :=
  fun name => if name ∈ query.parameters then values name else Term.var name

/-- A query with its rigid parameters replaced by ground terms: the names
outside `parameters` are kept. -/
def Query.instantiate (query : Query Variable Literal Symbol) (values : Variable → Term Variable Literal Symbol) :
    Query Variable Literal Symbol :=
  ⟨query.conditions.map (Goal.subst (query.instanceSubst values)), query.goals.map (Goal.subst (query.instanceSubst values)),
    query.answers⟩

end Substitution

/-! ## Facts of the rendering -/

section Facts

variable [DecidableEq Variable]

theorem Goal.toTerm_freeVars (goal : Goal Variable Literal Symbol) : (goal.toTerm).freeVars = goal.names := by
  cases goal <;> simp [Goal.toTerm, Goal.names, Goal.args, namesOf, Term.freeVars, List.flatMap_append]

omit [DecidableEq Variable] in
theorem mem_closedKeys {program : Program Variable Literal Symbol} {key : Symbol × Nat} :
    key ∈ program.closedKeys ↔ ∃ predicate ∈ program.predicates, predicate.closed = true ∧
      key = (predicate.symbol, predicate.arity) := by
  simp only [Program.closedKeys, List.mem_filterMap]
  constructor
  · rintro ⟨predicate, member, produced⟩
    by_cases closed : predicate.closed = true
    · simp only [closed, ite_true, Option.some.injEq] at produced
      exact ⟨predicate, member, closed, produced.symm⟩
    · simp [closed] at produced
  · rintro ⟨predicate, member, closed, rfl⟩
    exact ⟨predicate, member, by simp [closed]⟩

omit [DecidableEq Variable] in
theorem mem_rulesOf [DecidableEq Symbol] {program : Program Variable Literal Symbol} {symbol : Symbol}
    {entry : Nat × Rule Variable Literal Symbol} :
    entry ∈ program.rulesOf symbol ↔ program.rules[entry.1]? = some entry.2 ∧ entry.2.head = symbol := by
  obtain ⟨index, rule⟩ := entry
  simp only [Program.rulesOf, List.mem_filterMap]
  constructor
  · rintro ⟨⟨found, position⟩, member, produced⟩
    by_cases same : found.head = symbol
    · simp only [same, ite_true, Option.some.injEq, Prod.mk.injEq] at produced
      obtain ⟨rfl, rfl⟩ := produced
      exact ⟨List.mem_zipIdx_iff_getElem?.mp member, same⟩
    · simp [same] at produced
  · rintro ⟨found, same⟩
    exact ⟨(rule, index), List.mem_zipIdx_iff_getElem?.mpr found, by simp [same]⟩

omit [DecidableEq Variable] in
theorem rulesOf_mem [DecidableEq Symbol] {program : Program Variable Literal Symbol} {symbol : Symbol}
    {entry : Nat × Rule Variable Literal Symbol} (member : entry ∈ program.rulesOf symbol) : entry.2 ∈ program.rules := by
  obtain ⟨found, _⟩ := mem_rulesOf.mp member
  exact List.mem_of_getElem? found

end Facts

end AnthillModKbSpec.IR
