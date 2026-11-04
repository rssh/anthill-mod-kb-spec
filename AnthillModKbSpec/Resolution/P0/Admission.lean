import AnthillModKbSpec.Resolution.P0.Run

namespace AnthillModKbSpec.Admission

open Machine GroundSearch P0 AdmissionSignature InductiveDomains

/-! # P0 admission (S07)

`check` decides, before any rule runs, whether an input is in the P0 profile:
finite ground acyclic resolution over a ground atomic context. It inspects the
syntax, decides the ground guard atoms structurally, and constructs and verifies
a rank of the whole program's dependency graph, NAF operands included. It
returns `ready plan`, `needsEvidence` with one request per formula that needs a
capability P0 lacks (site, term path, formula, capability), or `invalid` when
the input contradicts its own declarations.

`Ready` is admission evidence, not a proof of the goal: the plan runs on the
shared machine (`Plan.run`), and that run terminates with a success or a
complete-failure certificate (`run_total_of_p0`, `run_correct_of_p0`).
`Plan.answer` decides the query with no fuel. `checkProgram` admits a program
for every P0 query at once. P0 rejection is not a negative answer: a P1 or P2
route may admit the same input. -/

variable {Domain Variable Literal Symbol : Type}

/-- What admission is checked against: the snapshot (the signature, with its
constructor rules listed and the variable naming of its generated clauses, and
the effective program) and the query. The signature declares its rules by a
predicate, so the input contract carries the proof that the list enumerates
exactly them, and that the naming is distinct; `check` relies on both. The
program marks exactly the signature's guard symbols, as `Program.build` does
(`Program.build_guard`); that it carries the generated clauses is checked
(`Input.unlisted`). A plan is admitted for exactly this input; any change
needs a new check. -/
structure Input (Domain Variable Literal Symbol : Type) where
  signature : SignatureSnapshot Domain Symbol
  names : Nat → Variable
  rules : List (Rule Domain Symbol)
  /-- The listed rules are declared constructor rules of the signature. -/
  listed : ∀ rule ∈ rules, signature.signature.data.definitions rule
  /-- Every declared constructor rule is listed. -/
  complete : ∀ rule, signature.signature.data.definitions rule → rule ∈ rules
  /-- The generated clauses name each rule's arguments distinctly. -/
  distinct : DistinctNames signature.signature.data.definitions names
  program : Machine.Program Variable Literal Symbol
  /-- The program's guard symbols are the signature's. -/
  marked : ∀ symbol, program.guard symbol = true ↔ symbol ∈ guardSymbols signature
  context : ProofContext Variable Literal Symbol
  goal : Formula Variable Literal Symbol

/-- An input without its query: the snapshot with its listed rules, and the
effective program. A program-level check takes only this. -/
structure ProgramInput (Domain Variable Literal Symbol : Type) where
  signature : SignatureSnapshot Domain Symbol
  names : Nat → Variable
  rules : List (Rule Domain Symbol)
  listed : ∀ rule ∈ rules, signature.signature.data.definitions rule
  complete : ∀ rule, signature.signature.data.definitions rule → rule ∈ rules
  distinct : DistinctNames signature.signature.data.definitions names
  program : Machine.Program Variable Literal Symbol
  marked : ∀ symbol, program.guard symbol = true ↔ symbol ∈ guardSymbols signature

/-- The program asked a query. -/
def ProgramInput.ask (base : ProgramInput Domain Variable Literal Symbol) (context : ProofContext Variable Literal Symbol)
    (goal : Formula Variable Literal Symbol) : Input Domain Variable Literal Symbol :=
  ⟨base.signature, base.names, base.rules, base.listed, base.complete, base.distinct, base.program, base.marked,
    context, goal⟩

/-- An input's program, without its query. -/
def Input.base (input : Input Domain Variable Literal Symbol) : ProgramInput Domain Variable Literal Symbol :=
  ⟨input.signature, input.names, input.rules, input.listed, input.complete, input.distinct, input.program, input.marked⟩

theorem Input.base_ask (input : Input Domain Variable Literal Symbol) :
    input.base.ask input.context input.goal = input := rfl

/-- The capability a formula outside P0 needs. Each names a route of a later
profile; none is a negative answer about the formula. -/
inductive Capability where
  /-- A variable where P0 needs ground data or a ground atom: an answer name,
  a clause template, or a formula variable. -/
  | groundInstance
  /-- A KB clause on a dependency cycle, positive or through NAF. -/
  | acyclicStrategy
  /-- An implication, quantifier, or disjunction goal, or a non-atomic
  assumption: scoped proof or left rules. -/
  | scopedProof
  /-- An equality goal, assumption, or clause head. -/
  | equality
  /-- A dictionary operation call: an evaluator or proved laws. -/
  | dictionaryLaw
  /-- An application by `ho_apply`, also inside data: conversion (S11) in a
  goal, an assumption, or a head; inside data none applies. -/
  | hoApplyConversion
  /-- A denial clause: contradiction search. -/
  | contradiction
  /-- A clause concluding a compound formula, such as an induction principle. -/
  | compoundHead
  /-- A KB clause concluding a guard atom: P0 decides guards from the
  signature, so a KB definition would change their meaning. -/
  | guardDefinition
  /-- A term of another kind where P0 needs data, an atom, or a goal: a formula
  inside data, or a literal as a goal, head, or assumption. -/
  | termKind
  deriving DecidableEq, Repr

/-- Where a requested formula sits: the query goal, an assumption, or a KB
clause's head or body goal, by the KB clause index. -/
inductive Site where
  | goal
  | assumption (index : Nat)
  | head (clause : Nat)
  | body (clause : Nat) (goal : Nat)
  deriving DecidableEq, Repr

/-- One evidence request: the formula at a term path under its site, and the
capability it needs. -/
structure Request (Variable Literal Symbol : Type) where
  site : Site
  path : List Nat
  formula : Term Variable Literal Symbol
  capability : Capability

/-- An input contradicting its own declarations. -/
inductive Diagnostic where
  /-- The program clause at this position is marked as generated from the
  signature, but the signature does not generate it. -/
  | signatureClause (position : Nat)
  /-- The signature generates the clause at this position of
  `signatureClauses`, but the program does not carry it. -/
  | missingSignatureClause (position : Nat)
  deriving DecidableEq, Repr

/-! ## Requests -/

section Requests

variable [DecidableEq Symbol] (hoApplySymbol : Symbol)

mutual
/-- Requests for a data position: P0 data are literals and application trees
without `ho_apply`. -/
def dataRequests (site : Site) (path : List Nat) : Term Variable Literal Symbol → List (Request Variable Literal Symbol)
  | .lit _ => []
  | .app symbol args =>
      if symbol = hoApplySymbol then [⟨site, path, .app symbol args, .hoApplyConversion⟩]
      else argsRequests site path 0 args
  | .var name => [⟨site, path, .var name, .groundInstance⟩]
  | .dictionaryCall dictionary selectors operation args =>
      [⟨site, path, .dictionaryCall dictionary selectors operation args, .dictionaryLaw⟩]
  | term => [⟨site, path, term, .termKind⟩]

def argsRequests (site : Site) (path : List Nat) : Nat → List (Term Variable Literal Symbol) →
    List (Request Variable Literal Symbol)
  | _, [] => []
  | index, arg :: rest => dataRequests site (path ++ [index]) arg ++ argsRequests site path (index + 1) rest
end

/-- Requests for a goal position: P0 goals are ground atoms, truth, falsity,
conjunction, and NAF. -/
def goalRequests (site : Site) : List Nat → Term Variable Literal Symbol → List (Request Variable Literal Symbol)
  | path, .app symbol args =>
      if symbol = hoApplySymbol then [⟨site, path, .app symbol args, .hoApplyConversion⟩]
      else argsRequests hoApplySymbol site path 0 args
  | _, .truth | _, .falsity => []
  | path, .conj left right => goalRequests site (path ++ [0]) left ++ goalRequests site (path ++ [1]) right
  | path, .defaultNeg body => goalRequests site (path ++ [0]) body
  | path, .var name => [⟨site, path, .var name, .groundInstance⟩]
  | path, .equal left right => [⟨site, path, .equal left right, .equality⟩]
  | path, .dictionaryCall dictionary selectors operation args =>
      [⟨site, path, .dictionaryCall dictionary selectors operation args, .dictionaryLaw⟩]
  | path, .lit value => [⟨site, path, .lit value, .termKind⟩]
  | path, term => [⟨site, path, term, .scopedProof⟩]

/-- Requests for an assumption: P0 assumptions are ground atoms. -/
def assumptionRequests (index : Nat) : Term Variable Literal Symbol → List (Request Variable Literal Symbol)
  | .app symbol args =>
      if symbol = hoApplySymbol then [⟨.assumption index, [], .app symbol args, .hoApplyConversion⟩]
      else argsRequests hoApplySymbol (.assumption index) [] 0 args
  | .var name => [⟨.assumption index, [], .var name, .groundInstance⟩]
  | .equal left right => [⟨.assumption index, [], .equal left right, .equality⟩]
  | .dictionaryCall dictionary selectors operation args =>
      [⟨.assumption index, [], .dictionaryCall dictionary selectors operation args, .dictionaryLaw⟩]
  | .lit value => [⟨.assumption index, [], .lit value, .termKind⟩]
  | term => [⟨.assumption index, [], term, .scopedProof⟩]

def contextRequests : Nat → ProofContext Variable Literal Symbol → List (Request Variable Literal Symbol)
  | _, [] => []
  | index, assumption :: rest => assumptionRequests hoApplySymbol index assumption ++ contextRequests (index + 1) rest

/-- Requests for a KB clause head: a ground atom over a symbol that is not a guard. -/
def headRequests (guard : Symbol → Bool) (index : Nat) : Term Variable Literal Symbol → List (Request Variable Literal Symbol)
  | .app symbol args =>
      if symbol = hoApplySymbol then [⟨.head index, [], .app symbol args, .hoApplyConversion⟩]
      else (if guard symbol then [⟨.head index, [], .app symbol args, .guardDefinition⟩] else []) ++
        argsRequests hoApplySymbol (.head index) [] 0 args
  | .var name => [⟨.head index, [], .var name, .groundInstance⟩]
  | .equal left right => [⟨.head index, [], .equal left right, .equality⟩]
  | .dictionaryCall dictionary selectors operation args =>
      [⟨.head index, [], .dictionaryCall dictionary selectors operation args, .dictionaryLaw⟩]
  | .lit value => [⟨.head index, [], .lit value, .termKind⟩]
  | term => [⟨.head index, [], term, .compoundHead⟩]

def bodyRequests (index : Nat) : Nat → List (Term Variable Literal Symbol) → List (Request Variable Literal Symbol)
  | _, [] => []
  | position, goal :: rest => goalRequests hoApplySymbol (.body index position) [] goal ++ bodyRequests index (position + 1) rest

/-- Requests for a KB clause: a definite clause with a ground head and P0 body goals. -/
def clauseRequests (guard : Symbol → Bool) (index : Nat) : HornClause Variable Literal Symbol →
    List (Request Variable Literal Symbol)
  | .definite head body => headRequests hoApplySymbol guard index head ++ bodyRequests hoApplySymbol index 0 body
  | .goal _ => [⟨.head index, [], .falsity, .contradiction⟩]

end Requests

/-! ### Requests characterize the P0 classes -/

section Characterization

variable {hoApplySymbol : Symbol}

theorem atomApp_iff {symbol : Symbol} {args : List (Term Variable Literal Symbol)} :
    IsAtom hoApplySymbol (.app symbol args) ∧ Ordinary hoApplySymbol (.app symbol args) ↔
      Plain hoApplySymbol (.app symbol args) := by
  constructor
  · intro ⟨atomic, ordinary⟩; exact Plain.of_atom atomic ordinary
  · intro plain
    have ⟨data, ordinary⟩ := Plain.iff.mp plain
    cases data with
    | app args' =>
        cases ordinary with
        | app different _ => exact ⟨.app different args', .app different (by assumption)⟩

variable [DecidableEq Symbol]

mutual
theorem dataRequests_nil : ∀ (site : Site) (path : List Nat) (term : Term Variable Literal Symbol),
    dataRequests hoApplySymbol site path term = [] ↔ Plain hoApplySymbol term
  | _, _, .lit _ => by simp [dataRequests, Plain.lit]
  | site, path, .app symbol args => by
      rw [Plain.app_iff, dataRequests]
      split
      · rename_i same; simp [same]
      · rename_i different; rw [argsRequests_nil site path 0 args]; simp [different]
  | _, _, .var _ => by simp [dataRequests]; intro plain; cases plain
  | _, _, .truth => by simp [dataRequests]; intro plain; cases plain
  | _, _, .falsity => by simp [dataRequests]; intro plain; cases plain
  | _, _, .conj _ _ => by simp [dataRequests]; intro plain; cases plain
  | _, _, .disj _ _ => by simp [dataRequests]; intro plain; cases plain
  | _, _, .imp _ _ => by simp [dataRequests]; intro plain; cases plain
  | _, _, .defaultNeg _ => by simp [dataRequests]; intro plain; cases plain
  | _, _, .forallVar _ _ => by simp [dataRequests]; intro plain; cases plain
  | _, _, .existsVar _ _ => by simp [dataRequests]; intro plain; cases plain
  | _, _, .dictionaryCall _ _ _ _ => by simp [dataRequests]; intro plain; cases plain
  | _, _, .equal _ _ => by simp [dataRequests]; intro plain; cases plain

theorem argsRequests_nil : ∀ (site : Site) (path : List Nat) (index : Nat) (args : List (Term Variable Literal Symbol)),
    argsRequests hoApplySymbol site path index args = [] ↔ ∀ arg ∈ args, Plain hoApplySymbol arg
  | _, _, _, [] => by simp [argsRequests]
  | site, path, index, arg :: rest => by
      rw [argsRequests, List.append_eq_nil_iff, dataRequests_nil site (path ++ [index]) arg,
        argsRequests_nil site path (index + 1) rest]
      simp
end

theorem goalRequests_nil : ∀ (site : Site) (path : List Nat) (term : Term Variable Literal Symbol),
    goalRequests hoApplySymbol site path term = [] ↔ IsGoal hoApplySymbol term ∧ Ordinary hoApplySymbol term
  | site, path, .app symbol args => by
      rw [goalRequests]
      have atomIff : IsGoal hoApplySymbol (.app symbol args) ∧ Ordinary hoApplySymbol (.app symbol args) ↔
          Plain hoApplySymbol (.app symbol args) := by
        rw [← atomApp_iff]
        exact ⟨fun ⟨valid, ordinary⟩ => by cases valid with | atom atomic => exact ⟨atomic, ordinary⟩,
          fun ⟨atomic, ordinary⟩ => ⟨.atom atomic, ordinary⟩⟩
      rw [atomIff, Plain.app_iff]
      split
      · rename_i same; simp [same]
      · rename_i different; rw [argsRequests_nil]; simp [different]
  | _, _, .truth => by simp [goalRequests]; exact ⟨.truth, .truth⟩
  | _, _, .falsity => by simp [goalRequests]; exact ⟨.falsity, .falsity⟩
  | site, path, .conj left right => by
      rw [goalRequests, List.append_eq_nil_iff, goalRequests_nil site _ left, goalRequests_nil site _ right]
      constructor
      · intro ⟨⟨leftValid, leftOrdinary⟩, rightValid, rightOrdinary⟩
        exact ⟨.conj leftValid rightValid, .conj leftOrdinary rightOrdinary⟩
      · intro ⟨valid, ordinary⟩
        cases valid with
        | atom atomic => cases atomic
        | conj leftValid rightValid =>
            cases ordinary with
            | conj leftOrdinary rightOrdinary => exact ⟨⟨leftValid, leftOrdinary⟩, rightValid, rightOrdinary⟩
  | site, path, .defaultNeg body => by
      rw [goalRequests, goalRequests_nil site _ body]
      constructor
      · intro ⟨valid, ordinary⟩; exact ⟨.defaultNeg valid, .defaultNeg ordinary⟩
      · intro ⟨valid, ordinary⟩
        cases valid with
        | atom atomic => cases atomic
        | defaultNeg inner =>
            cases ordinary with
            | defaultNeg innerOrdinary => exact ⟨inner, innerOrdinary⟩
  | _, _, .var _ => by simp [goalRequests]; intro valid; cases valid with | atom atomic => cases atomic
  | _, _, .lit _ => by simp [goalRequests]; intro valid; cases valid with | atom atomic => cases atomic
  | _, _, .disj _ _ => by simp [goalRequests]; intro valid; cases valid with | atom atomic => cases atomic
  | _, _, .imp _ _ => by simp [goalRequests]; intro valid; cases valid with | atom atomic => cases atomic
  | _, _, .forallVar _ _ => by simp [goalRequests]; intro valid; cases valid with | atom atomic => cases atomic
  | _, _, .existsVar _ _ => by simp [goalRequests]; intro valid; cases valid with | atom atomic => cases atomic
  | _, _, .dictionaryCall _ _ _ _ => by simp [goalRequests]; intro valid; cases valid with | atom atomic => cases atomic
  | _, _, .equal _ _ => by simp [goalRequests]; intro valid; cases valid with | atom atomic => cases atomic

omit [DecidableEq Symbol] in
theorem not_atom {term : Term Variable Literal Symbol} (notApp : ∀ symbol args, term ≠ .app symbol args) :
    ¬ IsAtom hoApplySymbol term := by
  intro atomic
  cases atomic with
  | app _ _ => exact notApp _ _ rfl

theorem assumptionRequests_nil (index : Nat) (term : Term Variable Literal Symbol) :
    assumptionRequests hoApplySymbol index term = [] ↔ IsAtom hoApplySymbol term ∧ Ordinary hoApplySymbol term := by
  cases term with
  | app symbol args =>
      rw [atomApp_iff, Plain.app_iff, assumptionRequests]
      split
      · rename_i same; simp [same]
      · rename_i different; rw [argsRequests_nil]; simp [different]
  | _ => simp only [assumptionRequests, reduceCtorEq, false_iff, not_and]; exact fun atomic => absurd atomic (not_atom (by simp))

theorem contextRequests_nil : ∀ (index : Nat) (context : ProofContext Variable Literal Symbol),
    contextRequests hoApplySymbol index context = [] ↔
      ∀ atom ∈ context, IsAtom hoApplySymbol atom ∧ Ordinary hoApplySymbol atom
  | _, [] => by simp [contextRequests]
  | index, assumption :: rest => by
      rw [contextRequests, List.append_eq_nil_iff, assumptionRequests_nil, contextRequests_nil (index + 1) rest]
      simp

theorem bodyRequests_nil (index : Nat) : ∀ (position : Nat) (body : List (Term Variable Literal Symbol)),
    bodyRequests hoApplySymbol index position body = [] ↔
      ∀ goal ∈ body, IsGoal hoApplySymbol goal ∧ Ordinary hoApplySymbol goal
  | _, [] => by simp [bodyRequests]
  | position, goal :: rest => by
      rw [bodyRequests, List.append_eq_nil_iff, goalRequests_nil, bodyRequests_nil index (position + 1) rest]
      simp

/-- A P0 clause: a definite ground clause without `ho_apply` whose head is not a
guard atom. -/
def ClauseOk (hoApplySymbol : Symbol) (guard : Symbol → Bool) (clause : HornClause Variable Literal Symbol) : Prop :=
  IsClause hoApplySymbol clause ∧ ClauseOrdinary hoApplySymbol clause ∧
    ∀ head body, clause = .definite head body → ∀ symbol args, head = .app symbol args → guard symbol = false

theorem headRequests_nil (guard : Symbol → Bool) (index : Nat) (head : Term Variable Literal Symbol) :
    headRequests hoApplySymbol guard index head = [] ↔
      (IsAtom hoApplySymbol head ∧ Ordinary hoApplySymbol head) ∧
        ∀ symbol args, head = .app symbol args → guard symbol = false := by
  cases head with
  | app symbol args =>
      rw [atomApp_iff, Plain.app_iff, headRequests]
      split
      · rename_i same; simp [same]
      · rename_i different
        rw [List.append_eq_nil_iff, argsRequests_nil]
        cases guardEq : guard symbol <;> simp [different, guardEq]
  | _ =>
      simp only [headRequests, reduceCtorEq, false_iff, not_and]
      exact fun atomic => absurd atomic.1 (not_atom (by simp))

theorem clauseRequests_nil (guard : Symbol → Bool) (index : Nat) (clause : HornClause Variable Literal Symbol) :
    clauseRequests hoApplySymbol guard index clause = [] ↔ ClauseOk hoApplySymbol guard clause := by
  cases clause with
  | goal body => simp [clauseRequests, ClauseOk, ClauseOrdinary]
  | definite head body =>
      rw [clauseRequests, List.append_eq_nil_iff, bodyRequests_nil, headRequests_nil]
      constructor
      · intro ⟨⟨⟨atomic, headOrdinary⟩, notGuard⟩, goals⟩
        refine ⟨.definite atomic fun goal member => (goals goal member).1,
          ⟨headOrdinary, fun goal member => (goals goal member).2⟩, ?_⟩
        intro head' body' same
        cases same
        exact notGuard
      · intro ⟨valid, ⟨headOrdinary, bodyOrdinary⟩, notGuard⟩
        cases valid with
        | definite atomic goals =>
            exact ⟨⟨⟨atomic, headOrdinary⟩, notGuard _ _ rfl⟩, fun goal member => ⟨goals goal member, bodyOrdinary goal member⟩⟩

end Characterization

/-! ### Where requests sit -/

section Sites

variable [DecidableEq Symbol] {hoApplySymbol : Symbol}

mutual
theorem dataRequests_site : ∀ (site : Site) (path : List Nat) (term : Term Variable Literal Symbol),
    ∀ request ∈ dataRequests hoApplySymbol site path term, request.site = site
  | site, path, .app symbol args => by
      unfold dataRequests
      split
      · simp
      · exact argsRequests_site site path 0 args
  | _, _, .lit _ | _, _, .var _ | _, _, .dictionaryCall _ _ _ _ | _, _, .truth | _, _, .falsity | _, _, .conj _ _
  | _, _, .disj _ _ | _, _, .imp _ _ | _, _, .defaultNeg _ | _, _, .forallVar _ _ | _, _, .existsVar _ _
  | _, _, .equal _ _ => by simp [dataRequests]

theorem argsRequests_site : ∀ (site : Site) (path : List Nat) (index : Nat) (args : List (Term Variable Literal Symbol)),
    ∀ request ∈ argsRequests hoApplySymbol site path index args, request.site = site
  | _, _, _, [] => by simp [argsRequests]
  | site, path, index, arg :: rest => by
      simp only [argsRequests, List.mem_append]
      rintro request (inside | inside)
      · exact dataRequests_site site _ arg request inside
      · exact argsRequests_site site path _ rest request inside
end

theorem goalRequests_site : ∀ (site : Site) (path : List Nat) (goal : Term Variable Literal Symbol),
    ∀ request ∈ goalRequests hoApplySymbol site path goal, request.site = site
  | site, path, .app symbol args => by
      unfold goalRequests
      split
      · simp
      · exact argsRequests_site site path 0 args
  | site, path, .conj left right => by
      simp only [goalRequests, List.mem_append]
      rintro request (inside | inside)
      · exact goalRequests_site site _ left request inside
      · exact goalRequests_site site _ right request inside
  | site, path, .defaultNeg body => by
      simpa only [goalRequests] using goalRequests_site site _ body
  | _, _, .truth | _, _, .falsity | _, _, .var _ | _, _, .equal _ _ | _, _, .dictionaryCall _ _ _ _ | _, _, .lit _
  | _, _, .disj _ _ | _, _, .imp _ _ | _, _, .forallVar _ _ | _, _, .existsVar _ _ => by simp [goalRequests]

/-- A KB clause's requests sit at its head or at one of its body goals. -/
theorem clauseRequests_site (guard : Symbol → Bool) (index : Nat) (clause : HornClause Variable Literal Symbol) :
    ∀ request ∈ clauseRequests hoApplySymbol guard index clause,
      request.site = .head index ∨ ∃ position, request.site = .body index position := by
  have body : ∀ (position : Nat) (goals : List (Term Variable Literal Symbol)),
      ∀ request ∈ bodyRequests hoApplySymbol index position goals, ∃ position, request.site = .body index position := by
    intro position goals
    induction goals generalizing position with
    | nil => simp [bodyRequests]
    | cons goal rest ih =>
        simp only [bodyRequests, List.mem_append]
        rintro request (inside | inside)
        · exact ⟨position, goalRequests_site _ _ goal request inside⟩
        · exact ih (position + 1) request inside
  cases clause with
  | goal _ => simp [clauseRequests]
  | definite head goals =>
      simp only [clauseRequests, List.mem_append]
      rintro request (inside | inside)
      · left
        cases head with
        | app symbol args =>
            by_cases ho : symbol = hoApplySymbol
            · simp only [headRequests, ho, ↓reduceIte, List.mem_singleton] at inside
              rw [inside]
            · simp only [headRequests, ho, ↓reduceIte, List.mem_append] at inside
              rcases inside with guarded | inside
              · by_cases guardHead : guard symbol = true
                · simp only [guardHead, ↓reduceIte, List.mem_singleton] at guarded
                  rw [guarded]
                · simp [guardHead] at guarded
              · exact argsRequests_site _ _ 0 args request inside
        | _ => simp only [headRequests, List.mem_singleton] at inside; rw [inside]
      · exact .inr (body 0 goals request inside)

end Sites

/-! ## Guard atoms

Guards are atoms over the signature's membership symbols. Their generated
clauses (`Elaboration.signatureKb`) are non-ground and recursive, so they are
outside P0 clause search, and P0 does not reject an input because of them. A
ground guard atom is decided instead, by an evaluator that follows the
generated clauses symbol by symbol on the structure of the term, and takes
assumed guard atoms of the context as facts: `m(c(t₁…tₖ))` by a listed rule
of a domain with membership symbol `m`, `D_all(t)` by some declared domain,
`P_n(s)` by a registered reference, and any of them by an assumption. It
decides exactly the least set of guard atoms closed under the generated
clauses and the context (`guardHolds_iff`, `Generated`), and every decided atom
is derivable from the generated clauses under the context (`Generated.derives`).
A plan lists the decided guards of its goals as facts; the others are not in
that set and have no candidate. -/

section Guards

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  (signature : SignatureSnapshot Domain Symbol) (rules : List (Rule Domain Symbol))
  (context : ProofContext Variable Literal Symbol)

/-- A guard atom the context assumes. -/
def assumed (symbol : Symbol) (term : Term Variable Literal Symbol) : Bool :=
  context.any fun assumption => identical assumption (.app symbol [term])

mutual
/-- The routes to a guard atom other than `D_all(x) :- m_D(x)`: an assumption,
a membership clause whose arguments hold, a registered predicate's fact. -/
def guardBase (symbol : Symbol) : Term Variable Literal Symbol → Bool
  | .app constructor args =>
      assumed context symbol (.app constructor args) ||
        (rules.any fun rule => decide (signature.naming.membershipSymbol rule.result = symbol) &&
          decide (rule.symbol = constructor) && guardArgs rule.fields args) ||
        (signature.signature.predicates.any fun declaration =>
          decide (signature.naming.predicateSymbol declaration.arity = symbol) &&
            decide (constructor = declaration.symbol) && args.isEmpty)
  | term => assumed context symbol term

/-- Every argument holds for its field's membership symbol. -/
def guardArgs : List Domain → List (Term Variable Literal Symbol) → Bool
  | [], [] => true
  | field :: fields, arg :: args =>
      (guardBase (signature.naming.membershipSymbol field) arg ||
        (decide (signature.naming.membershipSymbol field = signature.naming.dataSymbol) &&
          signature.signature.data.domains.any fun domain => guardBase (signature.naming.membershipSymbol domain) arg)) &&
        guardArgs fields args
  | _, _ => false
end

/-- A guard atom holds: by a base route, or for `D_all` by a base route of some
declared domain's membership symbol. -/
def guardHolds (symbol : Symbol) (term : Term Variable Literal Symbol) : Bool :=
  guardBase signature rules context symbol term ||
    (decide (symbol = signature.naming.dataSymbol) &&
      signature.signature.data.domains.any fun domain =>
        guardBase signature rules context (signature.naming.membershipSymbol domain) term)

/-- Decide a ground guard atom. -/
def decideGuard : Term Variable Literal Symbol → Bool
  | .app symbol [arg] => guardHolds signature rules context symbol arg
  | _ => false

/-- The guard atoms the generated clauses derive from the context's
assumptions: the least set containing the assumed guard atoms and closed under
the membership clauses, `D_all(x) :- m_D(x)`, and the registered facts. -/
inductive Generated : Symbol → Term Variable Literal Symbol → Prop where
  | assumed {symbol : Symbol} {term : Term Variable Literal Symbol} (member : Term.app symbol [term] ∈ context) :
      Generated symbol term
  | member {rule : Rule Domain Symbol} (declared : signature.signature.data.definitions rule)
      {args : List (Term Variable Literal Symbol)} (length : args.length = rule.fields.length)
      (each : ∀ pair ∈ rule.fields.zip args, Generated (signature.naming.membershipSymbol pair.1) pair.2) :
      Generated (signature.naming.membershipSymbol rule.result) (.app rule.symbol args)
  | data {domain : Domain} {term : Term Variable Literal Symbol}
      (member : Generated (signature.naming.membershipSymbol domain) term) :
      Generated signature.naming.dataSymbol term
  | predicate {declaration : PredicateDeclaration Symbol} (registered : declaration ∈ signature.signature.predicates) :
      Generated (signature.naming.predicateSymbol declaration.arity) (.app declaration.symbol [])

variable {signature rules context}

theorem assumed_iff {symbol : Symbol} {term : Term Variable Literal Symbol} :
    assumed context symbol term = true ↔ Term.app symbol [term] ∈ context := by
  simp only [assumed, List.any_eq_true, identical_iff]
  exact ⟨fun ⟨assumption, member, same⟩ => same ▸ member, fun member => ⟨_, member, rfl⟩⟩

theorem guardArgs_cons {field : Domain} {fields : List Domain} {arg : Term Variable Literal Symbol}
    {args : List (Term Variable Literal Symbol)} :
    guardArgs signature rules context (field :: fields) (arg :: args) =
      (guardHolds signature rules context (signature.naming.membershipSymbol field) arg &&
        guardArgs signature rules context fields args) := by
  rw [guardArgs]; rfl

theorem guardArgs_iff : ∀ {fields : List Domain} {args : List (Term Variable Literal Symbol)},
    guardArgs signature rules context fields args = true ↔ args.length = fields.length ∧
      ∀ pair ∈ fields.zip args, guardHolds signature rules context (signature.naming.membershipSymbol pair.1) pair.2 = true
  | [], [] => by simp [guardArgs]
  | [], _ :: _ => by simp [guardArgs]
  | _ :: _, [] => by simp [guardArgs]
  | field :: fields, arg :: args => by
      rw [guardArgs_cons, Bool.and_eq_true, guardArgs_iff]
      simp only [List.length_cons, Nat.add_right_cancel_iff, List.zip_cons_cons, List.mem_cons, forall_eq_or_imp]
      exact ⟨fun ⟨first, sameLength, rest⟩ => ⟨sameLength, first, rest⟩,
        fun ⟨sameLength, first, rest⟩ => ⟨first, sameLength, rest⟩⟩

mutual
theorem guardBase_generated (listed : ∀ rule ∈ rules, signature.signature.data.definitions rule) :
    ∀ (symbol : Symbol) (term : Term Variable Literal Symbol), guardBase signature rules context symbol term = true →
      Generated signature context symbol term
  | symbol, .app constructor args, holds => by
      rw [guardBase] at holds
      simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at holds
      rcases holds with (fromContext | ⟨rule, member, ⟨rfl, rfl⟩, argsHold⟩) |
          ⟨declaration, registered, ⟨rfl, rfl⟩, empty⟩
      · exact .assumed (assumed_iff.mp fromContext)
      · obtain ⟨length, pairs⟩ := guardArgs_generated listed rule.fields args argsHold
        exact .member (listed rule member) length pairs
      · rw [List.isEmpty_iff.mp empty]; exact .predicate registered
  | _, .var _, holds | _, .lit _, holds | _, .truth, holds | _, .falsity, holds | _, .conj _ _, holds
  | _, .disj _ _, holds | _, .imp _ _, holds | _, .defaultNeg _, holds | _, .forallVar _ _, holds
  | _, .existsVar _ _, holds | _, .dictionaryCall _ _ _ _, holds | _, .equal _ _, holds => by
      simp only [guardBase] at holds
      exact .assumed (assumed_iff.mp holds)

theorem guardArgs_generated (listed : ∀ rule ∈ rules, signature.signature.data.definitions rule) :
    ∀ (fields : List Domain) (args : List (Term Variable Literal Symbol)),
      guardArgs signature rules context fields args = true → args.length = fields.length ∧
        ∀ pair ∈ fields.zip args, Generated signature context (signature.naming.membershipSymbol pair.1) pair.2
  | [], [], _ => ⟨rfl, by simp⟩
  | field :: fields, arg :: args, holds => by
      rw [guardArgs] at holds
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at holds
      obtain ⟨first, rest⟩ := holds
      obtain ⟨length, pairs⟩ := guardArgs_generated listed fields args rest
      refine ⟨by simp [length], fun pair member => ?_⟩
      simp only [List.zip_cons_cons, List.mem_cons] at member
      rcases member with rfl | inside
      · rcases first with direct | ⟨same, domain, _, viaDomain⟩
        · exact guardBase_generated listed _ arg direct
        · rw [same]; exact .data (guardBase_generated listed _ arg viaDomain)
      · exact pairs pair inside
  | [], _ :: _, holds | _ :: _, [], holds => by simp [guardArgs] at holds
end

/-- The evaluator decides exactly the generated set, when the listed rules are
exactly the declared ones. -/
theorem guardHolds_iff (listed : ∀ rule ∈ rules, signature.signature.data.definitions rule)
    (complete : ∀ rule, signature.signature.data.definitions rule → rule ∈ rules) {symbol : Symbol}
    {term : Term Variable Literal Symbol} :
    guardHolds signature rules context symbol term = true ↔ Generated signature context symbol term := by
  constructor
  · intro holds
    simp only [guardHolds, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at holds
    rcases holds with direct | ⟨rfl, domain, _, viaDomain⟩
    · exact guardBase_generated listed symbol term direct
    · exact .data (guardBase_generated listed _ term viaDomain)
  · intro generated
    induction generated with
    | assumed member =>
        rename_i symbol term
        cases term <;> simp [guardHolds, guardBase, assumed_iff.mpr member]
    | @member rule declared args length each ih =>
        have argsHold : guardArgs signature rules context rule.fields args = true :=
          guardArgs_iff.mpr ⟨length, fun pair inside => ih pair inside⟩
        have ruleHolds : (rules.any fun candidate =>
            decide (signature.naming.membershipSymbol candidate.result = signature.naming.membershipSymbol rule.result) &&
              decide (candidate.symbol = rule.symbol) && guardArgs signature rules context candidate.fields args) = true :=
          List.any_eq_true.mpr ⟨rule, complete rule declared, by simp [argsHold]⟩
        simp [guardHolds, guardBase, ruleHolds]
    | @data domain term member ih =>
        simp only [guardHolds, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at ih ⊢
        rcases ih with direct | ⟨same, other, inside, viaOther⟩
        · exact .inr ⟨by simp, domain, signature.signature.data.complete domain, direct⟩
        · exact .inr ⟨by simp, other, inside, viaOther⟩
    | @predicate declaration registered =>
        simp only [guardHolds, guardBase, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq]
        exact .inl (.inr ⟨declaration, registered, by simp⟩)

omit [DecidableEq Literal] [DecidableEq Symbol] in
/-- Every generated guard atom is derivable from the generated signature
clauses under the context, with the clause rule and assumptions only. -/
theorem Generated.derives {hoApplySymbol : Symbol} {names : Nat → Variable}
    (distinct : DistinctNames signature.signature.data.definitions names) {naf : NafFailure Variable Literal Symbol}
    {symbol : Symbol} {term : Term Variable Literal Symbol} (generated : Generated signature context symbol term) :
    Derives hoApplySymbol (Elaboration.signatureKb signature names) context (.app symbol [term]) naf := by
  induction generated with
  | assumed member => exact .assumption member
  | @member rule declared args length each ih =>
      let children : Fin rule.fields.length → Term Variable Literal Symbol := fun index => args[index.1]'(by omega)
      have ofFn : List.ofFn children = args := by
        apply List.ext_getElem
        · simp [length]
        · intro index first second; simp [children]
      have contains : membershipClause (Literal := Literal) signature.signature.membershipSymbol names rule ∈
          Elaboration.signatureKb signature names := .inl ⟨rule, declared, rfl⟩
      have derived := membershipClause_derives (hoApplySymbol := hoApplySymbol) distinct declared contains
        (context := context) (naf := naf) children fun index => by
          have pairMember : (rule.fields[index], children index) ∈ rule.fields.zip args := by
            rw [List.mem_iff_getElem]
            exact ⟨index.1, by simp [length], by simp [children]⟩
          exact ih _ pairMember
      rw [ofFn] at derived
      exact derived
  | @data domain term member ih =>
      have dataMember : Elaboration.dataClause (Literal := Literal) signature.naming (names 0) domain ∈
          Elaboration.signatureKb signature names := .inr (.inl ⟨domain, rfl⟩)
      exact .clause dataMember (σ := Substitution.single (names 0) term)
        (.app (.cons (Substitutes.singleVar _ _) .nil))
        (SubstitutesList.conjunction (.cons (.app (.cons (Substitutes.singleVar _ _) .nil)) .nil))
        (.conjIntro ih .truth)
  | @predicate declaration registered =>
      have fact : Elaboration.predicateFact (Variable := Variable) (Literal := Literal) signature.naming declaration ∈
          Elaboration.signatureKb signature names := .inr (.inr ⟨declaration, registered, rfl⟩)
      exact .clause fact (Substitutes.identity _) (Substitutes.identity _) .truth

/-- A decided guard is derivable from the generated signature clauses under
the context. -/
theorem decideGuard_derives {hoApplySymbol : Symbol} {names : Nat → Variable}
    (listed : ∀ rule ∈ rules, signature.signature.data.definitions rule)
    (complete : ∀ rule, signature.signature.data.definitions rule → rule ∈ rules)
    (distinct : DistinctNames signature.signature.data.definitions names) {atom : Term Variable Literal Symbol}
    (decided : decideGuard signature rules context atom = true) {naf : NafFailure Variable Literal Symbol} :
    Derives hoApplySymbol (Elaboration.signatureKb signature names) context atom naf := by
  match atom, decided with
  | .app symbol [arg], decided =>
      exact ((guardHolds_iff listed complete).mp decided).derives distinct

end Guards

/-! ## The checker -/

section Check

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable]

attribute [local instance] termEq

attribute [local instance] clauseEq

def isLowered : ClauseSource → Bool
  | .lowered _ => true
  | .signature => false

namespace Input

variable (input : Input Domain Variable Literal Symbol)

/-- The KB clauses of the effective program with their lowering indices; the
generated signature clauses are replaced by guard decisions. -/
def kbClauses : List (Nat × HornClause Variable Literal Symbol) :=
  input.program.clauses.filterMap fun entry =>
    match entry.source with
    | .lowered index => some (index, entry.clause)
    | .signature => none

/-- The KB clauses as program entries, in program order. -/
def kbEntries : List (ProgramClause Variable Literal Symbol) :=
  input.kbClauses.map fun pair => ⟨.lowered pair.1, pair.2⟩

/-- The guard symbols of the signature. -/
def guard : Symbol → Bool := guardSymbol input.signature

/-- Positions of program clauses marked as generated from the signature that
the signature does not generate. -/
def forged : List Nat :=
  input.program.clauses.zipIdx.filterMap fun (entry, position) =>
    match entry.source with
    | .signature => if entry.clause ∈ signatureClauses input.signature input.names input.rules then none else some position
    | .lowered _ => none

/-- Clauses the signature generates that the program does not carry: such a
program is not the snapshot's effective program. -/
def unlisted : List (HornClause Variable Literal Symbol) :=
  (signatureClauses input.signature input.names input.rules).filter fun clause =>
    clause ∉ input.program.clauses.map ProgramClause.clause

/-- Every formula of the input outside the P0 classes, with its capability. -/
def requests (hoApplySymbol : Symbol) : List (Request Variable Literal Symbol) :=
  goalRequests hoApplySymbol .goal [] input.goal ++ contextRequests hoApplySymbol 0 input.context ++
    input.kbClauses.flatMap fun pair => clauseRequests hoApplySymbol input.guard pair.1 pair.2

/-- The atoms the query and the KB clause bodies may ask for. -/
def goalAtoms : List (Term Variable Literal Symbol) :=
  atoms input.goal ++ input.kbClauses.flatMap fun pair =>
    match pair.2 with
    | .definite _ body => atoms (.conjunction body)
    | .goal _ => []

/-- The guard atoms asked for that the signature decides: the plan's facts. -/
def guardFacts : List (Term Variable Literal Symbol) :=
  ((input.goalAtoms.filter fun atom =>
      match atom with
      | .app symbol _ => input.guard symbol
      | _ => false).filter (decideGuard input.signature input.rules input.context)).eraseDups

/-- The plan's clauses: the KB clauses, then the decided guard facts. `check`
passes the facts it computed once. -/
def planEntries (facts : List (Term Variable Literal Symbol) := input.guardFacts) :
    List (ProgramClause Variable Literal Symbol) :=
  input.kbEntries ++ facts.map fun atom => ⟨.signature, .definite atom []⟩

def planClauses (facts : List (Term Variable Literal Symbol) := input.guardFacts) :
    List (HornClause Variable Literal Symbol) :=
  (input.planEntries facts).map ProgramClause.clause

/-- Every atom of the dependency graph: heads, body atoms (also under NAF), the
query's atoms, and the assumptions. -/
def vertices (facts : List (Term Variable Literal Symbol) := input.guardFacts) : List (Term Variable Literal Symbol) :=
  ((input.planClauses facts).flatMap (fun
    | .definite head body => head :: atoms (.conjunction body)
    | .goal _ => []) ++ atoms input.goal ++ input.context).eraseDups

/-- The computed rank of the whole program's dependency graph. -/
def rank (facts : List (Term Variable Literal Symbol) := input.guardFacts) : List (Term Variable Literal Symbol × Nat) :=
  topoRank (edges (input.planClauses facts)) (input.vertices facts)

/-- KB clauses with an edge the rank does not decrease. Without them the rank
is a witness; with them under the computed rank, the graph has a cycle. -/
def unranked (rank : List (Term Variable Literal Symbol × Nat) := input.rank) : List (Request Variable Literal Symbol) :=
  input.kbClauses.filterMap fun pair =>
    match pair.2 with
    | .definite head body =>
        if (atoms (.conjunction body)).all fun atom => rankOf rank atom < rankOf rank head then none
        else some ⟨.head pair.1, [], head, .acyclicStrategy⟩
    | .goal _ => none

/-- KB clauses on a dependency cycle, through NAF or not: an atom of the body
reaches the head. A clause that only depends on a cycle is not listed: its
predicate becomes admissible once the cycle has a strategy. -/
def cycleRequests : List (Request Variable Literal Symbol) :=
  let graph := edges input.planClauses
  let bound := input.vertices.length
  input.kbClauses.filterMap fun pair =>
    match pair.2 with
    | .definite head body =>
        if (atoms (.conjunction body)).any fun atom => (reach graph bound [atom]).contains head then
          some ⟨.head pair.1, [], head, .acyclicStrategy⟩
        else none
    | .goal _ => none

end Input

/-- The P0 syntactic classes, for every formula of the input. -/
structure P0Input (hoApplySymbol : Symbol) (input : Input Domain Variable Literal Symbol) : Prop where
  goal : IsGoal hoApplySymbol input.goal ∧ Ordinary hoApplySymbol input.goal
  context : ∀ atom ∈ input.context, IsAtom hoApplySymbol atom ∧ Ordinary hoApplySymbol atom
  clauses : ∀ pair ∈ input.kbClauses, ClauseOk hoApplySymbol input.guard pair.2

/-- The KB clauses are acyclic: some rank decreases along every dependency edge. -/
def Acyclic (input : Input Domain Variable Literal Symbol) : Prop :=
  ∃ witness : Term Variable Literal Symbol → Nat, Ranked witness (input.kbClauses.map Prod.snd)

variable {hoApplySymbol : Symbol} {input : Input Domain Variable Literal Symbol}

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
/-- No request exactly when every formula is in its P0 class. -/
theorem requests_nil_iff : input.requests hoApplySymbol = [] ↔ P0Input hoApplySymbol input := by
  simp only [Input.requests, List.append_eq_nil_iff, goalRequests_nil, contextRequests_nil, List.flatMap_eq_nil_iff,
    clauseRequests_nil]
  exact ⟨fun ⟨⟨goal, context⟩, clauses⟩ => ⟨goal, context, clauses⟩,
    fun ⟨goal, context, clauses⟩ => ⟨⟨goal, context⟩, clauses⟩⟩

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem atoms_ok : ∀ {goal : Term Variable Literal Symbol}, IsGoal hoApplySymbol goal → Ordinary hoApplySymbol goal →
    ∀ atom ∈ atoms goal, IsAtom hoApplySymbol atom ∧ Ordinary hoApplySymbol atom
  | _, .atom atomic, ordinary, atom, member => by
      cases atomic with
      | app _ _ =>
          simp only [atoms, List.mem_singleton] at member
          subst member
          exact ⟨.app (by assumption) (by assumption), ordinary⟩
  | _, .truth, _, _, member | _, .falsity, _, _, member => by simp [atoms] at member
  | _, .conj left right, .conj leftOrdinary rightOrdinary, atom, member => by
      rcases List.mem_append.mp member with inside | inside
      · exact atoms_ok left leftOrdinary atom inside
      · exact atoms_ok right rightOrdinary atom inside
  | _, .defaultNeg body, .defaultNeg inner, atom, member => atoms_ok body inner atom member

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem goalAtoms_ok (valid : P0Input hoApplySymbol input) :
    ∀ atom ∈ input.goalAtoms, IsAtom hoApplySymbol atom ∧ Ordinary hoApplySymbol atom := by
  intro atom member
  rcases List.mem_append.mp member with inside | inside
  · exact atoms_ok valid.goal.1 valid.goal.2 atom inside
  · obtain ⟨pair, pairMember, found⟩ := List.mem_flatMap.mp inside
    obtain ⟨clauseValid, clauseOrdinary, _⟩ := valid.clauses pair pairMember
    revert found
    generalize pair.2 = clause at clauseValid clauseOrdinary
    cases clauseValid with
    | definite _ goals =>
        intro found
        exact atoms_ok (conjunction_isGoal goals) (Ordinary.conjunction clauseOrdinary.2) atom found

omit [FreshNames Variable] in
theorem mem_guardFacts {atom : Term Variable Literal Symbol} (member : atom ∈ input.guardFacts) :
    atom ∈ input.goalAtoms ∧ decideGuard input.signature input.rules input.context atom = true := by
  have inside := List.mem_eraseDups.mp member
  obtain ⟨filtered, decided⟩ := List.mem_filter.mp inside
  exact ⟨(List.mem_filter.mp filtered).1, decided⟩

omit [FreshNames Variable] in
theorem mem_planClauses {facts : List (Term Variable Literal Symbol)} {clause : HornClause Variable Literal Symbol} :
    clause ∈ input.planClauses facts ↔
      (∃ pair ∈ input.kbClauses, pair.2 = clause) ∨ ∃ atom ∈ facts, .definite atom [] = clause := by
  simp [Input.planClauses, Input.planEntries, Input.kbEntries]

omit [FreshNames Variable] in
theorem planClauses_ok (valid : P0Input hoApplySymbol input) :
    ∀ clause ∈ input.planClauses, IsClause hoApplySymbol clause ∧ ClauseOrdinary hoApplySymbol clause := by
  intro clause member
  rcases mem_planClauses.mp member with ⟨pair, pairMember, rfl⟩ | ⟨atom, factMember, rfl⟩
  · obtain ⟨clauseValid, clauseOrdinary, _⟩ := valid.clauses pair pairMember
    exact ⟨clauseValid, clauseOrdinary⟩
  · obtain ⟨atomic, ordinary⟩ := goalAtoms_ok valid atom (mem_guardFacts factMember).1
    exact ⟨.definite atomic (by simp), ordinary, by simp⟩

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem edges_facts (facts : List (Term Variable Literal Symbol)) :
    edges (facts.map fun atom => (HornClause.definite atom [] : HornClause Variable Literal Symbol)) = [] := by
  induction facts with
  | nil => rfl
  | cons fact rest ih => simp [edges, atoms, Term.conjunction]

omit [FreshNames Variable] in
theorem planClauses_edges :
    edges input.planClauses = edges (input.kbClauses.map Prod.snd) := by
  simp only [Input.planClauses, Input.planEntries, Input.kbEntries, List.map_append, List.map_map, Function.comp_def]
  rw [edges, List.flatMap_append, ← edges, ← edges]
  rw [edges_facts, List.append_nil]

omit [FreshNames Variable] in
/-- Without an unranked clause, the rank is a witness. -/
theorem unranked_ranked {rank : List (Term Variable Literal Symbol × Nat)} {facts : List (Term Variable Literal Symbol)}
    (acyclic : input.unranked rank = []) : Ranked (rankOf rank) (input.planClauses facts) := by
  intro head body member atom inside
  rcases mem_planClauses.mp member with ⟨pair, pairMember, pairClause⟩ | ⟨fact, _, factClause⟩
  · have none := List.filterMap_eq_nil_iff.mp acyclic pair pairMember
    rw [pairClause] at none
    simp only at none
    split at none
    · rename_i decreasing
      exact of_decide_eq_true (List.all_eq_true.mp decreasing atom inside)
    · cases none
  · cases factClause
    simp [atoms, Term.conjunction] at inside

omit [FreshNames Variable] in
/-- A program with no unlisted clause carries every generated signature clause. -/
theorem signatureKb_carried (generated : input.unlisted = []) {clause : HornClause Variable Literal Symbol}
    (member : clause ∈ Elaboration.signatureKb input.signature input.names) : clause ∈ input.program.kb := by
  have carried := List.filter_eq_nil_iff.mp generated clause (signatureClauses_complete input.complete member)
  simp only [decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Classical.not_not,
    List.mem_map] at carried
  obtain ⟨entry, inside, same⟩ := carried
  exact ⟨entry, inside, same⟩

/-- The run input of a plan, built from an input with no request: the KB
clauses and the decided guard facts, the context, the goal, and a rank with no
unranked clause. -/
def Input.ground (hoApplySymbol : Symbol) (input : Input Domain Variable Literal Symbol)
    (valid : input.requests hoApplySymbol = []) (facts : List (Term Variable Literal Symbol))
    (factsEq : facts = input.guardFacts) (rank : List (Term Variable Literal Symbol × Nat))
    (acyclic : input.unranked rank = []) : P0.Ground Variable Literal Symbol hoApplySymbol where
  program := ⟨input.planClauses facts, fun clause member => by
    subst factsEq; exact (planClauses_ok (requests_nil_iff.mp valid) clause member).1⟩
  entries := input.planEntries facts
  listed := rfl
  context := ⟨input.context, fun atom member => ((requests_nil_iff.mp valid).context atom member).1⟩
  goal := input.goal
  valid := (requests_nil_iff.mp valid).goal.1
  ordinary := (requests_nil_iff.mp valid).goal.2
  clausesOrdinary := fun clause member => by
    subst factsEq; exact (planClauses_ok (requests_nil_iff.mp valid) clause member).2
  contextOrdinary := fun atom member => ((requests_nil_iff.mp valid).context atom member).2
  rank := rankOf rank
  ranked := unranked_ranked acyclic

/-- What admission establishes for a plan's parts: the input's declarations
are consistent and its program carries every generated clause, every formula
is in its P0 class, and the run input runs the input's KB clauses with exactly
the decided guard facts, under the input's context and for its goal. The run
input carries the rank witness (`ground.ranked`). -/
structure Admits (hoApplySymbol : Symbol) (input : Input Domain Variable Literal Symbol)
    (guards : List (Term Variable Literal Symbol)) (ground : P0.Ground Variable Literal Symbol hoApplySymbol) :
    Prop where
  consistent : input.forged = []
  generated : input.unlisted = []
  classes : P0Input hoApplySymbol input
  facts : guards = input.guardFacts
  entries : ground.entries = input.kbEntries ++ guards.map fun atom => ⟨.signature, .definite atom []⟩
  context : ground.context.assumptions = input.context
  goal : ground.goal = input.goal

/-- A Ready plan: the input it was admitted for, the decided guard facts, the
run input, and what admission established about them, so no plan pairs an
input with another input's run. It records the finite candidate source and
the rank witness, not a proof path; it says nothing about whether the goal
holds. -/
structure Plan (Domain Variable Literal Symbol : Type) [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
    (hoApplySymbol : Symbol) where
  input : Input Domain Variable Literal Symbol
  guards : List (Term Variable Literal Symbol)
  ground : P0.Ground Variable Literal Symbol hoApplySymbol
  admits : Admits hoApplySymbol input guards ground

inductive Result (Domain Variable Literal Symbol : Type) [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
    (hoApplySymbol : Symbol) where
  | ready (plan : Plan Domain Variable Literal Symbol hoApplySymbol)
  | needsEvidence (request : Request Variable Literal Symbol) (more : List (Request Variable Literal Symbol))
  | invalid (diagnostic : Diagnostic)

/-- P0 admission. Declarations are checked first, then every formula's class,
then the rank of the whole dependency graph; a failed rank reports the clauses
on a cycle. The guard facts and the rank are computed once. No rule of the
program runs. -/
def check (hoApplySymbol : Symbol) (input : Input Domain Variable Literal Symbol) :
    Result Domain Variable Literal Symbol hoApplySymbol :=
  match consistent : input.forged with
  | position :: _ => .invalid (.signatureClause position)
  | [] =>
      match generated : input.unlisted with
      | clause :: _ =>
          .invalid (.missingSignatureClause ((signatureClauses input.signature input.names input.rules).idxOf clause))
      | [] =>
          match valid : input.requests hoApplySymbol with
          | request :: more => .needsEvidence request more
          | [] =>
              let facts := input.guardFacts
              let rank := input.rank facts
              match acyclic : input.unranked rank with
              | [] =>
                  .ready ⟨input, facts, input.ground hoApplySymbol valid facts rfl rank acyclic,
                    ⟨consistent, generated, requests_nil_iff.mp valid, rfl, rfl, rfl, rfl⟩⟩
              | first :: rest =>
                  match input.cycleRequests with
                  | request :: more => .needsEvidence request more
                  | [] => .needsEvidence first rest

/-! ## What `check` establishes -/

/-- The P0 admission judgment: the plan was admitted for exactly this input,
with what admission establishes about it (`Admits`). -/
structure P0Admitted (hoApplySymbol : Symbol) (input : Input Domain Variable Literal Symbol)
    (plan : Plan Domain Variable Literal Symbol hoApplySymbol) : Prop where
  exact : plan.input = input
  admits : Admits hoApplySymbol input plan.guards plan.ground

omit [FreshNames Variable] in
/-- Every plan is admitted for its own input. -/
theorem Plan.admitted (plan : Plan Domain Variable Literal Symbol hoApplySymbol) :
    P0Admitted hoApplySymbol plan.input plan :=
  ⟨rfl, plan.admits⟩

omit [FreshNames Variable] in
/-- A Ready plan's rank witnesses that its input's KB clauses are acyclic. -/
theorem Plan.acyclic (plan : Plan Domain Variable Literal Symbol hoApplySymbol) : Acyclic plan.input := by
  refine ⟨plan.ground.rank, fun head body member atom inside => plan.ground.ranked head body ?_ atom inside⟩
  rw [← plan.ground.listed, plan.admits.entries]
  obtain ⟨pair, pairMember, same⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨⟨.lowered pair.1, pair.2⟩, List.mem_append_left _ (List.mem_map_of_mem pairMember), same⟩

omit [FreshNames Variable] in
/-- `check_ready_sound`: a computed Ready is the admission judgment. -/
theorem check_ready_sound {plan : Plan Domain Variable Literal Symbol hoApplySymbol}
    (ready : check hoApplySymbol input = .ready plan) : P0Admitted hoApplySymbol input plan := by
  unfold check at ready
  split at ready
  · cases ready
  · rename_i consistent
    split at ready
    · cases ready
    · rename_i generated
      split at ready
      · cases ready
      · rename_i valid
        dsimp only at ready
        split at ready
        · cases ready
          exact ⟨rfl, consistent, generated, requests_nil_iff.mp valid, rfl, rfl, rfl, rfl⟩
        · split at ready <;> cases ready

omit [FreshNames Variable] in
/-- `check_p0_complete`: every consistent input whose program carries the
generated clauses, whose formulas are in the P0 classes, and whose KB clauses
are acyclic is Ready. Completeness for P0 inputs only, not for arbitrary
formulas. -/
theorem check_p0_complete (consistent : input.forged = []) (generated : input.unlisted = [])
    (classes : P0Input hoApplySymbol input) (acyclic : Acyclic input) :
    ∃ plan, check hoApplySymbol input = .ready plan := by
  have valid := requests_nil_iff.mpr classes
  have noCycle : input.unranked = [] := by
    obtain ⟨witness, ranked⟩ := acyclic
    have decreasing : ∀ edge ∈ edges input.planClauses, witness edge.2 < witness edge.1 := by
      rw [planClauses_edges]; exact ranked_iff_edges.mp ranked
    have endpoints : ∀ edge ∈ edges input.planClauses, edge.1 ∈ input.vertices ∧ edge.2 ∈ input.vertices := by
      intro edge member
      obtain ⟨body, clause, inside⟩ := mem_edges.mp member
      have headIn : edge.1 :: atoms (.conjunction body) ⊆ input.vertices := by
        intro vertex found
        exact List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_append_left _
          (List.mem_flatMap.mpr ⟨.definite edge.1 body, clause, found⟩)))
      exact ⟨headIn List.mem_cons_self, headIn (List.mem_cons_of_mem _ inside)⟩
    have ranks := topoRank_decreases ⟨witness, decreasing⟩ endpoints
    apply List.filterMap_eq_nil_iff.mpr
    intro pair member
    cases clauseEq : pair.2 with
    | goal body => rfl
    | definite head body =>
        have listed : HornClause.definite head body ∈ input.planClauses :=
          mem_planClauses.mpr (.inl ⟨pair, member, clauseEq⟩)
        have decreases : ((atoms (.conjunction body)).all fun atom => decide (rankOf input.rank atom < rankOf input.rank head)) = true :=
          List.all_eq_true.mpr fun atom inside =>
            decide_eq_true (ranks (head, atom) (mem_edges.mpr ⟨body, listed, inside⟩))
        simp only [decreases, ↓reduceIte]
  unfold check
  split
  · rename_i position rest forgedEq; rw [forgedEq] at consistent; cases consistent
  · split
    · rename_i clause rest unlistedEq; rw [unlistedEq] at generated; cases generated
    · split
      · rename_i request more requestsEq; rw [requestsEq] at valid; cases valid
      · dsimp only
        split
        · exact ⟨_, rfl⟩
        · rename_i first rest unrankedEq; rw [unrankedEq] at noCycle; cases noCycle

/-- What the program-level check answers. -/
inductive ProgramResult (Variable Literal Symbol : Type) where
  /-- Every P0 query on the program is Ready, and so decided. -/
  | decides
  /-- KB clauses outside the P0 classes or on a cycle, with what each needs. -/
  | needsEvidence (request : Request Variable Literal Symbol) (more : List (Request Variable Literal Symbol))
  /-- The program contradicts its declarations, for every query. -/
  | invalid (diagnostic : Diagnostic)

/-- P0 admission of a program for every query at once: `check` on the program
with the empty query (goal `true`, no assumptions). That query asks nothing of
its own, so every request and diagnostic is about the program. -/
def checkProgram (hoApplySymbol : Symbol) (base : ProgramInput Domain Variable Literal Symbol) :
    ProgramResult Variable Literal Symbol :=
  match check hoApplySymbol (base.ask [] .truth) with
  | .ready _ => .decides
  | .needsEvidence request more => .needsEvidence request more
  | .invalid diagnostic => .invalid diagnostic

omit [FreshNames Variable] in
/-- `checkProgram_ready`: a program the check accepts makes every P0 query
Ready, that is, every ground goal of the P0 classes under a ground atomic
context. The check is sufficient, not necessary: a recursive program may
decide its queries and still be rejected. -/
theorem checkProgram_ready {base : ProgramInput Domain Variable Literal Symbol}
    (accepted : checkProgram hoApplySymbol base = .decides)
    {context : ProofContext Variable Literal Symbol} {goal : Formula Variable Literal Symbol}
    (goalOk : IsGoal hoApplySymbol goal ∧ Ordinary hoApplySymbol goal)
    (contextOk : ∀ atom ∈ context, IsAtom hoApplySymbol atom ∧ Ordinary hoApplySymbol atom) :
    ∃ plan, check hoApplySymbol (base.ask context goal) = .ready plan := by
  unfold checkProgram at accepted
  split at accepted
  · rename_i plan ready
    have admitted := check_ready_sound ready
    have acyclic := admitted.exact ▸ plan.acyclic
    exact check_p0_complete (input := base.ask context goal) admitted.admits.consistent admitted.admits.generated
      ⟨goalOk, contextOk, admitted.admits.classes.clauses⟩ acyclic
  · cases accepted
  · cases accepted

omit [FreshNames Variable] in
/-- Invalid only for a contradicted declaration: a clause marked as generated
that the signature does not generate, or a generated clause the program does
not carry. P0 exclusion alone never makes an input invalid. -/
theorem check_invalid {diagnostic : Diagnostic} (invalid : check hoApplySymbol input = .invalid diagnostic) :
    (∃ position rest, input.forged = position :: rest ∧ diagnostic = .signatureClause position) ∨
      (input.forged = [] ∧ ∃ clause rest, input.unlisted = clause :: rest ∧
        diagnostic = .missingSignatureClause ((signatureClauses input.signature input.names input.rules).idxOf clause)) := by
  unfold check at invalid
  split at invalid
  · rename_i position rest forgedEq
    cases invalid
    exact .inl ⟨position, rest, forgedEq, rfl⟩
  · rename_i consistent
    split at invalid
    · rename_i clause rest unlistedEq
      cases invalid
      exact .inr ⟨consistent, clause, rest, unlistedEq, rfl⟩
    · split at invalid
      · cases invalid
      · dsimp only at invalid
        split at invalid
        · cases invalid
        · split at invalid <;> cases invalid

omit [FreshNames Variable] in
/-- NeedsEvidence lists every formula outside the P0 classes, or, when there is
none and the rank fails, every KB clause on a dependency cycle (the unranked
clauses only if no cycle was found, which `topoRank_decreases` excludes). It is
decided before any rule runs. -/
theorem check_needsEvidence {request : Request Variable Literal Symbol} {more : List (Request Variable Literal Symbol)}
    (needs : check hoApplySymbol input = .needsEvidence request more) :
    input.forged = [] ∧ input.unlisted = [] ∧ (input.requests hoApplySymbol = request :: more ∨
      (input.requests hoApplySymbol = [] ∧ input.unranked ≠ [] ∧
        (input.cycleRequests = request :: more ∨ (input.cycleRequests = [] ∧ input.unranked = request :: more)))) := by
  unfold check at needs
  split at needs
  · cases needs
  · rename_i consistent
    split at needs
    · cases needs
    · rename_i generated
      split at needs
      · rename_i first rest requestsEq
        cases needs
        exact ⟨consistent, generated, .inl requestsEq⟩
      · rename_i valid
        dsimp only at needs
        split at needs
        · cases needs
        · rename_i first rest unrankedEq
          split at needs
          · rename_i cyclesEq
            cases needs
            exact ⟨consistent, generated, .inr ⟨valid, by simp [unrankedEq], .inl cyclesEq⟩⟩
          · rename_i cyclesEq
            cases needs
            exact ⟨consistent, generated, .inr ⟨valid, by simp [unrankedEq], .inr ⟨cyclesEq, unrankedEq⟩⟩⟩

omit [FreshNames Variable] in
/-- Every request of the program-level check sits at a KB clause's head or
body: the empty query asks for nothing. -/
theorem checkProgram_needsEvidence {base : ProgramInput Domain Variable Literal Symbol}
    {request : Request Variable Literal Symbol} {more : List (Request Variable Literal Symbol)}
    (needs : checkProgram hoApplySymbol base = .needsEvidence request more) :
    ∀ found ∈ request :: more, ∃ index, found.site = .head index ∨ ∃ position, found.site = .body index position := by
  unfold checkProgram at needs
  split at needs
  · cases needs
  · rename_i first rest asked
    cases needs
    have headSite : ∀ {requests : List (Request Variable Literal Symbol)},
        (∀ found ∈ requests, ∃ index, found.site = .head index) →
          ∀ found ∈ requests, ∃ index, found.site = .head index ∨ ∃ position, found.site = .body index position :=
      fun sited found inside => (sited found inside).elim fun index same => ⟨index, .inl same⟩
    have kbSites : ∀ found ∈ (base.ask [] .truth).kbClauses.flatMap
        (fun pair => clauseRequests hoApplySymbol (base.ask [] .truth).guard pair.1 pair.2),
        ∃ index, found.site = .head index ∨ ∃ position, found.site = .body index position := by
      intro found inside
      obtain ⟨pair, _, inside⟩ := List.mem_flatMap.mp inside
      exact ⟨pair.1, clauseRequests_site _ _ _ found inside⟩
    have rankSites : ∀ found ∈ (base.ask [] .truth).unranked, ∃ index, found.site = .head index := by
      intro found inside
      obtain ⟨pair, _, made⟩ := List.mem_filterMap.mp inside
      revert made
      cases pair.2 with
      | definite head body =>
          dsimp only
          split <;> intro made <;> cases made <;> exact ⟨_, rfl⟩
      | goal _ => intro made; cases made
    have cycleSites : ∀ found ∈ (base.ask [] .truth).cycleRequests, ∃ index, found.site = .head index := by
      intro found inside
      obtain ⟨pair, _, made⟩ := List.mem_filterMap.mp inside
      revert made
      cases pair.2 with
      | definite head body =>
          dsimp only
          split <;> intro made <;> cases made <;> exact ⟨_, rfl⟩
      | goal _ => intro made; cases made
    obtain ⟨_, _, found⟩ := check_needsEvidence asked
    rcases found with requested | ⟨_, _, cycles | ⟨_, unranked⟩⟩
    · intro found inside
      rw [← requested] at inside
      simp only [Input.requests, ProgramInput.ask, goalRequests, contextRequests, List.nil_append] at inside
      exact kbSites found inside
    · rw [← cycles]; exact headSite cycleSites
    · rw [← unranked]; exact headSite rankSites
  · cases needs

omit [FreshNames Variable] in
/-- A program the check finds invalid is invalid for every query, with the
same diagnostic: the diagnostics are about the program. -/
theorem checkProgram_invalid {base : ProgramInput Domain Variable Literal Symbol} {diagnostic : Diagnostic}
    (invalid : checkProgram hoApplySymbol base = .invalid diagnostic)
    (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    check hoApplySymbol (base.ask context goal) = .invalid diagnostic := by
  unfold checkProgram at invalid
  split at invalid
  · cases invalid
  · cases invalid
  · rename_i found asked
    cases invalid
    have forgedEq : (base.ask context goal).forged = (base.ask [] .truth).forged := rfl
    have unlistedEq : (base.ask context goal).unlisted = (base.ask [] .truth).unlisted := rfl
    rcases check_invalid asked with ⟨position, rest, forged, rfl⟩ | ⟨consistent, clause, rest, unlisted, rfl⟩
    · unfold check
      split
      · next position' rest' forged' =>
          rw [forgedEq, forged] at forged'
          cases forged'
          rfl
      · next none => rw [forgedEq, forged] at none; cases none
    · unfold check
      split
      · next position' rest' forged' => rw [forgedEq, consistent] at forged'; cases forged'
      · split
        · next clause' rest' unlisted' =>
            rw [unlistedEq, unlisted] at unlisted'
            cases unlisted'
            rfl
        · next none => rw [unlistedEq, unlisted] at none; cases none

omit [DecidableEq Literal] [FreshNames Variable] in
/-- Lowering takes only the signature's naming, so a change of registry,
domains, or revision that keeps the naming leaves every lowered formula as it
was. This holds by the lowering functions' types; the theorem only records it.
The plan records the whole input and must be checked again. -/
theorem lowering_naming_only {first second : SignatureSnapshot Domain Symbol} (same : first.naming = second.naming)
    (goalRanges contextRanges : Elaboration.Ranges Domain) (context : ProofContext Variable Literal Symbol)
    (goal : Formula Variable Literal Symbol) (index : Nat) (sources : List (SourceClause Domain Variable Literal Symbol)) :
    lowerQuery hoApplySymbol first.naming goalRanges contextRanges context goal =
        lowerQuery hoApplySymbol second.naming goalRanges contextRanges context goal ∧
      lowerClauses hoApplySymbol first.naming index sources = lowerClauses hoApplySymbol second.naming index sources := by
  rw [same]; exact ⟨rfl, rfl⟩

omit [FreshNames Variable] in
/-- A plan is admitted for exactly one input: a changed program, signature,
context, or goal needs a new check. -/
theorem P0Admitted.unique {input other : Input Domain Variable Literal Symbol}
    {plan : Plan Domain Variable Literal Symbol hoApplySymbol} (admitted : P0Admitted hoApplySymbol input plan)
    (also : P0Admitted hoApplySymbol other plan) : input = other :=
  admitted.exact.symm.trans also.exact

/-! ## Running a plan -/

/-- Run a plan on the shared machine, from its query, with the run's snapshot
its input. -/
def Plan.run (plan : Plan Domain Variable Literal Symbol hoApplySymbol) (fuel : Nat) :
    Outcome Variable Literal Symbol (P0.Certificate Variable Literal Symbol) (Input Domain Variable Literal Symbol) :=
  Machine.run plan.ground.strategy fuel (plan.ground.init plan.input)

/-- `Plan.answer`: the answer to the plan's query, `true` when its run
succeeds and `false` when it is exhausted. The run needs no fuel: it ends by
the decreasing measure, which is never computed (`P0.runToEnd`). -/
def Plan.answer (plan : Plan Domain Variable Literal Symbol hoApplySymbol) : Bool :=
  match P0.runToEnd plan.ground (plan.ground.init plan.input) (plan.ground.init_inv plan.input) with
  | .success _ _ => true
  | .exhausted => false
  -- A run to the finish is never unknown or interrupted (`P0.runToEnd_finished`).
  | .unknown _ | .interrupted _ => false

/-- The answer is `true` with a success certificate or `false` with a
complete-failure certificate. -/
theorem Plan.answer_spec (plan : Plan Domain Variable Literal Symbol hoApplySymbol) :
    (plan.answer = true ∧ Succeeds plan.ground.program plan.ground.context plan.input.goal) ∨
      (plan.answer = false ∧ Fails plan.ground.program plan.ground.context plan.input.goal) := by
  rw [← plan.admits.goal]
  unfold Plan.answer
  rcases P0.runToEnd_finished plan.ground (plan.ground.init plan.input) (plan.ground.init_inv plan.input) with
    ⟨⟨proof, resume, ran⟩, proved⟩ | ⟨ran, failed⟩
  · exact .inl ⟨by simp [ran], proved⟩
  · exact .inr ⟨by simp [ran], failed⟩

/-- `true` exactly when the query has a success certificate. -/
theorem Plan.answer_true (plan : Plan Domain Variable Literal Symbol hoApplySymbol) :
    plan.answer = true ↔ Succeeds plan.ground.program plan.ground.context plan.input.goal := by
  rcases plan.answer_spec with ⟨answered, proved⟩ | ⟨answered, failed⟩
  · exact ⟨fun _ => proved, fun _ => answered⟩
  · rw [answered]
    exact ⟨fun same => (by cases same), fun proved => absurd failed (succeeds_not_fails proved)⟩

/-- `false` exactly when the query has a complete-failure certificate. -/
theorem Plan.answer_false (plan : Plan Domain Variable Literal Symbol hoApplySymbol) :
    plan.answer = false ↔ Fails plan.ground.program plan.ground.context plan.input.goal := by
  rcases plan.answer_spec with ⟨answered, proved⟩ | ⟨answered, failed⟩
  · rw [answered]
    exact ⟨fun same => (by cases same), fun failed => absurd failed (succeeds_not_fails proved)⟩
  · exact ⟨fun _ => failed, fun _ => answered⟩

omit [FreshNames Variable] in
/-- A Ready check of an asked input keeps the asked goal: the plan answers
that query. -/
theorem check_ask {base : ProgramInput Domain Variable Literal Symbol} {context : ProofContext Variable Literal Symbol}
    {goal : Formula Variable Literal Symbol} {plan : Plan Domain Variable Literal Symbol hoApplySymbol}
    (ready : check hoApplySymbol (base.ask context goal) = .ready plan) : plan.input.goal = goal := by
  rw [(check_ready_sound ready).exact]; rfl

/-- `checkProgram_decides`: on a program the check accepts, every P0 query is
decided: `Plan.answer` answers `true` exactly when it succeeds and `false`
exactly when it fails completely. Each query is decided against its own
plan's program, the KB clauses with the guard facts that query asks for;
relating its failure to the effective program is S16's. -/
theorem checkProgram_decides {base : ProgramInput Domain Variable Literal Symbol}
    (accepted : checkProgram hoApplySymbol base = .decides)
    {context : ProofContext Variable Literal Symbol} {goal : Formula Variable Literal Symbol}
    (goalOk : IsGoal hoApplySymbol goal ∧ Ordinary hoApplySymbol goal)
    (contextOk : ∀ atom ∈ context, IsAtom hoApplySymbol atom ∧ Ordinary hoApplySymbol atom) :
    ∃ plan, check hoApplySymbol (base.ask context goal) = .ready plan ∧
      (plan.answer = true ↔ Succeeds plan.ground.program plan.ground.context goal) ∧
      (plan.answer = false ↔ Fails plan.ground.program plan.ground.context goal) := by
  obtain ⟨plan, ready⟩ := checkProgram_ready accepted goalOk contextOk
  have asked := check_ask ready
  exact ⟨plan, ready, asked ▸ plan.answer_true, asked ▸ plan.answer_false⟩

/-- `Admission.ready_no_missing_capability`: every state a plan's run reaches
records no gap, keeps the empty store, and gets a next step from the command
set: candidates or ground NAF, never `unsupported`, `incomplete`, or `delay`.
Every plan is a Ready one: it carries its admission. -/
theorem ready_no_missing_capability (plan : Plan Domain Variable Literal Symbol hoApplySymbol)
    {state : State Variable Literal Symbol (P0.Certificate Variable Literal Symbol) (Input Domain Variable Literal Symbol)}
    (reached : Reaches plan.ground.strategy (plan.ground.init plan.input) state) :
    state.gaps = [] ∧ state.store = Store.empty ∧ ∀ obligation, state.focus = .solve obligation →
      (∃ alternatives, plan.ground.strategy obligation state.store = .candidates alternatives) ∨
        ∃ certificate, plan.ground.strategy obligation state.store = .negate certificate := by
  have inv : P0.Inv plan.ground state := by
    have general : ∀ {first last : State Variable Literal Symbol (P0.Certificate Variable Literal Symbol)
        (Input Domain Variable Literal Symbol)}, Reaches plan.ground.strategy first last →
        P0.Inv plan.ground first → P0.Inv plan.ground last := by
      intro first last reaches
      induction reaches with
      | refl => exact id
      | step stepped _ ih => exact fun inv => ih (P0.step_inv inv stepped).1
    exact general reached (plan.ground.init_inv plan.input)
  obtain ⟨_, store, _, gaps, focusOk, _, _⟩ := inv.shape
  refine ⟨gaps, store, fun obligation focused => ?_⟩
  rw [focused] at focusOk
  obtain ⟨scope, goalOk⟩ := focusOk
  obtain ⟨scope', goal⟩ := obligation
  simp only at scope goalOk
  subst scope
  rw [store, plan.ground.strategy_eq goalOk.valid goalOk.ordinary]
  cases goal <;> simp [P0.Ground.response]

omit [FreshNames Variable] in
/-- The decided guard facts of a Ready plan are exactly the asked guard atoms
of the generated set, and each is derivable from the input's own program under
the input's context: the program carries the generated signature clauses. -/
theorem Plan.guards_derive {plan : Plan Domain Variable Literal Symbol hoApplySymbol}
    (ready : check hoApplySymbol input = .ready plan) {naf : NafFailure Variable Literal Symbol} :
    ∀ atom ∈ plan.guards, Derives hoApplySymbol input.program.kb input.context atom naf := by
  intro atom member
  have admits := (check_ready_sound ready).admits
  rw [admits.facts] at member
  have derived := decideGuard_derives (hoApplySymbol := hoApplySymbol) (naf := NafFailure.disabled)
    input.listed input.complete input.distinct (mem_guardFacts member).2
  exact derived.mono (fun clause inside => signatureKb_carried admits.generated inside)
    (fun _ _ none => none.elim)

omit [FreshNames Variable] in
/-- A guard atom the query or a KB body asks for is a plan fact exactly when
it is in the generated set: no generated atom is missed, so a guard's failure
in the run is its absence from the least set the generated clauses and the
context's assumptions derive. -/
theorem Plan.guards_exact {plan : Plan Domain Variable Literal Symbol hoApplySymbol}
    (ready : check hoApplySymbol input = .ready plan) {symbol : Symbol} {arg : Term Variable Literal Symbol}
    (asked : Term.app symbol [arg] ∈ input.goalAtoms) (guard : input.guard symbol = true) :
    Term.app symbol [arg] ∈ plan.guards ↔ Generated input.signature input.context symbol arg := by
  rw [(check_ready_sound ready).admits.facts, ← guardHolds_iff input.listed input.complete]
  constructor
  · intro member; exact (mem_guardFacts member).2
  · intro holds
    exact List.mem_eraseDups.mpr (List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨asked, guard⟩, holds⟩)

end Check

end AnthillModKbSpec.Admission

namespace AnthillModKbSpec.Machine

open Admission GroundSearch

variable {Domain Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal]
  [DecidableEq Symbol] [FreshNames Variable] {hoApplySymbol : Symbol} {input : Input Domain Variable Literal Symbol}
  {plan : Plan Domain Variable Literal Symbol hoApplySymbol}

/-- `Machine.run_total_of_p0`: the run of a Ready plan finishes within a bound,
with a success or an exhaustion; it is never `unknown`. Running it with less
fuel may interrupt it, which is no result about the goal. -/
theorem run_total_of_p0 (plan : Plan Domain Variable Literal Symbol hoApplySymbol) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      (∃ proof resume, plan.run fuel = .success proof resume) ∨ plan.run fuel = .exhausted :=
  P0.run_total plan.ground plan.input

/-- `Machine.run_correct_of_p0`: the run of a Ready plan answers the original
query. Success proves the goal with a success certificate for the plan's
program and the input's context; the tree's NAF nodes hold valid certificates
for exactly that program and context; the goal is derivable with the ground
failure provider of that program and context; and every node is a rule
application of the run (`P0.Built`), which S08's export checks. Exhaustion
gives a complete-failure certificate. No run is `unknown`. -/
theorem run_correct_of_p0 (ready : check hoApplySymbol input = .ready plan) (fuel : Nat) :
    (∀ proof resume, plan.run fuel = .success proof resume →
      proof.snapshot = input ∧ Succeeds plan.ground.program plan.ground.context input.goal ∧
      (∀ evidence ∈ proof.tree.closedWorld, evidence.certificate.Valid plan.ground.program plan.ground.context) ∧
      Derives hoApplySymbol plan.ground.program.toKb input.context input.goal
        (failureEvidence plan.ground.program plan.ground.context) ∧
      P0.Built plan.ground proof.tree) ∧
    (plan.run fuel = .exhausted → Fails plan.ground.program plan.ground.context input.goal) ∧
    ∀ gaps, plan.run fuel ≠ .unknown gaps := by
  have admitted := check_ready_sound ready
  obtain ⟨success, exhausted, unknown⟩ := P0.run_correct plan.ground plan.input fuel
  rw [admitted.admits.goal] at success exhausted
  refine ⟨fun proof resume ran => ?_, exhausted, unknown⟩
  obtain ⟨_, _, proved, valid, derives, built, _⟩ := success proof resume ran
  refine ⟨?_, proved, valid, admitted.admits.context ▸ derives, built⟩
  have snapshotEq : proof.snapshot = plan.input := by
    rw [run_snapshot _ fuel ran, plan.ground.init_eq]
  rw [snapshotEq, admitted.exact]

end AnthillModKbSpec.Machine
