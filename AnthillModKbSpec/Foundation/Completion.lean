import AnthillModKbSpec.Foundation.Freshening
import AnthillModKbSpec.Foundation.Negation

/-! # Clark completion and refutation evidence for NAF (S10)

A program's clauses state when each predicate holds; its Clark completion adds
that it holds only then. For a predicate `p` of arity `n` with defining clauses
`p(t̄ᵢ) :- Bᵢ`, the only-if half is the clause

```text
(∃ȳ₁. x̄ = t̄₁ ∧ B₁) ∨ … ∨ (∃ȳₖ. x̄ = t̄ₖ ∧ Bₖ) ∨ false  :-  p(x̄)
```

where `ȳᵢ` are the names of the i-th clause and `x̄` are fresh. A predicate
without clauses gets `false :- p(x̄)`. The free equality theory adds that
distinct constructors denote distinct values (`false :- f(x̄) = g(ȳ)`) and that
constructors are injective (`xᵢ = yᵢ :- f(x̄) = f(ȳ)`). The completed program
is the program with these generated clauses (`completed`).

A refutation of `G` under a context is a positive derivation of `G → false` in
a KB (`refutation`). In a completed program it is NAF evidence: in every model
of the completed program, with complement NAF, `naf G` holds in every
environment satisfying the context (`refutation_adequate`). This holds for an
operand with free parameters as well: a derivation is generic in them, so the
evidence is uniform over their values, which `Model.FailureAdequate` requires.

That the intended model satisfies the completion and the equality theory is a
model hypothesis: the closed-world reading of the program, stated as concrete
clauses. A predicate is kept open by a clause `p(x̄) :- UNKNOWN` with a reserved
symbol that has no clauses and no completion: the case it adds to `p`'s
completion is never refuted. Only predicates whose clauses all have atomic
heads are closed (`Signature.of`): one an S09 compound head or a `ho_apply`
head may conclude stays open. The equality theory separates only declared
constructors and literals: a defined operation, such as one given by
equations, is not free. Consistency is part of the model hypothesis and is
not proved here: cycles through NAF in clause bodies, or a program equation
between declared constructors, can make the completion inconsistent, and then
no model satisfies it. -/

namespace AnthillModKbSpec

variable {Variable Literal Symbol : Type}

namespace Completion

/-- The head arguments and bodies of the clauses defining `symbol` at `arity`. -/
def definitions [DecidableEq Symbol] (clauses : List (HornClause Variable Literal Symbol)) (symbol : Symbol)
    (arity : Nat) : List (List (Term Variable Literal Symbol) × List (Term Variable Literal Symbol)) :=
  clauses.filterMap fun
    | .definite (.app head args) body => if head = symbol ∧ args.length = arity then some (args, body) else none
    | _ => none

/-- A data constructor: a literal, or a symbol with its arity. -/
inductive Constructor (Literal Symbol : Type) where
  | literal (value : Literal)
  | application (symbol : Symbol) (arity : Nat)
  deriving DecidableEq, Repr

def Constructor.arity : Constructor Literal Symbol → Nat
  | .literal _ => 0
  | .application _ arity => arity

/-- The constructor applied to the first names of `names`. -/
def Constructor.pattern (names : List Variable) : Constructor Literal Symbol → Term Variable Literal Symbol
  | .literal value => .lit value
  | .application symbol arity => .app symbol ((names.take arity).map .var)

/-- The predicates the completion closes and the constructors the equality
theory separates. -/
structure Signature (Literal Symbol : Type) where
  predicates : List (Symbol × Nat)
  constructors : List (Constructor Literal Symbol)

variable [DecidableEq Variable] [FreshNames Variable]

/-- A defining clause as a case of the definition at the head names: the
clause's own names existentially quantified over the head equations and its
body. -/
def case (heads : List Variable) (args body : List (Term Variable Literal Symbol)) : Term Variable Literal Symbol :=
  (Term.conjunction (args ++ body)).freeVars.eraseDups.foldr Term.existsVar
    (Term.conjunction ((heads.zip args).map (fun pair => Term.equal (.var pair.1) pair.2) ++ body))

/-- The only-if half of a predicate's definition: an atom of it holds only by
one of its clauses. -/
def onlyIf [DecidableEq Symbol] (clauses : List (HornClause Variable Literal Symbol)) (symbol : Symbol) (arity : Nat) :
    HornClause Variable Literal Symbol :=
  let defining := definitions clauses symbol arity
  let heads := freshNames (defining.flatMap fun pair => (Term.conjunction (pair.1 ++ pair.2)).freeVars) arity
  .definite ((defining.map fun pair => case heads pair.1 pair.2).foldr .disj .falsity) [.app symbol (heads.map .var)]

/-- Distinct constructors denote distinct values. -/
def clash (first second : Constructor Literal Symbol) : HornClause Variable Literal Symbol :=
  let names := freshNames [] (first.arity + second.arity)
  .goal [.equal (first.pattern names) (second.pattern (names.drop first.arity))]

/-- A constructor is injective in each argument. -/
def injective (symbol : Symbol) (arity : Nat) : List (HornClause Variable Literal Symbol) :=
  let names := freshNames [] (arity + arity)
  let left := names.take arity
  let right := names.drop arity
  (left.zip right).map fun pair =>
    .definite (.equal (.var pair.1) (.var pair.2)) [.equal (.app symbol (left.map .var)) (.app symbol (right.map .var))]

/-- The clash clauses of the free equality theory: one per ordered pair of
distinct constructors. -/
def clashes [DecidableEq Literal] [DecidableEq Symbol] (constructors : List (Constructor Literal Symbol)) :
    List (HornClause Variable Literal Symbol) :=
  constructors.flatMap fun first => constructors.filterMap fun second =>
    if first = second then none else some (clash first second)

/-- The injectivity clauses of the free equality theory. -/
def injections (constructors : List (Constructor Literal Symbol)) : List (HornClause Variable Literal Symbol) :=
  constructors.flatMap fun
    | .application symbol arity => injective symbol arity
    | .literal _ => []

/-- The free equality theory over a list of constructors. -/
def equality [DecidableEq Literal] [DecidableEq Symbol] (constructors : List (Constructor Literal Symbol)) :
    List (HornClause Variable Literal Symbol) :=
  clashes constructors ++ injections constructors

/-- The completed program: the program, the only-if half of each predicate of
the signature, and the free equality theory over its constructors. -/
def completed [DecidableEq Literal] [DecidableEq Symbol] (clauses : List (HornClause Variable Literal Symbol))
    (signature : Signature Literal Symbol) : List (HornClause Variable Literal Symbol) :=
  clauses ++ signature.predicates.map (fun key => onlyIf clauses key.1 key.2) ++ equality signature.constructors

theorem mem_completed [DecidableEq Literal] [DecidableEq Symbol] {clauses : List (HornClause Variable Literal Symbol)}
    {signature : Signature Literal Symbol} {clause : HornClause Variable Literal Symbol} (member : clause ∈ clauses) :
    clause ∈ completed clauses signature := by
  simp [completed, member]

end Completion

/-! ## The signature a program needs -/

namespace Completion

mutual
/-- The constructors of a data term. -/
def dataConstructors : Term Variable Literal Symbol → List (Constructor Literal Symbol)
  | .lit value => [.literal value]
  | .app symbol args => .application symbol args.length :: dataConstructorsOf args
  | _ => []

def dataConstructorsOf : List (Term Variable Literal Symbol) → List (Constructor Literal Symbol)
  | [] => []
  | term :: rest => dataConstructors term ++ dataConstructorsOf rest
end

/-- The atoms of a formula, through its connectives, with the constructors of
their arguments and of equations. -/
def formulaParts : Term Variable Literal Symbol → List (Symbol × Nat) × List (Constructor Literal Symbol)
  | .app symbol args => ([(symbol, args.length)], dataConstructorsOf args)
  | .equal left right => ([], dataConstructors left ++ dataConstructors right)
  | .conj a b | .disj a b | .imp a b =>
      let first := formulaParts a
      let second := formulaParts b
      (first.1 ++ second.1, first.2 ++ second.2)
  | .defaultNeg a | .forallVar _ a | .existsVar _ a => formulaParts a
  | _ => ([], [])

mutual
/-- Every symbol a term mentions: predicates, function and constant symbols,
and the symbols of dictionary calls. -/
def symbols : Term Variable Literal Symbol → List Symbol
  | .app symbol args => symbol :: symbolsOf args
  | .conj a b | .disj a b | .imp a b | .equal a b => symbols a ++ symbols b
  | .defaultNeg a | .forallVar _ a | .existsVar _ a => symbols a
  | .dictionaryCall dictionary path operation args => symbols dictionary ++ path ++ operation :: symbolsOf args
  | _ => []

def symbolsOf : List (Term Variable Literal Symbol) → List Symbol
  | [] => []
  | term :: rest => symbols term ++ symbolsOf rest
end

mutual
/-- Some `ho_apply` in the term applies a predicate that is not a constant. -/
def appliesVariable [DecidableEq Symbol] (hoApplySymbol : Symbol) : Term Variable Literal Symbol → Bool
  | .app symbol args =>
      (symbol == hoApplySymbol && match args with
        | .app _ [] :: _ => false
        | _ => true) || appliesVariableOf hoApplySymbol args
  | .conj a b | .disj a b | .imp a b | .equal a b => appliesVariable hoApplySymbol a || appliesVariable hoApplySymbol b
  | .defaultNeg a | .forallVar _ a | .existsVar _ a => appliesVariable hoApplySymbol a
  | .dictionaryCall dictionary _ _ args => appliesVariable hoApplySymbol dictionary || appliesVariableOf hoApplySymbol args
  | _ => false

def appliesVariableOf [DecidableEq Symbol] (hoApplySymbol : Symbol) : List (Term Variable Literal Symbol) → Bool
  | [] => false
  | term :: rest => appliesVariable hoApplySymbol term || appliesVariableOf hoApplySymbol rest
end

/-- A variable in formula position, outside atoms and equations: an instance
of the term may be any formula. -/
def formulaVariable : Term Variable Literal Symbol → Bool
  | .var _ => true
  | .conj a b | .disj a b | .imp a b => formulaVariable a || formulaVariable b
  | .defaultNeg a | .forallVar _ a | .existsVar _ a => formulaVariable a
  | _ => false

/-- The predicates a clause head may conclude other than as a defining clause
(`definitions`): none for an atom of an ordinary predicate or an equation; for
any other head, such as an S09 compound head or a `ho_apply` head, every symbol
it mentions. A head with a formula variable (`X`, `∀x. x`, `X ∧ q`) or one that
applies a predicate variable by `ho_apply` may conclude any predicate
(`none`). -/
def headOpens [DecidableEq Symbol] (hoApplySymbol : Symbol) (head : Term Variable Literal Symbol) : Option (List Symbol) :=
  match head with
  | .app symbol _ => if symbol == hoApplySymbol then opened else some []
  | .equal _ _ => some []
  | _ => opened
where
  opened := if appliesVariable hoApplySymbol head || formulaVariable head then none else some (symbols head)

/-- The predicates the completion closes and the constructors the equality
theory separates, for clauses and further formulas such as a query.

Constructors are declared, never inferred: an application symbol is a free
constructor when `free` says so, as the data signature's constructors are; a
defined operation, such as one with equations, is not. Literals are always
free. A predicate is closed unless it is a `marker` (an open marker such as
`UNKNOWN`), the `ho_apply` symbol, or a predicate some head may conclude other
than as a defining clause (`headOpens`); a head that applies a predicate
variable closes none. -/
def Signature.of [DecidableEq Literal] [DecidableEq Symbol] (marker : Symbol → Bool) (hoApplySymbol : Symbol)
    (free : Symbol → Bool) (clauses : List (HornClause Variable Literal Symbol))
    (formulas : List (Term Variable Literal Symbol)) : Signature Literal Symbol :=
  let parts := (clauses.flatMap fun
      | .definite head body => head :: body
      | .goal body => body) ++ formulas
  let found := parts.map formulaParts
  let constructors := (found.flatMap Prod.snd).eraseDups.filter fun
    | .literal _ => true
    | .application symbol _ => free symbol
  let heads := clauses.filterMap fun
    | .definite head _ => some head
    | .goal _ => none
  match heads.mapM (headOpens hoApplySymbol) with
  | none => ⟨[], constructors⟩
  | some opened =>
      ⟨(found.flatMap Prod.fst).eraseDups.filter (fun key =>
          !marker key.1 && key.1 != hoApplySymbol && !opened.flatten.contains key.1), constructors⟩

/-- The predicate a clause concludes, if its head is an atom. -/
def headSymbol? : HornClause Variable Literal Symbol → Option Symbol
  | .definite (.app symbol _) _ => some symbol
  | _ => none

/-- A marker occurs somewhere in the clauses or the formulas. -/
def markerUsed (marker : Symbol → Bool) (clauses : List (HornClause Variable Literal Symbol))
    (formulas : List (Term Variable Literal Symbol)) : Bool :=
  (clauses.flatMap (fun
      | .definite head body => symbols head ++ symbolsOf body
      | .goal body => symbolsOf body) ++ symbolsOf formulas).any marker

/-- A clause that may conclude a marker: its head mentions one, or, when a
marker is used at all, its head may conclude any predicate (`headOpens`). -/
def mayConcludeMarker [DecidableEq Symbol] (marker : Symbol → Bool) (hoApplySymbol : Symbol) (used : Bool) :
    HornClause Variable Literal Symbol → Bool
  | .definite head _ => (symbols head).any marker || (used && (headOpens hoApplySymbol head).isNone)
  | .goal _ => false

/-- The completed program of a KB with further formulas (`Signature.of`). A KB
clause that may conclude a marker is invalid: the open marker has no clauses of
its own, not through a compound or `ho_apply` head, and not through a head that
may conclude any predicate. The first such clause is reported. -/
def complete? [DecidableEq Literal] [DecidableEq Symbol] [DecidableEq Variable] [FreshNames Variable]
    (marker : Symbol → Bool) (hoApplySymbol : Symbol) (free : Symbol → Bool)
    (clauses : List (HornClause Variable Literal Symbol))
    (formulas : List (Term Variable Literal Symbol)) : Except Nat (List (HornClause Variable Literal Symbol)) :=
  match clauses.findIdx? (mayConcludeMarker marker hoApplySymbol (markerUsed marker clauses formulas)) with
  | some index => .error index
  | none => .ok (completed clauses (Signature.of marker hoApplySymbol free clauses formulas))

/-- The completion closes no marker and not `ho_apply`. -/
theorem Signature.of_open [DecidableEq Literal] [DecidableEq Symbol] {marker : Symbol → Bool} {hoApplySymbol : Symbol}
    {free : Symbol → Bool} {clauses : List (HornClause Variable Literal Symbol)}
    {formulas : List (Term Variable Literal Symbol)} {key : Symbol × Nat}
    (member : key ∈ (Signature.of marker hoApplySymbol free clauses formulas).predicates) :
    marker key.1 = false ∧ key.1 ≠ hoApplySymbol := by
  unfold Signature.of at member
  dsimp only at member
  split at member
  · cases member
  · simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq] at member
    exact ⟨member.2.1.1, member.2.1.2⟩

theorem headSymbol?_disjunction (cases : List (Term Variable Literal Symbol)) (body : List (Term Variable Literal Symbol)) :
    headSymbol? (.definite (cases.foldr .disj .falsity) body) = none := by
  cases cases <;> rfl

/-- No KB clause of an accepted completion may conclude a marker: its head
mentions none, and, when a marker is used, it may not conclude any predicate. -/
theorem complete?_heads [DecidableEq Literal] [DecidableEq Symbol] [DecidableEq Variable] [FreshNames Variable]
    {marker : Symbol → Bool} {hoApplySymbol : Symbol} {free : Symbol → Bool}
    {clauses result : List (HornClause Variable Literal Symbol)} {formulas : List (Term Variable Literal Symbol)}
    (completes : complete? marker hoApplySymbol free clauses formulas = .ok result) :
    ∀ clause ∈ clauses, mayConcludeMarker marker hoApplySymbol (markerUsed marker clauses formulas) clause = false := by
  unfold complete? at completes
  split at completes
  · cases completes
  · rename_i none
    intro clause member
    simpa using List.findIdx?_eq_none_iff.mp none clause member

/-- No clause of a completed program concludes a marker atom: the KB's clauses
may conclude none (`complete?_heads`), and the generated ones conclude cases,
equations, or falsity. So an open marker is never derived from a clause, and,
closing no marker, the completion never refutes it. -/
theorem complete?_reserved [DecidableEq Literal] [DecidableEq Symbol] [DecidableEq Variable] [FreshNames Variable]
    {marker : Symbol → Bool} {hoApplySymbol : Symbol} {free : Symbol → Bool}
    {clauses result : List (HornClause Variable Literal Symbol)} {formulas : List (Term Variable Literal Symbol)}
    (completes : complete? marker hoApplySymbol free clauses formulas = .ok result) :
    ∀ clause ∈ result, (headSymbol? clause).any marker = false := by
  have heads := complete?_heads completes
  unfold complete? at completes
  split at completes
  · cases completes
  · cases completes
    intro clause member
    simp only [completed, List.mem_append, List.mem_map] at member
    rcases member with (inKb | ⟨key, _, rfl⟩) | inEquality
    · have clean := heads clause inKb
      match clause, clean with
      | .definite (.app symbol args) _, clean =>
          simp only [mayConcludeMarker, symbols, List.any_cons, Bool.or_eq_false_iff] at clean
          simp [headSymbol?, clean.1.1]
      | .definite (.var _) _, _ | .definite (.lit _) _, _ | .definite .truth _, _ | .definite .falsity _, _
      | .definite (.conj _ _) _, _ | .definite (.disj _ _) _, _ | .definite (.imp _ _) _, _
      | .definite (.defaultNeg _) _, _ | .definite (.forallVar _ _) _, _ | .definite (.existsVar _ _) _, _
      | .definite (.dictionaryCall _ _ _ _) _, _ | .definite (.equal _ _) _, _ | .goal _, _ => rfl
    · simp [onlyIf, headSymbol?_disjunction]
    · simp only [equality, clashes, injections, List.mem_append, List.mem_flatMap, List.mem_filterMap] at inEquality
      rcases inEquality with ⟨_, _, _, _, produced⟩ | ⟨constructor, _, produced⟩
      · split at produced
        · cases produced
        · cases produced; rfl
      · cases constructor with
        | literal => cases produced
        | application symbol arity =>
            obtain ⟨_, _, rfl⟩ := List.mem_map.mp produced
            rfl

end Completion

/-! ## Refutations as NAF evidence -/

variable [DecidableEq Variable]

/-- Refutation evidence: a positive derivation of `goal → false` in `kb`, under
exactly the context of the NAF. -/
def refutation (hoApplySymbol : Symbol) (kb : LogicalKb Variable Literal Symbol) : NafFailure Variable Literal Symbol :=
  fun symbol actualKb context goal =>
    symbol = hoApplySymbol ∧ actualKb = kb ∧ Derives hoApplySymbol kb context (.imp goal .falsity)

open Semantics in
/-- Refutations are adequate NAF evidence in every model of the KB with
complement NAF. For a completed program this is the closed-world meaning of
NAF; an operand with free parameters is refuted for every value of them. -/
theorem refutation_adequate {Value : Type} {hoApplySymbol : Symbol} (model : Model Literal Symbol Value hoApplySymbol)
    {kb : LogicalKb Variable Literal Symbol} (validKb : model.Models kb) (negation : model.ComplementNAF) :
    model.FailureAdequate kb (refutation hoApplySymbol kb) := by
  intro context goal evidence environment valid
  obtain ⟨_, _, refuted⟩ := evidence
  have implication := model.positive_sound validKb refuted environment valid
  simp only [Model.Satisfies, Model.eval] at implication ⊢
  exact (negation _).mpr fun holds => model.holds_bottom ((model.holds_implication _ _).mp implication holds)

end AnthillModKbSpec
