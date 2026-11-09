import AnthillModKbSpec.Resolution.Tabled.Fixpoint

/-! # Abstract fixpoints over the data terms (S24)

The tabled run proves Yes. No and Unknown are decided against the completion
over a finite **universe** of ground data terms: the subterms of the program's
and the query's ground terms (`universeOf`). An **abstract value** is a term of
the universe or `none`, written ⋆, standing for every other value of a model.
Every value of a model of the completion has exactly one abstraction
(`Tabled/AbstractSound`), since its constructors are free.

- **Definitely and possibly true** (`kk`): the Kripke–Kleene iteration of the
  completion (Fitting 1985), over abstract atoms. `definitely` holds ground atoms
  of the universe that are true in every model; `possibly` holds abstract atoms
  that over-approximate every model's true atoms. NAF reads the other set:
  `naf A` is possibly true unless `A` is definitely true, and definitely true
  when `A` is not possibly true. For a positive program `possibly` is the greatest
  fixpoint, abstracted; with NAF it is the completion's. A goal that is not
  possibly true under any abstract value of its names is **refuted**
  (`refutes`): false in every model of the completion. That is No, and the
  evidence of a NAF.
- **The abstract least fixpoint** (`leastOver`): the possibly-true atoms of a
  positive program from nothing; closed (`closedLeast`), it over-approximates
  the least fixpoint, the witness in which a goal fails.
- **A concrete greatest post-fixpoint** (`greatestOver`): atoms over the universe
  and one fresh value ⋆, a distinct key, each supported by a clause instance
  inside the set (`postGreatest`); it is below the greatest fixpoint, the
  witness in which a goal holds.
- **Ground fixpoints** (`groundFixpoint`): for ground programs, NAF included, an
  assignment of the ground atoms that is a fixpoint of the consequence operator.

All computations are finite: the abstract atoms of a predicate of arity `n`
are `(|universe| + 1)ⁿ`. -/

namespace AnthillModKbSpec.Tabled

open Semantics Completion

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

attribute [local instance] Machine.termEq

/-- An abstract value: a data term of the universe, or `none` (⋆), standing for
every value no term of the universe denotes. -/
abbrev AValue (Variable Literal Symbol : Type) := Option (Term Variable Literal Symbol)

/-- An environment of abstract values. -/
abbrev AEnv (Variable Literal Symbol : Type) := Variable → AValue Variable Literal Symbol

/-- An abstract atom. -/
abbrev AAtom (Variable Literal Symbol : Type) := Symbol × List (AValue Variable Literal Symbol)

/-- A ground atom over the universe. -/
abbrev GAtom (Variable Literal Symbol : Type) := Symbol × List (Term Variable Literal Symbol)

/-! ## Data terms over declared constructors -/

section Data

variable (constructors : List (Constructor Literal Symbol))

mutual
/-- A data term whose constructors are declared. -/
def dataIn : Term Variable Literal Symbol → Bool
  | .var _ => true
  | .lit value => decide (Constructor.literal value ∈ constructors)
  | .app symbol args => decide (Constructor.application symbol args.length ∈ constructors) && dataInAll args
  | _ => false

def dataInAll : List (Term Variable Literal Symbol) → Bool
  | [] => true
  | arg :: rest => dataIn arg && dataInAll rest
end

mutual
/-- A ground data term whose constructors are declared. -/
def groundIn : Term Variable Literal Symbol → Bool
  | .lit value => decide (Constructor.literal value ∈ constructors)
  | .app symbol args => decide (Constructor.application symbol args.length ∈ constructors) && groundInAll args
  | _ => false

def groundInAll : List (Term Variable Literal Symbol) → Bool
  | [] => true
  | arg :: rest => groundIn arg && groundInAll rest
end

omit [DecidableEq Variable] in
theorem dataInAll_iff : ∀ {args : List (Term Variable Literal Symbol)},
    dataInAll constructors args = true ↔ ∀ arg ∈ args, dataIn constructors arg = true
  | [] => by simp [dataInAll]
  | arg :: rest => by simp [dataInAll, dataInAll_iff (args := rest)]

omit [DecidableEq Variable] in
theorem groundInAll_iff : ∀ {args : List (Term Variable Literal Symbol)},
    groundInAll constructors args = true ↔ ∀ arg ∈ args, groundIn constructors arg = true
  | [] => by simp [groundInAll]
  | arg :: rest => by simp [groundInAll, groundInAll_iff (args := rest)]

/-- A universe: ground data terms over the declared constructors, closed under
subterms. -/
def validUniverse (space : List (Term Variable Literal Symbol)) : Bool :=
  space.all fun term => groundIn constructors term &&
    match term with
    | .app _ args => args.all (· ∈ space)
    | _ => true

end Data

mutual
/-- The ground data subterms of a term, through formulas and arguments. -/
def groundSubterms : Term Variable Literal Symbol → List (Term Variable Literal Symbol)
  | .lit value => [.lit value]
  | .app symbol args =>
      let inner := groundSubtermsAll args
      if args.all (· ∈ inner) then .app symbol args :: inner else inner
  | .conj left right | .disj left right | .imp left right | .equal left right =>
      groundSubterms left ++ groundSubterms right
  | .defaultNeg body | .forallVar _ body | .existsVar _ body => groundSubterms body
  | .dictionaryCall dictionary _ _ args => groundSubterms dictionary ++ groundSubtermsAll args
  | .var _ | .truth | .falsity => []

def groundSubtermsAll : List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol)
  | [] => []
  | arg :: rest => groundSubterms arg ++ groundSubtermsAll rest
end

/-- The terms of a clause. -/
def HornClause.terms : HornClause Variable Literal Symbol → List (Term Variable Literal Symbol)
  | .definite head body => head :: body
  | .goal body => body

/-- The universe of a program and some formulas: their ground data subterms
over the declared constructors. -/
def universeOf (constructors : List (Constructor Literal Symbol)) (clauses : List (HornClause Variable Literal Symbol))
    (formulas : List (Term Variable Literal Symbol)) : List (Term Variable Literal Symbol) :=
  ((clauses.flatMap HornClause.terms ++ formulas).flatMap groundSubterms).eraseDups.filter (groundIn constructors)

/-- The values of a list of options, when all are present. -/
def allSome {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | some value :: rest => (allSome rest).map (value :: ·)
  | none :: _ => none

/-! ## Abstract evaluation -/

section Evaluation

variable (space : List (Term Variable Literal Symbol))

/-- The abstract values: ⋆ and the universe's terms. -/
def values : List (AValue Variable Literal Symbol) := none :: space.map some

mutual
/-- The abstraction of a data term's value: its term when that is in the
universe, and ⋆ otherwise. -/
def aeval (env : AEnv Variable Literal Symbol) : Term Variable Literal Symbol → AValue Variable Literal Symbol
  | .var name => env name
  | .lit value => if Term.lit value ∈ space then some (.lit value) else none
  | .app symbol args =>
      match aevals env args with
      | some found => if Term.app symbol found ∈ space then some (.app symbol found) else none
      | none => none
  | _ => none

/-- The arguments' terms, when each is in the universe. -/
def aevals (env : AEnv Variable Literal Symbol) : List (Term Variable Literal Symbol) → Option (List (Term Variable Literal Symbol))
  | [] => some []
  | arg :: rest =>
      match aeval env arg, aevals env rest with
      | some value, some found => some (value :: found)
      | _, _ => none
end

/-- Every environment over `names` taking `choices`, other names ⋆. -/
def envsOver (choices : List (AValue Variable Literal Symbol)) : List Variable → List (AEnv Variable Literal Symbol)
  | [] => [fun _ => none]
  | name :: names => (envsOver choices names).flatMap fun env => choices.map (update env name)

/-- Every tuple of `n` choices. -/
def tuples {α : Type} (choices : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => (tuples choices n).flatMap fun rest => choices.map (· :: rest)

end Evaluation

/-! ## Definitely and possibly true -/

section Kleene

variable (signature : Signature Literal Symbol) (space : List (Term Variable Literal Symbol))

mutual
/-- Possibly true: in some model, under an environment the abstract one abstracts. -/
def possible (definitely : List (GAtom Variable Literal Symbol)) (possibly : List (AAtom Variable Literal Symbol))
    (env : AEnv Variable Literal Symbol) : Term Variable Literal Symbol → Bool
  | .truth => true
  | .falsity => false
  | .conj left right => possible definitely possibly env left && possible definitely possibly env right
  | .disj left right => possible definitely possibly env left || possible definitely possibly env right
  | .imp left right => !definite definitely possibly env left || possible definitely possibly env right
  | .defaultNeg body => !definite definitely possibly env body
  | .existsVar name body => (values space).any fun value => possible definitely possibly (update env name value) body
  | .forallVar name body => space.all fun value => possible definitely possibly (update env name (some value)) body
  | .equal left right =>
      if dataIn signature.constructors left && dataIn signature.constructors right then
        match aeval space env left, aeval space env right with
        | some first, some second => decide (first = second)
        | none, none => true
        | _, _ => false
      else true
  | .app symbol args =>
      if decide ((symbol, args.length) ∈ signature.predicates) && dataInAll signature.constructors args then
        decide ((symbol, args.map (aeval space env)) ∈ possibly)
      else true
  | _ => true

/-- Definitely true: in every model, under every environment the abstract one
abstracts, its names valued in the universe. -/
def definite (definitely : List (GAtom Variable Literal Symbol)) (possibly : List (AAtom Variable Literal Symbol))
    (env : AEnv Variable Literal Symbol) : Term Variable Literal Symbol → Bool
  | .truth => true
  | .falsity => false
  | .conj left right => definite definitely possibly env left && definite definitely possibly env right
  | .disj left right => definite definitely possibly env left || definite definitely possibly env right
  | .imp left right => !possible definitely possibly env left || definite definitely possibly env right
  | .defaultNeg body => !possible definitely possibly env body
  | .existsVar name body => space.any fun value => definite definitely possibly (update env name (some value)) body
  | .forallVar _ _ => false
  | .equal left right =>
      if dataIn signature.constructors left && dataIn signature.constructors right then
        match aeval space env left, aeval space env right with
        | some first, some second => decide (first = second)
        | _, _ => false
      else false
  | .app symbol args =>
      if decide ((symbol, args.length) ∈ signature.predicates) && dataInAll signature.constructors args then
        match aevals space env args with
        | some found => decide ((symbol, found) ∈ definitely)
        | none => false
      else false
  | _ => false
end

/-- Every abstract atom of the closed predicates. -/
def allAtoms : List (AAtom Variable Literal Symbol) :=
  signature.predicates.flatMap fun key => (tuples (values space) key.2).map (key.1, ·)

variable (clauses : List (HornClause Variable Literal Symbol))

/-- The possibly-true atoms one round of the completion leaves: the head of a
clause instance whose body is possibly true. A head that is not data over the
declared constructors keeps every atom of its predicate. -/
def stepPossible (definitely : List (GAtom Variable Literal Symbol)) (possibly : List (AAtom Variable Literal Symbol)) :
    List (AAtom Variable Literal Symbol) :=
  signature.predicates.flatMap fun key =>
    (definitions clauses key.1 key.2).flatMap fun pair =>
      if dataInAll signature.constructors pair.1 then
        (envsOver (values space) (caseNames pair.1 pair.2)).filterMap fun env =>
          if possible signature space definitely possibly env (.conjunction pair.2) then
            some (key.1, pair.1.map (aeval space env))
          else none
      else (tuples (values space) key.2).map (key.1, ·)

/-- The definitely-true atoms one round derives: the head of a clause instance
over the universe whose body is definitely true. -/
def stepDefinite (definitely : List (GAtom Variable Literal Symbol)) (possibly : List (AAtom Variable Literal Symbol)) :
    List (GAtom Variable Literal Symbol) :=
  signature.predicates.flatMap fun key =>
    (definitions clauses key.1 key.2).flatMap fun pair =>
      (envsOver (space.map some) (caseNames pair.1 pair.2)).filterMap fun env =>
        if definite signature space definitely possibly env (.conjunction pair.2) then
          (aevals space env pair.1).map (key.1, ·)
        else none

/-- The Kripke–Kleene iteration: definitely true atoms grow from none, possibly
true atoms shrink from all. Every round is sound. -/
def kk : Nat → List (GAtom Variable Literal Symbol) × List (AAtom Variable Literal Symbol)
  | 0 => ([], allAtoms signature space)
  | n + 1 =>
      let previous := kk n
      ((stepDefinite signature space clauses previous.1 previous.2).eraseDups,
        (stepPossible signature space clauses previous.1 previous.2).eraseDups)

/-- Enough rounds: one per abstract atom that may change. -/
def rounds : Nat := (allAtoms signature space).length + 1

/-- The goal is not possibly true under any abstract value of its free names,
the iteration's result given. -/
def refutesWith (fixed : List (GAtom Variable Literal Symbol) × List (AAtom Variable Literal Symbol))
    (goal : Term Variable Literal Symbol) : Bool :=
  (envsOver (values space) goal.freeVars.eraseDups).all fun env => !possible signature space fixed.1 fixed.2 env goal

/-- The goal is false in every model of the completion: not possibly true
under any abstract value of its free names. The iteration runs once. -/
def refutes (count : Nat) (goal : Term Variable Literal Symbol) : Bool :=
  refutesWith signature space (kk signature space clauses count) goal

/-! ## The witnesses of positive programs -/

/-- The abstract least fixpoint: possibly-true atoms from none, with nothing
definitely true (positive programs read no NAF). -/
def leastOver : Nat → List (AAtom Variable Literal Symbol)
  | 0 => []
  | n + 1 => (stepPossible signature space clauses [] (leastOver n)).eraseDups

/-- The abstract least fixpoint is closed under one more round. -/
def closedLeast (found : List (AAtom Variable Literal Symbol)) : Bool :=
  (stepPossible signature space clauses [] found).all (· ∈ found)

/-- The goal fails in the least fixpoint: not possibly true over `found`. -/
def failsLeast (found : List (AAtom Variable Literal Symbol)) (goal : Term Variable Literal Symbol) : Bool :=
  (envsOver (values space) goal.freeVars.eraseDups).all fun env => !possible signature space [] found env goal

mutual
/-- The value of a data term over the universe and one fresh value ⋆, a key no
term denotes; `none` when it is outside them, as `f(⋆)` is. -/
def veval (env : AEnv Variable Literal Symbol) : Term Variable Literal Symbol → Option (AValue Variable Literal Symbol)
  | .var name => some (env name)
  | .lit value => if Term.lit value ∈ space then some (some (.lit value)) else none
  | .app symbol args =>
      match vevals env args with
      | some found =>
          match allSome found with
          | some terms => if Term.app symbol terms ∈ space then some (some (.app symbol terms)) else none
          | none => none
      | none => none
  | _ => none

def vevals (env : AEnv Variable Literal Symbol) : List (Term Variable Literal Symbol) → Option (List (AValue Variable Literal Symbol))
  | [] => some []
  | arg :: rest =>
      match veval env arg, vevals env rest with
      | some value, some found => some (value :: found)
      | _, _ => none
end

/-- A positive goal true over the atoms `found`, with the unknown markers true:
the fresh value is one value, compared exactly. -/
def vtrue (marked : Symbol → Bool) (found : List (AAtom Variable Literal Symbol)) (env : AEnv Variable Literal Symbol) :
    Term Variable Literal Symbol → Bool
  | .truth => true
  | .conj left right => vtrue marked found env left && vtrue marked found env right
  | .disj left right => vtrue marked found env left || vtrue marked found env right
  | .existsVar name body => (values space).any fun value => vtrue marked found (update env name value) body
  | .equal left right =>
      if dataIn signature.constructors left && dataIn signature.constructors right then
        match veval space env left, veval space env right with
        | some first, some second => decide (first = second)
        | _, _ => false
      else false
  | .app symbol args =>
      if dataInAll signature.constructors args then
        if decide ((symbol, args.length) ∈ signature.predicates) then
          match vevals space env args with
          | some found' => decide ((symbol, found') ∈ found)
          | none => false
        else marked symbol
      else false
  | _ => false

/-- An atom has a clause instance inside `found`. -/
def supported (marked : Symbol → Bool) (found : List (AAtom Variable Literal Symbol)) (atom : AAtom Variable Literal Symbol) : Bool :=
  (definitions clauses atom.1 atom.2.length).any fun pair =>
    dataInAll signature.constructors pair.1 &&
      (envsOver (values space) (caseNames pair.1 pair.2)).any fun env =>
        decide (vevals space env pair.1 = some atom.2) && vtrue signature space marked found env (.conjunction pair.2)

/-- Deflation from every atom: the atoms with a supporting instance inside. -/
def greatestOver (marked : Symbol → Bool) : Nat → List (AAtom Variable Literal Symbol)
  | 0 => allAtoms signature space
  | n + 1 =>
      let previous := greatestOver marked n
      previous.filter (supported signature space clauses marked previous)

/-- A post-fixpoint: every atom is supported inside the set. -/
def postGreatest (marked : Symbol → Bool) (found : List (AAtom Variable Literal Symbol)) : Bool :=
  found.all (supported signature space clauses marked found)

/-! ## Ground programs -/

/-- A ground goal true under an assignment of ground atoms: NAF is its complement. -/
def gtrue (assignment : List (GAtom Variable Literal Symbol)) : Term Variable Literal Symbol → Bool
  | .truth => true
  | .falsity => false
  | .conj left right => gtrue assignment left && gtrue assignment right
  | .disj left right => gtrue assignment left || gtrue assignment right
  | .imp left right => !gtrue assignment left || gtrue assignment right
  | .defaultNeg body => !gtrue assignment body
  | .equal left right => groundIn signature.constructors left && groundIn signature.constructors right && decide (left = right)
  | .app symbol args => groundInAll signature.constructors args && decide ((symbol, args) ∈ assignment)
  | _ => false

/-- A ground goal: no name, no quantifier, ground data arguments. -/
def groundGoal : Term Variable Literal Symbol → Bool
  | .truth | .falsity => true
  | .conj left right | .disj left right | .imp left right => groundGoal left && groundGoal right
  | .defaultNeg body => groundGoal body
  | .equal left right => groundIn signature.constructors left && groundIn signature.constructors right
  | .app _ args => groundInAll signature.constructors args
  | _ => false

/-- A ground atom's clause instances: its defining clauses with exactly its
arguments. -/
def groundSupported (assignment : List (GAtom Variable Literal Symbol)) (atom : GAtom Variable Literal Symbol) : Bool :=
  (definitions clauses atom.1 atom.2.length).any fun pair =>
    decide (pair.1 = atom.2) && gtrue signature assignment (.conjunction pair.2)

/-- The ground atoms the clauses conclude. -/
def groundHeads : List (GAtom Variable Literal Symbol) :=
  clauses.filterMap fun
    | .definite (.app symbol args) _ => some (symbol, args)
    | _ => none

/-- An assignment of ground atoms that is a fixpoint: an atom of a closed
predicate is assigned exactly when a clause with its head has a true body. -/
def groundFixpoint (assignment : List (GAtom Variable Literal Symbol)) : Bool :=
  (assignment ++ groundHeads clauses).all fun atom =>
    !decide ((atom.1, atom.2.length) ∈ signature.predicates) ||
      (decide (atom ∈ assignment) == groundSupported signature clauses assignment atom)

end Kleene

end AnthillModKbSpec.Tabled
