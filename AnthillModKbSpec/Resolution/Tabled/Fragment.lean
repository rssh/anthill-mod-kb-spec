import AnthillModKbSpec.Resolution.Answer
import AnthillModKbSpec.Resolution.Tabled.Graph

/-! # The fast fragment: modes, data terms, call sites, and safety (S23)

The fast fragment ([fast evaluation](../../../docs/fast-decision-routes.md))
is classified before anything runs. This module holds the per-clause analyses
the classification combines (`Tabled/Admission`):

- **Modes.** Each predicate declares the mode of each argument position,
  input or output (`Modes`). The KB generator emits them with the clauses,
  as it emits explicit binder ranges; they are never inferred.
- **Data terms.** `flow` follows which names hold data terms: subterms of the
  clause head's inputs, ground terms of the program, and the outputs of a
  predicate whose outputs are data terms, called with data-term inputs.
  `sites` lists every predicate call of a goal with whether its inputs are
  data terms and whether they decrease (each a subterm of the head input at
  its position, one strictly).
- **Safety.** `scan` reads a body left to right: every input of a call is
  bound by the head's inputs or an earlier positive goal, a range guard waits
  until its name is bound (S06 delays it) and must be bound by the end of its
  scope, and a head output is bound by the end of the body. NAF ground in data
  runs as finite failure; NAF with a flexible name or an eigenvariable needs
  constructive negation (S21), and its operand is scanned with those names
  unbound. Constructs outside the fragment are blockers at their site and
  path. -/

namespace AnthillModKbSpec.Tabled

open Admission Answers

/-! ## Modes and the fragment's program -/

/-- The mode of an argument position. -/
inductive Mode where
  /-- Bound when the predicate is called. -/
  | input
  /-- Bound by the call's answers. -/
  | output
  deriving DecidableEq, Repr

/-- Mode declarations, as the KB generator emits them with the clauses: for a
predicate symbol, the mode of each argument position. Never inferred; a
predicate without a declaration, or used at another arity, is a blocker. -/
abbrev Modes (Symbol : Type) := Symbol → Option (List Mode)

/-- The arguments at the positions of one mode. -/
def select {α : Type} (mode : Mode) : List Mode → List α → List α
  | first :: modes, arg :: args => if first = mode then arg :: select mode modes args else select mode modes args
  | _, _ => []

variable {Variable Literal Symbol : Type}

/-- What the fragment's admission reads: the KB clauses with their indices
(the sites of blockers), the declared free constructors by symbol and arity,
the guard symbols (decided from the signature), the open markers, the
`ho_apply` symbol, and the mode declarations. -/
structure Program (Variable Literal Symbol : Type) where
  clauses : List (Nat × HornClause Variable Literal Symbol)
  free : Symbol → Nat → Bool
  guard : Symbol → Bool
  marker : Symbol → Bool
  hoApply : Symbol
  modes : Modes Symbol

/-- Why a predicate is in P2 rather than P1: a reason found at a site. -/
inductive Reason where
  /-- A recursive call whose inputs are not all data terms: its terms may grow. -/
  | growingCall
  /-- A head output that is not a data term, in a component whose recursive
  calls do not all decrease: its answers may grow. -/
  | growingAnswer
  /-- An implication goal whose antecedent the fragment does not decide: a
  rule, or one with names bound from the data. -/
  | hypothesis
  /-- A generic universal goal: a failure is Undecided. -/
  | universal
  /-- NAF whose operand reaches a predicate on a cycle. -/
  | cyclicNegation
  /-- A denial over a predicate on a cycle. -/
  | cyclicDenial
  /-- A rule the query's context assumes. -/
  | localRule
  deriving DecidableEq, Repr

/-- The reasons of the budgeted cost class: term growth, or a hypothesis or
local rule whose clauses may grow it. -/
def Reason.growth : Reason → Bool
  | .growingCall | .growingAnswer | .hypothesis | .localRule => true
  | _ => false

/-- One reason, at its site and path. -/
structure Note (Variable Literal Symbol : Type) where
  site : Site
  path : List Nat
  formula : Term Variable Literal Symbol
  reason : Reason

/-- A blocker at an admission site. -/
def blocker (site : Site) (path : List Nat) (formula : Term Variable Literal Symbol)
    (missing : Missing Variable Literal Symbol) : Blocker Variable Literal Symbol :=
  ⟨.site site, path, formula, missing⟩

/-- A construct outside the fragment, by the P0 capability it needs. -/
def outside (site : Site) (path : List Nat) (formula : Term Variable Literal Symbol) (capability : Capability) :
    Blocker Variable Literal Symbol :=
  blocker site path formula (.ofCapability capability)

/-! ## Terms -/

section Terms

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

attribute [local instance] Machine.termEq

mutual
/-- `part` is a subterm of a data term. -/
def occurs (part : Term Variable Literal Symbol) : Term Variable Literal Symbol → Bool
  | .app symbol args => decide (part = .app symbol args) || occursIn part args
  | term => decide (part = term)

def occursIn (part : Term Variable Literal Symbol) : List (Term Variable Literal Symbol) → Bool
  | [] => false
  | arg :: rest => occurs part arg || occursIn part rest
end

/-- `part` is a strict subterm: a subterm of an argument. -/
def inside (part : Term Variable Literal Symbol) : Term Variable Literal Symbol → Bool
  | .app _ args => occursIn part args
  | _ => false

mutual
/-- A ground data term: literals and applications. -/
def closedData : Term Variable Literal Symbol → Bool
  | .lit _ => true
  | .app _ args => closedDataIn args
  | _ => false

def closedDataIn : List (Term Variable Literal Symbol) → Bool
  | [] => true
  | arg :: rest => closedData arg && closedDataIn rest
end

end Terms

namespace Program

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] (program : Program Variable Literal Symbol)

/-! ## Calls -/

/-- The predicate call a goal reads as: a direct call, or a concrete indirect
call `ho_apply(p, args)`, normalized as S11's `ho_goal` does. Guards and
markers are not predicate calls. -/
def callOf? : Term Variable Literal Symbol → Option (Symbol × List (Term Variable Literal Symbol))
  | .app symbol args =>
      if symbol = program.hoApply then
        match args with
        | .app predicate [] :: rest =>
            if predicate = program.hoApply ∨ program.guard predicate = true ∨ program.marker predicate = true then none
            else some (predicate, rest)
        | _ => none
      else if program.guard symbol = true ∨ program.marker symbol = true then none
      else some (symbol, args)
  | _ => none

/-- The inputs and outputs of a call, by the predicate's declared modes at
the call's arity. -/
def io? (predicate : Symbol) (args : List (Term Variable Literal Symbol)) :
    Option (List (Term Variable Literal Symbol) × List (Term Variable Literal Symbol)) :=
  match program.modes predicate with
  | some modes => if modes.length = args.length then some (select .input modes args, select .output modes args) else none
  | none => none

mutual
/-- Every predicate a goal may call: through connectives, quantifiers, NAF
operands, and the bodies of the rules an implication's antecedent assumes. -/
def calls : Term Variable Literal Symbol → List Symbol
  | .conj left right | .disj left right => calls left ++ calls right
  | .imp antecedent conclusion => ruleCalls antecedent ++ calls conclusion
  | .defaultNeg operand | .forallVar _ operand | .existsVar _ operand => calls operand
  | goal =>
      match program.callOf? goal with
      | some (predicate, _) => [predicate]
      | none => []

/-- The calls of the rule bodies a Harrop antecedent assumes. -/
def ruleCalls : Term Variable Literal Symbol → List Symbol
  | .conj left right => ruleCalls left ++ ruleCalls right
  | .imp body head => calls body ++ ruleCalls head
  | .forallVar _ body => ruleCalls body
  | _ => []
end

/-! ## Data terms and call sites -/

end Program

/-- What the data-term analysis knows of a clause: its head's input patterns,
and the names an enclosing binder rebinds. -/
structure Frame (Variable Literal Symbol : Type) where
  heads : List (Term Variable Literal Symbol)
  shadow : List Variable

section FrameOps

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

/-- Under a binder for `name`. -/
def Frame.enter (frame : Frame Variable Literal Symbol) (name : Variable) : Frame Variable Literal Symbol :=
  ⟨frame.heads, name :: frame.shadow⟩

/-- A subterm of a head input whose names no binder has rebound. -/
def Frame.headTerm (frame : Frame Variable Literal Symbol) (term : Term Variable Literal Symbol) : Bool :=
  frame.heads.any (occurs term) && term.freeVars.all fun name => !frame.shadow.contains name

/-- A data term, given the names `small` known to hold data terms: a subterm
of a head input, a ground term of the program, or such a name. -/
def Frame.small (frame : Frame Variable Literal Symbol) (small : List Variable) (term : Term Variable Literal Symbol) :
    Bool :=
  frame.headTerm term || closedData term ||
    match term with
    | .var name => small.contains name
    | _ => false

/-- The inputs of a call decrease: each is a subterm of the head input at its
position, with no rebound name, and one is a strict subterm. The sum of the
inputs' sizes then decreases (`Tabled/Calls`). -/
def Frame.decreasing (frame : Frame Variable Literal Symbol) (inputs : List (Term Variable Literal Symbol)) : Bool :=
  decide (inputs.length ≤ frame.heads.length) &&
    (inputs.zip frame.heads).all (fun pair => occurs pair.1 pair.2 && pair.1.freeVars.all fun name => !frame.shadow.contains name) &&
    (inputs.zip frame.heads).any fun pair => inside pair.1 pair.2

end FrameOps

/-- One predicate call of a goal: its path, callee, and formula; whether its
inputs are data terms; whether they decrease. -/
structure CallSite (Variable Literal Symbol : Type) where
  path : List Nat
  callee : Symbol
  formula : Term Variable Literal Symbol
  small : Bool
  decreasing : Bool

namespace Program

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] (program : Program Variable Literal Symbol)

/-- The names holding data terms after a goal, from those before it. `info`
says which predicates have data-term outputs. A call with data-term inputs
to such a predicate makes its output names data terms; an equation with a
data-term side makes the other side's names data terms; a disjunction keeps
what both branches give; a binder's name is rebound inside its body. -/
def flow (info : Symbol → Bool) (frame : Frame Variable Literal Symbol) (small : List Variable) :
    Term Variable Literal Symbol → List Variable
  | .conj left right => flow info frame (flow info frame small left) right
  | .disj left right =>
      let leftSmall := flow info frame small left
      let rightSmall := flow info frame small right
      leftSmall.filter rightSmall.contains
  | .equal left right =>
      small ++ (if frame.small small left then right.freeVars else []) ++
        (if frame.small small right then left.freeVars else [])
  | .existsVar name body | .forallVar name body =>
      (flow info (frame.enter name) (small.filter (· != name)) body).filter (· != name) ++
        (if small.contains name then [name] else [])
  | .imp _ conclusion => flow info frame small conclusion
  | goal =>
      match program.callOf? goal with
      | some (predicate, args) =>
          match program.io? predicate args with
          | some (inputs, outputs) =>
              if info predicate && inputs.all (frame.small small) then small ++ outputs.flatMap Term.freeVars
              else small
          | none => small
      | none => small

/-- The predicate calls of a goal, with what `flow` knows at each. -/
def sites (info : Symbol → Bool) (frame : Frame Variable Literal Symbol) (small : List Variable) (path : List Nat) :
    Term Variable Literal Symbol → List (CallSite Variable Literal Symbol)
  | .conj left right =>
      sites info frame small (path ++ [0]) left ++ sites info frame (program.flow info frame small left) (path ++ [1]) right
  | .disj left right => sites info frame small (path ++ [0]) left ++ sites info frame small (path ++ [1]) right
  | .defaultNeg operand => sites info frame small (path ++ [0]) operand
  | .existsVar name body | .forallVar name body =>
      sites info (frame.enter name) (small.filter (· != name)) (path ++ [0]) body
  | .imp _ conclusion => sites info frame small (path ++ [1]) conclusion
  | goal =>
      match program.callOf? goal with
      | some (predicate, args) =>
          match program.io? predicate args with
          | some (inputs, _) => [⟨path, predicate, goal, inputs.all (frame.small small), frame.decreasing inputs⟩]
          | none => []
      | none => []

/-- `flow` through a clause body, goal by goal. -/
def flowBody (info : Symbol → Bool) (frame : Frame Variable Literal Symbol) :
    List Variable → List (Term Variable Literal Symbol) → List Variable
  | small, [] => small
  | small, goal :: rest => flowBody info frame (program.flow info frame small goal) rest

/-- The call sites of a clause body, each at the site of its body goal. -/
def sitesBody (info : Symbol → Bool) (frame : Frame Variable Literal Symbol) (index : Nat) :
    Nat → List Variable → List (Term Variable Literal Symbol) → List (Site × CallSite Variable Literal Symbol)
  | _, _, [] => []
  | position, small, goal :: rest =>
      (program.sites info frame small [] goal).map (Site.body index position, ·) ++
        sitesBody info frame index (position + 1) (program.flow info frame small goal) rest

/-! ## Blockers of data and of heads -/

mutual
/-- Blockers for a data position: data are names, literals, and applications
of declared constructors. An application by `ho_apply`, a defined operation,
a dictionary call, or a formula is outside the fragment. -/
def dataBlockers (site : Site) (path : List Nat) : Term Variable Literal Symbol → List (Blocker Variable Literal Symbol)
  | .var _ | .lit _ => []
  | .app symbol args =>
      if symbol = program.hoApply then [outside site path (.app symbol args) .hoApplyConversion]
      else if program.free symbol args.length then argsBlockers site path 0 args
      else [blocker site path (.app symbol args) (.construct .operation)]
  | .dictionaryCall dictionary selectors operation args =>
      [outside site path (.dictionaryCall dictionary selectors operation args) .dictionaryLaw]
  | term => [outside site path term .termKind]

def argsBlockers (site : Site) (path : List Nat) : Nat → List (Term Variable Literal Symbol) →
    List (Blocker Variable Literal Symbol)
  | _, [] => []
  | index, arg :: rest => dataBlockers site (path ++ [index]) arg ++ argsBlockers site path (index + 1) rest
end

/-! ## Safety -/

end Program

/-- A NAF goal: its site, path, and formula, the predicates its operand may
call, and whether it needs constructive negation (a flexible name or an
eigenvariable in its operand). -/
structure Negation (Variable Literal Symbol : Type) where
  site : Site
  path : List Nat
  formula : Term Variable Literal Symbol
  callees : List Symbol
  constructive : Bool

/-- What scanning finds: blockers, P2 reasons, and NAF goals. -/
structure Found (Variable Literal Symbol : Type) where
  blockers : List (Blocker Variable Literal Symbol)
  notes : List (Note Variable Literal Symbol)
  negations : List (Negation Variable Literal Symbol)

instance : Append (Found Variable Literal Symbol) :=
  ⟨fun first second => ⟨first.blockers ++ second.blockers, first.notes ++ second.notes,
    first.negations ++ second.negations⟩⟩

def Found.empty : Found Variable Literal Symbol := ⟨[], [], []⟩

def Found.ofBlockers (blockers : List (Blocker Variable Literal Symbol)) : Found Variable Literal Symbol :=
  ⟨blockers, [], []⟩

/-- A range guard waiting for its names, at its site and path. -/
structure Pending (Variable Literal Symbol : Type) where
  site : Site
  path : List Nat
  formula : Term Variable Literal Symbol
  names : List Variable

/-- A scan's result: what it found, the names bound after the goal, the names
a constructive NAF constrains without binding them, and the guards still
waiting. -/
structure Scan (Variable Literal Symbol : Type) where
  found : Found Variable Literal Symbol
  bound : List Variable
  constrained : List Variable
  pending : List (Pending Variable Literal Symbol)

section Safety

variable [DecidableEq Variable]

/-- The names are bound flexible names or rigid ones. -/
def available (rigid bound names : List Variable) : Bool :=
  names.all fun name => bound.contains name || rigid.contains name

/-- Close the guards waiting in a scope: each must have its names available. -/
def close (rigid bound : List Variable) (pending : List (Pending Variable Literal Symbol)) :
    List (Blocker Variable Literal Symbol) :=
  pending.filterMap fun guard =>
    if available rigid bound guard.names then none else some (blocker guard.site guard.path guard.formula .mode)

/-- The bound names after a binder for `name`: the body's, with `name` as it
was outside. -/
def restore (name : Variable) (outer inner : List Variable) : List Variable :=
  inner.filter (· != name) ++ (if outer.contains name then [name] else [])

end Safety

/-- A Harrop clause, as an implication goal may assume: atoms, conjunctions,
implications with a Harrop conclusion, universals, truth. -/
def harrop : Term Variable Literal Symbol → Bool
  | .app _ _ | .truth => true
  | .conj left right => harrop left && harrop right
  | .imp _ conclusion | .forallVar _ conclusion => harrop conclusion
  | _ => false

/-- A conjunction of atoms: an antecedent the fragment decides, when closed. -/
def atomic : Term Variable Literal Symbol → Bool
  | .app _ _ | .truth => true
  | .conj left right => atomic left && atomic right
  | _ => false

namespace Program

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] (program : Program Variable Literal Symbol)

/-- A predicate call: a declared mode at its arity, data arguments, and inputs
bound; its outputs are bound after it. `offset` is the position of the first
argument, one for a normalized `ho_apply(p, args)`. -/
def scanCall (site : Site) (rigid bound : List Variable) (path : List Nat) (formula : Term Variable Literal Symbol)
    (predicate : Symbol) (args : List (Term Variable Literal Symbol)) (offset : Nat) : Scan Variable Literal Symbol :=
  match program.io? predicate args with
  | none => ⟨.ofBlockers [blocker site path formula .mode], bound, [], []⟩
  | some (inputs, outputs) =>
      let data := program.argsBlockers site path offset args
      let unbound := if available rigid bound (inputs.flatMap Term.freeVars) then [] else [blocker site path formula .mode]
      ⟨.ofBlockers (data ++ unbound), bound ++ outputs.flatMap Term.freeVars, [], []⟩

mutual
/-- Scan a goal left to right, with the rigid names in scope and the flexible
names bound before it. A range guard waits for its names; at the end of its
scope they must be bound, or constrained by a constructive NAF (S21 decides
the guard with the constraint, by disunification with domain closure). -/
def scan (site : Site) (rigid bound : List Variable) (path : List Nat) : Term Variable Literal Symbol →
    Scan Variable Literal Symbol
  | .truth | .falsity => ⟨.empty, bound, [], []⟩
  | .conj left right =>
      let first := scan site rigid bound (path ++ [0]) left
      let second := scan site rigid first.bound (path ++ [1]) right
      ⟨first.found ++ second.found, second.bound, first.constrained ++ second.constrained, first.pending ++ second.pending⟩
  | .disj left right =>
      let first := scan site rigid bound (path ++ [0]) left
      let second := scan site rigid bound (path ++ [1]) right
      ⟨first.found ++ second.found, first.bound.filter second.bound.contains,
        first.constrained.filter (second.bound ++ second.constrained).contains ++
          second.constrained.filter (first.bound ++ first.constrained).contains,
        first.pending ++ second.pending⟩
  | .defaultNeg operand =>
      let names := operand.freeVars
      let ground := names.all fun name => bound.contains name && !rigid.contains name
      let innerRigid := if ground then rigid else rigid.filter fun name => !names.contains name
      let inner := scan site innerRigid bound (path ++ [0]) operand
      let constrained := if ground then [] else names.filter fun name => !bound.contains name && !rigid.contains name
      ⟨inner.found ++ ⟨close innerRigid (inner.bound ++ inner.constrained) inner.pending, [],
          [⟨site, path, .defaultNeg operand, program.calls operand, !ground⟩]⟩, bound, constrained, []⟩
  | .equal left right =>
      let data := program.dataBlockers site (path ++ [0]) left ++ program.dataBlockers site (path ++ [1]) right
      if available rigid bound left.freeVars || available rigid bound right.freeVars then
        ⟨.ofBlockers data, bound ++ left.freeVars ++ right.freeVars, [], []⟩
      else ⟨.ofBlockers (data ++ [blocker site path (.equal left right) .mode]), bound, [], []⟩
  | .existsVar name body =>
      let innerRigid := rigid.filter (· != name)
      let inner := scan site innerRigid (bound.filter (· != name)) (path ++ [0]) body
      ⟨inner.found ++ .ofBlockers (close innerRigid (inner.bound ++ inner.constrained)
          (inner.pending.filter (·.names.contains name))),
        restore name bound inner.bound, inner.constrained.filter (· != name),
        inner.pending.filter fun guard => !guard.names.contains name⟩
  | .forallVar name body =>
      let inner := scan site (name :: rigid) (bound.filter (· != name)) (path ++ [0]) body
      ⟨inner.found ++ ⟨close (name :: rigid) (inner.bound ++ inner.constrained) (inner.pending.filter (·.names.contains name)),
          [⟨site, path, .forallVar name body, .universal⟩], []⟩,
        restore name bound inner.bound, inner.constrained.filter (· != name),
        inner.pending.filter fun guard => !guard.names.contains name⟩
  | .imp antecedent conclusion =>
      let inner := scan site rigid bound (path ++ [1]) conclusion
      let shape :=
        if harrop antecedent then
          antecedentBlockers site (path ++ [0]) antecedent ++
            (if available rigid bound antecedent.freeVars then [] else [blocker site (path ++ [0]) antecedent .mode])
        else [outside site (path ++ [0]) antecedent .scopedProof]
      let decided := atomic antecedent && antecedent.freeVars.isEmpty
      ⟨⟨shape, if harrop antecedent && !decided then [⟨site, path, .imp antecedent conclusion, .hypothesis⟩] else [],
          []⟩ ++ inner.found, inner.bound, inner.constrained, inner.pending⟩
  | .var name => ⟨.ofBlockers [outside site path (.var name) .formulaVariable], bound, [], []⟩
  | .lit value => ⟨.ofBlockers [outside site path (.lit value) .termKind], bound, [], []⟩
  | .dictionaryCall dictionary selectors operation args =>
      ⟨.ofBlockers [outside site path (.dictionaryCall dictionary selectors operation args) .dictionaryLaw], bound, [], []⟩
  | .app symbol args =>
      if symbol = program.hoApply then
        match args with
        | .app predicate [] :: rest =>
            if predicate = program.hoApply ∨ program.guard predicate = true ∨ program.marker predicate = true then
              ⟨.ofBlockers [outside site path (.app symbol args) .hoApplyConversion], bound, [], []⟩
            else program.scanCall site rigid bound path (.app symbol args) predicate rest 1
        | _ => ⟨.ofBlockers [outside site path (.app symbol args) .hoApplyConversion], bound, [], []⟩
      else if program.guard symbol then
        ⟨.ofBlockers (program.argsBlockers site path 0 args), bound, [],
          [⟨site, path, .app symbol args, (Term.app symbol args).freeVars⟩]⟩
      else if program.marker symbol then
        ⟨.ofBlockers (program.argsBlockers site path 0 args ++
            (if available rigid bound (Term.app symbol args).freeVars then [] else [blocker site path (.app symbol args) .mode])),
          bound, [], []⟩
      else program.scanCall site rigid bound path (.app symbol args) symbol args 0

/-- The blockers of what a Harrop antecedent assumes: its atoms' data, an
application by `ho_apply` of a predicate variable, and the constructs of its
rules' bodies, each scanned with its names available (the safety of a local
rule is S26's). -/
def antecedentBlockers (site : Site) (path : List Nat) : Term Variable Literal Symbol → List (Blocker Variable Literal Symbol)
  | .app symbol args =>
      if symbol = program.hoApply then
        match args with
        | .app predicate [] :: rest =>
            if predicate = program.hoApply ∨ program.guard predicate = true ∨ program.marker predicate = true then
              [outside site path (.app symbol args) .hoApplyConversion]
            else program.argsBlockers site path 1 rest
        | _ => [outside site path (.app symbol args) .hoApplyConversion]
      else program.argsBlockers site path 0 args
  | .conj left right =>
      antecedentBlockers site (path ++ [0]) left ++ antecedentBlockers site (path ++ [1]) right
  | .imp body conclusion =>
      (scan site body.freeVars [] (path ++ [0]) body).found.blockers ++ antecedentBlockers site (path ++ [1]) conclusion
  | .forallVar _ conclusion => antecedentBlockers site (path ++ [0]) conclusion
  | _ => []
end

/-- Scan a clause body goal by goal, each at its site. -/
def scanBody (index : Nat) (rigid : List Variable) :
    Nat → List Variable → List (Term Variable Literal Symbol) → Scan Variable Literal Symbol
  | _, bound, [] => ⟨.empty, bound, [], []⟩
  | position, bound, goal :: rest =>
      let first := program.scan (.body index position) rigid bound [] goal
      let next := scanBody index rigid (position + 1) first.bound rest
      ⟨first.found ++ next.found, next.bound, first.constrained ++ next.constrained, first.pending ++ next.pending⟩

end Program

/-- Close a scope's waiting guards: their names must be bound, or constrained
by a constructive NAF. -/
def Scan.close [DecidableEq Variable] (rigid : List Variable) (result : Scan Variable Literal Symbol) :
    List (Blocker Variable Literal Symbol) :=
  Tabled.close rigid (result.bound ++ result.constrained) result.pending

end AnthillModKbSpec.Tabled
