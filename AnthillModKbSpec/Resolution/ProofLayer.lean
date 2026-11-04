import AnthillModKbSpec.Resolution.P0.Admission
import AnthillModKbSpec.Resolution.Machine.LeftStrategy

/-! # Proof-layer capabilities beside P0 admission (S09)

P0 admission asks for evidence for every formula outside its classes. Some of
those formulas have proof-layer commands: S09's left rules and compound-head
commands use them in a machine run of the left strategy, and the trees such a
run exports are checked by the explicit-proof route (`P1.checkProof`). That is
a capability of the proof layer, not admitted automatic execution: the input
stays outside P0, and nothing claims that a search using these commands
terminates.

`Request.proofLayer` names, for one request, the S09 commands that use its
formula, or the introduction rules for a scoped goal; `Request.proofLayerIn`
also marks a name inside a NAF operand with S10's refutation route, and an
application by `ho_apply` outside data with S11's conversion. `diagnose` annotates
P0's own answer, so a proof-layer capability is reported only for an input P0
does not admit (`diagnose_not_ready`), and diagnosing changes no admission
result. -/

namespace AnthillModKbSpec.Admission

open Machine

variable {Domain Variable Literal Symbol : Type}

/-- What the proof layer offers for a formula P0 asks evidence for. -/
inductive ProofLayer where
  /-- Commands that use the formula. Proofs built with them are checked by the
  explicit-proof route, and the left strategy may try them; neither admits
  the formula for automatic execution. -/
  | commands (commands : List RuleId)
  /-- A scoped goal: the introduction rules (S06) and the left commands under
  the scope they open. -/
  | introduction
  /-- A name inside a NAF operand, where P0 needs a ground instance: evidence-
  first NAF (S10) refutes the operand in the completed program, the name a
  rigid parameter, and the refutation is checked by the explicit-proof route.
  Nothing claims the refutation search terminates. -/
  | refutation
  /-- No S09, S10, or S11 command: the request needs another capability
  (S12–S14), or none is implemented. -/
  | none
  deriving DecidableEq, Repr

/-- The commands that use an assumption of this shape. -/
def assumptionCommands (formula : Term Variable Literal Symbol) : List RuleId :=
  match formula with
  | .conj _ _ => [.conjUse]
  | .disj _ _ => [.disjCases]
  | .existsVar _ _ => [.existsOpen]
  | .imp _ _ => [.impUse]
  | .forallVar _ _ =>
      match stripLeading (leadingBinders formula).length formula with
      | .imp _ _ => [.impUse, .forallUse]
      | _ => [.forallUse]
  | .falsity => [.falsityElim]
  | _ => []

/-- The commands that use a clause head of this shape: a conjunctive head is
split or assumed, a head `A → false` is also a denial, a head `false` closes
falsity or eliminates it, and other compound heads are assumed once their
body is proved. -/
def headCommands : Term Variable Literal Symbol → List RuleId
  | .conj _ _ => [.headProject, .headUse]
  | .imp _ .falsity => [.headDenial, .headUse]
  | .disj _ _ | .imp _ _ | .forallVar _ _ | .existsVar _ _ => [.headUse]
  | .falsity => [.clause, .falsityElim]
  | _ => []

def ProofLayer.ofCommands : List RuleId → ProofLayer
  | [] => .none
  | first :: rest => .commands (first :: rest)

/-- The proof-layer capability for one request. -/
def Request.proofLayer (request : Request Variable Literal Symbol) : ProofLayer :=
  match request.site, request.capability with
  | .assumption _, .scopedProof => .ofCommands (assumptionCommands request.formula)
  | .head _, .compoundHead => .ofCommands (headCommands request.formula)
  | .head _, .contradiction => .commands [.goalClause, .falsityElim]
  | .goal, .scopedProof | .body _ _, .scopedProof => .introduction
  | _, _ => .none

/-- The path, inside a NAF operand, ends in the arguments of an atom. -/
def inAtomData : List Nat → Term Variable Literal Symbol → Bool
  | 0 :: rest, .conj left _ => inAtomData rest left
  | 1 :: rest, .conj _ right => inAtomData rest right
  | 0 :: rest, .defaultNeg operand => inAtomData rest operand
  | _ :: _, .app _ _ => true
  | _, _ => false

/-- The goal path, as `goalRequests` builds it, enters a NAF operand and ends
inside the arguments of one of its atoms: a name in data, which the refutation
route treats as a parameter. A formula variable as the operand, or as a goal
inside it, is not refuted. -/
def nafAlong : List Nat → Term Variable Literal Symbol → Bool
  | 0 :: rest, .defaultNeg operand => inAtomData rest operand
  | 0 :: rest, .conj left _ => nafAlong rest left
  | 1 :: rest, .conj _ right => nafAlong rest right
  | _, _ => false

/-- The goal formula at a site: the query goal or a KB clause's body goal. -/
def Input.goalAt? (input : Input Domain Variable Literal Symbol) : Site → Option (Term Variable Literal Symbol)
  | .goal => some input.goal
  | .body clause position =>
      (OperationDictionaries.lookup input.kbClauses clause).bind fun
        | .definite _ body | .goal body => body[position]?
  | _ => none

/-- The goal path, as `goalRequests` builds it, enters a NAF operand. -/
def throughNaf : List Nat → Term Variable Literal Symbol → Bool
  | 0 :: _, .defaultNeg _ => true
  | 0 :: rest, .conj left _ => throughNaf rest left
  | 1 :: rest, .conj _ right => throughNaf rest right
  | _, _ => false

/-- The S11 commands for an application by `ho_apply` that P0 asks evidence
for: as a goal, `ho_goal` (`hoApplyIntro`) and converted candidates; as an
assumption or a clause head, converted candidates for direct goals. Inside data
nothing converts: `holds_hoApply` relates truth, not values, so a call by
`ho_apply` as an argument is compared only with a call by `ho_apply`. Nor does
anything inside a NAF operand: conversion gives positive evidence, never
failure of the operand, and the completion closes no `ho_apply` (S10). -/
def Request.conversionLayer (input : Input Domain Variable Literal Symbol) (request : Request Variable Literal Symbol) :
    ProofLayer :=
  match request.site with
  | .goal | .body _ _ =>
      if ((input.goalAt? request.site).map fun goal =>
          inAtomData request.path goal || throughNaf request.path goal).getD true then .none
      else .commands [.hoApplyIntro, .converted]
  | .assumption _ | .head _ => if request.path.isEmpty then .commands [.converted] else .none

/-- The conclusion of a formula, through its implications, applies a predicate
by `ho_apply`. -/
def concludesIndirect [DecidableEq Symbol] (hoApplySymbol : Symbol) : Term Variable Literal Symbol → Bool
  | .imp _ conclusion => concludesIndirect hoApplySymbol conclusion
  | .app symbol _ => decide (symbol = hoApplySymbol)
  | _ => false

/-- The proof-layer capability for one request of an input: a ground-instance
request inside a NAF operand has the refutation route, and an application by
`ho_apply` in a goal, an assumption, or a head the S11 conversion. A compound
head concluding a call by `ho_apply`, such as an induction principle's, is also
selected whole and converted (S11's `headMatch`). -/
def Request.proofLayerIn [DecidableEq Symbol] (hoApplySymbol : Symbol) (input : Input Domain Variable Literal Symbol)
    (request : Request Variable Literal Symbol) : ProofLayer :=
  if request.capability == .groundInstance && ((input.goalAt? request.site).map (nafAlong request.path)).getD false then
    .refutation
  else if request.capability == .hoApplyConversion then request.conversionLayer input
  else if request.capability == .compoundHead && concludesIndirect hoApplySymbol request.formula then
    .commands (headCommands request.formula ++ [.converted])
  else request.proofLayer

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

/-- P0's requests for an input, each with its proof-layer capability. An input
P0 admits, or declares invalid, gets none. -/
def diagnose (hoApplySymbol : Symbol) (input : Input Domain Variable Literal Symbol) :
    List (Request Variable Literal Symbol × ProofLayer) :=
  match check hoApplySymbol input with
  | .needsEvidence request more => (request :: more).map fun found => (found, found.proofLayerIn hoApplySymbol input)
  | _ => []

/-- A diagnosis is P0's answer annotated: every diagnosed formula is one P0
asks evidence for. -/
theorem diagnose_requests {hoApplySymbol : Symbol} {input : Input Domain Variable Literal Symbol}
    {entry : Request Variable Literal Symbol × ProofLayer} (member : entry ∈ diagnose hoApplySymbol input) :
    ∃ request more, check hoApplySymbol input = .needsEvidence request more ∧ entry.1 ∈ request :: more ∧
      entry.2 = entry.1.proofLayerIn hoApplySymbol input := by
  unfold diagnose at member
  split at member
  · rename_i request more checked
    obtain ⟨found, inside, rfl⟩ := List.mem_map.mp member
    exact ⟨request, more, checked, inside, rfl⟩
  all_goals cases member

/-- A proof-layer capability is reported only for an input P0 does not admit:
the commands are not admitted automatic execution. -/
theorem diagnose_not_ready {hoApplySymbol : Symbol} {input : Input Domain Variable Literal Symbol}
    {entry : Request Variable Literal Symbol × ProofLayer} (member : entry ∈ diagnose hoApplySymbol input)
    (plan : Plan Domain Variable Literal Symbol hoApplySymbol) : check hoApplySymbol input ≠ .ready plan := by
  obtain ⟨request, more, checked, _, _⟩ := diagnose_requests member
  rw [checked]
  exact fun same => by cases same

end AnthillModKbSpec.Admission
