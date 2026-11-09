import AnthillModKbSpec.Resolution.P0.Admission
import AnthillModKbSpec.Resolution.Machine.Lemma

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
result.

A formula P0 asks evidence for at a goal may also be concluded by a checked
lemma (S20). `diagnoseLemmas` lists, for each such request, the lemmas whose
statement may conclude it and the command that would use each
(`lemmaCommand`). That too is a proof-layer capability: P0 admission takes no
lemma, so a lemma never makes an input P0-Ready (`diagnoseLemmas_not_ready`);
a lemma enters a P0 program only as an imported clause (`P1.admitImports`). -/

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

/-- Follow a goal path, as `goalRequests` builds it, through conjunctions to a
NAF operand, where `atNaf` reads the rest of the path and the operand. -/
def toNaf (atNaf : List Nat → Term Variable Literal Symbol → Bool) :
    List Nat → Term Variable Literal Symbol → Bool
  | 0 :: rest, .defaultNeg operand => atNaf rest operand
  | 0 :: rest, .conj left _ => toNaf atNaf rest left
  | 1 :: rest, .conj _ right => toNaf atNaf rest right
  | _, _ => false

/-- The goal path enters a NAF operand and ends inside the arguments of one of
its atoms: a name in data, which the refutation route treats as a parameter. A
formula variable as the operand, or as a goal inside it, is not refuted. -/
def nafAlong : List Nat → Term Variable Literal Symbol → Bool := toNaf inAtomData

/-- The goal formula at a site: the query goal or a KB clause's body goal. -/
def Input.goalAt? (input : Input Domain Variable Literal Symbol) : Site → Option (Term Variable Literal Symbol)
  | .goal => some input.goal
  | .body clause position =>
      (OperationDictionaries.lookup input.kbClauses clause).bind fun
        | .definite _ body | .goal body => body[position]?
  | _ => none

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
          inAtomData request.path goal || toNaf (fun _ _ => true) request.path goal).getD true then .none
      else .commands [.hoApplyIntro, .converted]
  | .assumption _ | .head _ => if request.path.isEmpty then .commands [.converted] else .none

/-- Some conclusion of a formula, through implications, quantifiers,
conjunctions, and disjunctions, applies a predicate by `ho_apply`: once the
left rules or a head command reach it, it is used converted (S11). -/
def concludesIndirect [DecidableEq Symbol] (hoApplySymbol : Symbol) : Term Variable Literal Symbol → Bool
  | .imp _ conclusion | .forallVar _ conclusion | .existsVar _ conclusion => concludesIndirect hoApplySymbol conclusion
  | .conj left right | .disj left right =>
      concludesIndirect hoApplySymbol left || concludesIndirect hoApplySymbol right
  | .app symbol _ => decide (symbol = hoApplySymbol)
  | _ => false

/-- A capability's commands with S11's conversion added. -/
def ProofLayer.withConversion : ProofLayer → ProofLayer
  | .commands used => .commands (used ++ [.converted])
  | other => other

/-- The proof-layer capability for one request of an input: a ground-instance
request inside a NAF operand has the refutation route, and an application by
`ho_apply` in a goal, an assumption, or a head the S11 conversion. A
non-atomic assumption or a compound head with a conclusion applying a
predicate by `ho_apply`, such as a local rule's or an induction principle's,
is also used converted: by `ruleUse`, `headProject`, or `headMatch`. -/
def Request.proofLayerIn [DecidableEq Symbol] (hoApplySymbol : Symbol) (input : Input Domain Variable Literal Symbol)
    (request : Request Variable Literal Symbol) : ProofLayer :=
  if request.capability == .groundInstance && ((input.goalAt? request.site).map (nafAlong request.path)).getD false then
    .refutation
  else if request.capability == .hoApplyConversion then request.conversionLayer input
  else if (request.capability == .compoundHead || request.capability == .scopedProof) &&
      concludesIndirect hoApplySymbol request.formula then request.proofLayer.withConversion
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

/-! ## Formulas a checked lemma may conclude (S20) -/

/-- The path, through conjunctions only, ends at a goal of the formula: not
inside a NAF operand, where proving the operand refutes the goal, nor in an
atom's arguments. -/
def atGoal : List Nat → Term Variable Literal Symbol → Bool
  | [], _ => true
  | 0 :: rest, .conj left _ => atGoal rest left
  | 1 :: rest, .conj _ right => atGoal rest right
  | _, _ => false

/-- The formula and the goals its introduction rules leave: through
conjunctions, disjunctions, implication conclusions, and quantifier bodies. -/
def subgoals : Term Variable Literal Symbol → List (Term Variable Literal Symbol)
  | .conj left right => .conj left right :: (subgoals left ++ subgoals right)
  | .disj left right => .disj left right :: (subgoals left ++ subgoals right)
  | .imp premise conclusion => .imp premise conclusion :: subgoals conclusion
  | .forallVar binder body => .forallVar binder body :: subgoals body
  | .existsVar binder body => .existsVar binder body :: subgoals body
  | goal => [goal]

/-- A simple conclusion that may conclude the goal, as the machine compares
them (`compareLemma`): the same head, a head that differs only by `ho_apply`,
or the same connective. -/
def mayConcludeAs (hoApplySymbol : Symbol) (goal conclusion : Term Variable Literal Symbol) : Bool :=
  simpleConclusion conclusion && (mayMatch hoApplySymbol goal conclusion || sameConnective goal conclusion)

/-- A component of a lemma's conclusion concludes the formula: the formula is
an instance of it over the names a use may instantiate (`universal`), or it is
simple with the formula's head. A component naming a name bound by an
enclosing existential (`existential`) concludes nothing: the cut opens the
existential at a fresh rigid name, which no goal names. -/
def componentConcludes (hoApplySymbol : Symbol) (formula : Term Variable Literal Symbol)
    (universal existential : List Variable) (component : Term Variable Literal Symbol) : Bool :=
  !(component.freeVars.any fun name => decide (name ∈ existential)) &&
    ((extract universal component formula []).isSome || mayConcludeAs hoApplySymbol formula component)

/-- Some component of a conclusion a cut leaves to the left commands concludes
the formula: the conclusion itself, then through conjunctions, disjunctions,
implication conclusions, and quantifier bodies, a universal's binder one a use
may instantiate and an existential's one it may not. -/
def lemmaReaches (hoApplySymbol : Symbol) (formula : Term Variable Literal Symbol) :
    List Variable → List Variable → Term Variable Literal Symbol → Bool
  | universal, existential, .imp premise conclusion =>
      componentConcludes hoApplySymbol formula universal existential (.imp premise conclusion) ||
        lemmaReaches hoApplySymbol formula universal existential conclusion
  | universal, existential, .forallVar binder body =>
      componentConcludes hoApplySymbol formula universal existential (.forallVar binder body) ||
        lemmaReaches hoApplySymbol formula (binder :: universal) (existential.filter (· ≠ binder)) body
  | universal, existential, .existsVar binder body =>
      componentConcludes hoApplySymbol formula universal existential (.existsVar binder body) ||
        lemmaReaches hoApplySymbol formula (universal.filter (· ≠ binder)) (binder :: existential) body
  | universal, existential, .conj left right =>
      componentConcludes hoApplySymbol formula universal existential (.conj left right) ||
        lemmaReaches hoApplySymbol formula universal existential left ||
        lemmaReaches hoApplySymbol formula universal existential right
  | universal, existential, .disj left right =>
      componentConcludes hoApplySymbol formula universal existential (.disj left right) ||
        lemmaReaches hoApplySymbol formula universal existential left ||
        lemmaReaches hoApplySymbol formula universal existential right
  | universal, existential, component => componentConcludes hoApplySymbol formula universal existential component

/-- How a lemma's statement may conclude a requested formula, at the formula or
at a goal its introduction rules leave, as the machine would use it: the
statement itself, or an instance of its simple matrix, by `lemmaUse`; the simple
conclusion of its implication by `lemmaRule`; a component of a compound
conclusion through a cut on an instance (`lemmaCut`), the S09 commands then
using it. -/
def lemmaCommand (hoApplySymbol : Symbol) (formula statement : Term Variable Literal Symbol) : Option RuleId :=
  if identical formula statement then some .lemmaUse
  else
    let binders := leadingBinders statement
    let goals := subgoals formula
    let cut := fun (matrix : Term Variable Literal Symbol) =>
      if goals.any fun goal => lemmaReaches hoApplySymbol goal binders [] matrix then some RuleId.lemmaCut else none
    match stripLeading binders.length statement with
    | .imp premise conclusion =>
        if goals.any fun goal => mayConcludeAs hoApplySymbol goal conclusion then some .lemmaRule
        else cut (.imp premise conclusion)
    | matrix => if goals.any fun goal => mayConcludeAs hoApplySymbol goal matrix then some .lemmaUse else cut matrix

/-- The lemmas that may conclude a requested formula, with their commands. -/
def lemmasConcluding (hoApplySymbol : Symbol) (statements : List (Symbol × Term Variable Literal Symbol))
    (formula : Term Variable Literal Symbol) : List (Symbol × RuleId) :=
  statements.filterMap fun entry => (lemmaCommand hoApplySymbol formula entry.2).map (entry.1, ·)

/-- P0's requests at a goal of the query or of a clause body that lemmas may
conclude, each with those lemmas and their commands. A request inside a NAF
operand or inside an atom's arguments is no goal a lemma could close. An input
P0 admits, or declares invalid, gets none. -/
def diagnoseLemmas (hoApplySymbol : Symbol) (statements : List (Symbol × Term Variable Literal Symbol))
    (input : Input Domain Variable Literal Symbol) : List (Request Variable Literal Symbol × List (Symbol × RuleId)) :=
  match check hoApplySymbol input with
  | .needsEvidence request more =>
      (request :: more).filterMap fun found =>
        if (input.goalAt? found.site).any (atGoal found.path) then
          match lemmasConcluding hoApplySymbol statements found.formula with
          | first :: rest => some (found, first :: rest)
          | [] => none
        else none
  | _ => []

/-- A lemma diagnosis is P0's answer annotated: every diagnosed formula is one
P0 asks evidence for. -/
theorem diagnoseLemmas_requests {hoApplySymbol : Symbol} {statements : List (Symbol × Term Variable Literal Symbol)}
    {input : Input Domain Variable Literal Symbol} {entry : Request Variable Literal Symbol × List (Symbol × RuleId)}
    (member : entry ∈ diagnoseLemmas hoApplySymbol statements input) :
    ∃ request more, check hoApplySymbol input = .needsEvidence request more ∧ entry.1 ∈ request :: more ∧
      entry.2 = lemmasConcluding hoApplySymbol statements entry.1.formula := by
  unfold diagnoseLemmas at member
  split at member
  · rename_i request more checked
    obtain ⟨found, inside, produced⟩ := List.mem_filterMap.mp member
    refine ⟨request, more, checked, ?_⟩
    split at produced
    · split at produced
      · rename_i concluding
        cases produced
        exact ⟨inside, concluding.symm⟩
      · cases produced
    · cases produced
  all_goals cases member

/-- A formula usable through a checked lemma is a proof-layer capability,
reported only for an input P0 does not admit: a lemma never makes an input
P0-Ready. -/
theorem diagnoseLemmas_not_ready {hoApplySymbol : Symbol} {statements : List (Symbol × Term Variable Literal Symbol)}
    {input : Input Domain Variable Literal Symbol} {entry : Request Variable Literal Symbol × List (Symbol × RuleId)}
    (member : entry ∈ diagnoseLemmas hoApplySymbol statements input) (plan : Plan Domain Variable Literal Symbol hoApplySymbol) :
    check hoApplySymbol input ≠ .ready plan := by
  obtain ⟨request, more, checked, _, _⟩ := diagnoseLemmas_requests member
  rw [checked]
  exact fun same => by cases same

end AnthillModKbSpec.Admission
