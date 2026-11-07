import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Machine AnthillModKbSpec.Semantics AnthillModKbSpec.InductiveDomains
  AnthillModKbSpec.AdmissionSignature AnthillModKbSpec.Induction

namespace InductionTests

/-! Executable traces of S12 on the induction model (`InductionModel`): the Nat
principle lowered with `P` at `.predicate 1`, its admission, one run of the
plan's strategy for `∀x:Nat. reachable(x)`, the exported tree checked by the
S08 checker, and the guarded universal true in the model by `InductiveSoundness`.
Each `#guard` evaluates compiled code. -/

open AnthillModKbSpec.InductionModel

attribute [local instance] termEq clauseEq

/-- Nat is the model's one domain: `isNat` its membership and `D_all` symbol,
`isPred n` the predicate range of arity n; reachable registered at arities 1
and 2, even at 1. -/
def signature : SignatureSnapshot Domain Symbol :=
  ⟨0, ⟨family, membershipSymbol, .isNat, .isPred, [⟨.reachable, 1⟩, ⟨.reachable, 2⟩, ⟨.even, 1⟩]⟩⟩

theorem realized : AdmissionSignature.Realizes signature model := by
  refine ⟨realizes, fun value => ?_, fun arity value => ?_⟩
  · constructor
    · intro truth
      obtain ⟨tree, member, same⟩ := (realizes .nat value).mp truth
      exact ⟨tree, ⟨.nat, by simp [signature, family], member⟩, same⟩
    · rintro ⟨tree, ⟨domain, _, member⟩, same⟩
      cases domain
      exact (realizes .nat value).mpr ⟨tree, member, same⟩
  · show model.holds (model.application (.isPred arity) [value]) ↔ _
    rw [application_isPred]
    constructor
    · rintro ⟨symbol, member, rfl⟩
      exact ⟨symbol, by simpa [SignatureSnapshot.Registered, signature, predicateRegistry] using member, rfl⟩
    · rintro ⟨symbol, declared, rfl⟩
      exact ⟨symbol, by simpa [SignatureSnapshot.Registered, signature, predicateRegistry] using declared, rfl⟩

def rules : List (Rule Domain Symbol) := [zeroRule, succRule]
def generatedNames : Nat → String := fun index => s!"v{index}"

theorem listed : ∀ rule ∈ rules, signature.signature.data.definitions rule := by
  intro rule member
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at member
  exact member

theorem complete : ∀ rule, signature.signature.data.definitions rule → rule ∈ rules := by
  intro rule declared
  rcases declared with rfl | rfl <;> simp [rules]

theorem distinct : DistinctNames signature.signature.data.definitions generatedNames := by
  intro rule declared first second _
  rcases declared with rfl | rfl
  · exact Fin.elim0 first
  · have := first.isLt; have := second.isLt
    exact Fin.ext (by simp [succRule] at *; omega)

/-- The principle's names: P, x, and the fields `y0, y1, …` of a case. -/
def principleNames : Names String := ⟨"P", "x", fun index => s!"y{index}"⟩

/-- The structural principle of Nat, generated from its rules: the base
`ho_apply(P, zero)` and the step `∀y0:Nat. (ho_apply(P, y0) → ho_apply(P, succ(y0)))`.
The source clause is lowered by `elaborateClause?` with `P` at `.predicate 1`. -/
def principleSource : HornClause String Unit Symbol := source .hoApply signature.naming .nat rules principleNames
def lowered : Option (HornClause String Unit Symbol) :=
  Elaboration.elaborateClause? .hoApply signature.naming (ranges .nat rules) (rangeOf principleNames) principleSource
def principleClause : HornClause String Unit Symbol := principle .hoApply signature.naming .nat rules principleNames

#guard lowered.isSome
#guard decide (lowered = some principleClause)
-- A data range on P is rejected, never D_all-guarded.
#guard (Elaboration.elaborateClause? .hoApply signature.naming (ranges .nat rules) (rangeOf principleNames .allData)
  principleSource).isNone
example : Elaboration.elaborateClause? .hoApply signature.naming (ranges .nat rules) (rangeOf principleNames .allData)
    principleSource = none := lower_rejects _ _ _ _ _ rfl
example : Elaboration.elaborateClause? .hoApply signature.naming (ranges .nat rules)
    (rangeOf principleNames (.data [.nat])) principleSource = none := lower_rejects _ _ _ _ _ rfl

/-- The effective program: the reachable clauses, the lowered principle, and
the generated signature clauses. -/
def kbClauses : List (HornClause String Unit Symbol) := [reachableZero, reachableSucc, principleClause]
def generated : List (HornClause String Unit Symbol) := signatureClauses signature generatedNames rules
def program (clauses : List (HornClause String Unit Symbol) := kbClauses) : Program String Unit Symbol :=
  ⟨clauses.mapIdx (fun index clause => ⟨.lowered index, clause⟩) ++ generated.map (⟨.signature, ·⟩),
    guardSymbol signature⟩

def input (goal : T) (clauses : List (HornClause String Unit Symbol) := kbClauses) (context : List T := []) :
    Admission.Input Domain String Unit Symbol :=
  ⟨signature, generatedNames, rules, listed, complete, distinct, program clauses, fun _ => guardSymbol_iff, context, goal⟩

/-- `∀x:Nat. p(x)`, lowered. -/
def universal (predicate : Symbol) : T := Target.goal signature.naming ⟨"x", .nat, predicate⟩

def admitted (goal : T) (clauses : List (HornClause String Unit Symbol) := kbClauses) :
    Induction.Result Domain String Unit Symbol .hoApply :=
  Induction.check .hoApply (input goal clauses)

def kindOf : Induction.Result Domain String Unit Symbol .hoApply → String
  | .ready _ => "ready"
  | .needsEvidence needs => s!"needs {needs.length}"
  | .invalid _ => "invalid"

def missingOf : Missing → String
  | .capability capability => s!"{repr capability}" | .negation => "negation"
  | .waitingGuard => "waitingGuard"

def gapOf (gap : CaseGap String Unit Symbol) : String := s!"{repr gap.site} {gap.path} {missingOf gap.missing}"

def needOf : Need String Unit Symbol → String
  | .shape => "shape" | .registration _ => "registration" | .principle => "principle"
  | .names => "names"
  | .context gap => s!"context {gapOf gap}"
  | .clause gap => s!"clause {gapOf gap}"

def needsOf : Induction.Result Domain String Unit Symbol .hoApply → List String
  | .needsEvidence needs => needs.map needOf
  | _ => []

/-! ### Admission -/

#guard kindOf (admitted (universal .reachable)) = "ready"
-- The universal has no P0 plan: P0 asks scoped-proof evidence for it.
#guard match Admission.check .hoApply (input (universal .reachable)) with
  | .needsEvidence request _ => request.site == .goal && request.capability == .scopedProof
  | _ => false
-- A predicate outside the unary range: zero is no registered reference.
#guard needsOf (admitted (universal .zero)) = ["registration"]
-- A goal that is not a lowered guarded universal over a declared domain.
#guard needsOf (admitted (.forallVar "x" (.imp (isNat (.var "x")) (reachable (.var "x"))))) = ["shape"]
#guard needsOf (admitted (reachable zero)) = ["shape"]
-- A program without the principle.
#guard needsOf (admitted (universal .reachable) [reachableZero, reachableSucc]) = ["principle"]
-- A clause a case may select needs an extension: reported before the run.
def disjunctive : HornClause String Unit Symbol := .definite (reachable (succ (.var "x")))
  [.disj (reachable (.var "x")) (even (.var "x"))]
#guard needsOf (admitted (universal .reachable) [reachableZero, disjunctive, principleClause]) =
  ["clause AnthillModKbSpec.Admission.Site.body 1 0 [] AnthillModKbSpec.Admission.Capability.scopedProof"]
-- So does the atomic induction clause, which positive search would select
-- again on every unary call: its head applies P by ho_apply.
#guard (needsOf (admitted (universal .reachable) (kbClauses ++ [inductionRule]))).contains
  "clause AnthillModKbSpec.Admission.Site.head 3 [] AnthillModKbSpec.Admission.Capability.hoApplyConversion"
-- NAF in a dependency: the plan's run has no NAF route.
def negated : HornClause String Unit Symbol := .definite (reachable (succ (.var "x")))
  [.defaultNeg (even (.var "x")), reachable (.var "x")]
#guard needsOf (admitted (universal .reachable) [reachableZero, negated, principleClause]) =
  ["clause AnthillModKbSpec.Admission.Site.body 1 0 [] negation"]
-- A KB clause concluding the guard P_1: the principle's premises ask it, so it
-- is a dependency, though no clause body mentions it.
def guardDefinition : HornClause String Unit Symbol := .definite (.app (.isPred 1) [.app .even []])
  [.app (.isPred 1) [.app .even []]]
#guard needsOf (admitted (universal .reachable) (kbClauses ++ [guardDefinition])) =
  ["clause AnthillModKbSpec.Admission.Site.head 3 [] AnthillModKbSpec.Admission.Capability.guardDefinition"]
-- A formula variable as a goal waits on its binding and flounders: P0's
-- formulaVariable request.
def variableGoal : HornClause String Unit Symbol := .definite (reachable (succ (.var "x")))
  [.var "q", reachable (.var "x")]
#guard needsOf (admitted (universal .reachable) [reachableZero, variableGoal, principleClause]) =
  ["clause AnthillModKbSpec.Admission.Site.body 1 0 [] AnthillModKbSpec.Admission.Capability.formulaVariable"]
-- A range guard on a name no other goal of its clause mentions flounders; one
-- on a name another body goal binds waits for it.
def waiting : HornClause String Unit Symbol := .definite (reachable (succ (.var "x")))
  [isNat (.var "z"), reachable (.var "x")]
#guard needsOf (admitted (universal .reachable) [reachableZero, waiting, principleClause]) =
  ["clause AnthillModKbSpec.Admission.Site.body 1 0 [] waitingGuard"]
def bound : HornClause String Unit Symbol := .definite (reachable (succ (.var "x")))
  [isNat (.var "z"), reachable (.var "z"), reachable (.var "x")]
#guard kindOf (admitted (universal .reachable) [reachableZero, bound, principleClause]) = "ready"
-- The query's context: a non-atomic assumption is reported.
#guard needsOf (Induction.check .hoApply (input (universal .reachable) kbClauses [.disj (even zero) (reachable zero)])) =
  ["context AnthillModKbSpec.Admission.Site.assumption 0 [] AnthillModKbSpec.Admission.Capability.scopedProof"]
-- An unrelated clause outside the dependencies is not reported.
def unrelated : HornClause String Unit Symbol := .definite (even (.var "x")) [.disj (even (.var "x")) (even zero)]
#guard kindOf (admitted (universal .reachable) (kbClauses ++ [unrelated])) = "ready"
-- A denial serves any `false` subgoal, so its body is checked; one with NAF is
-- reported, one without is not.
def negatedDenial : HornClause String Unit Symbol := .goal [.defaultNeg (even zero)]
#guard needsOf (admitted (universal .reachable) [reachableZero, reachableSucc, negatedDenial, principleClause]) =
  ["clause AnthillModKbSpec.Admission.Site.body 2 0 [] negation"]
#guard kindOf (admitted (universal .reachable) [reachableZero, reachableSucc, .goal [even zero], principleClause]) =
  "ready"
-- A formula variable as an assumption or as a head: a head `q` may meet any goal.
#guard needsOf (Induction.check .hoApply (input (universal .reachable) kbClauses [.var "q"])) =
  ["context AnthillModKbSpec.Admission.Site.assumption 0 [] AnthillModKbSpec.Admission.Capability.formulaVariable"]
#guard needsOf (admitted (universal .reachable) (kbClauses ++ [.definite (.var "q") [reachable zero]])) =
  ["clause AnthillModKbSpec.Admission.Site.head 3 [] AnthillModKbSpec.Admission.Capability.formulaVariable"]
-- NAF assumed in the query's context is a hypothesis, not a NAF goal: the plan
-- chooses no left rule on it, so it is P0's scoped-proof request.
#guard needsOf (Induction.check .hoApply (input (universal .reachable) kbClauses [.defaultNeg (even zero)])) =
  ["context AnthillModKbSpec.Admission.Site.assumption 0 [] AnthillModKbSpec.Admission.Capability.scopedProof"]
-- A guard assumption in the query's context is split at a guard goal on its term.
#guard kindOf (Induction.check .hoApply (input (universal .reachable) kbClauses [.disj (isNat zero) .falsity])) =
  "ready"
-- The principle is found in the program whatever names the generator chose.
def renamedPrinciple : HornClause String Unit Symbol :=
  principle .hoApply signature.naming .nat rules ⟨"Q", "z", fun index => s!"w{index}"⟩
#guard kindOf (admitted (universal .reachable) [reachableZero, reachableSucc, renamedPrinciple]) = "ready"

/-! ### The run -/

def runOf (goal : T) (clauses : List (HornClause String Unit Symbol) := kbClauses) (fuel : Nat := 2000) :
    Option (Outcome String Unit Symbol Unit Unit) :=
  match admitted goal clauses with
  | .ready plan => some (plan.run fuel)
  | _ => none

/-- The kind of the run of the admitted plan, or the admission result's kind. -/
def runKind (clauses : List (HornClause String Unit Symbol)) : String :=
  match admitted (universal .reachable) clauses with
  | .ready plan => s!"{repr (plan.run 3000).kind}"
  | other => kindOf other

def inductionRun : Option (Outcome String Unit Symbol Unit Unit) := runOf (universal .reachable)
def proofOf : Option (CompletedProof String Unit Symbol Unit Unit) := inductionRun.bind (·.proof?)

#guard (inductionRun.map (·.kind)) = some .success
-- The plan commits to the principle at the focus: a valid looping clause for
-- `reachable`, which the implication's introduction would reach first, is
-- never tried there.
def loop : HornClause String Unit Symbol := .definite (reachable (.var "z")) [reachable (.var "z")]
#guard runKind (kbClauses ++ [loop]) = "AnthillModKbSpec.Machine.OutcomeKind.success"
-- A step clause with an atomic guard on its variable: the case assumes the
-- field's guard as isNat(n) ∨ false and splits it at the guard goal, before the
-- generated clause isNat(v) :- isNat(v), which would loop.
def atomicGuard : HornClause String Unit Symbol := .definite (reachable (succ (.var "x")))
  [isNat (.var "x"), reachable (.var "x")]
#guard runKind [reachableZero, atomicGuard, principleClause] = "AnthillModKbSpec.Machine.OutcomeKind.success"
#guard (match admitted (universal .reachable) [reachableZero, atomicGuard, principleClause] with
  | .ready plan => (plan.run 3000).proof?.map fun proof => proof.tree.rules.contains .disjCases
  | _ => none) = some true
-- Names the generator chose differently give the same run.
#guard runKind [reachableZero, reachableSucc, renamedPrinciple] = "AnthillModKbSpec.Machine.OutcomeKind.success"
-- One guard per free name: P_1(reachable) by its generated fact, truth for
-- the target, then the base and the step.
#guard (proofOf.map (·.tree.rules)) = some [.forallIntro, .converted, .conjIntro, .clause, .truth, .conjIntro, .truth,
  .conjIntro, .hoApplyIntro, .clause, .truth, .conjIntro, .forallIntro, .impIntro, .impIntro, .hoApplyIntro, .clause,
  .conjIntro, .converted, .truth, .truth]

mutual
def nodes : ProofTree String Unit Symbol Unit → List (ProofTree String Unit Symbol Unit)
  | .node rule obligation premises subproofs => .node rule obligation premises subproofs :: nodesOf subproofs
  | .deferred _ _ => []

def nodesOf : List (ProofTree String Unit Symbol Unit) → List (ProofTree String Unit Symbol Unit)
  | [] => []
  | tree :: trees => nodes tree ++ nodesOf trees
end

/-- Every node with its rule, its goal, and its context, read through the final store. -/
def readNodes : List (RuleApp String Unit Symbol Unit × T × List T) :=
  match proofOf with
  | some proof =>
      (nodes proof.tree).filterMap fun
        | .node rule obligation _ _ =>
            some (rule, proof.store.resolve obligation.goal, obligation.context.map proof.store.resolve)
        | .deferred _ _ => none
  | none => []

/-- The rigid name the root universal is opened at. -/
def rootEigen : Option String :=
  readNodes.head?.bind fun | (.forallIntro eigen, _, _) => some eigen | _ => none

-- The principle is applied exactly once, at the focus G_Nat(a) → reachable(a),
-- with P := reachable and x := a; the rigid a is a value, never assigned.
def principleNode : RuleApp String Unit Symbol Unit × T × List T → Bool
  | (.converted _ (.clause clause _), _, _) => decide (clause = principleClause)
  | _ => false
#guard (readNodes.filter principleNode).length = 1
#guard match proofOf, rootEigen with
  | some proof, some eigen =>
      (nodes proof.tree).any fun
        | .node (.converted _ (.clause clause instantiation)) obligation _ _ =>
            decide (clause = principleClause) &&
              identical (proof.store.resolve obligation.goal)
                (.imp (Elaboration.rangeGuard signature.naming (.data [.nat]) (.var eigen)) (reachable (.var eigen))) &&
              (instantiation.map fun pair => (pair.1, proof.store.resolve pair.2)).all fun
                | ("P", value) => identical value (.app .reachable [])
                | ("x", value) => identical value (.var eigen)
                | _ => false
        | _ => false
  | _, _ => false
-- The guard P_1(reachable) is discharged by its generated fact.
#guard readNodes.any fun
  | (.clause clause _, goal, _) => decide (clause ∈ generated) && identical goal (.app (.isPred 1) [.app .reachable []])
  | _ => false
-- The step opens a fresh n, assumes Nat(n) and the hypothesis
-- ho_apply(reachable, n), and uses the hypothesis converted to reachable(n).
def stepEigen : Option String :=
  (readNodes.filterMap fun | (.forallIntro eigen, _, _) => some eigen | _ => none)[1]?
#guard match stepEigen, rootEigen with
  | some opened, some root => opened != root
  | _, _ => false
#guard match stepEigen with
  | some opened =>
      readNodes.any fun
        | (.converted _ .assumption, goal, context) =>
            identical goal (reachable (.var opened)) &&
              context.any (identical · (.hoApply .hoApply (.app .reachable []) [.var opened])) &&
              context.any (identical · (Elaboration.rangeGuard signature.naming (.data [.nat]) (.var opened)))
        | _ => false
  | none => false
-- Scope is restored: the hypothesis is assumed only inside the step's subtree,
-- and the body's last conjunct, after the step, is proved in the empty context.
def hypothesisAt : Option (List Nat) := stepEigen.map fun opened =>
  (readNodes.zipIdx.filter fun ((_, _, context), _) =>
    context.any (identical · (.hoApply .hoApply (.app .reachable []) [.var opened]))).map (·.2)
def stepAt : Option Nat := (readNodes.zipIdx.filter fun
  | ((.forallIntro _, _, _), _) => true | _ => false)[1]?.map (·.2)
#guard match hypothesisAt, stepAt with
  | some (first :: rest), some start => start < first && (first :: rest).all (· < readNodes.length - 1)
  | _, _ => false
/-- A node of the run's tree whose context holds the step's hypothesis. -/
def holdsHypothesis (proof : CompletedProof String Unit Symbol Unit Unit) (opened : String) :
    ProofTree String Unit Symbol Unit → Bool
  | .node _ obligation _ _ => obligation.context.any fun assumption =>
      identical (proof.store.resolve assumption) (.hoApply .hoApply (.app .reachable []) [.var opened])
  | .deferred _ _ => false
-- By the tree's structure: every node holding the hypothesis is in the step's
-- subtree, the one rooted at the step's universal introduction.
#guard match proofOf, stepEigen with
  | some proof, some opened =>
      match (nodes proof.tree).find? (fun | .node (.forallIntro eigen) _ _ _ => eigen == opened | _ => false) with
      | some subtree =>
          let holding := fun (trees : List (ProofTree String Unit Symbol Unit)) =>
            (trees.filter (holdsHypothesis proof opened)).length
          holding (nodes subtree) > 0 && holding (nodes subtree) == holding (nodes proof.tree)
      | none => false
  | _, _ => false
#guard (readNodes.getLast?.map fun (_, goal, context) => identical goal .truth && context.isEmpty) = some true
#guard readNodes.any fun
  | (.clause clause _, goal, context) => decide (clause = reachableZero) && identical goal (reachable zero) && context.isEmpty
  | _ => false

/-! ### The exported tree, checked -/

def checker : P1.Checker String Unit Symbol :=
  ⟨⟨.hoApply, (program).clauses.map (·.clause)⟩, NafFailure.disabled, none, []⟩

def exported : Option (P1.Proof String Unit Symbol) :=
  proofOf.bind fun proof => P1.exportTree (Certificate := Unit) (fun _ => .truth) proof.store (fun _ _ => none) proof.tree

-- S08 accepts the tree by its own rules, though the universal has no P0 plan.
#guard match exported with
  | some tree => P1.check checker (fun _ _ _ => false) [] tree && identical tree.conclusion (universal .reachable)
  | none => false

/-- The rules of a supplied tree in preorder. -/
partial def ruleNames : P1.Proof String Unit Symbol → List String
  | .node rule _ premises =>
      (match rule with
        | .clause clause _ => if decide (clause = principleClause) then ["principle"] else ["clause"]
        | .hoApplyElim => ["hoApplyElim"] | .hoApplyIntro => ["hoApplyIntro"] | .forallIntro _ => ["forallIntro"]
        | .impIntro => ["impIntro"] | .impElim => ["impElim"] | .assumption => ["assumption"] | _ => []) ++
        premises.flatMap ruleNames
-- The tree holds the principle's application, converted under the implication,
-- the base, and the scoped step.
#guard (exported.map fun tree => (ruleNames tree).take 7) =
  some ["forallIntro", "impElim", "impIntro", "impIntro", "hoApplyElim", "impElim", "assumption"]
#guard (exported.map fun tree => (ruleNames tree).contains "principle") = some true

/-- Replace the principle's application in a supplied tree. -/
partial def forge (rule : P1.Rule String Unit Symbol → P1.Rule String Unit Symbol) :
    P1.Proof String Unit Symbol → P1.Proof String Unit Symbol
  | .node original conclusion premises =>
      .node (match original with
        | .clause clause _ => if decide (clause = principleClause) then rule original else original
        | other => other) conclusion (premises.map (forge rule))

-- Forged evidence is rejected: P := even for the reachable focus.
def toEven : P1.Rule String Unit Symbol → P1.Rule String Unit Symbol
  | .clause clause instantiation =>
      .clause clause (instantiation.map fun pair => if pair.1 = "P" then (pair.1, .app .even []) else pair)
  | other => other
#guard match exported with
  | some tree => !(P1.check checker (fun _ _ _ => false) [] (forge toEven tree))
  | none => false
-- The genuine tree is rejected by a checker whose KB does not carry the
-- principle: a clause node is checked against the snapshot.
def withoutPrinciple : P1.Checker String Unit Symbol :=
  ⟨⟨.hoApply, ((program).clauses.map (·.clause)).filter (· ≠ principleClause)⟩, NafFailure.disabled, none, []⟩
#guard match exported with
  | some tree => !(P1.check withoutPrinciple (fun _ _ _ => false) [] tree)
  | none => false

/-! ### The theorems, instantiated -/

/-- The principle's names are admissible for Nat's rules. -/
theorem admissible : Admissible .hoApply (rulesOf rules .nat) principleNames :=
  admissible?_spec (by decide)

/-- Lowering the source gives the principle, for admissible names. -/
example : Elaboration.elaborateClause? .hoApply signature.naming (ranges .nat rules) (rangeOf principleNames)
    principleSource = some principleClause :=
  lower_principle _ _ _ _ _ admissible

/-- Every clause of the program is valid in the induction model: the principle
by `principle_valid`, from the exact Nat realization, the reachable clauses by
the model's own proofs, the generated clauses by the realization. -/
theorem program_valid : model.Models (program kbClauses).kb := by
  rintro clause ⟨entry, inside, rfl⟩ environment
  simp only [program, kbClauses, List.mapIdx_cons, List.mapIdx_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.mem_map] at inside
  rcases inside with rfl | rfl | rfl | ⟨generatedClause, member, rfl⟩
  · exact reachableZero_valid environment
  · exact reachableSucc_valid environment
  · exact principle_valid signature model realized complete admissible environment
  · exact Elaboration.models_signatureKb signature model realized generatedNames generatedClause
      (mem_signatureClauses listed member) environment

/-- A successful run of the admitted plan makes `∀x:Nat. reachable(x)` true in
the induction model: the run reconstructs `Derives` for the guarded universal,
and `InductiveSoundness` interprets it. -/
theorem universal_holds {plan : Induction.Plan Domain String Unit Symbol .hoApply}
    (ready : admitted (universal .reachable) = .ready plan) {fuel : Nat}
    {proof : CompletedProof String Unit Symbol Unit Unit} {resume : State String Unit Symbol Unit Unit}
    (ran : plan.run fuel = .success proof resume) (environment : Environment String Value) :
    model.Satisfies environment (universal .reachable) := by
  have sameInput := check_input ready
  let interpretation : InductiveSoundness.Interpretation family plan.input.program.kb Value .hoApply :=
    ⟨model, membershipSymbol, realizes, by rw [sameInput]; exact program_valid, complement⟩
  have derived := plan.reconstructs ran (CertifiedRefutation.failureEvidence model plan.input.program.kb)
  have goalEq : plan.target.goal plan.input.signature.naming = universal .reachable := by
    rw [← plan.goal_eq, sameInput]; rfl
  rw [← goalEq]
  exact InductiveSoundness.declarative_sound interpretation derived environment
    (by intro assumption member; simp [sameInput, input] at member)

/-- The plan's selection never chooses the principle on its premises' instances. -/
example (plan : Induction.Plan Domain String Unit Symbol .hoApply) {premise : T}
    (inside : ∀ head body, plan.principle = .definite head body → premise ∈ body)
    (σ : Substitution String Unit Symbol) :
    focus? plan.input.signature.naming plan.target (premise.instantiate σ) = false :=
  plan.body_unfocused inside σ

/-- The universal has no P0 plan. -/
example (plan : Induction.Plan Domain String Unit Symbol .hoApply)
    (other : Admission.Plan Domain String Unit Symbol .hoApply) :
    Admission.check .hoApply plan.input ≠ .ready other :=
  plan.not_p0 other

end InductionTests

namespace InductionEncodedTests

/-! Structural induction over three domains with tagged symbols, so each
exported proof is a `Term` (S08's encoding) checked by `checkProof`: Nat, Bool
(two cases without fields), and lists of Nat, whose `cons` case guards its Nat
field and has a hypothesis for its tail only. -/

attribute [local instance] termEq clauseEq

inductive Sym where
  | zero | succ | tt | ff | nil | cons | isNat | isBool | isList | allData | isPred | reachable | defined | allNat | ha
  | tag (tag : P1.Tag)
  deriving DecidableEq, Repr

def vocab : P1.Vocabulary Sym := ⟨Sym.tag, fun _ _ same => by cases same; rfl⟩

inductive Dom where
  | nat | bool | list
  deriving DecidableEq, Repr

abbrev T := Term Nat Nat Sym
abbrev Clause := HornClause Nat Nat Sym

def rules : List (Rule Dom Sym) :=
  [⟨.nat, .zero, []⟩, ⟨.nat, .succ, [.nat]⟩, ⟨.bool, .tt, []⟩, ⟨.bool, .ff, []⟩, ⟨.list, .nil, []⟩,
    ⟨.list, .cons, [.nat, .list]⟩]
def family : FiniteFamily Dom Sym := ⟨fun rule => rule ∈ rules, [.nat, .bool, .list], fun domain => by cases domain <;> simp⟩
def membership : Dom → Sym
  | .nat => .isNat
  | .bool => .isBool
  | .list => .isList
def signature : SignatureSnapshot Dom Sym :=
  ⟨0, ⟨family, membership, .allData, fun _ => .isPred, [⟨.reachable, 1⟩, ⟨.defined, 1⟩, ⟨.allNat, 1⟩]⟩⟩
def names : Nat → Nat := fun index => 100 + index

theorem listed : ∀ rule ∈ rules, signature.signature.data.definitions rule := fun _ member => member
theorem complete : ∀ rule, signature.signature.data.definitions rule → rule ∈ rules := fun _ member => member
theorem distinct : DistinctNames signature.signature.data.definitions names :=
  DistinctNames.of_injective fun first second same => by simpa [names] using same

def principleNames : Names Nat := ⟨1, 2, fun index => 20 + index⟩
def principleOf (domain : Dom) : Clause := principle .ha signature.naming domain rules principleNames
def guardOf (domain : Dom) (term : T) : T := Elaboration.rangeGuard signature.naming (.data [domain]) term
def k (symbol : Sym) : T := .app symbol []
def atom (symbol : Sym) (args : List T) : T := .app symbol args

def kbClauses : List Clause :=
  [.definite (atom .reachable [k .zero]) [], .definite (atom .reachable [atom .succ [.var 5]]) [atom .reachable [.var 5]],
    .definite (atom .defined [k .tt]) [], .definite (atom .defined [k .ff]) [],
    .definite (atom .allNat [k .nil]) [],
    .definite (atom .allNat [atom .cons [.var 5, .var 6]]) [guardOf .nat (.var 5), atom .allNat [.var 6]],
    principleOf .nat, principleOf .bool, principleOf .list]
def generated : List Clause := signatureClauses signature names rules
def program (clauses : List Clause := kbClauses) : Machine.Program Nat Nat Sym :=
  ⟨clauses.mapIdx (fun index clause => ⟨.lowered index, clause⟩) ++ generated.map (⟨.signature, ·⟩),
    guardSymbol signature⟩

def input (goal : T) (clauses : List Clause := kbClauses) : Admission.Input Dom Nat Nat Sym :=
  ⟨signature, names, rules, listed, complete, distinct, program clauses, fun _ => guardSymbol_iff, [], goal⟩
def universal (domain : Dom) (predicate : Sym) : T := Target.goal signature.naming ⟨9, domain, predicate⟩

def checker (clauses : List Clause := kbClauses) : P1.Checker Nat Nat Sym :=
  ⟨⟨.ha, (program clauses).clauses.map (·.clause)⟩, NafFailure.disabled, none, []⟩

def outcomeOf (goal : T) (clauses : List Clause := kbClauses) : Option (Outcome Nat Nat Sym Unit Unit) :=
  match Induction.check .ha (input goal clauses) with
  | .ready plan => some (plan.run 2000)
  | _ => none

def rulesOf' (goal : T) : Option (List RuleId) := (outcomeOf goal).bind fun outcome => outcome.proof?.map (·.tree.rules)

def encoded (goal : T) (clauses : List Clause := kbClauses) : Option T :=
  (outcomeOf goal clauses).bind fun outcome => outcome.proof?.bind (P1.exportProof vocab (fun _ => .truth))

def accepted (goal : T) (clauses : List Clause := kbClauses) : Bool :=
  match encoded goal clauses with
  | some term => decide (P1.checkProof vocab (checker clauses) [] [] goal term = .accept)
  | none => false

-- The principles are generated from the rules: Bool has two cases without
-- fields; the list's cons case binds a Nat field and a list field, with a
-- hypothesis for the list field only.
#guard match principleOf .bool with
  | .definite _ body => body.reverse.take 2 == [atom .ha [.var 1, k .ff], atom .ha [.var 1, k .tt]]
  | _ => false
#guard match principleOf .list with
  | .definite _ body =>
      body.getLast? == some (.forallVar 20 (.imp (guardOf .nat (.var 20)) (.forallVar 21 (.imp (guardOf .list (.var 21))
        (.imp (atom .ha [.var 1, .var 21]) (atom .ha [.var 1, atom .cons [.var 20, .var 21]]))))))
  | _ => false
-- Each lowers through elaborateClause? with P at .predicate 1.
#guard [Dom.nat, .bool, .list].all fun domain =>
  Elaboration.elaborateClause? .ha signature.naming (ranges domain rules) (rangeOf principleNames)
    (source .ha signature.naming domain rules principleNames) == some (principleOf domain)

-- Each universal is proved by its domain's principle, and the exported Term is
-- accepted by the explicit-proof route, though P0 does not admit the universal.
#guard accepted (universal .nat .reachable)
#guard accepted (universal .bool .defined)
#guard accepted (universal .list .allNat)
#guard [(Dom.nat, Sym.reachable), (.bool, .defined), (.list, .allNat)].all fun (domain, predicate) =>
  match Admission.check .ha (input (universal domain predicate)) with
  | .needsEvidence request _ => request.site == .goal && request.capability == .scopedProof
  | _ => false
-- Bool's proof has its two cases and no hypothesis; the list's cons case
-- opens two fields and uses the hypothesis for the tail, converted.
#guard (rulesOf' (universal .bool .defined)).map (·.count .forallIntro) = some 1
#guard (rulesOf' (universal .list .allNat)).map (·.count .forallIntro) = some 3
#guard (rulesOf' (universal .list .allNat)).map (·.count .converted) = some 2

-- A tampered encoding is no proof.
#guard match encoded (universal .nat .reachable) with
  | some (.app symbol (_ :: rest)) =>
      decide (P1.checkProof vocab checker [] [] (universal .nat .reachable) (.app symbol (.truth :: rest)) = .reject)
  | _ => false
-- Another domain's principle does not apply. A program carrying only Bool's
-- and the list's principles has no plan for a Nat universal, and a tree citing
-- Bool's principle at the Nat focus is rejected.
#guard match Induction.check .ha (input (universal .nat .reachable) (kbClauses.filter (· ≠ principleOf .nat))) with
  | .needsEvidence [.principle] => true
  | _ => false
def tree (goal : T) : Option (P1.Proof Nat Nat Sym) :=
  (outcomeOf goal).bind fun outcome => outcome.proof?.bind fun proof =>
    P1.exportTree (Certificate := Unit) (fun _ => .truth) proof.store (fun _ _ => none) proof.tree
partial def cite (original replacement : Clause) : P1.Proof Nat Nat Sym → P1.Proof Nat Nat Sym
  | .node rule conclusion premises =>
      .node (match rule with
        | .clause clause instantiation => if decide (clause = original) then .clause replacement instantiation else rule
        | other => other) conclusion (premises.map (cite original replacement))
#guard match tree (universal .nat .reachable) with
  | some proof => P1.check checker (fun _ _ _ => false) [] proof &&
      !(P1.check checker (fun _ _ _ => false) [] (cite (principleOf .nat) (principleOf .bool) proof))
  | none => false
-- A step clause guarding its variable atomically at the default D_all range:
-- the case's assumption isNat(n) ∨ false is split at the guard goal, and the
-- exported Term, with its split, is accepted.
def dallStep : Clause := .definite (atom .reachable [atom .succ [.var 5]]) [atom .allData [.var 5], atom .reachable [.var 5]]
def withDall : List Clause := [.definite (atom .reachable [k .zero]) [], dallStep, principleOf .nat]
#guard (outcomeOf (universal .nat .reachable) withDall).map (·.kind) = some .success
#guard accepted (universal .nat .reachable) withDall
-- A property that fails one case is not proved: `defined` has no list cases,
-- `reachable` no Bool cases.
#guard (outcomeOf (universal .list .defined)).map (·.kind) = some .exhausted
#guard (outcomeOf (universal .bool .reachable)).map (·.kind) = some .exhausted

end InductionEncodedTests
