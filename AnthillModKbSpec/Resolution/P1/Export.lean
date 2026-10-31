import AnthillModKbSpec.Resolution.P1.Encoding
import AnthillModKbSpec.Resolution.P0.Admission

/-! # Exporting machine proofs as checked terms (S08)

`exportTree` turns a completed machine tree into a supplied proof: every
node's goal and parameters are read through the final store, and each NAF
certificate becomes its evidence term. A tree that still holds a reference to
a delayed goal is an unresolved hole: it exports nothing (`exportTree_refs`).

For a Ready P0 plan the export is checked against the input's own effective
program, so its guard premises are checked against the generated signature
clauses, not against the plan's guard facts. Each guard fact of the plan
becomes a checked membership node (`Plan.membership`), whose procedure is the
exact guard decision of S07 and whose soundness is its derivation from the
generated clauses. NAF evidence is the operand's failure witness, checked
structurally against the plan's ground program and context (`Plan.negation`).
Every successful run of the plan exports a term that this checker accepts
(`exportProof_checked`), and the term reconstructs `Derives` in the input's
effective program (`exportProof_derives`). Export of general S06 runs is
defined, but that it checks is S15/S16's. -/

namespace AnthillModKbSpec.P1

open Machine GroundSearch Admission

variable {Domain Variable Literal Symbol : Type}

/-! ## Witnesses as terms -/

section Witnesses

variable (vocab : Vocabulary Symbol)

mutual
def encodeSuccess : SuccessTree Variable Literal Symbol → Term Variable Literal Symbol
  | .assumption => .app (vocab.symbol .assumed) []
  | .clause body proof => .app (vocab.symbol .byClause) [.app (vocab.symbol .list) body, encodeSuccess proof]
  | .truth => .app (vocab.symbol .trivially) []
  | .conj left right => .app (vocab.symbol .both) [encodeSuccess left, encodeSuccess right]
  | .negation refuted => .app (vocab.symbol .refutes) [encodeFailure refuted]

def encodeFailure : FailureTree Variable Literal Symbol → Term Variable Literal Symbol
  | .atom bodies => .app (vocab.symbol .failsAtom) [.app (vocab.symbol .list) (encodeFailures bodies)]
  | .falsity => .app (vocab.symbol .failsFalsity) []
  | .conjLeft refuted => .app (vocab.symbol .failsLeft) [encodeFailure refuted]
  | .conjRight refuted => .app (vocab.symbol .failsRight) [encodeFailure refuted]
  | .negation proof => .app (vocab.symbol .failsNegation) [encodeSuccess proof]

def encodeFailures : FailureList Variable Literal Symbol → List (Term Variable Literal Symbol)
  | .nil => []
  | .cons head tail => encodeFailure head :: encodeFailures tail
end

variable [DecidableEq Symbol]

mutual
def decodeSuccess : Term Variable Literal Symbol → Option (SuccessTree Variable Literal Symbol)
  | .app symbol args =>
      match vocab.tag? symbol, args with
      | some .assumed, [] => some .assumption
      | some .byClause, [.app list body, proof] =>
          if list = vocab.symbol .list then (decodeSuccess proof).map (.clause body) else none
      | some .trivially, [] => some .truth
      | some .both, [left, right] =>
          match decodeSuccess left, decodeSuccess right with
          | some first, some second => some (.conj first second)
          | _, _ => none
      | some .refutes, [refuted] => (decodeFailure refuted).map .negation
      | _, _ => none
  | _ => none

def decodeFailure : Term Variable Literal Symbol → Option (FailureTree Variable Literal Symbol)
  | .app symbol args =>
      match vocab.tag? symbol, args with
      | some .failsAtom, [.app list bodies] =>
          if list = vocab.symbol .list then (decodeFailures bodies).map .atom else none
      | some .failsFalsity, [] => some .falsity
      | some .failsLeft, [refuted] => (decodeFailure refuted).map .conjLeft
      | some .failsRight, [refuted] => (decodeFailure refuted).map .conjRight
      | some .failsNegation, [proof] => (decodeSuccess proof).map .negation
      | _, _ => none
  | _ => none

def decodeFailures : List (Term Variable Literal Symbol) → Option (FailureList Variable Literal Symbol)
  | [] => some .nil
  | term :: rest =>
      match decodeFailure term, decodeFailures rest with
      | some head, some tail => some (.cons head tail)
      | _, _ => none
end

mutual
theorem decodeSuccess_encodeSuccess : ∀ tree : SuccessTree Variable Literal Symbol,
    decodeSuccess vocab (encodeSuccess vocab tree) = some tree
  | .assumption => by simp [encodeSuccess, decodeSuccess, Vocabulary.tag?_symbol]
  | .clause body proof => by
      simp [encodeSuccess, decodeSuccess, Vocabulary.tag?_symbol, decodeSuccess_encodeSuccess proof]
  | .truth => by simp [encodeSuccess, decodeSuccess, Vocabulary.tag?_symbol]
  | .conj left right => by
      simp [encodeSuccess, decodeSuccess, Vocabulary.tag?_symbol, decodeSuccess_encodeSuccess left,
        decodeSuccess_encodeSuccess right]
  | .negation refuted => by
      simp [encodeSuccess, decodeSuccess, Vocabulary.tag?_symbol, decodeFailure_encodeFailure refuted]

theorem decodeFailure_encodeFailure : ∀ tree : FailureTree Variable Literal Symbol,
    decodeFailure vocab (encodeFailure vocab tree) = some tree
  | .atom bodies => by
      simp [encodeFailure, decodeFailure, Vocabulary.tag?_symbol, decodeFailures_encodeFailures bodies]
  | .falsity => by simp [encodeFailure, decodeFailure, Vocabulary.tag?_symbol]
  | .conjLeft refuted => by
      simp [encodeFailure, decodeFailure, Vocabulary.tag?_symbol, decodeFailure_encodeFailure refuted]
  | .conjRight refuted => by
      simp [encodeFailure, decodeFailure, Vocabulary.tag?_symbol, decodeFailure_encodeFailure refuted]
  | .negation proof => by
      simp [encodeFailure, decodeFailure, Vocabulary.tag?_symbol, decodeSuccess_encodeSuccess proof]

theorem decodeFailures_encodeFailures : ∀ trees : FailureList Variable Literal Symbol,
    decodeFailures vocab (encodeFailures vocab trees) = some trees
  | .nil => rfl
  | .cons head tail => by
      simp [encodeFailures, decodeFailures, decodeFailure_encodeFailure head, decodeFailures_encodeFailures tail]
end

end Witnesses

/-! ## Exporting machine trees -/

section Export

variable {Certificate : Type} [DecidableEq Variable] [FreshNames Variable]

/-- A machine rule as a supplied rule, its terms read through the store. An
existential elimination records the opened body its second premise assumes,
and exports nothing if that premise assumes anything else. A derived rule's
closed-world evidence travels as its last parameter. -/
def exportRule (evidence : Certificate → Term Variable Literal Symbol) (store : Store Variable Literal Symbol) :
    RuleApp Variable Literal Symbol Certificate → List (Premise Variable Literal Symbol) →
      Option (Rule Variable Literal Symbol)
  | .assumption, _ => some .assumption
  | .truth, _ => some .truth
  | .conjIntro, _ => some .conjIntro
  | .conjLeft, _ => some .conjLeft
  | .conjRight, _ => some .conjRight
  | .disjLeft, _ => some .disjLeft
  | .disjRight, _ => some .disjRight
  | .disjElim, _ => some .disjElim
  | .impIntro, _ => some .impIntro
  | .impElim, _ => some .impElim
  | .falsityElim, _ => some .falsityElim
  | .forallIntro eigen, _ => some (.forallIntro eigen)
  | .forallElim witness, _ => some (.forallElim (store.resolve witness))
  | .existsIntro witness, _ => some (.existsIntro (store.resolve witness))
  | .existsElim eigen, premises =>
      match premises with
      | [_, second] =>
          match second.discharge.assumptions with
          | [opened] => some (.existsElim eigen (store.resolve opened))
          | _ => none
      | _ => none
  | .clause clause instantiation, _ =>
      some (.clause clause (instantiation.map fun pair => (pair.1, store.resolve pair.2)))
  | .goalClause clause instantiation, _ =>
      some (.goalClause clause (instantiation.map fun pair => (pair.1, store.resolve pair.2)))
  | .defaultNegIntro certificate, _ => some (.defaultNegIntro (evidence certificate))
  | .hoApplyIntro, _ => some .hoApplyIntro
  | .hoApplyElim, _ => some .hoApplyElim
  | .equalRefl, _ => some .equalRefl
  | .equalSymm, _ => some .equalSymm
  | .equalTrans, _ => some .equalTrans
  | .equalSubst name template, _ => some (.equalSubst name (store.resolve template))
  | .extension name parameters closedWorld, _ =>
      some (.extension name (parameters.map store.resolve ++ (closedWorld.map fun found => evidence found.certificate).toList))

mutual
/-- A machine tree as a supplied proof, read through the store. `replace` may
stand in for a node by a checked node of its own; a reference to a delayed
goal, or a rule that does not export, exports nothing. -/
def exportTree (evidence : Certificate → Term Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (replace : RuleApp Variable Literal Symbol Certificate → Formula Variable Literal Symbol →
      Option (Proof Variable Literal Symbol)) :
    ProofTree Variable Literal Symbol Certificate → Option (Proof Variable Literal Symbol)
  | .node rule obligation premises subproofs =>
      match replace rule (store.resolve obligation.goal) with
      | some proof => some proof
      | none =>
          match exportRule evidence store rule premises, exportTrees evidence store replace subproofs with
          | some exported, some children => some (.node exported (store.resolve obligation.goal) children)
          | _, _ => none
  | .deferred _ _ => none

def exportTrees (evidence : Certificate → Term Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (replace : RuleApp Variable Literal Symbol Certificate → Formula Variable Literal Symbol →
      Option (Proof Variable Literal Symbol)) :
    List (ProofTree Variable Literal Symbol Certificate) → Option (List (Proof Variable Literal Symbol))
  | [] => some []
  | tree :: rest =>
      match exportTree evidence store replace tree, exportTrees evidence store replace rest with
      | some proof, some proofs => some (proof :: proofs)
      | _, _ => none
end

mutual
/-- `exportTree_refs`: without replacement, a tree that exports holds no
reference to a delayed goal. -/
theorem exportTree_refs (evidence : Certificate → Term Variable Literal Symbol) (store : Store Variable Literal Symbol) :
    ∀ (tree : ProofTree Variable Literal Symbol Certificate) {proof},
      exportTree evidence store (fun _ _ => none) tree = some proof → tree.refs = []
  | .node rule obligation premises subproofs, proof, exported => by
      simp only [exportTree] at exported
      split at exported
      · rename_i exportedRule children _ exportedChildren
        simp only [ProofTree.refs]
        exact exportTrees_refs evidence store subproofs exportedChildren
      · cases exported
  | .deferred _ _, _, exported => by simp [exportTree] at exported

theorem exportTrees_refs (evidence : Certificate → Term Variable Literal Symbol) (store : Store Variable Literal Symbol) :
    ∀ (trees : List (ProofTree Variable Literal Symbol Certificate)) {proofs},
      exportTrees evidence store (fun _ _ => none) trees = some proofs → ProofTree.refsOf trees = []
  | [], _, _ => rfl
  | tree :: rest, proofs, exported => by
      simp only [exportTrees] at exported
      split at exported
      · rename_i proof children first others
        simp only [ProofTree.refsOf, exportTree_refs evidence store tree first,
          exportTrees_refs evidence store rest others, List.append_nil]
      · cases exported
end

/-- A completed run as a supplied proof term, read through its final store. -/
def exportProof (vocab : Vocabulary Symbol) (evidence : Certificate → Term Variable Literal Symbol)
    {Snapshot : Type} (proof : CompletedProof Variable Literal Symbol Certificate Snapshot) :
    Option (Term Variable Literal Symbol) :=
  (exportTree evidence proof.store (fun _ _ => none) proof.tree).map (encode vocab)

end Export

end AnthillModKbSpec.P1

namespace AnthillModKbSpec.Admission

open Machine GroundSearch P1

variable {Domain Variable Literal Symbol : Type}

/-! ## Checking a P0 plan's export -/

section Plans

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable]
  {hoApplySymbol : Symbol} (vocab : Vocabulary Symbol) (plan : Plan Domain Variable Literal Symbol hoApplySymbol)

attribute [local instance] termEq

/-- What a plan's export is checked against: the input's effective program,
generated signature clauses included. -/
def Plan.snapshot : Snapshot Variable Literal Symbol := ⟨hoApplySymbol, plan.input.program.clauses.map ProgramClause.clause⟩

/-- The NAF provider of a plan's export: complete failure in the plan's ground
program, under exactly the snapshot's KB and the plan's context. -/
def Plan.failure : NafFailure Variable Literal Symbol := fun symbol kb context goal =>
  symbol = hoApplySymbol ∧ kb = plan.snapshot.kb ∧ context = plan.ground.context.assumptions ∧
    Fails plan.ground.program plan.ground.context goal

/-- NAF evidence of a plan: a failure witness, checked structurally against the
plan's ground program, under the plan's context only. -/
def Plan.negation : NafCheck plan.snapshot plan.failure where
  check context operand evidence :=
    decide (context = plan.ground.context.assumptions) &&
      match decodeFailure vocab evidence with
      | some tree => checkFailure hoApplySymbol plan.ground.program.clauses context operand tree
      | none => false
  sound context operand evidence accepted := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
    obtain ⟨rfl, found⟩ := accepted
    split at found
    · exact ⟨rfl, rfl, rfl, checkFailure_sound (program := plan.ground.program) (context := plan.ground.context) _ _ found⟩
    · cases found

/-- The checked membership node: a guard atom with no premises, decided by the
exact guard decision under the node's context, and derivable from the
generated signature clauses the program carries. -/
def Plan.membership : RuleCheck plan.snapshot plan.failure where
  name := vocab.symbol .membership
  discharges _ _ _ := []
  check context conclusion parameters premises :=
    decide (parameters = []) && decide (premises = []) &&
      decideGuard plan.input.signature plan.input.rules context conclusion
  sound context conclusion parameters premises accepted _ := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
    have derived := decideGuard_derives (hoApplySymbol := hoApplySymbol) (names := plan.input.names)
      (naf := NafFailure.disabled) plan.input.listed plan.input.complete plan.input.distinct accepted.2
    refine derived.mono (fun clause inside => ?_) (fun _ _ none => none.elim)
    obtain ⟨entry, member, same⟩ := signatureKb_carried plan.admits.generated inside
    exact List.mem_map.mpr ⟨entry, member, same⟩

/-- The checker for a plan's export. -/
def Plan.checker : Checker Variable Literal Symbol :=
  ⟨plan.snapshot, plan.failure, some (plan.negation vocab), [plan.membership vocab]⟩

/-- A P0 certificate's evidence: its failure witness as a term. -/
def witnessTerm (certificate : P0.Certificate Variable Literal Symbol) : Term Variable Literal Symbol :=
  match certificate.witness.get with
  | some tree => encodeFailure vocab tree
  | none => .falsity

/-- A guard fact of the plan becomes a membership node. -/
def Plan.replace : RuleApp Variable Literal Symbol (P0.Certificate Variable Literal Symbol) → Formula Variable Literal Symbol →
    Option (Proof Variable Literal Symbol)
  | .clause (.definite (.app symbol _) []) [], goal =>
      if plan.input.guard symbol then some (.node (.extension (vocab.symbol .membership) []) goal []) else none
  | _, _ => none

/-- A successful run of the plan as a supplied proof term. -/
def Plan.exportProof
    (proof : CompletedProof Variable Literal Symbol (P0.Certificate Variable Literal Symbol) (Input Domain Variable Literal Symbol)) :
    Option (Term Variable Literal Symbol) :=
  (exportTree (witnessTerm vocab) proof.store (plan.replace vocab) proof.tree).map (encode vocab)

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem _root_.AnthillModKbSpec.Machine.Scope.enter_empty (scope : Scope Variable Literal Symbol) : scope.enter {} = scope := by
  cases scope; simp [Scope.enter]

variable {vocab plan}

omit [FreshNames Variable] in
theorem Plan.replace_none {head : Term Variable Literal Symbol} {body : List (Term Variable Literal Symbol)}
    {goal : Formula Variable Literal Symbol}
    (plain : ∀ symbol args, head = .app symbol args → plan.input.guard symbol = false) :
    plan.replace vocab (.clause (.definite head body) []) goal = none := by
  cases head with
  | app symbol args =>
      cases body with
      | nil => simp [Plan.replace, plain symbol args rfl]
      | cons _ _ => simp [Plan.replace]
  | _ => simp [Plan.replace]

omit [FreshNames Variable] in
theorem Plan.rule?_membership :
    (plan.checker vocab).rule? (vocab.symbol .membership) = some (plan.membership vocab) := by
  simp [Checker.rule?, Plan.checker, Plan.membership]

/-- Every tree a plan's run builds exports, through the empty store, to a tree
valid against the plan's checker under the input's context, with the tree's
goal as its conclusion. -/
theorem Plan.export_valid {tree : ProofTree Variable Literal Symbol (P0.Certificate Variable Literal Symbol)}
    (built : P0.Built plan.ground tree) :
    tree.Coherent → tree.obligation.scope = plan.ground.scope →
      ∃ proof, exportTree (witnessTerm vocab) Store.empty (plan.replace vocab) tree = some proof ∧
        proof.conclusion = tree.obligation.goal ∧
        Valid (plan.checker vocab) (Resolves vocab (plan.checker vocab) []) plan.input.context proof := by
  have context : plan.ground.context.assumptions = plan.input.context := plan.admits.context
  induction built with
  | @node rule obligation premises subproofs step children ih =>
      intro coherent scope
      simp only [ProofTree.obligation] at scope ⊢
      cases coherent with
      | node coherentChildren =>
      cases step with
      | @truth _ goal =>
          cases coherentChildren
          refine ⟨.node .truth obligation.goal [], ?_, rfl, ?_⟩
          · simp [exportTree, exportTrees, exportRule, Plan.replace]
          · rw [goal]; exact .node .truth (by simp)
      | @conjIntro _ left right goal =>
          obtain _ | ⟨firstOpened, firstCoherent, rest⟩ := coherentChildren
          obtain _ | ⟨secondOpened, secondCoherent, last⟩ := rest
          cases last
          rename_i first second
          have firstScope : first.obligation.scope = plan.ground.scope := by
            rw [firstOpened]; simp [Obligation.premise, Scope.enter_empty, scope]
          have secondScope : second.obligation.scope = plan.ground.scope := by
            rw [secondOpened]; simp [Obligation.premise, Scope.enter_empty, scope]
          obtain ⟨firstProof, firstExport, firstGoal, firstValid⟩ := ih first (by simp) firstCoherent firstScope
          obtain ⟨secondProof, secondExport, secondGoal, secondValid⟩ :=
            ih second (by simp) secondCoherent secondScope
          rw [firstOpened] at firstGoal
          rw [secondOpened] at secondGoal
          refine ⟨.node .conjIntro obligation.goal [firstProof, secondProof], ?_, rfl, ?_⟩
          · simp [exportTree, exportTrees, exportRule, Plan.replace, firstExport, secondExport]
          · rw [goal]
            refine .node (contexts := [[], []]) ?_ (by simpa using ⟨firstValid, secondValid⟩)
            simp only [List.map_cons, List.map_nil, firstGoal, secondGoal, Obligation.premise]
            exact .conjIntro
      | assumption member =>
          cases coherentChildren
          refine ⟨.node .assumption obligation.goal [], ?_, rfl, ?_⟩
          · simp [exportTree, exportTrees, exportRule, Plan.replace]
          · exact .node (.assumption (context ▸ member)) (by simp)
      | @clause head body _ member goal =>
          obtain _ | ⟨opened, bodyCoherent, rest⟩ := coherentChildren
          cases rest
          rename_i premise
          have planned : HornClause.definite head body ∈ plan.input.planClauses := by
            rw [← plan.ground.listed, plan.admits.entries, plan.admits.facts] at member
            exact member
          rcases mem_planClauses.mp planned with ⟨pair, pairMember, pairClause⟩ | ⟨atom, factMember, factClause⟩
          · -- A KB clause: checked as a clause step of the effective program.
            obtain ⟨_, _, plain⟩ := plan.admits.classes.clauses pair pairMember
            have notGuard : ∀ symbol args, head = .app symbol args → plan.input.guard symbol = false :=
              fun symbol args same => plain head body pairClause symbol args same
            have premiseScope : premise.obligation.scope = plan.ground.scope := by
              rw [opened]; simp [Obligation.premise, Scope.enter_empty, scope]
            obtain ⟨bodyProof, bodyExport, bodyGoal, bodyValid⟩ := ih premise (by simp) bodyCoherent premiseScope
            rw [opened] at bodyGoal
            have listed : HornClause.definite head body ∈ plan.snapshot.clauses := by
              obtain ⟨entry, entryMember, entryEq⟩ :=
                List.mem_filterMap.mp (show pair ∈ plan.input.kbClauses from pairMember)
              refine List.mem_map.mpr ⟨entry, entryMember, ?_⟩
              revert entryEq
              cases entry.source <;> simp
              intro same; rw [← pairClause, ← same]
            refine ⟨.node (.clause (.definite head body) []) obligation.goal [bodyProof], ?_, rfl, ?_⟩
            · simp [exportTree, exportTrees, exportRule, Plan.replace_none notGuard, bodyExport]
            · refine .node (contexts := [[]]) ?_ (by simpa using bodyValid)
              simp only [List.map_cons, List.map_nil, bodyGoal, Obligation.premise]
              rw [goal]
              exact .clause listed (Substitutes.identity head) (Substitutes.identity _)
          · -- A guard fact: a checked membership node.
            cases factClause
            have inFacts : head ∈ plan.input.guardFacts := by
              first
                | exact factMember
                | (rw [plan.admits.facts] at factMember; exact factMember)
            have decided := (mem_guardFacts inFacts).2
            have guarded : ∃ symbol args, head = .app symbol args ∧ plan.input.guard symbol = true := by
              have inside := (List.mem_filter.mp (List.mem_filter.mp (List.mem_eraseDups.mp inFacts)).1).2
              cases head with
              | app symbol args => exact ⟨symbol, args, rfl, inside⟩
              | _ => simp at inside
            obtain ⟨symbol, args, rfl, guard⟩ := guarded
            refine ⟨.node (.extension (vocab.symbol .membership) []) obligation.goal [], ?_, rfl, ?_⟩
            · simp [exportTree, Plan.replace, guard]
            · refine .node (contexts := []) ?_ (by simp)
              rw [goal]
              refine .extension Plan.rule?_membership ?_ rfl
              simp [Plan.membership, decided]
      | @negation certificate _ goal certified =>
          cases coherentChildren
          have failed := certified.fails
          have closed : certificate.operand.freeVars = [] := (fails_isGoal failed).closed
          obtain ⟨clauses, assumptions, checked⟩ := certified
          simp only [P0.NegativeCertificate.check] at checked
          split at checked
          · rename_i witness witnessed
            refine ⟨.node (.defaultNegIntro (witnessTerm vocab certificate)) obligation.goal [], ?_, rfl, ?_⟩
            · simp [exportTree, exportTrees, exportRule, Plan.replace]
            · rw [goal]
              refine .node (contexts := []) (.defaultNegIntro closed rfl ?_) (by simp)
              simp only [Plan.negation, witnessTerm, witnessed, decodeFailure_encodeFailure, Bool.and_eq_true,
                decide_eq_true_eq]
              refine ⟨context.symm, ?_⟩
              rw [← context, ← clauses, ← assumptions]
              exact checked
          · cases checked

/-- `exportProof_checked`: every successful run of a Ready plan exports a term
the plan's checker accepts, for the input's context and goal. -/
theorem Plan.exportProof_checked {fuel : Nat}
    {proof : CompletedProof Variable Literal Symbol (P0.Certificate Variable Literal Symbol) (Input Domain Variable Literal Symbol)}
    {resume : State Variable Literal Symbol (P0.Certificate Variable Literal Symbol) (Input Domain Variable Literal Symbol)}
    (ran : plan.run fuel = .success proof resume) :
    ∃ term, plan.exportProof vocab proof = some term ∧
      checkProof vocab (plan.checker vocab) [] plan.input.context plan.input.goal term = .accept := by
  obtain ⟨success, _, _⟩ := P0.run_correct plan.ground plan.input fuel
  obtain ⟨_, proves, _, _, _, built, emptied, coherent⟩ := success proof resume ran
  obtain ⟨exported, exportedEq, proves', valid⟩ := Plan.export_valid (vocab := vocab) built coherent (by rw [proves])
  refine ⟨encode vocab exported, by simp [Plan.exportProof, emptied, exportedEq], ?_⟩
  refine (checkProof_accept_iff vocab (plan.checker vocab)).mpr ⟨exported, decode_encode vocab exported, ?_, valid⟩
  rw [proves', proves, plan.admits.goal]

/-- `exportProof_derives`: the exported term reconstructs `Derives` for the
input's goal and context in the input's effective program, with the plan's
ground failure provider. -/
theorem Plan.exportProof_derives (vocab : Vocabulary Symbol) {fuel : Nat}
    {proof : CompletedProof Variable Literal Symbol (P0.Certificate Variable Literal Symbol) (Input Domain Variable Literal Symbol)}
    {resume : State Variable Literal Symbol (P0.Certificate Variable Literal Symbol) (Input Domain Variable Literal Symbol)}
    (ran : plan.run fuel = .success proof resume) :
    Derives hoApplySymbol plan.snapshot.kb plan.input.context plan.input.goal plan.failure := by
  obtain ⟨term, _, accepted⟩ := Plan.exportProof_checked (vocab := vocab) ran
  exact checked_toDerives vocab (plan.checker vocab) ((checkProof_accept_iff vocab (plan.checker vocab)).mp accepted)

end Plans

end AnthillModKbSpec.Admission
