import AnthillModKbSpec.Resolution.P0.Strategy
import AnthillModKbSpec.Resolution.P0.CompletedGround

namespace AnthillModKbSpec.P0

open Machine GroundSearch

/-! # Total, correct P0 runs (S07)

A P0 run is the shared machine (`Machine.step`, `Machine.run`) with the P0
command set (`Ground.strategy`). For every admitted input:

* every state of the run keeps the empty store, records no gap, and holds only
  ground obligations of at most the root's level (`Shape`);
* every proved subtree proves a goal with a success certificate, and every NAF
  node in it holds a valid negative certificate (`Shape`, `TreeOk`);
* if the root goal has a success certificate, a live alternative remains on
  the current branch or among the saved choice points, segment by segment
  through the NAF barriers (`Complete`, `Covers`);
* each transition decreases a measure computed from the rank (`measure`).

So a run finishes within `measure` steps (`run_total`), success carries
`GroundSearch.Succeeds` and exhaustion `GroundSearch.Fails` for the original
program, context, and goal (`run_correct`), and no run is ever `unknown`. -/

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  [FreshNames Variable] {hoApplySymbol : Symbol}

abbrev Certificate (Variable Literal Symbol : Type) := NegativeCertificate Variable Literal Symbol

/-! ## Candidates of an atom -/

section Candidates

variable {ground : Ground Variable Literal Symbol hoApplySymbol}

theorem mem_atomCandidates {entries : List (ProgramClause Variable Literal Symbol)} {context : ProofContext Variable Literal Symbol}
    {goal : Term Variable Literal Symbol} {expansion : Expansion Variable Literal Symbol (Certificate Variable Literal Symbol)}
    (member : expansion ∈ atomCandidates entries context goal) :
    (expansion = Expansion.assumption [] ∧ goal ∈ context) ∨
      ∃ body, expansion = Expansion.clause goal body [] ∧ ∃ entry ∈ entries, entry.clause = .definite goal body := by
  simp only [atomCandidates, List.mem_append, List.mem_filterMap] at member
  rcases member with ⟨assumption, inside, found⟩ | ⟨entry, inside, found⟩
  · split at found
    · rename_i same
      cases found
      exact .inl ⟨rfl, identical_eq _ _ same ▸ inside⟩
    · cases found
  · split at found
    · rename_i head body definite
      split at found
      · rename_i same
        cases found
        rw [identical_eq _ _ same] at definite
        exact .inr ⟨body, by rw [identical_eq _ _ same], entry, inside, definite⟩
      · cases found
    · cases found

omit [DecidableEq Literal] [DecidableEq Symbol] in
/-- The one premise of a clause candidate is its body. -/
theorem clause_premises (head : Term Variable Literal Symbol) (body : List (Term Variable Literal Symbol)) :
    (Expansion.clause (Certificate := Certificate Variable Literal Symbol) head body []).premises =
      [{ goal := Term.conjunction body }] := by
  simp [Expansion.clause, instantiate_rename_nil]

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem Ground.mem_clauses {ground : Ground Variable Literal Symbol hoApplySymbol}
    {entry : ProgramClause Variable Literal Symbol} (member : entry ∈ ground.entries) :
    entry.clause ∈ ground.program.clauses := by
  rw [← ground.listed]; exact List.mem_map_of_mem member

/-- Every success certificate of an atom is found among its candidates: the
assumption it uses or the clause it selects. -/
theorem atomCandidates_complete {symbol : Symbol} {args : List (Term Variable Literal Symbol)}
    (proof : Succeeds ground.program ground.context (.app symbol args)) :
    ∃ expansion ∈ atomCandidates ground.entries ground.context.assumptions (.app symbol args),
      ∀ premise ∈ expansion.premises, Succeeds ground.program ground.context premise.goal := by
  cases proof with
  | assumption _ member =>
      refine ⟨Expansion.assumption [], ?_, by simp [Expansion.assumption]⟩
      simp only [atomCandidates, List.mem_append, List.mem_filterMap]
      exact .inl ⟨_, member, by simp [identical_self]⟩
  | @clause _ _ body _ member bodyProof =>
      have listed : HornClause.definite (.app symbol args) body ∈ ground.entries.map ProgramClause.clause := by
        rw [ground.listed]; exact member
      obtain ⟨entry, inside, same⟩ := List.mem_map.mp listed
      refine ⟨Expansion.clause (.app symbol args) body [], ?_, ?_⟩
      · simp only [atomCandidates, List.mem_append, List.mem_filterMap]
        exact .inr ⟨entry, inside, by simp [same, identical_self]⟩
      · rw [clause_premises]
        intro premise member
        simp only [List.mem_singleton] at member
        subst member
        exact bodyProof

end Candidates

/-! ## The measure

`budget n goal after` bounds the steps a branch focused on `goal` takes before
its alternatives, including those of the subgoals it selects, are exhausted,
when each success of `goal` continues at a cost of `after`. An atom's budget
sums one continuation per candidate: the depth-first search repeats the
continuation for each success. The level bound `n` decreases into clause
bodies; under the rank every bound at least the goal's level gives the same
budget (`budget_stable`). -/

/-- The cost of proving `premises` in order and then continuing at `after`. -/
def pendingWith (cost : Term Variable Literal Symbol → Nat → Nat) (premises : List (Premise Variable Literal Symbol))
    (after : Nat) : Nat :=
  premises.foldr (fun premise rest => cost premise.goal (rest + 1)) after

def budget (ground : Ground Variable Literal Symbol hoApplySymbol) : Nat → Term Variable Literal Symbol → Nat → Nat
  | _, .truth, after => after + 1
  | _, .falsity, _ => 2
  | n, .conj left right, after => budget ground n left (budget ground n right (after + 1) + 1) + 1
  | n, .defaultNeg operand, after => budget ground n operand 2 + after + 4
  | 0, .app _ _, _ => 0
  | n + 1, .app symbol args, after =>
      ((atomCandidates ground.entries ground.context.assumptions (.app symbol args)).map fun expansion =>
        pendingWith (fun goal rest => budget ground n goal rest) expansion.premises after + 2).sum + 2
  | _, _, _ => 0
termination_by n goal => (n, sizeOf goal)

section Budget

variable {ground : Ground Variable Literal Symbol hoApplySymbol}

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem pendingWith_congr {cost other : Term Variable Literal Symbol → Nat → Nat}
    {premises : List (Premise Variable Literal Symbol)}
    (same : ∀ premise ∈ premises, ∀ rest, cost premise.goal rest = other premise.goal rest) (after : Nat) :
    pendingWith cost premises after = pendingWith other premises after := by
  induction premises with
  | nil => rfl
  | cons premise rest ih =>
      simp only [pendingWith, List.foldr_cons] at ih ⊢
      rw [ih fun other member => same other (List.mem_cons_of_mem _ member), same premise List.mem_cons_self]

/-- Under the rank, any level bound at least the goal's level gives the same
budget. -/
theorem budget_stable : ∀ (n : Nat) (goal : Term Variable Literal Symbol) (after : Nat),
    level ground.rank goal ≤ n → budget ground (n + 1) goal after = budget ground n goal after
  | n, .conj left right, after, below => by
      simp only [level_conj, Nat.max_le] at below
      rw [budget, budget, budget_stable n left _ below.1, budget_stable n right _ below.2]
  | n, .defaultNeg operand, after, below => by
      rw [budget, budget, budget_stable n operand _ below]
  | 0, .app symbol args, _, below => by simp at below
  | m + 1, .app symbol args, after, below => by
      rw [budget, budget]
      congr 2
      apply List.map_congr_left
      intro expansion member
      congr 1
      apply pendingWith_congr
      intro premise inside rest
      rcases mem_atomCandidates member with ⟨rfl, _⟩ | ⟨body, rfl, entry, entryMember, definite⟩
      · simp [Expansion.assumption] at inside
      · rw [clause_premises] at inside
        simp only [List.mem_singleton] at inside
        subst inside
        have bodyBelow := ground.ranked.level_body (definite ▸ Ground.mem_clauses entryMember)
        rw [level_app] at below
        dsimp only
        exact budget_stable m _ rest (by omega)
  | _, .truth, _, _ => by rw [budget, budget]
  | _, .falsity, _, _ => by rw [budget, budget]
  | _, .var _, _, _ => by simp [budget]
  | _, .lit _, _, _ => by simp [budget]
  | _, .disj _ _, _, _ => by simp [budget]
  | _, .imp _ _, _, _ => by simp [budget]
  | _, .forallVar _ _, _, _ => by simp [budget]
  | _, .existsVar _ _, _, _ => by simp [budget]
  | _, .dictionaryCall _ _ _ _, _, _ => by simp [budget]
  | _, .equal _ _, _, _ => by simp [budget]
termination_by n goal => (n, sizeOf goal)

theorem budget_stable_le {n m : Nat} (le : n ≤ m) {goal : Term Variable Literal Symbol} (after : Nat)
    (below : level ground.rank goal ≤ n) : budget ground m goal after = budget ground n goal after := by
  induction le with
  | refl => rfl
  | step le ih => rw [budget_stable _ _ _ (Nat.le_trans below le), ih]

end Budget

/-! ## The state measure -/

section Measure

variable (ground : Ground Variable Literal Symbol hoApplySymbol) (bound : Nat)

/-- The cost of returning a proof to a continuation stack. A NAF entry ends the
branch: it fails, discarding the operand's alternatives. -/
def proceed : List (Continuation Variable Literal Symbol (Certificate Variable Literal Symbol)) → Nat
  | [] => 1
  | .frame frame :: rest => pendingWith (budget ground bound) frame.pending (proceed rest) + 1
  | .woken _ _ _ :: rest => proceed rest + 1
  | .negation _ _ _ :: _ => 2

def focusCost : Focus Variable Literal Symbol (Certificate Variable Literal Symbol) →
    List (Continuation Variable Literal Symbol (Certificate Variable Literal Symbol)) → Nat
  | .solve obligation, frames => budget ground bound obligation.goal (proceed ground bound frames)
  | .proved _, frames => proceed ground bound frames
  | .failed, _ => 1

/-- A saved choice point: each alternative started under its saved continuations. -/
def pointCost (point : ChoicePoint Variable Literal Symbol (Certificate Variable Literal Symbol)) : Nat :=
  (point.alternatives.map fun expansion =>
    pendingWith (budget ground bound) expansion.premises (proceed ground bound point.frames) + 2).sum + 1

/-- The measure of a state: its branch and every saved alternative, at the
root's level. Each P0 transition decreases it. -/
def measure {Snapshot : Type} (state : State Variable Literal Symbol (Certificate Variable Literal Symbol) Snapshot) : Nat :=
  focusCost ground (level ground.rank ground.goal) state.focus state.frames +
    (state.choices.map (pointCost ground (level ground.rank ground.goal))).sum

end Measure

/-! ## The invariant -/

section Invariant

variable (ground : Ground Variable Literal Symbol hoApplySymbol)

/-- A goal of the run: ground, without `ho_apply`, and at most the root's level. -/
structure GoalOk (goal : Term Variable Literal Symbol) : Prop where
  valid : IsGoal hoApplySymbol goal
  ordinary : Ordinary hoApplySymbol goal
  below : level ground.rank goal ≤ level ground.rank ground.goal

def ObligationOk (obligation : Obligation Variable Literal Symbol) : Prop :=
  obligation.scope = ground.scope ∧ GoalOk ground obligation.goal

def PremiseOk (premise : Premise Variable Literal Symbol) : Prop :=
  premise.discharge = {} ∧ GoalOk ground premise.goal

/-- The node holds: success certificates for all premises give one for the
conclusion. -/
def Holds (obligation : Obligation Variable Literal Symbol) (premises : List (Premise Variable Literal Symbol)) : Prop :=
  (∀ premise ∈ premises, Succeeds ground.program ground.context premise.goal) →
    Succeeds ground.program ground.context obligation.goal

/-- The rule application a node of the run records, as S08 checks it: its
rule with its parameters, its obligation's goal, and its premises, against the
run's program and context. -/
inductive NodeOk : RuleApp Variable Literal Symbol (Certificate Variable Literal Symbol) →
    Obligation Variable Literal Symbol → List (Premise Variable Literal Symbol) → Prop where
  | truth (goal : obligation.goal = .truth) : NodeOk .truth obligation []
  | conjIntro (goal : obligation.goal = .conj left right) :
      NodeOk .conjIntro obligation [{ goal := left }, { goal := right }]
  | assumption (member : obligation.goal ∈ ground.context.assumptions) : NodeOk .assumption obligation []
  | clause (member : HornClause.definite head body ∈ ground.program.clauses) (goal : obligation.goal = head) :
      NodeOk (.clause (.definite head body) []) obligation [{ goal := .conjunction body }]
  | negation (goal : obligation.goal = .defaultNeg certificate.operand)
      (valid : certificate.Valid ground.program ground.context) :
      NodeOk (.defaultNegIntro certificate) obligation []

/-- Every node of the tree is a rule application of the run. -/
inductive Built : ProofTree Variable Literal Symbol (Certificate Variable Literal Symbol) → Prop where
  | node (step : NodeOk ground rule obligation premises) (children : ∀ tree ∈ subproofs, Built tree) :
      Built (.node rule obligation premises subproofs)

/-- A finished subtree of the run: no reference, every closed-world node holds
a valid certificate for the run's exact program and context, and every node is
a rule application of the run. -/
def TreeOk (tree : ProofTree Variable Literal Symbol (Certificate Variable Literal Symbol)) : Prop :=
  tree.refs = [] ∧ (∀ evidence ∈ tree.closedWorld, evidence.certificate.Valid ground.program ground.context) ∧
    Built ground tree

structure FrameOk (frame : Frame Variable Literal Symbol (Certificate Variable Literal Symbol)) : Prop where
  parent : ObligationOk ground frame.parent
  premises : ∀ premise ∈ frame.premises, PremiseOk ground premise
  holds : Holds ground frame.parent frame.premises
  proved : ∀ premise ∈ frame.before, Succeeds ground.program ground.context premise.goal
  done : ∀ tree ∈ frame.done, TreeOk ground tree
  plain : frame.rule.closedWorld? = none
  node : NodeOk ground frame.rule frame.parent frame.premises

def ContinuationOk : Continuation Variable Literal Symbol (Certificate Variable Literal Symbol) → Prop
  | .frame frame => FrameOk ground frame
  | .woken _ _ _ => False
  | .negation obligation operand holes =>
      ObligationOk ground obligation ∧ operand.scope = ground.scope ∧ obligation.goal = .defaultNeg operand.goal ∧
        holes = 0

/-- A candidate of the run: no new names or bindings, ground premises, and a
node that holds. -/
structure ExpansionOk (obligation : Obligation Variable Literal Symbol)
    (expansion : Expansion Variable Literal Symbol (Certificate Variable Literal Symbol)) : Prop where
  flexibles : expansion.flexibles = []
  bindings : expansion.bindings = []
  premises : ∀ premise ∈ expansion.premises, PremiseOk ground premise
  holds : Holds ground obligation expansion.premises
  plain : expansion.rule.closedWorld? = none
  node : NodeOk ground expansion.rule obligation expansion.premises

def BarrierOk (point : ChoicePoint Variable Literal Symbol (Certificate Variable Literal Symbol)) : Prop :=
  ∃ certificate : Certificate Variable Literal Symbol, point.alternatives = [Expansion.negation certificate] ∧
    certificate.clauses = ground.program.clauses ∧ certificate.context = ground.context.assumptions ∧
    point.obligation.goal = .defaultNeg certificate.operand ∧
    certificate.witness.get = ground.witness certificate.context certificate.operand

structure PointOk (point : ChoicePoint Variable Literal Symbol (Certificate Variable Literal Symbol)) : Prop where
  store : point.store = Store.empty
  deferred : point.deferred = []
  obligation : ObligationOk ground point.obligation
  frames : ∀ continuation ∈ point.frames, ContinuationOk ground continuation
  alternatives : match point.barrier with
    | none => ∀ expansion ∈ point.alternatives, ExpansionOk ground point.obligation expansion
    | some marks => marks = ⟨0, 0⟩ ∧ BarrierOk ground point

def FocusOk : Focus Variable Literal Symbol (Certificate Variable Literal Symbol) → Prop
  | .solve obligation => ObligationOk ground obligation
  | .proved tree => Succeeds ground.program ground.context tree.obligation.goal ∧ TreeOk ground tree
  | .failed => True

/-- What every state of a P0 run looks like. -/
structure Shape {Snapshot : Type} (state : State Variable Literal Symbol (Certificate Variable Literal Symbol) Snapshot) :
    Prop where
  root : state.root = ⟨ground.scope, ground.goal⟩
  store : state.store = Store.empty
  deferred : state.deferred = []
  gaps : state.gaps = []
  focus : FocusOk ground state.focus
  frames : ∀ continuation ∈ state.frames, ContinuationOk ground continuation
  choices : ∀ point ∈ state.choices, PointOk ground point
  /-- Nothing delays: P0 is ground. -/
  holes : state.nextHole = 0

/-- The goals still to prove on a branch, up to the innermost NAF entry. -/
def segment : List (Continuation Variable Literal Symbol (Certificate Variable Literal Symbol)) →
    List (Term Variable Literal Symbol)
  | [] => []
  | .frame frame :: rest => frame.pending.map Premise.goal ++ segment rest
  | .woken _ _ _ :: rest => segment rest
  | .negation _ _ _ :: _ => []

/-- The goal the innermost segment works for: the innermost NAF operand, or the
root goal. -/
def targetOf : List (Continuation Variable Literal Symbol (Certificate Variable Literal Symbol)) → Term Variable Literal Symbol
  | [] => ground.goal
  | .frame _ :: rest | .woken _ _ _ :: rest => targetOf rest
  | .negation _ operand _ :: _ => operand.goal

/-- The number of NAF entries on a stack: barriers still waiting below it. -/
def entries : List (Continuation Variable Literal Symbol (Certificate Variable Literal Symbol)) → Nat
  | [] => 0
  | .frame _ :: rest | .woken _ _ _ :: rest => entries rest
  | .negation _ _ _ :: rest => entries rest + 1

def Live (goals : List (Term Variable Literal Symbol)) : Prop :=
  ∀ goal ∈ goals, Succeeds ground.program ground.context goal

def BranchLive : Focus Variable Literal Symbol (Certificate Variable Literal Symbol) →
    List (Continuation Variable Literal Symbol (Certificate Variable Literal Symbol)) → Prop
  | .solve obligation, frames => Live ground (obligation.goal :: segment frames)
  | .proved _, frames => Live ground (segment frames)
  | .failed, _ => False

def AltLive (expansion : Expansion Variable Literal Symbol (Certificate Variable Literal Symbol))
    (frames : List (Continuation Variable Literal Symbol (Certificate Variable Literal Symbol))) : Prop :=
  Live ground (expansion.premises.map Premise.goal ++ segment frames)

/-- Completeness of the remaining search, segment by segment. At `depth` NAF
barriers below the current segment, working for `target`: if the target
succeeds, `live` or a saved alternative of the segment is live. A barrier
closes the segment: below it, the next segment's branch is the NAF goal's
continuation, live when the operand fails and the continuation's goals
succeed. -/
def Covers : Nat → Term Variable Literal Symbol → Prop →
    List (ChoicePoint Variable Literal Symbol (Certificate Variable Literal Symbol)) → Prop
  | depth, target, live, [] => depth = 0 ∧ target = ground.goal ∧ (Succeeds ground.program ground.context target → live)
  | depth, target, live, point :: rest =>
      match point.barrier with
      | none => entries point.frames = depth ∧ targetOf ground point.frames = target ∧
          Covers depth target (live ∨ ∃ expansion ∈ point.alternatives, AltLive ground expansion point.frames) rest
      | some _ => ∃ below, depth = below + 1 ∧ entries point.frames = below ∧ point.obligation.goal = .defaultNeg target ∧
          (Succeeds ground.program ground.context target → live) ∧
          Covers below (targetOf ground point.frames) (Fails ground.program ground.context target ∧
            Live ground (segment point.frames)) rest

def Complete {Snapshot : Type} (state : State Variable Literal Symbol (Certificate Variable Literal Symbol) Snapshot) :
    Prop :=
  ∃ depth target, (state.focus ≠ .failed → target = targetOf ground state.frames ∧ entries state.frames = depth) ∧
    Covers ground depth target (BranchLive ground state.focus state.frames) state.choices

/-- The invariant of a P0 run. -/
structure Inv {Snapshot : Type} (state : State Variable Literal Symbol (Certificate Variable Literal Symbol) Snapshot) :
    Prop where
  valid : state.Valid
  shape : Shape ground state
  complete : Complete ground state

end Invariant

/-! ## Lemmas on the invariant -/

section Lemmas

variable {ground : Ground Variable Literal Symbol hoApplySymbol}

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem Covers.mono : ∀ {choices : List (ChoicePoint Variable Literal Symbol (Certificate Variable Literal Symbol))}
    {depth : Nat} {target : Term Variable Literal Symbol} {live other : Prop},
    Covers ground depth target live choices → (live → other) → Covers ground depth target other choices
  | [], _, _, _, _, ⟨zero, root, holds⟩, weaker => ⟨zero, root, fun proof => weaker (holds proof)⟩
  | point :: rest, depth, target, live, other, covers, weaker => by
      unfold Covers at covers ⊢
      split
      · rename_i plain
        rw [plain] at covers
        exact ⟨covers.1, covers.2.1, Covers.mono covers.2.2 fun either => either.imp_left weaker⟩
      · rename_i count barrier
        rw [barrier] at covers
        obtain ⟨below, deeper, frames, negation, holds, rest⟩ := covers
        exact ⟨below, deeper, frames, negation, fun proof => weaker (holds proof), rest⟩

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
/-- A proved NAF operand leaves the next segment covered without its barrier's
continuation: the NAF goal fails, so that continuation is not live. -/
theorem Covers.cut : ∀ {choices : List (ChoicePoint Variable Literal Symbol (Certificate Variable Literal Symbol))}
    {depth : Nat} {target : Term Variable Literal Symbol} {live : Prop},
    Covers ground depth target live choices → 0 < depth → Succeeds ground.program ground.context target →
      ∃ depth target, Covers ground depth target False (cutNegation choices)
  | [], _, _, _, ⟨zero, _, _⟩, positive, _ => by omega
  | point :: rest, depth, target, live, covers, positive, proof => by
      unfold Covers at covers
      unfold cutNegation
      split at covers
      · rename_i plain
        simp only [plain, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        exact Covers.cut covers.2.2 positive proof
      · rename_i count barrier
        simp only [barrier, Option.isSome_some, ↓reduceIte]
        obtain ⟨below, _, _, _, _, rest⟩ := covers
        exact ⟨below, _, rest.mono fun ⟨failed, _⟩ => succeeds_not_fails proof failed⟩

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem GoalOk.closed {goal : Term Variable Literal Symbol} (ok : GoalOk ground goal) : goal.freeVars = [] :=
  ok.valid.closed

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem PremiseOk.closed {premise : Premise Variable Literal Symbol} (ok : PremiseOk ground premise) :
    premise.discharge.rigids = [] ∧ premise.freeVars = [] := by
  obtain ⟨discharge, goal⟩ := ok
  refine ⟨by rw [discharge], ?_⟩
  simp [Premise.freeVars, discharge, goal.closed]

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem ObligationOk.premise {obligation : Obligation Variable Literal Symbol} {premise : Premise Variable Literal Symbol}
    (parent : ObligationOk ground obligation) (ok : PremiseOk ground premise) :
    ObligationOk ground (obligation.premise premise) := by
  obtain ⟨scope, _⟩ := parent
  obtain ⟨discharge, goal⟩ := ok
  refine ⟨?_, goal⟩
  simp only [Obligation.premise, Scope.enter, discharge, scope]
  rfl

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
/-- Entering a ground candidate in the empty store commits without changing it. -/
theorem enter_eq {Snapshot : Type} {state : State Variable Literal Symbol (Certificate Variable Literal Symbol) Snapshot}
    {obligation : Obligation Variable Literal Symbol}
    {expansion : Expansion Variable Literal Symbol (Certificate Variable Literal Symbol)}
    {rest : List (Expansion Variable Literal Symbol (Certificate Variable Literal Symbol))}
    (store : state.store = Store.empty) (scope : obligation.scope = ground.scope)
    (flexibles : expansion.flexibles = []) (bindings : expansion.bindings = [])
    (premises : ∀ premise ∈ expansion.premises, PremiseOk ground premise) :
    state.enter obligation expansion rest =
      { state with
        choices := state.save obligation rest
        store := Store.empty
        focus := (expansion.start obligation state.frames).1
        frames := (expansion.start obligation state.frames).2 } := by
  have committed : state.store.commit obligation expansion.flexibles expansion.rigids expansion.premises
      expansion.bindings = .committed Store.empty [] := by
    rw [store, flexibles, bindings, Expansion.rigids]
    exact Store.commit_ground (by rw [scope]; rfl) fun premise member => (premises premise member).closed
  rw [State.enter_committed committed]
  rfl

omit [FreshNames Variable] in
/-- A started candidate's continuation: its node at once, or its first premise
under a frame for the rest. -/
theorem start_ok {obligation : Obligation Variable Literal Symbol}
    {expansion : Expansion Variable Literal Symbol (Certificate Variable Literal Symbol)}
    {frames : List (Continuation Variable Literal Symbol (Certificate Variable Literal Symbol))}
    (parent : ObligationOk ground obligation) (premises : ∀ premise ∈ expansion.premises, PremiseOk ground premise)
    (holds : Holds ground obligation expansion.premises) (plain : expansion.rule.closedWorld? = none)
    (node : NodeOk ground expansion.rule obligation expansion.premises)
    (framesOk : ∀ continuation ∈ frames, ContinuationOk ground continuation) :
    FocusOk ground (expansion.start obligation frames).1 ∧
      ∀ continuation ∈ (expansion.start obligation frames).2, ContinuationOk ground continuation := by
  unfold Expansion.start
  split
  · rename_i none
    rw [none] at holds node
    refine ⟨⟨holds (fun _ member => by cases member), ?_, ?_, .node node fun _ member => by cases member⟩, framesOk⟩
    · simp [ProofTree.refs, ProofTree.refsOf]
    · simp [ProofTree.closedWorld, ProofTree.closedWorldOf, plain]
  · rename_i premise pending premisesEq
    refine ⟨parent.premise (premises premise (by simp [premisesEq])), fun continuation member => ?_⟩
    rcases List.mem_cons.mp member with rfl | member
    · have samePremises : (Frame.start obligation expansion.rule premise pending).premises = expansion.premises := by
        simp [Frame.start, Frame.premises, premisesEq]
      refine ⟨parent, ?_, ?_, by simp [Frame.start], by simp [Frame.start], plain, ?_⟩
      · rw [samePremises]; exact premises
      · show Holds ground obligation (Frame.start obligation expansion.rule premise pending).premises
        rw [samePremises]; exact holds
      · show NodeOk ground expansion.rule obligation (Frame.start obligation expansion.rule premise pending).premises
        rw [samePremises]; exact node
    · exact framesOk continuation member

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem start_live {obligation : Obligation Variable Literal Symbol}
    {expansion : Expansion Variable Literal Symbol (Certificate Variable Literal Symbol)}
    {frames : List (Continuation Variable Literal Symbol (Certificate Variable Literal Symbol))} :
    BranchLive ground (expansion.start obligation frames).1 (expansion.start obligation frames).2 ↔
      AltLive ground expansion frames := by
  unfold Expansion.start AltLive
  split
  · rename_i none
    simp [BranchLive, none]
  · rename_i premise pending premisesEq
    simp [BranchLive, premisesEq, segment, Frame.start, Obligation.premise]

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem start_frames {obligation : Obligation Variable Literal Symbol}
    {expansion : Expansion Variable Literal Symbol (Certificate Variable Literal Symbol)}
    {frames : List (Continuation Variable Literal Symbol (Certificate Variable Literal Symbol))} :
    targetOf ground (expansion.start obligation frames).2 = targetOf ground frames ∧
      entries (expansion.start obligation frames).2 = entries frames := by
  unfold Expansion.start
  split <;> simp [targetOf, entries]

theorem start_cost {obligation : Obligation Variable Literal Symbol}
    {expansion : Expansion Variable Literal Symbol (Certificate Variable Literal Symbol)}
    {frames : List (Continuation Variable Literal Symbol (Certificate Variable Literal Symbol))} (bound : Nat) :
    focusCost ground bound (expansion.start obligation frames).1 (expansion.start obligation frames).2 =
      pendingWith (budget ground bound) expansion.premises (proceed ground bound frames) := by
  unfold Expansion.start
  split
  · rename_i none
    simp [focusCost, none, pendingWith]
  · rename_i premise pending premisesEq
    simp [focusCost, premisesEq, pendingWith, proceed, Frame.start, Obligation.premise]

end Lemmas

/-! ## Candidates keep the invariant -/

section Entering

variable {ground : Ground Variable Literal Symbol hoApplySymbol}

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem _root_.AnthillModKbSpec.Machine.Ordinary.conjunction {goals : List (Term Variable Literal Symbol)}
    (each : ∀ goal ∈ goals, Ordinary hoApplySymbol goal) : Ordinary hoApplySymbol (Term.conjunction goals) := by
  induction goals with
  | nil => exact .truth
  | cons goal rest ih =>
      exact .conj (each goal List.mem_cons_self) (ih fun other member => each other (List.mem_cons_of_mem _ member))

omit [FreshNames Variable] in
theorem truth_ok {obligation : Obligation Variable Literal Symbol} (goal : obligation.goal = .truth) :
    ExpansionOk ground obligation (Expansion.truth (Certificate := Certificate Variable Literal Symbol)) :=
  ⟨rfl, rfl, by simp [Expansion.truth], fun _ => goal ▸ .truth, rfl, .truth goal⟩

omit [FreshNames Variable] in
theorem conj_ok {obligation : Obligation Variable Literal Symbol} {left right : Term Variable Literal Symbol}
    (goal : obligation.goal = .conj left right) (ok : GoalOk ground (.conj left right)) :
    ExpansionOk ground obligation (Expansion.conjIntro (Certificate := Certificate Variable Literal Symbol) left right) := by
  obtain ⟨valid, ordinary, below⟩ := ok
  cases valid with
  | atom ground => cases ground
  | conj leftValid rightValid =>
      cases ordinary with
      | conj leftOrdinary rightOrdinary =>
          simp only [level_conj, Nat.max_le] at below
          refine ⟨rfl, rfl, fun premise member => ?_, fun proved => ?_, rfl, .conjIntro goal⟩
          · simp only [Expansion.conjIntro, List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl
            · exact ⟨rfl, leftValid, leftOrdinary, below.1⟩
            · exact ⟨rfl, rightValid, rightOrdinary, below.2⟩
          · rw [goal]
            exact .conj (proved ⟨{}, left⟩ (by simp [Expansion.conjIntro]))
              (proved ⟨{}, right⟩ (by simp [Expansion.conjIntro]))

theorem atomCandidates_ok {obligation : Obligation Variable Literal Symbol} {symbol : Symbol}
    {args : List (Term Variable Literal Symbol)} (goal : obligation.goal = .app symbol args)
    (ok : GoalOk ground (.app symbol args)) :
    ∀ expansion ∈ atomCandidates ground.entries ground.context.assumptions (.app symbol args),
      ExpansionOk ground obligation expansion := by
  intro expansion member
  have atomic : IsAtom hoApplySymbol (.app symbol args) := by
    cases ok.valid with
    | atom ground => exact ground
  rcases mem_atomCandidates member with ⟨rfl, inside⟩ | ⟨body, rfl, entry, entryMember, definite⟩
  · exact ⟨rfl, rfl, by simp [Expansion.assumption], fun _ => goal ▸ .assumption atomic inside, rfl,
      .assumption (goal ▸ inside)⟩
  · have listed : HornClause.definite (.app symbol args) body ∈ ground.program.clauses :=
      definite ▸ Ground.mem_clauses entryMember
    have bodyValid : IsGoal hoApplySymbol (Term.conjunction body) := by
      cases ground.program.wellFormed _ listed with
      | definite _ goals => exact conjunction_isGoal goals
    have bodyOrdinary : Ordinary hoApplySymbol (Term.conjunction body) :=
      Ordinary.conjunction (ground.clausesOrdinary _ listed).2
    have bodyBelow := ground.ranked.level_body listed
    have atomBelow := ok.below
    rw [level_app] at atomBelow
    refine ⟨rfl, rfl, fun premise inside => ?_, fun proved => ?_, rfl, ?_⟩
    · rw [clause_premises] at inside
      simp only [List.mem_singleton] at inside
      subst inside
      exact ⟨rfl, bodyValid, bodyOrdinary, by dsimp only; omega⟩
    · rw [goal]
      exact .clause atomic listed (proved _ (by rw [clause_premises]; exact List.mem_singleton_self _))
    · rw [clause_premises]; exact .clause listed goal

omit [FreshNames Variable] in
theorem save_ok {Snapshot : Type} {state : State Variable Literal Symbol (Certificate Variable Literal Symbol) Snapshot}
    {obligation : Obligation Variable Literal Symbol}
    {rest : List (Expansion Variable Literal Symbol (Certificate Variable Literal Symbol))}
    (store : state.store = Store.empty) (deferred : state.deferred = [])
    (framesOk : ∀ continuation ∈ state.frames, ContinuationOk ground continuation)
    (choicesOk : ∀ point ∈ state.choices, PointOk ground point) (parent : ObligationOk ground obligation)
    (candidates : ∀ expansion ∈ rest, ExpansionOk ground obligation expansion) :
    ∀ point ∈ state.save obligation rest, PointOk ground point := by
  intro point member
  rcases State.mem_save member with rfl | old
  · exact ⟨store, deferred, parent, framesOk, candidates⟩
  · exact choicesOk point old

omit [FreshNames Variable] in
/-- Entering a candidate of the run keeps its shape and its completeness, when
the remaining search covers the target with some candidate live. -/
theorem inv_enter {Snapshot : Type} {state : State Variable Literal Symbol (Certificate Variable Literal Symbol) Snapshot}
    {obligation : Obligation Variable Literal Symbol}
    {expansion : Expansion Variable Literal Symbol (Certificate Variable Literal Symbol)}
    {rest : List (Expansion Variable Literal Symbol (Certificate Variable Literal Symbol))} {depth : Nat}
    {target : Term Variable Literal Symbol}
    (root : state.root = ⟨ground.scope, ground.goal⟩) (store : state.store = Store.empty)
    (deferred : state.deferred = []) (gaps : state.gaps = [])
    (framesOk : ∀ continuation ∈ state.frames, ContinuationOk ground continuation)
    (choicesOk : ∀ point ∈ state.choices, PointOk ground point) (holes : state.nextHole = 0)
    (parent : ObligationOk ground obligation)
    (candidates : ∀ candidate ∈ expansion :: rest, ExpansionOk ground obligation candidate)
    (targetEq : targetOf ground state.frames = target) (entriesEq : entries state.frames = depth)
    (covers : Covers ground depth target (∃ candidate ∈ expansion :: rest, AltLive ground candidate state.frames)
      state.choices) :
    Shape ground (state.enter obligation expansion rest) ∧ Complete ground (state.enter obligation expansion rest) := by
  have first := candidates expansion List.mem_cons_self
  have others := fun candidate member => candidates candidate (List.mem_cons_of_mem _ member)
  rw [enter_eq store parent.1 first.flexibles first.bindings first.premises]
  obtain ⟨focusOk, startedOk⟩ := start_ok parent first.premises first.holds first.plain first.node framesOk
  obtain ⟨sameTarget, sameEntries⟩ := start_frames (ground := ground) (obligation := obligation)
    (expansion := expansion) (frames := state.frames)
  refine ⟨⟨root, rfl, deferred, gaps, focusOk, startedOk,
    save_ok store deferred framesOk choicesOk parent others, holes⟩, depth, target,
    fun _ => ⟨(sameTarget.trans targetEq).symm, sameEntries.trans entriesEq⟩, ?_⟩
  cases rest with
  | nil =>
      exact covers.mono fun ⟨candidate, member, live⟩ => by
        rw [List.mem_singleton.mp member] at live
        exact start_live.mpr live
  | cons other more =>
      simp only [State.save]
      refine ⟨entriesEq, targetEq, covers.mono fun ⟨candidate, member, live⟩ => ?_⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact .inl (start_live.mpr live)
      · exact .inr ⟨candidate, member, live⟩

theorem measure_enter {Snapshot : Type} {state : State Variable Literal Symbol (Certificate Variable Literal Symbol) Snapshot}
    {obligation : Obligation Variable Literal Symbol}
    {expansion : Expansion Variable Literal Symbol (Certificate Variable Literal Symbol)}
    {rest : List (Expansion Variable Literal Symbol (Certificate Variable Literal Symbol))}
    (store : state.store = Store.empty) (scope : obligation.scope = ground.scope)
    (flexibles : expansion.flexibles = []) (bindings : expansion.bindings = [])
    (premises : ∀ premise ∈ expansion.premises, PremiseOk ground premise) :
    measure ground (state.enter obligation expansion rest) ≤
      pendingWith (budget ground (level ground.rank ground.goal)) expansion.premises
          (proceed ground (level ground.rank ground.goal) state.frames) +
        ((rest.map fun candidate => pendingWith (budget ground (level ground.rank ground.goal)) candidate.premises
          (proceed ground (level ground.rank ground.goal) state.frames) + 2).sum + 1) +
        (state.choices.map (pointCost ground (level ground.rank ground.goal))).sum ∧
    (rest = [] → measure ground (state.enter obligation expansion rest) =
      pendingWith (budget ground (level ground.rank ground.goal)) expansion.premises
          (proceed ground (level ground.rank ground.goal) state.frames) +
        (state.choices.map (pointCost ground (level ground.rank ground.goal))).sum) := by
  rw [enter_eq store scope flexibles bindings premises]
  simp only [measure]
  rw [start_cost]
  cases rest with
  | nil => simp [State.save]
  | cons other more =>
      refine ⟨?_, fun empty => by cases empty⟩
      simp [State.save, pointCost]
      omega

end Entering

/-! ## Every transition keeps the invariant and decreases the measure -/

section Steps

variable {ground : Ground Variable Literal Symbol hoApplySymbol} {Snapshot : Type}
  {state next : State Variable Literal Symbol (Certificate Variable Literal Symbol) Snapshot}

/-- An atom's budget at a bound covering its level, with every candidate's
premises costed at that same bound. -/
theorem budget_atom {symbol : Symbol} {args : List (Term Variable Literal Symbol)} {bound : Nat}
    (below : level ground.rank (.app symbol args) ≤ bound) (after : Nat) :
    budget ground bound (.app symbol args) after =
      ((atomCandidates ground.entries ground.context.assumptions (.app symbol args)).map fun expansion =>
        pendingWith (budget ground bound) expansion.premises after + 2).sum + 2 := by
  rw [level_app] at below
  obtain ⟨m, rfl⟩ : ∃ m, bound = m + 1 := ⟨bound - 1, by omega⟩
  rw [budget]
  congr 2
  apply List.map_congr_left
  intro expansion member
  congr 1
  apply pendingWith_congr
  intro premise inside rest
  rcases mem_atomCandidates member with ⟨rfl, _⟩ | ⟨body, rfl, entry, entryMember, definite⟩
  · simp [Expansion.assumption] at inside
  · rw [clause_premises] at inside
    simp only [List.mem_singleton] at inside
    subst inside
    have bodyBelow := ground.ranked.level_body (definite ▸ Ground.mem_clauses entryMember)
    exact (budget_stable m _ rest (by dsimp only; omega)).symm

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem _root_.AnthillModKbSpec.GroundSearch.Succeeds.conj_inv
    {program : GroundSearch.Program Variable Literal Symbol hoApplySymbol}
    {context : GroundSearch.Context Variable Literal Symbol hoApplySymbol} {left right : Term Variable Literal Symbol}
    (proof : Succeeds program context (.conj left right)) : Succeeds program context left ∧ Succeeds program context right := by
  cases proof with
  | conj first second => exact ⟨first, second⟩

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem _root_.AnthillModKbSpec.GroundSearch.Succeeds.defaultNeg_inv
    {program : GroundSearch.Program Variable Literal Symbol hoApplySymbol}
    {context : GroundSearch.Context Variable Literal Symbol hoApplySymbol} {operand : Term Variable Literal Symbol}
    (proof : Succeeds program context (.defaultNeg operand)) : Fails program context operand := by
  cases proof with
  | defaultNeg failed => exact failed

theorem inv_solve {obligation : Obligation Variable Literal Symbol} (inv : Inv ground state)
    (focused : state.focus = .solve obligation) (stepped : step ground.strategy state = .running next) :
    Inv ground next ∧ measure ground next < measure ground state := by
  have valid := (step_valid _ inv.valid stepped).1
  obtain ⟨root, store, deferred, gaps, focusOk, framesOk, choicesOk, holes⟩ := inv.shape
  obtain ⟨depth, target, current, covers⟩ := inv.complete
  obtain ⟨targetEq, entriesEq⟩ := current (by rw [focused]; exact fun h => by cases h)
  rw [focused] at covers focusOk
  obtain ⟨scope, goal⟩ := obligation
  obtain ⟨scopeEq, goalOk⟩ := focusOk
  simp only at scopeEq goalOk
  subst scopeEq
  have answer : ground.strategy ⟨ground.scope, goal⟩ state.store = ground.response ⟨ground.scope, goal⟩ := by
    rw [store]; exact ground.strategy_eq goalOk.valid goalOk.ordinary
  have measured : measure ground state = budget ground (level ground.rank ground.goal) goal
      (proceed ground (level ground.rank ground.goal) state.frames) +
      (state.choices.map (pointCost ground (level ground.rank ground.goal))).sum := by
    simp only [measure, focused, focusCost]
  unfold step at stepped
  rw [focused] at stepped
  simp only at stepped
  rw [answer] at stepped
  have parent : ObligationOk ground ⟨ground.scope, goal⟩ := ⟨rfl, goalOk⟩
  have plainBelow := goalOk.below
  cases hValid : goalOk.valid with
  | atom atomic =>
      cases atomic with
      | app ordinary dataArgs =>
          rename_i symbol args
          simp only [Ground.response] at stepped
          have cost := budget_atom (ground := ground) plainBelow
            (proceed ground (level ground.rank ground.goal) state.frames)
          generalize candidatesEq : atomCandidates ground.entries ground.context.assumptions (.app symbol args) = cands
            at stepped cost
          have candidatesOk : ∀ expansion ∈ cands, ExpansionOk ground ⟨ground.scope, .app symbol args⟩ expansion :=
            candidatesEq ▸ atomCandidates_ok rfl goalOk
          have found : Live ground (.app symbol args :: segment state.frames) →
              ∃ expansion ∈ cands, AltLive ground expansion state.frames := fun live => by
            obtain ⟨expansion, member, proved⟩ := atomCandidates_complete (ground := ground)
              (live _ List.mem_cons_self)
            refine ⟨expansion, candidatesEq ▸ member, fun goal inside => ?_⟩
            rcases List.mem_append.mp inside with fromPremise | fromRest
            · obtain ⟨premise, premiseMember, rfl⟩ := List.mem_map.mp fromPremise
              exact proved premise premiseMember
            · exact live goal (List.mem_cons_of_mem _ fromRest)
          cases cands with
          | nil =>
              cases stepped
              refine ⟨⟨valid, ⟨root, store, deferred, gaps, trivial, framesOk, choicesOk, holes⟩,
                depth, target, fun failed => absurd rfl failed, covers.mono fun live => ?_⟩, ?_⟩
              · obtain ⟨_, member, _⟩ := found live; cases member
              · rw [measured, cost]; simp [measure, focusCost]
          | cons expansion rest =>
              cases stepped
              have first := candidatesOk expansion List.mem_cons_self
              obtain ⟨shape, complete⟩ := inv_enter root store deferred gaps framesOk choicesOk holes parent candidatesOk
                targetEq.symm entriesEq (covers.mono found)
              refine ⟨⟨valid, shape, complete⟩, ?_⟩
              have bound := (measure_enter (rest := rest) (obligation := ⟨ground.scope, .app symbol args⟩) store rfl
                first.flexibles first.bindings first.premises).1
              rw [measured, cost, List.map_cons, List.sum_cons]
              generalize (rest.map fun candidate =>
                pendingWith (budget ground (level ground.rank ground.goal)) candidate.premises
                  (proceed ground (level ground.rank ground.goal) state.frames) + 2).sum = others at bound ⊢
              omega
  | truth =>
      simp only [Ground.response] at stepped
      cases stepped
      have candidate := truth_ok (ground := ground) (obligation := ⟨ground.scope, .truth⟩) rfl
      obtain ⟨shape, complete⟩ := inv_enter (rest := []) root store deferred gaps framesOk choicesOk holes parent
        (fun other member => by rw [List.mem_singleton.mp member]; exact candidate) targetEq.symm entriesEq
        (covers.mono fun live => ⟨_, List.mem_singleton_self _, fun goal inside => live goal (by
          simp only [Expansion.truth, List.map_nil, List.nil_append] at inside; exact List.mem_cons_of_mem _ inside)⟩)
      refine ⟨⟨valid, shape, complete⟩, ?_⟩
      rw [(measure_enter store rfl candidate.flexibles candidate.bindings candidate.premises).2 rfl, measured, budget]
      simp [Expansion.truth, pendingWith]
  | falsity =>
      simp only [Ground.response] at stepped
      cases stepped
      refine ⟨⟨valid, ⟨root, store, deferred, gaps, trivial, framesOk, choicesOk, holes⟩,
        depth, target, fun failed => absurd rfl failed, covers.mono fun live => ?_⟩, ?_⟩
      · have proof := live _ List.mem_cons_self
        cases proof
      · rw [measured, budget]; simp [measure, focusCost]
  | conj leftValid rightValid =>
      rename_i left right
      simp only [Ground.response] at stepped
      cases stepped
      have candidate := conj_ok (ground := ground) (obligation := ⟨ground.scope, .conj left right⟩) rfl goalOk
      obtain ⟨shape, complete⟩ := inv_enter (rest := []) root store deferred gaps framesOk choicesOk holes parent
        (fun other member => by rw [List.mem_singleton.mp member]; exact candidate) targetEq.symm entriesEq
        (covers.mono fun live => ⟨_, List.mem_singleton_self _, fun goal inside => by
          obtain ⟨leftOk, rightOk⟩ := Succeeds.conj_inv (live _ List.mem_cons_self)
          simp only [Expansion.conjIntro, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
            List.mem_cons] at inside
          rcases inside with rfl | rfl | rest
          · exact leftOk
          · exact rightOk
          · exact live goal (List.mem_cons_of_mem _ rest)⟩)
      refine ⟨⟨valid, shape, complete⟩, ?_⟩
      rw [(measure_enter store rfl candidate.flexibles candidate.bindings candidate.premises).2 rfl, measured, budget]
      simp [Expansion.conjIntro, pendingWith]
  | defaultNeg operandValid =>
      rename_i operand
      have settled : state.store.groundNegation ⟨ground.scope, .defaultNeg operand⟩ operand = true := by
        rw [store]; exact ground.groundNegation operandValid.closed _
      simp only [Ground.response, settled, ↓reduceIte] at stepped
      cases stepped
      have operandOk : GoalOk ground operand := by
        obtain ⟨_, ordinary, below⟩ := goalOk
        cases ordinary with
        | defaultNeg inner => exact ⟨operandValid, inner, by simpa using below⟩
      refine ⟨⟨valid, ⟨root, store, deferred, gaps, ⟨rfl, operandOk⟩, fun continuation member => ?_,
        fun point member => ?_, holes⟩, depth + 1, operand, fun _ => ⟨rfl, by simp [entries, entriesEq]⟩, ?_⟩, ?_⟩
      · rcases List.mem_cons.mp member with rfl | member
        · exact ⟨parent, rfl, rfl, holes⟩
        · exact framesOk continuation member
      · rcases List.mem_cons.mp member with rfl | member
        · refine ⟨store, deferred, parent, framesOk, ?_⟩
          show (⟨state.gaps.length, state.nextHole⟩ : Barrier) = ⟨0, 0⟩ ∧ BarrierOk ground _
          exact ⟨by simp [gaps, holes], _, rfl, rfl, rfl, rfl, rfl⟩
        · exact choicesOk point member
      · refine ⟨depth, rfl, entriesEq, rfl, fun proof => ?_, ?_⟩
        · intro other member
          simp only [segment, List.mem_cons, List.not_mem_nil, or_false] at member
          rw [member]; exact proof
        · dsimp only
          rw [← targetEq]
          exact covers.mono fun live => ⟨Succeeds.defaultNeg_inv (live _ List.mem_cons_self),
            fun other member => live other (List.mem_cons_of_mem _ member)⟩
      · rw [measured, budget]
        simp [measure, focusCost, proceed, pointCost, Expansion.negation, pendingWith]
        omega

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem mem_closedWorldOf {trees : List (ProofTree Variable Literal Symbol (Certificate Variable Literal Symbol))}
    {evidence : ClosedWorldEvidence (Certificate Variable Literal Symbol)} :
    evidence ∈ ProofTree.closedWorldOf trees ↔ ∃ tree ∈ trees, evidence ∈ tree.closedWorld := by
  induction trees with
  | nil => simp [ProofTree.closedWorldOf]
  | cons tree trees ih => simp [ProofTree.closedWorldOf, ih]

omit [FreshNames Variable] in
/-- A node built from finished subtrees of the run, by a rule with no
certificate, is a finished subtree of the run. -/
theorem TreeOk.node {rule : RuleApp Variable Literal Symbol (Certificate Variable Literal Symbol)}
    {obligation : Obligation Variable Literal Symbol} {premises : List (Premise Variable Literal Symbol)}
    {subproofs : List (ProofTree Variable Literal Symbol (Certificate Variable Literal Symbol))}
    (plain : rule.closedWorld? = none) (step : NodeOk ground rule obligation premises)
    (children : ∀ tree ∈ subproofs, TreeOk ground tree) :
    TreeOk ground (.node rule obligation premises subproofs) := by
  refine ⟨?_, fun evidence member => ?_, .node step fun tree inside => (children tree inside).2.2⟩
  · simp only [ProofTree.refs]
    exact List.eq_nil_iff_forall_not_mem.mpr fun ref found => by
      obtain ⟨tree, inside, here⟩ := ProofTree.mem_refsOf.mp found
      rw [(children tree inside).1] at here
      cases here
  · simp only [ProofTree.closedWorld, plain, Option.toList_none, List.nil_append] at member
    obtain ⟨tree, inside, here⟩ := mem_closedWorldOf.mp member
    exact (children tree inside).2.1 evidence here

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem cutNegation_sum (cost : ChoicePoint Variable Literal Symbol (Certificate Variable Literal Symbol) → Nat) :
    ∀ choices : List (ChoicePoint Variable Literal Symbol (Certificate Variable Literal Symbol)),
      ((cutNegation choices).map cost).sum ≤ (choices.map cost).sum
  | [] => Nat.le_refl _
  | point :: rest => by
      unfold cutNegation
      split
      · simp
      · have := cutNegation_sum cost rest
        simp only [List.map_cons, List.sum_cons]
        omega

theorem inv_proved {tree : ProofTree Variable Literal Symbol (Certificate Variable Literal Symbol)} (inv : Inv ground state)
    (focused : state.focus = .proved tree) (stepped : step ground.strategy state = .running next) :
    Inv ground next ∧ measure ground next < measure ground state := by
  have valid := (step_valid _ inv.valid stepped).1
  obtain ⟨root, store, deferred, gaps, focusOk, framesOk, choicesOk, holes⟩ := inv.shape
  obtain ⟨depth, target, current, covers⟩ := inv.complete
  obtain ⟨targetEq, entriesEq⟩ := current (by rw [focused]; exact fun h => by cases h)
  rw [focused] at covers focusOk
  obtain ⟨proof, treeOk⟩ := focusOk
  have opened := inv.valid.branch.valid
  rw [focused] at opened
  obtain ⟨proves, _⟩ := opened
  unfold step at stepped
  rw [focused] at stepped
  simp only at stepped
  match framesEq : state.frames, stepped with
  | [], stepped =>
      rw [store] at stepped
      simp [Store.residual, Store.empty] at stepped
  | .frame frame :: rest, stepped =>
      have frameOk : FrameOk ground frame := framesOk (.frame frame) (by simp [framesEq])
      have restOk : ∀ continuation ∈ rest, ContinuationOk ground continuation :=
        fun continuation member => framesOk continuation (by simp [framesEq, member])
      rw [framesEq] at proves covers targetEq entriesEq
      have currentProof : Succeeds ground.program ground.context frame.current.goal := by
        have same : tree.obligation.goal = frame.current.goal := by
          rw [proves]; rfl
        rw [← same]; exact proof
      obtain ⟨parent, rule, before, done, current, pending⟩ := frame
      cases pending with
      | nil =>
          simp only [Frame.receive] at stepped
          cases stepped
          have node : TreeOk ground (.node rule parent (before ++ [current]) (done ++ [tree])) :=
            TreeOk.node frameOk.plain (by simpa [Frame.premises] using frameOk.node) fun child member => by
              rcases List.mem_append.mp member with old | last
              · exact frameOk.done child old
              · rw [List.mem_singleton.mp last]; exact treeOk
          have holds := frameOk.holds
          simp only [Frame.premises] at holds
          refine ⟨⟨valid, ⟨root, store, deferred, gaps, ⟨holds fun premise member => ?_, node⟩, restOk, choicesOk,
            holes⟩,
            depth, target, fun _ => ⟨targetEq, entriesEq⟩, covers.mono fun live => ?_⟩, ?_⟩
          · rcases List.mem_append.mp member with old | last
            · exact frameOk.proved premise old
            · rw [List.mem_singleton.mp last]; exact currentProof
          · simpa [BranchLive, segment] using live
          · simp [measure, focusCost, focused, framesEq, proceed, pendingWith]
      | cons following later =>
          simp only [Frame.receive] at stepped
          cases stepped
          have followingOk := frameOk.premises following (by simp [Frame.premises])
          refine ⟨⟨valid, ⟨root, store, deferred, gaps, frameOk.parent.premise followingOk,
            fun continuation member => ?_, choicesOk, holes⟩, depth, target,
            fun _ => ⟨targetEq, entriesEq⟩, covers.mono fun live => ?_⟩, ?_⟩
          · rcases List.mem_cons.mp member with rfl | member
            · refine ⟨frameOk.parent, fun premise member => frameOk.premises premise (by
                simpa [Frame.premises] using member), by
                  have holds := frameOk.holds
                  simpa [Frame.premises] using holds, fun premise member => ?_, fun child member => ?_,
                frameOk.plain, by simpa [Frame.premises] using frameOk.node⟩
              · rcases List.mem_append.mp member with old | last
                · exact frameOk.proved premise old
                · rw [List.mem_singleton.mp last]; exact currentProof
              · rcases List.mem_append.mp member with old | last
                · exact frameOk.done child old
                · rw [List.mem_singleton.mp last]; exact treeOk
            · exact restOk continuation member
          · simpa [BranchLive, segment, Frame.focus, Obligation.premise] using live
          · simp [measure, focusCost, focused, framesEq, proceed, pendingWith, Frame.focus, Obligation.premise]
  | .woken hole obligation resumed :: rest, stepped =>
      exact (framesOk (.woken hole obligation resumed) (by simp [framesEq])).elim
  | .negation obligation operand entryHoles :: rest, stepped =>
      rw [framesEq] at proves targetEq entriesEq
      obtain ⟨_, _, _, noHoles⟩ := framesOk (.negation obligation operand entryHoles) (by simp [framesEq])
      simp only [holes, noHoles, beq_self_eq_true, ↓reduceIte] at stepped
      cases stepped
      have restOk : ∀ continuation ∈ rest, ContinuationOk ground continuation :=
        fun continuation member => framesOk continuation (by simp [framesEq, member])
      have operandProof : Succeeds ground.program ground.context target := by
        have same : tree.obligation = operand := proves
        rw [targetEq]; simp only [targetOf]; rw [← same]; exact proof
      obtain ⟨depth', target', cut⟩ := covers.cut (by simp [entries] at entriesEq; omega) operandProof
      refine ⟨⟨valid, ⟨root, store, deferred, gaps, trivial, restOk,
        fun point member => choicesOk point (mem_cutNegation member), rfl⟩, depth', target',
        fun failed => absurd rfl failed, cut⟩, ?_⟩
      have := cutNegation_sum (pointCost ground (level ground.rank ground.goal)) state.choices
      simp only [measure, focusCost, focused, framesEq, proceed]
      omega

theorem inv_failed (inv : Inv ground state) (focused : state.focus = .failed)
    (stepped : step ground.strategy state = .running next) :
    Inv ground next ∧ measure ground next < measure ground state := by
  have valid := (step_valid _ inv.valid stepped).1
  obtain ⟨root, store, deferred, gaps, _, framesOk, choicesOk, holes⟩ := inv.shape
  obtain ⟨depth, target, _, covers⟩ := inv.complete
  rw [focused] at covers
  unfold step at stepped
  rw [focused] at stepped
  simp only at stepped
  match choicesEq : state.choices, stepped with
  | [], stepped => simp at stepped
  | point :: others, stepped =>
      have pointOk := choicesOk point (by simp [choicesEq])
      have othersOk : ∀ other ∈ others, PointOk ground other :=
        fun other member => choicesOk other (by simp [choicesEq, member])
      rw [choicesEq] at covers
      have measured : measure ground state = 1 + pointCost ground (level ground.rank ground.goal) point +
          (others.map (pointCost ground (level ground.rank ground.goal))).sum := by
        simp only [measure, focusCost, focused, choicesEq, List.map_cons, List.sum_cons]
        omega
      have alternativesOk := pointOk.alternatives
      unfold Covers at covers
      cases alternativesEq : point.alternatives with
      | nil =>
          simp only [alternativesEq] at stepped
          cases stepped
          cases barrierEq : point.barrier with
          | some count =>
              rw [barrierEq] at alternativesOk
              obtain ⟨_, certificate, single, _⟩ := alternativesOk
              rw [alternativesEq] at single
              cases single
          | none =>
              rw [barrierEq] at covers
              refine ⟨⟨valid, ⟨root, store, deferred, gaps, trivial, framesOk, othersOk, holes⟩, depth, target,
                fun failed => absurd rfl failed, covers.2.2.mono fun either => ?_⟩, ?_⟩
              · rcases either with impossible | ⟨_, member, _⟩
                · exact impossible
                · rw [alternativesEq] at member; cases member
              · rw [measured]
                simp [measure, focusCost, pointCost, alternativesEq]
      | cons expansion rest =>
          simp only [alternativesEq] at stepped
          have opened : point.open state.gaps state.nextHole = true := by
            unfold ChoicePoint.open
            split
            · rfl
            · rename_i marks barrierEq
              rw [barrierEq] at alternativesOk
              simp [gaps, holes, alternativesOk.1]
          simp only [opened, ↓reduceIte] at stepped
          cases stepped
          cases barrierEq : point.barrier with
          | none =>
              rw [barrierEq] at covers alternativesOk
              rw [alternativesEq] at alternativesOk
              obtain ⟨entriesEq, targetEq, rest'⟩ := covers
              obtain ⟨shape, complete⟩ := inv_enter
                (state := { state with
                  focus := .failed, store := point.store, frames := point.frames, deferred := point.deferred,
                  choices := others })
                root pointOk.store pointOk.deferred gaps pointOk.frames othersOk holes pointOk.obligation alternativesOk
                targetEq entriesEq (rest'.mono fun either => by
                  rcases either with impossible | found
                  · exact impossible.elim
                  · rw [alternativesEq] at found; exact found)
              refine ⟨⟨valid, shape, complete⟩, ?_⟩
              have first := alternativesOk expansion List.mem_cons_self
              have bound := (measure_enter (rest := rest)
                (state := { state with
                  focus := .failed, store := point.store, frames := point.frames, deferred := point.deferred,
                  choices := others })
                pointOk.store pointOk.obligation.1 first.flexibles first.bindings first.premises).1
              rw [measured]
              simp only [pointCost, alternativesEq, List.map_cons, List.sum_cons] at bound ⊢
              generalize (rest.map fun candidate =>
                pendingWith (budget ground (level ground.rank ground.goal)) candidate.premises
                  (proceed ground (level ground.rank ground.goal) point.frames) + 2).sum = others' at bound ⊢
              omega
          | some count =>
              rw [barrierEq] at covers alternativesOk
              obtain ⟨_, certificate, single, clauses, context, negationGoal, witnessEq⟩ := alternativesOk
              rw [alternativesEq] at single
              simp only [List.cons.injEq] at single
              obtain ⟨rfl, rfl⟩ := single
              obtain ⟨below, deeper, entriesEq, targetGoal, missing, rest'⟩ := covers
              have sameOperand : certificate.operand = target := by
                rw [negationGoal] at targetGoal; cases targetGoal; rfl
              have operandValid : IsGoal hoApplySymbol target := by
                have whole := pointOk.obligation.2.valid
                rw [targetGoal] at whole
                cases whole with
                | atom ground => cases ground
                | defaultNeg body => exact body
              have failed := fails_of_not_succeeds ground.ranked operandValid missing
              have operandBelow : level ground.rank target ≤ level ground.rank ground.goal := by
                have whole := pointOk.obligation.2.below
                rw [targetGoal, level_defaultNeg] at whole
                exact whole
              have entered := enter_eq (ground := ground) (rest := [])
                (state := { state with
                  focus := .failed, store := point.store, frames := point.frames, deferred := point.deferred,
                  choices := others }) (expansion := Expansion.negation certificate)
                pointOk.store pointOk.obligation.1 rfl rfl (by simp [Expansion.negation])
              rw [entered] at valid ⊢
              simp only [Expansion.start, Expansion.negation, State.save] at valid ⊢
              have certified : certificate.Valid ground.program ground.context := by
                obtain ⟨tree, witnessed, checked⟩ := evaluate_failure ground.ranked operandValid operandBelow failed
                refine ⟨clauses, context, ?_⟩
                simp only [NegativeCertificate.check]
                rw [witnessEq, Ground.witness, context, sameOperand, witnessed, clauses]
                exact checked
              refine ⟨⟨valid, ⟨root, rfl, pointOk.deferred, gaps, ⟨?_, ?_, ?_, ?_⟩, pointOk.frames, othersOk, holes⟩,
                below,
                targetOf ground point.frames, fun _ => ⟨rfl, entriesEq⟩, rest'.mono fun live => live.2⟩, ?_⟩
              · show Succeeds ground.program ground.context point.obligation.goal
                rw [targetGoal]; exact .defaultNeg failed
              · simp [ProofTree.refs, ProofTree.refsOf]
              · intro evidence member
                simp only [ProofTree.closedWorld, RuleApp.closedWorld?, ProofTree.closedWorldOf, Option.toList_some,
                  List.append_nil, List.mem_singleton] at member
                subst member
                exact certified
              · exact .node (.negation negationGoal certified) fun _ member => by cases member
              · rw [measured]
                simp [measure, focusCost, pointCost, alternativesEq, Expansion.negation, pendingWith]
                omega

theorem step_inv (inv : Inv ground state) (stepped : step ground.strategy state = .running next) :
    Inv ground next ∧ measure ground next < measure ground state := by
  cases focused : state.focus with
  | solve obligation => exact inv_solve inv focused stepped
  | proved tree => exact inv_proved inv focused stepped
  | failed => exact inv_failed inv focused stepped

end Steps

/-! ## Runs -/

section Runs

variable (ground : Ground Variable Literal Symbol hoApplySymbol) {Snapshot : Type}

/-- A P0 run starts from the query with no answer names. -/
def Ground.init (snapshot : Snapshot) : State Variable Literal Symbol (Certificate Variable Literal Symbol) Snapshot :=
  State.init snapshot [] ground.context.assumptions ground.goal

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem Ground.rootRigids_nil : rootRigids [] ground.context.assumptions ground.goal = [] := by
  have closed : (Obligation.root ([] : List Variable) ground.context.assumptions ground.goal).freeVars = [] := by
    simp only [Obligation.freeVars, Obligation.root, Obligation.context, ground.valid.closed, List.nil_append]
    exact List.flatMap_eq_nil_iff.mpr fun atom member => (IsGoal.atom (ground.context.wellFormed atom member)).closed
  simp [rootRigids, closed]

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem Ground.init_eq (snapshot : Snapshot) :
    ground.init snapshot =
      { snapshot, root := ⟨ground.scope, ground.goal⟩, store := Store.empty, focus := .solve ⟨ground.scope, ground.goal⟩,
        frames := [], choices := [], gaps := [], deferred := [], nextHole := 0 } := by
  show State.init snapshot [] ground.context.assumptions ground.goal = _
  simp only [State.init, ground.rootRigids_nil]
  rfl

omit [FreshNames Variable] in
theorem Ground.init_inv (snapshot : Snapshot) : Inv ground (ground.init snapshot) := by
  have valid : (ground.init snapshot).Valid := State.init_valid snapshot [] ground.context.assumptions ground.goal
  rw [ground.init_eq] at valid ⊢
  refine ⟨valid, ⟨rfl, rfl, rfl, rfl, ⟨rfl, ground.valid, ground.ordinary, Nat.le_refl _⟩, by simp, by simp, rfl⟩,
    0, ground.goal, fun _ => ⟨rfl, rfl⟩, rfl, rfl, fun proof goal member => ?_⟩
  simp only [segment, List.mem_cons, List.not_mem_nil, or_false] at member
  rw [member]; exact proof

/-- What a finishing step of a P0 run returns: a success whose tree proves the
root with valid certificates, or exhaustion with a complete-failure
certificate. Never `unknown`. -/
theorem step_finished {state : State Variable Literal Symbol (Certificate Variable Literal Symbol) Snapshot}
    {outcome : Outcome Variable Literal Symbol (Certificate Variable Literal Symbol) Snapshot} (inv : Inv ground state)
    (stepped : step ground.strategy state = .finished outcome) :
    (∃ proof resume, outcome = .success proof resume ∧ proof.root = ⟨ground.scope, ground.goal⟩ ∧
        proof.tree.obligation = ⟨ground.scope, ground.goal⟩ ∧
        Succeeds ground.program ground.context ground.goal ∧ TreeOk ground proof.tree ∧
          proof.store = Store.empty ∧ proof.tree.Coherent) ∨
      (outcome = .exhausted ∧ Fails ground.program ground.context ground.goal) := by
  obtain ⟨root, store, deferred, gaps, focusOk, framesOk, choicesOk, holes⟩ := inv.shape
  obtain ⟨depth, target, current, covers⟩ := inv.complete
  have branchValid := inv.valid.branch.valid
  unfold step at stepped
  cases focused : state.focus with
  | solve obligation =>
      rw [focused] at stepped
      simp only at stepped
      repeat' split at stepped
      all_goals cases stepped
  | proved tree =>
      rw [focused] at stepped focusOk branchValid
      simp only at stepped
      split at stepped
      · rename_i framesEq
        rw [store] at stepped
        simp only [Store.residual, Store.empty, List.map_nil, List.append_nil] at stepped
        cases stepped
        obtain ⟨proves, coherent⟩ := branchValid
        rw [framesEq] at proves
        refine .inl ⟨_, _, rfl, root, ?_, ?_, ?_, rfl, ?_⟩
        · simp only [deferred, List.length_nil, ProofTree.fillAll]; rw [proves, root]; rfl
        · have goalEq : tree.obligation.goal = ground.goal := by rw [proves, root]; rfl
          rw [← goalEq]; exact focusOk.1
        · simp only [deferred, List.length_nil, ProofTree.fillAll]; exact focusOk.2
        · simp only [deferred, List.length_nil, ProofTree.fillAll]; exact coherent
      all_goals (try split at stepped) <;> cases stepped
  | failed =>
      rw [focused] at stepped covers
      simp only at stepped
      split at stepped
      · rename_i choicesEq
        rw [gaps] at stepped
        simp only [List.isEmpty_nil, ↓reduceIte] at stepped
        cases stepped
        rw [choicesEq] at covers
        obtain ⟨_, targetRoot, missing⟩ := covers
        rw [targetRoot] at missing
        exact .inr ⟨rfl, fails_of_not_succeeds ground.ranked ground.valid missing⟩
      · split at stepped <;> (try split at stepped) <;> cases stepped

/-- Along a P0 run from an invariant state: success proves the root goal with
valid certificates, exhaustion refutes it with a complete-failure certificate,
the run is never `unknown`, and it finishes within the measure. -/
theorem run_outcome : ∀ (fuel : Nat) (state : State Variable Literal Symbol (Certificate Variable Literal Symbol) Snapshot),
    Inv ground state →
      (∀ proof resume, run ground.strategy fuel state = .success proof resume →
        proof.root = ⟨ground.scope, ground.goal⟩ ∧ proof.tree.obligation = ⟨ground.scope, ground.goal⟩ ∧
          Succeeds ground.program ground.context ground.goal ∧ TreeOk ground proof.tree ∧
          proof.store = Store.empty ∧ proof.tree.Coherent) ∧
      (run ground.strategy fuel state = .exhausted → Fails ground.program ground.context ground.goal) ∧
      (∀ gaps, run ground.strategy fuel state ≠ .unknown gaps) ∧
      (measure ground state < fuel → ∀ stopped, run ground.strategy fuel state ≠ .interrupted stopped)
  | 0, state, _ => ⟨(fun _ _ ran => by cases ran), (fun ran => by cases ran), (fun _ ran => by cases ran),
      (fun small => absurd small (Nat.not_lt_zero _))⟩
  | fuel + 1, state, inv => by
      unfold run
      split
      · rename_i next stepped
        obtain ⟨nextInv, smaller⟩ := step_inv inv stepped
        obtain ⟨success, exhausted, unknown, total⟩ := run_outcome fuel next nextInv
        exact ⟨success, exhausted, unknown, fun small => total (by omega)⟩
      · rename_i outcome stepped
        rcases step_finished ground inv stepped with ⟨proof, resume, rfl, facts⟩ | ⟨rfl, failed⟩
        · exact ⟨(fun _ _ same => by cases same; exact facts), (fun same => by cases same),
            (fun _ same => by cases same), (fun _ _ same => by cases same)⟩
        · exact ⟨(fun _ _ same => by cases same), (fun _ => failed), (fun _ same => by cases same),
            (fun _ _ same => by cases same)⟩

/-- Termination: a P0 run from its query finishes within its measure, with a
success or exhaustion. Bounded fuel below the measure may interrupt it; an
interruption is no result about the goal. -/
theorem run_total (snapshot : Snapshot) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      (∃ proof resume, run ground.strategy fuel (ground.init snapshot) = .success proof resume) ∨
        run ground.strategy fuel (ground.init snapshot) = .exhausted := by
  refine ⟨measure ground (ground.init snapshot) + 1, fun fuel enough => ?_⟩
  obtain ⟨_, _, unknown, total⟩ := run_outcome ground fuel (ground.init snapshot) (ground.init_inv snapshot)
  cases ran : run ground.strategy fuel (ground.init snapshot) with
  | success proof resume => exact .inl ⟨proof, resume, rfl⟩
  | exhausted => exact .inr rfl
  | unknown gaps => exact absurd ran (unknown gaps)
  | interrupted stopped => exact absurd ran (total (by omega) stopped)

/-- Correctness: a successful P0 run proves the original query with a success
certificate, its tree's NAF nodes hold valid certificates for the exact program
and context, and it reconstructs `Derives` with the ground failure provider of
that program and context. An exhausted run has a complete-failure certificate.
No run is `unknown`, whatever the fuel. -/
theorem run_correct (snapshot : Snapshot) (fuel : Nat) :
    (∀ proof resume, run ground.strategy fuel (ground.init snapshot) = .success proof resume →
      proof.root = ⟨ground.scope, ground.goal⟩ ∧ proof.tree.obligation = ⟨ground.scope, ground.goal⟩ ∧
      Succeeds ground.program ground.context ground.goal ∧
      (∀ evidence ∈ proof.tree.closedWorld, evidence.certificate.Valid ground.program ground.context) ∧
      Derives hoApplySymbol ground.program.toKb ground.context.assumptions ground.goal
        (failureEvidence ground.program ground.context) ∧
      Built ground proof.tree ∧ proof.store = Store.empty ∧ proof.tree.Coherent) ∧
    (run ground.strategy fuel (ground.init snapshot) = .exhausted → Fails ground.program ground.context ground.goal) ∧
    ∀ gaps, run ground.strategy fuel (ground.init snapshot) ≠ .unknown gaps := by
  obtain ⟨success, exhausted, unknown, _⟩ := run_outcome ground fuel (ground.init snapshot) (ground.init_inv snapshot)
  refine ⟨fun proof resume ran => ?_, exhausted, unknown⟩
  obtain ⟨root, proves, proof, treeOk, emptied, coherent⟩ := success proof resume ran
  exact ⟨root, proves, proof, treeOk.2.1, succeeds_toDerives proof, treeOk.2.2, emptied, coherent⟩

/-- The semantic reading of a completed run, in a model completed for the
program and context with complement NAF: success makes the goal true and
exhaustion false. Completion is a hypothesis here; S16 owns a completed-model
witness for admitted inputs. -/
theorem run_semantic {Value : Type} {model : Semantics.Model Literal Symbol Value hoApplySymbol}
    (completed : model.GroundCompleted ground.program ground.context) (negation : model.ComplementNAF)
    (snapshot : Snapshot) (fuel : Nat) :
    (∀ proof resume, run ground.strategy fuel (ground.init snapshot) = .success proof resume →
      ∀ environment, model.Satisfies environment ground.goal) ∧
    (run ground.strategy fuel (ground.init snapshot) = .exhausted →
      ∀ environment, ¬ model.Satisfies environment ground.goal) := by
  obtain ⟨success, exhausted, _⟩ := run_correct ground snapshot fuel
  have sound := model.ground_certificates_sound completed negation
  exact ⟨fun proof resume ran => sound.1 _ (success proof resume ran).2.2.1,
    fun ran => sound.2 _ (exhausted ran)⟩

end Runs

end AnthillModKbSpec.P0
