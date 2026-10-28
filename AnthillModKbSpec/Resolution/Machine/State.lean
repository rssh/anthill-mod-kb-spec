import AnthillModKbSpec.Resolution.Machine.Evidence
import AnthillModKbSpec.Resolution.Machine.Instantiation

namespace AnthillModKbSpec.Machine

variable {Variable Literal Symbol Certificate Snapshot : Type}

/-- One candidate way to establish a focused obligation: a rule application with
its explicit parameters, the fresh flexible names it introduces, the answer
bindings it commits, and its premises. All premises must be proved (AND); the
candidates a command returns are alternatives (OR). Opening an expansion proves
nothing yet: its node is built only after every premise has a subproof. -/
structure Expansion (Variable Literal Symbol Certificate : Type) where
  rule : RuleApp Variable Literal Symbol Certificate
  flexibles : List Variable := []
  bindings : List (Variable × Term Variable Literal Symbol) := []
  premises : List (Premise Variable Literal Symbol) := []

/-- Rigid names opened for the premises; each is scoped to its own premise. -/
def Expansion.rigids (expansion : Expansion Variable Literal Symbol Certificate) : List Variable :=
  expansion.premises.flatMap (fun premise => premise.discharge.rigids)

/-- What a command answers for a focused obligation and the current store.
`candidates []` is a miss for this path. `unsupported` means the command has no
capability for this focus: the path is abandoned and recorded as a gap, and is
never treated as failure of the goal. -/
inductive Response (Variable Literal Symbol Certificate : Type) where
  | candidates (alternatives : List (Expansion Variable Literal Symbol Certificate))
  | unsupported

/-- A command reads the focused obligation and the shared store. Concrete
commands (S06 onward) choose clauses, matches, and fresh names; the machine
checks names and bindings and manages continuations and rollback. A command is
built for one snapshot, and its closed-world nodes are relative to it. -/
abbrev Command (Variable Literal Symbol Certificate : Type) :=
  Obligation Variable Literal Symbol → Store Variable Literal Symbol → Response Variable Literal Symbol Certificate

/-- A partially completed rule application (a continuation frame). `before`
are the premises already proved, with subproofs `done` in the same order;
`current` is being proved and `pending` follow. -/
structure Frame (Variable Literal Symbol Certificate : Type) where
  parent : Obligation Variable Literal Symbol
  rule : RuleApp Variable Literal Symbol Certificate
  before : List (Premise Variable Literal Symbol)
  done : List (ProofTree Variable Literal Symbol Certificate)
  current : Premise Variable Literal Symbol
  pending : List (Premise Variable Literal Symbol)

/-- A saved alternative point: the remaining candidates for an obligation and
the store and frames to restore before trying the next one. -/
structure ChoicePoint (Variable Literal Symbol Certificate : Type) where
  obligation : Obligation Variable Literal Symbol
  alternatives : List (Expansion Variable Literal Symbol Certificate)
  store : Store Variable Literal Symbol
  frames : List (Frame Variable Literal Symbol Certificate)

inductive GapReason where
  /-- The command had no capability for the focus. -/
  | unsupported
  /-- A candidate broke the machine's name or binding contract. -/
  | contract
  deriving DecidableEq, Repr

/-- A path abandoned without evidence either way. -/
structure Gap (Variable Literal Symbol : Type) where
  reason : GapReason
  obligation : Obligation Variable Literal Symbol

/-- The machine's current focus: an obligation to expand, a subproof to return
to the innermost frame, or failure of the current path. -/
inductive Focus (Variable Literal Symbol Certificate : Type) where
  | solve (obligation : Obligation Variable Literal Symbol)
  | proved (tree : ProofTree Variable Literal Symbol Certificate)
  | failed

/-- The abstract machine state. `frames` is the success continuation,
`choices` the failure continuation. `gaps` survives backtracking, so a run that
abandoned any path for lack of capability cannot report exhaustion. -/
structure State (Variable Literal Symbol Certificate Snapshot : Type) where
  snapshot : Snapshot
  root : Obligation Variable Literal Symbol
  store : Store Variable Literal Symbol
  focus : Focus Variable Literal Symbol Certificate
  frames : List (Frame Variable Literal Symbol Certificate)
  choices : List (ChoicePoint Variable Literal Symbol Certificate)
  gaps : List (Gap Variable Literal Symbol)

/-- Outcomes. Only `success` carries a proof, and it carries a state from which
search resumes for further answers. `exhausted` means every alternative of this
command strategy was tried with no gap: it is not complete failure (S07 needs a
`GroundSearch.Fails` certificate for that), non-derivability, or refutation.
`unknown` and `interrupted` give no evidence either way. -/
inductive Outcome (Variable Literal Symbol Certificate Snapshot : Type) where
  | success (proof : CompletedProof Variable Literal Symbol Certificate Snapshot) (resume : State Variable Literal Symbol Certificate Snapshot)
  | exhausted
  | unknown (gaps : List (Gap Variable Literal Symbol))
  | interrupted (state : State Variable Literal Symbol Certificate Snapshot)

inductive OutcomeKind where
  | success | exhausted | unknown | interrupted
  deriving DecidableEq, Repr

def Outcome.kind : Outcome Variable Literal Symbol Certificate Snapshot → OutcomeKind
  | .success _ _ => .success
  | .exhausted => .exhausted
  | .unknown _ => .unknown
  | .interrupted _ => .interrupted

def Outcome.proof? : Outcome Variable Literal Symbol Certificate Snapshot → Option (CompletedProof Variable Literal Symbol Certificate Snapshot)
  | .success proof _ => some proof
  | _ => none

/-- Unsuccessful and incomplete outcomes never carry a proof tree. -/
theorem Outcome.proof?_eq_some {outcome : Outcome Variable Literal Symbol Certificate Snapshot}
    {proof : CompletedProof Variable Literal Symbol Certificate Snapshot} (found : outcome.proof? = some proof) :
    ∃ resume, outcome = .success proof resume := by
  cases outcome with
  | success found' resume => cases found; exact ⟨resume, rfl⟩
  | _ => cases found

inductive Status (Variable Literal Symbol Certificate Snapshot : Type) where
  | running (state : State Variable Literal Symbol Certificate Snapshot)
  | finished (outcome : Outcome Variable Literal Symbol Certificate Snapshot)

/-! ## Frames: completion exactly once -/

namespace Frame

def start (parent : Obligation Variable Literal Symbol) (rule : RuleApp Variable Literal Symbol Certificate)
    (premise : Premise Variable Literal Symbol) (pending : List (Premise Variable Literal Symbol)) :
    Frame Variable Literal Symbol Certificate :=
  ⟨parent, rule, [], [], premise, pending⟩

/-- The obligation currently being proved: built from the parent scope alone. -/
def focus (frame : Frame Variable Literal Symbol Certificate) : Obligation Variable Literal Symbol :=
  frame.parent.premise frame.current

def premises (frame : Frame Variable Literal Symbol Certificate) : List (Premise Variable Literal Symbol) :=
  frame.before ++ frame.current :: frame.pending

inductive Received (Variable Literal Symbol Certificate : Type) where
  | complete (tree : ProofTree Variable Literal Symbol Certificate)
  | waiting (frame : Frame Variable Literal Symbol Certificate)

/-- Accept the subproof of the current premise; `step` applies this to every
returning subproof. The parent node is built when the last premise is proved,
from all premises and subproofs in order. -/
def receive (frame : Frame Variable Literal Symbol Certificate) (tree : ProofTree Variable Literal Symbol Certificate) :
    Received Variable Literal Symbol Certificate :=
  match frame.pending with
  | [] => .complete (.node frame.rule frame.parent (frame.before ++ [frame.current]) (frame.done ++ [tree]))
  | next :: rest =>
      .waiting
        { frame with
          before := frame.before ++ [frame.current]
          done := frame.done ++ [tree]
          current := next
          pending := rest }

inductive Fed (Variable Literal Symbol Certificate : Type) where
  | complete (tree : ProofTree Variable Literal Symbol Certificate)
  | waiting (frame : Frame Variable Literal Symbol Certificate)
  /-- A subproof arrived after completion; the machine never does this, since a
  completed frame is removed. -/
  | overfull

/-- `receive` iterated over a sequence of subproofs. -/
def feed (frame : Frame Variable Literal Symbol Certificate) : List (ProofTree Variable Literal Symbol Certificate) → Fed Variable Literal Symbol Certificate
  | [] => .waiting frame
  | tree :: trees =>
      match frame.receive tree with
      | .complete node => if trees.isEmpty then .complete node else .overfull
      | .waiting next => next.feed trees

theorem receive_waiting {frame next : Frame Variable Literal Symbol Certificate}
    {tree : ProofTree Variable Literal Symbol Certificate} (waiting : frame.receive tree = .waiting next) :
    next.parent = frame.parent ∧ next.rule = frame.rule ∧ next.premises = frame.premises ∧
      next.before = frame.before ++ [frame.current] ∧ next.done = frame.done ++ [tree] ∧
      next.pending.length + 1 = frame.pending.length := by
  obtain ⟨parent, rule, before, done, current, pending⟩ := frame
  cases pending with
  | nil => simp [receive] at waiting
  | cons following rest =>
      simp only [receive, Received.waiting.injEq] at waiting
      subst waiting
      simp [premises]

theorem receive_complete {frame : Frame Variable Literal Symbol Certificate}
    {tree node : ProofTree Variable Literal Symbol Certificate} (complete : frame.receive tree = .complete node) :
    frame.pending = [] ∧ node = .node frame.rule frame.parent frame.premises (frame.done ++ [tree]) := by
  obtain ⟨parent, rule, before, done, current, pending⟩ := frame
  cases pending with
  | nil =>
      simp only [receive, Received.complete.injEq] at complete
      subst complete
      simp [premises]
  | cons following rest => simp [receive] at complete

/-- With exactly one subproof per remaining premise, the frame completes, and
its node lists every premise with its own subproof. -/
theorem feed_exact (frame : Frame Variable Literal Symbol Certificate) (trees : List (ProofTree Variable Literal Symbol Certificate))
    (count : trees.length = frame.pending.length + 1) :
    frame.feed trees = .complete (.node frame.rule frame.parent frame.premises (frame.done ++ trees)) := by
  induction trees generalizing frame with
  | nil => simp at count
  | cons tree trees ih =>
      obtain ⟨parent, rule, before, done, current, pending⟩ := frame
      cases pending with
      | nil =>
          simp only [List.length_cons, List.length_nil, Nat.add_right_cancel_iff,
            List.length_eq_zero_iff] at count
          subst trees
          simp [feed, receive, premises]
      | cons following rest =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at count
          simp only [feed, receive]
          rw [ih _ count]
          simp [premises]

/-- With fewer subproofs, the frame is still waiting: the parent is not
completed early. -/
theorem feed_partial (frame : Frame Variable Literal Symbol Certificate) (trees : List (ProofTree Variable Literal Symbol Certificate))
    (count : trees.length ≤ frame.pending.length) :
    ∃ next, frame.feed trees = .waiting next ∧ next.parent = frame.parent ∧
      next.premises = frame.premises ∧ next.done = frame.done ++ trees := by
  induction trees generalizing frame with
  | nil => exact ⟨frame, rfl, rfl, rfl, by simp⟩
  | cons tree trees ih =>
      obtain ⟨parent, rule, before, done, current, pending⟩ := frame
      cases pending with
      | nil => simp at count
      | cons following rest =>
          simp only [List.length_cons, Nat.add_le_add_iff_right] at count
          obtain ⟨next, fed, sameParent, samePremises, sameDone⟩ :=
            ih ⟨parent, rule, before ++ [current], done ++ [tree], following, rest⟩ count
          refine ⟨next, ?_, sameParent, ?_, ?_⟩
          · simpa [feed, receive] using fed
          · rw [samePremises]; simp [premises]
          · rw [sameDone]; simp

/-- A frame cannot complete twice: further subproofs after completion are
rejected. -/
theorem feed_overfull (frame : Frame Variable Literal Symbol Certificate) (trees : List (ProofTree Variable Literal Symbol Certificate))
    (count : frame.pending.length + 1 < trees.length) : frame.feed trees = .overfull := by
  induction trees generalizing frame with
  | nil => simp at count
  | cons tree trees ih =>
      obtain ⟨parent, rule, before, done, current, pending⟩ := frame
      cases pending with
      | nil =>
          cases trees with
          | nil => simp at count
          | cons _ _ => simp [feed, receive]
      | cons following rest =>
          simp only [List.length_cons, Nat.add_lt_add_iff_right] at count
          simp only [feed, receive]
          exact ih _ count

end Frame

/-! ## Machine invariant, independent of the command -/

/-- The obligation the focus or the innermost frame is working on. -/
def expected (root : Obligation Variable Literal Symbol) :
    List (Frame Variable Literal Symbol Certificate) → Obligation Variable Literal Symbol
  | [] => root
  | frame :: _ => frame.focus

/-- Each frame continues the obligation of the frame below it, and its
completed subproofs prove exactly its completed premises. -/
inductive Linked (root : Obligation Variable Literal Symbol) : List (Frame Variable Literal Symbol Certificate) → Prop where
  | nil : Linked root []
  | cons {frame : Frame Variable Literal Symbol Certificate} {frames : List (Frame Variable Literal Symbol Certificate)}
      (parent : frame.parent = expected root frames)
      (children : ProofTree.CoherentPremises frame.parent frame.before frame.done)
      (rest : Linked root frames) : Linked root (frame :: frames)

def Focus.Valid (root : Obligation Variable Literal Symbol) (frames : List (Frame Variable Literal Symbol Certificate)) :
    Focus Variable Literal Symbol Certificate → Prop
  | .solve obligation => obligation = expected root frames
  | .proved tree => tree.obligation = expected root frames ∧ tree.Coherent
  | .failed => True

theorem Frame.receive_valid {frame : Frame Variable Literal Symbol Certificate} {tree : ProofTree Variable Literal Symbol Certificate}
    (children : ProofTree.CoherentPremises frame.parent frame.before frame.done)
    (opened : tree.obligation = frame.focus) (coherent : tree.Coherent) :
    (∀ node, frame.receive tree = .complete node → node.obligation = frame.parent ∧ node.Coherent) ∧
      ∀ next, frame.receive tree = .waiting next →
        next.parent = frame.parent ∧ ProofTree.CoherentPremises next.parent next.before next.done := by
  have extended := children.snoc opened coherent
  constructor
  · intro node complete
    obtain ⟨parent, rule, before, done, current, pending⟩ := frame
    cases pending with
    | nil => cases complete; exact ⟨rfl, .node extended⟩
    | cons _ _ => cases complete
  · intro next waiting
    obtain ⟨sameParent, _, _, sameBefore, sameDone, _⟩ := Frame.receive_waiting waiting
    rw [sameParent, sameBefore, sameDone]
    exact ⟨rfl, extended⟩

variable [DecidableEq Variable]

/-- The name invariant for a frame: its parent, every premise obligation, and
every completed subproof name only names declared in `store`. -/
structure Frame.Declared (store : Store Variable Literal Symbol) (frame : Frame Variable Literal Symbol Certificate) :
    Prop where
  parent : frame.parent.Declared store
  premises : ∀ premise ∈ frame.premises, (frame.parent.premise premise).Declared store
  done : ∀ tree ∈ frame.done, tree.Declared store

def Focus.Declared (store : Store Variable Literal Symbol) : Focus Variable Literal Symbol Certificate → Prop
  | .solve obligation => obligation.Declared store
  | .proved tree => tree.Declared store
  | .failed => True

theorem ProofTree.Declared.refines {store later : Store Variable Literal Symbol}
    {tree : ProofTree Variable Literal Symbol Certificate} (declared : tree.Declared store)
    (refines : store.Refines later) : tree.Declared later :=
  declared.mono fun _ present => refines.declared present

theorem Frame.Declared.refines {store later : Store Variable Literal Symbol}
    {frame : Frame Variable Literal Symbol Certificate} (declared : frame.Declared store)
    (refines : store.Refines later) : frame.Declared later :=
  ⟨declared.parent.refines refines, fun premise member => (declared.premises premise member).refines refines,
    fun tree member => (declared.done tree member).refines refines⟩

theorem Frame.receive_declared {store : Store Variable Literal Symbol}
    {frame : Frame Variable Literal Symbol Certificate} {tree : ProofTree Variable Literal Symbol Certificate}
    (declared : frame.Declared store) (proved : tree.Declared store) :
    (∀ node, frame.receive tree = .complete node → node.Declared store) ∧
      ∀ next, frame.receive tree = .waiting next → next.Declared store ∧ next.focus.Declared store := by
  have children : ∀ child ∈ frame.done ++ [tree], child.Declared store := fun child member => by
    rcases List.mem_append.mp member with done | last
    · exact declared.done child done
    · rw [List.mem_singleton.mp last]; exact proved
  constructor
  · intro node complete
    obtain ⟨_, rfl⟩ := Frame.receive_complete complete
    exact ProofTree.Declared.node declared.parent declared.premises children
  · intro next waiting
    obtain ⟨sameParent, _, samePremises, _, sameDone, _⟩ := Frame.receive_waiting waiting
    have nextDeclared : next.Declared store :=
      ⟨sameParent ▸ declared.parent, by rw [samePremises, sameParent]; exact declared.premises,
        by rw [sameDone]; exact children⟩
    exact ⟨nextDeclared, nextDeclared.premises next.current (by simp [Frame.premises])⟩

/-- A saved alternative point is linked like the state it was saved from, and
its obligation and frames name only names declared in its saved store. -/
structure ChoicePoint.Valid (root : Obligation Variable Literal Symbol)
    (point : ChoicePoint Variable Literal Symbol Certificate) : Prop where
  store : point.store.Scoped
  linked : Linked root point.frames
  obligation : point.obligation = expected root point.frames
  declared : point.obligation.Declared point.store
  frames : ∀ frame ∈ point.frames, frame.Declared point.store

/-- Scope coherence of the whole state and its saved alternatives, the store's
dependency invariant, and the name invariant: every free name of the focus and
of every frame is declared in the store. -/
structure State.Valid (state : State Variable Literal Symbol Certificate Snapshot) : Prop where
  store : state.store.Scoped
  linked : Linked state.root state.frames
  focus : state.focus.Valid state.root state.frames
  choices : ∀ point ∈ state.choices, point.Valid state.root
  declared : state.focus.Declared state.store
  frames : ∀ frame ∈ state.frames, frame.Declared state.store

/-! ## Transitions -/

/-- Save the remaining candidates, if any, with the store and frames to restore. -/
def State.save (state : State Variable Literal Symbol Certificate Snapshot) (obligation : Obligation Variable Literal Symbol)
    (rest : List (Expansion Variable Literal Symbol Certificate)) : List (ChoicePoint Variable Literal Symbol Certificate) :=
  match rest with
  | [] => state.choices
  | _ :: _ => ⟨obligation, rest, state.store, state.frames⟩ :: state.choices

/-- Try one candidate for an obligation, keeping `rest` as alternatives. A
candidate without premises completes the obligation at once; otherwise its
first premise becomes the focus under a new frame. -/
def State.enter (state : State Variable Literal Symbol Certificate Snapshot) (obligation : Obligation Variable Literal Symbol)
    (expansion : Expansion Variable Literal Symbol Certificate) (rest : List (Expansion Variable Literal Symbol Certificate)) :
    State Variable Literal Symbol Certificate Snapshot :=
  let saved := { state with choices := state.save obligation rest }
  match state.store.commit obligation expansion.flexibles expansion.rigids expansion.premises expansion.bindings with
  | .rejected => { saved with focus := .failed }
  | .violated => { saved with focus := .failed, gaps := ⟨.contract, obligation⟩ :: state.gaps }
  | .committed store =>
      match expansion.premises with
      | [] => { saved with store := store, focus := .proved (.node expansion.rule obligation [] []) }
      | premise :: pending =>
          { saved with
            store := store
            frames := Frame.start obligation expansion.rule premise pending :: state.frames
            focus := .solve (obligation.premise premise) }

/-- One machine transition. A proved subtree returns to the innermost frame;
a failed path resumes the newest choice point from its saved store and frames. -/
def step (command : Command Variable Literal Symbol Certificate) (state : State Variable Literal Symbol Certificate Snapshot) :
    Status Variable Literal Symbol Certificate Snapshot :=
  match state.focus with
  | .solve obligation =>
      match command obligation state.store with
      | .candidates [] => .running { state with focus := .failed }
      | .candidates (expansion :: rest) => .running (state.enter obligation expansion rest)
      | .unsupported =>
          .running { state with focus := .failed, gaps := ⟨.unsupported, obligation⟩ :: state.gaps }
  | .proved tree =>
      match state.frames with
      | [] => .finished (.success ⟨state.snapshot, state.root, tree, state.store⟩ { state with focus := .failed })
      | frame :: frames =>
          match frame.receive tree with
          | .complete node => .running { state with frames := frames, focus := .proved node }
          | .waiting next => .running { state with frames := next :: frames, focus := .solve next.focus }
  | .failed =>
      match state.choices with
      | [] => .finished (if state.gaps.isEmpty then .exhausted else .unknown state.gaps)
      | point :: choices =>
          match point.alternatives with
          | [] => .running { state with choices := choices }
          | expansion :: rest =>
              .running
                ({ state with store := point.store, frames := point.frames, choices := choices }.enter
                  point.obligation expansion rest)

/-- Run with a step budget. Running out of budget is an interruption, not a
result about the goal. -/
def run (command : Command Variable Literal Symbol Certificate) :
    Nat → State Variable Literal Symbol Certificate Snapshot → Outcome Variable Literal Symbol Certificate Snapshot
  | 0, state => .interrupted state
  | fuel + 1, state =>
      match step command state with
      | .running next => run command fuel next
      | .finished outcome => outcome

/-- The query's free names other than its answer names are its rigid parameters. -/
def rootRigids (flexibles : List Variable) (context : ProofContext Variable Literal Symbol)
    (goal : Formula Variable Literal Symbol) : List Variable :=
  (goal.freeVars ++ context.flatMap Term.freeVars).filter (fun name => decide (name ∉ flexibles))

/-- Start a query. Every free name of the context and goal is declared: the
`flexibles` as answer names depending on the query's parameters, all others as
rigid parameters. -/
def State.init (snapshot : Snapshot) (flexibles : List Variable) (context : ProofContext Variable Literal Symbol)
    (goal : Formula Variable Literal Symbol) : State Variable Literal Symbol Certificate Snapshot :=
  let rigids := rootRigids flexibles context goal
  let root := Obligation.root rigids context goal
  ⟨snapshot, root, ⟨rigids.map (fun name => (name, .rigid)) ++
    flexibles.map (fun name => (name, .flexible rigids)), []⟩, .solve root, [], [], []⟩

/-! ## Invariant preservation -/

theorem State.init_valid (snapshot : Snapshot) (flexibles : List Variable)
    (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    (State.init (Certificate := Certificate) snapshot flexibles context goal).Valid := by
  refine ⟨⟨?_, by simp [State.init], .nil⟩, .nil, rfl, by simp [State.init], ?_, by simp [State.init]⟩
  · intro name dependencies infoEq rigid member
    have found := lookup_mem infoEq
    simp only [State.init, List.mem_append, List.mem_map, Prod.mk.injEq] at found
    rcases found with ⟨_, _, _, impossible⟩ | ⟨_, _, _, same⟩
    · cases impossible
    · cases same
      exact lookup_declared _ _ _ _ member
  · -- Every free name of the query is declared: an answer name flexible, any other rigid.
    intro name member
    simp only [State.init, Obligation.root, Obligation.freeVars, Obligation.context] at member ⊢
    rw [Store.info?, ← Option.isSome_iff_ne_none]
    by_cases rigid : name ∈ rootRigids flexibles context goal
    · exact lookup_isSome_of_mem (List.mem_append_left _ (List.mem_map.mpr ⟨name, rigid, rfl⟩))
    · have flexible : name ∈ flexibles := by
        by_cases inside : name ∈ flexibles
        · exact inside
        · exact absurd (List.mem_filter.mpr ⟨member, by simpa using inside⟩) rigid
      exact lookup_isSome_of_mem (List.mem_append_right _ (List.mem_map.mpr ⟨name, flexible, rfl⟩))

theorem State.save_valid {state : State Variable Literal Symbol Certificate Snapshot}
    {obligation : Obligation Variable Literal Symbol} {rest : List (Expansion Variable Literal Symbol Certificate)}
    (valid : state.Valid) (focus : obligation = expected state.root state.frames)
    (declared : obligation.Declared state.store) :
    ∀ point ∈ state.save obligation rest, point.Valid state.root := by
  cases rest with
  | nil => exact valid.choices
  | cons _ _ =>
      intro point member
      simp only [State.save, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨valid.store, valid.linked, focus, declared, valid.frames⟩
      · exact valid.choices point member

theorem State.enter_valid {state : State Variable Literal Symbol Certificate Snapshot}
    {obligation : Obligation Variable Literal Symbol} {expansion : Expansion Variable Literal Symbol Certificate}
    {rest : List (Expansion Variable Literal Symbol Certificate)} (valid : state.Valid)
    (focus : obligation = expected state.root state.frames) (declared : obligation.Declared state.store) :
    (state.enter obligation expansion rest).Valid := by
  have saved := State.save_valid (rest := rest) valid focus declared
  unfold State.enter
  split
  · exact ⟨valid.store, valid.linked, trivial, saved, trivial, valid.frames⟩
  · exact ⟨valid.store, valid.linked, trivial, saved, trivial, valid.frames⟩
  · rename_i store committed
    have committedValid := Store.commit_scoped valid.store committed
    obtain ⟨parentDeclared, premisesDeclared⟩ := Store.commit_declared committed declared
    have frames : ∀ frame ∈ state.frames, frame.Declared store :=
      fun frame member => (valid.frames frame member).refines (Store.commit_refines committed)
    split
    · exact ⟨committedValid, valid.linked, ⟨focus, .node .nil⟩, saved,
        ProofTree.Declared.node parentDeclared (by simp) (by simp), frames⟩
    · rename_i premise pending premisesEq
      refine ⟨committedValid, .cons focus .nil valid.linked, rfl, saved,
        premisesDeclared premise (by simp [premisesEq]), fun frame member => ?_⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨parentDeclared, fun other inside => premisesDeclared other
          (by simpa [Frame.start, Frame.premises, premisesEq] using inside), by simp [Frame.start]⟩
      · exact frames frame member

theorem State.enter_root (state : State Variable Literal Symbol Certificate Snapshot)
    (obligation : Obligation Variable Literal Symbol) (expansion : Expansion Variable Literal Symbol Certificate)
    (rest : List (Expansion Variable Literal Symbol Certificate)) :
    (state.enter obligation expansion rest).root = state.root := by
  unfold State.enter
  split <;> (try split) <;> rfl

theorem State.enter_gaps (state : State Variable Literal Symbol Certificate Snapshot)
    (obligation : Obligation Variable Literal Symbol) (expansion : Expansion Variable Literal Symbol Certificate)
    (rest : List (Expansion Variable Literal Symbol Certificate)) :
    ∃ added, (state.enter obligation expansion rest).gaps = added ++ state.gaps := by
  unfold State.enter
  split
  · exact ⟨[], rfl⟩
  · exact ⟨[_], rfl⟩
  · split <;> exact ⟨[], rfl⟩

/-- Entering a candidate either keeps the store's bindings or adds some of that
candidate's bindings. -/
theorem State.enter_store (state : State Variable Literal Symbol Certificate Snapshot)
    (obligation : Obligation Variable Literal Symbol) (expansion : Expansion Variable Literal Symbol Certificate)
    (rest : List (Expansion Variable Literal Symbol Certificate)) :
    ∃ added, (state.enter obligation expansion rest).store.bindings = added ++ state.store.bindings ∧
      ∀ binding ∈ added, binding ∈ expansion.bindings := by
  unfold State.enter
  split
  · exact ⟨[], rfl, by simp⟩
  · exact ⟨[], rfl, by simp⟩
  · rename_i store committed
    split <;> exact Store.commit_extends committed

/-- Every transition preserves the invariant, whatever the command answers. -/
theorem step_valid (command : Command Variable Literal Symbol Certificate)
    {state next : State Variable Literal Symbol Certificate Snapshot} (valid : state.Valid)
    (stepped : step command state = .running next) : next.Valid ∧ next.root = state.root := by
  have focusValid := valid.focus
  have focusDeclared := valid.declared
  unfold step at stepped
  split at stepped
  · rename_i obligation focusEq
    rw [focusEq] at focusValid focusDeclared
    split at stepped
    · cases stepped; exact ⟨⟨valid.store, valid.linked, trivial, valid.choices, trivial, valid.frames⟩, rfl⟩
    · cases stepped
      exact ⟨State.enter_valid valid focusValid focusDeclared, State.enter_root _ _ _ _⟩
    · cases stepped; exact ⟨⟨valid.store, valid.linked, trivial, valid.choices, trivial, valid.frames⟩, rfl⟩
  · rename_i tree focusEq
    rw [focusEq] at focusValid focusDeclared
    obtain ⟨opened, coherent⟩ := focusValid
    split at stepped
    · cases stepped
    · rename_i frame frames framesEq
      have linked := valid.linked
      have framesDeclared := valid.frames
      rw [framesEq] at linked opened framesDeclared
      have rest : ∀ other ∈ frames, other.Declared state.store :=
        fun other member => framesDeclared other (List.mem_cons_of_mem _ member)
      have received := Frame.receive_declared (framesDeclared frame List.mem_cons_self) focusDeclared
      cases linked with
      | cons parent children restLinked =>
          have receivedValid := Frame.receive_valid children opened coherent
          split at stepped
          · rename_i node complete
            cases stepped
            obtain ⟨nodeObligation, nodeCoherent⟩ := receivedValid.1 node complete
            exact ⟨⟨valid.store, restLinked, ⟨nodeObligation.trans parent, nodeCoherent⟩, valid.choices,
              received.1 node complete, rest⟩, rfl⟩
          · rename_i waiting frameWaiting
            cases stepped
            obtain ⟨sameParent, nextChildren⟩ := receivedValid.2 waiting frameWaiting
            obtain ⟨nextDeclared, nextFocus⟩ := received.2 waiting frameWaiting
            refine ⟨⟨valid.store, .cons (sameParent.trans parent) nextChildren restLinked, rfl, valid.choices,
              nextFocus, fun other member => ?_⟩, rfl⟩
            rcases List.mem_cons.mp member with rfl | member
            · exact nextDeclared
            · exact rest other member
  · rename_i focusEq
    split at stepped
    · cases stepped
    · rename_i point others choicesEq
      have pointValid := valid.choices point (by simp [choicesEq])
      have othersValid : ∀ other ∈ others, other.Valid state.root :=
        fun other member => valid.choices other (by simp [choicesEq, member])
      split at stepped
      · cases stepped
        exact ⟨⟨valid.store, valid.linked, by simp [focusEq, Focus.Valid], othersValid,
          by simp [focusEq, Focus.Declared], valid.frames⟩, rfl⟩
      · cases stepped
        exact ⟨State.enter_valid
          (state := { state with store := point.store, frames := point.frames, choices := others })
          ⟨pointValid.store, pointValid.linked, by simp [focusEq, Focus.Valid], othersValid,
            by simp [focusEq, Focus.Declared], pointValid.frames⟩ pointValid.obligation pointValid.declared,
          State.enter_root _ _ _ _⟩

/-- A successful step finishes the root obligation with a coherent tree, a
store satisfying the dependency invariant, and a tree naming only names that
store declares. -/
theorem step_success (command : Command Variable Literal Symbol Certificate)
    {state resume : State Variable Literal Symbol Certificate Snapshot} {proof : CompletedProof Variable Literal Symbol Certificate Snapshot}
    (valid : state.Valid) (stepped : step command state = .finished (.success proof resume)) :
    proof.root = state.root ∧ proof.tree.obligation = state.root ∧ proof.tree.Coherent ∧
      proof.store.Scoped ∧ proof.tree.Declared proof.store ∧ resume.Valid ∧ resume.root = state.root := by
  have focusValid := valid.focus
  have focusDeclared := valid.declared
  unfold step at stepped
  split at stepped
  · split at stepped <;> cases stepped
  · rename_i tree focusEq
    rw [focusEq] at focusValid focusDeclared
    split at stepped
    · rename_i framesEq
      cases stepped
      rw [framesEq] at focusValid
      exact ⟨rfl, focusValid.1, focusValid.2, valid.store, focusDeclared,
        ⟨valid.store, by rw [framesEq]; exact .nil, trivial, valid.choices, trivial, valid.frames⟩, rfl⟩
    · split at stepped <;> cases stepped
  · split at stepped
    · split at stepped <;> cases stepped
    · split at stepped <;> cases stepped

/-- A completed run proves the original query under the original scope, every
node's subproofs prove exactly its premises under their own scopes, the final
answers satisfy the dependency invariant, and every obligation of the tree
names only names declared in the final store. -/
theorem run_success (command : Command Variable Literal Symbol Certificate) :
    ∀ (fuel : Nat) {state resume : State Variable Literal Symbol Certificate Snapshot}
      {proof : CompletedProof Variable Literal Symbol Certificate Snapshot},
      state.Valid → run command fuel state = .success proof resume →
        proof.root = state.root ∧ proof.tree.obligation = state.root ∧ proof.tree.Coherent ∧
          proof.store.Scoped ∧ proof.tree.Declared proof.store ∧ resume.Valid ∧ resume.root = state.root
  | 0, _, _, _, _, ran => by cases ran
  | fuel + 1, state, resume, proof, valid, ran => by
      unfold run at ran
      split at ran
      · rename_i next stepped
        obtain ⟨nextValid, sameRoot⟩ := step_valid command valid stepped
        rw [← sameRoot]
        exact run_success command fuel nextValid ran
      · rename_i outcome stepped
        subst outcome
        exact step_success command valid stepped

/-! ## Answers, completion, rollback, and gaps -/

/-- The next AND sibling starts from the store the previous sibling left. -/
theorem step_proved_store (command : Command Variable Literal Symbol Certificate)
    {state next : State Variable Literal Symbol Certificate Snapshot} {tree : ProofTree Variable Literal Symbol Certificate}
    (focused : state.focus = .proved tree) (stepped : step command state = .running next) :
    next.store = state.store := by
  unfold step at stepped
  rw [focused] at stepped
  simp only at stepped
  split at stepped
  · cases stepped
  · split at stepped <;> (cases stepped; rfl)

/-- A returning subproof is passed to the innermost frame by `receive`; while
premises remain, the next premise becomes the focus. -/
theorem step_waiting (command : Command Variable Literal Symbol Certificate)
    {state : State Variable Literal Symbol Certificate Snapshot} {tree : ProofTree Variable Literal Symbol Certificate}
    {frame next : Frame Variable Literal Symbol Certificate} {frames : List (Frame Variable Literal Symbol Certificate)}
    (focused : state.focus = .proved tree) (framesEq : state.frames = frame :: frames)
    (waiting : frame.receive tree = .waiting next) :
    step command state = .running { state with frames := next :: frames, focus := .solve next.focus } := by
  simp [step, focused, framesEq, waiting]

/-- When the last premise is proved, the frame is removed and its node is the
focus: the parent completes exactly once. -/
theorem step_complete (command : Command Variable Literal Symbol Certificate)
    {state : State Variable Literal Symbol Certificate Snapshot} {tree : ProofTree Variable Literal Symbol Certificate}
    {frame : Frame Variable Literal Symbol Certificate} {frames : List (Frame Variable Literal Symbol Certificate)}
    (focused : state.focus = .proved tree) (framesEq : state.frames = frame :: frames) (last : frame.pending = []) :
    step command state = .running
      { state with
        frames := frames
        focus := .proved (.node frame.rule frame.parent frame.premises (frame.done ++ [tree])) } := by
  obtain ⟨parent, rule, before, done, current, pending⟩ := frame
  subst last
  simp [step, focused, framesEq, Frame.receive, Frame.premises]

/-- A failed path resumes the newest choice point from its saved store and
frames: bindings made by the failed alternative are discarded. -/
theorem step_backtrack (command : Command Variable Literal Symbol Certificate)
    {state : State Variable Literal Symbol Certificate Snapshot} {point : ChoicePoint Variable Literal Symbol Certificate}
    {choices : List (ChoicePoint Variable Literal Symbol Certificate)}
    {expansion : Expansion Variable Literal Symbol Certificate} {rest : List (Expansion Variable Literal Symbol Certificate)}
    (focused : state.focus = .failed) (choicesEq : state.choices = point :: choices)
    (alternatives : point.alternatives = expansion :: rest) :
    step command state = .running
      ({ state with store := point.store, frames := point.frames, choices := choices }.enter
        point.obligation expansion rest) := by
  simp [step, focused, choicesEq, alternatives]

/-- Gaps are never forgotten, even across backtracking. -/
theorem step_gaps (command : Command Variable Literal Symbol Certificate)
    {state next : State Variable Literal Symbol Certificate Snapshot} (stepped : step command state = .running next) :
    ∃ added, next.gaps = added ++ state.gaps := by
  unfold step at stepped
  split at stepped
  · split at stepped
    · cases stepped; exact ⟨[], rfl⟩
    · cases stepped; exact State.enter_gaps _ _ _ _
    · cases stepped; exact ⟨[_], rfl⟩
  · split at stepped
    · cases stepped
    · split at stepped <;> (cases stepped; exact ⟨[], rfl⟩)
  · split at stepped
    · cases stepped
    · split at stepped
      · cases stepped; exact ⟨[], rfl⟩
      · cases stepped; exact State.enter_gaps _ _ _ _

/-- A run reports exhaustion only if no state on it recorded a gap. -/
theorem run_exhausted (command : Command Variable Literal Symbol Certificate) :
    ∀ (fuel : Nat) {state : State Variable Literal Symbol Certificate Snapshot},
      run command fuel state = .exhausted → state.gaps = []
  | 0, _, ran => by cases ran
  | fuel + 1, state, ran => by
      unfold run at ran
      split at ran
      · rename_i next stepped
        obtain ⟨added, gaps⟩ := step_gaps command stepped
        have empty := run_exhausted command fuel ran
        rw [empty] at gaps
        exact (List.append_eq_nil_iff.mp gaps.symm).2
      · rename_i outcome stepped
        subst outcome
        unfold step at stepped
        split at stepped
        · split at stepped <;> cases stepped
        · split at stepped
          · cases stepped
          · split at stepped <;> cases stepped
        · split at stepped
          · split at stepped
            · rename_i empty
              exact List.isEmpty_iff.mp empty
            · cases stepped
          · split at stepped <;> cases stepped

end AnthillModKbSpec.Machine
