import AnthillModKbSpec.Resolution.Machine.Evidence
import AnthillModKbSpec.Resolution.Machine.Instantiation

namespace AnthillModKbSpec.Machine

variable {Variable Literal Symbol Certificate Snapshot : Type}

/-- One candidate way to establish a focused obligation: a rule application with
its explicit parameters, the fresh flexible names it introduces, the answer
bindings it commits, and its premises. All premises must be proved (AND); the
candidates a strategy returns are alternatives (OR). Opening an expansion proves
nothing yet: its node is built only after every premise has a subproof. -/
structure Expansion (Variable Literal Symbol Certificate : Type) where
  rule : RuleApp Variable Literal Symbol Certificate
  flexibles : List Variable := []
  bindings : List (Variable × Term Variable Literal Symbol) := []
  premises : List (Premise Variable Literal Symbol) := []

/-- Rigid names opened for the premises; each is scoped to its own premise. -/
def Expansion.rigids (expansion : Expansion Variable Literal Symbol Certificate) : List Variable :=
  expansion.premises.flatMap (fun premise => premise.discharge.rigids)

/-- What a strategy answers for a focused obligation and the current store.
`candidates []` is a miss for this path. `unsupported` means the strategy has no
capability for this focus: the path is abandoned and recorded as a gap, and is
never treated as failure of the goal. `incomplete alternatives` is both: the
alternatives are tried as for `candidates`, and the focus is recorded as an
`unsupported` gap for the candidates the strategy could not build, so the run
never reports exhaustion. `delay names` means the obligation cannot
proceed until one of `names` is bound: it is suspended and the enclosing frame
continues as if it were proved. Every name must be a declared, unbound flexible
name, and there must be one; otherwise the answer breaks the contract. -/
inductive Response (Variable Literal Symbol Certificate : Type) where
  | candidates (alternatives : List (Expansion Variable Literal Symbol Certificate))
  | unsupported
  | incomplete (alternatives : List (Expansion Variable Literal Symbol Certificate))
  | delay (names : List Variable)

/-- The candidates a response offers: those of `candidates` and `incomplete`. -/
def Response.alternatives : Response Variable Literal Symbol Certificate → List (Expansion Variable Literal Symbol Certificate)
  | .candidates alternatives | .incomplete alternatives => alternatives
  | .unsupported | .delay _ => []

/-- A strategy reads the focused obligation and the shared store and proposes
what to do with it: candidate rule applications, a delay, or a gap. Concrete
strategies (S06 onward) choose clauses, matches, and fresh names; the machine
checks names and bindings and manages continuations and rollback. A strategy is
built for one snapshot, and its closed-world nodes are relative to it. -/
abbrev Strategy (Variable Literal Symbol Certificate : Type) :=
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

inductive GapReason where
  /-- The strategy had no capability for the focus. -/
  | unsupported
  /-- A candidate or a delay broke the machine's name or binding contract. -/
  | contract
  /-- A delayed goal or an unresolved constraint was still pending when the
  branch would have succeeded. -/
  | floundered
  deriving DecidableEq, Repr

/-- A path abandoned without evidence either way. -/
structure Gap (Variable Literal Symbol : Type) where
  reason : GapReason
  obligation : Obligation Variable Literal Symbol

/-- The machine's current focus: an obligation to expand, a subproof to return
to the innermost continuation, or failure of the current path. -/
inductive Focus (Variable Literal Symbol Certificate : Type) where
  | solve (obligation : Obligation Variable Literal Symbol)
  | proved (tree : ProofTree Variable Literal Symbol Certificate)
  | failed

/-- An entry of the success continuation: a rule frame (the AND continuation),
or a woken delayed goal. `woken id obligation next` records the proof of the
woken obligation under `id`, then resumes `next`, the focus the waking commit
would otherwise have taken. -/
inductive Continuation (Variable Literal Symbol Certificate : Type) where
  | frame (frame : Frame Variable Literal Symbol Certificate)
  | woken (id : Nat) (obligation : Obligation Variable Literal Symbol) (next : Focus Variable Literal Symbol Certificate)

/-- A saved alternative point: the remaining candidates for an obligation and
the store, continuations, and deferred proofs to restore before trying the
next one. -/
structure ChoicePoint (Variable Literal Symbol Certificate : Type) where
  obligation : Obligation Variable Literal Symbol
  alternatives : List (Expansion Variable Literal Symbol Certificate)
  store : Store Variable Literal Symbol
  frames : List (Continuation Variable Literal Symbol Certificate)
  deferred : List (DeferredProof Variable Literal Symbol Certificate)

/-- The abstract machine state. `frames` is the success continuation,
`choices` the failure continuation. `gaps` survives backtracking, so a run that
abandoned any path for lack of capability, or floundered, cannot report
exhaustion. `deferred` holds the proofs of woken goals and is restored on
backtracking; `nextHole` numbers suspensions and is not, so ids are unique
across the run. -/
structure State (Variable Literal Symbol Certificate Snapshot : Type) where
  snapshot : Snapshot
  root : Obligation Variable Literal Symbol
  store : Store Variable Literal Symbol
  focus : Focus Variable Literal Symbol Certificate
  frames : List (Continuation Variable Literal Symbol Certificate)
  choices : List (ChoicePoint Variable Literal Symbol Certificate)
  gaps : List (Gap Variable Literal Symbol)
  deferred : List (DeferredProof Variable Literal Symbol Certificate)
  nextHole : Nat

/-- Outcomes. Only `success` carries a proof, and it carries a state from which
search resumes for further answers. `exhausted` means every alternative of this
strategy was tried with no gap: it is not complete failure (S07 needs a
`GroundSearch.Fails` certificate for that), non-derivability, or refutation.
`unknown` and `interrupted` give no evidence either way; a floundered branch
makes the outcome `unknown` unless another branch succeeds. -/
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
subproof returning to a frame. The parent node is built when the last premise is proved,
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

/-! ## Machine invariant, independent of the strategy -/

/-- The obligation the focus or the innermost continuation is working on: the
innermost frame's current premise, or the woken obligation. -/
def expected (root : Obligation Variable Literal Symbol) :
    List (Continuation Variable Literal Symbol Certificate) → Obligation Variable Literal Symbol
  | [] => root
  | .frame frame :: _ => frame.focus
  | .woken _ obligation _ :: _ => obligation

def Focus.Valid (root : Obligation Variable Literal Symbol) (frames : List (Continuation Variable Literal Symbol Certificate)) :
    Focus Variable Literal Symbol Certificate → Prop
  | .solve obligation => obligation = expected root frames
  | .proved tree => tree.obligation = expected root frames ∧ tree.Coherent
  | .failed => True

/-- Each frame continues the obligation of the continuation below it, and its
completed subproofs prove exactly its completed premises. A woken entry works on
its own obligation, unrelated to the entries below it, and the focus it resumes
is valid for them. -/
inductive Linked (root : Obligation Variable Literal Symbol) :
    List (Continuation Variable Literal Symbol Certificate) → Prop where
  | nil : Linked root []
  | frame {frame : Frame Variable Literal Symbol Certificate} {frames : List (Continuation Variable Literal Symbol Certificate)}
      (parent : frame.parent = expected root frames)
      (children : ProofTree.CoherentPremises frame.parent frame.before frame.done)
      (rest : Linked root frames) : Linked root (.frame frame :: frames)
  | woken {id : Nat} {obligation : Obligation Variable Literal Symbol} {next : Focus Variable Literal Symbol Certificate}
      {frames : List (Continuation Variable Literal Symbol Certificate)}
      (resumes : next.Valid root frames) (rest : Linked root frames) : Linked root (.woken id obligation next :: frames)

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

theorem Focus.Declared.refines {store later : Store Variable Literal Symbol}
    {focus : Focus Variable Literal Symbol Certificate} (declared : focus.Declared store)
    (refines : store.Refines later) : focus.Declared later := by
  cases focus with
  | solve obligation => exact Obligation.Declared.refines declared refines
  | proved tree => exact ProofTree.Declared.refines declared refines
  | failed => trivial

/-- The name invariant for a continuation: a frame's, or a woken obligation's
and the focus it resumes. -/
def Continuation.Declared (store : Store Variable Literal Symbol) :
    Continuation Variable Literal Symbol Certificate → Prop
  | .frame entry => entry.Declared store
  | .woken _ obligation next => obligation.Declared store ∧ next.Declared store

theorem Continuation.Declared.refines {store later : Store Variable Literal Symbol}
    {continuation : Continuation Variable Literal Symbol Certificate} (declared : continuation.Declared store)
    (refines : store.Refines later) : continuation.Declared later := by
  cases continuation with
  | frame entry => exact Frame.Declared.refines declared refines
  | woken _ obligation next =>
      exact ⟨Obligation.Declared.refines declared.1 refines, Focus.Declared.refines declared.2 refines⟩

theorem DeferredProof.Valid.refines {store later : Store Variable Literal Symbol}
    {record : DeferredProof Variable Literal Symbol Certificate} (valid : record.Valid store)
    (refines : store.Refines later) : record.Valid later :=
  ⟨valid.obligation, valid.coherent, valid.declared.refines refines⟩

/-- The name invariant for what the store holds: every suspended obligation and
every constraint names only names the store declares. -/
def Store.Declared (store : Store Variable Literal Symbol) : Prop :=
  (∀ suspension ∈ store.wakeups, suspension.obligation.Declared store) ∧
    ∀ constraint ∈ store.constraints, constraint.obligation.Declared store

/-! ## Delayed goals: holes and references -/

def Suspension.hole (suspension : Suspension Variable Literal Symbol) : Hole Variable Literal Symbol :=
  (suspension.id, suspension.obligation)

def Focus.refs : Focus Variable Literal Symbol Certificate → List (Hole Variable Literal Symbol)
  | .proved tree => tree.refs
  | _ => []

def Continuation.refs : Continuation Variable Literal Symbol Certificate → List (Hole Variable Literal Symbol)
  | .frame entry => ProofTree.refsOf entry.done
  | .woken _ _ next => next.refs

def Continuation.holes : Continuation Variable Literal Symbol Certificate → List (Hole Variable Literal Symbol)
  | .frame _ => []
  | .woken id obligation _ => [(id, obligation)]

/-- Every suspension id a branch holds, with its obligation: pending in the
store, woken on the continuation stack, or proved. -/
def branchHoles (store : Store Variable Literal Symbol) (frames : List (Continuation Variable Literal Symbol Certificate))
    (deferred : List (DeferredProof Variable Literal Symbol Certificate)) : List (Hole Variable Literal Symbol) :=
  store.wakeups.map Suspension.hole ++ frames.flatMap Continuation.holes ++ deferred.map DeferredProof.hole

/-- Every reference of a branch: in the focus, the continuations, and the
deferred proofs. -/
def branchRefs (focus : Focus Variable Literal Symbol Certificate)
    (frames : List (Continuation Variable Literal Symbol Certificate))
    (deferred : List (DeferredProof Variable Literal Symbol Certificate)) : List (Hole Variable Literal Symbol) :=
  focus.refs ++ frames.flatMap Continuation.refs ++ deferred.flatMap fun record => record.tree.refs

/-- Closes a disjunction from a hypothesis that is a disjunction of some of its
disjuncts, constructively. Used for membership in appended lists after
`simp only [List.mem_append]`. -/
syntax "pick_member " ident : tactic
macro_rules
  | `(tactic| pick_member $h) => `(tactic| first
      | exact $h
      | (cases $h:ident with
          | inl $h => pick_member $h
          | inr $h => pick_member $h)
      | (apply Or.inl; pick_member $h)
      | (apply Or.inr; pick_member $h))

/-- Membership in reference lists that hold the same pieces in another order. -/
syntax "refs_member " ident " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| refs_member $h [$extra,*]) => `(tactic| (
      simp only [branchRefs, Focus.refs, ProofTree.refs, ProofTree.refsOf_append, ProofTree.refsOf, List.append_nil,
        List.nil_append, List.flatMap_cons, Continuation.refs, List.mem_append, $extra,*] at $h:ident ⊢
      pick_member $h))

/-- References point forward: a woken entry's id is below every reference built
above it on the stack, since those are delays created after it woke. -/
def Ordered : List (Hole Variable Literal Symbol) → List (Continuation Variable Literal Symbol Certificate) → Prop
  | _, [] => True
  | above, .frame frame :: rest => Ordered (above ++ ProofTree.refsOf frame.done) rest
  | above, .woken id _ next :: rest => (∀ ref ∈ above, id < ref.1) ∧ Ordered (above ++ next.refs) rest

omit [DecidableEq Variable] in
theorem Ordered.mono {frames : List (Continuation Variable Literal Symbol Certificate)} :
    ∀ {above smaller : List (Hole Variable Literal Symbol)}, Ordered above frames →
      (∀ ref ∈ smaller, ref ∈ above) → Ordered smaller frames := by
  induction frames with
  | nil => intros; trivial
  | cons continuation rest ih =>
      intro above smaller ordered contained
      have extended : ∀ extra : List (Hole Variable Literal Symbol), ∀ ref ∈ smaller ++ extra, ref ∈ above ++ extra :=
        fun extra ref member => by
          rcases List.mem_append.mp member with here | there
          · exact List.mem_append_left _ (contained ref here)
          · exact List.mem_append_right _ there
      cases continuation with
      | frame frame => exact ih ordered (extended _)
      | woken id obligation next =>
          exact ⟨fun ref member => ordered.1 ref (contained ref member), ih ordered.2 (extended _)⟩

omit [DecidableEq Variable] in
/-- A reference newer than every woken entry may be added above all of them. -/
theorem Ordered.extend {frames : List (Continuation Variable Literal Symbol Certificate)} :
    ∀ {above extra : List (Hole Variable Literal Symbol)}, Ordered above frames →
      (∀ ref ∈ extra, ∀ hole ∈ frames.flatMap Continuation.holes, hole.1 < ref.1) → Ordered (above ++ extra) frames := by
  induction frames with
  | nil => intros; trivial
  | cons continuation rest ih =>
      intro above extra ordered newer
      have restNewer : ∀ ref ∈ extra, ∀ hole ∈ rest.flatMap Continuation.holes, hole.1 < ref.1 :=
        fun ref member hole inside => newer ref member hole (by simp only [List.flatMap_cons]; exact List.mem_append_right _ inside)
      have swap : ∀ middle : List (Hole Variable Literal Symbol),
          ∀ ref ∈ above ++ extra ++ middle, ref ∈ above ++ middle ++ extra := fun middle ref member => by
        simp only [List.mem_append] at member ⊢; pick_member member
      cases continuation with
      | frame frame => exact (ih ordered restNewer).mono (swap _)
      | woken id obligation next =>
          refine ⟨fun ref member => ?_, (ih ordered.2 restNewer).mono (swap _)⟩
          rcases List.mem_append.mp member with old | new
          · exact ordered.1 ref old
          · exact newer ref new (id, obligation) (by simp [Continuation.holes])

/-- The delayed-goal bookkeeping of a branch. Every suspension id is held
exactly once, by a pending wakeup, a woken continuation, or a deferred proof,
and is below `bound`; every reference stands for a held id with its obligation;
and references point forward, so no deferred proof references itself, even
through other records. -/
structure Accounted (store : Store Variable Literal Symbol) (focus : Focus Variable Literal Symbol Certificate)
    (frames : List (Continuation Variable Literal Symbol Certificate))
    (deferred : List (DeferredProof Variable Literal Symbol Certificate)) (bound : Nat) : Prop where
  distinct : ((branchHoles store frames deferred).map Prod.fst).Nodup
  bounded : ∀ hole ∈ branchHoles store frames deferred, hole.1 < bound
  resolved : ∀ ref ∈ branchRefs focus frames deferred, ref ∈ branchHoles store frames deferred
  ordered : Ordered focus.refs frames
  acyclic : ∀ record ∈ deferred, ∀ ref ∈ record.tree.refs, record.id < ref.1

omit [DecidableEq Variable] in
/-- The bookkeeping carries over to a branch holding the same holes, fewer
references, and ordered references. -/
theorem Accounted.of_perm {store later : Store Variable Literal Symbol}
    {focus next : Focus Variable Literal Symbol Certificate}
    {frames continued : List (Continuation Variable Literal Symbol Certificate)}
    {deferred recorded : List (DeferredProof Variable Literal Symbol Certificate)} {bound : Nat}
    (accounted : Accounted store focus frames deferred bound)
    (holes : (branchHoles later continued recorded).Perm (branchHoles store frames deferred))
    (refs : ∀ ref ∈ branchRefs next continued recorded, ref ∈ branchRefs focus frames deferred)
    (ordered : Ordered next.refs continued)
    (acyclic : ∀ record ∈ recorded, ∀ ref ∈ record.tree.refs, record.id < ref.1) :
    Accounted later next continued recorded bound :=
  ⟨(holes.map Prod.fst).nodup_iff.mpr accounted.distinct,
    fun hole member => accounted.bounded hole (holes.mem_iff.mp member),
    fun ref member => holes.mem_iff.mpr (accounted.resolved ref (refs ref member)), ordered, acyclic⟩

/-- The invariant of one branch of the search, for the state and for every
saved alternative: the store is scoped and waiting; continuations are linked
to the root and the focus to them; every committed obligation, suspension,
constraint, and deferred proof names only declared names; every deferred proof
proves its obligation; and the delayed-goal bookkeeping holds. -/
structure Branch.Valid (root : Obligation Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (focus : Focus Variable Literal Symbol Certificate) (frames : List (Continuation Variable Literal Symbol Certificate))
    (deferred : List (DeferredProof Variable Literal Symbol Certificate)) (bound : Nat) : Prop where
  storeScoped : store.Scoped
  waiting : store.Waiting
  held : store.Declared
  linked : Linked root frames
  valid : focus.Valid root frames
  declared : focus.Declared store
  continuations : ∀ continuation ∈ frames, continuation.Declared store
  records : ∀ record ∈ deferred, record.Valid store
  accounted : Accounted store focus frames deferred bound

/-- A saved alternative point is a branch focused on its obligation. -/
abbrev ChoicePoint.Valid (root : Obligation Variable Literal Symbol) (bound : Nat)
    (point : ChoicePoint Variable Literal Symbol Certificate) : Prop :=
  Branch.Valid root point.store (.solve point.obligation) point.frames point.deferred bound

/-- The invariant of the whole state: its branch and every saved alternative,
with ids below the run's counter. -/
structure State.Valid (state : State Variable Literal Symbol Certificate Snapshot) : Prop where
  branch : Branch.Valid state.root state.store state.focus state.frames state.deferred state.nextHole
  choices : ∀ point ∈ state.choices, point.Valid state.root state.nextHole

/-! ## Transitions -/

/-- Save the remaining candidates, if any, with the store, continuations, and
deferred proofs to restore. -/
def State.save (state : State Variable Literal Symbol Certificate Snapshot) (obligation : Obligation Variable Literal Symbol)
    (rest : List (Expansion Variable Literal Symbol Certificate)) : List (ChoicePoint Variable Literal Symbol Certificate) :=
  match rest with
  | [] => state.choices
  | _ :: _ => ⟨obligation, rest, state.store, state.frames, state.deferred⟩ :: state.choices

/-- Where a committed candidate continues: a candidate without premises
completes the obligation at once; otherwise its first premise becomes the focus
under a new frame. -/
def Expansion.start (expansion : Expansion Variable Literal Symbol Certificate)
    (obligation : Obligation Variable Literal Symbol) (frames : List (Continuation Variable Literal Symbol Certificate)) :
    Focus Variable Literal Symbol Certificate × List (Continuation Variable Literal Symbol Certificate) :=
  match expansion.premises with
  | [] => (.proved (.node expansion.rule obligation [] []), frames)
  | premise :: pending =>
      (.solve (obligation.premise premise), .frame (Frame.start obligation expansion.rule premise pending) :: frames)

/-- Run woken suspensions before a focus. Each runs under its own scope with a
woken continuation that records its proof and then resumes what follows it.
Woken lists are newest first, so the oldest runs first and the focus the
commit would otherwise have taken runs last. -/
def Continuation.schedule : List (Suspension Variable Literal Symbol) →
    Focus Variable Literal Symbol Certificate × List (Continuation Variable Literal Symbol Certificate) →
    Focus Variable Literal Symbol Certificate × List (Continuation Variable Literal Symbol Certificate)
  | [], next => next
  | suspension :: rest, (focus, frames) =>
      schedule rest (.solve suspension.obligation, .woken suspension.id suspension.obligation focus :: frames)

/-- Try one candidate for an obligation, keeping `rest` as alternatives. The
suspensions its commit wakes run first, then the candidate's own continuation. -/
def State.enter (state : State Variable Literal Symbol Certificate Snapshot) (obligation : Obligation Variable Literal Symbol)
    (expansion : Expansion Variable Literal Symbol Certificate) (rest : List (Expansion Variable Literal Symbol Certificate)) :
    State Variable Literal Symbol Certificate Snapshot :=
  let saved := { state with choices := state.save obligation rest }
  match state.store.commit obligation expansion.flexibles expansion.rigids expansion.premises expansion.bindings with
  | .rejected => { saved with focus := .failed }
  | .violated => { saved with focus := .failed, gaps := ⟨.contract, obligation⟩ :: state.gaps }
  | .committed store woken =>
      let next := Continuation.schedule woken (expansion.start obligation state.frames)
      { saved with store := store, focus := next.1, frames := next.2 }

/-- One machine transition. A delayed obligation is suspended in the store and
stands proved by a reference. A proved subtree returns to the innermost
continuation: a frame records it, a woken entry records it as a deferred proof.
With no continuation left the branch succeeds, filling every reference with
its deferred proof, or flounders when goals are still delayed. A failed path resumes the newest choice point from its saved
store, continuations, and deferred proofs. -/
def step (strategy : Strategy Variable Literal Symbol Certificate) (state : State Variable Literal Symbol Certificate Snapshot) :
    Status Variable Literal Symbol Certificate Snapshot :=
  match state.focus with
  | .solve obligation =>
      match strategy obligation state.store with
      | .candidates [] => .running { state with focus := .failed }
      | .candidates (expansion :: rest) => .running (state.enter obligation expansion rest)
      | .unsupported | .incomplete [] =>
          .running { state with focus := .failed, gaps := ⟨.unsupported, obligation⟩ :: state.gaps }
      | .incomplete (expansion :: rest) =>
          .running ({ state with gaps := ⟨.unsupported, obligation⟩ :: state.gaps }.enter obligation expansion rest)
      | .delay names =>
          if state.store.delayable names then
            .running
              { state with
                store := state.store.suspend ⟨state.nextHole, obligation, names⟩
                focus := .proved (.deferred state.nextHole obligation)
                nextHole := state.nextHole + 1 }
          else .running { state with focus := .failed, gaps := ⟨.contract, obligation⟩ :: state.gaps }
  | .proved tree =>
      match state.frames with
      | [] =>
          match state.store.residual with
          | [] =>
              .finished
                (.success ⟨state.snapshot, state.root, tree.fillAll state.deferred state.deferred.length,
                    state.deferred, state.store⟩
                { state with focus := .failed })
          | pending :: more =>
              .running
                { state with
                  focus := .failed
                  gaps := (pending :: more).map (fun obligation => ⟨.floundered, obligation⟩) ++ state.gaps }
      | .frame frame :: frames =>
          match frame.receive tree with
          | .complete node => .running { state with frames := frames, focus := .proved node }
          | .waiting next => .running { state with frames := .frame next :: frames, focus := .solve next.focus }
      | .woken id obligation next :: frames =>
          .running { state with frames := frames, focus := next, deferred := ⟨id, obligation, tree⟩ :: state.deferred }
  | .failed =>
      match state.choices with
      | [] => .finished (if state.gaps.isEmpty then .exhausted else .unknown state.gaps)
      | point :: choices =>
          match point.alternatives with
          | [] => .running { state with choices := choices }
          | expansion :: rest =>
              .running
                ({ state with
                    store := point.store
                    frames := point.frames
                    deferred := point.deferred
                    choices := choices }.enter point.obligation expansion rest)

/-- Run with a step budget. Running out of budget is an interruption, not a
result about the goal. -/
def run (strategy : Strategy Variable Literal Symbol Certificate) :
    Nat → State Variable Literal Symbol Certificate Snapshot → Outcome Variable Literal Symbol Certificate Snapshot
  | 0, state => .interrupted state
  | fuel + 1, state =>
      match step strategy state with
      | .running next => run strategy fuel next
      | .finished outcome => outcome

/-- The query's free names other than its answer names are its rigid parameters. -/
def rootRigids (flexibles : List Variable) (context : ProofContext Variable Literal Symbol)
    (goal : Formula Variable Literal Symbol) : List Variable :=
  (Obligation.root [] context goal).freeVars.filter (fun name => decide (name ∉ flexibles))

/-- Start a query. Every free name of the context and goal is declared: the
`flexibles` as answer names depending on the query's parameters, all others as
rigid parameters. -/
def State.init (snapshot : Snapshot) (flexibles : List Variable) (context : ProofContext Variable Literal Symbol)
    (goal : Formula Variable Literal Symbol) : State Variable Literal Symbol Certificate Snapshot :=
  let rigids := rootRigids flexibles context goal
  let root := Obligation.root rigids context goal
  { snapshot, root
    store := { names := rigids.map (fun name => (name, .rigid)) ++ flexibles.map (fun name => (name, .flexible rigids))
               bindings := [], wakeups := [], constraints := [] }
    focus := .solve root, frames := [], choices := [], gaps := [], deferred := [], nextHole := 0 }

/-! ## Invariant preservation -/

section Preservation

variable {root : Obligation Variable Literal Symbol} {store : Store Variable Literal Symbol}
  {frames : List (Continuation Variable Literal Symbol Certificate)}
  {deferred : List (DeferredProof Variable Literal Symbol Certificate)} {bound : Nat}

theorem Branch.Valid.raise {focus : Focus Variable Literal Symbol Certificate}
    (valid : Branch.Valid root store focus frames deferred bound) {larger : Nat} (grows : bound ≤ larger) :
    Branch.Valid root store focus frames deferred larger :=
  { valid with
    accounted := { valid.accounted with
      bounded := fun hole member => Nat.lt_of_lt_of_le (valid.accounted.bounded hole member) grows } }

/-- Abandoning the focus keeps the branch valid. -/
theorem Branch.Valid.fail {focus : Focus Variable Literal Symbol Certificate}
    (valid : Branch.Valid root store focus frames deferred bound) :
    Branch.Valid root store .failed frames deferred bound :=
  { valid with
    valid := trivial
    declared := trivial
    accounted := valid.accounted.of_perm (.refl _)
      (fun ref member => by refs_member member [])
      (valid.accounted.ordered.mono fun _ member => by simp [Focus.refs] at member) valid.accounted.acyclic }

/-- A valid delay suspends the focused obligation under the next id; the
reference stands proved for it. -/
theorem Branch.Valid.suspend {obligation : Obligation Variable Literal Symbol} {names : List Variable}
    (valid : Branch.Valid root store (.solve obligation) frames deferred bound) (delayable : store.delayable names = true) :
    Branch.Valid root (store.suspend ⟨bound, obligation, names⟩) (.proved (.deferred bound obligation)) frames deferred
      (bound + 1) := by
  obtain ⟨_, waits⟩ := Store.delayable_spec delayable
  have refines := Store.Refines.suspend store ⟨bound, obligation, names⟩
  have accounted := valid.accounted
  have heldBelow : ∀ hole ∈ branchHoles store frames deferred, hole.1 < bound := accounted.bounded
  have newer : ∀ suspension ∈ store.wakeups, suspension.id < bound := fun suspension member =>
    heldBelow suspension.hole
      (by simp only [branchHoles, List.mem_append]; exact .inl (.inl (List.mem_map.mpr ⟨suspension, member, rfl⟩)))
  have holesEq : branchHoles (store.suspend ⟨bound, obligation, names⟩) frames deferred =
      (bound, obligation) :: branchHoles store frames deferred := by
    simp [branchHoles, Store.suspend, Suspension.hole]
  refine ⟨valid.storeScoped.suspend (fun name member => (waits name member).1) newer, fun suspension member => ?_,
    ⟨fun suspension member => ?_, fun constraint member => (valid.held.2 constraint member).refines refines⟩,
    valid.linked, ⟨valid.valid, .deferred⟩, ProofTree.Declared.deferred (valid.declared.refines refines),
    fun continuation member => (valid.continuations continuation member).refines refines,
    fun record member => (valid.records record member).refines refines, ?_⟩
  · rcases List.mem_cons.mp member with rfl | member
    · exact fun name inside => (waits name inside).2
    · exact valid.waiting suspension member
  · rcases List.mem_cons.mp member with rfl | member
    · exact valid.declared.refines refines
    · exact (valid.held.1 suspension member).refines refines
  · refine ⟨?_, ?_, ?_, ?_, accounted.acyclic⟩
    · rw [holesEq, List.map_cons, List.nodup_cons]
      exact ⟨fun inside => by
          obtain ⟨hole, member, idEq⟩ := List.mem_map.mp inside
          have below := heldBelow hole member
          rw [idEq] at below
          exact Nat.lt_irrefl _ below, accounted.distinct⟩
    · intro hole member
      rw [holesEq] at member
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (heldBelow hole member)
    · intro ref member
      rw [holesEq]
      simp only [branchRefs, Focus.refs, ProofTree.refs, List.mem_append, List.mem_singleton] at member
      rcases member with (rfl | old) | old
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (accounted.resolved ref (by simp [branchRefs, Focus.refs, old]))
      · exact List.mem_cons_of_mem _ (accounted.resolved ref (by simp [branchRefs, Focus.refs, old]))
    · have extended := accounted.ordered.extend (extra := [(bound, obligation)]) fun ref member hole inside => by
        rw [List.mem_singleton.mp member]
        exact heldBelow hole (by simp only [branchHoles, List.mem_append]; exact .inl (.inr inside))
      exact extended.mono fun ref member => by simpa [Focus.refs, ProofTree.refs] using member

/-- A frame receiving a subproof: the last one completes its node, an earlier
one focuses the next premise. -/
theorem Branch.Valid.receive {tree : ProofTree Variable Literal Symbol Certificate}
    {frame : Frame Variable Literal Symbol Certificate}
    (valid : Branch.Valid root store (.proved tree) (.frame frame :: frames) deferred bound) :
    (∀ node, frame.receive tree = .complete node → Branch.Valid root store (.proved node) frames deferred bound) ∧
      ∀ next, frame.receive tree = .waiting next →
        Branch.Valid root store (.solve next.focus) (.frame next :: frames) deferred bound := by
  obtain ⟨opened, coherent⟩ := valid.valid
  have declared := Frame.receive_declared (valid.continuations (.frame frame) List.mem_cons_self) valid.declared
  have below := fun continuation member => valid.continuations continuation (List.mem_cons_of_mem _ member)
  have ordered : Ordered (tree.refs ++ ProofTree.refsOf frame.done) frames := valid.accounted.ordered
  have joined : Ordered (ProofTree.refsOf (frame.done ++ [tree])) frames := ordered.mono fun ref member => by
    refs_member member []
  cases valid.linked with
  | frame parent children rest =>
      have received := Frame.receive_valid children opened coherent
      refine ⟨fun node complete => ?_, fun next waiting => ?_⟩
      · obtain ⟨nodeObligation, nodeCoherent⟩ := received.1 node complete
        obtain ⟨_, rfl⟩ := Frame.receive_complete complete
        exact ⟨valid.storeScoped, valid.waiting, valid.held, rest, ⟨nodeObligation.trans parent, nodeCoherent⟩,
          declared.1 _ complete, below, valid.records,
          valid.accounted.of_perm (by simp [branchHoles, Continuation.holes]) (fun ref member => by refs_member member [])
            joined valid.accounted.acyclic⟩
      · obtain ⟨nextDeclared, nextFocus⟩ := declared.2 next waiting
        obtain ⟨_, _, _, _, sameDone, _⟩ := Frame.receive_waiting waiting
        obtain ⟨sameParent, nextChildren⟩ := received.2 next waiting
        refine ⟨valid.storeScoped, valid.waiting, valid.held, .frame (sameParent.trans parent) nextChildren rest, rfl,
          nextFocus, fun continuation member => ?_, valid.records,
          valid.accounted.of_perm (by simp [branchHoles, Continuation.holes]) (fun ref member => by
            refs_member member [sameDone]) (show Ordered ([] ++ ProofTree.refsOf next.done) frames by
              rw [List.nil_append, sameDone]; exact joined) valid.accounted.acyclic⟩
        rcases List.mem_cons.mp member with rfl | member
        · exact nextDeclared
        · exact below continuation member

/-- A woken goal's proof is recorded under its id, and the focus it interrupted
resumes. Nothing from the woken goal's scope reaches that focus. -/
theorem Branch.Valid.record {tree : ProofTree Variable Literal Symbol Certificate} {id : Nat}
    {obligation : Obligation Variable Literal Symbol} {next : Focus Variable Literal Symbol Certificate}
    (valid : Branch.Valid root store (.proved tree) (.woken id obligation next :: frames) deferred bound) :
    Branch.Valid root store next frames (⟨id, obligation, tree⟩ :: deferred) bound := by
  obtain ⟨opened, coherent⟩ := valid.valid
  obtain ⟨_, nextDeclared⟩ := valid.continuations (.woken id obligation next) List.mem_cons_self
  have ordered := valid.accounted.ordered
  cases valid.linked with
  | woken resumes rest =>
      refine ⟨valid.storeScoped, valid.waiting, valid.held, rest, resumes, nextDeclared,
        fun continuation member => valid.continuations continuation (List.mem_cons_of_mem _ member),
        fun record member => ?_, valid.accounted.of_perm ?_ (fun ref member => ?_)
          (ordered.2.mono fun ref member => List.mem_append_right _ member) fun record member => ?_⟩
      · rcases List.mem_cons.mp member with rfl | member
        · exact ⟨opened, coherent, valid.declared⟩
        · exact valid.records record member
      · simp only [branchHoles, List.flatMap_cons, Continuation.holes, List.map_cons, DeferredProof.hole]
        simp only [List.singleton_append, List.append_assoc]
        exact (List.perm_middle.append_left _)
      · refs_member member []
      · rcases List.mem_cons.mp member with rfl | member
        · exact ordered.1
        · exact valid.accounted.acyclic record member

omit [DecidableEq Variable] in
/-- Scheduling pushes one woken entry per suspension above the given stack, in
reverse: the last suspension of the list ends on top and runs first. -/
theorem Continuation.schedule_stack : ∀ (suspensions : List (Suspension Variable Literal Symbol))
    (focus : Focus Variable Literal Symbol Certificate) (frames : List (Continuation Variable Literal Symbol Certificate)),
    ∃ entries, (schedule suspensions (focus, frames)).2 = entries ++ frames ∧
      entries.flatMap Continuation.holes = (suspensions.map Suspension.hole).reverse
  | [], _, _ => ⟨[], rfl, rfl⟩
  | suspension :: rest, focus, frames => by
      obtain ⟨entries, stack, holes⟩ :=
        schedule_stack rest (.solve suspension.obligation) (.woken suspension.id suspension.obligation focus :: frames)
      exact ⟨entries ++ [.woken suspension.id suspension.obligation focus], by simp [schedule, stack],
        by simp [List.flatMap_append, holes, Continuation.holes, Suspension.hole]⟩

omit [DecidableEq Variable] in
theorem Continuation.schedule_holes (suspensions : List (Suspension Variable Literal Symbol))
    (focus : Focus Variable Literal Symbol Certificate) (frames : List (Continuation Variable Literal Symbol Certificate)) :
    (schedule suspensions (focus, frames)).2.flatMap Continuation.holes =
      (suspensions.map Suspension.hole).reverse ++ frames.flatMap Continuation.holes := by
  obtain ⟨entries, stack, holes⟩ := schedule_stack suspensions focus frames
  rw [stack, List.flatMap_append, holes]

omit [DecidableEq Variable] in
/-- After scheduling, the focus is the obligation of the last suspension of the
list, the one on top of the stack, or the given focus when there is none. -/
theorem Continuation.schedule_focus : ∀ (suspensions : List (Suspension Variable Literal Symbol))
    (focus : Focus Variable Literal Symbol Certificate) (frames : List (Continuation Variable Literal Symbol Certificate)),
    (schedule suspensions (focus, frames)).1 =
      (suspensions.getLast?.map fun suspension => Focus.solve suspension.obligation).getD focus
  | [], _, _ => rfl
  | suspension :: rest, focus, frames => by
      rw [schedule, schedule_focus rest]
      cases rest with
      | nil => rfl
      | cons other more => simp [List.getLast?_cons]

omit [DecidableEq Variable] in
theorem Continuation.schedule_refs : ∀ (suspensions : List (Suspension Variable Literal Symbol))
    (focus : Focus Variable Literal Symbol Certificate) (frames : List (Continuation Variable Literal Symbol Certificate)),
    (schedule suspensions (focus, frames)).1.refs ++ (schedule suspensions (focus, frames)).2.flatMap Continuation.refs =
      focus.refs ++ frames.flatMap Continuation.refs
  | [], _, _ => rfl
  | suspension :: rest, focus, frames => by
      rw [schedule, schedule_refs rest]
      simp [Focus.refs, Continuation.refs]

/-- A focus and its continuation stack: the focus valid for the stack, the
stack linked, both declared, and references ordered. -/
structure Stack.Valid (root : Obligation Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (next : Focus Variable Literal Symbol Certificate × List (Continuation Variable Literal Symbol Certificate)) :
    Prop where
  focus : next.1.Valid root next.2
  linked : Linked root next.2
  declared : next.1.Declared store
  continuations : ∀ continuation ∈ next.2, continuation.Declared store
  ordered : Ordered next.1.refs next.2

/-- Scheduled woken goals keep the branch linked, declared, and ordered. -/
theorem Continuation.schedule_valid : ∀ (suspensions : List (Suspension Variable Literal Symbol))
    (next : Focus Variable Literal Symbol Certificate × List (Continuation Variable Literal Symbol Certificate)),
    Stack.Valid root store next → (∀ suspension ∈ suspensions, suspension.obligation.Declared store) →
      Stack.Valid root store (schedule suspensions next)
  | [], _, valid, _ => valid
  | suspension :: rest, (_, _), valid, suspended =>
      schedule_valid rest _ ⟨rfl, .woken valid.focus valid.linked, suspended suspension List.mem_cons_self,
        fun continuation member => by
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨suspended suspension List.mem_cons_self, valid.declared⟩
          · exact valid.continuations continuation member,
        ⟨fun _ member => (by cases member), by simpa [Focus.refs] using valid.ordered⟩⟩
        (fun other member => suspended other (List.mem_cons_of_mem _ member))

/-- A committed candidate's own continuation, before any woken goal. -/
theorem Expansion.start_valid {obligation : Obligation Variable Literal Symbol} {next : Store Variable Literal Symbol}
    (expansion : Expansion Variable Literal Symbol Certificate) (focus : obligation = expected root frames)
    (linked : Linked root frames) (ordered : Ordered [] frames) (parentDeclared : obligation.Declared next)
    (premisesDeclared : ∀ premise ∈ expansion.premises, (obligation.premise premise).Declared next)
    (continuations : ∀ continuation ∈ frames, continuation.Declared next) :
    Stack.Valid root next (expansion.start obligation frames) ∧ (expansion.start obligation frames).1.refs = [] ∧
      (expansion.start obligation frames).2.flatMap Continuation.refs = frames.flatMap Continuation.refs ∧
      (expansion.start obligation frames).2.flatMap Continuation.holes = frames.flatMap Continuation.holes := by
  unfold Expansion.start
  split
  · exact ⟨⟨⟨focus, .node .nil⟩, linked, ProofTree.Declared.node parentDeclared (by simp) (by simp), continuations,
      by simpa [Focus.refs, ProofTree.refs, ProofTree.refsOf] using ordered⟩,
      by simp [Focus.refs, ProofTree.refs, ProofTree.refsOf], rfl, rfl⟩
  · rename_i premise pending premisesEq
    refine ⟨⟨rfl, .frame focus .nil linked, premisesDeclared premise (by simp [premisesEq]),
      fun continuation member => ?_, by simpa [Ordered, Focus.refs, Frame.start, ProofTree.refsOf] using ordered⟩,
      rfl, by simp [Continuation.refs, Frame.start, ProofTree.refsOf], by simp [Continuation.holes]⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨parentDeclared, fun other inside => premisesDeclared other
        (by simpa [Frame.start, Frame.premises, premisesEq] using inside), by simp [Frame.start]⟩
    · exact continuations continuation member

/-- A committed candidate continues the branch: its woken goals run first, each
under its own scope, then its own continuation. -/
theorem Branch.Valid.commit {obligation : Obligation Variable Literal Symbol}
    {expansion : Expansion Variable Literal Symbol Certificate} {next : Store Variable Literal Symbol}
    {woken : List (Suspension Variable Literal Symbol)}
    (valid : Branch.Valid root store (.solve obligation) frames deferred bound)
    (committed : store.commit obligation expansion.flexibles expansion.rigids expansion.premises expansion.bindings =
      .committed next woken) :
    Branch.Valid root next (Continuation.schedule woken (expansion.start obligation frames)).1
      (Continuation.schedule woken (expansion.start obligation frames)).2 deferred bound := by
  have refines := Store.commit_refines committed
  obtain ⟨partition, _, _, _, waiting, constraints⟩ := Store.commit_wakes valid.storeScoped valid.waiting committed
  have old : ∀ suspension, suspension ∈ woken ∨ suspension ∈ next.wakeups → suspension ∈ store.wakeups :=
    fun suspension member => partition.mem_iff.mp (List.mem_append.mpr member)
  have suspended : ∀ suspension ∈ store.wakeups, suspension.obligation.Declared next :=
    fun suspension member => (valid.held.1 suspension member).refines refines
  obtain ⟨parentDeclared, premisesDeclared⟩ := Store.commit_declared committed valid.declared
  have accounted := valid.accounted
  obtain ⟨started, startRefs, startFrameRefs, startHoles⟩ := expansion.start_valid valid.valid valid.linked
    accounted.ordered parentDeclared premisesDeclared fun continuation member =>
      (valid.continuations continuation member).refines refines
  obtain ⟨scheduledValid, scheduledLinked, scheduledDeclared, scheduledContinuations, scheduledOrdered⟩ :=
    Continuation.schedule_valid woken _ started fun suspension member => suspended suspension (old suspension (.inl member))
  refine ⟨Store.commit_scoped valid.storeScoped committed, waiting,
    ⟨fun suspension member => suspended suspension (old suspension (.inr member)),
      fun constraint member => (valid.held.2 constraint (constraints ▸ member)).refines refines⟩,
    scheduledLinked, scheduledValid, scheduledDeclared, scheduledContinuations,
    fun record member => (valid.records record member).refines refines,
    accounted.of_perm ?_ (fun ref member => ?_) scheduledOrdered accounted.acyclic⟩
  · have scheduled := Continuation.schedule_holes woken (expansion.start obligation frames).1
      (expansion.start obligation frames).2
    rw [startHoles] at scheduled
    have wake : (woken.map Suspension.hole ++ next.wakeups.map Suspension.hole).Perm (store.wakeups.map Suspension.hole) := by
      simpa [List.map_append] using partition.map Suspension.hole
    unfold branchHoles
    refine ((((List.Perm.of_eq scheduled).trans ((List.reverse_perm _).append_right _)).append_left _).append_right _).trans ?_
    rw [← List.append_assoc]
    exact ((List.perm_append_comm.append_right _).trans (wake.append_right _)).append_right _
  · have scheduled := Continuation.schedule_refs woken (expansion.start obligation frames).1
      (expansion.start obligation frames).2
    rw [startRefs, startFrameRefs] at scheduled
    simp only [branchRefs] at member ⊢
    rw [scheduled] at member
    simpa [Focus.refs] using member

theorem State.init_valid (snapshot : Snapshot) (flexibles : List Variable)
    (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    (State.init (Certificate := Certificate) snapshot flexibles context goal).Valid := by
  refine ⟨⟨⟨?_, by simp [State.init], .nil, by simp [State.init], by simp [State.init], by simp [State.init]⟩,
    by simp [State.init, Store.Waiting], by simp [State.init, Store.Declared], .nil, rfl, ?_,
    by simp [State.init], by simp [State.init],
    ⟨by simp [State.init, branchHoles], by simp [State.init, branchHoles], by simp [State.init, branchRefs, Focus.refs],
      trivial, by simp [State.init]⟩⟩, by simp [State.init]⟩
  · intro name dependencies infoEq rigid member
    have found := lookup_mem infoEq
    simp only [State.init, List.mem_append, List.mem_map, Prod.mk.injEq] at found
    rcases found with ⟨_, _, _, impossible⟩ | ⟨_, _, _, same⟩
    · cases impossible
    · cases same
      exact lookup_declared _ _ _ _ member
  · -- Every free name of the query is declared: an answer name flexible, any other rigid.
    intro name member
    simp only [State.init] at member ⊢
    rw [Store.info?, ← Option.isSome_iff_ne_none]
    by_cases rigid : name ∈ rootRigids flexibles context goal
    · exact lookup_isSome_of_mem (List.mem_append_left _ (List.mem_map.mpr ⟨name, rigid, rfl⟩))
    · have flexible : name ∈ flexibles := by
        by_cases inside : name ∈ flexibles
        · exact inside
        · exact absurd (List.mem_filter.mpr ⟨member, by simpa using inside⟩) rigid
      exact lookup_isSome_of_mem (List.mem_append_right _ (List.mem_map.mpr ⟨name, flexible, rfl⟩))

omit [DecidableEq Variable] in
/-- The saved choice points are the old ones and, when candidates remain, one
for them with the current store, continuations, and deferred proofs. -/
theorem State.mem_save {state : State Variable Literal Symbol Certificate Snapshot}
    {obligation : Obligation Variable Literal Symbol} {rest : List (Expansion Variable Literal Symbol Certificate)}
    {point : ChoicePoint Variable Literal Symbol Certificate} (member : point ∈ state.save obligation rest) :
    point = ⟨obligation, rest, state.store, state.frames, state.deferred⟩ ∨ point ∈ state.choices := by
  cases rest with
  | nil => exact .inr member
  | cons _ _ => exact List.mem_cons.mp member

theorem State.save_valid {state : State Variable Literal Symbol Certificate Snapshot}
    {obligation : Obligation Variable Literal Symbol} {rest : List (Expansion Variable Literal Symbol Certificate)}
    (branch : Branch.Valid state.root state.store (.solve obligation) state.frames state.deferred state.nextHole)
    (choices : ∀ point ∈ state.choices, point.Valid state.root state.nextHole) :
    ∀ point ∈ state.save obligation rest, point.Valid state.root state.nextHole := fun point member => by
  rcases State.mem_save member with rfl | old
  · exact branch
  · exact choices point old

/-- Entering a candidate from a branch focused on its obligation keeps the
state valid, whatever the commit answers. -/
theorem State.enter_valid {state : State Variable Literal Symbol Certificate Snapshot}
    {obligation : Obligation Variable Literal Symbol} {expansion : Expansion Variable Literal Symbol Certificate}
    {rest : List (Expansion Variable Literal Symbol Certificate)}
    (branch : Branch.Valid state.root state.store (.solve obligation) state.frames state.deferred state.nextHole)
    (choices : ∀ point ∈ state.choices, point.Valid state.root state.nextHole) :
    (state.enter obligation expansion rest).Valid := by
  have saved := State.save_valid (rest := rest) branch choices
  unfold State.enter
  split
  · exact ⟨branch.fail, saved⟩
  · exact ⟨branch.fail, saved⟩
  · rename_i store woken committed
    exact ⟨branch.commit committed, saved⟩

end Preservation

theorem State.enter_root (state : State Variable Literal Symbol Certificate Snapshot)
    (obligation : Obligation Variable Literal Symbol) (expansion : Expansion Variable Literal Symbol Certificate)
    (rest : List (Expansion Variable Literal Symbol Certificate)) :
    (state.enter obligation expansion rest).root = state.root := by
  unfold State.enter
  split <;> rfl

theorem State.enter_gaps (state : State Variable Literal Symbol Certificate Snapshot)
    (obligation : Obligation Variable Literal Symbol) (expansion : Expansion Variable Literal Symbol Certificate)
    (rest : List (Expansion Variable Literal Symbol Certificate)) :
    ∃ added, (state.enter obligation expansion rest).gaps = added ++ state.gaps := by
  unfold State.enter
  split
  · exact ⟨[], rfl⟩
  · exact ⟨[_], rfl⟩
  · exact ⟨[], rfl⟩

/-- A committed candidate's woken suspensions run first, oldest first, each
under a woken continuation, and the candidate's own continuation after them. -/
theorem State.enter_committed {state : State Variable Literal Symbol Certificate Snapshot}
    {obligation : Obligation Variable Literal Symbol} {expansion : Expansion Variable Literal Symbol Certificate}
    {rest : List (Expansion Variable Literal Symbol Certificate)} {store : Store Variable Literal Symbol}
    {woken : List (Suspension Variable Literal Symbol)}
    (committed : state.store.commit obligation expansion.flexibles expansion.rigids expansion.premises
      expansion.bindings = .committed store woken) :
    state.enter obligation expansion rest =
      { state with
        choices := state.save obligation rest
        store := store
        focus := (Continuation.schedule woken (expansion.start obligation state.frames)).1
        frames := (Continuation.schedule woken (expansion.start obligation state.frames)).2 } := by
  simp [State.enter, committed]

/-- Woken goals run oldest first. From the top of the stack, the entries a
commit schedules hold its woken suspensions in increasing id order, above the
candidate's own continuation. The focus is the oldest woken obligation, the one
with the least id, or the candidate's own focus when nothing woke. -/
theorem State.enter_oldest_first {state : State Variable Literal Symbol Certificate Snapshot}
    {obligation : Obligation Variable Literal Symbol} {expansion : Expansion Variable Literal Symbol Certificate}
    {rest : List (Expansion Variable Literal Symbol Certificate)} {store : Store Variable Literal Symbol}
    {woken : List (Suspension Variable Literal Symbol)} (storeScoped : state.store.Scoped)
    (committed : state.store.commit obligation expansion.flexibles expansion.rigids expansion.premises
      expansion.bindings = .committed store woken) :
    (∃ entries, (state.enter obligation expansion rest).frames = entries ++ (expansion.start obligation state.frames).2 ∧
      entries.flatMap Continuation.holes = (woken.map Suspension.hole).reverse ∧
      ((entries.flatMap Continuation.holes).map Prod.fst).Pairwise (· < ·)) ∧
    (state.enter obligation expansion rest).focus =
      (woken.getLast?.map fun suspension => Focus.solve suspension.obligation).getD
        (expansion.start obligation state.frames).1 ∧
    ∀ oldest ∈ woken.getLast?, ∀ suspension ∈ woken, oldest.id ≤ suspension.id := by
  have newestFirst := (Store.commit_woken storeScoped committed).2
  obtain ⟨entries, stack, holes⟩ := Continuation.schedule_stack woken (expansion.start obligation state.frames).1
    (expansion.start obligation state.frames).2
  refine ⟨⟨entries, by rw [State.enter_committed committed]; exact stack, holes, ?_⟩,
    by rw [State.enter_committed committed]; exact Continuation.schedule_focus _ _ _, ?_⟩
  · rw [holes, List.map_reverse, List.map_map, List.pairwise_reverse]
    exact newestFirst
  · intro oldest last suspension member
    obtain ⟨newer, rfl⟩ := List.getLast?_eq_some_iff.mp last
    rw [List.map_append, List.pairwise_append] at newestFirst
    rcases List.mem_append.mp member with older | same
    · exact Nat.le_of_lt (newestFirst.2.2 _ (List.mem_map.mpr ⟨suspension, older, rfl⟩) _ (by simp))
    · rw [List.mem_singleton.mp same]; exact Nat.le_refl _

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
  · rename_i store woken committed
    exact Store.commit_extends committed

/-- Every transition preserves the invariant, whatever the strategy answers. -/
theorem step_valid (strategy : Strategy Variable Literal Symbol Certificate)
    {state next : State Variable Literal Symbol Certificate Snapshot} (valid : state.Valid)
    (stepped : step strategy state = .running next) : next.Valid ∧ next.root = state.root := by
  have branch := valid.branch
  unfold step at stepped
  split at stepped
  · rename_i obligation focusEq
    rw [focusEq] at branch
    split at stepped
    · cases stepped; exact ⟨⟨branch.fail, valid.choices⟩, rfl⟩
    · cases stepped; exact ⟨State.enter_valid branch valid.choices, State.enter_root _ _ _ _⟩
    · cases stepped; exact ⟨⟨branch.fail, valid.choices⟩, rfl⟩
    · cases stepped; exact ⟨⟨branch.fail, valid.choices⟩, rfl⟩
    · cases stepped
      exact ⟨State.enter_valid (state := { state with gaps := _ :: state.gaps }) branch valid.choices,
        State.enter_root _ _ _ _⟩
    · split at stepped
      · rename_i delayable
        cases stepped
        exact ⟨⟨branch.suspend delayable, fun point member => (valid.choices point member).raise (Nat.le_succ _)⟩, rfl⟩
      · cases stepped; exact ⟨⟨branch.fail, valid.choices⟩, rfl⟩
  · rename_i tree focusEq
    rw [focusEq] at branch
    split at stepped
    · split at stepped
      · cases stepped
      · cases stepped; exact ⟨⟨branch.fail, valid.choices⟩, rfl⟩
    · rename_i frame frames framesEq
      rw [framesEq] at branch
      split at stepped
      · rename_i node complete
        cases stepped; exact ⟨⟨branch.receive.1 _ complete, valid.choices⟩, rfl⟩
      · rename_i waiting frameWaiting
        cases stepped; exact ⟨⟨branch.receive.2 _ frameWaiting, valid.choices⟩, rfl⟩
    · rename_i id obligation resume frames framesEq
      rw [framesEq] at branch
      cases stepped; exact ⟨⟨branch.record, valid.choices⟩, rfl⟩
  · split at stepped
    · cases stepped
    · rename_i point others choicesEq
      have pointValid := valid.choices point (by simp [choicesEq])
      have othersValid : ∀ other ∈ others, other.Valid state.root state.nextHole :=
        fun other member => valid.choices other (by simp [choicesEq, member])
      split at stepped
      · cases stepped; exact ⟨⟨valid.branch, othersValid⟩, rfl⟩
      · cases stepped
        exact ⟨State.enter_valid
          (state := { state with
            store := point.store
            frames := point.frames
            deferred := point.deferred
            choices := others }) pointValid othersValid, State.enter_root _ _ _ _⟩

/-- What a successful run guarantees. The tree proves the root obligation,
coherently, names only names the final store declares, and holds no
reference: the success step filled each with its deferred proof. The final
answers are scoped. No goal is still delayed and no constraint unresolved;
restrictions (dependency sets) are not counted. The deferred proofs, kept as
provenance, have distinct ids, each proves its recorded obligation, and the
references left in them resolve to later records. -/
structure CompletedProof.Valid [DecidableEq Variable] (root : Obligation Variable Literal Symbol)
    (proof : CompletedProof Variable Literal Symbol Certificate Snapshot) : Prop where
  rooted : proof.root = root
  proves : proof.tree.obligation = root
  coherent : proof.tree.Coherent
  answers : proof.store.Scoped
  declared : proof.tree.Declared proof.store
  complete : proof.tree.refs = []
  settled : proof.store.wakeups = [] ∧ proof.store.constraints = []
  records : ∀ record ∈ proof.deferred, record.Valid proof.store
  distinct : (proof.deferred.map DeferredProof.id).Nodup
  forward : ∀ record ∈ proof.deferred, ∀ ref ∈ record.tree.refs,
    ref ∈ proof.deferred.map DeferredProof.hole ∧ record.id < ref.1

/-- A successful run's tree holds no reference, so it is monotonic exactly when
it retains no closed-world evidence. -/
theorem CompletedProof.Valid.monotonic_iff {root : Obligation Variable Literal Symbol}
    {proof : CompletedProof Variable Literal Symbol Certificate Snapshot} (valid : proof.Valid root) :
    proof.tree.Monotonic ↔ proof.tree.closedWorld = [] :=
  ⟨fun monotonic => monotonic.2, fun empty => ⟨valid.complete, empty⟩⟩

/-- A successful step finishes the root obligation with a valid completed proof:
the references of the finished tree resolve to the deferred proofs, and the
references in those records point to later records, so filling leaves a
complete tree (`ProofTree.fillAll_complete`). -/
theorem step_success (strategy : Strategy Variable Literal Symbol Certificate)
    {state resume : State Variable Literal Symbol Certificate Snapshot} {proof : CompletedProof Variable Literal Symbol Certificate Snapshot}
    (valid : state.Valid) (stepped : step strategy state = .finished (.success proof resume)) :
    proof.Valid state.root ∧ resume.Valid ∧ resume.root = state.root := by
  have branch := valid.branch
  have resumed : ({ state with focus := .failed } : State Variable Literal Symbol Certificate Snapshot).Valid :=
    ⟨valid.branch.fail, valid.choices⟩
  unfold step at stepped
  split at stepped
  · split at stepped <;> (try split at stepped) <;> cases stepped
  · rename_i tree focusEq
    rw [focusEq] at branch
    split at stepped
    · rename_i framesEq
      split at stepped
      · rename_i settled
        cases stepped
        rw [framesEq] at branch
        obtain ⟨noWakeups, noConstraints⟩ := Store.residual_eq_nil.mp settled
        have accounted := branch.accounted
        have holesEq : branchHoles state.store [] state.deferred = state.deferred.map DeferredProof.hole := by
          simp [branchHoles, noWakeups]
        have distinct : (state.deferred.map DeferredProof.id).Nodup := by
          have held := accounted.distinct
          rw [holesEq, List.map_map] at held
          exact held
        have resolved : ProofTree.Resolved state.deferred tree.refs := fun ref member => by
          rw [← holesEq]
          exact accounted.resolved ref (by simp [branchRefs, Focus.refs, member])
        have inner : ∀ record ∈ state.deferred, ∀ ref ∈ record.tree.refs,
            ref ∈ state.deferred.map DeferredProof.hole ∧ record.id < ref.1 := fun record member ref inside =>
          ⟨holesEq ▸ accounted.resolved ref
              (by simp only [branchRefs, List.mem_append, List.mem_flatMap]; exact .inr ⟨record, member, inside⟩),
            accounted.acyclic record member ref inside⟩
        obtain ⟨sameObligation, filledCoherent, filledDeclared, empty⟩ :=
          ProofTree.fillAll_complete distinct branch.records inner branch.valid.2 branch.declared resolved
        exact ⟨⟨rfl, sameObligation.trans branch.valid.1, filledCoherent, branch.storeScoped, filledDeclared, empty,
          ⟨noWakeups, noConstraints⟩, branch.records, distinct, inner⟩, resumed, rfl⟩
      · cases stepped
    · split at stepped <;> cases stepped
    · cases stepped
  · split at stepped
    · split at stepped <;> cases stepped
    · split at stepped <;> cases stepped

/-- A completed run proves the original query under the original scope with a
valid completed proof: every node's subproofs prove exactly its premises under
their own scopes, the final answers satisfy the dependency invariant, every
obligation of the tree names only names declared in the final store, the tree
holds no reference, and no goal is still delayed. -/
theorem run_success (strategy : Strategy Variable Literal Symbol Certificate) :
    ∀ (fuel : Nat) {state resume : State Variable Literal Symbol Certificate Snapshot}
      {proof : CompletedProof Variable Literal Symbol Certificate Snapshot},
      state.Valid → run strategy fuel state = .success proof resume →
        proof.Valid state.root ∧ resume.Valid ∧ resume.root = state.root
  | 0, _, _, _, _, ran => by cases ran
  | fuel + 1, state, resume, proof, valid, ran => by
      unfold run at ran
      split at ran
      · rename_i next stepped
        obtain ⟨nextValid, sameRoot⟩ := step_valid strategy valid stepped
        rw [← sameRoot]
        exact run_success strategy fuel nextValid ran
      · rename_i outcome stepped
        subst outcome
        exact step_success strategy valid stepped

/-! ## Answers, completion, delay, rollback, and gaps -/

/-- The next AND sibling starts from the store the previous sibling left, and a
suspension outlives the frame that created it: returning a subproof, recording
a woken goal's proof, or floundering never changes the store. -/
theorem step_proved_store (strategy : Strategy Variable Literal Symbol Certificate)
    {state next : State Variable Literal Symbol Certificate Snapshot} {tree : ProofTree Variable Literal Symbol Certificate}
    (focused : state.focus = .proved tree) (stepped : step strategy state = .running next) :
    next.store = state.store := by
  unfold step at stepped
  rw [focused] at stepped
  simp only at stepped
  split at stepped
  · split at stepped
    · cases stepped
    · cases stepped; rfl
  · split at stepped <;> (cases stepped; rfl)
  · cases stepped; rfl

/-- A subproof returning to the innermost frame is passed to it by `receive`; while
premises remain, the next premise becomes the focus. -/
theorem step_waiting (strategy : Strategy Variable Literal Symbol Certificate)
    {state : State Variable Literal Symbol Certificate Snapshot} {tree : ProofTree Variable Literal Symbol Certificate}
    {frame next : Frame Variable Literal Symbol Certificate} {frames : List (Continuation Variable Literal Symbol Certificate)}
    (focused : state.focus = .proved tree) (framesEq : state.frames = .frame frame :: frames)
    (waiting : frame.receive tree = .waiting next) :
    step strategy state = .running { state with frames := .frame next :: frames, focus := .solve next.focus } := by
  simp [step, focused, framesEq, waiting]

/-- When the last premise is proved, the frame is removed and its node is the
focus: the parent completes exactly once. -/
theorem step_complete (strategy : Strategy Variable Literal Symbol Certificate)
    {state : State Variable Literal Symbol Certificate Snapshot} {tree : ProofTree Variable Literal Symbol Certificate}
    {frame : Frame Variable Literal Symbol Certificate} {frames : List (Continuation Variable Literal Symbol Certificate)}
    (focused : state.focus = .proved tree) (framesEq : state.frames = .frame frame :: frames) (last : frame.pending = []) :
    step strategy state = .running
      { state with
        frames := frames
        focus := .proved (.node frame.rule frame.parent frame.premises (frame.done ++ [tree])) } := by
  obtain ⟨parent, rule, before, done, current, pending⟩ := frame
  subst last
  simp [step, focused, framesEq, Frame.receive, Frame.premises]

/-- A valid delay suspends the focused obligation in the store under the next
id and stands proved by a reference; the enclosing frame continues. -/
theorem step_delay (strategy : Strategy Variable Literal Symbol Certificate)
    {state : State Variable Literal Symbol Certificate Snapshot} {obligation : Obligation Variable Literal Symbol}
    {names : List Variable} (focused : state.focus = .solve obligation)
    (delays : strategy obligation state.store = .delay names) (delayable : state.store.delayable names = true) :
    step strategy state = .running
      { state with
        store := state.store.suspend ⟨state.nextHole, obligation, names⟩
        focus := .proved (.deferred state.nextHole obligation)
        nextHole := state.nextHole + 1 } := by
  simp [step, focused, delays, delayable]

/-- A delay on no name, a rigid name, a bound name, or an undeclared name is a
contract gap. -/
theorem step_delay_invalid (strategy : Strategy Variable Literal Symbol Certificate)
    {state : State Variable Literal Symbol Certificate Snapshot} {obligation : Obligation Variable Literal Symbol}
    {names : List Variable} (focused : state.focus = .solve obligation)
    (delays : strategy obligation state.store = .delay names) (invalid : state.store.delayable names = false) :
    step strategy state = .running { state with focus := .failed, gaps := ⟨.contract, obligation⟩ :: state.gaps } := by
  simp [step, focused, delays, invalid]

/-- A woken goal's proof is recorded under its suspension id and the focus it
interrupted resumes exactly as saved: nothing from the woken goal's scope
reaches the caller. -/
theorem step_woken (strategy : Strategy Variable Literal Symbol Certificate)
    {state : State Variable Literal Symbol Certificate Snapshot} {tree : ProofTree Variable Literal Symbol Certificate}
    {id : Nat} {obligation : Obligation Variable Literal Symbol} {next : Focus Variable Literal Symbol Certificate}
    {frames : List (Continuation Variable Literal Symbol Certificate)}
    (focused : state.focus = .proved tree) (framesEq : state.frames = .woken id obligation next :: frames) :
    step strategy state = .running
      { state with frames := frames, focus := next, deferred := ⟨id, obligation, tree⟩ :: state.deferred } := by
  simp [step, focused, framesEq]

/-- A branch that finishes with goals still delayed or constraints unresolved
flounders: one gap per residual item, never success, and the path fails. -/
theorem step_flounder (strategy : Strategy Variable Literal Symbol Certificate)
    {state : State Variable Literal Symbol Certificate Snapshot} {tree : ProofTree Variable Literal Symbol Certificate}
    (focused : state.focus = .proved tree) (framesEq : state.frames = []) (residual : state.store.residual ≠ []) :
    step strategy state = .running
      { state with
        focus := .failed
        gaps := state.store.residual.map (fun obligation => ⟨.floundered, obligation⟩) ++ state.gaps } := by
  obtain ⟨pending, more, residualEq⟩ := List.exists_cons_of_ne_nil residual
  simp [step, focused, framesEq, residualEq]

/-- A failed path resumes the newest choice point from its saved store,
continuations, and deferred proofs: bindings, suspensions, and deferred proofs
of the failed alternative are discarded, and suspensions it woke are pending
again. -/
theorem step_backtrack (strategy : Strategy Variable Literal Symbol Certificate)
    {state : State Variable Literal Symbol Certificate Snapshot} {point : ChoicePoint Variable Literal Symbol Certificate}
    {choices : List (ChoicePoint Variable Literal Symbol Certificate)}
    {expansion : Expansion Variable Literal Symbol Certificate} {rest : List (Expansion Variable Literal Symbol Certificate)}
    (focused : state.focus = .failed) (choicesEq : state.choices = point :: choices)
    (alternatives : point.alternatives = expansion :: rest) :
    step strategy state = .running
      ({ state with
          store := point.store
          frames := point.frames
          deferred := point.deferred
          choices := choices }.enter point.obligation expansion rest) := by
  simp [step, focused, choicesEq, alternatives]

/-- Gaps are never forgotten, even across backtracking. -/
theorem step_gaps (strategy : Strategy Variable Literal Symbol Certificate)
    {state next : State Variable Literal Symbol Certificate Snapshot} (stepped : step strategy state = .running next) :
    ∃ added, next.gaps = added ++ state.gaps := by
  unfold step at stepped
  split at stepped
  · split at stepped
    · cases stepped; exact ⟨[], rfl⟩
    · cases stepped; exact State.enter_gaps _ _ _ _
    · cases stepped; exact ⟨[_], rfl⟩
    · cases stepped; exact ⟨[_], rfl⟩
    · cases stepped
      rename_i obligation _ _ expansion rest _
      obtain ⟨added, addedEq⟩ :=
        State.enter_gaps { state with gaps := ⟨.unsupported, obligation⟩ :: state.gaps } obligation expansion rest
      exact ⟨added ++ [⟨.unsupported, obligation⟩], by rw [addedEq]; simp⟩
    · split at stepped
      · cases stepped; exact ⟨[], rfl⟩
      · cases stepped; exact ⟨[_], rfl⟩
  · split at stepped
    · split at stepped
      · cases stepped
      · cases stepped; exact ⟨_, rfl⟩
    · split at stepped <;> (cases stepped; exact ⟨[], rfl⟩)
    · cases stepped; exact ⟨[], rfl⟩
  · split at stepped
    · cases stepped
    · split at stepped
      · cases stepped; exact ⟨[], rfl⟩
      · cases stepped; exact State.enter_gaps _ _ _ _

/-- A run reports exhaustion only if no state on it recorded a gap. -/
theorem run_exhausted (strategy : Strategy Variable Literal Symbol Certificate) :
    ∀ (fuel : Nat) {state : State Variable Literal Symbol Certificate Snapshot},
      run strategy fuel state = .exhausted → state.gaps = []
  | 0, _, ran => by cases ran
  | fuel + 1, state, ran => by
      unfold run at ran
      split at ran
      · rename_i next stepped
        obtain ⟨added, gaps⟩ := step_gaps strategy stepped
        have empty := run_exhausted strategy fuel ran
        rw [empty] at gaps
        exact (List.append_eq_nil_iff.mp gaps.symm).2
      · rename_i outcome stepped
        subst outcome
        unfold step at stepped
        split at stepped
        · split at stepped <;> (try split at stepped) <;> cases stepped
        · split at stepped
          · split at stepped <;> cases stepped
          · split at stepped <;> cases stepped
          · cases stepped
        · split at stepped
          · split at stepped
            · rename_i empty
              exact List.isEmpty_iff.mp empty
            · cases stepped
          · split at stepped <;> cases stepped

/-- Floundering is never exhaustion: once a branch floundered, or any path was
abandoned, the run ends in another success, in `unknown`, or interrupted. -/
theorem run_not_exhausted (strategy : Strategy Variable Literal Symbol Certificate) (fuel : Nat)
    {state : State Variable Literal Symbol Certificate Snapshot} (gapped : state.gaps ≠ []) :
    run strategy fuel state ≠ .exhausted :=
  fun ran => gapped (run_exhausted strategy fuel ran)

end AnthillModKbSpec.Machine
