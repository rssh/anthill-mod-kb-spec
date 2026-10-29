import AnthillModKbSpec.Resolution.Machine.Commands

namespace AnthillModKbSpec.Machine

/-! # Reconstruction along a run (S06)

A successful run's tree records each rule application, but not the store of the
commit that chose it. The completion contract of a candidate (`Expansion.SoundUnder`)
holds in the stores the rest of its branch reads: those refining its commit. This
module carries that contract along the run, from each commit to the final store,
and composes the nodes of the completed tree into a `Derives` proof of the root
obligation read through the final answers.

`Command.Sound` is the obligation of a concrete command: every candidate it
answers is sound in every scoped store refining its commit. Under it, every
transition keeps the state sound (`step_sound`), and a successful run reconstructs
its answer instance (`run_reconstructs`, `run_init_reconstructs`). -/

variable {Variable Literal Symbol Certificate Snapshot : Type} [DecidableEq Variable] [FreshNames Variable]

/-- The completion contract of one node read through `store`: derivations of its
read premises, each in its own scope, give a derivation of its read obligation.
For a candidate it is `Expansion.SoundUnder`. -/
def NodeSound (hoApplySymbol : Symbol) (kb : LogicalKb Variable Literal Symbol)
    (naf : NafFailure Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (obligation : Obligation Variable Literal Symbol) (premises : List (Premise Variable Literal Symbol)) : Prop :=
  (∀ premise ∈ premises, ReadDerives hoApplySymbol kb naf store (obligation.premise premise)) →
    ReadDerives hoApplySymbol kb naf store obligation

/-- The node's contract holds in every scoped store refining `store`: in every
store the rest of the branch reads. -/
def SoundFrom (hoApplySymbol : Symbol) (kb : LogicalKb Variable Literal Symbol)
    (naf : NafFailure Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (obligation : Obligation Variable Literal Symbol) (premises : List (Premise Variable Literal Symbol)) : Prop :=
  ∀ later, store.Refines later → later.Scoped → NodeSound hoApplySymbol kb naf later obligation premises

section Contracts

variable {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}

theorem Expansion.soundUnder_iff {store : Store Variable Literal Symbol} {obligation : Obligation Variable Literal Symbol}
    {expansion : Expansion Variable Literal Symbol Certificate} :
    expansion.SoundUnder hoApplySymbol kb naf store obligation ↔
      NodeSound hoApplySymbol kb naf store obligation expansion.premises := Iff.rfl

theorem SoundFrom.refines {store next : Store Variable Literal Symbol} {obligation : Obligation Variable Literal Symbol}
    {premises : List (Premise Variable Literal Symbol)} (sound : SoundFrom hoApplySymbol kb naf store obligation premises)
    (refines : store.Refines next) : SoundFrom hoApplySymbol kb naf next obligation premises :=
  fun later further laterScoped => sound later (refines.trans further) laterScoped

/-- What a command guarantees for one candidate: if the commit accepts it, its
completion contract holds from the committed store on. Candidates the commit
refuses need nothing. -/
def CandidateSound (hoApplySymbol : Symbol) (kb : LogicalKb Variable Literal Symbol)
    (naf : NafFailure Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (obligation : Obligation Variable Literal Symbol) (expansion : Expansion Variable Literal Symbol Certificate) : Prop :=
  ∀ next woken, store.commit obligation expansion.flexibles expansion.rigids expansion.premises expansion.bindings =
      .committed next woken → SoundFrom hoApplySymbol kb naf next obligation expansion.premises

/-- A sound command: on a scoped store and a declared obligation, as every branch
of a valid state supplies them, each candidate it answers (`candidates` or
`incomplete`) is sound. Delays and unsupported answers carry no proof and need
nothing. -/
def Command.Sound (hoApplySymbol : Symbol) (kb : LogicalKb Variable Literal Symbol)
    (naf : NafFailure Variable Literal Symbol) (command : Command Variable Literal Symbol Certificate) : Prop :=
  ∀ obligation store, store.Scoped → obligation.Declared store →
    ∀ expansion ∈ (command obligation store).alternatives, CandidateSound hoApplySymbol kb naf store obligation expansion

/-- A scoped store reads a read term as itself: readings name no bound name. -/
theorem Store.Scoped.resolve_resolve {store : Store Variable Literal Symbol} (valid : store.Scoped)
    (term : Term Variable Literal Symbol) : store.resolve (store.resolve term) = store.resolve term :=
  resolveWith_unbound (valid.triangular.resolve_unbound term)

/-- What a goal reads as in a scoped store it still reads as in every refinement. -/
theorem Store.Scoped.read_refines {store later : Store Variable Literal Symbol} (valid : store.Scoped)
    {term read : Term Variable Literal Symbol} (reads : store.resolve term = read) (refines : store.Refines later) :
    later.resolve term = later.resolve read :=
  refines.resolve_eq (by rw [← reads, valid.resolve_resolve])

end Contracts

/-! ## Every node of a tree -/

namespace ProofTree

/-- Every node of the tree satisfies `property` of its obligation and premises.
A reference is not a node; the record it stands for is checked on its own. -/
inductive Nodes (property : Obligation Variable Literal Symbol → List (Premise Variable Literal Symbol) → Prop) :
    ProofTree Variable Literal Symbol Certificate → Prop where
  | node {rule : RuleApp Variable Literal Symbol Certificate} {obligation : Obligation Variable Literal Symbol}
      {premises : List (Premise Variable Literal Symbol)} {subproofs : List (ProofTree Variable Literal Symbol Certificate)}
      (here : property obligation premises) (children : ∀ tree ∈ subproofs, Nodes property tree) :
      Nodes property (.node rule obligation premises subproofs)
  | deferred {id : Nat} {obligation : Obligation Variable Literal Symbol} : Nodes property (.deferred id obligation)

variable {property weaker : Obligation Variable Literal Symbol → List (Premise Variable Literal Symbol) → Prop}

omit [DecidableEq Variable] [FreshNames Variable] in
theorem Nodes.mono {tree : ProofTree Variable Literal Symbol Certificate} (nodes : tree.Nodes property)
    (implies : ∀ obligation premises, property obligation premises → weaker obligation premises) :
    tree.Nodes weaker := by
  induction nodes with
  | node here _ ih => exact .node (implies _ _ here) ih
  | deferred => exact .deferred

omit [DecidableEq Variable] [FreshNames Variable] in
theorem fillOf_eq_map (records : List (DeferredProof Variable Literal Symbol Certificate)) :
    ∀ trees : List (ProofTree Variable Literal Symbol Certificate), fillOf records trees = trees.map (fill records)
  | [] => rfl
  | tree :: trees => by rw [fillOf, fillOf_eq_map records trees, List.map_cons]

omit [DecidableEq Variable] [FreshNames Variable] in
/-- Filling a tree whose nodes and records all satisfy a property leaves a tree
whose nodes satisfy it: filling only substitutes records for references. -/
theorem Nodes.fill {records : List (DeferredProof Variable Literal Symbol Certificate)}
    (recorded : ∀ record ∈ records, record.tree.Nodes property) {tree : ProofTree Variable Literal Symbol Certificate}
    (nodes : tree.Nodes property) : (tree.fill records).Nodes property := by
  induction nodes with
  | node here _ ih =>
      rw [ProofTree.fill, fillOf_eq_map]
      exact .node here fun tree member => by
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact ih original inside
  | @deferred id obligation =>
      simp only [ProofTree.fill]
      split
      · rename_i record found
        exact recorded record (List.mem_of_find?_eq_some found)
      · exact .deferred

omit [DecidableEq Variable] [FreshNames Variable] in
theorem Nodes.fillAll {records : List (DeferredProof Variable Literal Symbol Certificate)}
    (recorded : ∀ record ∈ records, record.tree.Nodes property) :
    ∀ (count : Nat) {tree : ProofTree Variable Literal Symbol Certificate}, tree.Nodes property →
      (tree.fillAll records count).Nodes property
  | 0, _, nodes => nodes
  | count + 1, _, nodes => Nodes.fillAll recorded count (nodes.fill recorded)

variable {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}

/-- A coherent tree without references, each of whose nodes satisfies its
completion contract read through `store`, derives its obligation read through
`store`. -/
theorem Nodes.readDerives {store : Store Variable Literal Symbol} {tree : ProofTree Variable Literal Symbol Certificate}
    (nodes : tree.Nodes (NodeSound hoApplySymbol kb naf store)) :
    tree.Coherent → tree.refs = [] → ReadDerives hoApplySymbol kb naf store tree.obligation := by
  induction nodes with
  | @node rule obligation premises subproofs here _ ih =>
      intro coherent empty
      cases coherent with
      | node children =>
          refine here ?_
          have closed : ∀ child ∈ subproofs, child.refs = [] := fun child member =>
            List.eq_nil_iff_forall_not_mem.mpr fun ref inside =>
              (List.eq_nil_iff_forall_not_mem.mp empty) ref (mem_refsOf.mpr ⟨child, member, inside⟩)
          -- Each premise is proved by the subproof in its position.
          have each : ∀ (premises : List (Premise Variable Literal Symbol))
              (trees : List (ProofTree Variable Literal Symbol Certificate)),
              CoherentPremises obligation premises trees → (∀ child ∈ trees, child ∈ subproofs) →
                ∀ premise ∈ premises, ReadDerives hoApplySymbol kb naf store (obligation.premise premise) := by
            intro premises
            induction premises with
            | nil => intro _ _ _ premise member; cases member
            | cons first rest restIh =>
                intro trees coherent contained premise member
                cases coherent with
                | cons opened childCoherent tail =>
                    rename_i child others
                    rcases List.mem_cons.mp member with rfl | later
                    · have inside := contained child List.mem_cons_self
                      rw [← opened]
                      exact ih child inside childCoherent (closed child inside)
                    · exact restIh others tail (fun other inside => contained other (List.mem_cons_of_mem _ inside))
                        premise later
          exact each premises subproofs children (fun _ member => member)
  | deferred => intro _ empty; cases empty

end ProofTree

/-! ## Soundness of a branch -/

section Branch

variable {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}

/-- A proved focus: every node of its tree is sound from `store` on. -/
def Focus.SoundFrom (hoApplySymbol : Symbol) (kb : LogicalKb Variable Literal Symbol)
    (naf : NafFailure Variable Literal Symbol) (store : Store Variable Literal Symbol) :
    Focus Variable Literal Symbol Certificate → Prop
  | .proved tree => tree.Nodes (Machine.SoundFrom hoApplySymbol kb naf store)
  | _ => True

/-- A frame: the node it will build is sound, and so are its completed
subproofs. A woken entry: the focus it resumes. -/
def Continuation.SoundFrom (hoApplySymbol : Symbol) (kb : LogicalKb Variable Literal Symbol)
    (naf : NafFailure Variable Literal Symbol) (store : Store Variable Literal Symbol) :
    Continuation Variable Literal Symbol Certificate → Prop
  | .frame entry => Machine.SoundFrom hoApplySymbol kb naf store entry.parent entry.premises ∧
      ∀ tree ∈ entry.done, tree.Nodes (Machine.SoundFrom hoApplySymbol kb naf store)
  | .woken _ _ next => next.SoundFrom hoApplySymbol kb naf store

/-- Every node a branch holds or will build is sound from its store on: in the
focus, in the continuations, and in the deferred proofs. -/
structure Branch.Sound (hoApplySymbol : Symbol) (kb : LogicalKb Variable Literal Symbol)
    (naf : NafFailure Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (focus : Focus Variable Literal Symbol Certificate) (frames : List (Continuation Variable Literal Symbol Certificate))
    (deferred : List (DeferredProof Variable Literal Symbol Certificate)) : Prop where
  focus : focus.SoundFrom hoApplySymbol kb naf store
  continuations : ∀ continuation ∈ frames, continuation.SoundFrom hoApplySymbol kb naf store
  records : ∀ record ∈ deferred, record.tree.Nodes (SoundFrom hoApplySymbol kb naf store)

/-- A saved alternative point: its branch, and every remaining candidate sound
for its obligation and saved store. -/
def ChoicePoint.Sound (hoApplySymbol : Symbol) (kb : LogicalKb Variable Literal Symbol)
    (naf : NafFailure Variable Literal Symbol) (point : ChoicePoint Variable Literal Symbol Certificate) : Prop :=
  Branch.Sound hoApplySymbol kb naf point.store (.solve point.obligation) point.frames point.deferred ∧
    ∀ expansion ∈ point.alternatives, CandidateSound hoApplySymbol kb naf point.store point.obligation expansion

/-- The state and every saved alternative are sound branches. -/
structure State.Sound (hoApplySymbol : Symbol) (kb : LogicalKb Variable Literal Symbol)
    (naf : NafFailure Variable Literal Symbol) (state : State Variable Literal Symbol Certificate Snapshot) : Prop where
  branch : Branch.Sound hoApplySymbol kb naf state.store state.focus state.frames state.deferred
  choices : ∀ point ∈ state.choices, point.Sound hoApplySymbol kb naf

variable {store next : Store Variable Literal Symbol} {frames : List (Continuation Variable Literal Symbol Certificate)}
  {deferred : List (DeferredProof Variable Literal Symbol Certificate)}

theorem Nodes.refines {tree : ProofTree Variable Literal Symbol Certificate}
    (nodes : tree.Nodes (SoundFrom hoApplySymbol kb naf store)) (refines : store.Refines next) :
    tree.Nodes (SoundFrom hoApplySymbol kb naf next) :=
  nodes.mono fun _ _ sound => sound.refines refines

theorem Focus.SoundFrom.refines {focus : Focus Variable Literal Symbol Certificate}
    (sound : focus.SoundFrom hoApplySymbol kb naf store) (refines : store.Refines next) :
    focus.SoundFrom hoApplySymbol kb naf next := by
  cases focus with
  | proved tree => exact Nodes.refines (store := store) sound refines
  | _ => trivial

theorem Continuation.SoundFrom.refines {continuation : Continuation Variable Literal Symbol Certificate}
    (sound : continuation.SoundFrom hoApplySymbol kb naf store) (refines : store.Refines next) :
    continuation.SoundFrom hoApplySymbol kb naf next := by
  cases continuation with
  | frame entry =>
      exact ⟨sound.1.refines refines, fun tree member => Nodes.refines (store := store) (sound.2 tree member) refines⟩
  | woken _ _ resumed =>
      have resumes : resumed.SoundFrom hoApplySymbol kb naf store := sound
      exact resumes.refines refines

theorem Branch.Sound.refines {focus : Focus Variable Literal Symbol Certificate}
    (sound : Branch.Sound hoApplySymbol kb naf store focus frames deferred) (refines : store.Refines next) :
    Branch.Sound hoApplySymbol kb naf next focus frames deferred :=
  ⟨sound.focus.refines refines, fun continuation member => (sound.continuations continuation member).refines refines,
    fun record member => Nodes.refines (store := store) (sound.records record member) refines⟩

theorem Branch.Sound.fail {focus : Focus Variable Literal Symbol Certificate}
    (sound : Branch.Sound hoApplySymbol kb naf store focus frames deferred) :
    Branch.Sound hoApplySymbol kb naf store .failed frames deferred :=
  { sound with focus := trivial }

/-- A committed candidate's own continuation is sound: a candidate without
premises is a sound node at once, and otherwise its frame will build one. -/
theorem Expansion.start_sound {obligation : Obligation Variable Literal Symbol}
    {expansion : Expansion Variable Literal Symbol Certificate}
    (candidate : SoundFrom hoApplySymbol kb naf next obligation expansion.premises)
    (continuations : ∀ continuation ∈ frames, continuation.SoundFrom hoApplySymbol kb naf next) :
    (expansion.start obligation frames).1.SoundFrom hoApplySymbol kb naf next ∧
      ∀ continuation ∈ (expansion.start obligation frames).2, continuation.SoundFrom hoApplySymbol kb naf next := by
  unfold Expansion.start
  split
  · rename_i none
    rw [none] at candidate
    exact ⟨.node candidate (fun _ member => by cases member), continuations⟩
  · rename_i premise pending premisesEq
    refine ⟨trivial, fun continuation member => ?_⟩
    rcases List.mem_cons.mp member with rfl | below
    · have premisesOf : (Frame.start obligation expansion.rule premise pending).premises = expansion.premises := by
        simp [Frame.start, Frame.premises, premisesEq]
      have parentOf : (Frame.start obligation expansion.rule premise pending).parent = obligation := rfl
      refine ⟨?_, fun _ inside => by simp [Frame.start] at inside⟩
      rw [premisesOf, parentOf]
      exact candidate
    · exact continuations continuation below

/-- Woken goals scheduled before a sound focus keep the branch sound: each
woken entry resumes the focus below it. -/
theorem Continuation.schedule_sound : ∀ (woken : List (Suspension Variable Literal Symbol))
    {focus : Focus Variable Literal Symbol Certificate} {frames : List (Continuation Variable Literal Symbol Certificate)},
    focus.SoundFrom hoApplySymbol kb naf next →
      (∀ continuation ∈ frames, continuation.SoundFrom hoApplySymbol kb naf next) →
      (Continuation.schedule woken (focus, frames)).1.SoundFrom hoApplySymbol kb naf next ∧
        ∀ continuation ∈ (Continuation.schedule woken (focus, frames)).2,
          continuation.SoundFrom hoApplySymbol kb naf next
  | [], _, _, focus, continuations => ⟨focus, continuations⟩
  | suspension :: rest, _, _, focus, continuations =>
      Continuation.schedule_sound rest (focus := .solve suspension.obligation) trivial fun continuation member => by
        rcases List.mem_cons.mp member with rfl | below
        · show Focus.SoundFrom hoApplySymbol kb naf next _
          exact focus
        · exact continuations continuation below

/-- Entering a sound candidate from a sound branch keeps the state sound,
whatever the commit answers; the saved alternatives are sound for the saved
store. -/
theorem State.enter_sound {state : State Variable Literal Symbol Certificate Snapshot}
    {obligation : Obligation Variable Literal Symbol} {expansion : Expansion Variable Literal Symbol Certificate}
    {rest : List (Expansion Variable Literal Symbol Certificate)}
    (branch : Branch.Sound hoApplySymbol kb naf state.store (.solve obligation) state.frames state.deferred)
    (choices : ∀ point ∈ state.choices, point.Sound hoApplySymbol kb naf)
    (candidate : CandidateSound hoApplySymbol kb naf state.store obligation expansion)
    (alternatives : ∀ other ∈ rest, CandidateSound hoApplySymbol kb naf state.store obligation other) :
    (state.enter obligation expansion rest).Sound hoApplySymbol kb naf := by
  have saved : ∀ point ∈ state.save obligation rest, point.Sound hoApplySymbol kb naf := by
    cases rest with
    | nil => exact choices
    | cons _ _ =>
        intro point member
        simp only [State.save, List.mem_cons] at member
        rcases member with rfl | member
        · exact ⟨branch, alternatives⟩
        · exact choices point member
  unfold State.enter
  split
  · exact ⟨branch.fail, saved⟩
  · exact ⟨branch.fail, saved⟩
  · rename_i store woken committed
    have refines := Store.commit_refines committed
    have moved := branch.refines refines
    obtain ⟨started, startedFrames⟩ :=
      Expansion.start_sound (expansion := expansion) (candidate store woken committed) moved.continuations
    obtain ⟨scheduled, scheduledFrames⟩ := Continuation.schedule_sound woken started startedFrames
    exact ⟨⟨scheduled, scheduledFrames, moved.records⟩, saved⟩

end Branch

/-! ## Transitions keep the state sound -/

section Preservation

variable {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}

theorem State.init_sound (snapshot : Snapshot) (flexibles : List Variable)
    (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    (State.init (Certificate := Certificate) snapshot flexibles context goal).Sound hoApplySymbol kb naf :=
  ⟨⟨trivial, by simp [State.init], by simp [State.init]⟩, by simp [State.init]⟩

/-- Every transition of a sound command keeps a valid state sound. -/
theorem step_sound (command : Command Variable Literal Symbol Certificate)
    (commandSound : Command.Sound hoApplySymbol kb naf command)
    {state next : State Variable Literal Symbol Certificate Snapshot} (valid : state.Valid)
    (sound : state.Sound hoApplySymbol kb naf) (stepped : step command state = .running next) :
    next.Sound hoApplySymbol kb naf := by
  have branch := sound.branch
  have validBranch := valid.branch
  unfold step at stepped
  split at stepped
  · rename_i obligation focusEq
    rw [focusEq] at branch validBranch
    split at stepped
    · cases stepped; exact ⟨branch.fail, sound.choices⟩
    · rename_i expansion rest responseEq
      cases stepped
      have candidates := commandSound obligation state.store validBranch.storeScoped validBranch.declared
      rw [responseEq] at candidates
      exact State.enter_sound branch sound.choices (candidates expansion List.mem_cons_self)
        fun other member => candidates other (List.mem_cons_of_mem _ member)
    · cases stepped; exact ⟨branch.fail, sound.choices⟩
    · cases stepped; exact ⟨branch.fail, sound.choices⟩
    · rename_i expansion rest responseEq
      cases stepped
      have candidates := commandSound obligation state.store validBranch.storeScoped validBranch.declared
      rw [responseEq] at candidates
      exact State.enter_sound (state := { state with gaps := _ :: state.gaps }) branch sound.choices
        (candidates expansion List.mem_cons_self) fun other member => candidates other (List.mem_cons_of_mem _ member)
    · split at stepped
      · cases stepped
        exact ⟨⟨.deferred, (branch.refines (Store.Refines.suspend _ _)).continuations,
          (branch.refines (Store.Refines.suspend _ _)).records⟩, sound.choices⟩
      · cases stepped; exact ⟨branch.fail, sound.choices⟩
  · rename_i tree focusEq
    rw [focusEq] at branch
    split at stepped
    · split at stepped
      · cases stepped
      · cases stepped; exact ⟨branch.fail, sound.choices⟩
    · rename_i frame frames framesEq
      rw [framesEq] at branch
      obtain ⟨parentSound, doneSound⟩ := branch.continuations (.frame frame) List.mem_cons_self
      have below := fun continuation member => branch.continuations continuation (List.mem_cons_of_mem _ member)
      have children : ∀ child ∈ frame.done ++ [tree], child.Nodes (SoundFrom hoApplySymbol kb naf state.store) :=
        fun child member => by
          rcases List.mem_append.mp member with done | last
          · exact doneSound child done
          · rw [List.mem_singleton.mp last]; exact branch.focus
      split at stepped
      · rename_i node complete
        cases stepped
        obtain ⟨_, rfl⟩ := Frame.receive_complete complete
        exact ⟨⟨.node parentSound children, below, branch.records⟩, sound.choices⟩
      · rename_i waiting frameWaiting
        cases stepped
        obtain ⟨sameParent, _, samePremises, _, sameDone, _⟩ := Frame.receive_waiting frameWaiting
        refine ⟨⟨trivial, fun continuation member => ?_, branch.records⟩, sound.choices⟩
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨by rw [sameParent, samePremises]; exact parentSound, by rw [sameDone]; exact children⟩
        · exact below continuation member
    · rename_i id obligation resume frames framesEq
      rw [framesEq] at branch
      cases stepped
      have resumes : resume.SoundFrom hoApplySymbol kb naf state.store :=
        branch.continuations (.woken id obligation resume) List.mem_cons_self
      refine ⟨⟨resumes,
        fun continuation member => branch.continuations continuation (List.mem_cons_of_mem _ member),
        fun record member => ?_⟩, sound.choices⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact branch.focus
      · exact branch.records record member
  · split at stepped
    · cases stepped
    · rename_i point others choicesEq
      have pointSound := sound.choices point (by simp [choicesEq])
      have othersSound : ∀ other ∈ others, other.Sound hoApplySymbol kb naf :=
        fun other member => sound.choices other (by simp [choicesEq, member])
      split at stepped
      · cases stepped; exact ⟨sound.branch, othersSound⟩
      · rename_i expansion rest alternativesEq
        cases stepped
        have alternatives := pointSound.2
        rw [alternativesEq] at alternatives
        exact State.enter_sound
          (state := { state with
            store := point.store
            frames := point.frames
            deferred := point.deferred
            choices := others }) pointSound.1 othersSound (alternatives expansion List.mem_cons_self)
          fun other member => alternatives other (List.mem_cons_of_mem _ member)

/-- The success step of a sound state: every node of the completed tree, its
references filled with the deferred proofs, is sound from the final store on,
and the resume state is sound. -/
theorem step_reconstructs (command : Command Variable Literal Symbol Certificate)
    {state resume : State Variable Literal Symbol Certificate Snapshot}
    {proof : CompletedProof Variable Literal Symbol Certificate Snapshot}
    (sound : state.Sound hoApplySymbol kb naf) (stepped : step command state = .finished (.success proof resume)) :
    proof.tree.Nodes (SoundFrom hoApplySymbol kb naf proof.store) ∧ resume.Sound hoApplySymbol kb naf := by
  have branch := sound.branch
  unfold step at stepped
  split at stepped
  · split at stepped <;> (try split at stepped) <;> cases stepped
  · rename_i tree focusEq
    rw [focusEq] at branch
    split at stepped
    · split at stepped
      · cases stepped
        exact ⟨ProofTree.Nodes.fillAll branch.records _ branch.focus, ⟨branch.fail, sound.choices⟩⟩
      · cases stepped
    · split at stepped <;> cases stepped
    · cases stepped
  · split at stepped
    · split at stepped <;> cases stepped
    · split at stepped <;> cases stepped

/-- A successful run of a sound command reconstructs its answer instance: the
root obligation read through the final answers is derivable. The resume state is
valid and sound, so every further answer is reconstructed too. -/
theorem run_reconstructs (command : Command Variable Literal Symbol Certificate)
    (commandSound : Command.Sound hoApplySymbol kb naf command) :
    ∀ (fuel : Nat) {state resume : State Variable Literal Symbol Certificate Snapshot}
      {proof : CompletedProof Variable Literal Symbol Certificate Snapshot},
      state.Valid → state.Sound hoApplySymbol kb naf → run command fuel state = .success proof resume →
        ReadDerives hoApplySymbol kb naf proof.store proof.root ∧ resume.Valid ∧ resume.Sound hoApplySymbol kb naf
  | 0, _, _, _, _, _, ran => by cases ran
  | fuel + 1, state, resume, proof, valid, sound, ran => by
      unfold run at ran
      split at ran
      · rename_i next stepped
        exact run_reconstructs command commandSound fuel (step_valid command valid stepped).1
          (step_sound command commandSound valid sound stepped) ran
      · rename_i outcome stepped
        subst outcome
        obtain ⟨completed, resumeValid, _⟩ := step_success command valid stepped
        obtain ⟨nodes, resumeSound⟩ := step_reconstructs command sound stepped
        have read := (nodes.mono fun _ _ from' => from' proof.store (.refl _) completed.answers).readDerives
          completed.coherent completed.complete
        rw [completed.proves, ← completed.rooted] at read
        exact ⟨read, resumeValid, resumeSound⟩

/-- A query answered by a sound command is derivable for its answer instance:
the goal and context read through the final answers. -/
theorem run_init_reconstructs (command : Command Variable Literal Symbol Certificate)
    (commandSound : Command.Sound hoApplySymbol kb naf command) (fuel : Nat) (snapshot : Snapshot)
    (flexibles : List Variable) (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol)
    {resume : State Variable Literal Symbol Certificate Snapshot}
    {proof : CompletedProof Variable Literal Symbol Certificate Snapshot}
    (ran : run command fuel (State.init snapshot flexibles context goal) = .success proof resume) :
    Derives hoApplySymbol kb (context.map proof.store.resolve) (proof.store.resolve goal) naf := by
  obtain ⟨completed, _, _⟩ := run_success command fuel (State.init_valid snapshot flexibles context goal) ran
  have read := (run_reconstructs command commandSound fuel (State.init_valid snapshot flexibles context goal)
    (State.init_sound snapshot flexibles context goal) ran).1
  rw [completed.rooted] at read
  simpa [ReadDerives, State.init, Obligation.root, Obligation.context] using read

end Preservation

end AnthillModKbSpec.Machine
