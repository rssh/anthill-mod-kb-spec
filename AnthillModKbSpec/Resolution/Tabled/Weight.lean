import AnthillModKbSpec.Resolution.Tabled.Multiset
import AnthillModKbSpec.Resolution.Machine.State

/-! # Every machine step lowers the branches' weights (S24)

A machine state is a collection of branches: the current one, unless it has
failed, and each alternative saved in a choice point. Each branch has a weight
(`State.elements`):

- the **goal size** of what it still has to prove (`goalSize`): the focused
  goal, the pending premises of every frame up to a NAF entry
  (`proceed`), and the goals delayed in its store (`storeWeight`), plus one
  until the branch closes;
- second, twice its woken continuations plus one while it solves a goal, which
  a delay and a woken goal's return lower when the size stays.

`startCost` is what a candidate's premises weigh once it is entered. When
every alternative a strategy offers for the focused goal costs less than the
goal (`startCost e + 1 < goalSize goal`), every machine step replaces one
branch by smaller ones, or drops an empty choice point (`step_lower`). The
multiset order on the weights is well-founded (`Tabled/Multiset`), so a
machine run with such a strategy ends; a bounded tabled run keeps only such
alternatives (`Engine.fit`).

A delayed goal is weighed once in the store; the commit that wakes it moves
that weight into the branch (`commit_weight`, `schedule_weight`). -/

namespace AnthillModKbSpec.Tabled

open Machine

variable {Variable Literal Symbol Certificate Snapshot : Type} [DecidableEq Variable] [DecidableEq Literal]
  [DecidableEq Symbol] [FreshNames Variable]

/-! ## Weights -/

section Weights

variable (hoApplySymbol : Symbol)

/-- The size of a goal: its connectives, each atom two, an indirect call five,
so that its direct form, its one premise, costs less. -/
def goalSize : Term Variable Literal Symbol → Nat
  | .conj left right => goalSize left + goalSize right + 4
  | .disj left right => max (goalSize left) (goalSize right) + 3
  | .imp _ conclusion => goalSize conclusion + 3
  | .forallVar _ body => goalSize body + 3
  | .existsVar _ body => goalSize body + 3
  | .defaultNeg operand => goalSize operand + 3
  | .app symbol _ => if symbol = hoApplySymbol then 5 else 2
  | _ => 2

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem two_le_goalSize : ∀ goal : Term Variable Literal Symbol, 2 ≤ goalSize hoApplySymbol goal
  | .conj _ _ | .disj _ _ | .imp _ _ | .forallVar _ _ | .existsVar _ _ | .defaultNeg _ => by
      simp only [goalSize]; omega
  | .app symbol _ => by simp only [goalSize]; split <;> omega
  | .var _ | .lit _ | .truth | .falsity | .dictionaryCall _ _ _ _ | .equal _ _ => by simp [goalSize]

/-- The weight of premises still pending in a frame. -/
def pendingWeight (premises : List (Premise Variable Literal Symbol)) : Nat :=
  (premises.map fun premise => goalSize hoApplySymbol premise.goal + 1).sum

/-- The size of a focus: its goal, when it solves one. -/
def focusSize : Focus Variable Literal Symbol Certificate → Nat
  | .solve obligation => goalSize hoApplySymbol obligation.goal
  | _ => 0

/-- What returning a proof to the continuations still costs: every frame's
pending premises, and every woken continuation's next focus, up to a NAF entry,
which ends the branch. -/
def proceed : List (Continuation Variable Literal Symbol Certificate) → Nat
  | [] => 1
  | .frame frame :: rest => pendingWeight hoApplySymbol frame.pending + 1 + proceed rest
  | .woken _ _ next :: rest => focusSize hoApplySymbol next + proceed rest
  | .negation _ _ _ :: _ => 1

/-- The woken continuations. -/
def wokenCount : List (Continuation Variable Literal Symbol Certificate) → Nat
  | [] => 0
  | .woken _ _ _ :: rest => wokenCount rest + 1
  | _ :: rest => wokenCount rest

/-- The weight of a delayed goal. -/
def suspensionWeight (suspension : Suspension Variable Literal Symbol) : Nat :=
  goalSize hoApplySymbol suspension.obligation.goal

/-- The goals delayed in a store, and one until the branch closes. -/
def storeWeight (store : Store Variable Literal Symbol) : Nat :=
  (store.wakeups.map (suspensionWeight hoApplySymbol)).sum + if store.closing then 0 else 1

/-- What a candidate's premises weigh once it is entered. -/
def startCost (expansion : Expansion Variable Literal Symbol Certificate) : Nat :=
  match expansion.premises with
  | [] => 0
  | premise :: pending => goalSize hoApplySymbol premise.goal + pendingWeight hoApplySymbol pending + 1

/-- A candidate fits a focus of weight `top`. -/
def Fits (top : Nat) (expansion : Expansion Variable Literal Symbol Certificate) : Prop :=
  startCost hoApplySymbol expansion + 1 < top

instance (top : Nat) (expansion : Expansion Variable Literal Symbol Certificate) :
    Decidable (Fits hoApplySymbol top expansion) :=
  Nat.decLt _ _

/-- The weight of a branch: its focus weighed `top` when it solves a goal. -/
def branchElement (top : Nat) : Focus Variable Literal Symbol Certificate →
    List (Continuation Variable Literal Symbol Certificate) → Store Variable Literal Symbol → List (Nat × Nat)
  | .solve _, frames, store =>
      [(top + proceed hoApplySymbol frames + storeWeight hoApplySymbol store, 2 * wokenCount frames + 1)]
  | .proved _, frames, store => [(proceed hoApplySymbol frames + storeWeight hoApplySymbol store, 2 * wokenCount frames)]
  | .failed, _, _ => []

/-- The weights of a choice point's alternatives. -/
def pointElements (point : ChoicePoint Variable Literal Symbol Certificate) : List (Nat × Nat) :=
  point.alternatives.map fun expansion =>
    (startCost hoApplySymbol expansion + proceed hoApplySymbol point.frames + storeWeight hoApplySymbol point.store + 1, 0)

/-- The weights of a state's branches, its focus weighed `top`. -/
def weightsWith (top : Nat) (state : State Variable Literal Symbol Certificate Snapshot) : List (Nat × Nat) :=
  branchElement hoApplySymbol top state.focus state.frames state.store ++ state.choices.flatMap (pointElements hoApplySymbol)

/-- The weights of a state's branches. -/
def weights (state : State Variable Literal Symbol Certificate Snapshot) : List (Nat × Nat) :=
  weightsWith hoApplySymbol (focusSize hoApplySymbol state.focus) state

end Weights

/-! ## The order on weights -/

/-- Weights compared by size, then by the second component. -/
def Below : Nat × Nat → Nat × Nat → Prop := Prod.Lex (· < ·) (· < ·)

theorem Below.wellFounded : WellFounded Below :=
  ⟨fun (a, b) => Prod.lexAccessible (Nat.lt_wfRel.wf.apply a) Nat.lt_wfRel.wf.apply b⟩

theorem below_of_lt {x y : Nat × Nat} (smaller : x.1 < y.1) : Below x y := by
  obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y
  exact Prod.Lex.left _ _ smaller

theorem below_of_le {x y : Nat × Nat} (size : x.1 ≤ y.1) (second : x.2 < y.2) : Below x y := by
  obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y
  rcases Nat.lt_or_eq_of_le size with lt | eq
  · exact Prod.Lex.left _ _ lt
  · simp only at eq; subst eq; exact Prod.Lex.right _ second

/-- A step's effect on a state's weights: lower in the multiset order, or the
same weights with a choice point fewer. -/
def StepLower {Snapshot : Type} (hoApplySymbol : Symbol) (top : Nat)
    (next state : State Variable Literal Symbol Certificate Snapshot) : Prop :=
  Lower Below (weights hoApplySymbol next) (weightsWith hoApplySymbol top state) ∨
    (weights hoApplySymbol next = weightsWith hoApplySymbol top state ∧ next.choices.length < state.choices.length)

/-! ## Bookkeeping lemmas -/

section Bookkeeping

variable {hoApplySymbol : Symbol}

theorem sum_filter_add {α : Type} (items : List α) (keep : α → Bool) (weight : α → Nat) :
    ((items.filter keep).map weight).sum + ((items.filter fun item => !keep item).map weight).sum = (items.map weight).sum := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      cases keeps : keep item <;> simp [keeps] <;> omega

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem bind_keeps {store next : Store Variable Literal Symbol} {scope : Scope Variable Literal Symbol} {name : Variable}
    {value : Term Variable Literal Symbol} (bound : store.bind scope name value = .bound next) :
    next.wakeups = store.wakeups ∧ next.closing = store.closing := by
  unfold Store.bind at bound
  repeat' (first | split at bound | dsimp only at bound)
  all_goals first | (cases bound; done) | (cases bound; exact ⟨rfl, rfl⟩)

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem bindAll_keeps {scope : Scope Variable Literal Symbol} :
    ∀ {store next : Store Variable Literal Symbol} {bindings : List (Variable × Term Variable Literal Symbol)},
      store.bindAll scope bindings = .bound next → next.wakeups = store.wakeups ∧ next.closing = store.closing
  | store, next, [], bound => by cases bound; exact ⟨rfl, rfl⟩
  | store, next, (name, value) :: rest, bound => by
      unfold Store.bindAll at bound
      split at bound
      · rename_i middle middleBound
        obtain ⟨wakeups, closing⟩ := bind_keeps middleBound
        obtain ⟨wakeups', closing'⟩ := bindAll_keeps bound
        exact ⟨wakeups'.trans wakeups, closing'.trans closing⟩
      all_goals cases bound

omit [DecidableEq Literal] [FreshNames Variable] in
/-- A commit moves the goals it wakes out of the store and keeps its phase. -/
theorem commit_weight {store next : Store Variable Literal Symbol} {obligation : Obligation Variable Literal Symbol}
    {flexibles rigids : List Variable} {premises : List (Premise Variable Literal Symbol)}
    {bindings : List (Variable × Term Variable Literal Symbol)} {woken : List (Suspension Variable Literal Symbol)}
    (committed : store.commit obligation flexibles rigids premises bindings = .committed next woken) :
    (woken.map (suspensionWeight hoApplySymbol)).sum + storeWeight hoApplySymbol next = storeWeight hoApplySymbol store := by
  unfold Store.commit at committed
  split at committed
  · split at committed
    · rename_i middle bound
      cases committed
      obtain ⟨wakeups, closing⟩ := bindAll_keeps bound
      have prepared : (store.prepare obligation flexibles rigids).wakeups = store.wakeups ∧
          (store.prepare obligation flexibles rigids).closing = store.closing := ⟨rfl, rfl⟩
      unfold storeWeight
      have closed : middle.wake.closing = store.closing := closing.trans prepared.2
      have woke : middle.wake.wakeups = middle.wakeups.filter (fun suspension => !middle.wakes suspension) := rfl
      rw [closed, woke, ← Nat.add_assoc]
      simp only [Store.woken]
      rw [sum_filter_add, wakeups, prepared.1]
    all_goals cases committed
  · cases committed

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
/-- Scheduling woken goals before a focus adds their weights. -/
theorem schedule_weight : ∀ (woken : List (Suspension Variable Literal Symbol))
    (next : Focus Variable Literal Symbol Certificate × List (Continuation Variable Literal Symbol Certificate)),
    focusSize hoApplySymbol (Continuation.schedule woken next).1 + proceed hoApplySymbol (Continuation.schedule woken next).2 =
      (woken.map (suspensionWeight hoApplySymbol)).sum + (focusSize hoApplySymbol next.1 + proceed hoApplySymbol next.2)
  | [], _ => by simp [Continuation.schedule]
  | suspension :: rest, (focus, frames) => by
      simp only [Continuation.schedule]
      rw [schedule_weight rest]
      simp only [focusSize, proceed, List.map_cons, List.sum_cons, suspensionWeight]
      omega

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
/-- An entered candidate weighs its premises on top of the continuations. -/
theorem start_weight (expansion : Expansion Variable Literal Symbol Certificate) (obligation : Obligation Variable Literal Symbol)
    (frames : List (Continuation Variable Literal Symbol Certificate)) :
    focusSize hoApplySymbol (expansion.start obligation frames).1 + proceed hoApplySymbol (expansion.start obligation frames).2 =
      startCost hoApplySymbol expansion + proceed hoApplySymbol frames := by
  unfold Expansion.start startCost
  split
  · rename_i none_; simp [none_, focusSize]
  · rename_i premise pending some_
    simp only [some_, focusSize, proceed, Machine.Frame.start, Obligation.premise]
    omega

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
/-- A branch's weight is its focus's size, its continuations', and its store's. -/
theorem branchElement_bound {focus : Focus Variable Literal Symbol Certificate}
    {frames : List (Continuation Variable Literal Symbol Certificate)} {store : Store Variable Literal Symbol} :
    ∀ x ∈ branchElement hoApplySymbol (focusSize hoApplySymbol focus) focus frames store,
      x.1 = focusSize hoApplySymbol focus + proceed hoApplySymbol frames + storeWeight hoApplySymbol store := by
  intro x member
  cases focus with
  | solve obligation => simp only [branchElement, List.mem_singleton] at member; subst member; rfl
  | proved tree => simp only [branchElement, List.mem_singleton] at member; subst member; simp [focusSize]
  | failed => cases member

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem branchElement_length_le {top : Nat} {focus : Focus Variable Literal Symbol Certificate}
    {frames : List (Continuation Variable Literal Symbol Certificate)} {store : Store Variable Literal Symbol} :
    (branchElement hoApplySymbol top focus frames store).length ≤ 1 := by
  cases focus <;> simp [branchElement]

omit [DecidableEq Literal] [FreshNames Variable] in
/-- The weights of an entered candidate: the new branch, at most its
premises', its continuations', and its store's, and the alternatives saved
beside it. -/
theorem enter_elements (state : State Variable Literal Symbol Certificate Snapshot) (obligation : Obligation Variable Literal Symbol)
    (expansion : Expansion Variable Literal Symbol Certificate) (rest : List (Expansion Variable Literal Symbol Certificate)) :
    ∃ entered : List (Nat × Nat),
      weights hoApplySymbol (state.enter obligation expansion rest) =
        entered ++ (rest.map fun other => (startCost hoApplySymbol other + proceed hoApplySymbol state.frames +
          storeWeight hoApplySymbol state.store + 1, 0)) ++ state.choices.flatMap (pointElements hoApplySymbol) ∧
      ∀ x ∈ entered, x.1 ≤ startCost hoApplySymbol expansion + proceed hoApplySymbol state.frames +
        storeWeight hoApplySymbol state.store := by
  have saved : ({ state with choices := state.save obligation rest } : State Variable Literal Symbol Certificate Snapshot).choices.flatMap
      (pointElements hoApplySymbol) =
      (rest.map fun other => (startCost hoApplySymbol other + proceed hoApplySymbol state.frames +
        storeWeight hoApplySymbol state.store + 1, 0)) ++ state.choices.flatMap (pointElements hoApplySymbol) := by
    cases rest with
    | nil => simp [State.save]
    | cons first more => simp [State.save, pointElements]
  unfold State.enter
  dsimp only
  split
  · refine ⟨[], ?_, fun _ member => by cases member⟩
    simp only [weights, weightsWith, branchElement, List.nil_append]
    exact saved
  · refine ⟨[], ?_, fun _ member => by cases member⟩
    simp only [weights, weightsWith, branchElement, List.nil_append]
    exact saved
  · refine ⟨[], ?_, fun _ member => by cases member⟩
    simp only [weights, weightsWith, branchElement, List.nil_append]
    exact saved
  · rename_i next woken committed
    refine ⟨branchElement hoApplySymbol
      (focusSize hoApplySymbol (Continuation.schedule woken (expansion.start obligation state.frames)).1)
      (Continuation.schedule woken (expansion.start obligation state.frames)).1
      (Continuation.schedule woken (expansion.start obligation state.frames)).2 next, ?_, fun x member => ?_⟩
    · simp only [weights, weightsWith]
      rw [List.append_assoc]
      congr 1
    · rw [branchElement_bound x member, schedule_weight, start_weight]
      have := commit_weight (hoApplySymbol := hoApplySymbol) committed
      omega

end Bookkeeping

/-! ## Every step lowers the weights -/

section Step

variable {hoApplySymbol : Symbol}

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem receive_pending {frame next : Machine.Frame Variable Literal Symbol Certificate}
    {tree : ProofTree Variable Literal Symbol Certificate} (waiting : frame.receive tree = .waiting next) :
    frame.pending = next.current :: next.pending := by
  obtain ⟨parent, rule, before, done, current, pending⟩ := frame
  cases pending with
  | nil => simp [Machine.Frame.receive] at waiting
  | cons following rest =>
      simp only [Machine.Frame.receive, Machine.Frame.Received.waiting.injEq] at waiting
      subst waiting
      rfl

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem cutNegation_sublist :
    ∀ choices : List (ChoicePoint Variable Literal Symbol Certificate), (cutNegation choices).Sublist choices
  | [] => .slnil
  | point :: rest => by
      unfold cutNegation
      split
      · exact .cons _ (List.Sublist.refl rest)
      · exact .cons _ (cutNegation_sublist rest)

omit [DecidableEq Literal] [FreshNames Variable] in
/-- Entering a candidate at the focus: its weights replace the focus's, which
weighs `top`, when every alternative fits `top`. -/
theorem enter_lower (state : State Variable Literal Symbol Certificate Snapshot) (obligation : Obligation Variable Literal Symbol)
    (expansion : Expansion Variable Literal Symbol Certificate) (rest : List (Expansion Variable Literal Symbol Certificate))
    {top : Nat} (focus : state.focus = .solve obligation)
    (fits : ∀ other ∈ expansion :: rest, Fits hoApplySymbol top other) (next : State Variable Literal Symbol Certificate Snapshot)
    (entered : state.enter obligation expansion rest = next) :
    Lower Below (weights hoApplySymbol next) (weightsWith hoApplySymbol top state) := by
  obtain ⟨added, elementsEq, bound⟩ := enter_elements (hoApplySymbol := hoApplySymbol) state obligation expansion rest
  rw [← entered, elementsEq]
  simp only [weightsWith, focus, branchElement, List.singleton_append]
  apply Lower.replace
  intro b member
  rcases List.mem_append.mp member with inAdded | inRest
  · have := bound b inAdded
    have fit := fits expansion List.mem_cons_self
    unfold Fits at fit
    exact below_of_lt (by simp only; omega)
  · obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp inRest
    have fit := fits other (List.mem_cons_of_mem _ otherMember)
    unfold Fits at fit
    exact below_of_lt (by simp only; omega)

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem sublist_flatMap {β γ : Type} {first second : List β} (sub : first.Sublist second) (f : β → List γ) :
    (first.flatMap f).Sublist (second.flatMap f) := by
  induction sub with
  | slnil => exact .slnil
  | cons x _ ih => simp only [List.flatMap_cons]; exact ih.trans (List.sublist_append_right _ _)
  | cons_cons x _ ih => simp only [List.flatMap_cons]; exact ih.append_left _

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem branchElement_second {top : Nat} {focus : Focus Variable Literal Symbol Certificate}
    {frames : List (Continuation Variable Literal Symbol Certificate)} {store : Store Variable Literal Symbol} :
    ∀ x ∈ branchElement hoApplySymbol top focus frames store, x.2 ≤ 2 * wokenCount frames + 1 := by
  intro x member
  cases focus <;> simp only [branchElement, List.mem_singleton, List.not_mem_nil] at member <;> subst member <;> simp

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem one_le_proceed (hoApplySymbol : Symbol) :
    ∀ frames : List (Continuation Variable Literal Symbol Certificate), 1 ≤ proceed hoApplySymbol frames
  | [] => by simp [proceed]
  | .frame _ :: rest => by have := one_le_proceed hoApplySymbol rest; simp only [proceed]; omega
  | .woken _ _ _ :: rest => by have := one_le_proceed hoApplySymbol rest; simp only [proceed]; omega
  | .negation _ _ _ :: _ => by simp [proceed]

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem storeWeight_suspend (store : Store Variable Literal Symbol) (suspension : Suspension Variable Literal Symbol) :
    storeWeight hoApplySymbol (store.suspend suspension) =
      suspensionWeight hoApplySymbol suspension + storeWeight hoApplySymbol store := by
  unfold storeWeight Store.suspend
  simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
/-- A branch that fails or is cut drops its weight. -/
theorem drop_lower {top : Nat} (state next : State Variable Literal Symbol Certificate Snapshot)
    (live : state.focus ≠ .failed) (failed : next.focus = .failed)
    (choices : (next.choices.flatMap (pointElements hoApplySymbol)).Sublist (state.choices.flatMap (pointElements hoApplySymbol))) :
    StepLower hoApplySymbol top next state := by
  left
  unfold weights weightsWith
  rw [failed]
  simp only [branchElement, List.nil_append]
  cases focus : state.focus with
  | failed => exact absurd focus live
  | solve obligation => simp only [List.singleton_append]; exact Lower.sublist choices _
  | proved tree => simp only [List.singleton_append]; exact Lower.sublist choices _

omit [DecidableEq Literal] [FreshNames Variable] in
/-- **Every machine step lowers the weights** of a state whose focused goal,
weighed `top`, is at least its size and outweighs every alternative the
strategy offers for it: one branch is replaced by smaller ones, or an empty
choice point is dropped. -/
theorem step_lower (strategy : Strategy Variable Literal Symbol Certificate)
    {state next : State Variable Literal Symbol Certificate Snapshot} (stepped : step strategy state = .running next)
    {top : Nat} (heavy : ∀ obligation, state.focus = .solve obligation →
      goalSize hoApplySymbol obligation.goal ≤ top ∧
        ∀ expansion ∈ (strategy obligation state.store).alternatives, Fits hoApplySymbol top expansion) :
    StepLower hoApplySymbol top next state := by
  cases hfocus : state.focus with
  | solve obligation =>
      obtain ⟨sized, fits⟩ := heavy obligation hfocus
      have live : state.focus ≠ .failed := by rw [hfocus]; exact fun same => by cases same
      cases hresponse : strategy obligation state.store with
      | candidates alternatives =>
          cases alternatives with
          | nil =>
              simp only [step, hfocus, hresponse] at stepped; cases stepped
              exact drop_lower _ _ live rfl (List.Sublist.refl _)
          | cons expansion rest =>
              simp only [step, hfocus, hresponse] at stepped; cases stepped
              left
              exact enter_lower state obligation expansion rest hfocus
                (by simpa [hresponse, Response.alternatives] using fits) _ rfl
      | unsupported =>
          simp only [step, hfocus, hresponse] at stepped; cases stepped
          exact drop_lower _ _ live rfl (List.Sublist.refl _)
      | incomplete alternatives =>
          cases alternatives with
          | nil =>
              simp only [step, hfocus, hresponse] at stepped; cases stepped
              exact drop_lower _ _ live rfl (List.Sublist.refl _)
          | cons expansion rest =>
              simp only [step, hfocus, hresponse] at stepped; cases stepped
              left
              let gapped : State Variable Literal Symbol Certificate Snapshot :=
                { state with focus := .solve obligation, gaps := ⟨.unsupported, obligation, trailOf state.frames⟩ :: state.gaps }
              have lower := enter_lower (hoApplySymbol := hoApplySymbol) gapped obligation expansion rest rfl
                (by simpa [hresponse, Response.alternatives] using fits) _ rfl
              unfold weightsWith at lower ⊢
              rw [hfocus]
              exact lower
      | delay names =>
          simp only [step, hfocus, hresponse] at stepped
          split at stepped
          · cases stepped
            left
            simp only [weights, weightsWith, hfocus, branchElement, List.singleton_append]
            refine Lower.replace (added := [_]) fun b member => ?_
            simp only [List.mem_singleton] at member
            subst member
            apply below_of_le
            · rw [storeWeight_suspend]
              simp only [suspensionWeight]
              omega
            · simp
          · cases stepped
            exact drop_lower _ _ live rfl (List.Sublist.refl _)
      | negate certificate =>
          simp only [step, hfocus, hresponse] at stepped
          split at stepped
          · rename_i operand goalEq
            split at stepped
            · cases stepped
              left
              rw [goalEq] at sized
              simp only [goalSize] at sized
              simp only [weights, weightsWith, hfocus, branchElement, focusSize, List.flatMap_cons, pointElements,
                Expansion.negation, startCost, proceed, List.map_cons, List.map_nil, List.singleton_append]
              refine Lower.replace (added := [_, _]) fun b member => ?_
              have one := two_le_goalSize hoApplySymbol operand
              have positive := one_le_proceed hoApplySymbol state.frames
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl
              · exact below_of_lt (by simp only; omega)
              · exact below_of_lt (by simp only; omega)
            · cases stepped
              exact drop_lower _ _ live rfl (List.Sublist.refl _)
          · cases stepped
            exact drop_lower _ _ live rfl (List.Sublist.refl _)
      | opened =>
          simp only [step, hfocus, hresponse] at stepped; cases stepped
          exact drop_lower _ _ live rfl (List.Sublist.refl _)
  | proved tree =>
      have live : state.focus ≠ .failed := by rw [hfocus]; exact fun same => by cases same
      cases hframes : state.frames with
      | nil =>
          simp only [step, hfocus, hframes] at stepped
          split at stepped
          · cases stepped
          · split at stepped
            · cases stepped
              exact drop_lower _ _ live rfl (List.Sublist.refl _)
            · rename_i pending more residual closing
              cases stepped
              left
              simp only [weights, weightsWith, hfocus, hframes, branchElement, List.singleton_append]
              apply Lower.replace
              intro b member
              apply below_of_lt
              rw [branchElement_bound b member, schedule_weight]
              simp only [storeWeight, Store.close, focusSize, proceed, closing, Bool.false_eq_true, ↓reduceIte,
                List.map_nil, List.sum_nil]
              omega
      | cons continuation frames =>
          cases continuation with
          | frame frame =>
              simp only [step, hfocus, hframes] at stepped
              split at stepped
              · rename_i node received
                cases stepped
                left
                simp only [weights, weightsWith, hfocus, hframes, branchElement, proceed,
                  List.singleton_append]
                refine Lower.replace (added := [_]) fun b member => ?_
                simp only [List.mem_singleton] at member
                subst member
                exact below_of_lt (by simp only; omega)
              · rename_i following received
                cases stepped
                left
                have pending := receive_pending received
                simp only [weights, weightsWith, hfocus, hframes, branchElement, focusSize, proceed,
                  List.singleton_append, pending, pendingWeight, List.map_cons, List.sum_cons, Machine.Frame.focus,
                  Obligation.premise]
                refine Lower.replace (added := [_]) fun b member => ?_
                simp only [List.mem_singleton] at member
                subst member
                exact below_of_lt (by simp only; omega)
          | woken id obligation following =>
              simp only [step, hfocus, hframes] at stepped
              cases stepped
              left
              simp only [weights, weightsWith, hfocus, hframes, branchElement, proceed, wokenCount, List.singleton_append]
              apply Lower.replace
              intro b member
              apply below_of_le
              · rw [branchElement_bound b member]; simp only; omega
              · have := branchElement_second b member; simp only; omega
          | negation obligation operand holes =>
              simp only [step, hfocus, hframes] at stepped
              cases stepped
              exact drop_lower _ _ live rfl (sublist_flatMap (cutNegation_sublist _) _)
  | failed =>
      cases hchoices : state.choices with
      | nil => simp only [step, hfocus, hchoices] at stepped; cases stepped
      | cons point choices =>
          simp only [step, hfocus, hchoices] at stepped
          split at stepped
          · rename_i empty
            cases stepped
            right
            refine ⟨?_, by rw [hchoices]; simp⟩
            simp only [weights, weightsWith, hfocus, hchoices, branchElement, List.flatMap_cons, pointElements, empty,
              List.map_nil, List.nil_append]
          · rename_i expansion rest alternatives
            split at stepped
            · cases stepped
              left
              let restored : State Variable Literal Symbol Certificate Snapshot :=
                { state with focus := .failed, store := point.store, frames := point.frames, deferred := point.deferred, choices := choices }
              obtain ⟨added, elementsEq, bound⟩ := enter_elements (hoApplySymbol := hoApplySymbol) restored
                point.obligation expansion rest
              rw [elementsEq]
              simp only [weightsWith, hfocus, hchoices, branchElement, List.flatMap_cons, pointElements, alternatives,
                List.map_cons, List.nil_append, List.cons_append]
              rw [List.append_assoc]
              apply Lower.replace
              intro b member
              have := bound b member
              exact below_of_lt (by simp only [restored] at this ⊢; omega)
            · cases stepped
              left
              simp only [weights, weightsWith, hfocus, hchoices, branchElement, List.flatMap_cons, pointElements,
                alternatives, List.map_cons, List.nil_append, List.cons_append]
              exact Lower.sublist (List.sublist_append_right _ _) _

end Step

end AnthillModKbSpec.Tabled
