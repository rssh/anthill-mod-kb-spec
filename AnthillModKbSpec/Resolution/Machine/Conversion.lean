import AnthillModKbSpec.Resolution.Machine.Reconstruction

/-! # `ho_apply` conversion (S11)

A direct call `p(args)` and the indirect call `ho_apply(p, args)` are
interderivable (`Derives.hoApplyIntro`, `Derives.hoApplyElim`). The machine
uses that as a proof step, never as a goal rewrite, so the two directions
cannot loop:

- **`ho_goal`.** A goal reading as a concrete indirect call `ho_apply(p, args)`
  is normalized once to the direct goal `p(args)`, its node `hoApplyIntro`
  (`Expansion.hoGoal`). No direct goal is ever rewritten back.
- **Indirect views.** A direct goal is compared with a candidate concluding a
  call by `ho_apply` through the goal's *indirect view*: the goal with its
  conclusion, itself or the conclusion of its implications, as an indirect
  call (`Term.indirect?`, `Indirect`). The S05 matcher compares the candidate
  with the view, so `Store.unify_sound` and the commit replay are unchanged; a
  flexible predicate name of the candidate is bound to the goal's predicate
  symbol by that match, a rigid one is never assigned. The candidate's node is
  wrapped as `converted view`: it proves the view, and conversion by
  elimination, under the implications, proves the goal (`Derives.ofIndirect`).
  The reverse, a direct conclusion for a goal applying a flexible name, matches
  the goal against the conclusion's view and converts by introduction.
- **Static classification.** `compare` reads a candidate's conclusion against
  the goal: the same head (`direct`, S05), the two conversions, a conclusion
  applying a name it may bind that only a lambda-valued answer could make the
  goal (`lambda`: unsupported, since `Term` has no lambda; `compareAtom_lambda`
  shows no instance is the goal or its view), or `apart`. Structural reference
  matching binds a predicate name to a symbol value; general higher-order
  unification is not attempted.

Direct and indirect calls thus share one candidate view: an indirect goal is
answered as its direct form, and a direct goal reaches indirect candidates
through its view. -/

namespace AnthillModKbSpec

variable {Variable Literal Symbol : Type}

/-- `view` is the indirect view of `goal`: the same formula, with its
conclusion (the formula itself, or the conclusion of its implications) a direct
call `p(args)` in `goal` and `ho_apply(p, args)` in `view`. -/
inductive Indirect (hoApplySymbol : Symbol) : Term Variable Literal Symbol → Term Variable Literal Symbol → Prop where
  | call {symbol : Symbol} {args : List (Term Variable Literal Symbol)} (ordinary : symbol ≠ hoApplySymbol) :
      Indirect hoApplySymbol (.hoApply hoApplySymbol (.app symbol []) args) (.app symbol args)
  | imp {premise view goal : Term Variable Literal Symbol} (conclusion : Indirect hoApplySymbol view goal) :
      Indirect hoApplySymbol (.imp premise view) (.imp premise goal)

/-- Either formula is the other's indirect view: a proof of one converts to a
proof of the other. -/
def Converts (hoApplySymbol : Symbol) (conclusion goal : Term Variable Literal Symbol) : Prop :=
  Indirect hoApplySymbol conclusion goal ∨ Indirect hoApplySymbol goal conclusion

section Views

variable [DecidableEq Symbol] {hoApplySymbol : Symbol}

/-- The indirect view of a formula whose conclusion is a direct call. -/
def Term.indirect? (hoApplySymbol : Symbol) : Term Variable Literal Symbol → Option (Term Variable Literal Symbol)
  | .app symbol args => if symbol = hoApplySymbol then none else some (.hoApply hoApplySymbol (.app symbol []) args)
  | .imp premise conclusion => (conclusion.indirect? hoApplySymbol).map (.imp premise)
  | _ => none

theorem Term.indirect?_spec : ∀ {term view : Term Variable Literal Symbol},
    term.indirect? hoApplySymbol = some view → Indirect hoApplySymbol view term
  | .app symbol args, view, found => by
      unfold Term.indirect? at found
      split at found
      · cases found
      · rename_i ordinary; cases found; exact .call ordinary
  | .imp premise conclusion, view, found => by
      simp only [Term.indirect?, Option.map_eq_some_iff] at found
      obtain ⟨inner, found, rfl⟩ := found
      exact .imp (Term.indirect?_spec found)
  | .var _, _, found | .lit _, _, found | .truth, _, found | .falsity, _, found | .conj _ _, _, found
  | .disj _ _, _, found | .defaultNeg _, _, found | .forallVar _ _, _, found | .existsVar _ _, _, found
  | .dictionaryCall _ _ _ _, _, found | .equal _ _, _, found => by cases found

/-- A concrete indirect call `ho_apply(p, args)`, `p` not `ho_apply` itself:
its predicate symbol and arguments. -/
def Term.call? (hoApplySymbol : Symbol) : Term Variable Literal Symbol → Option (Symbol × List (Term Variable Literal Symbol))
  | .app applied (.app symbol [] :: args) => if applied = hoApplySymbol ∧ symbol ≠ hoApplySymbol then some (symbol, args) else none
  | _ => none

theorem Term.call?_spec {term : Term Variable Literal Symbol} {symbol : Symbol} {args : List (Term Variable Literal Symbol)}
    (found : term.call? hoApplySymbol = some (symbol, args)) :
    term = .hoApply hoApplySymbol (.app symbol []) args ∧ symbol ≠ hoApplySymbol := by
  unfold Term.call? at found
  split at found
  · split at found
    · rename_i same; obtain ⟨rfl, ordinary⟩ := same; cases found; exact ⟨rfl, ordinary⟩
    · cases found
  · cases found

/-- An ordinary application is no concrete indirect call. -/
theorem Term.call?_ordinary {applied : Symbol} (ordinary : applied ≠ hoApplySymbol)
    (args : List (Term Variable Literal Symbol)) : (Term.app applied args).call? hoApplySymbol = none := by
  unfold Term.call?
  split
  · next same symbol rest heq =>
      simp only [Term.app.injEq] at heq
      obtain ⟨rfl, _⟩ := heq
      simp [ordinary]
  · rfl

end Views

section Derivations

variable [DecidableEq Variable] {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
  {naf : NafFailure Variable Literal Symbol}

/-- Conversion by elimination: a proof of the indirect view proves the goal.
Under an implication `A → V`, a cut on it: `A → G` by implication
introduction, `V` from the cut and `A`, then the inner conversion. No
weakening or transport of context-indexed evidence is needed. -/
theorem Derives.ofIndirect {view goal : Formula Variable Literal Symbol} (indirect : Indirect hoApplySymbol view goal) :
    ∀ {context : ProofContext Variable Literal Symbol}, Derives hoApplySymbol kb context view naf →
      Derives hoApplySymbol kb context goal naf := by
  induction indirect with
  | call => exact fun proof => .hoApplyElim proof
  | imp _ ih =>
      exact fun proof => Derives.cut proof (.impIntro (ih (.impElim
        (.assumption (List.mem_cons_of_mem _ List.mem_cons_self)) (.assumption List.mem_cons_self))))

/-- Conversion by introduction: a proof of the goal proves its indirect view. -/
theorem Derives.toIndirect {view goal : Formula Variable Literal Symbol} (indirect : Indirect hoApplySymbol view goal) :
    ∀ {context : ProofContext Variable Literal Symbol}, Derives hoApplySymbol kb context goal naf →
      Derives hoApplySymbol kb context view naf := by
  induction indirect with
  | call => exact fun proof => .hoApplyIntro proof
  | imp _ ih =>
      exact fun proof => Derives.cut proof (.impIntro (ih (.impElim
        (.assumption (List.mem_cons_of_mem _ List.mem_cons_self)) (.assumption List.mem_cons_self))))

theorem Converts.derives {conclusion goal : Formula Variable Literal Symbol}
    (converts : Converts hoApplySymbol conclusion goal) {context : ProofContext Variable Literal Symbol}
    (proof : Derives hoApplySymbol kb context conclusion naf) : Derives hoApplySymbol kb context goal naf := by
  rcases converts with indirect | indirect
  · exact Derives.ofIndirect indirect proof
  · exact Derives.toIndirect indirect proof

end Derivations

namespace Machine

section Reading

variable [DecidableEq Variable] [FreshNames Variable] {hoApplySymbol : Symbol}

/-- A view read through the answers is the view of the read goal. -/
theorem _root_.AnthillModKbSpec.Indirect.resolve (store : Store Variable Literal Symbol) {view goal : Term Variable Literal Symbol}
    (indirect : Indirect hoApplySymbol view goal) :
    Indirect hoApplySymbol (store.resolve view) (store.resolve goal) := by
  induction indirect with
  | call ordinary =>
      simp only [Term.hoApply, Store.resolve_app, List.map_cons, List.map_nil]
      exact .call ordinary
  | imp _ ih => simp only [Store.resolve_imp]; exact .imp ih

theorem _root_.AnthillModKbSpec.Converts.resolve (store : Store Variable Literal Symbol) {conclusion goal : Term Variable Literal Symbol}
    (converts : Converts hoApplySymbol conclusion goal) :
    Converts hoApplySymbol (store.resolve conclusion) (store.resolve goal) :=
  converts.imp (Indirect.resolve store) (Indirect.resolve store)

end Reading

/-! ## Comparing a conclusion with a goal -/

variable [DecidableEq Symbol]

/-- The index of atomic and falsity goals: the same symbol and arity, or both
falsity. -/
def sameHead : Term Variable Literal Symbol → Term Variable Literal Symbol → Bool
  | .app left leftArgs, .app right rightArgs => decide (left = right) && leftArgs.length == rightArgs.length
  | .falsity, .falsity => true
  | _, _ => false

/-- An application by `ho_apply` against a direct one of the matching arity, or
the reverse: comparing them needs `ho_apply` conversion. -/
def hoMixed (hoApplySymbol : Symbol) : Term Variable Literal Symbol → Term Variable Literal Symbol → Bool
  | .app left leftArgs, .app right rightArgs =>
      (decide (left = hoApplySymbol) && decide (right ≠ hoApplySymbol) && leftArgs.length == rightArgs.length + 1) ||
        (decide (right = hoApplySymbol) && decide (left ≠ hoApplySymbol) && rightArgs.length == leftArgs.length + 1)
  | _, _ => false

/-- A whole formula the S05 matcher compares as it is: the same constructor at
the top other than an application, binders included; a conclusion that is a
name; or an operation call on either side, which the matcher reports as a gap. -/
def sameKind : Term Variable Literal Symbol → Term Variable Literal Symbol → Bool
  | _, .var _ | .dictionaryCall _ _ _ _, _ | _, .dictionaryCall _ _ _ _ => true
  | .lit _, .lit _ | .truth, .truth | .falsity, .falsity | .conj _ _, .conj _ _ | .disj _ _, .disj _ _
  | .imp _ _, .imp _ _ | .defaultNeg _, .defaultNeg _ | .forallVar _ _, .forallVar _ _
  | .existsVar _ _, .existsVar _ _ | .equal _ _, .equal _ _ => true
  | _, _ => false

/-- A call: an application. -/
def isCall : Term Variable Literal Symbol → Bool
  | .app _ _ => true
  | _ => false

/-- The term applies, by `ho_apply`, a name `binds` admits. -/
def appliesName (hoApplySymbol : Symbol) (binds : Variable → Bool) : Term Variable Literal Symbol → Bool
  | .app applied (.var name :: _) => decide (applied = hoApplySymbol) && binds name
  | _ => false

/-- The predicate a goal applies by `ho_apply`, as introduction sees it: a name
the goal may bind, or a reference (a symbol value). A rigid name or a compound
term is neither: nothing assigns or converts it. -/
def introducible (assignable : Variable → Bool) : Term Variable Literal Symbol → Bool
  | .app _ (.var name :: _) => assignable name
  | .app _ (.app _ [] :: _) => true
  | _ => false

/-- How a candidate's conclusion compares with a goal, both as read. -/
inductive Comparison where
  /-- The same head, or for whole formulas the same kind: the S05 matcher
  compares them. -/
  | direct
  /-- The conclusion is a call by `ho_apply`, the goal a direct call: the
  conclusion is matched against the goal's indirect view, and the candidate's
  proof converted by elimination. -/
  | elim
  /-- The conclusion is a direct call, the goal a call by `ho_apply` of a name
  it may bind or of a reference: the goal is matched against the conclusion's
  indirect view, and the candidate's proof converted by introduction. -/
  | intro
  /-- Both are calls, one applies a name its side may bind by `ho_apply`, and
  only a lambda-valued answer for that name could make the conclusion the
  goal, such as one of another arity: unsupported, a gap. `Term` has no lambda,
  and this is not general higher-order unification (`compareAtom_lambda`). -/
  | lambda
  /-- The conclusion's shape never gives the goal. -/
  | apart
  deriving DecidableEq, Repr

/-- Compare an atomic conclusion with an atomic or falsity goal. `binds` admits
the names the candidate may bind, `assignable` those the goal may bind:

- the same head is `direct`;
- an indirect conclusion against a direct goal of the matching arity is
  elimination;
- a direct conclusion against an indirect goal of the matching arity is
  introduction when the goal applies a name it may bind or a reference, and
  `apart` when it applies a rigid name or a compound term;
- two other calls are `lambda` when either applies a name its side may bind;
- a goal that is no call, falsity included, is never an instance of an
  application, and a lambda-valued formula is not considered for it: `apart`. -/
def compareAtom (hoApplySymbol : Symbol) (binds assignable : Variable → Bool)
    (goal conclusion : Term Variable Literal Symbol) : Comparison :=
  if sameHead goal conclusion then .direct
  else if hoMixed hoApplySymbol goal conclusion then
    (match conclusion with
      | .app applied _ =>
          if applied = hoApplySymbol then .elim else if introducible assignable goal then .intro else .apart
      | _ => .apart)
  else if isCall goal && isCall conclusion &&
      (appliesName hoApplySymbol binds conclusion || appliesName hoApplySymbol assignable goal) then .lambda
  else .apart

/-- Compare a conclusion with a goal through their implications, as a whole
formula: the premises are left to the matcher; conclusions of the same kind are
compared by it as they are, and calls by `compareAtom`, so the classification
reads the goal's conclusion. -/
def compare (hoApplySymbol : Symbol) (binds assignable : Variable → Bool) :
    Term Variable Literal Symbol → Term Variable Literal Symbol → Comparison
  | .imp _ goal, .imp _ conclusion => compare hoApplySymbol binds assignable goal conclusion
  | goal, conclusion =>
      if sameKind goal conclusion then .direct else compareAtom hoApplySymbol binds assignable goal conclusion

/-- Two calls with neither the same head nor heads that differ only by
`ho_apply` have no common instance, directly or through either one's indirect
view. -/
theorem calls_apart [DecidableEq Variable] [FreshNames Variable] {hoApplySymbol : Symbol}
    {goal conclusion : Term Variable Literal Symbol} (goalCall : isCall goal = true)
    (conclusionCall : isCall conclusion = true) (notHead : sameHead goal conclusion = false)
    (notMixed : hoMixed hoApplySymbol goal conclusion = false) (σ : Substitution Variable Literal Symbol) :
    conclusion.instantiate σ ≠ goal.instantiate σ ∧
      (∀ view, goal.indirect? hoApplySymbol = some view → conclusion.instantiate σ ≠ view.instantiate σ) ∧
      (∀ view, conclusion.indirect? hoApplySymbol = some view → view.instantiate σ ≠ goal.instantiate σ) := by
  cases goal <;> simp only [isCall, Bool.false_eq_true] at goalCall
  cases conclusion <;> simp only [isCall, Bool.false_eq_true] at conclusionCall
  rename_i g ys f xs
  simp only [sameHead, Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq] at notHead
  simp only [hoMixed, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne,
    ne_eq, Decidable.not_not] at notMixed
  have lengths : ∀ {left right : List (Term Variable Literal Symbol)}, left.map (Term.instantiate σ) =
      right.map (Term.instantiate σ) → left.length = right.length := fun same => by
    simpa using congrArg List.length same
  refine ⟨fun same => ?_, fun view found same => ?_, fun view found same => ?_⟩
  · simp only [Term.instantiate, Term.app.injEq] at same
    obtain ⟨rfl, same⟩ := same
    rcases notHead with different | different
    · exact different rfl
    · exact different (lengths same).symm
  · simp only [Term.indirect?] at found
    split at found
    · cases found
    · rename_i ordinary
      cases found
      simp only [Term.hoApply, Term.instantiate, List.map_cons, List.map_nil, Term.app.injEq] at same
      obtain ⟨rfl, same⟩ := same
      have counted := congrArg List.length same
      simp only [List.length_map, List.length_cons] at counted
      simp_all
  · simp only [Term.indirect?] at found
    split at found
    · cases found
    · rename_i ordinary
      cases found
      simp only [Term.hoApply, Term.instantiate, List.map_cons, List.map_nil, Term.app.injEq] at same
      obtain ⟨rfl, same⟩ := same
      have counted := congrArg List.length same
      simp only [List.length_map, List.length_cons] at counted
      simp_all

/-- A `lambda` comparison has no common instance of the conclusion and the
goal, directly or through either one's indirect view: only a lambda-valued
answer could conclude the goal from it. Structural reference matching has
nothing to propose, and the gap stands for what general higher-order
unification might find, which is not attempted. -/
theorem compareAtom_lambda [DecidableEq Variable] [FreshNames Variable] {hoApplySymbol : Symbol}
    {binds assignable : Variable → Bool} {goal conclusion : Term Variable Literal Symbol}
    (classified : compareAtom hoApplySymbol binds assignable goal conclusion = .lambda)
    (σ : Substitution Variable Literal Symbol) :
    conclusion.instantiate σ ≠ goal.instantiate σ ∧
      (∀ view, goal.indirect? hoApplySymbol = some view → conclusion.instantiate σ ≠ view.instantiate σ) ∧
      (∀ view, conclusion.indirect? hoApplySymbol = some view → view.instantiate σ ≠ goal.instantiate σ) := by
  unfold compareAtom at classified
  split at classified
  · cases classified
  rename_i notHead
  split at classified
  · split at classified
    · split at classified
      · cases classified
      · split at classified <;> cases classified
    · cases classified
  rename_i notMixed
  split at classified
  · rename_i calls
    simp only [Bool.and_eq_true] at calls
    exact calls_apart calls.1.1 calls.1.2 (by simpa using notHead) (by simpa using notMixed) σ
  · cases classified

/-! ## Commands and their contracts -/

section Commands

variable [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] {Certificate : Type}

namespace Expansion

/-- `ho_goal`: a goal reading as the concrete indirect call `ho_apply(p, args)`
is normalized to the direct goal `p(args)`, its node `hoApplyIntro`. -/
def hoGoal (symbol : Symbol) (args : List (Term Variable Literal Symbol)) : Expansion Variable Literal Symbol Certificate :=
  { rule := .hoApplyIntro, premises := [{ goal := .app symbol args }] }

/-- `inner`, built for `conclusion`, applied for a goal that converts from it:
the same premises, names, and bindings. -/
def convert (conclusion : Formula Variable Literal Symbol) (inner : Expansion Variable Literal Symbol Certificate) :
    Expansion Variable Literal Symbol Certificate :=
  { inner with rule := .converted conclusion inner.rule }

variable {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}
  {scope : Scope Variable Literal Symbol} {store : Store Variable Literal Symbol}

omit [DecidableEq Symbol] [DecidableEq Literal] in
theorem hoGoal_soundUnder {goal : Formula Variable Literal Symbol} {symbol : Symbol}
    {args : List (Term Variable Literal Symbol)}
    (read : store.resolve goal = store.resolve (.hoApply hoApplySymbol (.app symbol []) args)) :
    (hoGoal (Certificate := Certificate) symbol args).SoundUnder hoApplySymbol kb naf store ⟨scope, goal⟩ :=
  fun proofs => by
    have premise := read_premise.mp (proofs { goal := .app symbol args } (by simp [hoGoal]))
    simp only [List.map_nil, List.nil_append, Store.resolve_app] at premise
    simp only [ReadDerives, Obligation.context, read, Term.hoApply, Store.resolve_app, List.map_cons, List.map_nil]
    exact .hoApplyIntro premise

omit [DecidableEq Symbol] [DecidableEq Literal] in
/-- A candidate sound for its conclusion is sound, converted, for a goal that
converts from that conclusion. -/
theorem convert_soundUnder {conclusion goal : Formula Variable Literal Symbol}
    {inner : Expansion Variable Literal Symbol Certificate}
    (sound : inner.SoundUnder hoApplySymbol kb naf store ⟨scope, conclusion⟩)
    (converts : Converts hoApplySymbol (store.resolve conclusion) (store.resolve goal)) :
    (inner.convert conclusion).SoundUnder hoApplySymbol kb naf store ⟨scope, goal⟩ :=
  fun proofs => converts.derives (sound fun premise inside => proofs premise inside)

end Expansion

/-- A candidate built by `make` for a conclusion compared with the goal as
`comparison`, its new names `flexibles`:

- `direct`: the conclusion matched against the goal (S05);
- elimination: the conclusion matched against the goal's indirect view, the
  candidate converted;
- introduction: the goal matched against the conclusion's view, the
  candidate converted. Where `intro` does not admit it, a gap: it would choose
  a predicate for the goal's name among the program's clauses, which needs an
  admitted finite candidate set;
- a lambda answer is a gap, and `apart` a miss. -/
def conclusionAttempt (hoApplySymbol : Symbol) (obligation : Obligation Variable Literal Symbol)
    (store : Store Variable Literal Symbol) (flexibles : List Variable) (comparison : Comparison)
    (conclusion : Formula Variable Literal Symbol)
    (make : List (Variable × Term Variable Literal Symbol) → Expansion Variable Literal Symbol Certificate)
    (intro : Bool) : Attempt Variable Literal Symbol Certificate :=
  match comparison with
  | .direct =>
      attempt ((store.prepare obligation flexibles []).unify obligation.scope hoApplySymbol conclusion obligation.goal) make
  | .elim =>
      match (store.resolve obligation.goal).indirect? hoApplySymbol with
      | some view =>
          attempt ((store.prepare obligation flexibles []).unify obligation.scope hoApplySymbol conclusion view)
            fun bindings => (make bindings).convert view
      | none => none
  | .intro =>
      if intro then
        match (store.resolve conclusion).indirect? hoApplySymbol with
        | some view =>
            attempt ((store.prepare obligation flexibles []).unify obligation.scope hoApplySymbol view obligation.goal)
              fun bindings => (make bindings).convert conclusion
        | none => none
      else none
  | .lambda => none
  | .apart => some none

variable {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}
  {obligation : Obligation Variable Literal Symbol} {store : Store Variable Literal Symbol}

/-- A match-built candidate is sound when its contract holds in every scoped
store refining the match's where the matched sides read the same. -/
theorem attempt_sound_refines (valid : store.Scoped) {flexibles : List Variable}
    {left right : Term Variable Literal Symbol}
    {make : List (Variable × Term Variable Literal Symbol) → Expansion Variable Literal Symbol Certificate}
    (shape : ∀ bindings, (make bindings).flexibles = flexibles ∧ (make bindings).rigids = [] ∧
      (make bindings).bindings = bindings)
    (matched : ∀ bindings (later : Store Variable Literal Symbol), store.Refines later → later.Scoped →
      later.resolve left = later.resolve right → NodeSound hoApplySymbol kb naf later obligation (make bindings).premises) :
    AttemptSound hoApplySymbol kb naf store obligation
      (attempt ((store.prepare obligation flexibles []).unify obligation.scope hoApplySymbol left right) make) := by
  intro expansion found next woken committed later refines laterScoped
  unfold attempt at found
  split at found
  · rename_i final bindings computed
    cases found
    obtain ⟨sameFlexibles, noRigids, sameBindings⟩ := shape bindings
    rw [sameFlexibles, noRigids, sameBindings] at committed
    exact matched bindings later ((Store.commit_refines committed).trans refines) laterScoped
      (refines.resolve_eq (Store.commit_matched valid computed committed))
  all_goals cases found

/-- A conclusion's candidate is sound when the candidate `make` builds is sound,
in every scoped store refining the match's, for every goal the conclusion reads
as: the goal itself, the view it is matched against, or the conclusion. -/
theorem conclusionAttempt_sound_scoped (valid : store.Scoped) {flexibles : List Variable}
    {comparison : Comparison} {conclusion : Formula Variable Literal Symbol}
    {make : List (Variable × Term Variable Literal Symbol) → Expansion Variable Literal Symbol Certificate}
    {intro : Bool}
    (shape : ∀ bindings, (make bindings).flexibles = flexibles ∧ (make bindings).rigids = [] ∧
      (make bindings).bindings = bindings)
    (inner : ∀ bindings (later : Store Variable Literal Symbol) (target : Formula Variable Literal Symbol),
      store.Refines later → later.Scoped → later.resolve conclusion = later.resolve target →
        NodeSound hoApplySymbol kb naf later ⟨obligation.scope, target⟩ (make bindings).premises) :
    AttemptSound hoApplySymbol kb naf store obligation
      (conclusionAttempt hoApplySymbol obligation store flexibles comparison conclusion make intro) := by
  unfold conclusionAttempt
  split
  · exact attempt_sound_refines valid shape fun bindings later refines laterScoped matched =>
      inner bindings later obligation.goal refines laterScoped matched
  · split
    · rename_i view found
      refine attempt_sound_refines valid (fun bindings => shape bindings)
        fun bindings later refines laterScoped matched => ?_
      have indirect := (Term.indirect?_spec found).resolve later
      rw [← valid.read_refines rfl refines] at indirect
      exact Expansion.convert_soundUnder (inner bindings later view refines laterScoped matched) (.inl indirect)
    · intro _ found; cases found
  · split
    · split
      · rename_i view found
        refine attempt_sound_refines valid (fun bindings => shape bindings)
          fun bindings later refines laterScoped matched => ?_
        have indirect := (Term.indirect?_spec found).resolve later
        rw [← valid.read_refines rfl refines, matched] at indirect
        exact Expansion.convert_soundUnder (inner bindings later conclusion refines laterScoped rfl) (.inr indirect)
      · intro _ found; cases found
    · intro _ found; cases found
  all_goals intro _ found; cases found

/-- A conclusion's candidate is sound when the candidate `make` builds is sound
for every goal the conclusion reads as: the goal itself, the view it is matched
against, or the conclusion. -/
theorem conclusionAttempt_sound (valid : store.Scoped) {flexibles : List Variable}
    {comparison : Comparison} {conclusion : Formula Variable Literal Symbol}
    {make : List (Variable × Term Variable Literal Symbol) → Expansion Variable Literal Symbol Certificate}
    {intro : Bool}
    (shape : ∀ bindings, (make bindings).flexibles = flexibles ∧ (make bindings).rigids = [] ∧
      (make bindings).bindings = bindings)
    (inner : ∀ bindings (later : Store Variable Literal Symbol) (target : Formula Variable Literal Symbol),
      later.resolve conclusion = later.resolve target →
        NodeSound hoApplySymbol kb naf later ⟨obligation.scope, target⟩ (make bindings).premises) :
    AttemptSound hoApplySymbol kb naf store obligation
      (conclusionAttempt hoApplySymbol obligation store flexibles comparison conclusion make intro) :=
  conclusionAttempt_sound_scoped valid shape fun bindings later target _ _ matched => inner bindings later target matched

omit [DecidableEq Literal] in
/-- `ho_goal` is sound: the goal reads as the indirect call in every later store. -/
theorem hoGoal_sound (valid : store.Scoped) {symbol : Symbol} {args : List (Term Variable Literal Symbol)}
    (found : (store.resolve obligation.goal).call? hoApplySymbol = some (symbol, args)) :
    CandidateSound hoApplySymbol kb naf store obligation (Expansion.hoGoal (Certificate := Certificate) symbol args) :=
  fixed_sound fun later refines => Expansion.hoGoal_soundUnder
    (by rw [valid.read_refines rfl refines, (Term.call?_spec found).1])

end Commands

end Machine

end AnthillModKbSpec
