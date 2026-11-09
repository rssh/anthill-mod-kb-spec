import AnthillModKbSpec.Resolution.Machine.LeftStrategy

/-! # Checked lemmas inside machine runs (S20)

A run may close a subgoal with a checked lemma instead of rediscovering it.
The machine sees the lemmas through `Lemmas`: each lemma's name and statement,
a decision whether a lemma holds under a context, and whether its own context
is among a context's assumptions. Its soundness (`Lemmas.Sound`) is that what
the decision accepts is derivable under exactly that context. The run's checker
supplies them (`P1.lemmasFor`): only lemmas
checked against the lemmas older than them are offered, and a lemma holds at a
use site when its proof checks again under the use site's context, as S08's
references are checked. A lemma proved under assumptions is not a global fact,
and no weakening is assumed.

Three commands use a lemma, mirroring how a local rule is used:

| Command | Lemma `∀x̄. M`, at witnesses | Premises |
| --- | --- | --- |
| `lemmaUse` | the instance concludes the goal: an atom, falsity, an equation, or a NAF formula compared with it, or the whole statement read as the goal | — |
| `lemmaRule` | the instance `B → H`, `H` simple and compared with the goal | `B` |
| `lemmaCut` | any instance, chosen by a `LemmaSelection` | the goal under the instance |

`lemmaUse` and `lemmaRule` backchain at fresh flexible witnesses, as `positive`
uses a local rule, and are offered wherever the conclusion may conclude the
goal. An atom is compared as a local rule's conclusion is (S11): through an
indirect view where the two differ by `ho_apply`, the node then converted. A
compound conclusion is used through a cut: the instance becomes an assumption
of the continuation, where the S09 commands and local rules use it.

A lemma is re-checked once, at the focus, under the context as read, and only
for a conclusion that matches. That reading must stay the same for the rest of
the branch, where the node's contract is read: the context and the statement
must name only rigid names (`Store.lemmaSite`). Otherwise a binding could still
change the context, and the lemma is a gap there, never a miss. A lemma whose
own context is not among the use site's assumptions does not apply: a miss.
One whose context is there but whose proof does not check under the use site's
context is a gap: its proof is checked as written, so its context-indexed NAF
evidence or an eigenvariable the use site's context names makes it fail there,
which is no evidence about the goal. Each command's contract is the lemma's
derivation, read through every later store (`Lemmas.Sound.later`), followed by
universal eliminations and implication elimination or a cut
(`Expansion.lemma*_soundUnder`), so the extended strategy is sound
(`withLemmas_sound_within`). -/

namespace AnthillModKbSpec.Machine

variable {Variable Literal Symbol Certificate Snapshot : Type}

/-- The lemmas a run may use, as the machine sees them: each lemma's name and
statement; a decision whether the lemma with that name and statement holds
under a context; and whether its own context is among a context's
assumptions, where it applies even if its proof does not check there. -/
structure Lemmas (Variable Literal Symbol : Type) where
  statements : List (Symbol × Formula Variable Literal Symbol)
  holds : ProofContext Variable Literal Symbol → Symbol → Formula Variable Literal Symbol → Bool
  applies : ProofContext Variable Literal Symbol → Symbol → Formula Variable Literal Symbol → Bool

/-- No lemma. -/
def Lemmas.none : Lemmas Variable Literal Symbol := ⟨[], fun _ _ _ => false, fun _ _ _ => false⟩

/-- What `holds` accepts is derivable under exactly that context. -/
def Lemmas.Sound [DecidableEq Variable] (hoApplySymbol : Symbol) (kb : LogicalKb Variable Literal Symbol)
    (naf : NafFailure Variable Literal Symbol) (lemmas : Lemmas Variable Literal Symbol) : Prop :=
  ∀ context name statement, lemmas.holds context name statement = true →
    Derives hoApplySymbol kb context statement naf

theorem Lemmas.none_sound [DecidableEq Variable] {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol} : (Lemmas.none : Lemmas Variable Literal Symbol).Sound hoApplySymbol kb naf :=
  fun _ _ _ holds => by cases holds

/-! ## Use sites that keep their reading -/

section Fixed

variable [DecidableEq Variable]

/-- Every free name of the term is rigid in the store: no binding changes its
reading. -/
def Store.fixed (store : Store Variable Literal Symbol) (term : Term Variable Literal Symbol) : Bool :=
  term.freeVars.all fun name => decide (store.info? name = some .rigid)

/-- A use site of a lemma: its statement and the context as read name only
rigid names, so both read the same for the rest of the branch. -/
def Store.lemmaSite (store : Store Variable Literal Symbol)
    (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) (statement : Term Variable Literal Symbol) :
    Bool :=
  store.fixed statement && context.all fun pair => store.fixed pair.2

theorem Store.fixed_refines {store later : Store Variable Literal Symbol} (refines : store.Refines later)
    {term : Term Variable Literal Symbol} (fixed : store.fixed term = true) : later.fixed term = true := by
  simp only [Store.fixed, List.all_eq_true, decide_eq_true_eq] at fixed ⊢
  exact fun name inside => refines.rigid name (fixed name inside)

variable [FreshNames Variable]

/-- A scoped store binds only flexible names, so it reads a fixed term as itself. -/
theorem Store.Scoped.resolve_fixed {store : Store Variable Literal Symbol} (valid : store.Scoped)
    {term : Term Variable Literal Symbol} (fixed : store.fixed term = true) : store.resolve term = term := by
  apply resolveWith_unbound
  intro name inside bound
  simp only [Store.fixed, List.all_eq_true, decide_eq_true_eq] at fixed
  obtain ⟨⟨_, value⟩, member, rfl⟩ := List.mem_map.mp bound
  obtain ⟨dependencies, flexible, _⟩ := valid.answers _ value member
  rw [fixed _ inside] at flexible
  cases flexible

/-- A term that reads as a fixed term reads the same in every scoped
refinement. -/
theorem Store.Scoped.read_fixed {store later : Store Variable Literal Symbol} (valid : store.Scoped)
    (refines : store.Refines later) (laterScoped : later.Scoped) {term : Term Variable Literal Symbol}
    (fixed : store.fixed (store.resolve term) = true) : later.resolve term = store.resolve term := by
  rw [valid.read_refines rfl refines]
  exact laterScoped.resolve_fixed (Store.fixed_refines refines fixed)

/-- At a use site, a lemma that holds under the context as read is derivable
under the obligation's context read through every scoped refinement: the
context and the statement read the same there. -/
theorem Lemmas.Sound.later {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol} {lemmas : Lemmas Variable Literal Symbol}
    (sound : lemmas.Sound hoApplySymbol kb naf) {store later : Store Variable Literal Symbol}
    {obligation : Obligation Variable Literal Symbol} {name : Symbol} {statement : Formula Variable Literal Symbol}
    (valid : store.Scoped) (site : store.lemmaSite (store.readContext obligation) statement = true)
    (holds : lemmas.holds ((store.readContext obligation).map Prod.snd) name statement = true)
    (refines : store.Refines later) (laterScoped : later.Scoped) :
    Derives hoApplySymbol kb (obligation.context.map later.resolve) (later.resolve statement) naf := by
  simp only [Store.lemmaSite, Bool.and_eq_true, List.all_eq_true] at site
  have derived := sound _ name statement holds
  have context : obligation.context.map later.resolve = (store.readContext obligation).map Prod.snd := by
    simp only [Store.readContext, List.map_map]
    refine List.map_congr_left fun assumption member => ?_
    exact valid.read_fixed refines laterScoped
      (site.2 (assumption, store.resolve assumption) (List.mem_map_of_mem member))
  rw [context, laterScoped.resolve_fixed (Store.fixed_refines refines site.1)]
  exact derived

end Fixed

/-! ## The lemma commands and their contracts -/

namespace Expansion

/-- A lemma's instance at `witnesses` concludes the goal, matched against it
(`bindings`). `flexibles` are the fresh names among the witnesses. -/
def lemmaUse (name : Symbol) (statement : Formula Variable Literal Symbol) (witnesses : List (Term Variable Literal Symbol))
    (flexibles : List Variable) (bindings : List (Variable × Term Variable Literal Symbol)) :
    Expansion Variable Literal Symbol Certificate :=
  { rule := .derived (.lemmaUse name statement witnesses), flexibles := flexibles, bindings := bindings }

/-- A lemma's instance `premise → conclusion`: the conclusion matched against
the goal (`bindings`), the premise the one obligation. -/
def lemmaRule (name : Symbol) (statement : Formula Variable Literal Symbol) (witnesses : List (Term Variable Literal Symbol))
    (premise : Formula Variable Literal Symbol) (flexibles : List Variable)
    (bindings : List (Variable × Term Variable Literal Symbol)) : Expansion Variable Literal Symbol Certificate :=
  { rule := .derived (.lemmaRule name statement witnesses), flexibles := flexibles, bindings := bindings
    premises := [{ goal := premise }] }

/-- A lemma's instance assumed by the continuation: the goal under it. -/
def lemmaCut (name : Symbol) (statement : Formula Variable Literal Symbol) (witnesses : List (Term Variable Literal Symbol))
    (instantiated goal : Formula Variable Literal Symbol) (flexibles : List Variable) :
    Expansion Variable Literal Symbol Certificate :=
  { rule := .derived (.lemmaCut name statement witnesses), flexibles := flexibles
    premises := [{ discharge := { assumptions := [instantiated] }, goal := goal }] }

section Reading

variable [DecidableEq Variable] [FreshNames Variable] {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
  {naf : NafFailure Variable Literal Symbol} {scope : Scope Variable Literal Symbol}
  {store : Store Variable Literal Symbol} {name : Symbol} {statement goal : Formula Variable Literal Symbol}
  {witnesses : List (Term Variable Literal Symbol)} {flexibles : List Variable}

/-- The instance from the lemma's derivation by universal eliminations; the
match makes the goal read as it. -/
theorem lemmaUse_soundUnder {instantiated : Formula Variable Literal Symbol}
    {bindings : List (Variable × Term Variable Literal Symbol)}
    (lemma : Derives hoApplySymbol kb (scope.assumptions.map store.resolve) (store.resolve statement) naf)
    (computed : statement.instantiateLeading witnesses = some instantiated)
    (matched : store.resolve instantiated = store.resolve goal) :
    (lemmaUse (Certificate := Certificate) name statement witnesses flexibles bindings).SoundUnder hoApplySymbol kb
      naf store ⟨scope, goal⟩ := fun _ => by
  simp only [ReadDerives, Obligation.context, ← matched]
  exact Derives.resolve_instantiateLeading store.bindings witnesses computed lemma

/-- The instance `B → H` from the lemma's derivation, then `H` by implication
elimination on the premise's proof; the match makes the goal read as `H`. -/
theorem lemmaRule_soundUnder {premise conclusion : Formula Variable Literal Symbol}
    {bindings : List (Variable × Term Variable Literal Symbol)}
    (lemma : Derives hoApplySymbol kb (scope.assumptions.map store.resolve) (store.resolve statement) naf)
    (computed : statement.instantiateLeading witnesses = some (.imp premise conclusion))
    (matched : store.resolve conclusion = store.resolve goal) :
    (lemmaRule (Certificate := Certificate) name statement witnesses premise flexibles bindings).SoundUnder hoApplySymbol
      kb naf store ⟨scope, goal⟩ := fun proofs => by
  have argument := read_premise.mp (proofs { goal := premise } (by simp [lemmaRule]))
  simp only [List.map_nil, List.nil_append] at argument
  have instantiated : Derives hoApplySymbol kb (scope.assumptions.map store.resolve)
      (store.resolve (.imp premise conclusion)) naf :=
    Derives.resolve_instantiateLeading store.bindings witnesses computed lemma
  rw [Store.resolve_imp] at instantiated
  simp only [ReadDerives, Obligation.context, ← matched]
  exact .impElim instantiated argument

/-- The instance from the lemma's derivation, then a cut on it. -/
theorem lemmaCut_soundUnder {instantiated : Formula Variable Literal Symbol}
    (lemma : Derives hoApplySymbol kb (scope.assumptions.map store.resolve) (store.resolve statement) naf)
    (computed : statement.instantiateLeading witnesses = some instantiated) :
    (lemmaCut (Certificate := Certificate) name statement witnesses instantiated goal flexibles).SoundUnder hoApplySymbol
      kb naf store ⟨scope, goal⟩ := fun proofs => by
  have continuation := read_premise.mp
    (proofs { discharge := { assumptions := [instantiated] }, goal := goal } (by simp [lemmaCut]))
  exact Derives.cut (Derives.resolve_instantiateLeading store.bindings witnesses computed lemma) continuation

end Reading

end Expansion

/-! ## Offering lemmas -/

section Strategy

variable [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal] [FreshNames Variable]

/-- A conclusion used by backchaining: an atom, falsity, an equation, or a NAF
formula. A compound conclusion is used through a cut. -/
def simpleConclusion : Term Variable Literal Symbol → Bool
  | .app _ _ | .falsity | .equal _ _ | .defaultNeg _ => true
  | _ => false

/-- How a lemma's conclusion compares with the goal: an equation or a NAF
formula directly when the goal has its connective; an atom or falsity as
`compareAtom` compares a local rule's (S11), through an indirect view where the
two differ by `ho_apply`; any other conclusion is apart, used only through a
cut. `binds` are the names the lemma may bind, its leading binders. -/
def compareLemma (hoApplySymbol : Symbol) (binds assignable : Variable → Bool)
    (goal conclusion : Term Variable Literal Symbol) : Comparison :=
  match conclusion with
  | .equal _ _ | .defaultNeg _ => if sameConnective goal conclusion then .direct else .apart
  | .app _ _ | .falsity => compareAtom hoApplySymbol binds assignable goal conclusion
  | _ => .apart

/-- A lemma's candidate for a conclusion compared with the goal: the
conclusion's candidate (`conclusionAttempt`), a miss when it misses; then a gap
where the use site may still change (`Store.lemmaSite`); the candidate where the
lemma holds under the context as read; and where it does not, a gap if its own
context is there (its proof does not check here, though the lemma applies) and
a miss otherwise. The lemma's proof is checked again only for a conclusion that
matches. -/
def lemmaMatch (hoApplySymbol : Symbol) (lemmas : Lemmas Variable Literal Symbol)
    (obligation : Obligation Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol)) (name : Symbol)
    (statement : Formula Variable Literal Symbol) (fresh : List Variable) (comparison : Comparison)
    (conclusion : Formula Variable Literal Symbol)
    (make : List (Variable × Term Variable Literal Symbol) → Expansion Variable Literal Symbol Certificate) :
    Attempt Variable Literal Symbol Certificate :=
  let candidate := conclusionAttempt hoApplySymbol obligation store fresh comparison conclusion make false
  match candidate with
  | some none => some none
  | _ =>
      if store.lemmaSite context statement then
        if lemmas.holds (context.map Prod.snd) name statement then candidate
        else if lemmas.applies (context.map Prod.snd) name statement then none
        else some none
      else none

/-- The backchaining candidate of one lemma for a goal, as read: the whole
statement for a goal that reads as it; otherwise the lemma's matrix, after its
leading binders, compared with the goal (`compareLemma`), its conclusion if it
is an implication. Only a lemma that may apply gets fresh flexible witnesses
for its leading binders: the instance concludes the goal (`lemmaUse`), or the
implication's conclusion does (`lemmaRule`). -/
def lemmaAttempt (hoApplySymbol : Symbol) (lemmas : Lemmas Variable Literal Symbol)
    (obligation : Obligation Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (goal : Term Variable Literal Symbol) (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol))
    (avoid : List Variable) (name : Symbol) (statement : Formula Variable Literal Symbol) :
    Attempt Variable Literal Symbol Certificate :=
  if identical goal statement then
    lemmaMatch hoApplySymbol lemmas obligation store context name statement [] .direct statement
      fun bindings => Expansion.lemmaUse name statement [] [] bindings
  else
    let binders := leadingBinders statement
    let binds := fun other => decide (other ∈ binders)
    match stripLeading binders.length statement with
    | .imp _ head =>
        match compareLemma hoApplySymbol binds store.assignable goal head with
        | .apart => some none
        | comparison =>
            let fresh := store.witnessesFor avoid statement
            match statement.instantiateLeading (fresh.map Term.var) with
            | some (.imp premise conclusion) =>
                lemmaMatch hoApplySymbol lemmas obligation store context name statement fresh comparison conclusion
                  fun bindings => Expansion.lemmaRule name statement (fresh.map Term.var) premise fresh bindings
            | _ => some none
    | matrix =>
        match compareLemma hoApplySymbol binds store.assignable goal matrix with
        | .apart => some none
        | comparison =>
            let fresh := store.witnessesFor avoid statement
            match statement.instantiateLeading (fresh.map Term.var) with
            | some instantiated =>
                lemmaMatch hoApplySymbol lemmas obligation store context name statement fresh comparison instantiated
                  fun bindings => Expansion.lemmaUse name statement (fresh.map Term.var) fresh bindings
            | none => some none

/-- Cuts on lemmas chosen at a focus: a lemma's name, with witnesses for its
leading binders, an explicit term or `none` for a fresh flexible witness. -/
abbrev LemmaSelection (Variable Literal Symbol : Type) :=
  Obligation Variable Literal Symbol → Store Variable Literal Symbol → Term Variable Literal Symbol →
    List (Term Variable Literal Symbol × Term Variable Literal Symbol) → List (Symbol × List (Option (Term Variable Literal Symbol)))

/-- The candidate of a chosen cut: the newest lemma with the name, at the
witnesses, assumed by the continuation. A name with no lemma or witnesses past
its leading binders are a miss; a use site that may still change is a gap; a
lemma that does not hold under the context as read is a gap if its own context
is there, and a miss otherwise. -/
def cutAttempt (lemmas : Lemmas Variable Literal Symbol) (obligation : Obligation Variable Literal Symbol)
    (store : Store Variable Literal Symbol) (context : List (Term Variable Literal Symbol × Term Variable Literal Symbol))
    (avoid : List Variable) (choice : Symbol × List (Option (Term Variable Literal Symbol))) :
    Attempt Variable Literal Symbol Certificate :=
  match lemmas.statements.find? fun entry => decide (entry.1 = choice.1) with
  | some (name, statement) =>
      if choice.2.length ≤ (leadingBinders statement).length then
        if store.lemmaSite context statement then
          if lemmas.holds (context.map Prod.snd) name statement then
            let chosen := store.chooseWitnesses avoid statement choice.2
            match statement.instantiateLeading chosen.1 with
            | some instantiated =>
                some (some (Expansion.lemmaCut name statement chosen.1 instantiated obligation.goal chosen.2))
            | none => some none
          else if lemmas.applies (context.map Prod.snd) name statement then none
          else some none
        else none
      else some none
  | none => some none

/-- The lemma candidates at a focus: backchaining on every lemma, then the
chosen cuts. -/
def lemmaAttempts (hoApplySymbol : Symbol) (lemmas : Lemmas Variable Literal Symbol)
    (cuts : LemmaSelection Variable Literal Symbol) : Offers Variable Literal Symbol Certificate :=
  fun obligation store goal context =>
    let avoid := readAvoid goal context
    lemmas.statements.map (fun entry => lemmaAttempt hoApplySymbol lemmas obligation store goal context avoid entry.1 entry.2) ++
      (cuts obligation store goal context).map (cutAttempt lemmas obligation store context avoid)

/-- The left strategy with checked lemmas: at each focus where it offers
commands, the lemmas' candidates (`lemmaAttempts`), then the S09 commands
`select` chooses. -/
def withLemmas (hoApplySymbol : Symbol) (program : Program Variable Literal Symbol) (lemmas : Lemmas Variable Literal Symbol)
    (select : Selection Variable Literal Symbol) (cuts : LemmaSelection Variable Literal Symbol) :
    Strategy Variable Literal Symbol Certificate :=
  leftWith hoApplySymbol program fun obligation store goal context =>
    lemmaAttempts hoApplySymbol lemmas cuts obligation store goal context ++
      chosenAttempts hoApplySymbol program select obligation store goal context

/-! ## Soundness -/

variable {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}
  {lemmas : Lemmas Variable Literal Symbol} {obligation : Obligation Variable Literal Symbol}
  {store : Store Variable Literal Symbol}

theorem lemmaMatch_sound (sound : lemmas.Sound hoApplySymbol kb naf) (valid : store.Scoped) {name : Symbol}
    {statement conclusion : Formula Variable Literal Symbol} {fresh : List Variable} {comparison : Comparison}
    {make : List (Variable × Term Variable Literal Symbol) → Expansion Variable Literal Symbol Certificate}
    (shape : ∀ bindings, (make bindings).flexibles = fresh ∧ (make bindings).rigids = [] ∧
      (make bindings).bindings = bindings)
    (contract : ∀ bindings (later : Store Variable Literal Symbol) (target : Formula Variable Literal Symbol),
      Derives hoApplySymbol kb (obligation.context.map later.resolve) (later.resolve statement) naf →
      later.resolve conclusion = later.resolve target →
        NodeSound hoApplySymbol kb naf later ⟨obligation.scope, target⟩ (make bindings).premises) :
    AttemptSound hoApplySymbol kb naf store obligation
      (lemmaMatch hoApplySymbol lemmas obligation store (store.readContext obligation) name statement fresh comparison
        conclusion make) := by
  unfold lemmaMatch
  dsimp only
  split
  · intro _ found; cases found
  · split
    · rename_i site
      split
      · rename_i holds
        exact conclusionAttempt_sound_scoped valid shape fun bindings later target refines laterScoped matched =>
          contract bindings later target (sound.later valid site holds refines laterScoped) matched
      · split <;> intro _ found <;> cases found
    · intro _ found; cases found

theorem lemmaAttempt_sound (sound : lemmas.Sound hoApplySymbol kb naf) (valid : store.Scoped)
    {goal : Term Variable Literal Symbol} {avoid : List Variable} {name : Symbol}
    {statement : Formula Variable Literal Symbol} :
    AttemptSound hoApplySymbol kb naf store obligation
      (lemmaAttempt (Certificate := Certificate) hoApplySymbol lemmas obligation store goal (store.readContext obligation)
        avoid name statement) := by
  unfold lemmaAttempt
  split
  · exact lemmaMatch_sound sound valid (fun _ => ⟨rfl, by simp [Expansion.rigids, Expansion.lemmaUse], rfl⟩)
      fun _ later _ lemma matched => Expansion.lemmaUse_soundUnder lemma rfl matched
  · dsimp only
    split
    · split
      · intro _ found; cases found
      · split
        · rename_i premise conclusion computed
          exact lemmaMatch_sound sound valid (fun _ => ⟨rfl, by simp [Expansion.rigids, Expansion.lemmaRule], rfl⟩)
            fun _ later _ lemma matched => Expansion.lemmaRule_soundUnder lemma computed matched
        · intro _ found; cases found
    · split
      · intro _ found; cases found
      · split
        · rename_i instantiated computed
          exact lemmaMatch_sound sound valid (fun _ => ⟨rfl, by simp [Expansion.rigids, Expansion.lemmaUse], rfl⟩)
            fun _ later _ lemma matched => Expansion.lemmaUse_soundUnder lemma computed matched
        · intro _ found; cases found

omit [DecidableEq Literal] in
theorem cutAttempt_sound (sound : lemmas.Sound hoApplySymbol kb naf) (valid : store.Scoped) {avoid : List Variable}
    (choice : Symbol × List (Option (Term Variable Literal Symbol))) :
    AttemptSound hoApplySymbol kb naf store obligation
      (cutAttempt (Certificate := Certificate) lemmas obligation store (store.readContext obligation) avoid choice) := by
  unfold cutAttempt
  split
  · rename_i name statement _
    split
    · split
      · rename_i site
        split
        · rename_i holds
          dsimp only
          split
          · rename_i instantiated computed
            intro _ produced next woken committed later refines laterScoped
            cases produced
            exact Expansion.lemmaCut_soundUnder
              (sound.later valid site holds ((Store.commit_refines committed).trans refines) laterScoped) computed
          · intro _ found; cases found
        · split <;> intro _ found <;> cases found
      · intro _ found; cases found
    · intro _ found; cases found
  · intro _ found; cases found

theorem lemmaAttempts_sound (sound : lemmas.Sound hoApplySymbol kb naf) (valid : store.Scoped)
    (cuts : LemmaSelection Variable Literal Symbol) {goal : Term Variable Literal Symbol} :
    ∀ candidate ∈ lemmaAttempts (Certificate := Certificate) hoApplySymbol lemmas cuts obligation store goal
      (store.readContext obligation), AttemptSound hoApplySymbol kb naf store obligation candidate := by
  intro candidate inside
  simp only [lemmaAttempts, List.mem_append, List.mem_map] at inside
  rcases inside with ⟨_, _, rfl⟩ | ⟨choice, _, rfl⟩
  · exact lemmaAttempt_sound sound valid
  · exact cutAttempt_sound sound valid choice

/-- The left strategy with lemmas, on a program whose clauses are among those
of `full`, is sound for `full`'s KB with lemmas sound there: every lemma
command's contract is the lemma's derivation read through the answers. -/
theorem withLemmas_sound_within {program full : Program Variable Literal Symbol}
    (within : ∀ entry ∈ program.clauses, entry ∈ full.clauses) (sound : lemmas.Sound hoApplySymbol full.kb naf)
    (select : Selection Variable Literal Symbol) (cuts : LemmaSelection Variable Literal Symbol) :
    Strategy.Sound hoApplySymbol full.kb naf
      (withLemmas (Certificate := Certificate) hoApplySymbol program lemmas select cuts) :=
  leftWith_sound_within within fun obligation store valid declared candidate inside => by
    rcases List.mem_append.mp inside with lemma | chosen
    · exact lemmaAttempts_sound sound valid cuts candidate lemma
    · exact chosenAttempts_sound_within (fun _ ⟨entry, member, same⟩ => ⟨entry, within entry member, same⟩) valid
        declared select candidate chosen

/-- A successful run with lemmas sound for `full`'s KB reconstructs `Derives`
for its answer instance there. -/
theorem withLemmas_reconstructs {program full : Program Variable Literal Symbol}
    (within : ∀ entry ∈ program.clauses, entry ∈ full.clauses) (sound : lemmas.Sound hoApplySymbol full.kb naf)
    (select : Selection Variable Literal Symbol) (cuts : LemmaSelection Variable Literal Symbol) (fuel : Nat)
    (snapshot : Snapshot) (flexibles : List Variable) (context : ProofContext Variable Literal Symbol)
    (goal : Formula Variable Literal Symbol) {resume : State Variable Literal Symbol Certificate Snapshot}
    {proof : CompletedProof Variable Literal Symbol Certificate Snapshot}
    (ran : run (withLemmas hoApplySymbol program lemmas select cuts) fuel (State.init snapshot flexibles context goal) =
      .success proof resume) :
    Derives hoApplySymbol full.kb (context.map proof.store.resolve) (proof.store.resolve goal) naf :=
  run_init_reconstructs _ (withLemmas_sound_within within sound select cuts) fuel snapshot flexibles context goal ran

end Strategy

end AnthillModKbSpec.Machine
