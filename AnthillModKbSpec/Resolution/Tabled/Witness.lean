import AnthillModKbSpec.Resolution.Tabled.AbstractSound

/-! # The two witnesses of an open goal (S24)

For a positive covered program, the completion's models are the fixpoints of
the consequence operator (`fixpoint_iff_models`), between the least and the
greatest. An open goal has both as witnesses:

- **The least fixpoint** (`least_witness`): the key model of the least
  fixpoint, unknown markers as `base` gives them. A closed abstract least
  fixpoint (`closedLeast`) bounds its true atoms (`lowInterp_pre`), so a goal
  that fails over it (`failsLeast`) is false there. Every denial body must fail
  over it too.
- **The greatest fixpoint** (`greatest_witness`): the key model of the
  greatest fixpoint. A post-fixpoint over the universe and one fresh value ⋆
  (`postGreatest`) lies below it (`highInterp_post`), so a positive goal true
  over it (`vtrue`) is true there. Every denial body must be refuted
  (`refutes`), which is sound in every fixpoint model.

Both are models of the completed program with complement NAF. -/

namespace AnthillModKbSpec.Tabled

open Semantics Completion

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  [FreshNames Variable]

attribute [local instance] Machine.termEq

variable {hoApplySymbol : Symbol} {signature : Signature Literal Symbol} {clauses : List (HornClause Variable Literal Symbol)}
  {space : List (Term Variable Literal Symbol)}

omit [DecidableEq Literal] in
/-- A fixpoint over keys has what the abstract fixpoints need. -/
theorem Completes.of_fixpoint {base interp : Interp Literal Symbol} (covered : Covered hoApplySymbol signature clauses)
    (fixpoint : Fixpoint hoApplySymbol signature clauses base interp) :
    Completes (keyModel hoApplySymbol signature base interp) signature clauses where
  program _ _ _ member environment := fixpoint_program covered fixpoint member environment
  onlyIf := fun ⟨_, _⟩ member environment => fixpoint_onlyIf covered fixpoint member environment
  free := free_keys _ _

omit [DecidableEq Literal] in
theorem keys_holds_app {interpretation : Interp Literal Symbol} {symbol : Symbol} (ordinary : symbol ≠ hoApplySymbol)
    (keys : List (Key Literal Symbol)) :
    (Model.keys hoApplySymbol interpretation).holds ((Model.keys hoApplySymbol interpretation).application symbol keys) ↔
      interpretation symbol keys :=
  resolveKey_ordinary interpretation ordinary keys

omit [DecidableEq Literal] [FreshNames Variable] in
/-- A fixpoint of a monotone operator. -/
theorem fixpoint_of_monotone {base : Interp Literal Symbol} {interp : Interp Literal Symbol}
    (pre : (consequence hoApplySymbol signature clauses base interp).Le interp)
    (post : interp.Le (consequence hoApplySymbol signature clauses base interp)) :
    Fixpoint hoApplySymbol signature clauses base interp :=
  fun symbol keys _ => ⟨post symbol keys, pre symbol keys⟩

/-! ## The least fixpoint -/

/-- The atoms an abstract least fixpoint allows: every abstraction of their
keys is among its atoms. -/
def lowInterp (space : List (Term Variable Literal Symbol)) (found : List (AAtom Variable Literal Symbol)) : Interp Literal Symbol :=
  fun symbol keys => ∀ abstract, Along (AbsKey space) keys abstract → (symbol, abstract) ∈ found

omit [FreshNames Variable] in
theorem lowInterp_sound (covered : Covered hoApplySymbol signature clauses) (valid : validUniverse signature.constructors space = true)
    {base interp : Interp Literal Symbol} {found : List (AAtom Variable Literal Symbol)} (bounded : interp.Le (lowInterp space found)) :
    SoundPossible (keyModel hoApplySymbol signature base interp) space signature found := by
  intro symbol keys abstract closed holds along
  rw [keys_holds_app (covered.ordinary _ closed), join_closed closed] at holds
  exact bounded symbol keys holds abstract ((along_abs_keys valid _).mp along)

omit [FreshNames Variable] in
/-- A closed abstract least fixpoint is a pre-fixpoint: it bounds the least
fixpoint. -/
theorem lowInterp_pre (covered : Covered hoApplySymbol signature clauses) (valid : validUniverse signature.constructors space = true)
    {found : List (AAtom Variable Literal Symbol)} (closedL : closedLeast signature space clauses found = true)
    (base : Interp Literal Symbol) :
    (consequence hoApplySymbol signature clauses base (lowInterp space found)).Le (lowInterp space found) := by
  intro symbol keys ⟨closed, args, body, inClauses, env, argsEq, bodyHolds⟩ abstract along
  simp only [closedLeast, List.all_eq_true, decide_eq_true_eq] at closedL
  have lengths : args.length = keys.length := by rw [← argsEq, List.length_map]
  have defining : (args, body) ∈ definitions clauses symbol keys.length := lengths ▸ mem_definitions inClauses
  have soundP := lowInterp_sound (base := base) covered valid (Interp.Le.refl (lowInterp space found))
  have soundD : SoundDefinite (keyModel hoApplySymbol signature base (lowInterp space found))
      ([] : List (GAtom Variable Literal Symbol)) := fun _ member => by cases member
  apply closedL
  cases data : dataInAll signature.constructors args with
  | true =>
      obtain ⟨abstractEnv, envMember, abstracts⟩ := envsOver_abstracts (space := space) env (caseNames args body)
      have bodyPossible := (body_sound valid (free_keys _ _) (Model.keys_complement _) soundP soundD (.conjunction body) env
        abstractEnv fun name occurs => abstracts name (freeVars_case_body occurs)).1 bodyHolds
      have headsAlong := aevals_abs valid (free_keys _ _) args data fun name occurs => abstracts name (freeVars_case_args occurs)
      rw [argsEq] at headsAlong
      obtain rfl : abstract = args.map (aeval space abstractEnv) :=
        Along.unique (relation := Abs (keyModel hoApplySymbol signature base (lowInterp space found)) space)
          (fun _ _ _ left right => Abs.unique valid (free_keys _ _) left right) ((along_abs_keys valid _).mpr along) headsAlong
      exact mem_stepPossible (key := (symbol, keys.length)) closed defining data envMember bodyPossible
  | false =>
      have abstractLength : abstract.length = keys.length := along.length.symm
      exact mem_stepPossible_tuples (key := (symbol, keys.length)) closed defining data (abstractLength ▸ mem_tuples fun item member => by
        obtain ⟨key, _, related⟩ := Along.mem along item member
        exact ((abs_keys_iff (hoApplySymbol := hoApplySymbol) valid (fun _ _ => False) key item).mpr related).mem_values)

/-- **The least witness.** For a positive covered program, the key model of the
least fixpoint is a model of the completed program, and a goal that fails over
a closed abstract least fixpoint is false in it. -/
theorem least_witness (covered : Covered hoApplySymbol signature clauses) (positive : PositiveProgram hoApplySymbol clauses)
    (valid : validUniverse signature.constructors space = true) {found : List (AAtom Variable Literal Symbol)}
    (closedL : closedLeast signature space clauses found = true) (base : Interp Literal Symbol)
    (denials : ∀ body, HornClause.goal body ∈ clauses → failsLeast signature space found (.conjunction body) = true)
    {goal : Term Variable Literal Symbol} (fails : failsLeast signature space found goal = true) :
    (keyModel hoApplySymbol signature base (lfp (consequence hoApplySymbol signature clauses base))).Models
        (fun clause => clause ∈ (completion clauses signature).clauses : LogicalKb Variable Literal Symbol) ∧
      ∀ environment, ¬ (keyModel hoApplySymbol signature base (lfp (consequence hoApplySymbol signature clauses base))).Satisfies
        environment goal := by
  have mono := consequence_mono signature positive base
  have fixpoint := fixpoint_of_monotone (lfp_pre mono) (lfp_post mono)
  have bounded := lfp_le (lowInterp_pre covered valid closedL base)
  have soundP := lowInterp_sound (base := base) covered valid bounded
  have soundD : SoundDefinite (keyModel hoApplySymbol signature base (lfp (consequence hoApplySymbol signature clauses base)))
      ([] : List (GAtom Variable Literal Symbol)) :=
    fun _ member => by cases member
  have refuted : ∀ formula, failsLeast signature space found formula = true → ∀ environment,
      ¬ (keyModel hoApplySymbol signature base (lfp (consequence hoApplySymbol signature clauses base))).Satisfies environment formula :=
    fun formula failed => notPossible_sound valid (free_keys _ _) (Model.keys_complement _) soundP soundD failed
  exact ⟨models_of_fixpoint covered fixpoint fun body member environment => refuted _ (denials body member) environment,
    refuted goal fails⟩

/-! ## The greatest fixpoint -/

/-- The key of a value over the universe and the fresh value: a term's key,
or a truth value no data term has. -/
def vkey : AValue Variable Literal Symbol → Key Literal Symbol
  | some term => Open.dataKey term
  | none => .truth False

/-- The atoms of a post-fixpoint, at their keys. -/
def highInterp (found : List (AAtom Variable Literal Symbol)) : Interp Literal Symbol :=
  fun symbol keys => ∃ found', (symbol, found') ∈ found ∧ keys = found'.map vkey

omit [FreshNames Variable] in
mutual
theorem veval_key (interpretation : Interp Literal Symbol) (env : AEnv Variable Literal Symbol) :
    ∀ (term : Term Variable Literal Symbol) (value : AValue Variable Literal Symbol), veval space env term = some value →
      (Model.keys hoApplySymbol interpretation).eval (fun name => vkey (env name)) term = vkey value
  | .var name, value, evaluated => by simp only [veval, Option.some.injEq] at evaluated; subst evaluated; simp [Model.eval]
  | .lit literal, value, evaluated => by
      simp only [veval] at evaluated
      split at evaluated
      · cases evaluated; simp only [Model.eval, vkey, Open.dataKey]; rfl
      · cases evaluated
  | .app symbol args, value, evaluated => by
      simp only [veval] at evaluated
      split at evaluated
      · rename_i found computed
        split at evaluated
        · rename_i terms someTerms
          split at evaluated
          · cases evaluated
            simp only [Model.eval]
            rw [vevals_key interpretation env args found computed]
            rw [allSome_eq_some] at someTerms
            rw [someTerms, List.map_map]
            show Key.app symbol _ = Key.app symbol (Open.dataKeys terms)
            rw [Open.dataKeys_eq]
            rfl
          · cases evaluated
        · cases evaluated
      · cases evaluated
  | .truth, _, evaluated | .falsity, _, evaluated | .conj _ _, _, evaluated | .disj _ _, _, evaluated
  | .imp _ _, _, evaluated | .defaultNeg _, _, evaluated | .forallVar _ _, _, evaluated | .existsVar _ _, _, evaluated
  | .dictionaryCall _ _ _ _, _, evaluated | .equal _ _, _, evaluated => by simp [veval] at evaluated

theorem vevals_key (interpretation : Interp Literal Symbol) (env : AEnv Variable Literal Symbol) :
    ∀ (args : List (Term Variable Literal Symbol)) (values : List (AValue Variable Literal Symbol)), vevals space env args = some values →
      args.map ((Model.keys hoApplySymbol interpretation).eval (fun name => vkey (env name))) = values.map vkey
  | [], values, evaluated => by simp only [vevals, Option.some.injEq] at evaluated; subst evaluated; rfl
  | arg :: rest, values, evaluated => by
      simp only [vevals] at evaluated
      split at evaluated
      · rename_i value found here there
        cases evaluated
        simp only [List.map_cons, veval_key interpretation env arg value here, vevals_key interpretation env rest found there]
      · cases evaluated
end

omit [FreshNames Variable] in
/-- A positive goal true over a post-fixpoint is true in the model of its atoms. -/
theorem vtrue_sound (ordinary : ∀ key ∈ signature.predicates, key.1 ≠ hoApplySymbol) {marked : Symbol → Bool}
    (markedOrdinary : marked hoApplySymbol = false) {base : Interp Literal Symbol}
    (markedTrue : ∀ symbol keys, marked symbol = true → base symbol keys) {found : List (AAtom Variable Literal Symbol)} :
    ∀ (goal : Term Variable Literal Symbol) (env : AEnv Variable Literal Symbol),
      vtrue signature space marked found env goal = true →
        (keyModel hoApplySymbol signature base (highInterp found)).Satisfies (fun name => vkey (env name)) goal
  | .truth, _, _ => sat_truth _ _
  | .conj left right, env, holds => by
      simp only [vtrue, Bool.and_eq_true] at holds
      exact (sat_conj _ _ _ _).mpr ⟨vtrue_sound ordinary markedOrdinary markedTrue left env holds.1,
        vtrue_sound ordinary markedOrdinary markedTrue right env holds.2⟩
  | .disj left right, env, holds => by
      simp only [vtrue, Bool.or_eq_true] at holds
      exact (sat_disj _ _ _ _).mpr (holds.imp (vtrue_sound ordinary markedOrdinary markedTrue left env)
        (vtrue_sound ordinary markedOrdinary markedTrue right env))
  | .existsVar name body, env, holds => by
      simp only [vtrue, List.any_eq_true] at holds
      obtain ⟨value, _, bodyHolds⟩ := holds
      refine (sat_exists _ _ _ _).mpr ⟨vkey value, ?_⟩
      have same : update (fun other => vkey (env other)) name (vkey value) = fun other => vkey (update env name value other) := by
        funext other; by_cases equal : other = name <;> simp [update, equal]
      rw [same]
      exact vtrue_sound ordinary markedOrdinary markedTrue body _ bodyHolds
  | .equal left right, env, holds => by
      simp only [vtrue] at holds
      split at holds
      · split at holds
        · rename_i first second leftEq rightEq
          simp only [decide_eq_true_eq] at holds
          subst holds
          rw [Model.satisfies_equal, veval_key _ env left first leftEq, veval_key _ env right first rightEq]
        · simp at holds
      · simp at holds
  | .app symbol args, env, holds => by
      simp only [vtrue] at holds
      split at holds
      · split at holds
        · rename_i _ closed
          split at holds
          · rename_i values computed
            have closed' : (symbol, args.length) ∈ signature.predicates := of_decide_eq_true closed
            rw [Model.keys_atom _ _ (ordinary _ closed'), vevals_key _ env args values computed]
            have lengths : (values.map vkey).length = args.length := by
              rw [← vevals_key (hoApplySymbol := hoApplySymbol) (fun _ _ => False) env args values computed, List.length_map]
            rw [join_closed (by rw [lengths]; exact closed')]
            exact ⟨values, of_decide_eq_true holds, rfl⟩
          · simp at holds
        · rename_i _ notClosed
          have isOrdinary : symbol ≠ hoApplySymbol := fun same => by subst same; rw [markedOrdinary] at holds; cases holds
          rw [Model.keys_atom _ _ isOrdinary]
          have notClosed' : (symbol, (args.map ((keyModel hoApplySymbol signature base (highInterp found)).eval
              (fun name => vkey (env name)))).length) ∉ signature.predicates := by
            simpa using notClosed
          rw [join_open notClosed']
          exact markedTrue _ _ holds
      · simp at holds
  | .falsity, _, holds | .var _, _, holds | .lit _, _, holds | .imp _ _, _, holds | .defaultNeg _, _, holds
  | .forallVar _ _, _, holds | .dictionaryCall _ _ _ _, _, holds => by simp [vtrue] at holds

omit [FreshNames Variable] in
/-- A post-fixpoint over the universe and the fresh value lies below the
greatest fixpoint. -/
theorem highInterp_post (ordinary : ∀ key ∈ signature.predicates, key.1 ≠ hoApplySymbol) {marked : Symbol → Bool}
    (markedOrdinary : marked hoApplySymbol = false) {base : Interp Literal Symbol}
    (markedTrue : ∀ symbol keys, marked symbol = true → base symbol keys) {found : List (AAtom Variable Literal Symbol)}
    (post : postGreatest signature space clauses marked found = true)
    (atoms : ∀ atom ∈ found, (atom.1, atom.2.length) ∈ signature.predicates) :
    (highInterp found).Le (consequence hoApplySymbol signature clauses base (highInterp found)) := by
  intro symbol keys ⟨values, member, keysEq⟩
  subst keysEq
  simp only [postGreatest, List.all_eq_true] at post
  have supportedHere := post _ member
  simp only [supported, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at supportedHere
  obtain ⟨⟨args, body⟩, defining, _, env, _, computed, bodyHolds⟩ := supportedHere
  refine ⟨by simpa using atoms _ member, args, body, (definitions_mem defining).1, fun name => vkey (env name), ?_,
    vtrue_sound ordinary markedOrdinary markedTrue _ env bodyHolds⟩
  exact vevals_key _ env args values computed

/-- **The greatest witness.** For a positive covered program, the key model of
the greatest fixpoint is a model of the completed program when every denial
body is refuted, and a positive closed goal true over a post-fixpoint is true
in it. -/
theorem greatest_witness (covered : Covered hoApplySymbol signature clauses) (positive : PositiveProgram hoApplySymbol clauses)
    (valid : validUniverse signature.constructors space = true) {marked : Symbol → Bool}
    (markedOrdinary : marked hoApplySymbol = false) {base : Interp Literal Symbol}
    (markedTrue : ∀ symbol keys, marked symbol = true → base symbol keys) {found : List (AAtom Variable Literal Symbol)}
    (post : postGreatest signature space clauses marked found = true)
    (atoms : ∀ atom ∈ found, (atom.1, atom.2.length) ∈ signature.predicates) {count : Nat}
    (denials : ∀ body, HornClause.goal body ∈ clauses → refutes signature space clauses count (.conjunction body) = true)
    {goal : Term Variable Literal Symbol} (goalPositive : positiveGoal hoApplySymbol goal = true)
    (holds : vtrue signature space marked found (fun _ => none) goal = true) :
    (keyModel hoApplySymbol signature base (gfp (consequence hoApplySymbol signature clauses base))).Models
        (fun clause => clause ∈ (completion clauses signature).clauses : LogicalKb Variable Literal Symbol) ∧
      (keyModel hoApplySymbol signature base (gfp (consequence hoApplySymbol signature clauses base))).Satisfies
        (fun _ => vkey (none : AValue Variable Literal Symbol)) goal := by
  have mono := consequence_mono signature positive base
  have fixpoint := fixpoint_of_monotone (gfp_pre mono) (gfp_post mono)
  have below := le_gfp (highInterp_post covered.ordinary markedOrdinary markedTrue post atoms)
  have completes := Completes.of_fixpoint covered fixpoint
  refine ⟨models_of_fixpoint covered fixpoint fun body member environment =>
    refutes_sound completes valid (Model.keys_complement _) (denials body member) environment, ?_⟩
  exact satisfies_mono (join_mono signature base below) goal _ goalPositive
    (vtrue_sound covered.ordinary markedOrdinary markedTrue goal (fun _ => none) holds)

theorem length_of_mem_tuples {α : Type} {choices : List α} :
    ∀ {count : Nat} {items : List α}, items ∈ tuples choices count → items.length = count
  | 0, items, member => by simp only [tuples, List.mem_singleton] at member; subst member; rfl
  | count + 1, items, member => by
      simp only [tuples, List.mem_flatMap, List.mem_map] at member
      obtain ⟨rest, restMember, _, _, rfl⟩ := member
      simp [length_of_mem_tuples restMember]

omit [FreshNames Variable] in
theorem greatestOver_atoms {marked : Symbol → Bool} :
    ∀ (count : Nat), ∀ atom ∈ greatestOver signature space clauses marked count, (atom.1, atom.2.length) ∈ signature.predicates
  | 0, atom, member => by
      simp only [greatestOver, allAtoms, List.mem_flatMap, List.mem_map] at member
      obtain ⟨key, keyMember, abstract, inTuples, rfl⟩ := member
      simpa [length_of_mem_tuples inTuples] using keyMember
  | count + 1, atom, member => greatestOver_atoms count atom (List.mem_filter.mp member).1

/-! ## Ground programs -/

section Ground

variable (hoApplySymbol) (signature) (marked : Symbol → Bool)

/-- A ground goal over known atoms: closed atoms and unknown markers, ground
data, no name and no quantifier. -/
def knownGoal : Term Variable Literal Symbol → Bool
  | .truth | .falsity => true
  | .conj left right | .disj left right | .imp left right => knownGoal left && knownGoal right
  | .defaultNeg body => knownGoal body
  | .equal left right => groundIn signature.constructors left && groundIn signature.constructors right
  | .app symbol args => groundInAll signature.constructors args && decide (symbol ≠ hoApplySymbol) &&
      (decide ((symbol, args.length) ∈ signature.predicates) || marked symbol)
  | _ => false

/-- A ground program: definite clauses with ground heads of closed predicates
and known bodies, and denials with known bodies. -/
def groundProgram (clauses : List (HornClause Variable Literal Symbol)) : Bool :=
  signature.predicates.all (fun key => decide (key.1 ≠ hoApplySymbol)) &&
    clauses.all fun
      | .definite (.app symbol args) body =>
          decide ((symbol, args.length) ∈ signature.predicates) && groundInAll signature.constructors args &&
            body.all (knownGoal hoApplySymbol signature marked)
      | .goal body => body.all (knownGoal hoApplySymbol signature marked)
      | _ => false

/-- The atoms of an assignment. -/
def groundInterp (assignment : List (GAtom Variable Literal Symbol)) : Interp Literal Symbol :=
  fun symbol keys => ∃ args, (symbol, args) ∈ assignment ∧ keys = args.map Open.dataKey

/-- The ground model's other atoms: unknown markers by the assignment, the rest
(guards) by `outside`. -/
def groundBase (assignment : List (GAtom Variable Literal Symbol)) (outside : Interp Literal Symbol) : Interp Literal Symbol :=
  fun symbol keys => (marked symbol = true ∧ groundInterp assignment symbol keys) ∨ (marked symbol = false ∧ outside symbol keys)

variable {hoApplySymbol} {signature} {marked}

omit [DecidableEq Variable] [FreshNames Variable] in
theorem knownGoal_conjunction : ∀ {goals : List (Term Variable Literal Symbol)},
    (∀ goal ∈ goals, knownGoal hoApplySymbol signature marked goal = true) →
      knownGoal hoApplySymbol signature marked (Term.conjunction goals) = true
  | [], _ => by simp [Term.conjunction, knownGoal]
  | goal :: rest, known => by
      simp only [Term.conjunction, List.foldr_cons, knownGoal, Bool.and_eq_true]
      exact ⟨known goal List.mem_cons_self, knownGoal_conjunction fun other member => known other (List.mem_cons_of_mem _ member)⟩

omit [FreshNames Variable] in
theorem gtrue_conjunction {assignment : List (GAtom Variable Literal Symbol)} : ∀ {goals : List (Term Variable Literal Symbol)},
    gtrue signature assignment (Term.conjunction goals) = true ↔ ∀ goal ∈ goals, gtrue signature assignment goal = true
  | [] => by simp [Term.conjunction, gtrue]
  | goal :: rest => by
      simp only [Term.conjunction, List.foldr_cons, gtrue, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
      rw [← gtrue_conjunction (goals := rest)]; rfl

omit [FreshNames Variable] in
theorem eval_ground_keys (interpretation : Interp Literal Symbol) (environment : Environment Variable (Key Literal Symbol))
    {term : Term Variable Literal Symbol} (ground : groundIn signature.constructors term = true) :
    (Model.keys hoApplySymbol interpretation).eval environment term = Open.dataKey term := by
  rw [eval_ground environment term ground, den_keys interpretation signature.constructors term ground]

omit [FreshNames Variable] in
theorem evals_ground_keys (interpretation : Interp Literal Symbol) (environment : Environment Variable (Key Literal Symbol))
    {args : List (Term Variable Literal Symbol)} (ground : groundInAll signature.constructors args = true) :
    args.map ((Model.keys hoApplySymbol interpretation).eval environment) = args.map Open.dataKey := by
  rw [eval_grounds environment args ground, dens_keys interpretation signature.constructors args ground]

omit [FreshNames Variable] in
theorem dataKeys_injective (hoApplySymbol : Symbol) {args others : List (Term Variable Literal Symbol)}
    (ground : groundInAll signature.constructors args = true) (otherGround : groundInAll signature.constructors others = true)
    (same : args.map Open.dataKey = others.map Open.dataKey) : args = others := by
  apply den_injectives (free_keys (hoApplySymbol := hoApplySymbol) (fun _ _ => False) signature.constructors) args others ground otherGround
  rw [dens_keys _ _ args ground, dens_keys _ _ others otherGround, same]

omit [FreshNames Variable] in
theorem gtrue_sound {assignment : List (GAtom Variable Literal Symbol)} {outside : Interp Literal Symbol}
    (groundAssignment : ∀ atom ∈ assignment, groundInAll signature.constructors atom.2 = true)
    (environment : Environment Variable (Key Literal Symbol)) :
    ∀ goal : Term Variable Literal Symbol, knownGoal hoApplySymbol signature marked goal = true →
      ((keyModel hoApplySymbol signature (groundBase marked assignment outside) (groundInterp assignment)).Satisfies environment goal ↔
        gtrue signature assignment goal = true)
  | .truth, _ => ⟨fun _ => by simp [gtrue], fun _ => sat_truth _ _⟩
  | .falsity, _ => by simp only [gtrue]; exact ⟨fun holds => absurd holds (not_sat_falsity _ _), fun found => by cases found⟩
  | .conj left right, known => by
      simp only [knownGoal, Bool.and_eq_true] at known
      rw [sat_conj, gtrue_sound groundAssignment environment left known.1, gtrue_sound groundAssignment environment right known.2]
      simp [gtrue]
  | .disj left right, known => by
      simp only [knownGoal, Bool.and_eq_true] at known
      rw [sat_disj, gtrue_sound groundAssignment environment left known.1, gtrue_sound groundAssignment environment right known.2]
      simp [gtrue]
  | .imp left right, known => by
      simp only [knownGoal, Bool.and_eq_true] at known
      rw [sat_imp, gtrue_sound groundAssignment environment left known.1, gtrue_sound groundAssignment environment right known.2]
      simp only [gtrue, Bool.or_eq_true, Bool.not_eq_true']
      cases gtrue signature assignment left <;> cases gtrue signature assignment right <;> simp
  | .defaultNeg body, known => by
      simp only [knownGoal] at known
      rw [sat_neg _ _ (Model.keys_complement _), gtrue_sound groundAssignment environment body known]
      simp [gtrue]
  | .equal left right, known => by
      simp only [knownGoal, Bool.and_eq_true] at known
      rw [Model.satisfies_equal, eval_ground_keys _ environment known.1, eval_ground_keys _ environment known.2]
      simp only [gtrue, known.1, known.2, Bool.true_and, decide_eq_true_eq]
      constructor
      · intro same
        have := dataKeys_injective hoApplySymbol (signature := signature) (args := [left]) (others := [right])
          (by simp [groundInAll, known.1]) (by simp [groundInAll, known.2]) (by simp [same])
        simpa using this
      · intro same; rw [same]
  | .app symbol args, known => by
      simp only [knownGoal, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at known
      obtain ⟨⟨ground, ordinary⟩, closedOrMarked⟩ := known
      rw [Model.keys_atom _ _ ordinary, evals_ground_keys _ environment ground]
      simp only [gtrue, ground, Bool.true_and, decide_eq_true_eq]
      have lengths : (args.map Open.dataKey).length = args.length := List.length_map _
      have inAssignment : groundInterp assignment symbol (args.map Open.dataKey) ↔ (symbol, args) ∈ assignment := by
        constructor
        · rintro ⟨others, member, same⟩
          rw [dataKeys_injective hoApplySymbol ground (groundAssignment _ member) same]; exact member
        · intro member; exact ⟨args, member, rfl⟩
      by_cases closed : (symbol, args.length) ∈ signature.predicates
      · rw [join_closed (by rw [lengths]; exact closed)]; exact inAssignment
      · have isMarked : marked symbol = true := closedOrMarked.resolve_left closed
        rw [join_open (by rw [lengths]; exact closed)]
        simp only [groundBase, isMarked, true_and, Bool.true_eq_false, false_and, or_false]
        exact inAssignment
  | .var _, known | .lit _, known | .forallVar _ _, known | .existsVar _ _, known
  | .dictionaryCall _ _ _ _, known => by simp [knownGoal] at known

/-- **The ground witness.** For a ground program, an assignment that is a
fixpoint and makes every denial body false gives a model of the completed
program, in which a known goal holds exactly when it is true under the
assignment. -/
theorem ground_witness {clauses : List (HornClause Variable Literal Symbol)}
    (program : groundProgram hoApplySymbol signature marked clauses = true)
    {assignment : List (GAtom Variable Literal Symbol)} (fixed : groundFixpoint signature clauses assignment = true)
    (groundAssignment : ∀ atom ∈ assignment, groundInAll signature.constructors atom.2 = true)
    (denials : ∀ body, HornClause.goal body ∈ clauses → gtrue signature assignment (.conjunction body) = false)
    (outside : Interp Literal Symbol) {goal : Term Variable Literal Symbol}
    (known : knownGoal hoApplySymbol signature marked goal = true) :
    (keyModel hoApplySymbol signature (groundBase marked assignment outside) (groundInterp assignment)).Models
        (fun clause => clause ∈ (completion clauses signature).clauses : LogicalKb Variable Literal Symbol) ∧
      ∀ environment, ((keyModel hoApplySymbol signature (groundBase marked assignment outside) (groundInterp assignment)).Satisfies
        environment goal ↔ gtrue signature assignment goal = true) := by
  simp only [groundProgram, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at program
  obtain ⟨ordinary, shapes⟩ := program
  have covered : Covered hoApplySymbol signature clauses := by
    refine ⟨fun clause member => ?_, ordinary⟩
    have shape := shapes clause member
    match clause, shape with
    | .definite (.app symbol args) body, shape =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at shape
        exact .inl ⟨symbol, args, body, rfl, shape.1.1⟩
    | .goal body, _ => exact .inr ⟨body, rfl⟩
  have bodyKnown : ∀ head body, HornClause.definite head body ∈ clauses →
      knownGoal hoApplySymbol signature marked (.conjunction body) = true := by
    intro head body member
    have shape := shapes _ member
    match head, shape with
    | .app _ _, shape =>
        simp only [Bool.and_eq_true, List.all_eq_true] at shape
        exact knownGoal_conjunction shape.2
  have headGround : ∀ symbol args body, HornClause.definite (.app symbol args) body ∈ clauses →
      groundInAll signature.constructors args = true := by
    intro symbol args body member
    have shape := shapes _ member
    simp only [Bool.and_eq_true] at shape
    exact shape.1.2
  simp only [groundFixpoint, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    beq_iff_eq] at fixed
  have fixpoint : Fixpoint hoApplySymbol signature clauses (groundBase marked assignment outside) (groundInterp assignment) := by
    intro symbol keys closed
    constructor
    · rintro ⟨args, member, rfl⟩
      have check := (fixed _ (List.mem_append_left _ member)).resolve_left (by simpa using closed)
      simp only [decide_eq_true member] at check
      have supported := check.symm
      simp only [groundSupported, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at supported
      obtain ⟨⟨heads, body⟩, defining, rfl, bodyTrue⟩ := supported
      refine ⟨closed, heads, body, (definitions_mem defining).1, fun _ => .truth False, ?_, ?_⟩
      · exact evals_ground_keys _ _ (headGround _ _ _ (definitions_mem defining).1)
      · exact (gtrue_sound groundAssignment _ _ (bodyKnown _ _ (definitions_mem defining).1)).mpr bodyTrue
    · rintro ⟨_, args, body, member, environment, argsEq, bodyHolds⟩
      rw [evals_ground_keys _ _ (headGround _ _ _ member)] at argsEq
      subst argsEq
      have bodyTrue := (gtrue_sound groundAssignment _ _ (bodyKnown _ _ member)).mp bodyHolds
      have isHead : (symbol, args) ∈ groundHeads clauses := List.mem_filterMap.mpr ⟨_, member, rfl⟩
      have check := (fixed _ (List.mem_append_right _ isHead)).resolve_left (by simpa using closed)
      have supported : groundSupported signature clauses assignment (symbol, args) = true := by
        simp only [groundSupported, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨(args, body), mem_definitions member, rfl, bodyTrue⟩
      rw [supported] at check
      exact ⟨args, of_decide_eq_true check, rfl⟩
  refine ⟨models_of_fixpoint covered fixpoint fun body member environment holds => ?_, fun environment =>
    gtrue_sound groundAssignment environment goal known⟩
  have shape := shapes _ member
  simp only [List.all_eq_true] at shape
  have bodyTrue := (gtrue_sound groundAssignment environment _ (knownGoal_conjunction shape)).mp holds
  rw [denials body member] at bodyTrue
  cases bodyTrue

end Ground

end AnthillModKbSpec.Tabled
