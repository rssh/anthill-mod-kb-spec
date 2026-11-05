import AnthillModKbSpec.Resolution.Machine.Positive
import AnthillModKbSpec.Resolution.Machine.Negation
import AnthillModKbSpec.Resolution.P0.Witness

namespace AnthillModKbSpec.P0

open Machine GroundSearch

/-! # The P0 command set on the shared machine (S07)

A P0 plan runs the shared `positive` strategy (S06) with ground negation as
failure (`Strategy.withNegation`) over a finite ground program. This module
computes what that strategy answers on a ground obligation in the empty store:
truth and conjunction by their introduction rules, falsity by nothing, NAF by
`negate`, and an atom by one assumption candidate per occurrence in the context
and one clause candidate per program clause with exactly that head, in that
order. No answer is `unsupported`, `incomplete`, or `delay`: matching ground
terms without the reserved `ho_apply` symbol is decided (`Store.unify_plain`),
and every commit keeps the empty store (`Store.commit_ground`). -/

variable {Variable Literal Symbol : Type}

/-- Ground data and atoms without the reserved `ho_apply` symbol anywhere:
`GroundSearch.IsData` and `Machine.Ordinary` together. The shared matcher
compares these by identity. -/
inductive Plain (hoApplySymbol : Symbol) : Term Variable Literal Symbol → Prop where
  | lit {value : Literal} : Plain hoApplySymbol (.lit value)
  | app {symbol : Symbol} {args : List (Term Variable Literal Symbol)} (ordinary : symbol ≠ hoApplySymbol)
      (arguments : ∀ arg ∈ args, Plain hoApplySymbol arg) : Plain hoApplySymbol (.app symbol args)

variable {hoApplySymbol : Symbol}

theorem Plain.of_data {term : Term Variable Literal Symbol} (data : IsData term)
    (ordinary : Ordinary hoApplySymbol term) : Plain hoApplySymbol term := by
  induction data with
  | lit => exact .lit
  | app args ih =>
      cases ordinary with
      | app different arguments => exact .app different fun arg member => ih arg member (arguments arg member)

theorem Plain.of_atom {term : Term Variable Literal Symbol} (atom : IsAtom hoApplySymbol term)
    (ordinary : Ordinary hoApplySymbol term) : Plain hoApplySymbol term := by
  cases atom with
  | app _ args =>
      cases ordinary with
      | app different arguments =>
          exact .app different fun arg member => Plain.of_data (args arg member) (arguments arg member)

theorem Plain.iff {term : Term Variable Literal Symbol} :
    Plain hoApplySymbol term ↔ IsData term ∧ Ordinary hoApplySymbol term := by
  refine ⟨fun plain => ?_, fun ⟨data, ordinary⟩ => Plain.of_data data ordinary⟩
  induction plain with
  | lit => exact ⟨.lit, .lit⟩
  | app different _ ih => exact ⟨.app fun arg member => (ih arg member).1, .app different fun arg member => (ih arg member).2⟩

theorem Plain.app_iff {symbol : Symbol} {args : List (Term Variable Literal Symbol)} :
    Plain hoApplySymbol (.app symbol args) ↔ symbol ≠ hoApplySymbol ∧ ∀ arg ∈ args, Plain hoApplySymbol arg := by
  constructor
  · intro plain; cases plain with
    | app different arguments => exact ⟨different, arguments⟩
  · intro ⟨different, arguments⟩; exact .app different arguments

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

variable [FreshNames Variable]

section Matching

variable {scope : Scope Variable Literal Symbol}

omit [FreshNames Variable] in
private theorem compare_plain {left right : Term Variable Literal Symbol} (leftPlain : Plain hoApplySymbol left)
    (rightPlain : Plain hoApplySymbol right) (different : identical left right = false) :
    (∃ parts, matchParts left right = some parts ∧ compareTerms hoApplySymbol left right = .split parts ∧
        (∀ pair ∈ parts, Plain hoApplySymbol pair.1 ∧ Plain hoApplySymbol pair.2) ∧
        parts.all (fun pair => identical pair.1 pair.2) = false) ∨
      compareTerms hoApplySymbol left right = .mismatch := by
  cases leftPlain with
  | lit =>
      cases rightPlain with
      | lit => exact .inr (by simp [compareTerms, matchParts])
      | app => exact .inr (by simp [compareTerms, matchParts])
  | @app f xs fOrdinary xsPlain =>
      cases rightPlain with
      | lit => exact .inr (by simp [compareTerms, matchParts])
      | @app g ys gOrdinary ysPlain =>
          by_cases same : f = g
          · subst same
            cases xs with
            | nil =>
                cases ys with
                | nil => simp [identical, identicalArgs] at different
                | cons y ys => exact .inr (by simp [compareTerms, matchParts])
            | cons x xs =>
                cases ys with
                | nil => exact .inr (by simp [compareTerms, matchParts])
                | cons y ys =>
                    refine .inl ⟨[(x, y), (.app f xs, .app f ys)], by simp [matchParts],
                      by simp [compareTerms, matchParts], fun pair member => ?_, ?_⟩
                    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                      rcases member with rfl | rfl
                      · exact ⟨xsPlain x (by simp), ysPlain y (by simp)⟩
                      · exact ⟨.app fOrdinary fun arg member => xsPlain arg (by simp [member]),
                          .app gOrdinary fun arg member => ysPlain arg (by simp [member])⟩
                    · simp only [identical, identicalArgs, decide_true, Bool.true_and] at different
                      simp [identical, different]
          · refine .inr ?_
            have notHo : ¬ (f = hoApplySymbol ∨ g = hoApplySymbol) := by
              rintro (h | h)
              · exact fOrdinary h
              · exact gOrdinary h
            cases xs <;> cases ys <;> simp [compareTerms, matchParts, same, notHo]

/-- Matching plain terms is decided by identity: `unified` with no binding, or
`mismatch`. Nothing is unsupported or violated. -/
theorem unifyPairs_plain (store : Store Variable Literal Symbol) (done : List (Variable × Term Variable Literal Symbol)) :
    ∀ (size : Nat) (pairs : List (Term Variable Literal Symbol × Term Variable Literal Symbol)), pairsSize pairs ≤ size →
      (∀ pair ∈ pairs, Plain hoApplySymbol pair.1 ∧ Plain hoApplySymbol pair.2) →
        unifyPairs hoApplySymbol scope store pairs done =
          if pairs.all (fun pair => identical pair.1 pair.2) then .unified store done else .mismatch := by
  intro size
  induction size with
  | zero =>
      intro pairs small plain
      cases pairs with
      | nil => simp [unifyPairs_nil]
      | cons pair rest =>
          obtain ⟨left, right⟩ := pair
          have := term_sizeOf_pos left
          simp only [pairsSize] at small
          omega
  | succ size ih =>
      intro pairs small plain
      cases pairs with
      | nil => simp [unifyPairs_nil]
      | cons pair rest =>
          obtain ⟨left, right⟩ := pair
          have leftPlain := (plain (left, right) List.mem_cons_self).1
          have rightPlain := (plain (left, right) List.mem_cons_self).2
          have restPlain := fun other member => plain other (List.mem_cons_of_mem _ member)
          have leftPos := term_sizeOf_pos left
          have rightPos := term_sizeOf_pos right
          simp only [pairsSize] at small
          rw [unifyPairs_cons]
          by_cases same : identical left right = true
          · have dropped : matchStep hoApplySymbol store left right = .drop := by simp [matchStep, same]
            rw [dropped, ih rest (by omega) restPlain, List.all_cons, same, Bool.true_and]
          · have different : identical left right = false := by simpa using same
            have noName : ∀ term : Term Variable Literal Symbol, Plain hoApplySymbol term →
                assignableName? store term = none := by
              intro term plainTerm
              cases plainTerm <;> rfl
            have compared : matchStep hoApplySymbol store left right = compareTerms hoApplySymbol left right := by
              simp [matchStep, different, noName left leftPlain, noName right rightPlain]
            rw [compared]
            rcases compare_plain leftPlain rightPlain different with ⟨parts, split, comparedEq, partsPlain, partsDiffer⟩ |
                mismatched
            · simp only [comparedEq]
              have shrinks := matchParts_size split
              simp only at shrinks
              rw [ih (parts ++ rest) (by rw [pairsSize_append]; omega) (fun pair member => by
                rcases List.mem_append.mp member with inside | inside
                · exact partsPlain pair inside
                · exact restPlain pair inside)]
              simp [List.all_append, partsDiffer, different]
            · simp only [mismatched]
              simp [different]

end Matching

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem Plain.closed {term : Term Variable Literal Symbol} (plain : Plain hoApplySymbol term) : term.freeVars = [] := by
  induction plain with
  | lit => simp [Term.freeVars]
  | app _ _ ih => simpa only [Term.freeVars] using List.flatMap_eq_nil_iff.mpr ih

/-- Matching two plain terms in the empty store. -/
theorem _root_.AnthillModKbSpec.Machine.Store.unify_plain {scope : Scope Variable Literal Symbol} {left right : Term Variable Literal Symbol} (leftPlain : Plain hoApplySymbol left)
    (rightPlain : Plain hoApplySymbol right) :
    (Store.empty : Store Variable Literal Symbol).unify scope hoApplySymbol left right =
      if identical left right then .unified Store.empty [] else .mismatch := by
  unfold Store.unify
  rw [Store.empty_resolve, Store.empty_resolve, leftPlain.closed, rightPlain.closed]
  simp only [List.append_nil, List.all_nil, ↓reduceIte]
  rw [unifyPairs_plain _ _ _ _ (Nat.le_refl _) (fun pair member => by
    simp only [List.mem_singleton] at member; subst member; exact ⟨leftPlain, rightPlain⟩)]
  simp

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
/-- A ground candidate commits without changing the empty store: no new names,
no bindings, premises without free names in the obligation's scope. -/
theorem _root_.AnthillModKbSpec.Machine.Store.commit_ground {obligation : Obligation Variable Literal Symbol}
    {premises : List (Premise Variable Literal Symbol)} (rigids : obligation.scope.rigids = [])
    (closed : ∀ premise ∈ premises, premise.discharge.rigids = [] ∧ premise.freeVars = []) :
    (Store.empty : Store Variable Literal Symbol).commit obligation [] (premises.flatMap fun premise => premise.discharge.rigids)
      premises [] = .committed Store.empty [] := by
  have noRigids : (premises.flatMap fun premise => premise.discharge.rigids) = [] :=
    List.flatMap_eq_nil_iff.mpr fun premise member => (closed premise member).1
  have accepts : (Store.empty : Store Variable Literal Symbol).Accepts obligation [] [] premises := by
    refine ⟨by simp, by simp, by simp [rigids], fun premise member name inside => ?_, fun premise member name inside => ?_⟩
    · rw [(closed premise member).1] at inside; cases inside
    · rw [(closed premise member).2] at inside; cases inside
  rw [noRigids]
  simp only [Store.commit, accepts, ↓reduceIte]
  rfl

/-! ## The run input and the strategy -/

/-- A clause P0 runs: a definite clause whose head and body goals contain no
`ho_apply` application, also inside data. -/
def ClauseOrdinary (hoApplySymbol : Symbol) : HornClause Variable Literal Symbol → Prop
  | .definite head body => Ordinary hoApplySymbol head ∧ ∀ goal ∈ body, Ordinary hoApplySymbol goal
  | .goal _ => False

/-- The input of a P0 run, as a Ready plan supplies it: a finite ground program
in selection order with each clause's source, a ground atomic context, a ground
goal, no `ho_apply` application anywhere, and a rank witness. -/
structure Ground (Variable Literal Symbol : Type) (hoApplySymbol : Symbol) where
  program : GroundSearch.Program Variable Literal Symbol hoApplySymbol
  entries : List (ProgramClause Variable Literal Symbol)
  listed : entries.map ProgramClause.clause = program.clauses
  context : GroundSearch.Context Variable Literal Symbol hoApplySymbol
  goal : Term Variable Literal Symbol
  valid : IsGoal hoApplySymbol goal
  ordinary : Ordinary hoApplySymbol goal
  clausesOrdinary : ∀ clause ∈ program.clauses, ClauseOrdinary hoApplySymbol clause
  contextOrdinary : ∀ atom ∈ context.assumptions, Ordinary hoApplySymbol atom
  rank : Term Variable Literal Symbol → Nat
  ranked : Ranked rank program.clauses

/-- Negative evidence a P0 NAF node retains: the exact clause list and context
it was computed against, the operand, and a finite failure witness for the
operand there. The witness is built when first read, so a NAF whose operand
is proved, or whose node is never checked, never builds one. -/
structure NegativeCertificate (Variable Literal Symbol : Type) where
  clauses : List (HornClause Variable Literal Symbol)
  context : ProofContext Variable Literal Symbol
  operand : Term Variable Literal Symbol
  witness : Thunk (Option (FailureTree Variable Literal Symbol))

/-- Check a certificate on its own data, by the structural failure checker: no
search is repeated. -/
def NegativeCertificate.check (hoApplySymbol : Symbol) (certificate : NegativeCertificate Variable Literal Symbol) : Bool :=
  match certificate.witness.get with
  | some tree => checkFailure hoApplySymbol certificate.clauses certificate.context certificate.operand tree
  | none => false

/-- A certificate holds for a ground program and context: it names exactly
them, and its witness checks. Evidence computed under another program or
context is never valid here (`NegativeCertificate.stale`). -/
def NegativeCertificate.Valid (program : GroundSearch.Program Variable Literal Symbol hoApplySymbol)
    (context : GroundSearch.Context Variable Literal Symbol hoApplySymbol)
    (certificate : NegativeCertificate Variable Literal Symbol) : Prop :=
  certificate.clauses = program.clauses ∧ certificate.context = context.assumptions ∧
    certificate.check hoApplySymbol = true

omit [FreshNames Variable] in
/-- A valid certificate's operand has a complete-failure certificate for the
program and context. -/
theorem NegativeCertificate.Valid.fails {program : GroundSearch.Program Variable Literal Symbol hoApplySymbol}
    {context : GroundSearch.Context Variable Literal Symbol hoApplySymbol}
    {certificate : NegativeCertificate Variable Literal Symbol} (valid : certificate.Valid program context) :
    Fails program context certificate.operand := by
  obtain ⟨clauses, assumptions, checked⟩ := valid
  unfold NegativeCertificate.check at checked
  split at checked
  · rw [clauses, assumptions] at checked
    exact checkFailure_sound _ _ checked
  · cases checked

omit [FreshNames Variable] in
/-- Negative evidence is snapshot-indexed: a certificate valid for one program
and context is not valid once the context's assumptions or the program's
clauses change. A NAF result under a grown context needs a new run. -/
theorem NegativeCertificate.stale {program program' : GroundSearch.Program Variable Literal Symbol hoApplySymbol}
    {context context' : GroundSearch.Context Variable Literal Symbol hoApplySymbol}
    {certificate : NegativeCertificate Variable Literal Symbol} (valid : certificate.Valid program context)
    (changed : context.assumptions ≠ context'.assumptions ∨ program.clauses ≠ program'.clauses) :
    ¬ certificate.Valid program' context' := fun other => by
  rcases changed with differentContext | differentClauses
  · exact differentContext (valid.2.1.symm.trans other.2.1)
  · exact differentClauses (valid.1.symm.trans other.1)

namespace Ground

variable (ground : Ground Variable Literal Symbol hoApplySymbol)

/-- The effective program the strategy selects from. No symbol is a guard: a
plan decides guard atoms at admission and lists the members as facts. -/
def machine : Machine.Program Variable Literal Symbol := ⟨ground.entries, fun _ => false⟩

/-- The scope of every P0 obligation: no rigid names, the ground context. -/
def scope : Scope Variable Literal Symbol := ⟨[], ground.context.assumptions⟩

/-- The failure witness of an operand, built by the ranked evaluator at the
root's level bound; `none` if the operand does not fail. -/
def witness (context : ProofContext Variable Literal Symbol) (operand : Formula Variable Literal Symbol) :
    Option (FailureTree Variable Literal Symbol) :=
  (evaluate ground.program.clauses context (level ground.rank ground.goal) operand).bind Verdict.failure?

/-- The certificate of a NAF node: the run's exact clauses and context, the
operand, and its failure witness, built on demand. -/
def certify (obligation : Obligation Variable Literal Symbol) (operand : Formula Variable Literal Symbol) :
    NegativeCertificate Variable Literal Symbol :=
  ⟨ground.program.clauses, obligation.context, operand, .mk fun _ => ground.witness obligation.context operand⟩

/-- The P0 command set: ground NAF over ordinary positive execution. -/
def strategy : Strategy Variable Literal Symbol (NegativeCertificate Variable Literal Symbol) :=
  (positive hoApplySymbol ground.machine).withNegation ground.certify

end Ground

/-- The candidates for a ground atom: an assumption per occurrence of the atom
in the context, then a clause per program clause with exactly that head. -/
def atomCandidates (entries : List (ProgramClause Variable Literal Symbol)) (context : ProofContext Variable Literal Symbol)
    (goal : Term Variable Literal Symbol) : List (Expansion Variable Literal Symbol (NegativeCertificate Variable Literal Symbol)) :=
  context.filterMap (fun assumption => if identical goal assumption then some (Expansion.assumption []) else none) ++
    entries.filterMap fun entry =>
      match entry.clause with
      | .definite head body => if identical head goal then some (Expansion.clause head body []) else none
      | .goal _ => none

/-- What the strategy answers for a ground obligation of the run. -/
def Ground.response (ground : Ground Variable Literal Symbol hoApplySymbol) (obligation : Obligation Variable Literal Symbol) :
    Response Variable Literal Symbol (NegativeCertificate Variable Literal Symbol) :=
  match obligation.goal with
  | .truth => .candidates [Expansion.truth]
  | .falsity => .candidates []
  | .conj left right => .candidates [Expansion.conjIntro left right]
  | .defaultNeg operand => .negate (ground.certify obligation operand)
  | goal => .candidates (atomCandidates ground.entries ground.context.assumptions goal)

/-! ## The strategy's answer on ground obligations -/

section Response

variable {ground : Ground Variable Literal Symbol hoApplySymbol}

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
@[simp] theorem Ground.scope_assumptions : ground.scope.assumptions = ground.context.assumptions := rfl

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem instantiate_rename_nil (term : Term Variable Literal Symbol) :
    term.instantiate (Substitution.rename []) = term :=
  Term.instantiate_fixed fun _ _ => rfl

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem sameHead_self [DecidableEq Symbol] (symbol : Symbol) (args : List (Term Variable Literal Symbol)) :
    sameHead (.app symbol args) (.app symbol args) = true := by
  simp [sameHead]

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
theorem appliesName_plain {term : Term Variable Literal Symbol} {binds : Variable → Bool}
    (plain : Plain hoApplySymbol term) : appliesName hoApplySymbol binds term = false := by
  cases plain with
  | lit => rfl
  | app ordinary _ =>
      unfold appliesName
      split
      · next heq =>
          simp only [Term.app.injEq] at heq
          obtain ⟨rfl, _⟩ := heq
          simp [ordinary]
      · rfl

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
/-- Plain terms apply nothing by `ho_apply`, so a plain conclusion without the
goal's head is apart from it: no conversion and no lambda gap. -/
theorem compareAtom_plain {goal conclusion : Term Variable Literal Symbol} {binds assignable : Variable → Bool}
    (goalPlain : Plain hoApplySymbol goal) (conclusionPlain : Plain hoApplySymbol conclusion)
    (different : sameHead goal conclusion = false) :
    compareAtom hoApplySymbol binds assignable goal conclusion = .apart := by
  have mixed : hoMixed hoApplySymbol goal conclusion = false := by
    cases goalPlain with
    | lit => rfl
    | app goalOrdinary _ =>
        cases conclusionPlain with
        | lit => rfl
        | app conclusionOrdinary _ => simp [hoMixed, goalOrdinary, conclusionOrdinary]
  simp [compareAtom, different, mixed, appliesName_plain conclusionPlain, appliesName_plain goalPlain]

omit [DecidableEq Variable] [DecidableEq Literal] [FreshNames Variable] in
/-- No plain conclusion compares with falsity. -/
theorem compareAtom_falsity {conclusion : Term Variable Literal Symbol} {binds assignable : Variable → Bool}
    (plain : Plain hoApplySymbol conclusion) :
    compareAtom hoApplySymbol binds assignable .falsity conclusion = .apart := by
  have different : sameHead (.falsity : Term Variable Literal Symbol) conclusion = false := by cases plain <;> rfl
  have mixed : hoMixed hoApplySymbol (.falsity : Term Variable Literal Symbol) conclusion = false := rfl
  simp [compareAtom, different, mixed, isCall]

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
private theorem respond_candidates {attempts : List (Attempt Variable Literal Symbol (NegativeCertificate Variable Literal Symbol))}
    (found : ∀ attempt ∈ attempts, attempt.isSome) : respond attempts = .candidates (attempts.filterMap Option.join) := by
  have none : attempts.any Option.isNone = false := by
    rw [List.any_eq_false]
    intro attempt member
    cases attempt with
    | none => exact absurd (found none member) (by simp)
    | some _ => simp
  simp [respond, none]

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
private theorem filterMap_join_ite {α : Type} (items : List α) (condition : α → Bool)
    (make : α → Expansion Variable Literal Symbol (NegativeCertificate Variable Literal Symbol)) :
    (items.map fun item => if condition item then some (some (make item)) else some none).filterMap Option.join =
      items.filterMap fun item => if condition item then some (make item) else none := by
  rw [List.filterMap_map]
  congr 1
  funext item
  simp only [Function.comp_def]
  split <;> rfl

theorem identityAttempts_ground {symbol : Symbol} {args : List (Term Variable Literal Symbol)}
    (goalPlain : Plain hoApplySymbol (.app symbol args))
    (contextPlain : ∀ atom ∈ ground.context.assumptions, Plain hoApplySymbol atom) :
    identityAttempts (Certificate := NegativeCertificate Variable Literal Symbol) hoApplySymbol
        ⟨ground.scope, .app symbol args⟩ Store.empty (.app symbol args)
        ((Store.empty : Store Variable Literal Symbol).readContext ⟨ground.scope, .app symbol args⟩) =
      ground.context.assumptions.map fun assumption =>
        if identical (.app symbol args) assumption then some (some (Expansion.assumption [])) else some none := by
  rw [Store.empty_readContext, identityAttempts, List.map_map]
  apply List.map_congr_left
  intro assumption member
  simp only [Function.comp_def]
  by_cases candidate : sameHead (.app symbol args) assumption = true
  · simp only [candidate, ↓reduceIte, Store.empty_prepare]
    rw [Store.unify_plain goalPlain (contextPlain assumption member)]
    by_cases same : identical (.app symbol args) assumption = true <;> simp [same, attempt]
  · have different : identical (.app symbol args) assumption = false := by
      by_cases same : identical (.app symbol args) assumption = true
      · rw [← identical_eq _ _ same, sameHead_self] at candidate; exact absurd rfl candidate
      · simpa using same
    simp only [candidate, Bool.false_eq_true, ↓reduceIte, different]
    rw [compareAtom_plain goalPlain (contextPlain assumption member) (by simpa using candidate)]
    rfl

omit [FreshNames Variable] in
/-- No ground atomic assumption reads as falsity, so ex falso never applies. -/
theorem exFalso_ground (goal : Term Variable Literal Symbol)
    (contextPlain : ∀ atom ∈ ground.context.assumptions, Plain hoApplySymbol atom) :
    exFalso (Certificate := NegativeCertificate Variable Literal Symbol) goal
      (ground.context.assumptions.map fun assumption => (assumption, assumption)) = [] := by
  have none : (ground.context.assumptions.map fun assumption => (assumption, assumption)).any
      (fun pair => identical pair.2 .falsity) = false := by
    rw [List.any_eq_false]
    intro pair member
    obtain ⟨atom, inside, rfl⟩ := List.mem_map.mp member
    cases contextPlain atom inside <;> simp [identical]
  unfold exFalso
  split
  · rfl
  · simp [none]

theorem localAttempt_ground {obligation : Obligation Variable Literal Symbol} {store : Store Variable Literal Symbol}
    {goal : Term Variable Literal Symbol} {avoid : List Variable} (symbol : Symbol) (args : List (Term Variable Literal Symbol)) :
    localAttempt (Certificate := NegativeCertificate Variable Literal Symbol) hoApplySymbol obligation store goal avoid
      (.app symbol args) (.app symbol args) = some none := by
  simp [localAttempt, leadingBinders, stripLeading, Matrix.of]

theorem clauseAttempt_ground {symbol : Symbol} {args : List (Term Variable Literal Symbol)} {avoid : List Variable}
    (goalPlain : Plain hoApplySymbol (.app symbol args)) {entry : ProgramClause Variable Literal Symbol}
    {head : Term Variable Literal Symbol} {body : List (Term Variable Literal Symbol)}
    (definite : entry.clause = .definite head body) (headPlain : Plain hoApplySymbol head)
    (bodyClosed : (Term.conjunction body).freeVars = []) :
    clauseAttempt (Certificate := NegativeCertificate Variable Literal Symbol) hoApplySymbol
        ⟨ground.scope, .app symbol args⟩ Store.empty (.app symbol args) avoid entry =
      if identical head (.app symbol args) then some (some (Expansion.clause head body [])) else some none := by
  have noTemplates : (HornClause.definite head body : HornClause Variable Literal Symbol).templates = [] := by
    simp [HornClause.templates, headPlain.closed, bodyClosed]
  have fresh : ∀ avoided : List Variable,
      (Store.empty : Store Variable Literal Symbol).freshen (HornClause.definite head body).templates avoided = [] := by
    intro avoided
    rw [noTemplates]
    rfl
  unfold clauseAttempt
  rw [definite]
  dsimp only
  by_cases candidate : sameHead (.app symbol args) head = true
  · have direct : compareAtom hoApplySymbol (clauseBinds head body)
        (Store.empty : Store Variable Literal Symbol).assignable (.app symbol args) head =
        .direct := by
      simp [compareAtom, candidate]
    rw [direct]
    simp only [clauseUse, conclusionAttempt, Store.clauseNames, fresh, List.map_nil, Store.empty_prepare,
      instantiate_rename_nil]
    rw [Store.unify_plain headPlain goalPlain]
    by_cases same : identical head (.app symbol args) = true <;> simp [same, attempt]
  · have different : identical head (.app symbol args) = false := by
      by_cases same : identical head (.app symbol args) = true
      · rw [identical_eq _ _ same, sameHead_self] at candidate; exact absurd rfl candidate
      · simpa using same
    rw [compareAtom_plain goalPlain headPlain (by simpa using candidate)]
    simp [clauseUse, different]

/-- The answer for a ground atom, in the run's empty store. -/
theorem atomResponse_ground {symbol : Symbol} {args : List (Term Variable Literal Symbol)}
    (goalPlain : Plain hoApplySymbol (.app symbol args))
    (contextAtoms : ∀ atom ∈ ground.context.assumptions, ∃ f xs, atom = .app f xs ∧ Plain hoApplySymbol atom)
    (clausesPlain : ∀ entry ∈ ground.entries, ∃ head body, entry.clause = .definite head body ∧
      Plain hoApplySymbol head ∧ (Term.conjunction body).freeVars = []) :
    atomResponse (Certificate := NegativeCertificate Variable Literal Symbol) hoApplySymbol ground.machine
        ⟨ground.scope, .app symbol args⟩ Store.empty (.app symbol args)
        ((Store.empty : Store Variable Literal Symbol).readContext ⟨ground.scope, .app symbol args⟩) =
      .candidates (atomCandidates ground.entries ground.context.assumptions (.app symbol args)) := by
  have contextPlain : ∀ atom ∈ ground.context.assumptions, Plain hoApplySymbol atom := fun atom member => by
    obtain ⟨_, _, _, plain⟩ := contextAtoms atom member
    exact plain
  have direct : (Term.app symbol args : Term Variable Literal Symbol).call? hoApplySymbol = none := by
    cases goalPlain with | app ordinary _ => exact Term.call?_ordinary ordinary args
  unfold atomResponse
  rw [direct]
  dsimp only
  rw [identityAttempts_ground goalPlain contextPlain, Store.empty_readContext]
  dsimp only
  have locals : ∀ avoid : List Variable,
      ((ground.scope.assumptions.map fun assumption => (assumption, assumption)).map fun pair =>
        localAttempt (Certificate := NegativeCertificate Variable Literal Symbol) hoApplySymbol
          ⟨ground.scope, .app symbol args⟩ Store.empty (.app symbol args) avoid pair.1 pair.2) =
        ground.context.assumptions.map fun _ => some none := by
    intro avoid
    rw [List.map_map]
    apply List.map_congr_left
    intro atom member
    obtain ⟨f, xs, rfl, _⟩ := contextAtoms atom member
    exact localAttempt_ground f xs
  have clauses : ∀ avoid : List Variable,
      ground.machine.clauses.map (clauseAttempt (Certificate := NegativeCertificate Variable Literal Symbol)
        hoApplySymbol ⟨ground.scope, .app symbol args⟩ Store.empty (.app symbol args) avoid) =
        ground.entries.map fun entry =>
          match entry.clause with
          | .definite head body =>
              if identical head (.app symbol args) then some (some (Expansion.clause head body [])) else some none
          | .goal _ => some none := by
    intro avoid
    apply List.map_congr_left
    intro entry member
    obtain ⟨head, body, definite, headPlain, bodyClosed⟩ := clausesPlain entry member
    rw [clauseAttempt_ground goalPlain definite headPlain bodyClosed, definite]
  rw [locals, clauses, Ground.scope_assumptions, exFalso_ground _ contextPlain, respond_candidates]
  · simp only [List.map_nil, List.append_nil, List.filterMap_append, filterMap_join_ite, atomCandidates]
    have noLocal : List.filterMap (Option.join ∘ fun _ =>
        (some none : Attempt Variable Literal Symbol (NegativeCertificate Variable Literal Symbol)))
        ground.context.assumptions = [] := by simp [Function.comp_def]
    rw [List.filterMap_map, List.filterMap_map, noLocal, List.append_nil]
    congr 1
    apply congrArg (List.filterMap _ ground.context.assumptions ++ ·)
    apply congrArg (List.filterMap · ground.entries)
    funext entry
    simp only [Function.comp_def]
    split <;> (try split) <;> rfl
  · intro attempt member
    simp only [List.map_nil, List.append_nil, List.mem_append, List.mem_map] at member
    rcases member with (⟨atom, _, rfl⟩ | ⟨atom, _, rfl⟩) | ⟨entry, _, rfl⟩
    · split <;> rfl
    · rfl
    · split
      · split <;> rfl
      · rfl

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem Ground.contextAtoms (ground : Ground Variable Literal Symbol hoApplySymbol) :
    ∀ atom ∈ ground.context.assumptions, ∃ f xs, atom = .app f xs ∧ Plain hoApplySymbol atom := by
  intro atom member
  have atomic := ground.context.wellFormed atom member
  have plain := Plain.of_atom atomic (ground.contextOrdinary atom member)
  cases atomic with
  | app _ _ => exact ⟨_, _, rfl, plain⟩

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
theorem Ground.clausesPlain (ground : Ground Variable Literal Symbol hoApplySymbol) :
    ∀ entry ∈ ground.entries, ∃ head body, entry.clause = .definite head body ∧ Plain hoApplySymbol head ∧
      (Term.conjunction body).freeVars = [] := by
  intro entry member
  have listed : entry.clause ∈ ground.program.clauses := by
    rw [← ground.listed]; exact List.mem_map_of_mem member
  have ordinary := ground.clausesOrdinary _ listed
  have valid := ground.program.wellFormed _ listed
  generalize entry.clause = clause at valid ordinary ⊢
  cases valid with
  | definite headAtom bodyGoals =>
      exact ⟨_, _, rfl, Plain.of_atom headAtom ordinary.1, (conjunction_isGoal bodyGoals).closed⟩

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
/-- Nothing waits in the empty store: no name is assignable. -/
theorem waiting?_empty (program : Machine.Program Variable Literal Symbol) (goal : Term Variable Literal Symbol) :
    waiting? program (Store.empty : Store Variable Literal Symbol) goal = none := by
  have noName : assignableName? (Store.empty : Store Variable Literal Symbol) goal = none := by
    cases goal <;> simp [assignableName?, Store.empty_assignable]
  simp only [waiting?, noName]
  cases guardSubject? program goal <;> simp [Option.filter, Store.empty_assignable]

theorem exactCandidates_composite {goal : Term Variable Literal Symbol}
    (composite : ∀ f xs, goal ≠ .app f xs) :
    exactCandidates (Certificate := NegativeCertificate Variable Literal Symbol) ⟨ground.scope, goal⟩ goal
      ((Store.empty : Store Variable Literal Symbol).readContext ⟨ground.scope, goal⟩) = [] := by
  have atoms := ground.contextAtoms
  have noIdentity : identities (Certificate := NegativeCertificate Variable Literal Symbol) goal
      (ground.context.assumptions.map fun assumption => (assumption, assumption)) = [] := by
    simp only [identities, List.filterMap_map, Function.comp_def, List.filterMap_eq_nil_iff]
    intro atom member
    obtain ⟨f, xs, rfl, _⟩ := atoms atom member
    have different : identical goal (.app f xs) = false := by
      by_cases same : identical goal (.app f xs) = true
      · exact absurd (identical_eq _ _ same) (composite f xs)
      · simpa using same
    simp [different]
  have noFalsity := exFalso_ground goal fun atom member => by
    obtain ⟨_, _, _, plain⟩ := atoms atom member
    exact plain
  have noSteps : (ground.scope.assumptions.flatMap fun assumption =>
      (List.range (leadingBinders assumption).length).filterMap fun index =>
        exactStep (Certificate := NegativeCertificate Variable Literal Symbol) ⟨ground.scope, goal⟩ assumption
          (index + 1)) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro atom member
    obtain ⟨f, xs, rfl, _⟩ := atoms atom member
    simp [leadingBinders]
  simp only [exactCandidates, Store.empty_readContext, Ground.scope_assumptions] at noSteps ⊢
  rw [noIdentity, noFalsity, noSteps]
  rfl

/-- What `positive` answers on a ground obligation of a P0 run: the P0
response, except for NAF, which it leaves to the ground NAF command. -/
theorem Ground.positive_eq {goal : Term Variable Literal Symbol} (valid : IsGoal hoApplySymbol goal)
    (ordinary : Ordinary hoApplySymbol goal) :
    positive (Certificate := NegativeCertificate Variable Literal Symbol) hoApplySymbol ground.machine
        ⟨ground.scope, goal⟩ Store.empty =
      match goal with
      | .defaultNeg _ => .unsupported
      | _ => ground.response ⟨ground.scope, goal⟩ := by
  cases valid with
  | atom atomic =>
      have plain := Plain.of_atom atomic ordinary
      cases atomic with
      | app _ _ =>
          simp only [Store.empty_resolve, positive, respondTo,
            waiting?_empty, Ground.response]
          exact atomResponse_ground plain ground.contextAtoms ground.clausesPlain
  | truth =>
      simp only [Store.empty_resolve, positive, respondTo,
        waiting?_empty, Ground.response, compositeResponse]
      rw [exactCandidates_composite (by intro f xs h; cases h)]
      rfl
  | falsity =>
      simp only [Store.empty_resolve, positive, respondTo,
        waiting?_empty, Ground.response, atomResponse, Term.call?, List.append_nil]
      have atoms := ground.contextAtoms
      have clausesPlain := ground.clausesPlain
      have allNone : ∀ attempt ∈ identityAttempts (Certificate := NegativeCertificate Variable Literal Symbol)
            hoApplySymbol ⟨ground.scope, .falsity⟩ Store.empty .falsity
            ((Store.empty : Store Variable Literal Symbol).readContext ⟨ground.scope, .falsity⟩) ++
          (exFalso .falsity ((Store.empty : Store Variable Literal Symbol).readContext ⟨ground.scope, .falsity⟩)).map
            (some ∘ some) ++
          ((Store.empty : Store Variable Literal Symbol).readContext ⟨ground.scope, .falsity⟩).map (fun pair =>
            localAttempt hoApplySymbol ⟨ground.scope, .falsity⟩ Store.empty .falsity
              (readAvoid .falsity ((Store.empty : Store Variable Literal Symbol).readContext ⟨ground.scope, .falsity⟩))
              pair.1 pair.2) ++
          ground.machine.clauses.map (clauseAttempt hoApplySymbol ⟨ground.scope, .falsity⟩ Store.empty .falsity
            (readAvoid .falsity ((Store.empty : Store Variable Literal Symbol).readContext ⟨ground.scope, .falsity⟩))),
          attempt = some none := by
        intro attempt member
        simp only [Store.empty_readContext, Ground.scope_assumptions, List.mem_append, identityAttempts,
          List.map_map, List.mem_map, exFalso, List.map_nil, List.not_mem_nil, or_false] at member
        rcases member with (⟨atom, inside, rfl⟩ | ⟨atom, inside, rfl⟩) | ⟨entry, inside, rfl⟩
        · obtain ⟨f, xs, rfl, plain⟩ := atoms atom inside
          simp only [Function.comp_apply, sameHead, Bool.false_eq_true, ↓reduceIte]
          rw [compareAtom_falsity plain]
          rfl
        · obtain ⟨f, xs, rfl, _⟩ := atoms atom inside
          simp only [Function.comp_apply]
          exact localAttempt_ground f xs
        · obtain ⟨head, body, definite, headPlain, _⟩ := clausesPlain entry inside
          cases headPlain with
          | lit =>
              have wellFormed := ground.program.wellFormed _ (by rw [← ground.listed]; exact List.mem_map_of_mem inside)
              rw [definite] at wellFormed
              cases wellFormed with
              | definite headAtom _ => cases headAtom
          | app ordinary arguments =>
              simp only [clauseAttempt, definite]
              rw [compareAtom_falsity (.app ordinary arguments)]
              rfl
      rw [respond_candidates fun attempt member => by rw [allNone attempt member]; rfl]
      congr 1
      exact List.filterMap_eq_nil_iff.mpr fun attempt member => by rw [allNone attempt member]; rfl
  | conj left right =>
      simp only [Store.empty_resolve, positive, respondTo,
        waiting?_empty, Ground.response, compositeResponse]
      rw [exactCandidates_composite (by intro f xs h; cases h)]
      rfl
  | defaultNeg body =>
      simp only [Store.empty_resolve, positive, respondTo, waiting?_empty, compositeResponse]
      rw [exactCandidates_composite (by intro f xs h; cases h)]
      rfl

omit [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable] in
/-- A P0 NAF obligation is ground as read: its operand and the ground
context are closed. -/
theorem Ground.groundNegation {operand : Formula Variable Literal Symbol} (closed : operand.freeVars = [])
    (goal : Formula Variable Literal Symbol) :
    (Store.empty : Store Variable Literal Symbol).groundNegation ⟨ground.scope, goal⟩ operand = true :=
  Store.empty_groundNegation closed fun atom member => by
    obtain ⟨_, _, _, plain⟩ := ground.contextAtoms atom member
    exact plain.closed

/-- The strategy's answer on every ground obligation of a P0 run, in the
empty store: no gap and no delay. -/
theorem Ground.strategy_eq {goal : Term Variable Literal Symbol} (valid : IsGoal hoApplySymbol goal)
    (ordinary : Ordinary hoApplySymbol goal) :
    ground.strategy ⟨ground.scope, goal⟩ Store.empty = ground.response ⟨ground.scope, goal⟩ := by
  have base := ground.positive_eq valid ordinary
  simp only [Ground.strategy, Strategy.withNegation]
  rw [base]
  cases valid with
  | atom atomic => cases atomic with | app _ _ => simp only [Ground.response]
  | truth | falsity | conj _ _ => simp only [Ground.response]
  | defaultNeg body => simp [Ground.response, ground.groundNegation body.closed]

end Response

end AnthillModKbSpec.P0
