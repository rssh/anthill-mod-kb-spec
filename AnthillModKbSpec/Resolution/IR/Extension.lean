import AnthillModKbSpec.Resolution.IR.GroundModels

/-! # Extending a model of the relevant program (S28)

Every key fixpoint restricts to a model of the ground relevant program
(`fixpoint_model`), so a goal true (false) in every such model is true (false)
in every model of the completion: Yes and No need nothing more. Unknown needs
the converse for its two models: each must extend to a model of the whole
completion. The rest of the KB can rule one out even when the KB is
consistent (`r(a) :- p(a), naf r(a)` forces `p(a)` false), so S28 answers
Unknown only when no rule outside the relevant program reads a relevant atom
under NAF on a cycle (decided with the user, 2026-11-18), checked here in a
form that makes the extension provable:

- **The check** (`Program.stratifiedBy`): every rule that is not *computed*
  (a rule with no name whose head is a relevant atom, its one instance in the
  relevant program) respects a rank of the predicates: its calls no higher
  than its head, its NAF literals strictly lower. The ranks are computed by
  iteration (`Program.ranks`), and the check fails exactly at a rule on a
  cycle through NAF among the rules outside: it names the first such rule
  (`Program.unstratified`). A NAF cycle outside the relevant program fails
  the check whether or not it reaches a relevant atom: its consistency is not
  decided (the KB-level check, below).
- **The construction** (`Strata.strata`): the relevant atoms take the model's
  values, and every other closed atom is decided stratum by stratum, rank 0
  first, each stratum's atoms by the least fixpoint of their rules given the
  strata below (Knaster–Tarski, S24's `lfp`): a stratum reads itself only
  positively, the strata below and the relevant atoms as fixed.
- **The extension** (`extends_model`): the result is a key fixpoint agreeing
  with the model on the relevant atoms and the markers, by S27's splitting
  theorem (`fixpoint_of_relevant`) and its reading of the denials
  (`denied_iff`). -/

namespace AnthillModKbSpec.IR

open Semantics Completion Tabled Answers

/-! ## Strata: a stratified least fixpoint -/

namespace Strata

variable {Literal Symbol : Type} (Ins : Symbol → List (Key Literal Symbol) → Prop) (insideVal : Interp Literal Symbol)
  (rank : Symbol → Nat) (Closed : Symbol → List (Key Literal Symbol) → Prop)
  (cons : Interp Literal Symbol → Interp Literal Symbol)

/-- The atoms of a stratum `k` from `X`, the inside atoms from `insideVal`,
every other atom from `lower`. -/
def layer (k : Nat) (lower values : Interp Literal Symbol) : Interp Literal Symbol := fun symbol keys =>
  (Ins symbol keys ∧ insideVal symbol keys) ∨
    (¬ Ins symbol keys ∧ ((rank symbol = k ∧ values symbol keys) ∨ (rank symbol ≠ k ∧ lower symbol keys)))

/-- The operator of stratum `k`, the strata below given. -/
def stratumOp (k : Nat) (lower : Interp Literal Symbol) (values : Interp Literal Symbol) : Interp Literal Symbol :=
  fun symbol keys => ¬ Ins symbol keys ∧ rank symbol = k ∧ Closed symbol keys ∧
    cons (layer Ins insideVal rank k lower values) symbol keys

/-- Stratum `k` decided: its least fixpoint over the strata below. -/
def stepStrata (k : Nat) (lower : Interp Literal Symbol) : Interp Literal Symbol :=
  layer Ins insideVal rank k lower (lfp (stratumOp Ins insideVal rank Closed cons k lower))

/-- The strata up to `k` decided. -/
def strata : Nat → Interp Literal Symbol
  | 0 => stepStrata Ins insideVal rank Closed cons 0 fun _ _ => False
  | k + 1 => stepStrata Ins insideVal rank Closed cons (k + 1) (strata k)

/-- The strata below `k`. -/
def lowerOf : Nat → Interp Literal Symbol
  | 0 => fun _ _ => False
  | k + 1 => strata Ins insideVal rank Closed cons k

theorem strata_eq (k : Nat) :
    strata Ins insideVal rank Closed cons k =
      stepStrata Ins insideVal rank Closed cons k (lowerOf Ins insideVal rank Closed cons k) := by
  cases k <;> rfl

/-- The consequence operator reads, at an atom of rank `r` outside, the atoms
of rank below `r` as fixed and those of rank `r` positively. -/
def Reads : Prop :=
  ∀ symbol keys, ¬ Ins symbol keys → Closed symbol keys → ∀ first second : Interp Literal Symbol,
    (∀ symbol' keys', rank symbol' < rank symbol → (first symbol' keys' ↔ second symbol' keys')) →
    (∀ symbol' keys', rank symbol' = rank symbol → first symbol' keys' → second symbol' keys') →
      cons first symbol keys → cons second symbol keys

variable {Ins insideVal rank Closed cons}

theorem layer_inside {k : Nat} {lower values : Interp Literal Symbol} {symbol : Symbol} {keys : List (Key Literal Symbol)}
    (inside : Ins symbol keys) : layer Ins insideVal rank k lower values symbol keys ↔ insideVal symbol keys := by
  simp [layer, inside]

theorem layer_here {k : Nat} {lower values : Interp Literal Symbol} {symbol : Symbol} {keys : List (Key Literal Symbol)}
    (outside : ¬ Ins symbol keys) (here : rank symbol = k) : layer Ins insideVal rank k lower values symbol keys ↔ values symbol keys := by
  simp [layer, outside, here]

theorem layer_other {k : Nat} {lower values : Interp Literal Symbol} {symbol : Symbol} {keys : List (Key Literal Symbol)}
    (outside : ¬ Ins symbol keys) (other : rank symbol ≠ k) : layer Ins insideVal rank k lower values symbol keys ↔ lower symbol keys := by
  simp [layer, outside, other]

/-- The inside atoms keep their values at every stratum. -/
theorem strata_inside {symbol : Symbol} {keys : List (Key Literal Symbol)} (inside : Ins symbol keys) (k : Nat) :
    strata Ins insideVal rank Closed cons k symbol keys ↔ insideVal symbol keys := by
  rw [strata_eq]; exact layer_inside inside

/-- An outside atom keeps the value of its own stratum at every later one. -/
theorem strata_stable {symbol : Symbol} {keys : List (Key Literal Symbol)} (outside : ¬ Ins symbol keys) :
    ∀ k, rank symbol ≤ k →
      (strata Ins insideVal rank Closed cons k symbol keys ↔ strata Ins insideVal rank Closed cons (rank symbol) symbol keys)
  | 0, le => by rw [Nat.le_zero.mp le]
  | k + 1, le => by
      rcases Nat.lt_or_eq_of_le le with lt | same
      · show stepStrata Ins insideVal rank Closed cons (k + 1) (strata Ins insideVal rank Closed cons k) symbol keys ↔ _
        rw [stepStrata, layer_other outside (Nat.ne_of_lt lt)]
        exact strata_stable outside k (Nat.le_of_lt_succ lt)
      · rw [same]

/-- Each stratum's operator is monotone. -/
theorem stratumOp_mono (reads : Reads Ins rank Closed cons) (k : Nat) (lower : Interp Literal Symbol) :
    Monotone (stratumOp Ins insideVal rank Closed cons k lower) := by
  intro first second le symbol keys ⟨outside, here, closed, holds⟩
  refine ⟨outside, here, closed, reads symbol keys outside closed _ _ (fun symbol' keys' lower' => ?_) (fun symbol' keys' same => ?_) holds⟩
  · by_cases inside : Ins symbol' keys'
    · rw [layer_inside inside, layer_inside inside]
    · have other : rank symbol' ≠ k := by omega
      rw [layer_other inside other, layer_other inside other]
  · by_cases inside : Ins symbol' keys'
    · rw [layer_inside inside, layer_inside inside]; exact id
    · rw [layer_here inside (same.trans here), layer_here inside (same.trans here)]
      exact le symbol' keys'

/-- **The strata give a fixpoint at every outside atom**: an atom of the last
stratum's rank or below holds exactly when the consequence operator derives
it. -/
theorem strata_fixpoint (reads : Reads Ins rank Closed cons) (top : Nat)
    (bounded : ∀ symbol keys, Closed symbol keys → rank symbol ≤ top) {symbol : Symbol} {keys : List (Key Literal Symbol)}
    (outside : ¬ Ins symbol keys) (closed : Closed symbol keys) :
    strata Ins insideVal rank Closed cons top symbol keys ↔ cons (strata Ins insideVal rank Closed cons top) symbol keys := by
  have le := bounded symbol keys closed
  generalize hk : rank symbol = k at le
  let op := stratumOp Ins insideVal rank Closed cons k (lowerOf Ins insideVal rank Closed cons k)
  have mono := stratumOp_mono (insideVal := insideVal) reads k (lowerOf Ins insideVal rank Closed cons k)
  -- The last stratum agrees with stratum `k`'s layer on every atom of rank `k` or below.
  have agree : ∀ symbol' keys', rank symbol' ≤ k →
      (layer Ins insideVal rank k (lowerOf Ins insideVal rank Closed cons k) (lfp op) symbol' keys' ↔
        strata Ins insideVal rank Closed cons top symbol' keys') := by
    intro symbol' keys' le'
    by_cases inside : Ins symbol' keys'
    · rw [layer_inside inside, strata_inside inside]
    · rw [strata_stable inside top (Nat.le_trans le' le)]
      rcases Nat.lt_or_eq_of_le le' with lt | same
      · rw [layer_other inside (Nat.ne_of_lt lt)]
        cases k with
        | zero => exact absurd lt (Nat.not_lt_zero _)
        | succ k =>
            show strata Ins insideVal rank Closed cons k symbol' keys' ↔ _
            rw [strata_stable inside k (Nat.le_of_lt_succ lt)]
      · rw [same, strata_eq, stepStrata]
  rw [strata_stable outside top (hk ▸ le), hk, strata_eq, stepStrata, layer_here outside hk]
  constructor
  · intro holds
    obtain ⟨_, _, _, derived⟩ := lfp_post mono symbol keys holds
    exact reads symbol keys outside closed _ _ (fun symbol' keys' lt => agree symbol' keys' (by omega))
      (fun symbol' keys' same => (agree symbol' keys' (by omega)).mp) derived
  · intro derived
    refine lfp_pre mono symbol keys ⟨outside, hk, closed, ?_⟩
    exact reads symbol keys outside closed _ _ (fun symbol' keys' lt => (agree symbol' keys' (by omega)).symm)
      (fun symbol' keys' same => (agree symbol' keys' (by omega)).mpr) derived

end Strata


variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

attribute [local instance] Machine.termEq

/-! ## The check: the rules outside the relevant program, stratified -/

namespace Program

variable (program : Program Variable Literal Symbol)

/-- A rule computed by the relevant program: its head's arguments have no
name, and its head is a relevant atom, so every instance of it is an instance
of that relevant atom. -/
def computedRule (atoms : List (GAtom Variable Literal Symbol)) (rule : Rule Variable Literal Symbol) : Bool :=
  (namesOf rule.args).isEmpty && decide ((rule.head, rule.args) ∈ atoms)

/-- A rule respects ranks: its calls no higher than its head, its NAF
literals strictly lower. -/
def respects (rank : Symbol → Nat) (rule : Rule Variable Literal Symbol) : Bool :=
  rule.body.all fun
    | .call predicate _ => decide (rank predicate ≤ rank rule.head)
    | .naf predicate _ => decide (rank predicate < rank rule.head)
    | _ => true

/-- Every rule outside the relevant program respects the ranks. -/
def stratifiedBy (atoms : List (GAtom Variable Literal Symbol)) (rank : Symbol → Nat) : Bool :=
  program.rules.all fun rule => computedRule atoms rule || respects rank rule

/-- The rank a table gives a symbol. -/
def rankIn (table : List (Symbol × Nat)) (symbol : Symbol) : Nat :=
  ((table.find? (·.1 == symbol)).map (·.2)).getD 0

/-- The rank a rule's head needs: its calls' ranks, its NAF literals' ranks
and one. -/
def rankNeed (rank : Symbol → Nat) (rule : Rule Variable Literal Symbol) : Nat :=
  rule.body.foldr (fun goal need => match goal with
    | .call predicate _ => max need (rank predicate)
    | .naf predicate _ => max need (rank predicate + 1)
    | _ => need) 0

/-- One round of the ranks: each declared predicate at least what its rules
outside the relevant program need. -/
def rankRound (atoms : List (GAtom Variable Literal Symbol)) (table : List (Symbol × Nat)) : List (Symbol × Nat) :=
  program.predicates.map fun predicate => (predicate.symbol,
    (program.rules.filter fun rule => rule.head == predicate.symbol && !computedRule atoms rule).foldr
      (fun rule rank => max rank (rankNeed (rankIn table) rule)) (rankIn table predicate.symbol))

/-- The ranks, by as many rounds as there are predicates and one: enough
when no cycle among the rules outside passes through NAF, which the check
then confirms. -/
def ranks (atoms : List (GAtom Variable Literal Symbol)) : List (Symbol × Nat) :=
  Nat.repeat (program.rankRound atoms) (program.predicates.length + 1) []

/-- The rules outside the relevant program, stratified by the computed ranks. -/
def outsideStratified (atoms : List (GAtom Variable Literal Symbol)) : Bool :=
  program.stratifiedBy atoms (rankIn (program.ranks atoms))

/-- The predicate graph's edges of some rules: a rule's head to each
predicate it calls or reads under NAF. -/
def edgesOf (rules : List (Rule Variable Literal Symbol)) : List (Symbol × Symbol) :=
  rules.flatMap fun rule => rule.body.filterMap fun
    | .call predicate _ | .naf predicate _ => some (rule.head, predicate)
    | _ => none

/-- The edges through NAF of some rules. -/
def nafEdgesOf (rules : List (Rule Variable Literal Symbol)) : List (Symbol × Symbol) :=
  rules.flatMap fun rule => rule.body.filterMap fun
    | .naf predicate _ => some (rule.head, predicate)
    | _ => none

/-- The declared predicates on a cycle through NAF of some rules' predicate
graph, the reachability of each predicate computed once. -/
def nafCycleSymbols (rules : List (Rule Variable Literal Symbol)) : List Symbol :=
  let symbols := program.predicates.map (·.symbol)
  let edges := edgesOf rules
  let naf := nafEdgesOf rules
  let reaches := symbols.map fun symbol => (symbol, Tabled.reach edges symbols symbol)
  let reachOf := fun symbol => ((reaches.find? (·.1 == symbol)).map (·.2)).getD []
  symbols.filter fun symbol => naf.any fun edge =>
    (edge.1 == symbol || (reachOf symbol).contains edge.1) && (edge.2 == symbol || (reachOf edge.2).contains symbol)

/-- The rule the check names, with its index: the first rule outside the
relevant program whose head is on a cycle through NAF among the rules outside
and that the computed ranks do not respect; failing that, the first rule
outside they do not respect. -/
def unstratified (atoms : List (GAtom Variable Literal Symbol)) : Option (Nat × Rule Variable Literal Symbol) :=
  let outside := program.rules.zipIdx.filter fun entry => !computedRule atoms entry.1
  let cyclic := program.nafCycleSymbols (outside.map (·.1))
  let rank := rankIn (program.ranks atoms)
  let failing := outside.filter fun entry => !respects rank entry.1
  ((failing.find? fun entry => cyclic.contains entry.1.head).or failing.head?).map fun entry => (entry.2, entry.1)

/-! ## The consequence operator reads by rank -/

variable {program}

mutual
/-- The values of data terms in a key model do not depend on its
interpretation. -/
theorem keys_eval_data {constructors : List (Constructor Literal Symbol)} {hoApplySymbol : Symbol}
    (first second : Symbol → List (Key Literal Symbol) → Prop) (environment : Environment Variable (Key Literal Symbol)) :
    ∀ term : Term Variable Literal Symbol, dataIn constructors term = true →
      (Model.keys hoApplySymbol first).eval environment term = (Model.keys hoApplySymbol second).eval environment term
  | .var _, _ => by simp only [Model.eval]
  | .lit _, _ => by simp only [Model.eval]; rfl
  | .app symbol args, data => by
      simp only [dataIn, Bool.and_eq_true] at data
      simp only [Model.eval]
      show Key.app symbol _ = Key.app symbol _
      rw [keys_evalAll_data first second environment args data.2]
  | .truth, data | .falsity, data | .conj _ _, data | .disj _ _, data | .imp _ _, data | .defaultNeg _, data
  | .forallVar _ _, data | .existsVar _ _, data | .dictionaryCall _ _ _ _, data | .equal _ _, data => by
      simp [dataIn] at data

theorem keys_evalAll_data {constructors : List (Constructor Literal Symbol)} {hoApplySymbol : Symbol}
    (first second : Symbol → List (Key Literal Symbol) → Prop) (environment : Environment Variable (Key Literal Symbol)) :
    ∀ args : List (Term Variable Literal Symbol), dataInAll constructors args = true →
      args.map ((Model.keys hoApplySymbol first).eval environment) = args.map ((Model.keys hoApplySymbol second).eval environment)
  | [], _ => rfl
  | arg :: rest, data => by
      simp only [dataInAll, Bool.and_eq_true] at data
      simp only [List.map_cons, keys_eval_data first second environment arg data.1, keys_evalAll_data first second environment rest data.2]
end

/-- A closed atom holds in a key model by its interpretation, under any
environment. -/
theorem key_call_env (wellFormed : program.WellFormed) {markers interp : Interp Literal Symbol} {symbol : Symbol}
    {args : List (Term Variable Literal Symbol)} (closed : program.closedAt symbol args.length = true)
    (environment : Environment Variable (Key Literal Symbol)) :
    (program.keyModel markers interp).Satisfies environment (.app symbol args) ↔
      interp symbol (args.map ((program.keyModel markers interp).eval environment)) := by
  obtain ⟨found, foundEq, _, _⟩ := closedAt_declared closed
  simp only [Model.Satisfies, Model.eval]
  show resolveKey program.hoApply _ symbol _ ↔ _
  rw [resolveKey_ordinary _ (ordinary_of_declared wellFormed.reserved foundEq)]
  exact join_closed (by rw [List.length_map]; exact closedAt_mem closed)

/-- An atom the completion does not close holds in a key model by the base,
under any environment. -/
theorem key_open_env {markers interp : Interp Literal Symbol} {symbol : Symbol} {args : List (Term Variable Literal Symbol)}
    (ordinary : symbol ≠ program.hoApply) (notClosed : (symbol, args.length) ∉ program.signature.predicates)
    (environment : Environment Variable (Key Literal Symbol)) :
    (program.keyModel markers interp).Satisfies environment (.app symbol args) ↔
      program.base markers symbol (args.map ((program.keyModel markers interp).eval environment)) := by
  simp only [Model.Satisfies, Model.eval]
  show resolveKey program.hoApply _ symbol _ ↔ _
  rw [resolveKey_ordinary _ ordinary]
  exact join_open (by rw [List.length_map]; exact notClosed)

/-- **One literal read by its closed atom**: an interpretation that keeps a
call's atom true, and a NAF literal's atom as it is, keeps the literal true;
every other literal reads no closed atom. -/
theorem goal_transfer (wellFormed : program.WellFormed) {markers first second : Interp Literal Symbol}
    {goal : Goal Variable Literal Symbol} (declared : program.declares goal = true) (data : program.data goal = true)
    {environment : Environment Variable (Key Literal Symbol)}
    (calls : ∀ predicate args, goal = .call predicate args →
      first predicate (args.map ((program.keyModel markers first).eval environment)) →
        second predicate (args.map ((program.keyModel markers first).eval environment)))
    (nafs : ∀ predicate args, goal = .naf predicate args →
      (first predicate (args.map ((program.keyModel markers first).eval environment)) ↔
        second predicate (args.map ((program.keyModel markers first).eval environment)))) :
    (program.keyModel markers first).Satisfies environment goal.toTerm →
      (program.keyModel markers second).Satisfies environment goal.toTerm := by
  have allData : ∀ arg ∈ goal.args, dataIn program.constructors arg = true := List.all_eq_true.mp data
  have sameArgs : ∀ args : List (Term Variable Literal Symbol), (∀ arg ∈ args, dataIn program.constructors arg = true) →
      args.map ((program.keyModel markers first).eval environment) = args.map ((program.keyModel markers second).eval environment) :=
    fun args argsData => keys_evalAll_data _ _ environment args (dataInAll_of argsData)
  have openSame : ∀ (symbol : Symbol) (args : List (Term Variable Literal Symbol)), symbol ≠ program.hoApply →
      (symbol, args.length) ∉ program.signature.predicates → (∀ arg ∈ args, dataIn program.constructors arg = true) →
      (program.keyModel markers first).Satisfies environment (.app symbol args) →
        (program.keyModel markers second).Satisfies environment (.app symbol args) := by
    intro symbol args ordinary notClosed argsData holds
    rw [key_open_env ordinary notClosed] at holds ⊢
    rw [← sameArgs args argsData]; exact holds
  cases goal with
  | call predicate args =>
      intro holds
      change (program.keyModel markers second).Satisfies environment (.app predicate args)
      change (program.keyModel markers first).Satisfies environment (.app predicate args) at holds
      rw [key_call_env wellFormed declared] at holds ⊢
      rw [← sameArgs args allData]
      exact calls predicate args rfl holds
  | naf predicate args =>
      intro holds
      change (program.keyModel markers second).Satisfies environment (.defaultNeg (.app predicate args))
      change (program.keyModel markers first).Satisfies environment (.defaultNeg (.app predicate args)) at holds
      rw [sat_neg _ _ (Model.keys_complement _), key_call_env wellFormed declared] at holds ⊢
      rw [← sameArgs args allData]
      exact fun yes => holds ((nafs predicate args rfl).mpr yes)
  | marker symbol args =>
      simp only [declares, Bool.and_eq_true, Option.isNone_iff_eq_none, bne_iff_ne, ne_eq] at declared
      exact openSame symbol args declared.2 (not_closed_of_none declared.1 _) allData
  | guard symbol arg =>
      obtain ⟨found, foundEq, kind, _⟩ := kindAt_declared declared
      exact openSame symbol [arg] (ordinary_of_declared wellFormed.reserved foundEq)
        (not_closed_of_kind wellFormed.unique foundEq (by simp [Predicate.closed, kind]) _) allData
  | primitive symbol inputs output =>
      obtain ⟨found, foundEq, kind, _⟩ := kindAt_declared declared
      exact openSame symbol (inputs ++ [output]) (ordinary_of_declared wellFormed.reserved foundEq)
        (not_closed_of_kind wellFormed.unique foundEq (by simp [Predicate.closed, kind]) _) allData
  | equal left right =>
      intro holds
      change (program.keyModel markers second).Satisfies environment (.equal left right)
      change (program.keyModel markers first).Satisfies environment (.equal left right) at holds
      rw [Model.satisfies_equal] at holds ⊢
      rw [← keys_eval_data _ _ environment left (allData left (by simp [Goal.args])),
        ← keys_eval_data _ _ environment right (allData right (by simp [Goal.args]))]
      exact holds
  | differ left right =>
      intro holds
      change (program.keyModel markers second).Satisfies environment (.defaultNeg (.equal left right))
      change (program.keyModel markers first).Satisfies environment (.defaultNeg (.equal left right)) at holds
      rw [sat_neg _ _ (Model.keys_complement _), Model.satisfies_equal] at holds ⊢
      rw [← keys_eval_data _ _ environment left (allData left (by simp [Goal.args])),
        ← keys_eval_data _ _ environment right (allData right (by simp [Goal.args]))]
      exact holds

/-- **The consequence operator reads by rank**: at an atom outside the
relevant program, a rule outside it reads the atoms of lower rank as fixed and
those of its own rank positively; a computed rule's head is relevant, so it
does not conclude the atom. -/
theorem consequence_reads (wellFormed : program.WellFormed) {markers : Interp Literal Symbol}
    {atoms : List (GAtom Variable Literal Symbol)} {rank : Symbol → Nat} (stratified : program.stratifiedBy atoms rank = true) :
    Strata.Reads (fun symbol keys => ∃ atom ∈ atoms, atom.1 = symbol ∧ keyArgs atom = keys) rank
      (fun symbol keys => (symbol, keys.length) ∈ program.signature.predicates)
      (consequence program.hoApply program.signature program.clauses (program.base markers)) := by
  intro symbol keys outside _ first second lower same ⟨closedKey, args, body, member, environment, argsEq, bodyHolds⟩
  obtain ⟨rule, ruleMember, headEq, rfl, rfl⟩ := rule_of_clause member
  have ruleOk := wellFormed.rules rule ruleMember
  refine ⟨closedKey, rule.args, rule.body.map Goal.toTerm, member, environment, ?_, ?_⟩
  · rw [← argsEq, keys_evalAll_data _ _ environment rule.args (dataInAll_of ruleOk.data)]
  rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp stratified rule ruleMember) with computed | respected
  · exfalso
    simp only [computedRule, Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at computed
    obtain ⟨noNames, relevant⟩ := computed
    refine outside ⟨(rule.head, rule.args), relevant, headEq, ?_⟩
    have argsGround : groundInAll program.constructors rule.args = true := by
      refine (groundInAll_iff _).mpr fun arg inside => groundIn_of_closed (ruleOk.data arg inside) ?_
      cases names : arg.freeVars with
      | nil => rfl
      | cons name _ =>
          have : name ∈ namesOf rule.args := List.mem_flatMap.mpr ⟨arg, inside, by rw [names]; exact List.mem_cons_self⟩
          rw [noNames] at this; cases this
    rw [← argsEq, eval_grounds (model := program.keyModel markers first) environment rule.args argsGround,
      dens_keys _ program.constructors rule.args argsGround]
    rfl
  · simp only [respects, List.all_eq_true] at respected
    rw [Model.satisfies_conjunction] at bodyHolds ⊢
    intro term termMember
    obtain ⟨goal, goalMember, rfl⟩ := List.mem_map.mp termMember
    have ranked := respected goal goalMember
    have goalOk := Scans.goals ruleOk.scans goal goalMember
    refine goal_transfer wellFormed goalOk.1 goalOk.2 (fun predicate callArgs isCall => ?_) (fun predicate nafArgs isNaf => ?_)
      (bodyHolds _ termMember)
    · subst isCall
      simp only [decide_eq_true_eq] at ranked
      rw [headEq] at ranked
      rcases Nat.lt_or_eq_of_le ranked with lt | eq
      · exact (lower _ _ lt).mp
      · exact same _ _ eq
    · subst isNaf
      simp only [decide_eq_true_eq] at ranked
      rw [headEq] at ranked
      exact lower _ _ ranked

/-! ## The extension -/

/-- The atoms of a ground body over ground data terms: those of its calls,
its NAF literals, and its markers, at an instance ground on its names. -/
theorem groundBody_ground {σ : Variable → Term Variable Literal Symbol} {body : List (Goal Variable Literal Symbol)}
    (ok : ∀ goal ∈ body, program.declares goal = true ∧ program.data goal = true)
    (ground : GroundOn program.constructors σ (bodyNames body)) :
    ∀ atom, atom ∈ (groundBody σ body).1 ∨ atom ∈ (groundBody σ body).2.1 ∨ atom ∈ (groundBody σ body).2.2 →
      ∀ term ∈ atom.2, groundIn program.constructors term = true := by
  have each : ∀ goal ∈ body, ∀ term ∈ goal.args.map (subst σ), groundIn program.constructors term = true :=
    fun goal member => groundIn_substs (List.all_eq_true.mp (ok goal member).2)
      fun name inside => ground name (List.mem_flatMap.mpr ⟨goal, member, inside⟩)
  intro atom inside
  simp only [groundBody, List.mem_filterMap] at inside
  rcases inside with ⟨goal, member, produced⟩ | ⟨goal, member, produced⟩ | ⟨goal, member, produced⟩ <;>
  · cases goal <;> simp only [Goal.callAtom, Goal.nafAtom, Goal.markerAtom, Option.some.injEq, reduceCtorEq] at produced <;>
      (subst produced; exact each _ member)

/-- **The ground relevant program is over ground data terms**: its atoms and
its markers. -/
theorem groundProgram_ground (wellFormed : program.WellFormed) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) (noParameters : query.parameters = [])
    (conditionsGround : ∀ goal ∈ query.conditions, goal.names = [])
    (closes_ : ∃ n, program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) = true) :
    (∀ atom ∈ (program.groundProgram query closes_).atoms, ∀ term ∈ atom.2, groundIn program.constructors term = true) ∧
      ∀ atom ∈ (program.groundProgram query closes_).markerAtoms, ∀ term ∈ atom.2, groundIn program.constructors term = true := by
  refine ⟨fun atom member => ?_, fun atom member => ?_⟩
  · obtain ⟨_, entry⟩ := (relevantAtoms_iff wellFormed queryOk evidence noParameters conditionsGround closes_ atom).mp member
    exact entry.2.2.2.1
  · simp only [GroundProgram.markerAtoms, List.mem_eraseDups, List.mem_append, List.mem_flatMap] at member
    rcases member with ⟨⟨head, body⟩, bodyMember, inside⟩ | ⟨body, bodyMember, inside⟩
    · obtain ⟨rule, σ, ⟨_, _, _, atVertex, groundRule, _, _⟩, rfl⟩ :=
        (relevantInstances_iff wellFormed queryOk evidence noParameters closes_ head body).mp bodyMember
      have ruleOk := wellFormed.rules rule (rulesOf_mem (mem_rulesAt.mp atVertex).1)
      exact groundBody_ground (Scans.goals ruleOk.scans) (fun name inside => groundRule name (List.mem_append_right _ inside))
        atom (.inr (.inr inside))
    · simp only [groundProgram, List.mem_cons] at bodyMember
      rcases bodyMember with fromDenials | rfl | fromGoals
      · obtain ⟨denial, denialMember, σ, ground, _, rfl⟩ := (denialBodies_iff wellFormed queryOk evidence body).mp fromDenials
        exact groundBody_ground (Scans.goals (wellFormed.denials denial denialMember)) ground atom (.inr (.inr inside))
      · have namesNil : bodyNames query.conditions = [] := by
          simp only [bodyNames, List.flatMap_eq_nil_iff]; exact conditionsGround
        refine groundBody_ground (fun goal member => ⟨(queryOk.conditions goal member).1, (queryOk.conditions goal member).2.1⟩)
          (fun name inside => by rw [namesNil] at inside; cases inside) atom (.inr (.inr inside))
      · obtain ⟨σ, ⟨ground, _⟩, rfl⟩ := (goalBodies_iff wellFormed queryOk evidence noParameters body).mp fromGoals
        exact groundBody_ground (Scans.goals queryOk.goals) ground atom (.inr (.inr inside))

/-- Ground atoms with the same symbol and keys are the same. -/
theorem atom_keys_injective {atom other : GAtom Variable Literal Symbol}
    (ground : ∀ term ∈ atom.2, groundIn program.constructors term = true)
    (otherGround : ∀ term ∈ other.2, groundIn program.constructors term = true)
    (symbolEq : atom.1 = other.1) (keysEq : keyArgs atom = keyArgs other) : atom = other := by
  obtain ⟨symbol, args⟩ := atom
  obtain ⟨_, others⟩ := other
  simp only at symbolEq
  subst symbolEq
  exact congrArg (Prod.mk _) (dataKeys_injective_of program.hoApply ground otherGround keysEq)

/-- **A model of the relevant program extends to a key fixpoint** when the
rules outside it are stratified: the relevant atoms keep the model's values,
the markers it reads too, and every other atom is decided by the strata. -/
theorem extends_model (wellFormed : program.WellFormed) (guarded : program.Guarded) {query : Query Variable Literal Symbol}
    (queryOk : QueryOk program query) (evidence : program.notes query = []) (noParameters : query.parameters = [])
    (conditionsGround : ∀ goal ∈ query.conditions, goal.names = [])
    (closes_ : ∃ n, program.closedCalls (program.answersFor query) (program.callRounds (program.answersFor query) query n) = true)
    {rank : Symbol → Nat} (stratified : program.stratifiedBy (program.relevantAtoms query closes_) rank = true)
    {closed marked : GAtom Variable Literal Symbol → Prop} (model : (program.groundProgram query closes_).Model closed marked) :
    ∃ markers interp, program.KeyFixpoint markers interp ∧
      (∀ atom ∈ (program.groundProgram query closes_).atoms, closedOf interp atom ↔ closed atom) ∧
      ∀ atom ∈ (program.groundProgram query closes_).markerAtoms, closedOf markers atom ↔ marked atom := by
  have atomsIff := relevantAtoms_iff wellFormed queryOk evidence noParameters conditionsGround closes_
  have instancesIff := relevantInstances_iff wellFormed queryOk evidence noParameters closes_
  have closedProgram := groundProgram_closed wellFormed queryOk evidence noParameters conditionsGround closes_
  obtain ⟨atomsGround, markersGround⟩ := groundProgram_ground wellFormed queryOk evidence noParameters conditionsGround closes_
  let g := program.groundProgram query closes_
  let markers : Interp Literal Symbol := fun symbol keys =>
    ∃ atom ∈ g.markerAtoms, marked atom ∧ atom.1 = symbol ∧ keyArgs atom = keys
  let Ins : Symbol → List (Key Literal Symbol) → Prop := fun symbol keys => ∃ atom ∈ g.atoms, atom.1 = symbol ∧ keyArgs atom = keys
  let insideVal : Interp Literal Symbol := fun symbol keys => ∃ atom ∈ g.atoms, closed atom ∧ atom.1 = symbol ∧ keyArgs atom = keys
  let Closed : Symbol → List (Key Literal Symbol) → Prop := fun symbol keys => (symbol, keys.length) ∈ program.signature.predicates
  let cons := consequence program.hoApply program.signature program.clauses (program.base markers)
  let top := (program.closedKeys.map fun key => rank key.1).foldr max 0
  let interp := Strata.strata Ins insideVal rank Closed cons top
  have reads : Strata.Reads Ins rank Closed cons := consequence_reads wellFormed stratified
  have bounded : ∀ symbol keys, Closed symbol keys → rank symbol ≤ top := by
    intro symbol keys closedKey
    exact (le_foldr_max _ 0).2 _ (List.mem_map.mpr ⟨_, closedKey, rfl⟩)
  have outsideFix : ∀ symbol keys, ¬ Ins symbol keys → Closed symbol keys → (interp symbol keys ↔ cons interp symbol keys) :=
    fun _ _ outside closedKey => Strata.strata_fixpoint reads top bounded outside closedKey
  have atomsAgree : ∀ atom ∈ g.atoms, closedOf interp atom ↔ closed atom := by
    intro atom member
    refine (Strata.strata_inside (insideVal := insideVal) (rank := rank) (Closed := Closed) (cons := cons)
      ⟨atom, member, rfl, rfl⟩ top).trans ?_
    constructor
    · rintro ⟨other, otherMember, holds, symbolEq, keysEq⟩
      rw [atom_keys_injective (atomsGround other otherMember) (atomsGround atom member) symbolEq keysEq] at holds
      exact holds
    · exact fun holds => ⟨atom, member, holds, rfl, rfl⟩
  have markersAgree : ∀ atom ∈ g.markerAtoms, closedOf markers atom ↔ marked atom := by
    intro atom member
    constructor
    · rintro ⟨other, otherMember, holds, symbolEq, keysEq⟩
      rw [atom_keys_injective (markersGround other otherMember) (markersGround atom member) symbolEq keysEq] at holds
      exact holds
    · exact fun holds => ⟨atom, member, holds, rfl, rfl⟩
  have bodyAgree : ∀ body : GroundBody Variable Literal Symbol, (∀ atom, atom ∈ body.1 ∨ atom ∈ body.2.1 → atom ∈ g.atoms) →
      (∀ atom ∈ body.2.2, atom ∈ g.markerAtoms) →
        (body.Holds (closedOf interp) (closedOf markers) ↔ body.Holds closed marked) :=
    fun body inAtoms inMarkers => GroundBody.holds_congr (fun atom inside => atomsAgree atom (inAtoms atom inside))
      (fun atom inside => markersAgree atom (inMarkers atom inside))
  have instanceHolds : ∀ {atom : GAtom Variable Literal Symbol} {rule : Rule Variable Literal Symbol}
      {σ : Variable → Term Variable Literal Symbol}, program.Instance query atom rule σ →
        ((program.keyModel markers interp).Satisfies (fun name => Open.dataKey (σ name)) (bodyTerm rule.body) ↔
          (groundBody σ rule.body).Holds closed marked) := by
    intro atom rule σ inst
    obtain ⟨_, _, _, atVertex, groundRule, _, passes⟩ := id inst
    have ruleOk := wellFormed.rules rule (rulesOf_mem (mem_rulesAt.mp atVertex).1)
    have member := (instancesIff atom (groundBody σ rule.body)).mpr ⟨rule, σ, inst, rfl⟩
    rw [passing_holds_iff wellFormed (Scans.goals ruleOk.scans)
      (fun name inside => groundRule name (List.mem_append_right _ inside)) passes]
    exact bodyAgree _ (closedProgram.1 _ member).2 (g.markerAtoms_rules member)
  have inside : ∀ atom, program.RelevantAtom query atom → program.RelevantHolds query markers interp atom := by
    intro atom relevant
    have member := (atomsIff atom).mpr relevant
    unfold RelevantHolds
    rw [show interp atom.1 (keyArgs atom) ↔ closedOf interp atom from Iff.rfl, atomsAgree atom member, model.1 atom member]
    constructor
    · rintro ⟨body, bodyMember, holds⟩
      obtain ⟨rule, σ, inst, rfl⟩ := (instancesIff atom body).mp bodyMember
      exact ⟨rule, σ, inst, (instanceHolds inst).mpr holds⟩
    · rintro ⟨rule, σ, inst, holds⟩
      exact ⟨_, (instancesIff atom _).mpr ⟨rule, σ, inst, rfl⟩, (instanceHolds inst).mp holds⟩
  have notInside : ∀ symbol keys, ¬ (∃ atom, program.RelevantAtom query atom ∧ atom.1 = symbol ∧ keyArgs atom = keys) →
      ¬ Ins symbol keys := fun symbol keys none ⟨atom, member, symbolEq, keysEq⟩ =>
    none ⟨atom, (atomsIff atom).mp member, symbolEq, keysEq⟩
  have supported : program.Supported markers interp := by
    intro symbol keys closedKey holds
    by_cases isInside : Ins symbol keys
    · obtain ⟨atom, member, rfl, rfl⟩ := isInside
      obtain ⟨rule, σ, inst, bodyHolds⟩ := (inside atom ((atomsIff atom).mp member)).mp holds
      obtain ⟨vertex, _, entry, atVertex, _, headEq, _⟩ := inst
      obtain ⟨found, ruleHead⟩ := mem_rulesOf.mp (mem_rulesAt.mp atVertex).1
      have derived := consequence_of_instance wellFormed (List.mem_of_getElem? found) bodyHolds
      rw [headEq, ruleHead, ← entry.2.1] at derived
      exact derived
    · exact (outsideFix symbol keys isInside closedKey).mp holds
  have denied : Denied program.hoApply program.signature program.clauses (program.base markers) interp := by
    refine (denied_iff wellFormed guarded evidence supported).mpr fun body member σ ground passes holds => ?_
    have bodyMember := (denialBodies_iff wellFormed queryOk evidence (groundBody σ body)).mpr ⟨body, member, σ, ground, passes, rfl⟩
    have keyHolds := (passing_holds_iff wellFormed (Scans.goals (wellFormed.denials body member)) ground passes).mp holds
    have inBodies : groundBody σ body ∈ g.denials ++ g.conditions :: g.goals := List.mem_append_left _ bodyMember
    exact model.2 _ bodyMember ((bodyAgree _ (closedProgram.2 _ inBodies) (g.markerAtoms_bodies inBodies)).mp keyHolds)
  exact ⟨markers, interp,
    fixpoint_of_relevant wellFormed guarded queryOk evidence inside
      (fun symbol keys closedKey none => outsideFix symbol keys (notInside symbol keys none) closedKey) denied,
    atomsAgree, markersAgree⟩

end Program

end AnthillModKbSpec.IR
