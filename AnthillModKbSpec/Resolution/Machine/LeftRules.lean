import AnthillModKbSpec.Resolution.Machine.Commands

/-! # Left rules and compound clause heads: command contracts (S09)

Each S09 command uses a selected assumption, or a clause with a compound head,
together with its continuation. It is one machine candidate whose rule is a
`Derived` command and whose premises are the obligations it leaves, in the
order they run. Its node is completed, like every node, only after all its
premises are proved. The contracts here fix what each command means; the left
strategy (`Machine/LeftStrategy`) decides when to offer which.

| Command | Selected | Premises, in order (added assumptions, opened names) |
| --- | --- | --- |
| `conjUse` | `A ∧ B` assumed | the goal (`A`, `B`) |
| `disjCases` | `A ∨ B` assumed | the goal (`A`); the goal (`B`) |
| `existsOpen` | `∃x. A` assumed | the goal (`A[e/x]`; rigid `e`) |
| `forallUse` | `∀x̄. A` assumed, with witnesses | the goal (the instance) |
| `impUse` | `∀x̄. (A → B)` assumed, with witnesses | the instance of `A`; the goal (the instance of `B`) |
| `headUse` | a clause `H :- body` | the renamed body; the goal (the renamed head) |
| `headProject` | a clause with a conjunctive head | the renamed body, for a goal matched against a conjunct |
| `headDenial` | a clause with head `A → false` | the renamed body; the renamed `A`, for a falsity goal |

An assumption is selected as read through the store, so a command also reads an
assumption written as a flexible name. Its premises are built from that
reading and read through the final answers like every obligation. Implication
selection proves `A` and only then makes `B` available: assuming `A → B` does
not run `A`. A disjunctive head is never used by choosing a disjunct: its
instance is assumed by the continuation, where case analysis needs both cases.
A head `P → Q` stays a local rule of the continuation; a head `A → false` is
also a denial, conditional falsity. The completion contracts read every
command through the answers (`*_soundUnder`), by `Derives` rules only: a cut
is implication introduction followed by elimination, in the original context. -/

namespace AnthillModKbSpec

variable {Variable Literal Symbol : Type} [DecidableEq Variable]

/-- The conjunct of a nested conjunction at `path`: `false` the left
component, `true` the right one. -/
def Term.component? : List Bool → Term Variable Literal Symbol → Option (Term Variable Literal Symbol)
  | [], term => some term
  | false :: path, .conj left _ => Term.component? path left
  | true :: path, .conj _ right => Term.component? path right
  | _ :: _, _ => none

omit [DecidableEq Variable] in
theorem Term.component?_conj {direction : Bool} {path : List Bool} {formula component : Term Variable Literal Symbol}
    (found : formula.component? (direction :: path) = some component) :
    ∃ left right, formula = .conj left right ∧ (if direction then right else left).component? path = some component := by
  cases formula <;> cases direction <;> simp only [Term.component?, reduceCtorEq] at found <;>
    exact ⟨_, _, rfl, found⟩

/-- Projecting a conjunct derives it. -/
theorem Derives.component {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
    {context : ProofContext Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol} :
    ∀ {path : List Bool} {formula component : Formula Variable Literal Symbol},
      formula.component? path = some component → Derives hoApplySymbol kb context formula naf →
        Derives hoApplySymbol kb context component naf
  | [], _, _, found, proof => by cases found; exact proof
  | direction :: _, _, _, found, proof => by
      obtain ⟨left, right, rfl, rest⟩ := Term.component?_conj found
      cases direction
      · exact Derives.component rest (.conjLeft proof)
      · exact Derives.component rest (.conjRight proof)

omit [DecidableEq Variable] in
/-- A map that commutes with conjunction keeps the conjuncts. -/
theorem Term.component?_map {f : Term Variable Literal Symbol → Term Variable Literal Symbol}
    (conj : ∀ left right, f (.conj left right) = .conj (f left) (f right)) :
    ∀ {path : List Bool} {formula component : Term Variable Literal Symbol},
      formula.component? path = some component → (f formula).component? path = some (f component)
  | [], _, _, found => by cases found; rfl
  | direction :: _, _, _, found => by
      obtain ⟨left, right, rfl, rest⟩ := Term.component?_conj found
      cases direction <;> simpa [conj, Term.component?] using Term.component?_map conj rest

variable [FreshNames Variable]

namespace Machine

namespace Expansion

variable {Certificate : Type}

/-- `A ∧ B` assumed, as read: the goal under both components. -/
def conjUse (left right goal : Formula Variable Literal Symbol) : Expansion Variable Literal Symbol Certificate :=
  { rule := .derived (.conjUse (.conj left right))
    premises := [{ discharge := { assumptions := [left, right] }, goal := goal }] }

/-- `A ∨ B` assumed, as read: the same goal in two AND contexts, one per case.
Neither case's assumption reaches the other or the parent. -/
def disjCases (left right goal : Formula Variable Literal Symbol) : Expansion Variable Literal Symbol Certificate :=
  { rule := .derived (.disjCases (.disj left right))
    premises := [{ discharge := { assumptions := [left] }, goal := goal },
      { discharge := { assumptions := [right] }, goal := goal }] }

/-- `∃x. A` assumed, as read: opened at a fresh rigid witness, which is in
scope only in the continuation. -/
def existsOpen (binder : Variable) (body : Formula Variable Literal Symbol) (eigen : Variable)
    (goal : Formula Variable Literal Symbol) : Expansion Variable Literal Symbol Certificate :=
  { rule := .derived (.existsOpen (.existsVar binder body) eigen)
    premises := [{ discharge := { assumptions := [body.instantiate (Substitution.single binder (.var eigen))],
                                  rigids := [eigen] }
                   goal := goal }] }

/-- `∀x̄. A` assumed, as read, at explicit witnesses: the goal under the
instance. `flexibles` are the fresh names among the witnesses. -/
def forallUse (assumption : Formula Variable Literal Symbol) (witnesses : List (Term Variable Literal Symbol))
    (instantiated goal : Formula Variable Literal Symbol) (flexibles : List Variable) :
    Expansion Variable Literal Symbol Certificate :=
  { rule := .derived (.forallUse assumption witnesses), flexibles := flexibles
    premises := [{ discharge := { assumptions := [instantiated] }, goal := goal }] }

/-- `∀x̄. (A → B)` assumed, as read, at explicit witnesses: first the instance
of `A`, then the goal under the instance of `B`. -/
def impUse (assumption : Formula Variable Literal Symbol) (witnesses : List (Term Variable Literal Symbol))
    (premise conclusion goal : Formula Variable Literal Symbol) (flexibles : List Variable) :
    Expansion Variable Literal Symbol Certificate :=
  { rule := .derived (.impUse assumption witnesses), flexibles := flexibles
    premises := [{ goal := premise }, { discharge := { assumptions := [conclusion] }, goal := goal }] }

/-- A clause `H :- body`, its template names renamed to fresh flexible names:
first the renamed body, then the goal under the renamed head. The head is
assumed only once the body is proved. -/
def headUse (head : Formula Variable Literal Symbol) (body : List (Term Variable Literal Symbol))
    (fresh : List (Variable × Variable)) (goal : Formula Variable Literal Symbol) :
    Expansion Variable Literal Symbol Certificate :=
  { rule := .derived (.headUse (.definite head body) fresh), flexibles := fresh.map Prod.snd
    premises := [{ goal := (Term.conjunction body).instantiate (Substitution.rename fresh) },
      { discharge := { assumptions := [head.instantiate (Substitution.rename fresh)] }, goal := goal }] }

/-- A clause with a conjunctive head, split: the conjunct at `path`, renamed and
matched against the goal (the bindings), concludes it from the renamed body. -/
def headProject (head : Formula Variable Literal Symbol) (body : List (Term Variable Literal Symbol))
    (fresh : List (Variable × Variable)) (path : List Bool) (bindings : List (Variable × Term Variable Literal Symbol)) :
    Expansion Variable Literal Symbol Certificate :=
  { rule := .derived (.headProject (.definite head body) fresh path), flexibles := fresh.map Prod.snd
    bindings := bindings
    premises := [{ goal := (Term.conjunction body).instantiate (Substitution.rename fresh) }] }

/-- A clause with head `A → false`, as the denial `false :- body, A`: the
renamed body, then the renamed `A`. -/
def headDenial (premise : Formula Variable Literal Symbol) (body : List (Term Variable Literal Symbol))
    (fresh : List (Variable × Variable)) : Expansion Variable Literal Symbol Certificate :=
  { rule := .derived (.headDenial (.definite (.imp premise .falsity) body) fresh), flexibles := fresh.map Prod.snd
    premises := [{ goal := (Term.conjunction body).instantiate (Substitution.rename fresh) },
      { goal := premise.instantiate (Substitution.rename fresh) }] }

/-! ## Completion contracts, read through the answers -/

section Reading

variable {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}
  {scope : Scope Variable Literal Symbol} {store : Store Variable Literal Symbol}

/-- A selected assumption read as `formula` is derived by assumption. -/
private theorem selected {assumption formula : Formula Variable Literal Symbol}
    (member : assumption ∈ scope.assumptions) (reads : store.resolve assumption = store.resolve formula) :
    Derives hoApplySymbol kb (scope.assumptions.map store.resolve) (store.resolve formula) naf := by
  rw [← reads]; exact .assumption (List.mem_map_of_mem member)

theorem conjUse_soundUnder {assumption left right goal : Formula Variable Literal Symbol}
    (member : assumption ∈ scope.assumptions) (reads : store.resolve assumption = store.resolve (.conj left right)) :
    (conjUse (Certificate := Certificate) left right goal).SoundUnder hoApplySymbol kb naf store ⟨scope, goal⟩ :=
  fun proofs => by
    have premise := read_premise.mp
      (proofs { discharge := { assumptions := [left, right] }, goal := goal } (by simp [conjUse]))
    have inside : Term.conj (store.resolve left) (store.resolve right) ∈ scope.assumptions.map store.resolve := by
      rw [← Store.resolve_conj, ← reads]; exact List.mem_map_of_mem member
    show Derives _ _ (scope.assumptions.map store.resolve) (store.resolve goal) _
    exact Derives.cut (.conjRight (.assumption inside))
      (Derives.cut (.conjLeft (.assumption (List.mem_cons_of_mem _ inside))) premise)

theorem disjCases_soundUnder {assumption left right goal : Formula Variable Literal Symbol}
    (member : assumption ∈ scope.assumptions) (reads : store.resolve assumption = store.resolve (.disj left right)) :
    (disjCases (Certificate := Certificate) left right goal).SoundUnder hoApplySymbol kb naf store ⟨scope, goal⟩ :=
  fun proofs => disjElim_soundUnder (Certificate := Certificate) fun premise inside => by
    simp only [disjElim, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl
    · exact read_premise.mpr (by simpa [Obligation.context] using selected (hoApplySymbol := hoApplySymbol) (kb := kb) (naf := naf) member reads)
    all_goals exact proofs _ (by simp [disjCases])

/-- The eigenvariable must be fresh for the read obligation
(`Store.commit_fresh_resolved`); its freshness for the read existential follows,
since the existential is an assumption of the obligation. -/
theorem existsOpen_soundUnder {assumption : Formula Variable Literal Symbol} {binder eigen : Variable}
    {body goal : Formula Variable Literal Symbol} (member : assumption ∈ scope.assumptions)
    (reads : store.resolve assumption = store.resolve (.existsVar binder body))
    (fresh : (⟨scope, goal⟩ : Obligation Variable Literal Symbol).FreshUnder store eigen) :
    (existsOpen (Certificate := Certificate) binder body eigen goal).SoundUnder hoApplySymbol kb naf store
      ⟨scope, goal⟩ := fun proofs => by
  have freshBody : eigen ∉ (store.resolve (.existsVar binder body)).freeVars := by
    rw [← reads]; exact fresh.context _ (List.mem_map_of_mem member)
  refine existsElim_soundUnder (Certificate := Certificate) fresh freshBody fun premise inside => ?_
  simp only [existsElim, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl
  · exact read_premise.mpr (by simpa [Obligation.context] using selected (hoApplySymbol := hoApplySymbol) (kb := kb) (naf := naf) member reads)
  · exact proofs _ (by simp [existsOpen])

theorem forallUse_soundUnder {assumption rule instantiated goal : Formula Variable Literal Symbol}
    {witnesses : List (Term Variable Literal Symbol)} {flexibles : List Variable}
    (member : assumption ∈ scope.assumptions) (reads : store.resolve assumption = store.resolve rule)
    (computed : rule.instantiateLeading witnesses = some instantiated) :
    (forallUse (Certificate := Certificate) rule witnesses instantiated goal flexibles).SoundUnder hoApplySymbol kb naf store
      ⟨scope, goal⟩ := fun proofs => by
  have premise := read_premise.mp
    (proofs { discharge := { assumptions := [instantiated] }, goal := goal } (by simp [forallUse]))
  exact Derives.cut (Derives.resolve_instantiateLeading store.bindings witnesses computed
    (selected member reads)) premise

/-- Implication selection: the instance of `A` in the original context, then
the goal under the instance of `B`, which is derived by implication elimination
and discharged from the continuation. -/
theorem impUse_soundUnder {assumption rule premise conclusion goal : Formula Variable Literal Symbol}
    {witnesses : List (Term Variable Literal Symbol)} {flexibles : List Variable}
    (member : assumption ∈ scope.assumptions) (reads : store.resolve assumption = store.resolve rule)
    (computed : rule.instantiateLeading witnesses = some (.imp premise conclusion)) :
    (impUse (Certificate := Certificate) rule witnesses premise conclusion goal flexibles).SoundUnder hoApplySymbol kb
      naf store ⟨scope, goal⟩ := fun proofs => by
  have argument := read_premise.mp (proofs { goal := premise } (by simp [impUse]))
  have continuation := read_premise.mp
    (proofs { discharge := { assumptions := [conclusion] }, goal := goal } (by simp [impUse]))
  have instantiated : Derives hoApplySymbol kb (scope.assumptions.map store.resolve)
      (store.resolve (.imp premise conclusion)) naf :=
    Derives.resolve_instantiateLeading store.bindings witnesses computed (selected member reads)
  rw [Store.resolve_imp] at instantiated
  exact Derives.cut (.impElim instantiated argument) continuation

theorem headUse_soundUnder {head goal : Formula Variable Literal Symbol} {body : List (Term Variable Literal Symbol)}
    {fresh : List (Variable × Variable)} (member : HornClause.definite head body ∈ kb) :
    (headUse (Certificate := Certificate) head body fresh goal).SoundUnder hoApplySymbol kb naf store ⟨scope, goal⟩ :=
  fun proofs => by
    have established := clause_soundUnder (Certificate := Certificate) (bindings := []) (scope := scope)
      (goal := head.instantiate (Substitution.rename fresh)) member rfl fun premise inside =>
        proofs premise (by simp only [clause, List.mem_singleton] at inside; simp [headUse, inside])
    have continuation := read_premise.mp
      (proofs { discharge := { assumptions := [head.instantiate (Substitution.rename fresh)] }, goal := goal }
        (by simp [headUse]))
    exact Derives.cut established continuation

theorem headProject_soundUnder {head component goal : Formula Variable Literal Symbol}
    {body : List (Term Variable Literal Symbol)} {fresh : List (Variable × Variable)} {path : List Bool}
    {bindings : List (Variable × Term Variable Literal Symbol)} (member : HornClause.definite head body ∈ kb)
    (found : head.component? path = some component)
    (matched : store.resolve (component.instantiate (Substitution.rename fresh)) = store.resolve goal) :
    (headProject (Certificate := Certificate) head body fresh path bindings).SoundUnder hoApplySymbol kb naf store
      ⟨scope, goal⟩ := fun proofs => by
  have whole := clause_soundUnder (Certificate := Certificate) (bindings := bindings) (scope := scope)
    (goal := head.instantiate (Substitution.rename fresh)) member rfl fun premise inside =>
      proofs premise (by simpa [clause, headProject] using inside)
  simp only [ReadDerives, Obligation.context, ← matched]
  exact Derives.component
    (Term.component?_map (Store.resolve_conj store) (Term.component?_map (fun _ _ => by simp [Term.instantiate]) found))
    whole

theorem headDenial_soundUnder {premise goal : Formula Variable Literal Symbol}
    {body : List (Term Variable Literal Symbol)} {fresh : List (Variable × Variable)}
    (member : HornClause.definite (.imp premise .falsity) body ∈ kb) (read : store.resolve goal = .falsity) :
    (headDenial (Certificate := Certificate) premise body fresh).SoundUnder hoApplySymbol kb naf store ⟨scope, goal⟩ :=
  fun proofs => by
    have rule := clause_soundUnder (Certificate := Certificate) (bindings := []) (scope := scope)
      (goal := (Term.imp premise .falsity).instantiate (Substitution.rename fresh)) member rfl fun premise inside =>
        proofs premise (by simp only [clause, List.mem_singleton] at inside; simp [headDenial, inside])
    have argument := read_premise.mp
      (proofs { goal := premise.instantiate (Substitution.rename fresh) } (by simp [headDenial]))
    simp only [ReadDerives, Obligation.context, Term.instantiate, Store.resolve_imp, Store.resolve_falsity] at rule
    simp only [ReadDerives, Obligation.context, read]
    exact .impElim rule argument

end Reading

end Expansion

end Machine

end AnthillModKbSpec
