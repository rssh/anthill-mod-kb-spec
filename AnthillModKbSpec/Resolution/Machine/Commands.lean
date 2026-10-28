import AnthillModKbSpec.Resolution.Machine.State
import AnthillModKbSpec.Resolution.Machine.Instantiation

namespace AnthillModKbSpec.Machine

variable {Variable Literal Symbol Certificate : Type} [DecidableEq Variable]

/-! ## Named command contracts

Each contract maps a focused obligation to one candidate: the rule it applies,
its premises with their scope effects, and the fresh names it introduces. The
machine fixes completion: the node is built after all premises succeed. Concrete
commands (S06 onward) decide when to offer which contract; this file fixes what
each one means. -/

namespace Expansion

/-- Close a truth goal. -/
def truth : Expansion Variable Literal Symbol Certificate := { rule := .truth }

/-- Close a goal present in the scope's assumptions, after `bindings`. -/
def assumption (bindings : List (Variable × Term Variable Literal Symbol) := []) :
    Expansion Variable Literal Symbol Certificate :=
  { rule := .assumption, bindings := bindings }

/-- AND: both conjuncts, in the parent's scope, sharing answers. -/
def conjIntro (left right : Formula Variable Literal Symbol) : Expansion Variable Literal Symbol Certificate :=
  { rule := .conjIntro, premises := [{ goal := left }, { goal := right }] }

/-- One OR alternative of a disjunctive goal; the other is a separate candidate. -/
def disjLeft (left : Formula Variable Literal Symbol) : Expansion Variable Literal Symbol Certificate :=
  { rule := .disjLeft, premises := [{ goal := left }] }

def disjRight (right : Formula Variable Literal Symbol) : Expansion Variable Literal Symbol Certificate :=
  { rule := .disjRight, premises := [{ goal := right }] }

/-- Case analysis on a disjunction: the same goal under each case, an AND of two
proofs with separate local assumptions. -/
def disjElim (left right goal : Formula Variable Literal Symbol) : Expansion Variable Literal Symbol Certificate :=
  { rule := .disjElim
    premises := [{ goal := .disj left right }, { discharge := { assumptions := [left] }, goal := goal },
      { discharge := { assumptions := [right] }, goal := goal }] }

/-- Prove the conclusion under a local premise, discharged at this node. -/
def impIntro (premise conclusion : Formula Variable Literal Symbol) : Expansion Variable Literal Symbol Certificate :=
  { rule := .impIntro, premises := [{ discharge := { assumptions := [premise] }, goal := conclusion }] }

/-- Use an implication: prove it and its premise. -/
def impElim (premise goal : Formula Variable Literal Symbol) : Expansion Variable Literal Symbol Certificate :=
  { rule := .impElim, premises := [{ goal := .imp premise goal }, { goal := premise }] }

def falsityElim : Expansion Variable Literal Symbol Certificate :=
  { rule := .falsityElim, premises := [{ goal := .falsity }] }

/-- Open a universal goal with a fresh rigid name, scoped to its premise. The
body is opened by capture-avoiding substitution, renaming an inner binder that
would capture the name, so the name need only be fresh for the free names. -/
def forallIntro [FreshNames Variable] (binder : Variable) (body : Formula Variable Literal Symbol) (eigen : Variable) :
    Expansion Variable Literal Symbol Certificate :=
  { rule := .forallIntro eigen
    premises := [{ discharge := { rigids := [eigen] }, goal := body.instantiate (Substitution.single binder (.var eigen)) }] }

/-- Open an existential goal with a fresh flexible witness depending on the
obligation's rigid names; matching may bind it later. -/
def existsIntro [FreshNames Variable] (binder : Variable) (body : Formula Variable Literal Symbol) (witness : Variable) :
    Expansion Variable Literal Symbol Certificate :=
  { rule := .existsIntro (.var witness), flexibles := [witness]
    premises := [{ goal := body.instantiate (Substitution.single binder (.var witness)) }] }

/-- Use an existential: open it with a fresh rigid witness, available only in
the premise proving the goal. -/
def existsElim [FreshNames Variable] (binder : Variable) (body : Formula Variable Literal Symbol) (eigen : Variable)
    (goal : Formula Variable Literal Symbol) : Expansion Variable Literal Symbol Certificate :=
  { rule := .existsElim eigen
    premises := [{ goal := .existsVar binder body },
      { discharge := { assumptions := [body.instantiate (Substitution.single binder (.var eigen))], rigids := [eigen] }
        goal := goal }] }

/-- The completion contract: derivations of every premise, each in its own
scope, give a derivation of the obligation. Stated for candidates without
answer bindings; `SoundUnder` states it for obligations read through answers. -/
def Sound (hoApplySymbol : Symbol) (kb : LogicalKb Variable Literal Symbol) (naf : NafFailure Variable Literal Symbol)
    (obligation : Obligation Variable Literal Symbol) (expansion : Expansion Variable Literal Symbol Certificate) : Prop :=
  (∀ premise ∈ expansion.premises,
      Derives hoApplySymbol kb (obligation.premise premise).context premise.goal naf) →
    Derives hoApplySymbol kb obligation.context obligation.goal naf

variable {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}
  {scope : Scope Variable Literal Symbol}

theorem truth_sound : (truth (Certificate := Certificate)).Sound hoApplySymbol kb naf ⟨scope, .truth⟩ :=
  fun _ => .truth

theorem assumption_sound {goal : Formula Variable Literal Symbol} (member : goal ∈ scope.assumptions) :
    (assumption (Certificate := Certificate)).Sound hoApplySymbol kb naf ⟨scope, goal⟩ :=
  fun _ => .assumption member

theorem conjIntro_sound {left right : Formula Variable Literal Symbol} :
    (conjIntro (Certificate := Certificate) left right).Sound hoApplySymbol kb naf ⟨scope, .conj left right⟩ :=
  fun proofs => .conjIntro (proofs { goal := left } (by simp [conjIntro]))
    (proofs { goal := right } (by simp [conjIntro]))

theorem disjLeft_sound {left right : Formula Variable Literal Symbol} :
    (disjLeft (Certificate := Certificate) left).Sound hoApplySymbol kb naf ⟨scope, .disj left right⟩ :=
  fun proofs => .disjLeft (proofs { goal := left } (by simp [disjLeft]))

theorem disjRight_sound {left right : Formula Variable Literal Symbol} :
    (disjRight (Certificate := Certificate) right).Sound hoApplySymbol kb naf ⟨scope, .disj left right⟩ :=
  fun proofs => .disjRight (proofs { goal := right } (by simp [disjRight]))

theorem disjElim_sound {left right goal : Formula Variable Literal Symbol} :
    (disjElim (Certificate := Certificate) left right goal).Sound hoApplySymbol kb naf ⟨scope, goal⟩ :=
  fun proofs => .disjElim (proofs { goal := .disj left right } (by simp [disjElim]))
    (proofs { discharge := { assumptions := [left] }, goal := goal } (by simp [disjElim]))
    (proofs { discharge := { assumptions := [right] }, goal := goal } (by simp [disjElim]))

theorem impIntro_sound {premise conclusion : Formula Variable Literal Symbol} :
    (impIntro (Certificate := Certificate) premise conclusion).Sound hoApplySymbol kb naf ⟨scope, .imp premise conclusion⟩ :=
  fun proofs => .impIntro (proofs { discharge := { assumptions := [premise] }, goal := conclusion }
    (by simp [impIntro]))

theorem impElim_sound {premise goal : Formula Variable Literal Symbol} :
    (impElim (Certificate := Certificate) premise goal).Sound hoApplySymbol kb naf ⟨scope, goal⟩ :=
  fun proofs => .impElim (proofs { goal := .imp premise goal } (by simp [impElim]))
    (proofs { goal := premise } (by simp [impElim]))

theorem falsityElim_sound {goal : Formula Variable Literal Symbol} :
    (falsityElim (Certificate := Certificate)).Sound hoApplySymbol kb naf ⟨scope, goal⟩ :=
  fun proofs => .falsityElim (proofs { goal := .falsity } (by simp [falsityElim]))

/-- The freshness `Derives` checks for opening the goal follows from avoiding the
obligation's names, which `Store.commit` enforces for every opened name
(`Store.commit_fresh`). -/
theorem forallIntro_sound [FreshNames Variable] {binder eigen : Variable} {body : Formula Variable Literal Symbol}
    (fresh : eigen ∉ (⟨scope, .forallVar binder body⟩ : Obligation Variable Literal Symbol).names) :
    (forallIntro (Certificate := Certificate) binder body eigen).Sound hoApplySymbol kb naf ⟨scope, .forallVar binder body⟩ := by
  obtain ⟨freshContext, freshGoal, _⟩ := Obligation.fresh_of_not_mem_names fresh
  exact fun proofs => .forallIntro freshContext freshGoal (body.instantiate_substitutes _)
    (proofs { discharge := { rigids := [eigen] }, goal := body.instantiate (Substitution.single binder (.var eigen)) }
      (by simp [forallIntro]))

/-- A flexible witness needs no freshness for the opening itself; the commit
makes it a new name so that it can be bound later. -/
theorem existsIntro_sound [FreshNames Variable] {binder witness : Variable} {body : Formula Variable Literal Symbol} :
    (existsIntro (Certificate := Certificate) binder body witness).Sound hoApplySymbol kb naf ⟨scope, .existsVar binder body⟩ :=
  fun proofs => .existsIntro (body.instantiate_substitutes _)
    (proofs { goal := body.instantiate (Substitution.single binder (.var witness)) } (by simp [existsIntro]))

/-- The opened existential comes from a premise, not from the obligation, so
its freshness conditions are stated directly. -/
theorem existsElim_sound [FreshNames Variable] {binder eigen : Variable} {body goal : Formula Variable Literal Symbol}
    (freshContext : FreshForContext eigen scope.assumptions)
    (freshBody : eigen ∉ (Term.existsVar binder body).freeVars) (freshGoal : eigen ∉ goal.freeVars) :
    (existsElim (Certificate := Certificate) binder body eigen goal).Sound hoApplySymbol kb naf ⟨scope, goal⟩ :=
  fun proofs => .existsElim (proofs { goal := .existsVar binder body } (by simp [existsElim]))
    freshContext freshBody freshGoal (body.instantiate_substitutes _)
    (proofs
      { discharge := { assumptions := [body.instantiate (Substitution.single binder (.var eigen))], rigids := [eigen] }
        goal := goal }
      (by simp [existsElim]))

/-- Use a universal: its premise is the quantifier, and the goal must read as
an instance of its body. A local rule's leading binders are instantiated this
way, with fresh flexible witnesses; its captured names are kept. -/
def forallElim (binder : Variable) (body : Formula Variable Literal Symbol) (witness : Term Variable Literal Symbol) :
    Expansion Variable Literal Symbol Certificate :=
  { rule := .forallElim witness, premises := [{ goal := .forallVar binder body }] }

/-- Use a KB clause: its template names are renamed to fresh flexible names, its
renamed head is matched against the goal (the bindings), and its renamed body is
the one premise, in the parent scope. The rule records the clause and the
renaming; read through the final answers, they give the clause instance. -/
def clause [FreshNames Variable] (head : Atom Variable Literal Symbol) (body : List (Term Variable Literal Symbol))
    (fresh : List (Variable × Variable)) (bindings : List (Variable × Term Variable Literal Symbol) := []) :
    Expansion Variable Literal Symbol Certificate :=
  { rule := .clause (.definite head body) (fresh.map fun pair => (pair.1, .var pair.2))
    flexibles := fresh.map Prod.snd
    bindings := bindings
    premises := [{ goal := (Term.conjunction body).instantiate (Substitution.rename fresh) }] }

theorem forallElim_sound [FreshNames Variable] {binder : Variable} {body : Formula Variable Literal Symbol}
    {witness : Term Variable Literal Symbol} :
    (forallElim (Certificate := Certificate) binder body witness).Sound hoApplySymbol kb naf
      ⟨scope, body.instantiate (Substitution.single binder witness)⟩ :=
  fun proofs => .forallElim (proofs { goal := .forallVar binder body } (by simp [forallElim]))
    (body.instantiate_substitutes _)

/-! ## Reading through committed answers

An obligation's goal and context may mention flexible names; they mean their
reading through the final store. `SoundUnder` is the completion contract for
read obligations: it covers candidates that commit bindings, such as a goal
matched against an assumption or a clause head. Opening a quantifier needs the
opened name fresh for the read obligation, which `Store.commit_fresh_resolved`
provides from the commit. -/

end Expansion

/-- An obligation is derivable when read through a store's answers. -/
def ReadDerives [FreshNames Variable] (hoApplySymbol : Symbol) (kb : LogicalKb Variable Literal Symbol)
    (naf : NafFailure Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (obligation : Obligation Variable Literal Symbol) : Prop :=
  Derives hoApplySymbol kb (obligation.context.map store.resolve) (store.resolve obligation.goal) naf

namespace Expansion

section Reading

variable [FreshNames Variable] {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
  {naf : NafFailure Variable Literal Symbol} {scope : Scope Variable Literal Symbol}
  {store : Store Variable Literal Symbol}

/-- Derivations of every premise read through `store` give a derivation of the
obligation read through it. -/
def SoundUnder (hoApplySymbol : Symbol) (kb : LogicalKb Variable Literal Symbol)
    (naf : NafFailure Variable Literal Symbol) (store : Store Variable Literal Symbol)
    (obligation : Obligation Variable Literal Symbol) (expansion : Expansion Variable Literal Symbol Certificate) :
    Prop :=
  (∀ premise ∈ expansion.premises, ReadDerives hoApplySymbol kb naf store (obligation.premise premise)) →
    ReadDerives hoApplySymbol kb naf store obligation

private theorem read_premise {obligation : Obligation Variable Literal Symbol} {premise : Premise Variable Literal Symbol} :
    ReadDerives hoApplySymbol kb naf store (obligation.premise premise) ↔
      Derives hoApplySymbol kb (premise.discharge.assumptions.map store.resolve ++ obligation.context.map store.resolve)
        (store.resolve premise.goal) naf := by
  simp only [ReadDerives, Obligation.premise_context, List.map_append]; rfl

theorem truth_soundUnder {goal : Formula Variable Literal Symbol} (read : store.resolve goal = .truth) :
    (truth (Certificate := Certificate)).SoundUnder hoApplySymbol kb naf store ⟨scope, goal⟩ := fun _ => by
  simp only [ReadDerives, read]; exact .truth

/-- A goal closed against an assumption: the match makes both read the same. -/
theorem assumption_soundUnder {goal assumption : Formula Variable Literal Symbol}
    {bindings : List (Variable × Term Variable Literal Symbol)} (member : assumption ∈ scope.assumptions)
    (matched : store.resolve goal = store.resolve assumption) :
    (Expansion.assumption (Certificate := Certificate) bindings).SoundUnder hoApplySymbol kb naf store ⟨scope, goal⟩ :=
  fun _ => by
    simp only [ReadDerives, Obligation.context, matched]
    exact .assumption (List.mem_map_of_mem member)

theorem conjIntro_soundUnder {goal left right : Formula Variable Literal Symbol}
    (read : store.resolve goal = store.resolve (.conj left right)) :
    (conjIntro (Certificate := Certificate) left right).SoundUnder hoApplySymbol kb naf store
      ⟨scope, goal⟩ := fun proofs => by
  have first := read_premise.mp (proofs { goal := left } (by simp [conjIntro]))
  have second := read_premise.mp (proofs { goal := right } (by simp [conjIntro]))
  simp only [List.map_nil, List.nil_append] at first second
  simp only [ReadDerives, read, Store.resolve_conj]
  exact .conjIntro first second

theorem disjLeft_soundUnder {goal left right : Formula Variable Literal Symbol}
    (read : store.resolve goal = store.resolve (.disj left right)) :
    (disjLeft (Certificate := Certificate) left).SoundUnder hoApplySymbol kb naf store
      ⟨scope, goal⟩ := fun proofs => by
  have first := read_premise.mp (proofs { goal := left } (by simp [disjLeft]))
  simp only [List.map_nil, List.nil_append] at first
  simp only [ReadDerives, read, Store.resolve_disj]
  exact .disjLeft first

theorem disjRight_soundUnder {goal left right : Formula Variable Literal Symbol}
    (read : store.resolve goal = store.resolve (.disj left right)) :
    (disjRight (Certificate := Certificate) right).SoundUnder hoApplySymbol kb naf store
      ⟨scope, goal⟩ := fun proofs => by
  have second := read_premise.mp (proofs { goal := right } (by simp [disjRight]))
  simp only [List.map_nil, List.nil_append] at second
  simp only [ReadDerives, read, Store.resolve_disj]
  exact .disjRight second

theorem disjElim_soundUnder {left right goal : Formula Variable Literal Symbol} :
    (disjElim (Certificate := Certificate) left right goal).SoundUnder hoApplySymbol kb naf store
      ⟨scope, goal⟩ := fun proofs => by
  have choice := read_premise.mp (proofs { goal := .disj left right } (by simp [disjElim]))
  have first := read_premise.mp
    (proofs { discharge := { assumptions := [left] }, goal := goal } (by simp [disjElim]))
  have second := read_premise.mp
    (proofs { discharge := { assumptions := [right] }, goal := goal } (by simp [disjElim]))
  simp only [Store.resolve_disj, List.map_cons, List.map_nil, List.nil_append, List.singleton_append] at choice first second
  exact .disjElim choice first second

theorem impIntro_soundUnder {goal premise conclusion : Formula Variable Literal Symbol}
    (read : store.resolve goal = store.resolve (.imp premise conclusion)) :
    (impIntro (Certificate := Certificate) premise conclusion).SoundUnder hoApplySymbol kb naf store
      ⟨scope, goal⟩ := fun proofs => by
  have body := read_premise.mp
    (proofs { discharge := { assumptions := [premise] }, goal := conclusion } (by simp [impIntro]))
  simp only [List.map_cons, List.map_nil, List.singleton_append] at body
  simp only [ReadDerives, read, Store.resolve_imp]
  exact .impIntro body

theorem impElim_soundUnder {premise goal : Formula Variable Literal Symbol} :
    (impElim (Certificate := Certificate) premise goal).SoundUnder hoApplySymbol kb naf store ⟨scope, goal⟩ :=
  fun proofs => by
    have rule := read_premise.mp (proofs { goal := .imp premise goal } (by simp [impElim]))
    have argument := read_premise.mp (proofs { goal := premise } (by simp [impElim]))
    simp only [Store.resolve_imp, List.map_nil, List.nil_append] at rule argument
    exact .impElim rule argument

theorem falsityElim_soundUnder {goal : Formula Variable Literal Symbol} :
    (falsityElim (Certificate := Certificate)).SoundUnder hoApplySymbol kb naf store ⟨scope, goal⟩ :=
  fun proofs => by
    have contradiction := read_premise.mp (proofs { goal := .falsity } (by simp [falsityElim]))
    simp only [Store.resolve_falsity, List.map_nil, List.nil_append] at contradiction
    exact .falsityElim contradiction

/-- Opening a universal goal under answers: the read goal is a universal whose
read body opens to the read premise. The eigenvariable must be unbound and
absent from the free names of the read obligation (`Store.commit_fresh_resolved`);
binders are renamed by the opening, so they impose nothing. -/
theorem forallIntro_soundUnder {goal : Formula Variable Literal Symbol} {binder eigen : Variable}
    {body : Formula Variable Literal Symbol} (read : store.resolve goal = store.resolve (.forallVar binder body))
    (unbound : eigen ∉ store.bindings.map Prod.fst)
    (freshGoal : eigen ∉ (store.resolve goal).freeVars)
    (freshContext : FreshForContext eigen (scope.assumptions.map store.resolve)) :
    (forallIntro (Certificate := Certificate) binder body eigen).SoundUnder hoApplySymbol kb naf store
      ⟨scope, goal⟩ := fun proofs => by
  have premise := read_premise.mp
    (proofs { discharge := { rigids := [eigen] }, goal := body.instantiate (Substitution.single binder (.var eigen)) }
      (by simp [forallIntro]))
  simp only [List.map_nil, List.nil_append] at premise
  obtain ⟨renamed, result, quantifier, opening⟩ := store.resolve_forallVar binder body
  have opened := opening (body.instantiate_substitutes (Substitution.single binder (.var eigen)))
  rw [store.resolve_unbound unbound] at opened
  rw [read, quantifier] at freshGoal
  simp only [ReadDerives, Obligation.context, read, quantifier]
  exact .forallIntro freshContext freshGoal opened premise

/-- Introducing an existential goal with a flexible witness: the read goal is an
existential whose read body, instantiated with the witness's answer, is the
read premise. No freshness is needed. -/
theorem existsIntro_soundUnder {goal : Formula Variable Literal Symbol} {binder witness : Variable}
    {body : Formula Variable Literal Symbol} (read : store.resolve goal = store.resolve (.existsVar binder body)) :
    (existsIntro (Certificate := Certificate) binder body witness).SoundUnder hoApplySymbol kb naf store
      ⟨scope, goal⟩ := fun proofs => by
  have premise := read_premise.mp
    (proofs { goal := body.instantiate (Substitution.single binder (.var witness)) } (by simp [existsIntro]))
  simp only [List.map_nil, List.nil_append] at premise
  obtain ⟨renamed, result, quantifier, opening⟩ := store.resolve_existsVar binder body
  have opened := opening (body.instantiate_substitutes (Substitution.single binder (.var witness)))
  simp only [ReadDerives, Obligation.context, read, quantifier]
  exact .existsIntro opened premise

/-- Opening an existential assumption under answers, with the eigenvariable
unbound and absent from the read context, existential, and goal. -/
theorem existsElim_soundUnder {binder eigen : Variable} {body goal : Formula Variable Literal Symbol}
    (unbound : eigen ∉ store.bindings.map Prod.fst)
    (freshContext : FreshForContext eigen (scope.assumptions.map store.resolve))
    (freshBody : eigen ∉ (store.resolve (.existsVar binder body)).freeVars)
    (freshGoal : eigen ∉ (store.resolve goal).freeVars) :
    (existsElim (Certificate := Certificate) binder body eigen goal).SoundUnder hoApplySymbol kb naf store
      ⟨scope, goal⟩ := fun proofs => by
  have existence := read_premise.mp (proofs { goal := .existsVar binder body } (by simp [existsElim]))
  have premise := read_premise.mp
    (proofs
      { discharge := { assumptions := [body.instantiate (Substitution.single binder (.var eigen))], rigids := [eigen] }
        goal := goal }
      (by simp [existsElim]))
  simp only [List.map_cons, List.map_nil, List.nil_append, List.singleton_append, Obligation.context] at existence premise
  obtain ⟨renamed, result, read, opening⟩ := store.resolve_existsVar binder body
  have opened := opening (body.instantiate_substitutes (Substitution.single binder (.var eigen)))
  rw [store.resolve_unbound unbound] at opened
  rw [read] at existence freshBody
  simp only [ReadDerives, Obligation.context]
  exact .existsElim existence freshContext freshBody freshGoal opened premise

/-- Universal elimination under answers: a goal reading as an instance of the
body is derived from the read quantifier with the witness's answer. -/
theorem forallElim_soundUnder {binder : Variable} {body goal : Formula Variable Literal Symbol}
    {witness : Term Variable Literal Symbol}
    (matched : store.resolve goal = store.resolve (body.instantiate (Substitution.single binder witness))) :
    (forallElim (Certificate := Certificate) binder body witness).SoundUnder hoApplySymbol kb naf store
      ⟨scope, goal⟩ := fun proofs => by
  have rule := read_premise.mp (proofs { goal := .forallVar binder body } (by simp [forallElim]))
  simp only [List.map_nil, List.nil_append] at rule
  obtain ⟨renamed, result, read, opening⟩ := store.resolve_forallVar binder body
  rw [read] at rule
  simp only [ReadDerives, Obligation.context, matched]
  exact .forallElim rule (opening (body.instantiate_substitutes _))

/-- A clause use under answers: the renamed clause read through the answers is
one clause instance, and the matched head reads as the goal. -/
theorem clause_soundUnder {head goal : Atom Variable Literal Symbol} {body : List (Term Variable Literal Symbol)}
    {fresh : List (Variable × Variable)} {bindings : List (Variable × Term Variable Literal Symbol)}
    (member : HornClause.definite head body ∈ kb)
    (matched : store.resolve (head.instantiate (Substitution.rename fresh)) = store.resolve goal) :
    (clause (Certificate := Certificate) head body fresh bindings).SoundUnder hoApplySymbol kb naf store
      ⟨scope, goal⟩ := fun proofs => by
  have premise := read_premise.mp
    (proofs { goal := (Term.conjunction body).instantiate (Substitution.rename fresh) } (by simp [clause]))
  simp only [List.map_nil, List.nil_append] at premise
  simp only [ReadDerives, Obligation.context, ← matched]
  exact .clause member (store.resolve_substitutes (head.instantiate_substitutes _))
    (store.resolve_substitutes ((Term.conjunction body).instantiate_substitutes _)) premise

end Reading

end Expansion

end AnthillModKbSpec.Machine
