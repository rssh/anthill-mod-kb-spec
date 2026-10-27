import AnthillModKbSpec.Resolution.Machine.State

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

/-- Open a universal goal with a fresh rigid name, scoped to its premise. -/
def forallIntro (binder : Variable) (body : Formula Variable Literal Symbol) (eigen : Variable) :
    Expansion Variable Literal Symbol Certificate :=
  { rule := .forallIntro eigen, premises := [{ discharge := { rigids := [eigen] }, goal := body.openFree binder eigen }] }

/-- Open an existential goal with a fresh flexible witness depending on the
obligation's rigid names; matching may bind it later. -/
def existsIntro (binder : Variable) (body : Formula Variable Literal Symbol) (witness : Variable) :
    Expansion Variable Literal Symbol Certificate :=
  { rule := .existsIntro (.var witness), flexibles := [witness], premises := [{ goal := body.openFree binder witness }] }

/-- Use an existential: open it with a fresh rigid witness, available only in
the premise proving the goal. -/
def existsElim (binder : Variable) (body : Formula Variable Literal Symbol) (eigen : Variable)
    (goal : Formula Variable Literal Symbol) : Expansion Variable Literal Symbol Certificate :=
  { rule := .existsElim eigen
    premises := [{ goal := .existsVar binder body },
      { discharge := { assumptions := [body.openFree binder eigen], rigids := [eigen] }, goal := goal }] }

/-- The completion contract: derivations of every premise, each in its own
scope, give a derivation of the obligation. Stated for candidates without
answer bindings; reconstruction under committed bindings is S05/S06's. -/
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
theorem forallIntro_sound {binder eigen : Variable} {body : Formula Variable Literal Symbol}
    (fresh : eigen ∉ (⟨scope, .forallVar binder body⟩ : Obligation Variable Literal Symbol).names) :
    (forallIntro (Certificate := Certificate) binder body eigen).Sound hoApplySymbol kb naf ⟨scope, .forallVar binder body⟩ := by
  obtain ⟨freshContext, freshGoal, freshBinders⟩ := Obligation.fresh_of_not_mem_names fresh
  exact fun proofs => .forallIntro freshContext freshGoal
    (body.openFree_substitutes binder eigen (fun member => freshBinders (by simp [Term.binderNames, member])))
    (proofs { discharge := { rigids := [eigen] }, goal := body.openFree binder eigen } (by simp [forallIntro]))

theorem existsIntro_sound {binder witness : Variable} {body : Formula Variable Literal Symbol}
    (fresh : witness ∉ (⟨scope, .existsVar binder body⟩ : Obligation Variable Literal Symbol).names) :
    (existsIntro (Certificate := Certificate) binder body witness).Sound hoApplySymbol kb naf ⟨scope, .existsVar binder body⟩ := by
  obtain ⟨_, _, freshBinders⟩ := Obligation.fresh_of_not_mem_names fresh
  exact fun proofs => .existsIntro
    (body.openFree_substitutes binder witness (fun member => freshBinders (by simp [Term.binderNames, member])))
    (proofs { goal := body.openFree binder witness } (by simp [existsIntro]))

/-- The opened existential comes from a premise, not from the obligation, so
its freshness conditions are stated directly. -/
theorem existsElim_sound {binder eigen : Variable} {body goal : Formula Variable Literal Symbol}
    (freshContext : FreshForContext eigen scope.assumptions)
    (freshBody : eigen ∉ (Term.existsVar binder body).freeVars) (freshGoal : eigen ∉ goal.freeVars)
    (freshBinders : eigen ∉ body.binderNames) :
    (existsElim (Certificate := Certificate) binder body eigen goal).Sound hoApplySymbol kb naf ⟨scope, goal⟩ :=
  fun proofs => .existsElim (proofs { goal := .existsVar binder body } (by simp [existsElim]))
    freshContext freshBody freshGoal (body.openFree_substitutes binder eigen freshBinders)
    (proofs { discharge := { assumptions := [body.openFree binder eigen], rigids := [eigen] }, goal := goal }
      (by simp [existsElim]))

end Expansion

end AnthillModKbSpec.Machine
