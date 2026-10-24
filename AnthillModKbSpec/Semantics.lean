import AnthillModKbSpec.Derivation

namespace AnthillModKbSpec.Semantics

/-- An algebra for the shared carrier of data and formulas. Quantifiers range
only over the nonempty value domain. Formula constructors also denote values,
so formulas stored in application arguments retain a compositional meaning.
Logical laws concern truth; equality denotes equality of values. No injectivity
or unique-name assumptions are imposed on symbol interpretations.
NAF has its own operation, constrained here only by truth coherence. -/
structure Model (Literal Symbol : Type) (Value : Type) (hoApplySymbol : Symbol) where
  inhabitant : Value
  literal : Literal → Value
  application : Symbol → List Value → Value
  holds : Value → Prop
  top : Value
  bottom : Value
  conjunction : Value → Value → Value
  disjunction : Value → Value → Value
  implication : Value → Value → Value
  universal : (Value → Value) → Value
  existential : (Value → Value) → Value
  defaultNegation : Value → Value
  equality : Value → Value → Value
  /-- Interpretation of dictionary operation calls. A dictionary extension
  supplies checked lookup/invocation; other models may leave it uninterpreted. -/
  dictionaryCall : Value → List Symbol → Symbol → List Value → Value :=
    fun _ _ _ _ => inhabitant
  holds_top : holds top
  holds_bottom : ¬ holds bottom
  holds_conjunction : ∀ a b, holds (conjunction a b) ↔ holds a ∧ holds b
  holds_disjunction : ∀ a b, holds (disjunction a b) ↔ holds a ∨ holds b
  holds_implication : ∀ a b, holds (implication a b) ↔ (holds a → holds b)
  holds_universal : ∀ f, holds (universal f) ↔ ∀ value, holds (f value)
  holds_existential : ∀ f, holds (existential f) ↔ ∃ value, holds (f value)
  holds_equality : ∀ a b, holds (equality a b) ↔ a = b
  defaultNegation_coherent : ∀ value, holds (defaultNegation value) → ¬ holds value
  holds_hoApply : ∀ predicate args,
    holds (application hoApplySymbol (application predicate [] :: args)) ↔ holds (application predicate args)

variable {Variable Literal Symbol Value : Type} [DecidableEq Variable] {hoApplySymbol : Symbol}

abbrev Environment (Variable Value : Type) := Variable → Value

def update (environment : Environment Variable Value) (name : Variable) (value : Value) :
    Environment Variable Value := fun candidate => if candidate = name then value else environment candidate

variable (model : Model Literal Symbol Value hoApplySymbol)

def Model.eval (model : Model Literal Symbol Value hoApplySymbol) (environment : Environment Variable Value) : Term Variable Literal Symbol → Value
  | .var name => environment name
  | .lit value => model.literal value
  | .app symbol args => model.application symbol (args.map (model.eval environment))
  | .truth => model.top
  | .falsity => model.bottom
  | .conj a b => model.conjunction (model.eval environment a) (model.eval environment b)
  | .disj a b => model.disjunction (model.eval environment a) (model.eval environment b)
  | .imp a b => model.implication (model.eval environment a) (model.eval environment b)
  | .defaultNeg body => model.defaultNegation (model.eval environment body)
  | .forallVar binder body => model.universal (fun value => model.eval (update environment binder value) body)
  | .existsVar binder body => model.existential (fun value => model.eval (update environment binder value) body)
  | .dictionaryCall dictionary path operation args =>
      model.dictionaryCall (model.eval environment dictionary) path operation
        (args.map (model.eval environment))
  | .equal a b => model.equality (model.eval environment a) (model.eval environment b)

def Model.Satisfies (environment : Environment Variable Value) (goal : Term Variable Literal Symbol) : Prop :=
  model.holds (model.eval environment goal)

theorem Model.satisfies_equal (environment : Environment Variable Value)
    (left right : Term Variable Literal Symbol) :
    model.Satisfies environment (.equal left right) ↔
      model.eval environment left = model.eval environment right := by
  simp only [Model.Satisfies, Model.eval]
  exact model.holds_equality _ _

theorem Model.satisfies_equation (environment : Environment Variable Value)
    (left right : Term Variable Literal Symbol) (body : List (Term Variable Literal Symbol)) :
    model.Satisfies environment (HornClause.equation left right body).toFormula ↔
      (model.Satisfies environment (.conjunction body) →
        model.eval environment left = model.eval environment right) := by
  simp only [Model.Satisfies, HornClause.equation, HornClause.toFormula, Model.eval]
  rw [model.holds_implication, model.holds_equality]

private theorem congrTwo {A B C : Type} (f : A → B → C) {a a' : A} {b b' : B}
    (left : a = a') (right : b = b') : f a b = f a' b' := by
  cases left; cases right; rfl

/-- Agreement on free names suffices even when formulas appear as data. -/
theorem Model.eval_congr (term : Term Variable Literal Symbol) :
    ∀ {left right : Environment Variable Value},
      (∀ name ∈ term.freeVars, left name = right name) → model.eval left term = model.eval right term := by
  refine Term.rec
    (motive_1 := fun term => ∀ {left right : Environment Variable Value},
      (∀ name ∈ term.freeVars, left name = right name) → model.eval left term = model.eval right term)
    (motive_2 := fun terms => ∀ {left right : Environment Variable Value},
      (∀ term ∈ terms, ∀ name ∈ term.freeVars, left name = right name) →
        terms.map (model.eval left) = terms.map (model.eval right))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ term
  · intro name left right agree; simp only [Model.eval]; exact agree name (by simp [Term.freeVars])
  · intros; first | rfl | simp only [Model.eval]
  · intro symbol args ih left right agree
    simp only [Model.eval]
    exact congrArg (model.application symbol) (ih (fun term member name occurs => agree name (by simp [Term.freeVars]; exact ⟨term, member, occurs⟩)))
  · intros; first | rfl | simp only [Model.eval]
  · intros; first | rfl | simp only [Model.eval]
  · intro a b ihA ihB left right agree
    simp only [Model.eval]
    exact congrTwo model.conjunction (ihA (fun n h => agree n (by simp [Term.freeVars, h])))
      (ihB (fun n h => agree n (by simp [Term.freeVars, h])))
  · intro a b ihA ihB left right agree
    simp only [Model.eval]
    exact congrTwo model.disjunction (ihA (fun n h => agree n (by simp [Term.freeVars, h])))
      (ihB (fun n h => agree n (by simp [Term.freeVars, h])))
  · intro a b ihA ihB left right agree
    simp only [Model.eval]
    exact congrTwo model.implication (ihA (fun n h => agree n (by simp [Term.freeVars, h])))
      (ihB (fun n h => agree n (by simp [Term.freeVars, h])))
  · intro body ih left right agree; simp only [Model.eval]; exact congrArg model.defaultNegation (ih (by simpa [Term.freeVars] using agree))
  · intro binder body ih left right agree
    simp only [Model.eval]
    apply congrArg model.universal; funext value
    apply ih
    intro name member
    by_cases same : name = binder
    · simp [update, same]
    · simp only [update, ite_eq_right same]
      exact agree name (by simp [Term.freeVars, member, same])
  · intro binder body ih left right agree
    simp only [Model.eval]
    apply congrArg model.existential; funext value
    apply ih
    intro name member
    by_cases same : name = binder
    · simp [update, same]
    · simp only [update, ite_eq_right same]
      exact agree name (by simp [Term.freeVars, member, same])
  · intro dictionary path operation args ihDictionary ihArgs left right agree
    simp only [Term.freeVars, List.mem_append] at agree
    simp only [Model.eval]
    exact congrTwo (fun value values => model.dictionaryCall value path operation values)
      (ihDictionary (fun name member => agree name (Or.inl member)))
      (ihArgs (fun term member name occurs => agree name
        (Or.inr (by simp only [List.mem_flatMap]; exact ⟨term, member, occurs⟩))))
  · intro a b ihA ihB left right agree
    simp only [Model.eval]
    exact congrTwo model.equality (ihA (fun n h => agree n (by simp [Term.freeVars, h])))
      (ihB (fun n h => agree n (by simp [Term.freeVars, h])))
  · intros; first | rfl | simp only [Model.eval]
  · intro head tail ihHead ihTail left right agree
    exact congrTwo List.cons (ihHead (agree head (by simp)))
      (ihTail (fun term member => agree term (by simp [member])))

/-- Capture-avoiding syntactic substitution agrees with environment composition. -/
theorem Model.eval_substitutes {σ : Substitution Variable Literal Symbol}
    {before after : Term Variable Literal Symbol} (proof : Substitutes σ before after) :
    ∀ environment, model.eval environment after = model.eval (fun name => model.eval environment (σ name)) before := by
  refine Substitutes.rec
    (motive_1 := fun σ before after _ => ∀ environment,
      model.eval environment after = model.eval (fun name => model.eval environment (σ name)) before)
    (motive_2 := fun σ before after _ => ∀ environment,
      after.map (model.eval environment) = before.map (model.eval (fun name => model.eval environment (σ name))))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ proof
  · intros; first | rfl | simp only [Model.eval]
  · intros; first | rfl | simp only [Model.eval]
  · intros; first | rfl | simp only [Model.eval]
  · intros; first | rfl | simp only [Model.eval]
  · intro σ before after symbol args ih environment; simp only [Model.eval]; exact congrArg (model.application _) (ih environment)
  · intro σ a a' b b' left right ihLeft ihRight environment
    simp only [Model.eval]
    exact congrTwo model.conjunction (ihLeft environment) (ihRight environment)
  · intro σ a a' b b' left right ihLeft ihRight environment
    simp only [Model.eval]
    exact congrTwo model.disjunction (ihLeft environment) (ihRight environment)
  · intro σ a a' b b' left right ihLeft ihRight environment
    simp only [Model.eval]
    exact congrTwo model.implication (ihLeft environment) (ihRight environment)
  · intro σ before after body ih environment; simp only [Model.eval]; exact congrArg model.defaultNegation (ih environment)
  · intro binder σ renamed body result fresh bodySubst ih environment
    simp only [Model.eval]
    apply congrArg model.universal; funext value
    rw [ih]
    apply model.eval_congr body
    intro name member
    by_cases same : name = binder
    · subst name; simp [Substitution.bind, update, Model.eval]
    · simp only [Substitution.bind, ite_eq_right same, update]
      apply model.eval_congr
      intro other occurs
      have different := fresh name member same
      have ne : other ≠ renamed := fun equal => different (equal ▸ occurs)
      exact ite_eq_right ne
  · intro binder σ renamed body result fresh bodySubst ih environment
    simp only [Model.eval]
    apply congrArg model.existential; funext value
    rw [ih]
    apply model.eval_congr body
    intro name member
    by_cases same : name = binder
    · subst name; simp [Substitution.bind, update, Model.eval]
    · simp only [Substitution.bind, ite_eq_right same, update]
      apply model.eval_congr
      intro other occurs
      have different := fresh name member same
      have ne : other ≠ renamed := fun equal => different (equal ▸ occurs)
      exact ite_eq_right ne
  · intro σ beforeDictionary afterDictionary before after path operation dictionary args
      ihDictionary ihArgs environment
    simp only [Model.eval]
    exact congrTwo (fun value values => model.dictionaryCall value path operation values)
      (ihDictionary environment) (ihArgs environment)
  · intro σ a a' b b' left right ihLeft ihRight environment
    simp only [Model.eval]
    exact congrTwo model.equality (ihLeft environment) (ihRight environment)
  · intros; first | rfl | simp only [Model.eval]
  · intro σ a a' tail tail' head rest ihHead ihRest environment
    exact congrTwo List.cons (ihHead environment) (ihRest environment)

/-- Universal closure of every clause in the set, including goal clauses. -/
def Model.Models (kb : LogicalKb Variable Literal Symbol) : Prop :=
  ∀ clause ∈ kb, ∀ environment : Environment Variable Value,
    model.Satisfies environment clause.toFormula

def Model.ContextHolds (environment : Environment Variable Value)
    (context : ProofContext Variable Literal Symbol) : Prop :=
  ∀ assumption ∈ context, model.Satisfies environment assumption

/-- The semantic obligation on a failure provider. It is additional to merely
being a Horn-clause model. No completeness of search is assumed by soundness. -/
def Model.FailureAdequate (kb : LogicalKb Variable Literal Symbol)
    (naf : NafFailure Variable Literal Symbol) : Prop :=
  ∀ context goal, goal.freeVars = [] → naf hoApplySymbol kb context goal →
    ∀ environment, model.ContextHolds environment context → model.Satisfies environment (.defaultNeg goal)

theorem Model.disabled_adequate (kb : LogicalKb Variable Literal Symbol) :
    model.FailureAdequate kb NafFailure.disabled := by
  intro context goal closed evidence
  exact False.elim evidence

theorem Model.eval_single {binder : Variable} {witness before after : Term Variable Literal Symbol}
    (proof : Substitutes (Substitution.single binder witness) before after)
    (environment : Environment Variable Value) :
    model.eval environment after = model.eval (update environment binder (model.eval environment witness)) before := by
  rw [model.eval_substitutes proof]
  apply model.eval_congr
  intro name member
  by_cases same : name = binder <;> simp [Substitution.single, Substitution.bind, update, same, Model.eval]

theorem Model.eval_fresh (term : Term Variable Literal Symbol) (environment : Environment Variable Value)
    {name : Variable} (fresh : name ∉ term.freeVars) (value : Value) :
    model.eval (update environment name value) term = model.eval environment term := by
  apply model.eval_congr
  intro candidate member
  have different : candidate ≠ name := fun equal => fresh (equal ▸ member)
  exact ite_eq_right different

theorem Model.context_fresh (environment : Environment Variable Value)
    {context : ProofContext Variable Literal Symbol} {name : Variable}
    (fresh : FreshForContext name context) (value : Value)
    (valid : model.ContextHolds environment context) :
    model.ContextHolds (update environment name value) context := by
  intro assumption member
  unfold Model.Satisfies
  rw [model.eval_fresh assumption environment (fresh assumption member) value]
  exact valid assumption member

theorem Model.eval_open_fresh {binder eigen : Variable} {body opened : Term Variable Literal Symbol}
    (fresh : eigen ∉ (Term.forallVar binder body).freeVars)
    (opening : Substitutes (Substitution.single binder (.var eigen)) body opened)
    (environment : Environment Variable Value) (value : Value) :
    model.eval (update environment eigen value) opened = model.eval (update environment binder value) body := by
  rw [model.eval_single opening]
  apply model.eval_congr
  intro name member
  by_cases same : name = binder
  · simp [update, Model.eval, same]
  · have different : name ≠ eigen := by
      intro equal; subst name
      exact fresh (by simp [Term.freeVars, member, same])
    simp [update, same, different]

/-- Every declarative derivation preserves truth in every model of its KB
whose failure evidence is adequate. This includes all raw goal forms. -/
theorem Model.sound {kb : LogicalKb Variable Literal Symbol}
    {context : ProofContext Variable Literal Symbol} {goal : Term Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol}
    (validKb : model.Models kb) (adequate : model.FailureAdequate kb naf)
    (proof : Derives hoApplySymbol kb context goal naf) :
    ∀ environment, model.ContextHolds environment context → model.Satisfies environment goal := by
  induction proof with
  | assumption member => intro environment valid; exact valid _ member
  | truth => intro environment valid; simp only [Model.Satisfies, Model.eval] at *; exact model.holds_top
  | conjIntro left right ihLeft ihRight =>
      intro environment valid
      simp only [Model.Satisfies, Model.eval] at *
      exact (model.holds_conjunction _ _).mpr ⟨ihLeft adequate environment valid, ihRight adequate environment valid⟩
  | conjLeft proof ih => intro environment valid; simp only [Model.Satisfies, Model.eval] at *; exact ((model.holds_conjunction _ _).mp (ih adequate environment valid)).1
  | conjRight proof ih => intro environment valid; simp only [Model.Satisfies, Model.eval] at *; exact ((model.holds_conjunction _ _).mp (ih adequate environment valid)).2
  | disjLeft proof ih => intro environment valid; simp only [Model.Satisfies, Model.eval] at *; exact (model.holds_disjunction _ _).mpr (Or.inl (ih adequate environment valid))
  | disjRight proof ih => intro environment valid; simp only [Model.Satisfies, Model.eval] at *; exact (model.holds_disjunction _ _).mpr (Or.inr (ih adequate environment valid))
  | disjElim choice left right ihChoice ihLeft ihRight =>
      intro environment valid
      simp only [Model.Satisfies, Model.eval] at *
      rcases (model.holds_disjunction _ _).mp (ihChoice adequate environment valid) with yes | yes
      · exact ihLeft adequate environment (by intro assumption member; simp at member; rcases member with rfl | member; exact yes; exact valid _ member)
      · exact ihRight adequate environment (by intro assumption member; simp at member; rcases member with rfl | member; exact yes; exact valid _ member)
  | impIntro proof ih =>
      intro environment valid
      simp only [Model.Satisfies, Model.eval] at *
      apply (model.holds_implication _ _).mpr
      intro premise
      exact ih adequate environment (by intro assumption member; simp at member; rcases member with rfl | member; exact premise; exact valid _ member)
  | impElim rule argument ihRule ihArgument =>
      intro environment valid
      simp only [Model.Satisfies, Model.eval] at *
      exact (model.holds_implication _ _).mp (ihRule adequate environment valid) (ihArgument adequate environment valid)
  | falsityElim proof ih => intro environment valid; simp only [Model.Satisfies, Model.eval] at *; exact False.elim (model.holds_bottom (ih adequate environment valid))
  | forallIntro freshContext freshGoal opening proof ih =>
      intro environment valid
      simp only [Model.Satisfies, Model.eval] at *
      apply (model.holds_universal _).mpr
      intro value
      have result := ih adequate (update environment _ value) (model.context_fresh environment freshContext value valid)
      rw [model.eval_open_fresh freshGoal opening environment value] at result
      exact result
  | forallElim proof instantiation ih =>
      intro environment valid
      simp only [Model.Satisfies, Model.eval] at *
      rw [model.eval_single instantiation]
      exact (model.holds_universal _).mp (ih adequate environment valid) _
  | @existsIntro binder witness body instantiated context naf instantiation proof ih =>
      intro environment valid
      simp only [Model.Satisfies, Model.eval] at *
      apply (model.holds_existential _).mpr
      refine ⟨model.eval environment witness, ?_⟩
      have result := ih adequate environment valid
      rw [model.eval_single instantiation] at result
      exact result
  | @existsElim context binder body naf eigen opened goal existence freshContext freshBody freshGoal opening proof ihExistence ihProof =>
      intro environment valid
      simp only [Model.Satisfies, Model.eval] at *
      rcases (model.holds_existential _).mp (ihExistence adequate environment valid) with ⟨value, witness⟩
      have openedTrue : model.Satisfies (update environment eigen value) opened := by
        dsimp only [Model.Satisfies]
        rw [model.eval_open_fresh (by simpa [Term.freeVars] using freshBody) opening]
        exact witness
      have result := ihProof adequate (update environment _ value) (by
        intro assumption member; simp at member
        rcases member with rfl | member
        · exact openedTrue
        · exact model.context_fresh environment freshContext value valid _ member)
      rw [model.eval_fresh _ environment freshGoal value] at result
      exact result
  | @clause head body σ instantiatedHead instantiatedBody context naf member headInstance bodyInstance proof ih =>
      intro environment valid
      simp only [Model.Satisfies] at *
      have rule := validKb _ member (fun name => model.eval environment (σ name))
      have bodyTrue := ih adequate environment valid
      dsimp only [Model.Satisfies] at rule bodyTrue ⊢
      simp only [HornClause.toFormula, Model.eval] at rule
      rw [model.eval_substitutes headInstance]
      rw [model.eval_substitutes bodyInstance] at bodyTrue
      exact (model.holds_implication _ _).mp rule bodyTrue
  | @goalClause body σ instantiatedBody context naf member bodyInstance proof ih =>
      intro environment valid
      simp only [Model.Satisfies, Model.eval] at *
      have rule := validKb _ member (fun name => model.eval environment (σ name))
      have bodyTrue := ih adequate environment valid
      dsimp only [Model.Satisfies] at rule bodyTrue ⊢
      simp only [HornClause.toFormula, Model.eval] at rule
      rw [model.eval_substitutes bodyInstance] at bodyTrue
      exact (model.holds_implication _ _).mp rule bodyTrue
  | defaultNegIntro closed evidence =>
      intro environment valid
      exact adequate _ _ closed evidence environment valid
  | hoApplyIntro proof ih =>
      intro environment valid
      simp only [Model.Satisfies, Term.hoApply, Model.eval, List.map_cons, List.map_nil] at *
      exact (model.holds_hoApply _ _).mpr (ih adequate environment valid)
  | hoApplyElim proof ih =>
      intro environment valid
      simp only [Model.Satisfies, Term.hoApply, Model.eval, List.map_cons, List.map_nil] at *
      exact (model.holds_hoApply _ _).mp (ih adequate environment valid)
  | equalRefl =>
      intro environment valid
      exact (model.satisfies_equal environment _ _).mpr rfl
  | equalSymm proof ih =>
      intro environment valid
      exact (model.satisfies_equal environment _ _).mpr
        ((model.satisfies_equal environment _ _).mp (ih adequate environment valid)).symm
  | equalTrans left right ihLeft ihRight =>
      intro environment valid
      exact (model.satisfies_equal environment _ _).mpr
        (((model.satisfies_equal environment _ _).mp (ihLeft adequate environment valid)).trans
          ((model.satisfies_equal environment _ _).mp (ihRight adequate environment valid)))
  | equalSubst equality leftInstance rightInstance proof ihEquality ihProof =>
      intro environment valid
      have equalValues := (model.satisfies_equal environment _ _).mp (ihEquality adequate environment valid)
      have result := ihProof adequate environment valid
      dsimp only [Model.Satisfies] at result ⊢
      rw [model.eval_single rightInstance, ← equalValues, ← model.eval_single leftInstance]
      exact result

/-- Positive soundness has no premise about a failure provider. -/
theorem Model.positive_sound {kb : LogicalKb Variable Literal Symbol}
    {context : ProofContext Variable Literal Symbol} {goal : Term Variable Literal Symbol}
    (validKb : model.Models kb) (proof : Derives hoApplySymbol kb context goal) :
    ∀ environment, model.ContextHolds environment context → model.Satisfies environment goal :=
  model.sound validKb (model.disabled_adequate kb) proof

/-- Semantic coherence also rules out deriving a goal and its default
negation together whenever the local context is satisfiable in the model. -/
theorem Model.not_both {kb : LogicalKb Variable Literal Symbol}
    {context : ProofContext Variable Literal Symbol} {goal : Term Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol}
    (validKb : model.Models kb) (adequate : model.FailureAdequate kb naf)
    (environment : Environment Variable Value) (validContext : model.ContextHolds environment context)
    (positive : Derives hoApplySymbol kb context goal naf) :
    ¬ Derives hoApplySymbol kb context (.defaultNeg goal) naf := by
  intro negative
  have yes := model.sound validKb adequate positive environment validContext
  have no := model.sound validKb adequate negative environment validContext
  apply model.defaultNegation_coherent (model.eval environment goal) _ yes
  simpa only [Model.Satisfies, Model.eval] using no

/-- A model of the KB with adequate NAF evidence rules out a closed proof of
falsity. Model existence is essential: arbitrary KBs may contain contradictions. -/
theorem Model.consistent {kb : LogicalKb Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}
    (validKb : model.Models kb) (adequate : model.FailureAdequate kb naf) :
    ¬ Derives hoApplySymbol kb [] .falsity naf := by
  intro proof
  have impossible := model.sound validKb adequate proof (fun _ => model.inhabitant)
    (by intro assumption member; cases member)
  exact model.holds_bottom (by simpa only [Model.Satisfies, Model.eval] using impossible)

theorem Model.positive_consistent {kb : LogicalKb Variable Literal Symbol} (validKb : model.Models kb) :
    ¬ Derives hoApplySymbol kb [] .falsity :=
  model.consistent validKb (model.disabled_adequate kb)

end AnthillModKbSpec.Semantics
