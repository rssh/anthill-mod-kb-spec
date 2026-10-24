import AnthillModKbSpec.CounterexampleSearch

namespace AnthillModKbSpec.Archive.InductionGoals

open Semantics InductiveDomains

variable {Domain Variable Literal Symbol Value : Type} [DecidableEq Variable]
variable {hoApplySymbol : Symbol}

/-- A declared induction scheme must cover every constructor of the family.
The finite constructor catalog makes its generated obligations enumerable. -/
structure Scheme (family : FiniteFamily Domain Symbol) where
  constructors : List (Rule Domain Symbol)
  exact : ∀ rule, family.definitions rule ↔ rule ∈ constructors

/-- Operational goals distinguish an induction certificate from an atomic
predicate. Predicate values still use the ordinary untyped term syntax. -/
inductive Goal (Domain Variable Literal Symbol : Type) where
  | formula (term : Term Variable Literal Symbol)
  | inductiveProof (predicates : Domain → Term Variable Literal Symbol)

def Goal.Holds (model : Model Literal Symbol Value hoApplySymbol)
    (family : FiniteFamily Domain Symbol) (environment : Environment Variable Value) :
    Goal Domain Variable Literal Symbol → Prop
  | .formula term => model.Satisfies environment term
  | .inductiveProof predicates => ∀ domain tree, Member family.definitions domain tree →
      model.holds (model.application hoApplySymbol [model.eval environment (predicates domain), denote model tree])

def freshList [FreshNames Variable] : Nat → List Variable → List Variable
  | 0, _ => []
  | n + 1, avoid => let name := FreshNames.fresh avoid
    name :: freshList n (name :: avoid)

omit [DecidableEq Variable] in
@[simp] theorem freshList_length [FreshNames Variable] (n : Nat) (avoid : List Variable) :
    (freshList n avoid).length = n := by
  induction n generalizing avoid <;> simp_all [freshList]

omit [DecidableEq Variable] in
theorem freshList_fresh [FreshNames Variable] (n : Nat) (avoid : List Variable) :
    ∀ name ∈ freshList n avoid, name ∉ avoid := by
  induction n generalizing avoid with
  | zero => simp [freshList]
  | succ n ih =>
      intro name member
      simp only [freshList, List.mem_cons] at member
      rcases member with rfl | member
      · exact FreshNames.fresh_not_mem avoid
      · exact fun occurs => ih _ _ member (by simp [occurs])

omit [DecidableEq Variable] in
theorem freshList_nodup [FreshNames Variable] (n : Nat) (avoid : List Variable) :
    (freshList n avoid).Nodup := by
  induction n generalizing avoid with
  | zero => simp [freshList]
  | succ n ih =>
      apply List.nodup_cons.mpr
      exact ⟨fun member => freshList_fresh n _ _ member (by simp), ih _⟩

structure Arguments (predicates : Domain → Term Variable Literal Symbol) (rule : Rule Domain Symbol) where
  names : Fin rule.fields.length → Variable
  distinct : Function.Injective names
  fresh : ∀ domain i, names i ∉ (predicates domain).freeVars

/-- Canonical fresh binders for a constructor's fields. -/
def arguments [FreshNames Variable] (family : FiniteFamily Domain Symbol)
    (predicates : Domain → Term Variable Literal Symbol) (rule : Rule Domain Symbol) : Arguments predicates rule := by
  let avoid := family.domains.flatMap (fun domain => (predicates domain).freeVars)
  let names := freshList rule.fields.length avoid
  have length : names.length = rule.fields.length := freshList_length _ _
  refine ⟨fun i => names[i.val]'(by omega), ?_, ?_⟩
  · intro i j same
    apply Fin.ext
    exact (freshList_nodup rule.fields.length avoid).getElem_inj.mp same
  · intro domain i member
    have selected : names[i.val]'(by omega) ∈ names := List.getElem_mem (by omega)
    apply freshList_fresh rule.fields.length avoid _ selected
    exact List.mem_flatMap.mpr ⟨domain, family.complete domain, member⟩

def premises (membershipSymbol : Domain → Symbol) (predicates : Domain → Term Variable Literal Symbol)
    (rule : Rule Domain Symbol) (names : Fin rule.fields.length → Variable) : Term Variable Literal Symbol :=
  .conjunction (List.ofFn (fun i => .conj (.app (membershipSymbol rule.fields[i]) [.var (names i)])
    (.hoApply hoApplySymbol (predicates rule.fields[i]) [.var (names i)])))

def conclusion (predicates : Domain → Term Variable Literal Symbol) (rule : Rule Domain Symbol)
    (names : Fin rule.fields.length → Variable) : Term Variable Literal Symbol :=
  .hoApply hoApplySymbol (predicates rule.result) [.app rule.symbol (List.ofFn (fun i => .var (names i)))]

/-- Constructor obligations are actual scoped formulas searched by the logic:
forall fields. (domain memberships and recursive IHs) -> P(constructor fields).
One invariant per domain supports mutually recursive definitions. -/
def constructorGoal [FreshNames Variable] (family : FiniteFamily Domain Symbol)
    (membershipSymbol : Domain → Symbol) (predicates : Domain → Term Variable Literal Symbol)
    (rule : Rule Domain Symbol) : Term Variable Literal Symbol :=
  let args := arguments family predicates rule
  (List.ofFn args.names).foldr .forallVar
    (.imp (premises (hoApplySymbol := hoApplySymbol) membershipSymbol predicates rule args.names)
      (conclusion (hoApplySymbol := hoApplySymbol) predicates rule args.names))

/-- The finite subgoal list produced when an InductiveProof goal is selected. -/
def Scheme.obligations [FreshNames Variable] {family : FiniteFamily Domain Symbol}
    (scheme : Scheme family) (membershipSymbol : Domain → Symbol)
    (predicates : Domain → Term Variable Literal Symbol) : List (Goal Domain Variable Literal Symbol) :=
  scheme.constructors.map (fun rule => .formula
    (constructorGoal (hoApplySymbol := hoApplySymbol) family membershipSymbol predicates rule))

private theorem conjunction_true (model : Model Literal Symbol Value hoApplySymbol)
    (environment : Environment Variable Value) (terms : List (Term Variable Literal Symbol))
    (all : ∀ term ∈ terms, model.Satisfies environment term) : model.Satisfies environment (.conjunction terms) := by
  induction terms with
  | nil => simpa only [Term.conjunction, List.foldr_nil, Model.Satisfies, Model.eval] using model.holds_top
  | cons head tail ih =>
      simp only [Term.conjunction, List.foldr_cons, Model.Satisfies, Model.eval, model.holds_conjunction]
      exact ⟨all _ (by simp), ih (by intro term member; exact all _ (by simp [member]))⟩

private theorem forallList_elim (model : Model Literal Symbol Value hoApplySymbol)
    (names : List Variable) (body : Term Variable Literal Symbol)
    (environment target : Environment Variable Value)
    (proof : model.Satisfies environment (names.foldr .forallVar body))
    (agree : ∀ name, name ∉ names → target name = environment name) : model.Satisfies target body := by
  induction names generalizing environment with
  | nil =>
      have same : target = environment := funext (fun name => agree name (by simp))
      simpa only [same, List.foldr_nil] using proof
  | cons name names ih =>
      simp only [List.foldr_cons, Model.Satisfies, Model.eval, model.holds_universal] at proof
      apply ih (update environment name (target name)) (proof (target name))
      intro candidate absent
      by_cases same : candidate = name
      · simp [update, same]
      · simp [update, same, agree candidate (by simp [absent, same])]

private noncomputable def assign (names : Fin n → Variable) (values : Fin n → Value)
    (environment : Environment Variable Value) : Environment Variable Value := fun name =>
  if found : ∃ i, names i = name then values (Classical.choose found) else environment name

private theorem assign_name (names : Fin n → Variable) (distinct : Function.Injective names)
    (values : Fin n → Value) (environment : Environment Variable Value) (i : Fin n) :
    assign names values environment (names i) = values i := by
  unfold assign
  split
  · rename_i found
    exact congrArg values (distinct (Classical.choose_spec found))
  · rename_i missing
    exact False.elim (missing ⟨i, rfl⟩)

private theorem assign_other (names : Fin n → Variable) (values : Fin n → Value)
    (environment : Environment Variable Value) (absent : ∀ i, names i ≠ name) :
    assign names values environment name = environment name := by
  simp only [assign]
  split
  · rename_i found
    obtain ⟨i, same⟩ := found
    exact False.elim (absent i same)
  · rfl

/-- Soundness of a generated constructor obligation at arbitrary generated
children. The proof goal itself may have been solved by clause search or NAF. -/
theorem constructorGoal_sound [FreshNames Variable]
    (family : FiniteFamily Domain Symbol) (model : Model Literal Symbol Value hoApplySymbol)
    (realizes : Realizes model family.definitions membershipSymbol)
    (predicates : Domain → Term Variable Literal Symbol) (rule : Rule Domain Symbol)
    (environment : Environment Variable Value)
    (proof : model.Satisfies environment (constructorGoal (hoApplySymbol := hoApplySymbol) family membershipSymbol predicates rule))
    (children : Fin rule.fields.length → Tree Symbol)
    (members : ∀ i, Member family.definitions rule.fields[i] (children i))
    (ih : ∀ i, model.holds (model.application hoApplySymbol
      [model.eval environment (predicates rule.fields[i]), denote model (children i)])) :
    model.holds (model.application hoApplySymbol [model.eval environment (predicates rule.result),
      denote model (.node rule.symbol (List.ofFn children))]) := by
  let args := arguments family predicates rule
  let values := fun i => denote model (children i)
  let target := assign args.names values environment
  have atName (i) : target (args.names i) = denote model (children i) := assign_name _ args.distinct _ _ i
  have predicateSame (domain) : model.eval target (predicates domain) = model.eval environment (predicates domain) := by
    apply model.eval_congr
    intro name occurs
    exact assign_other _ _ _ (fun i same => args.fresh domain i (same.symm ▸ occurs))
  have opened := forallList_elim model (List.ofFn args.names) _ environment target proof (by
    intro name absent
    exact assign_other _ _ _ (fun i same => absent (List.mem_ofFn.mpr ⟨i, same⟩)))
  simp only [Model.Satisfies, Model.eval, model.holds_implication] at opened
  have premiseTrue : model.Satisfies target
      (premises (hoApplySymbol := hoApplySymbol) membershipSymbol predicates rule args.names) := by
    apply conjunction_true
    intro term member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
    simp only [Model.Satisfies, Model.eval, model.holds_conjunction, Term.hoApply,
      List.map_cons, List.map_nil, atName, predicateSame]
    exact ⟨(realizes _ _).mpr ⟨children i, members i, rfl⟩, ih i⟩
  have result := opened premiseTrue
  simp only [conclusion, Term.hoApply, Model.eval, List.map_cons, List.map_nil,
    List.map_ofFn, Function.comp_def, Model.eval] at result
  change model.holds (model.application hoApplySymbol [model.eval target (predicates rule.result),
    model.application rule.symbol (List.ofFn (fun i => target (args.names i)))]) at result
  simpa only [atName, predicateSame, denote, List.map_ofFn, Function.comp_def] using result

end AnthillModKbSpec.Archive.InductionGoals
