import AnthillModKbSpec.Foundation.InductiveDomains

/-! Horn clauses generated from constructor-domain definitions. Guards mention
membership predicates; `Realizes` makes them true, but `Derives` can establish
them only from KB clauses. These clauses supply that derivation path. -/
namespace AnthillModKbSpec.InductiveDomains

open Semantics

/-- A closed syntax representative of a generated constructor value. -/
def Tree.toTerm (tree : Tree Symbol) : Term Variable Literal Symbol :=
  match tree with
  | .node symbol children => .app symbol (children.map Tree.toTerm)

variable {Domain Variable Literal Symbol Value : Type} [DecidableEq Variable] {hoApplySymbol : Symbol}

theorem Tree.eval_toTerm (tree : Tree Symbol) (model : Model Literal Symbol Value hoApplySymbol)
    (environment : Environment Variable Value) : model.eval environment tree.toTerm = denote model tree := by
  refine Tree.rec
    (motive_1 := fun value => model.eval environment value.toTerm = denote model value)
    (motive_2 := fun children => children.map (fun child => model.eval environment child.toTerm) =
      children.map (denote model)) ?_ rfl ?_ tree
  · intro symbol children ih
    simpa only [Tree.toTerm, Model.eval, denote, List.map_map, Function.comp_def] using
      congrArg (model.application symbol) ih
  · intro head tail ihHead ihTail
    simp only [List.map_cons, ihHead, ihTail]

/-- `m_result(c(x_0, ..., x_k)) :- m_field_0(x_0), ..., m_field_k(x_k)`.
Argument i uses clause variable `names i`; the body follows field order. -/
def membershipClause (membershipSymbol : Domain → Symbol) (names : Nat → Variable)
    (rule : Rule Domain Symbol) : HornClause Variable Literal Symbol :=
  .definite (.app (membershipSymbol rule.result)
      [.app rule.symbol (List.ofFn fun i : Fin rule.fields.length => .var (names i))])
    (List.ofFn fun i : Fin rule.fields.length => .app (membershipSymbol rule.fields[i]) [.var (names i)])

/-- One clause per declared rule. Like Sigma itself, this set need not be finite. -/
def membershipKb (sigma : Definitions Domain Symbol) (membershipSymbol : Domain → Symbol)
    (names : Nat → Variable) : LogicalKb Variable Literal Symbol :=
  fun clause => ∃ rule, sigma rule ∧ membershipClause membershipSymbol names rule = clause

omit [DecidableEq Variable] in
theorem mem_membershipKb {sigma : Definitions Domain Symbol} {membershipSymbol : Domain → Symbol}
    {names : Nat → Variable} {rule : Rule Domain Symbol} (declared : sigma rule) :
    membershipClause (Literal := Literal) membershipSymbol names rule ∈
      membershipKb sigma membershipSymbol names :=
  Exists.intro rule ⟨declared, rfl⟩

/-- Each declared rule gets pairwise distinct argument names, so its arguments
can be instantiated independently. Repeated names give valid but weaker clauses. -/
def DistinctNames (sigma : Definitions Domain Symbol) (names : Nat → Variable) : Prop :=
  ∀ rule, sigma rule → ∀ i j : Fin rule.fields.length, names i = names j → i = j

omit [DecidableEq Variable] in
theorem DistinctNames.of_injective {sigma : Definitions Domain Symbol} {names : Nat → Variable}
    (injective : Function.Injective names) : DistinctNames sigma names :=
  fun _ _ _ _ same => Fin.ext (injective same)

/-- Realization makes every generated clause valid. No carrier coverage,
domain disjointness, or name distinctness is needed. -/
theorem membershipClause_valid (model : Model Literal Symbol Value hoApplySymbol)
    {sigma : Definitions Domain Symbol} {membershipSymbol : Domain → Symbol}
    (valid : Realizes model sigma membershipSymbol) {rule : Rule Domain Symbol} (declared : sigma rule)
    (names : Nat → Variable) (environment : Environment Variable Value) :
    model.Satisfies environment
      (membershipClause (Literal := Literal) membershipSymbol names rule).toFormula := by
  simp only [membershipClause, HornClause.toFormula]
  unfold Model.Satisfies
  rw [Model.eval, model.holds_implication]
  intro body
  have fields (i : Fin rule.fields.length) :
      ∃ tree, Member sigma rule.fields[i] tree ∧ denote model tree = environment (names i) := by
    have holds : model.holds (model.application (membershipSymbol rule.fields[i]) [environment (names i)]) := by
      simpa [Model.Satisfies, Model.eval] using
        (model.satisfies_conjunction environment _).mp body _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    exact (valid _ _).mp holds
  obtain ⟨children, spec⟩ := Classical.axiomOfChoice fields
  simp only [Model.eval, List.map_cons, List.map_nil]
  apply (valid rule.result _).mpr
  refine ⟨.node rule.symbol (List.ofFn children), .construct declared children (fun i => (spec i).1), ?_⟩
  simp [denote, Model.eval, List.map_ofFn, Function.comp_def, fun i => (spec i).2]

theorem models_membershipKb (model : Model Literal Symbol Value hoApplySymbol)
    {sigma : Definitions Domain Symbol} {membershipSymbol : Domain → Symbol}
    (valid : Realizes model sigma membershipSymbol) (names : Nat → Variable) :
    model.Models (membershipKb (Literal := Literal) sigma membershipSymbol names) := by
  rintro clause ⟨rule, declared, rfl⟩ environment
  exact membershipClause_valid model valid declared names environment

private noncomputable def childSubstitution (names : Nat → Variable) {arity : Nat}
    (children : Fin arity → Term Variable Literal Symbol) : Substitution Variable Literal Symbol :=
  fun name => open Classical in
    if found : ∃ i : Fin arity, names i = name then children found.choose else .var name

private theorem childSubstitution_name {names : Nat → Variable} {arity : Nat}
    {children : Fin arity → Term Variable Literal Symbol}
    (distinct : ∀ i j : Fin arity, names i = names j → i = j) (i : Fin arity) :
    childSubstitution names children (names i) = children i := by
  unfold childSubstitution
  split
  · rename_i found
    exact congrArg children (distinct _ _ found.choose_spec)
  · rename_i missing
    exact absurd ⟨i, rfl⟩ missing

private theorem substitutesList_ofFn {σ : Substitution Variable Literal Symbol} :
    ∀ {arity : Nat} {before after : Fin arity → Term Variable Literal Symbol},
      (∀ i, Substitutes σ (before i) (after i)) →
        SubstitutesList σ (List.ofFn before) (List.ofFn after)
  | 0, _, _, _ => by simp only [List.ofFn_zero]; exact .nil
  | _ + 1, _, _, each => by
      rw [List.ofFn_succ, List.ofFn_succ]
      exact .cons (each 0) (substitutesList_ofFn (fun i => each i.succ))

/-- Every generated member is derivable using only the generated clauses and
the existing clause rule. No membership axiom or new inference rule is added. -/
theorem Member.derives {sigma : Definitions Domain Symbol} {membershipSymbol : Domain → Symbol}
    {names : Nat → Variable} (distinct : DistinctNames sigma names)
    {kb : LogicalKb Variable Literal Symbol}
    (contains : ∀ rule, sigma rule → membershipClause membershipSymbol names rule ∈ kb)
    {context : ProofContext Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}
    {domain : Domain} {tree : Tree Symbol} (member : Member sigma domain tree) :
    Derives hoApplySymbol kb context (.app (membershipSymbol domain) [tree.toTerm]) naf := by
  induction member with
  | @construct rule declared children members ih =>
      have image := childSubstitution_name
        (children := fun i => ((children i).toTerm : Term Variable Literal Symbol)) (distinct rule declared)
      have argument (i : Fin rule.fields.length) :
          Substitutes (childSubstitution names (fun i => (children i).toTerm))
            (.var (names i)) ((children i).toTerm : Term Variable Literal Symbol) := by
        rw [← image i]; exact .var
      have shape : (Tree.node rule.symbol (List.ofFn children)).toTerm =
          (.app rule.symbol (List.ofFn fun i => (children i).toTerm) : Term Variable Literal Symbol) := by
        simp [Tree.toTerm, List.map_ofFn, Function.comp_def]
      rw [shape]
      exact .clause (contains rule declared)
        (.app (.cons (.app (substitutesList_ofFn argument)) .nil))
        (substitutesList_ofFn (fun i => .app (.cons (argument i) .nil))).conjunction
        (Derives.conjunctionIntro (fun goal member => by
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
          exact ih i))

theorem guard_derives {kb : LogicalKb Variable Literal Symbol}
    {context : ProofContext Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}
    (membershipSymbol : Domain → Symbol) {domains : List Domain} {domain : Domain}
    {subject : Term Variable Literal Symbol} (selected : domain ∈ domains)
    (proof : Derives hoApplySymbol kb context (.app (membershipSymbol domain) [subject]) naf) :
    Derives hoApplySymbol kb context (guard membershipSymbol domains subject) naf := by
  induction domains with
  | nil => cases selected
  | cons head rest ih =>
      simp only [guard, List.map_cons, List.foldr_cons]
      rcases List.mem_cons.mp selected with rfl | selected
      · exact .disjLeft proof
      · exact .disjRight (ih selected)

/-- A generated member of any selected domain derives the D_all-style guard. -/
theorem InUnion.derives {sigma : Definitions Domain Symbol} {membershipSymbol : Domain → Symbol}
    {names : Nat → Variable} (distinct : DistinctNames sigma names)
    {kb : LogicalKb Variable Literal Symbol}
    (contains : ∀ rule, sigma rule → membershipClause membershipSymbol names rule ∈ kb)
    {context : ProofContext Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}
    {domains : List Domain} {tree : Tree Symbol} (member : InUnion sigma domains tree) :
    Derives hoApplySymbol kb context (guard membershipSymbol domains tree.toTerm) naf := by
  obtain ⟨domain, selected, member⟩ := member
  exact guard_derives membershipSymbol selected (member.derives distinct contains)

end AnthillModKbSpec.InductiveDomains
