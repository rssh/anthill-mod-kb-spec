import AnthillModKbSpec.CompletedGround

namespace AnthillModKbSpec.InductiveDomains

/-- Canonical constructor values. Domain membership is defined separately, so
one value may belong to several domains. -/
inductive Tree (Symbol : Type) where
  | node (symbol : Symbol) (children : List (Tree Symbol))
  deriving Repr

/-- A constructor with a finite ordered list of recursive argument domains.
A set of these rules can define several mutually recursive domains. -/
structure Rule (Domain Symbol : Type) where
  result : Domain
  symbol : Symbol
  fields : List Domain

/-- The set Sigma, represented by its membership predicate. -/
abbrev Definitions (Domain Symbol : Type) := Rule Domain Symbol → Prop

/-- Least constructor-generated membership: only finite derivations using
rules in Sigma establish membership. Constructor closure alone is not used as
a substitute for this inductive definition. -/
inductive Member (sigma : Definitions Domain Symbol) : Domain → Tree Symbol → Prop where
  | construct {rule : Rule Domain Symbol} (declared : sigma rule)
      (children : Fin rule.fields.length → Tree Symbol)
      (members : ∀ i, Member sigma rule.fields[i] (children i)) :
      Member sigma rule.result (.node rule.symbol (List.ofFn children))

variable {Domain Symbol : Type} {sigma : Definitions Domain Symbol}

/-- An explicit family of induction cases, including all mutually recursive
argument domains. A property is not silently assumed for the children. -/
structure Induction (sigma : Definitions Domain Symbol) (invariant : Domain → Tree Symbol → Prop) : Prop where
  step : ∀ rule, sigma rule → ∀ children : Fin rule.fields.length → Tree Symbol,
    (∀ i, Member sigma rule.fields[i] (children i)) →
    (∀ i, invariant rule.fields[i] (children i)) →
    invariant rule.result (.node rule.symbol (List.ofFn children))

theorem Member.induct {invariant : Domain → Tree Symbol → Prop}
    (cases : Induction sigma invariant) (member : Member sigma domain tree) : invariant domain tree := by
  induction member with
  | construct declared children members ih => exact cases.step _ declared children members ih

/-- A finite union of domains, with no requirement of disjointness. -/
def InUnion (sigma : Definitions Domain Symbol) (domains : List Domain) (tree : Tree Symbol) : Prop :=
  ∃ domain ∈ domains, Member sigma domain tree

/-- The mathematical meaning of a guarded universal, parameterized by the
meaning of its property. Syntax and compositional-model connections are below. -/
def Holds (sigma : Definitions Domain Symbol) (domains : List Domain) (property : Tree Symbol → Prop) : Prop :=
  ∀ tree, InUnion sigma domains tree → property tree

/-- A refutation must exhibit actual domain membership and semantic falsity of
the property. Hypothetical proof-search failure supplies neither premise. -/
inductive Refutes (sigma : Definitions Domain Symbol) (domains : List Domain)
    (property : Tree Symbol → Prop) : Prop where
  | witness (selected : domain ∈ domains) (member : Member sigma domain tree)
      (falseProperty : ¬ property tree) : Refutes sigma domains property

theorem refutes_not_holds (refuted : Refutes sigma domains property) : ¬ Holds sigma domains property := by
  intro universal
  cases refuted with
  | witness selected member falseProperty => exact falseProperty (universal _ ⟨_, selected, member⟩)

theorem holds_by_induction {invariant : Domain → Tree Symbol → Prop}
    (cases : Induction sigma invariant)
    (roots : ∀ domain ∈ domains, ∀ tree, invariant domain tree → property tree) :
    Holds sigma domains property := by
  intro tree ⟨domain, selected, member⟩
  exact roots domain selected tree (member.induct cases)

/-- Enumeration can prove universality only with soundness and exhaustive
coverage of the least domain. Infinite domains need not have such a cover. -/
structure Cover (sigma : Definitions Domain Symbol) (domain : Domain) where
  values : List (Tree Symbol)
  sound : ∀ tree ∈ values, Member sigma domain tree
  complete : ∀ tree, Member sigma domain tree → tree ∈ values

theorem holds_by_covers (covers : ∀ domain ∈ domains, Cover sigma domain)
    (checked : ∀ domain selected, ∀ tree ∈ (covers domain selected).values, property tree) :
    Holds sigma domains property := by
  intro tree ⟨domain, selected, member⟩
  exact checked domain selected tree ((covers domain selected).complete tree member)

@[simp] theorem holds_empty (property : Tree Symbol → Prop) : Holds sigma [] property := by
  intro tree ⟨domain, selected, _⟩; cases selected

/-- A guard is explicitly a disjunction of unary membership predicates. -/
def guard (membershipSymbol : Domain → Symbol) (domains : List Domain)
    (subject : Term Variable Literal Symbol) : Term Variable Literal Symbol :=
  (domains.map (fun domain => Term.app (membershipSymbol domain) [subject])).foldr .disj .falsity

/-- The executable quantifier shape is recorded separately from raw Term. -/
structure Universal (Domain Variable Literal Symbol : Type) where
  domains : List Domain
  binder : Variable
  body : Term Variable Literal Symbol

def Universal.toTerm (goal : Universal Domain Variable Literal Symbol) (membershipSymbol : Domain → Symbol) :
    Term Variable Literal Symbol :=
  .forallVar goal.binder (.imp (guard membershipSymbol goal.domains (.var goal.binder)) goal.body)

/-- A finite catalog of all domain definitions. Finiteness concerns domain
identifiers, not their generated inhabitants or the number of constructor rules.
The catalog and its definitions are entirely independent of a type system. -/
structure FiniteFamily (Domain Symbol : Type) where
  definitions : Definitions Domain Symbol
  domains : List Domain
  complete : ∀ domain, domain ∈ domains

/-- The data universe generated by the whole family. Empty and overlapping
domains are allowed; arbitrary constructor trees need not belong to it. -/
def FiniteFamily.Generated (family : FiniteFamily Domain Symbol) :=
  {tree : Tree Symbol // ∃ domain, Member family.definitions domain tree}

theorem FiniteFamily.inUnion_iff (family : FiniteFamily Domain Symbol) (tree : Tree Symbol) :
    InUnion family.definitions family.domains tree ↔ ∃ domain, Member family.definitions domain tree := by
  constructor
  · rintro ⟨domain, _, member⟩; exact ⟨domain, member⟩
  · rintro ⟨domain, member⟩; exact ⟨domain, family.complete domain, member⟩

theorem FiniteFamily.holds_iff (family : FiniteFamily Domain Symbol) (property : Tree Symbol → Prop) :
    Holds family.definitions family.domains property ↔ ∀ value : family.Generated, property value.val := by
  constructor
  · intro proof value; exact proof value.val ((family.inUnion_iff _).mpr value.property)
  · intro proof tree member; exact proof ⟨tree, (family.inUnion_iff _).mp member⟩

/-- Surface forall over all generated data lowers to the disjunction of every
domain predicate. Raw Term.forallVar retains its original carrier semantics. -/
def FiniteFamily.forallAll (family : FiniteFamily Domain Symbol) (binder : Variable)
    (body : Term Variable Literal Symbol) : Universal Domain Variable Literal Symbol :=
  ⟨family.domains, binder, body⟩

open Semantics

variable {Variable Literal Value : Type} [DecidableEq Variable] {hoApplySymbol : Symbol}

/-- Interpret canonical constructor trees compositionally in the existing model. -/
def denote (model : Model Literal Symbol Value hoApplySymbol) : Tree Symbol → Value
  | .node symbol children => model.application symbol (children.map (denote model))

/-- Exact domain interpretation: membership holds precisely on denotations of
constructor-generated trees. This rules out extra, unsupported domain members.
A model may identify denotations; constructor trees themselves remain free. -/
def Realizes (model : Model Literal Symbol Value hoApplySymbol) (sigma : Definitions Domain Symbol)
    (membershipSymbol : Domain → Symbol) : Prop :=
  ∀ domain value, model.holds (model.application (membershipSymbol domain) [value]) ↔
    ∃ tree, Member sigma domain tree ∧ denote model tree = value

/-- An additional condition needed only when identifying data quantification
with unrestricted quantification over the model's entire semantic carrier. -/
def FiniteFamily.Covers (family : FiniteFamily Domain Symbol)
    (model : Model Literal Symbol Value hoApplySymbol) : Prop :=
  ∀ value, ∃ tree : family.Generated, denote model tree.val = value

theorem guard_eval (model : Model Literal Symbol Value hoApplySymbol)
    (membershipSymbol : Domain → Symbol) (domains : List Domain)
    (environment : Environment Variable Value) (subject : Term Variable Literal Symbol) :
    model.Satisfies environment (guard membershipSymbol domains subject) ↔
      ∃ domain ∈ domains, model.holds (model.application (membershipSymbol domain) [model.eval environment subject]) := by
  induction domains with
  | nil =>
      simp only [guard, List.map_nil, List.foldr_nil, Model.Satisfies, Model.eval]
      constructor
      · intro impossible; exact False.elim (model.holds_bottom impossible)
      · intro ⟨_, impossible, _⟩; cases impossible
  | cons domain domains ih =>
      simp only [guard, List.map_cons, List.foldr_cons, Model.Satisfies, Model.eval,
        List.map_cons, List.map_nil, model.holds_disjunction] at ih ⊢
      constructor
      · intro either
        rcases either with yes | yes
        · exact ⟨domain, by simp, yes⟩
        · obtain ⟨other, member, yes⟩ := ih.mp yes
          exact ⟨other, by simp [member], yes⟩
      · intro ⟨other, member, yes⟩
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact Or.inl yes
        · exact Or.inr (ih.mpr ⟨other, member, yes⟩)

/-- The guarded-universal syntax has exactly the intended domain-union meaning.
No generic implication-failure rule is involved. -/
theorem Universal.satisfies_iff (goal : Universal Domain Variable Literal Symbol)
    (model : Model Literal Symbol Value hoApplySymbol) (realizes : Realizes model sigma membershipSymbol)
    (environment : Environment Variable Value) :
    model.Satisfies environment (goal.toTerm membershipSymbol) ↔
      Holds sigma goal.domains (fun tree => model.Satisfies
        (update environment goal.binder (denote model tree)) goal.body) := by
  simp only [Universal.toTerm, Model.Satisfies, Model.eval, model.holds_universal, model.holds_implication]
  constructor
  · intro universal tree ⟨domain, selected, member⟩
    apply universal (denote model tree)
    apply (guard_eval model membershipSymbol goal.domains _ (.var goal.binder)).mpr
    refine ⟨domain, selected, (realizes domain _).mpr ⟨tree, member, ?_⟩⟩
    simp [Model.eval, update]
  · intro universal value guardTrue
    obtain ⟨domain, selected, member⟩ := (guard_eval model membershipSymbol goal.domains _ (.var goal.binder)).mp guardTrue
    simp only [Model.eval, update, ite_true] at member
    obtain ⟨tree, member, same⟩ := (realizes domain value).mp member
    have result := universal tree ⟨domain, selected, member⟩
    simpa only [same] using result

/-- The all-domain guard quantifies exactly over the generated data universe,
even when the semantic carrier contains additional logical or other values. -/
theorem FiniteFamily.forallAll_satisfies_iff (family : FiniteFamily Domain Symbol)
    (model : Model Literal Symbol Value hoApplySymbol)
    (realizes : Realizes model family.definitions membershipSymbol)
    (environment : Environment Variable Value) (binder : Variable) (body : Term Variable Literal Symbol) :
    model.Satisfies environment ((family.forallAll binder body).toTerm membershipSymbol) ↔
      ∀ value : family.Generated, model.Satisfies
        (update environment binder (denote model value.val)) body :=
  (Universal.satisfies_iff _ model realizes environment).trans (family.holds_iff _)

/-- Coverage makes the guarded and unrestricted universal formulas equivalent.
No such equivalence is assumed when the carrier has values outside the data universe. -/
theorem FiniteFamily.forallAll_iff_forall (family : FiniteFamily Domain Symbol)
    (model : Model Literal Symbol Value hoApplySymbol)
    (realizes : Realizes model family.definitions membershipSymbol) (coverage : family.Covers model)
    (environment : Environment Variable Value) (binder : Variable) (body : Term Variable Literal Symbol) :
    model.Satisfies environment ((family.forallAll binder body).toTerm membershipSymbol) ↔
      model.Satisfies environment (.forallVar binder body) := by
  rw [family.forallAll_satisfies_iff model realizes environment binder body]
  simp only [Model.Satisfies, Model.eval, model.holds_universal]
  constructor
  · intro proof value
    obtain ⟨tree, same⟩ := coverage value
    simpa only [same] using proof tree
  · intro proof value; exact proof (denote model value.val)

theorem Universal.refutes_sound (goal : Universal Domain Variable Literal Symbol)
    (model : Model Literal Symbol Value hoApplySymbol) (realizes : Realizes model sigma membershipSymbol)
    (environment : Environment Variable Value)
    (refuted : Refutes sigma goal.domains (fun tree => model.Satisfies
      (update environment goal.binder (denote model tree)) goal.body)) :
    ¬ model.Satisfies environment (goal.toTerm membershipSymbol) :=
  fun proof => refutes_not_holds refuted ((goal.satisfies_iff model realizes environment).mp proof)

/-- A certified counterexample justifies NAF of this universal in a model with
complement NAF. It does not turn ordinary hypothetical search failure into NAF. -/
theorem Universal.naf_of_refutation (goal : Universal Domain Variable Literal Symbol)
    (model : Model Literal Symbol Value hoApplySymbol) (realizes : Realizes model sigma membershipSymbol)
    (negation : model.ComplementNAF) (environment : Environment Variable Value)
    (refuted : Refutes sigma goal.domains (fun tree => model.Satisfies
      (update environment goal.binder (denote model tree)) goal.body)) :
    model.Satisfies environment (.defaultNeg (goal.toTerm membershipSymbol)) := by
  simp only [Model.Satisfies, Model.eval]
  exact (negation _).mpr (goal.refutes_sound model realizes environment refuted)

/-- Evidence indexed by the exact KB and by the actual local context. Its
certificates must refute the property for an actual generated member under
every environment satisfying that context. This is a certified interface, not
an implemented counterexample finder or the old ScopedSearch failure provider. -/
def failureEvidence (sigma : Definitions Domain Symbol) (model : Model Literal Symbol Value hoApplySymbol)
    (membershipSymbol : Domain → Symbol) (kb : LogicalKb Variable Literal Symbol) :
    NafFailure Variable Literal Symbol :=
  fun actualSymbol actualKb context formula =>
    actualSymbol = hoApplySymbol ∧ actualKb = kb ∧
      ∃ goal : Universal Domain Variable Literal Symbol,
        formula = goal.toTerm membershipSymbol ∧
        ∀ environment, model.ContextHolds environment context →
          Refutes sigma goal.domains (fun tree => model.Satisfies
            (update environment goal.binder (denote model tree)) goal.body)

theorem failureAdequate (model : Model Literal Symbol Value hoApplySymbol)
    (realizes : Realizes model sigma membershipSymbol) (negation : model.ComplementNAF)
    (kb : LogicalKb Variable Literal Symbol) :
    model.FailureAdequate kb (failureEvidence sigma model membershipSymbol kb) := by
  intro context formula closed evidence environment valid
  rcases evidence with ⟨_, _, goal, rfl, counterexamples⟩
  exact goal.naf_of_refutation model realizes negation environment (counterexamples environment valid)

end AnthillModKbSpec.InductiveDomains
