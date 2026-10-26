import AnthillModKbSpec.Resolution.VariableSearch
import AnthillModKbSpec.Foundation.Opening

namespace AnthillModKbSpec.ScopedSearch

variable {Variable Literal Symbol : Type} [DecidableEq Variable] {hoApplySymbol : Symbol}

/-- Runtime data: variables are permitted only as declared rigid parameters.
Clause-template variables are instantiated separately and cannot bind them. -/
inductive IsData (parameters : List Variable) : Term Variable Literal Symbol → Prop where
  | parameter (declared : name ∈ parameters) : IsData parameters (.var name)
  | lit : IsData parameters (.lit value)
  | app (args : ∀ arg ∈ arguments, IsData parameters arg) : IsData parameters (.app symbol arguments)

inductive IsAtom (hoApplySymbol : Symbol) (parameters : List Variable) : Term Variable Literal Symbol → Prop where
  | app (ordinary : symbol ≠ hoApplySymbol)
      (args : ∀ arg ∈ arguments, IsData parameters arg) : IsAtom hoApplySymbol parameters (.app symbol arguments)

mutual
/-- Runtime goals with hypothetical local definite clauses. -/
inductive IsGoal (hoApplySymbol : Symbol) : List Variable → Term Variable Literal Symbol → Prop where
  | atom (valid : IsAtom hoApplySymbol parameters atom) : IsGoal hoApplySymbol parameters atom
  | truth : IsGoal hoApplySymbol parameters .truth
  | falsity : IsGoal hoApplySymbol parameters .falsity
  | conj (left : IsGoal hoApplySymbol parameters a) (right : IsGoal hoApplySymbol parameters b) :
      IsGoal hoApplySymbol parameters (.conj a b)
  | defaultNeg (body : IsGoal hoApplySymbol parameters goal) : IsGoal hoApplySymbol parameters (.defaultNeg goal)
  | forallVar (body : IsGoal hoApplySymbol (binder :: parameters) goal) :
      IsGoal hoApplySymbol parameters (.forallVar binder goal)
  | imp (premise : IsLocal hoApplySymbol parameters a) (conclusion : IsGoal hoApplySymbol parameters b) :
      IsGoal hoApplySymbol parameters (.imp a b)

/-- Definite local assumptions: facts, conjunctions, universally quantified
clauses, and implications whose conclusions are definite clauses. Free names
remain fixed parameters, rather than implicit universally quantified variables.
Default negation, disjunction, and falsity are not local clause heads. -/
inductive IsLocal (hoApplySymbol : Symbol) : List Variable → Term Variable Literal Symbol → Prop where
  | atom (valid : IsAtom hoApplySymbol parameters atom) : IsLocal hoApplySymbol parameters atom
  | truth : IsLocal hoApplySymbol parameters .truth
  | conj (left : IsLocal hoApplySymbol parameters a) (right : IsLocal hoApplySymbol parameters b) :
      IsLocal hoApplySymbol parameters (.conj a b)
  | forallVar (body : IsLocal hoApplySymbol (binder :: parameters) clause) :
      IsLocal hoApplySymbol parameters (.forallVar binder clause)
  | imp (premise : IsGoal hoApplySymbol parameters a) (conclusion : IsLocal hoApplySymbol parameters b) :
      IsLocal hoApplySymbol parameters (.imp a b)
end

/-- Source binding safety, extended with universal and hypothetical scopes.
Names learned inside either scope do not escape into following conjuncts. NAF on a bound name is still
subject to the stricter runtime opacity gate below. -/
inductive SafeGoal (hoApplySymbol : Symbol) : List Variable → Term Variable Literal Symbol → List Variable → Prop where
  | basic (safe : VariableSearch.SafeGoal hoApplySymbol before goal after) :
      SafeGoal hoApplySymbol before goal after
  | conj (left : SafeGoal hoApplySymbol before a middle)
      (right : SafeGoal hoApplySymbol middle b after) :
      SafeGoal hoApplySymbol before (.conj a b) after
  | forallVar (body : SafeGoal hoApplySymbol (binder :: known) goal after) :
      SafeGoal hoApplySymbol known (.forallVar binder goal) known
  | defaultNeg (valid : IsGoal hoApplySymbol goal.freeVars goal)
      (bound : ∀ name ∈ goal.freeVars, name ∈ known) :
      SafeGoal hoApplySymbol known (.defaultNeg goal) known
  /-- A hypothetical premise uses already-fixed names. Information learned
  while proving its conclusion is local to that implication. -/
  | imp (premise : IsLocal hoApplySymbol antecedent.freeVars antecedent)
      (bound : ∀ name ∈ antecedent.freeVars, name ∈ known)
      (conclusion : SafeGoal hoApplySymbol known consequent after) :
      SafeGoal hoApplySymbol known (.imp antecedent consequent) known

inductive IsClause (hoApplySymbol : Symbol) : HornClause Variable Literal Symbol → Prop where
  | definite (head : VariableSearch.IsAtom hoApplySymbol atom)
      (body : SafeGoal hoApplySymbol atom.freeVars (.conjunction goals) after) :
      IsClause hoApplySymbol (.definite atom goals)

structure Program (Variable Literal Symbol : Type) [DecidableEq Variable] (hoApplySymbol : Symbol) where
  clauses : List (HornClause Variable Literal Symbol)
  wellFormed : ∀ clause ∈ clauses, IsClause hoApplySymbol clause

structure Context (Variable Literal Symbol : Type) (hoApplySymbol : Symbol) where
  parameters : List Variable
  assumptions : ProofContext Variable Literal Symbol
  wellFormed : ∀ clause ∈ assumptions, IsLocal hoApplySymbol parameters clause

omit [DecidableEq Variable] in
private theorem data_mono (proof : IsData parameters (Variable := Variable) term)
    (includeNames : ∀ name ∈ parameters, name ∈ larger) : IsData larger term := by
  induction proof with
  | parameter declared => exact .parameter (includeNames _ declared)
  | lit => exact .lit
  | app args ih => exact .app ih

omit [DecidableEq Variable] in
private theorem atom_mono (proof : IsAtom hoApplySymbol parameters (Variable := Variable) atom)
    (includeNames : ∀ name ∈ parameters, name ∈ larger) : IsAtom hoApplySymbol larger atom := by
  cases proof with
  | app ordinary args => exact .app ordinary (fun a h => data_mono (args a h) includeNames)

omit [DecidableEq Variable] in
private theorem local_mono (proof : IsLocal hoApplySymbol parameters (Variable := Variable) clause) :
    ∀ larger, (∀ name ∈ parameters, name ∈ larger) → IsLocal hoApplySymbol larger clause := by
  refine IsLocal.rec
    (motive_1 := fun parameters goal _ => ∀ larger, (∀ name ∈ parameters, name ∈ larger) → IsGoal hoApplySymbol larger goal)
    (motive_2 := fun parameters clause _ => ∀ larger, (∀ name ∈ parameters, name ∈ larger) → IsLocal hoApplySymbol larger clause)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ proof
  · intro parameters atom valid larger includeNames; exact .atom (atom_mono valid includeNames)
  · intros; exact .truth
  · intros; exact .falsity
  · intro parameters a b left right ihLeft ihRight larger includeNames
    exact .conj (ihLeft larger includeNames) (ihRight larger includeNames)
  · intro parameters goal body ih larger includeNames; exact .defaultNeg (ih larger includeNames)
  · intro binder parameters goal body ih larger includeNames
    apply IsGoal.forallVar
    apply ih (binder :: larger)
    intro name member
    simp only [List.mem_cons] at member ⊢
    exact member.elim Or.inl (fun h => Or.inr (includeNames _ h))
  · intro parameters a b premise conclusion ihPremise ihConclusion larger includeNames
    exact .imp (ihPremise larger includeNames) (ihConclusion larger includeNames)
  · intro parameters atom valid larger includeNames; exact .atom (atom_mono valid includeNames)
  · intros; exact .truth
  · intro parameters a b left right ihLeft ihRight larger includeNames
    exact .conj (ihLeft larger includeNames) (ihRight larger includeNames)
  · intro binder parameters clause body ih larger includeNames
    apply IsLocal.forallVar
    apply ih (binder :: larger)
    intro name member
    simp only [List.mem_cons] at member ⊢
    exact member.elim Or.inl (fun h => Or.inr (includeNames _ h))
  · intro parameters a b premise conclusion ihPremise ihConclusion larger includeNames
    exact .imp (ihPremise larger includeNames) (ihConclusion larger includeNames)

/-- Enter a universal scope without modifying existing assumptions. -/
def Context.extend (context : Context Variable Literal Symbol hoApplySymbol) (name : Variable) :
    Context Variable Literal Symbol hoApplySymbol where
  parameters := name :: context.parameters
  assumptions := context.assumptions
  wellFormed := fun clause member => local_mono (context.wellFormed clause member) _
    (fun candidate declared => by simp [declared])

/-- A hypothetical premise is available only to its conclusion subproof. -/
def Context.assume (context : Context Variable Literal Symbol hoApplySymbol)
    (premise : Term Variable Literal Symbol) (valid : IsLocal hoApplySymbol context.parameters premise) :
    Context Variable Literal Symbol hoApplySymbol where
  parameters := context.parameters
  assumptions := premise :: context.assumptions
  wellFormed := by
    intro clause member
    simp only [List.mem_cons] at member
    exact member.elim (fun equal => equal ▸ valid) (context.wellFormed clause)

/-- Syntactic absence cannot refute an atom against opaque local assumptions:
a rigid name in a hypothesis might denote a concrete queried value. A future
symbolic matcher may discharge some of these cases more precisely. -/
def Context.Closed (context : Context Variable Literal Symbol hoApplySymbol) : Prop :=
  ∀ assumption ∈ context.assumptions, assumption.freeVars = []

def Program.toKb (program : Program Variable Literal Symbol hoApplySymbol) :
    LogicalKb Variable Literal Symbol := fun clause => clause ∈ program.clauses

variable [FreshNames Variable]

/-- Avoid active parameters, assumption variables, the binder itself, free body
variables, and every nested binder. A canonical choice makes success/failure
certificates use the same eigenvariable without a separate alpha-equivalence
invariance theorem. -/
def Context.avoid (context : Context Variable Literal Symbol hoApplySymbol)
    (binder : Variable) (body : Term Variable Literal Symbol) : List Variable :=
  context.parameters ++ context.assumptions.flatMap Term.freeVars ++
    [binder] ++ body.freeVars ++ body.binderNames

def Context.eigen (context : Context Variable Literal Symbol hoApplySymbol)
    (binder : Variable) (body : Term Variable Literal Symbol) : Variable :=
  FreshNames.fresh (context.avoid binder body)

theorem Context.eigen_not_mem (context : Context Variable Literal Symbol hoApplySymbol)
    (binder : Variable) (body : Term Variable Literal Symbol) :
    context.eigen binder body ∉ context.avoid binder body := FreshNames.fresh_not_mem _

theorem Context.eigen_new (context : Context Variable Literal Symbol hoApplySymbol)
    (binder : Variable) (body : Term Variable Literal Symbol) :
    context.eigen binder body ∉ context.parameters := by
  intro member
  apply context.eigen_not_mem binder body
  simp [Context.avoid, member]

theorem Context.eigen_freshContext (context : Context Variable Literal Symbol hoApplySymbol)
    (binder : Variable) (body : Term Variable Literal Symbol) :
    FreshForContext (context.eigen binder body) context.assumptions := by
  intro assumption member free
  apply context.eigen_not_mem binder body
  have occurs : context.eigen binder body ∈ context.assumptions.flatMap Term.freeVars :=
    List.mem_flatMap.mpr ⟨assumption, member, free⟩
  simp [Context.avoid, occurs]

theorem Context.eigen_freshGoal (context : Context Variable Literal Symbol hoApplySymbol)
    (binder : Variable) (body : Term Variable Literal Symbol) :
    context.eigen binder body ∉ (Term.forallVar binder body).freeVars := by
  intro member
  simp only [Term.freeVars] at member
  have free : context.eigen binder body ∈ body.freeVars := (List.mem_filter.mp member).1
  apply context.eigen_not_mem binder body
  simp [Context.avoid, free]

theorem Context.opening (context : Context Variable Literal Symbol hoApplySymbol)
    (binder : Variable) (body : Term Variable Literal Symbol) :
    Substitutes (Substitution.single binder (.var (context.eigen binder body))) body
      (body.openFree binder (context.eigen binder body)) := by
  apply body.openFree_substitutes
  intro member
  apply context.eigen_not_mem binder body
  simp [Context.avoid, member]

/-- Decompose a local definite formula into an atomic head and a goal body.
Universal assumptions are instantiated explicitly; free parameters are never
implicitly universally closed. Conjuncts and nested implications remain local. -/
inductive LocalInstance (parameters : List Variable) : Term Variable Literal Symbol →
    Term Variable Literal Symbol → Term Variable Literal Symbol → Prop where
  | fact (valid : IsAtom hoApplySymbol parameters atom) : LocalInstance parameters atom atom .truth
  | conjLeft (instanceLeft : LocalInstance parameters left atom body) :
      LocalInstance parameters (.conj left right) atom body
  | conjRight (instanceRight : LocalInstance parameters right atom body) :
      LocalInstance parameters (.conj left right) atom body
  | imp (instanceConclusion : LocalInstance parameters conclusion atom body) :
      LocalInstance parameters (.imp premise conclusion) atom (.conj premise body)
  | forallVar (witness : IsData parameters value)
      (instantiation : Substitutes (Substitution.single binder value) clause instantiated)
      (instanceBody : LocalInstance parameters instantiated atom body) :
      LocalInstance parameters (.forallVar binder clause) atom body

inductive Instance (program : Program Variable Literal Symbol hoApplySymbol)
    (context : Context Variable Literal Symbol hoApplySymbol) (atom : Term Variable Literal Symbol) :
    List (Term Variable Literal Symbol) → Prop where
  | intro (member : HornClause.definite head body ∈ program.clauses)
      (headInstance : Substitutes σ head atom) (bodyInstance : SubstitutesList σ body instantiated)
      (valid : ∀ goal ∈ instantiated, IsGoal hoApplySymbol context.parameters goal) :
      Instance program context atom instantiated
  | hypothesis (member : assumption ∈ context.assumptions)
      (backchain : LocalInstance (hoApplySymbol := hoApplySymbol) context.parameters assumption atom body)
      (valid : IsGoal hoApplySymbol context.parameters body) :
      Instance program context atom [body]

/-- Exhaust all applicable instantiated bodies in the current rigid scope. -/
structure ExhaustedInstances (program : Program Variable Literal Symbol hoApplySymbol)
    (context : Context Variable Literal Symbol hoApplySymbol) (atom : Term Variable Literal Symbol) where
  bodies : List (List (Term Variable Literal Symbol))
  sound : ∀ body ∈ bodies, Instance program context atom body
  complete : ∀ body, Instance program context atom body → body ∈ bodies

mutual
inductive Succeeds (program : Program Variable Literal Symbol hoApplySymbol) :
    Context Variable Literal Symbol hoApplySymbol → Term Variable Literal Symbol → Prop where
  | assumption {context : Context Variable Literal Symbol hoApplySymbol} (valid : IsAtom hoApplySymbol context.parameters (.app symbol args))
      (member : Term.app symbol args ∈ context.assumptions) : Succeeds program context (.app symbol args)
  | clause {context : Context Variable Literal Symbol hoApplySymbol} (valid : IsAtom hoApplySymbol context.parameters (.app symbol args))
      (instantiation : Instance program context (.app symbol args) body)
      (proof : Succeeds program context (.conjunction body)) : Succeeds program context (.app symbol args)
  | truth {context : Context Variable Literal Symbol hoApplySymbol} : Succeeds program context .truth
  | conj {context : Context Variable Literal Symbol hoApplySymbol} (left : Succeeds program context a) (right : Succeeds program context b) :
      Succeeds program context (.conj a b)
  | defaultNeg {context : Context Variable Literal Symbol hoApplySymbol} (closed : goal.freeVars = []) (refuted : Fails program context goal) :
      Succeeds program context (.defaultNeg goal)
  /-- A fresh rigid parameter, never an enumerated concrete value. -/
  | forallVar {context : Context Variable Literal Symbol hoApplySymbol} (valid : IsGoal hoApplySymbol context.parameters (.forallVar binder body))
      (proof : Succeeds program (context.extend (context.eigen binder body))
        (body.openFree binder (context.eigen binder body))) :
      Succeeds program context (.forallVar binder body)
  | imp {context : Context Variable Literal Symbol hoApplySymbol}
      (premise : IsLocal hoApplySymbol context.parameters antecedent)
      (conclusion : IsGoal hoApplySymbol context.parameters consequent)
      (proof : Succeeds program (context.assume antecedent premise) consequent) :
      Succeeds program context (.imp antecedent consequent)

inductive Fails (program : Program Variable Literal Symbol hoApplySymbol) :
    Context Variable Literal Symbol hoApplySymbol → Term Variable Literal Symbol → Prop where
  /-- Closed-world absence is not a refutation about an opaque parameter. -/
  | atom {context : Context Variable Literal Symbol hoApplySymbol} (valid : IsAtom hoApplySymbol context.parameters (.app symbol args))
      (closed : (Term.app symbol args).freeVars = [])
      (contextClosed : context.Closed)
      (absent : Term.app symbol args ∉ context.assumptions)
      (generator : ExhaustedInstances program context (.app symbol args))
      (allBodies : ∀ body ∈ generator.bodies, Fails program context (.conjunction body)) :
      Fails program context (.app symbol args)
  | falsity {context : Context Variable Literal Symbol hoApplySymbol} : Fails program context .falsity
  | conjLeft {context : Context Variable Literal Symbol hoApplySymbol} (left : Fails program context a) (right : IsGoal hoApplySymbol context.parameters b) :
      Fails program context (.conj a b)
  | conjRight {context : Context Variable Literal Symbol hoApplySymbol} (left : IsGoal hoApplySymbol context.parameters a) (right : Fails program context b) :
      Fails program context (.conj a b)
  | defaultNeg {context : Context Variable Literal Symbol hoApplySymbol} (closed : goal.freeVars = []) (proof : Succeeds program context goal) :
      Fails program context (.defaultNeg goal)
  /-- Failure of the canonically opened body. Opaque-parameter gates above
  conservatively prevent reading missing p(eigen) as a counterexample. -/
  | forallVar {context : Context Variable Literal Symbol hoApplySymbol} (valid : IsGoal hoApplySymbol context.parameters (.forallVar binder body))
      (refuted : Fails program (context.extend (context.eigen binder body))
        (body.openFree binder (context.eigen binder body))) :
      Fails program context (.forallVar binder body)
  | imp {context : Context Variable Literal Symbol hoApplySymbol}
      (premise : IsLocal hoApplySymbol context.parameters antecedent)
      (conclusion : IsGoal hoApplySymbol context.parameters consequent)
      (refuted : Fails program (context.assume antecedent premise) consequent) :
      Fails program context (.imp antecedent consequent)
end

variable {program : Program Variable Literal Symbol hoApplySymbol}
  {context : Context Variable Literal Symbol hoApplySymbol} {goal : Term Variable Literal Symbol}

/-- Answer substitutions may instantiate flexible query names but must preserve
every active rigid parameter. Validity in the original context prevents newly
introduced universal witnesses from escaping into the answer. -/
inductive Answers (program : Program Variable Literal Symbol hoApplySymbol)
    (context : Context Variable Literal Symbol hoApplySymbol)
    (query : Term Variable Literal Symbol) (σ : Substitution Variable Literal Symbol) : Prop where
  | intro (safe : SafeGoal hoApplySymbol context.parameters query known)
      (preserves : ∀ name ∈ context.parameters, σ name = .var name)
      (instantiation : Substitutes σ query instantiated)
      (valid : IsGoal hoApplySymbol context.parameters instantiated)
      (proof : Succeeds program context instantiated) : Answers program context query σ

/-- Disjointness includes universal and hypothetical goals in their exact local scopes. -/
theorem succeeds_not_fails (proof : Succeeds program context goal) : ¬ Fails program context goal := by
  refine Succeeds.rec
    (motive_1 := fun context goal _ => ¬ Fails program context goal)
    (motive_2 := fun context goal _ => ¬ Succeeds program context goal)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ proof
  · intro symbol args context valid member refuted
    cases refuted with
    | atom _ _ _ absent _ _ => exact absent member
  · intro symbol args body context valid inst bodyProof ih refuted
    cases refuted with
    | atom _ _ _ _ generator allBodies => exact ih (allBodies _ (generator.complete _ inst))
  · intro context refuted; cases refuted
  · intro a b context left right ihLeft ihRight refuted
    cases refuted with
    | conjLeft failed _ => exact ihLeft failed
    | conjRight _ failed => exact ihRight failed
  · intro goal context closed refuted ih failed
    cases failed with
    | defaultNeg _ proof => exact ih proof
  · intro binder body context valid proof ih refuted
    cases refuted with
    | forallVar _ failed => exact ih failed
  · intro antecedent consequent context premise conclusion proof ih refuted
    cases refuted with
    | imp _ _ failed => exact ih failed
  · intro symbol args context valid closed contextClosed absent generator allBodies ih proof
    cases proof with
    | assumption _ member => exact absent member
    | clause _ inst bodyProof => exact ih _ (generator.complete _ inst) bodyProof
  · intro context proof; cases proof
  · intro a b context failed valid ih proof
    cases proof with
    | conj left _ => exact ih left
  · intro a b context valid failed ih proof
    cases proof with
    | conj _ right => exact ih right
  · intro goal context closed proof ih failed
    cases failed with
    | defaultNeg _ refuted => exact ih refuted
  · intro binder body context valid refuted ih proof
    cases proof with
    | forallVar _ success => exact ih success
  · intro antecedent consequent context premise conclusion refuted ih proof
    cases proof with
    | imp _ _ success => exact ih success

theorem fails_not_succeeds (refuted : Fails program context goal) : ¬ Succeeds program context goal :=
  fun proof => succeeds_not_fails proof refuted

/-- Failure evidence records the exact logical KB and assumption list. Rigid
scopes are existentially packaged; closedness is checked at each NAF rule.
This permits the same evidence relation while entering nested universal goals. -/
def failureEvidence (program : Program Variable Literal Symbol hoApplySymbol) : NafFailure Variable Literal Symbol :=
  fun actualSymbol actualKb assumptions goal =>
    actualSymbol = hoApplySymbol ∧ actualKb = program.toKb ∧
      ∃ context : Context Variable Literal Symbol hoApplySymbol,
        context.assumptions = assumptions ∧ Fails program context goal

omit [FreshNames Variable] in
private theorem conjunctionSubstitution {σ : Substitution Variable Literal Symbol}
    (proof : SubstitutesList σ before after) : Substitutes σ (.conjunction before) (.conjunction after) := by
  induction before generalizing after with
  | nil => cases proof; exact .truth
  | cons head tail ih => cases proof with | cons first rest => exact .conj first (ih rest)

omit [FreshNames Variable] in
/-- Local clause use is justified by conjunction/implication elimination and
explicit instantiation of universally quantified assumptions. -/
theorem LocalInstance.toDerives
    {parameters : List Variable} {assumption atom body : Term Variable Literal Symbol}
    {kb : LogicalKb Variable Literal Symbol} {assumptions : ProofContext Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol}
    (backchain : LocalInstance (hoApplySymbol := hoApplySymbol) parameters assumption atom body) :
    Derives hoApplySymbol kb assumptions assumption naf →
    Derives hoApplySymbol kb assumptions body naf → Derives hoApplySymbol kb assumptions atom naf := by
  induction backchain with
  | fact valid => intro assumed proved; exact assumed
  | conjLeft child ih => intro assumed proved; exact ih (.conjLeft assumed) proved
  | conjRight child ih => intro assumed proved; exact ih (.conjRight assumed) proved
  | imp child ih =>
      intro assumed proved
      exact ih (.impElim assumed (.conjLeft proved)) (.conjRight proved)
  | forallVar witness inst child ih =>
      intro assumed proved
      exact ih (.forallElim assumed inst) proved

/-- Every scoped success gives a derivation. Universal introduction is connected
to the existing capture-avoiding substitution and eigenvariable side conditions. -/
theorem succeeds_toDerives (proof : Succeeds program context goal) :
    Derives hoApplySymbol program.toKb context.assumptions goal (failureEvidence program) := by
  refine Succeeds.rec
    (motive_1 := fun context goal _ => Derives hoApplySymbol program.toKb context.assumptions goal (failureEvidence program))
    (motive_2 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ proof
  · intro symbol args context valid member; exact .assumption member
  · intro symbol args body context valid inst bodyProof ih
    cases inst with
    | intro member headInstance bodyInstance valid =>
        exact .clause member headInstance (conjunctionSubstitution bodyInstance) ih
    | hypothesis member backchain valid =>
        exact backchain.toDerives (.assumption member) (.conjLeft ih)
  · intro context; exact .truth
  · intro a b context left right ihLeft ihRight; exact .conjIntro ihLeft ihRight
  · intro goal context closed refuted ih
    exact .defaultNegIntro closed ⟨rfl, rfl, context, rfl, refuted⟩
  · intro binder body context valid proof ih
    exact .forallIntro (context.eigen_freshContext binder body) (context.eigen_freshGoal binder body)
      (context.opening binder body) ih
  · intro antecedent consequent context premise conclusion proof ih
    exact .impIntro ih
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

/-- Answers remain proofs of capture-avoiding instances in the original scope. -/
theorem answers_toDerives (answer : Answers program context query σ) :
    ∃ instantiated, Substitutes σ query instantiated ∧
      Derives hoApplySymbol program.toKb context.assumptions instantiated (failureEvidence program) := by
  cases answer with
  | intro safe preserves inst valid proof => exact ⟨_, inst, succeeds_toDerives proof⟩

end AnthillModKbSpec.ScopedSearch
