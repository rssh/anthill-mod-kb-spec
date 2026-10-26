import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.ScopedSearch AnthillModKbSpec.Semantics

private abbrev T := Term String Nat String
private abbrev P := Program String Nat String "ho_apply"
private abbrev C := Context String Nat String "ho_apply"
private def p (value : T) : T := .app "p" [value]
private def q (value : T) : T := .app "q" [value]
private def emptyContext : C := ⟨[], [], by simp⟩
private def falseInterpretation : String → List (DataKey Nat String) → Prop := fun _ _ => False
private def model := Model.herbrand "ho_apply" falseInterpretation
private theorem atomFalse {parameters : List String} {symbol : String} {args : List T}
    (valid : IsAtom "ho_apply" parameters (.app symbol args)) :
    ∀ environment, ¬ model.Satisfies environment (.app symbol args) := by
  intro environment
  cases valid with
  | app ordinary argsValid =>
      dsimp only [model]
      rw [Model.herbrand_atom falseInterpretation environment ordinary]
      exact id

private theorem pAtom (parameters : List String) (value : T) (valid : IsData parameters value) :
    IsAtom "ho_apply" parameters (p value) :=
  .app (by decide) (by intro arg member; simp at member; subst arg; exact valid)
private theorem qAtom (parameters : List String) (value : T) (valid : IsData parameters value) :
    IsAtom "ho_apply" parameters (q value) :=
  .app (by decide) (by intro arg member; simp at member; subst arg; exact valid)

-- A schematic global rule uses the same substitution in its head and body.
private def program : P := ⟨[.definite (q (.var "x")) [p (.var "x")]], by
  intro clause member; simp at member; subst clause
  apply IsClause.definite (.app (by decide) (by intro arg member; simp at member; subst arg; exact .var))
  apply SafeGoal.conj
  · exact .basic (.atom (.app (by decide) (by intro arg member; simp at member; subst arg; exact .var)))
  · exact .basic .truth⟩

private theorem unarySubst {σ : Substitution String Nat String} {symbol name : String} {target : T}
    (substitution : Substitutes σ (.app symbol [.var name]) target) :
    target = .app symbol [σ name] := by
  cases substitution with
  | app args => cases args with
    | cons first rest => cases first; cases rest; rfl

private def noP : ExhaustedInstances program emptyContext (p (.lit 0)) := ⟨[], by simp, by
  intro body instanceProof
  cases instanceProof with
  | intro member headSubst bodySubst valid =>
      simp [program] at member
      rcases member with ⟨rfl, rfl⟩
      have impossible := unarySubst headSubst
      simp [p] at impossible
  | hypothesis member _ _ => simp [emptyContext] at member⟩

private theorem qBody {body : List T} (instanceProof : Instance program emptyContext (q (.lit 0)) body) :
    body = [p (.lit 0)] := by
  cases instanceProof with
  | intro member headSubst bodySubst valid =>
      simp [program] at member
      rcases member with ⟨rfl, rfl⟩
      have value := unarySubst headSubst
      simp only [q, Term.app.injEq, List.cons.injEq, and_true, true_and] at value
      cases bodySubst with
      | cons first rest =>
          cases rest
          have same := unarySubst first
          rw [← value] at same
          exact congrArg (fun term => [term]) same
  | hypothesis member _ _ => simp [emptyContext] at member

private def allQ : ExhaustedInstances program emptyContext (q (.lit 0)) :=
  ⟨[[p (.lit 0)]], by
    intro body member; simp only [List.mem_singleton] at member; subst body
    exact .intro (σ := Substitution.single "x" (.lit 0)) (by simp [program, p, q])
      (.app (.cons (.singleVar "x" (.lit 0)) .nil))
      (.cons (.app (.cons (.singleVar "x" (.lit 0)) .nil)) .nil)
      (by intro goal member; simp at member; subst goal; exact .atom (pAtom _ _ .lit)), by
    intro body instanceProof
    simp only [List.mem_singleton]
    exact qBody instanceProof⟩

private theorem pCompleted : model.ScopedAtomCompleted program emptyContext (p (.lit 0)) := by
  intro environment valid
  constructor
  · intro impossible; exact False.elim (atomFalse (pAtom [] _ .lit) environment impossible)
  · intro alternatives
    rcases alternatives with member | ⟨body, instanceProof, bodyTrue⟩
    · simp [emptyContext] at member
    · have impossible := noP.complete body instanceProof
      simp [noP] at impossible

private theorem qCompleted : model.ScopedAtomCompleted program emptyContext (q (.lit 0)) := by
  intro environment valid
  constructor
  · intro impossible; exact False.elim (atomFalse (qAtom [] _ .lit) environment impossible)
  · intro alternatives
    rcases alternatives with member | ⟨body, instanceProof, bodyTrue⟩
    · simp [emptyContext] at member
    · rw [qBody instanceProof] at bodyTrue
      simp only [Term.conjunction, List.foldr_cons, List.foldr_nil, Model.Satisfies, Model.eval] at bodyTrue
      exact False.elim (atomFalse (pAtom [] _ .lit) environment ((model.holds_conjunction _ _).mp bodyTrue).1)

private theorem pRefuted : CertifiedRefutation.Refutes model program.toKb [] (p (.lit 0)) :=
  .scopedAtom rfl (pAtom [] _ .lit) (by simp [p, Term.freeVars])
    (by simp [Context.Closed, emptyContext]) pCompleted (by simp [emptyContext]) noP (by simp [noP])

private theorem qRefuted : CertifiedRefutation.Refutes model program.toKb [] (q (.lit 0)) :=
  .scopedAtom rfl (qAtom [] _ .lit) (by simp [q, Term.freeVars])
    (by simp [Context.Closed, emptyContext]) qCompleted (by simp [emptyContext]) allQ (by
      intro body member
      simp only [allQ, List.mem_singleton] at member
      subst body
      exact .conjLeft pRefuted)

example : Derives "ho_apply" program.toKb [] (.defaultNeg (q (.lit 0)))
    (CertifiedRefutation.failureEvidence model program.toKb) :=
  qRefuted.toDerives (by simp [q, Term.freeVars])

-- Adapt an old atom failure only after independently certifying its bodies.
private theorem pFailure : Fails program emptyContext (p (.lit 0)) :=
  .atom (pAtom [] _ .lit) (by simp [Term.freeVars]) (by simp [Context.Closed, emptyContext])
    (by simp [emptyContext]) noP (by simp [noP])
example : CertifiedRefutation.Refutes model program.toKb [] (p (.lit 0)) :=
  .ofScopedAtomFailure rfl pCompleted pFailure (by
    intro body instanceProof
    have impossible := noP.complete body instanceProof
    simp [noP] at impossible)

-- A local rule is an alternative in the SAME exhaustive instance cover.
private def emptyProgram : P := ⟨[], by simp⟩
private def localRuleContext : C := emptyContext.assume (.imp .falsity (q (.lit 0)))
  (.imp .falsity (.atom (qAtom [] _ .lit)))
private theorem atomicLocal {parameters : List String} {symbol : String} {args : List T} {head body : T}
    (instanceProof : LocalInstance (hoApplySymbol := "ho_apply") parameters (.app symbol args) head body) :
    head = .app symbol args ∧ body = .truth := by
  cases instanceProof with | fact _ => exact ⟨rfl, rfl⟩

private def localCover : ExhaustedInstances emptyProgram localRuleContext (q (.lit 0)) :=
  ⟨[[.conj .falsity .truth]], by
    intro body member; simp only [List.mem_singleton] at member; subst body
    exact .hypothesis (assumption := .imp .falsity (q (.lit 0)))
      (by simp [localRuleContext, Context.assume]) (.imp (.fact (qAtom _ _ .lit))) (.conj .falsity .truth), by
    intro body instanceProof
    cases instanceProof with
    | intro member _ _ _ => simp [emptyProgram] at member
    | hypothesis member backchain _ =>
        simp only [localRuleContext, Context.assume, emptyContext, List.mem_cons,
          List.not_mem_nil, or_false] at member
        subst_vars
        cases backchain with
        | imp child =>
            have shape := atomicLocal child
            rcases shape with ⟨_, rfl⟩
            simp⟩

private theorem localCompleted : model.ScopedAtomCompleted emptyProgram localRuleContext (q (.lit 0)) := by
  intro environment valid
  constructor
  · intro impossible; exact False.elim (atomFalse (qAtom [] _ .lit) environment impossible)
  · intro alternatives
    rcases alternatives with member | ⟨body, instanceProof, bodyTrue⟩
    · simp [localRuleContext, Context.assume, emptyContext, q] at member
    · have shape := localCover.complete body instanceProof
      simp only [localCover, List.mem_singleton] at shape
      subst body
      simp only [Term.conjunction, List.foldr_cons, List.foldr_nil, Model.Satisfies, Model.eval] at bodyTrue
      exact False.elim (model.holds_bottom ((model.holds_conjunction _ _).mp
        ((model.holds_conjunction _ _).mp bodyTrue).1).1)

private theorem localRefuted : CertifiedRefutation.Refutes model emptyProgram.toKb localRuleContext.assumptions (q (.lit 0)) :=
  .scopedAtom rfl (qAtom [] _ .lit) (by simp [q, Term.freeVars])
    (by simp [Context.Closed, localRuleContext, Context.assume, emptyContext, q, Term.freeVars])
    localCompleted (by simp [localRuleContext, Context.assume, emptyContext, q]) localCover (by
      intro body member
      simp only [localCover, List.mem_singleton] at member
      subst body
      exact .conjLeft (.conjLeft .falsity))

example : Derives "ho_apply" emptyProgram.toKb localRuleContext.assumptions (.defaultNeg (q (.lit 0)))
    (CertifiedRefutation.failureEvidence model emptyProgram.toKb) :=
  localRefuted.toDerives (by simp [q, Term.freeVars])

example : ¬ (∀ body, Instance emptyProgram localRuleContext (q (.lit 0)) body → body ∈ []) := by
  intro incomplete
  have missing := incomplete [.conj .falsity .truth] (localCover.sound _ (by simp [localCover]))
  simp at missing

private theorem qFailure : Fails program emptyContext (q (.lit 0)) :=
  .atom (qAtom [] _ .lit) (by simp [Term.freeVars]) (by simp [Context.Closed, emptyContext])
    (by simp [emptyContext]) allQ (by
      intro body member
      simp only [allQ, List.mem_singleton] at member
      subst body
      exact .conjLeft pFailure .truth)

example : CertifiedRefutation.Refutes model program.toKb [] (q (.lit 0)) :=
  .ofScopedAtomFailure rfl qCompleted qFailure (by
    intro body instanceProof
    rw [qBody instanceProof]
    exact .conjLeft pRefuted)

-- A local fact supplies actual support and blocks a negative certificate.
private def factContext : C := emptyContext.assume (p (.lit 0)) (.atom (pAtom [] _ .lit))
private def factModel := Model.trueAtoms Nat String "ho_apply"
private theorem factCompleted : factModel.ScopedAtomCompleted emptyProgram factContext (p (.lit 0)) := by
  intro environment valid
  constructor
  · intro yes; exact Or.inl (by simp [factContext, Context.assume])
  · intro support; simp [Model.Satisfies, Model.eval, factModel, Model.trueAtoms, p]

private theorem factEstablished : CertifiedRefutation.Established factModel factContext.assumptions (p (.lit 0)) :=
  CertifiedRefutation.Established.ofScopedInstance factModel factCompleted
    (.hypothesis (assumption := p (.lit 0)) (by simp [factContext, Context.assume])
      (.fact (pAtom [] _ .lit)) .truth)
    (by intro environment valid
        simp [Term.conjunction, Model.Satisfies, Model.eval, factModel, Model.trueAtoms])

example : ¬ CertifiedRefutation.Refutes factModel emptyProgram.toKb factContext.assumptions (p (.lit 0)) := by
  intro refuted
  have negation : factModel.ComplementNAF := by
    intro value; change (!value = true ↔ ¬value = true)
    cases value <;> decide
  exact refuted.not_established negation (fun _ => false)
    (by intro assumption member; simp [factContext, Context.assume, emptyContext] at member
        subst assumption; simp [Model.Satisfies, Model.eval, factModel, Model.trueAtoms, p]) factEstablished

-- A closed query remains eligible in a rigid scope when the assumptions are closed.
private def rigidScope : C := emptyContext.extend "e"
private def rigidCover : ExhaustedInstances emptyProgram rigidScope (p (.lit 0)) := ⟨[], by simp, by
  intro body instanceProof
  cases instanceProof with
  | intro member _ _ _ => simp [emptyProgram] at member
  | hypothesis member _ _ => simp [rigidScope, Context.extend, emptyContext] at member⟩
private theorem rigidCompleted : model.ScopedAtomCompleted emptyProgram rigidScope (p (.lit 0)) := by
  intro environment valid
  constructor
  · intro yes; exact False.elim (atomFalse (pAtom ["e"] _ .lit) environment yes)
  · intro support
    rcases support with member | ⟨body, instanceProof, bodyTrue⟩
    · simp [rigidScope, Context.extend, emptyContext] at member
    · have impossible := rigidCover.complete body instanceProof
      simp [rigidCover] at impossible

example : CertifiedRefutation.Refutes model emptyProgram.toKb rigidScope.assumptions (p (.lit 0)) :=
  .scopedAtom rfl (pAtom ["e"] _ .lit) (by simp [p, Term.freeVars])
    (by simp [Context.Closed, rigidScope, Context.extend, emptyContext]) rigidCompleted
    (by simp [rigidScope, Context.extend, emptyContext]) rigidCover (by simp [rigidCover])

example : (p (.var "e")).freeVars ≠ [] := by simp [p, Term.freeVars]

-- A failed hypothetical search in a body is not itself a body refutation.
private def r : T := .app "r" []
private def hypothetical : P := ⟨[.definite r [.imp (p (.lit 0)) (q (.lit 0))]], by
  intro clause member; simp at member; subst clause
  apply IsClause.definite (.app (by decide) (by simp))
  apply SafeGoal.conj
  · exact .imp (.atom (pAtom (p (.lit 0)).freeVars _ .lit)) (by simp [p, Term.freeVars])
      (.basic (.atom (.app (by decide) (by intro arg member; simp at member; subst arg; exact .lit))))
  · exact .basic .truth⟩
private def rInterpretation (symbol : String) (args : List (DataKey Nat String)) : Prop :=
  symbol = "r" ∧ args = []
private def rModel := Model.herbrand "ho_apply" rInterpretation
private theorem hypotheticalInstance : Instance hypothetical emptyContext r [.imp (p (.lit 0)) (q (.lit 0))] :=
  .intro (σ := Term.var) (head := r) (body := [.imp (p (.lit 0)) (q (.lit 0))])
    (by simp [hypothetical]) (Substitutes.identity _)
    (.cons (Substitutes.identity _) .nil)
    (by intro goal member; simp at member; subst goal
        exact .imp (.atom (pAtom [] _ .lit)) (.atom (qAtom [] _ .lit)))
private theorem hypotheticalBodyTrue : CertifiedRefutation.Established rModel []
    (.conjunction [.imp (p (.lit 0)) (q (.lit 0))]) := by
  intro environment valid
  simp only [Term.conjunction, List.foldr_cons, List.foldr_nil, Model.Satisfies, Model.eval]
  apply (rModel.holds_conjunction _ _).mpr
  refine ⟨(rModel.holds_implication _ _).mpr ?_, rModel.holds_top⟩
  intro impossible
  simp [p, rModel, Model.eval, Model.herbrand, resolveAtom, rInterpretation] at impossible
private theorem rCompleted : rModel.ScopedAtomCompleted hypothetical emptyContext r := by
  intro environment valid
  constructor
  · intro yes; exact Or.inr ⟨_, hypotheticalInstance, hypotheticalBodyTrue environment valid⟩
  · intro support
    simp [r, rModel, Model.Satisfies, Model.eval, Model.herbrand, resolveAtom, rInterpretation]

example : ¬ CertifiedRefutation.Refutes rModel hypothetical.toKb []
    (.conjunction [.imp (p (.lit 0)) (q (.lit 0))]) := by
  intro refuted
  exact refuted.not_established (Model.herbrand_complement rInterpretation) (fun _ => rModel.inhabitant)
    (by intro assumption member; cases member) hypotheticalBodyTrue

example : ¬ CertifiedRefutation.Refutes rModel hypothetical.toKb [] r := by
  intro refuted
  exact refuted.not_established (Model.herbrand_complement rInterpretation) (fun _ => rModel.inhabitant)
    (by intro assumption member; cases member)
    (CertifiedRefutation.Established.ofScopedInstance rModel rCompleted hypotheticalInstance hypotheticalBodyTrue)

private theorem programModels : model.Models program.toKb := by
  intro clause member environment
  change clause ∈ program.clauses at member
  simp [program] at member
  subst clause
  simp only [Model.Satisfies, HornClause.toFormula, Term.conjunction, List.foldr_cons, List.foldr_nil, Model.eval]
  apply (model.holds_implication _ _).mpr
  intro bodyTrue
  have premise := ((model.holds_conjunction _ _).mp bodyTrue).1
  exact False.elim (atomFalse (pAtom ["x"] (.var "x") (.parameter (by simp))) environment premise)

example : ¬ Derives "ho_apply" program.toKb [] .falsity
    (CertifiedRefutation.failureEvidence model program.toKb) :=
  CertifiedRefutation.consistent model programModels (Model.herbrand_complement falseInterpretation)
