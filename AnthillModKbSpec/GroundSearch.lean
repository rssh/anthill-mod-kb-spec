import AnthillModKbSpec.Derivation

namespace AnthillModKbSpec.GroundSearch

/-- Ground data in the first search fragment: literals and constructor trees. -/
inductive IsData : Term Variable Literal Symbol → Prop where
  | lit : IsData (.lit value)
  | app (args : ∀ arg ∈ arguments, IsData arg) : IsData (.app symbol arguments)

/-- Ordinary ground atoms. The designated `ho_apply` symbol is reserved: this
first fragment does not treat it as an uninterpreted predicate. -/
inductive IsAtom (hoApplySymbol : Symbol) : Term Variable Literal Symbol → Prop where
  | app (ordinary : symbol ≠ hoApplySymbol)
      (args : ∀ arg ∈ arguments, IsData arg) : IsAtom hoApplySymbol (.app symbol arguments)

/-- Supported ground goals, using the shared syntax. There are no variables,
quantifiers, nested implications, disjunctions, or higher-order applications yet. -/
inductive IsGoal (hoApplySymbol : Symbol) : Term Variable Literal Symbol → Prop where
  | atom (ground : IsAtom hoApplySymbol atom) : IsGoal hoApplySymbol atom
  | truth : IsGoal hoApplySymbol .truth
  | falsity : IsGoal hoApplySymbol .falsity
  | conj (left : IsGoal hoApplySymbol a) (right : IsGoal hoApplySymbol b) :
      IsGoal hoApplySymbol (.conj a b)
  | defaultNeg (body : IsGoal hoApplySymbol goal) : IsGoal hoApplySymbol (.defaultNeg goal)

/-- Definite ground clauses only. Goal clauses (integrity constraints) are
excluded from this first fragment. Bodies may include negation as failure. -/
inductive IsClause (hoApplySymbol : Symbol) : HornClause Variable Literal Symbol → Prop where
  | definite (head : IsAtom hoApplySymbol atom)
      (body : ∀ goal ∈ goals, IsGoal hoApplySymbol goal) :
      IsClause hoApplySymbol (.definite atom goals)

/-- A finite presentation of a ground logical KB. Selection uses membership,
so order and duplicates have no semantic effect. -/
structure Program (Variable Literal Symbol : Type) (hoApplySymbol : Symbol) where
  clauses : List (HornClause Variable Literal Symbol)
  wellFormed : ∀ clause ∈ clauses, IsClause hoApplySymbol clause

/-- Local context restricted to ground atomic facts. Richer scoped assumptions
will require an extension of this fragment. -/
structure Context (Variable Literal Symbol : Type) (hoApplySymbol : Symbol) where
  assumptions : ProofContext Variable Literal Symbol
  wellFormed : ∀ atom ∈ assumptions, IsAtom hoApplySymbol atom

/-- Forget the finite presentation, retaining the logical set of clauses. -/
def Program.toKb (program : Program Variable Literal Symbol hoApplySymbol) :
    LogicalKb Variable Literal Symbol := fun clause => clause ∈ program.clauses

variable {Variable Literal Symbol : Type} {hoApplySymbol : Symbol}

mutual
/-- A finite success certificate. It selects one successful clause, or a local
fact. Negation succeeds from a finite failure certificate of its operand. -/
inductive Succeeds (program : Program Variable Literal Symbol hoApplySymbol)
    (context : Context Variable Literal Symbol hoApplySymbol) :
    Term Variable Literal Symbol → Prop where
  | assumption (ground : IsAtom hoApplySymbol (.app symbol args))
      (member : Term.app symbol args ∈ context.assumptions) :
      Succeeds program context (.app symbol args)
  | clause (ground : IsAtom hoApplySymbol (.app symbol args))
      (member : HornClause.definite (.app symbol args) body ∈ program.clauses)
      (proof : Succeeds program context (.conjunction body)) :
      Succeeds program context (.app symbol args)
  | truth : Succeeds program context .truth
  | conj (left : Succeeds program context a) (right : Succeeds program context b) :
      Succeeds program context (.conj a b)
  | defaultNeg (refuted : Fails program context goal) :
      Succeeds program context (.defaultNeg goal)

/-- A finite complete-failure certificate. An atom fails only when it is not a
local fact and EVERY clause defining it has a failing body. The list of clauses
is finite. With no applicable clauses, the universal premise is vacuous.
There is no rule turning recursion, a depth limit, or an unfinished search into
failure. Both judgments are inductive and use only positive recursive premises. -/
inductive Fails (program : Program Variable Literal Symbol hoApplySymbol)
    (context : Context Variable Literal Symbol hoApplySymbol) :
    Term Variable Literal Symbol → Prop where
  | atom (ground : IsAtom hoApplySymbol (.app symbol args))
      (absent : Term.app symbol args ∉ context.assumptions)
      (allClauses : ∀ body, HornClause.definite (.app symbol args) body ∈ program.clauses →
        Fails program context (.conjunction body)) : Fails program context (.app symbol args)
  | falsity : Fails program context .falsity
  | conjLeft (left : Fails program context a) (right : IsGoal hoApplySymbol b) :
      Fails program context (.conj a b)
  | conjRight (left : IsGoal hoApplySymbol a) (right : Fails program context b) :
      Fails program context (.conj a b)
  | defaultNeg (proof : Succeeds program context goal) :
      Fails program context (.defaultNeg goal)
end

variable {program : Program Variable Literal Symbol hoApplySymbol}
  {context : Context Variable Literal Symbol hoApplySymbol}
  {goal : Term Variable Literal Symbol}

/-- Success and complete failure never both have certificates. The mutual
induction also establishes the symmetric property for failure certificates.
This concerns these judgments, not arbitrary raw logical KBs. -/
theorem succeeds_not_fails (proof : Succeeds program context goal) :
    ¬ Fails program context goal := by
  refine Succeeds.rec
    (motive_1 := fun goal _ => ¬ Fails program context goal)
    (motive_2 := fun goal _ => ¬ Succeeds program context goal)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ proof
  · intro symbol args ground member refuted
    cases refuted with
    | atom _ absent _ => exact absent member
  · intro symbol args body ground member bodyProof ih refuted
    cases refuted with
    | atom _ _ allClauses => exact ih (allClauses _ member)
  · intro refuted; cases refuted
  · intro a b left right ihLeft ihRight refuted
    cases refuted with
    | conjLeft failed _ => exact ihLeft failed
    | conjRight _ failed => exact ihRight failed
  · intro goal refuted ih failed
    cases failed with
    | defaultNeg proof => exact ih proof
  · intro symbol args ground absent allClauses ih proof
    cases proof with
    | assumption _ member => exact absent member
    | clause _ member bodyProof => exact ih _ member bodyProof
  · intro proof; cases proof
  · intro a b failed ground ih proof
    cases proof with
    | conj left _ => exact ih left
  · intro a b ground failed ih proof
    cases proof with
    | conj _ right => exact ih right
  · intro goal proof ih failed
    cases failed with
    | defaultNeg refuted => exact ih refuted

/-- The symmetric orientation of certificate consistency. -/
theorem fails_not_succeeds (refuted : Fails program context goal) :
    ¬ Succeeds program context goal := fun proof => succeeds_not_fails proof refuted

/-- Every failure certificate concerns a well-formed ground goal. -/
theorem fails_isGoal (refuted : Fails program context goal) : IsGoal hoApplySymbol goal := by
  refine Fails.rec
    (motive_1 := fun goal _ => IsGoal hoApplySymbol goal)
    (motive_2 := fun goal _ => IsGoal hoApplySymbol goal)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ refuted
  · intro symbol args ground member; exact .atom ground
  · intro symbol args body ground member proof ih; exact .atom ground
  · exact .truth
  · intro a b left right ihLeft ihRight; exact .conj ihLeft ihRight
  · intro goal refuted ih; exact .defaultNeg ih
  · intro symbol args ground absent allClauses ih; exact .atom ground
  · exact .falsity
  · intro a b left right ih; exact .conj ih right
  · intro a b left right ih; exact .conj left ih
  · intro goal proof ih; exact .defaultNeg ih

variable [DecidableEq Variable]

/-- Ground data contain no free variable names. -/
theorem IsData.closed (proof : IsData (Variable := Variable) term) : term.freeVars = [] := by
  induction proof with
  | lit => simp [Term.freeVars]
  | app args ih => simpa only [Term.freeVars] using List.flatMap_eq_nil_iff.mpr ih

/-- Ground goals contain no free variable names. -/
theorem IsGoal.closed (proof : IsGoal hoApplySymbol (Variable := Variable) goal) :
    goal.freeVars = [] := by
  induction proof with
  | atom ground =>
      cases ground with
      | app ordinary args =>
          simpa only [Term.freeVars] using
            List.flatMap_eq_nil_iff.mpr (fun arg member => (args arg member).closed)
  | truth => simp [Term.freeVars]
  | falsity => simp [Term.freeVars]
  | conj left right ihLeft ihRight => simp [Term.freeVars, ihLeft, ihRight]
  | defaultNeg body ih => simpa only [Term.freeVars] using ih

private theorem identityArgs {args : List (Term Variable Literal Symbol)}
    (proof : ∀ arg ∈ args, Substitutes Term.var arg arg) :
    SubstitutesList Term.var args args := by
  induction args with
  | nil => exact .nil
  | cons arg args ih =>
      exact .cons (proof arg (by simp)) (ih (fun a member => proof a (by simp [member])))

private theorem dataIdentity (proof : IsData (Variable := Variable) term) :
    Substitutes Term.var term term := by
  induction proof with
  | lit => exact .lit
  | app args ih => exact .app (identityArgs ih)

private theorem atomIdentity (proof : IsAtom hoApplySymbol (Variable := Variable) atom) :
    Substitutes Term.var atom atom := by
  cases proof with
  | app ordinary args => exact .app (identityArgs (fun a member => dataIdentity (args a member)))

private theorem goalIdentity (proof : IsGoal hoApplySymbol (Variable := Variable) goal) :
    Substitutes Term.var goal goal := by
  induction proof with
  | atom ground => exact atomIdentity ground
  | truth => exact .truth
  | falsity => exact .falsity
  | conj left right ihLeft ihRight => exact .conj ihLeft ihRight
  | defaultNeg body ih => exact .defaultNeg ih

omit [DecidableEq Variable] in
private theorem conjunction_isGoal {goals : List (Term Variable Literal Symbol)}
    (proof : ∀ goal ∈ goals, IsGoal hoApplySymbol goal) :
    IsGoal hoApplySymbol (.conjunction goals) := by
  induction goals with
  | nil => exact .truth
  | cons goal goals ih =>
      exact .conj (proof goal (by simp)) (ih (fun a member => proof a (by simp [member])))

/-- Concrete finite-failure evidence for this ground program and atomic context.
Equality guards prevent reuse under a different KB, context, or builtin symbol. -/
def failureEvidence (program : Program Variable Literal Symbol hoApplySymbol)
    (context : Context Variable Literal Symbol hoApplySymbol) : NafFailure Variable Literal Symbol :=
  fun actualSymbol actualKb actualContext goal =>
    actualSymbol = hoApplySymbol ∧ actualKb = program.toKb ∧
      actualContext = context.assumptions ∧ Fails program context goal

/-- Every ground success certificate is a proof in the declarative calculus,
using the ground failure judgment as its NAF evidence. This is a connection
between the two specifications, not yet model-theoretic soundness or resolver
completeness. -/
theorem succeeds_toDerives (proof : Succeeds program context goal) :
    Derives hoApplySymbol program.toKb context.assumptions goal
      (failureEvidence program context) := by
  refine Succeeds.rec
    (motive_1 := fun goal _ => Derives hoApplySymbol program.toKb context.assumptions goal
      (failureEvidence program context))
    (motive_2 := fun _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ proof
  · intro symbol args ground member; exact .assumption member
  · intro symbol args body ground member bodyProof ih
    have wellFormed := program.wellFormed _ member
    cases wellFormed with
    | definite headValid bodyValid =>
        exact .clause member (atomIdentity ground)
          (goalIdentity (conjunction_isGoal bodyValid)) ih
  · exact .truth
  · intro a b left right ihLeft ihRight; exact .conjIntro ihLeft ihRight
  · intro goal refuted ih
    exact .defaultNegIntro (fails_isGoal refuted).closed ⟨rfl, rfl, rfl, refuted⟩
  · intros; trivial
  · trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

end AnthillModKbSpec.GroundSearch
