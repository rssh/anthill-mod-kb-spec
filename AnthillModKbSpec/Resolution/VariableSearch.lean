import AnthillModKbSpec.Resolution.P0.GroundSearch

namespace AnthillModKbSpec.VariableSearch

variable {Variable Literal Symbol : Type} [DecidableEq Variable] {hoApplySymbol : Symbol}

/-- First-order data templates. Variables share the existing term carrier. -/
inductive IsData : Term Variable Literal Symbol → Prop where
  | var : IsData (.var name)
  | lit : IsData (.lit value)
  | app (args : ∀ arg ∈ arguments, IsData arg) : IsData (.app symbol arguments)

inductive IsAtom (hoApplySymbol : Symbol) : Term Variable Literal Symbol → Prop where
  | app (ordinary : symbol ≠ hoApplySymbol)
      (args : ∀ arg ∈ arguments, IsData arg) : IsAtom hoApplySymbol (.app symbol arguments)

inductive IsGoal (hoApplySymbol : Symbol) : Term Variable Literal Symbol → Prop where
  | atom (valid : IsAtom hoApplySymbol atom) : IsGoal hoApplySymbol atom
  | truth : IsGoal hoApplySymbol .truth
  | falsity : IsGoal hoApplySymbol .falsity
  | conj (left : IsGoal hoApplySymbol a) (right : IsGoal hoApplySymbol b) :
      IsGoal hoApplySymbol (.conj a b)
  | defaultNeg (body : IsGoal hoApplySymbol goal) : IsGoal hoApplySymbol (.defaultNeg goal)

/-- Syntactic binding safety. A positive atom supplies values for its variables;
conjunction passes these names left to right. NAF may use only names already
known. This prevents an arbitrary grounding from making `not p(X)` succeed when
X is actually unbound. The judgments below describe ground answers, not most
general unifiers or an executable enumeration strategy. -/
inductive SafeGoal (hoApplySymbol : Symbol) : List Variable → Term Variable Literal Symbol →
    List Variable → Prop where
  | atom (valid : IsAtom hoApplySymbol (.app symbol args)) :
      SafeGoal hoApplySymbol known (.app symbol args) ((Term.app symbol args).freeVars ++ known)
  | truth : SafeGoal hoApplySymbol known .truth known
  | falsity : SafeGoal hoApplySymbol known .falsity known
  | conj (left : SafeGoal hoApplySymbol before a middle)
      (right : SafeGoal hoApplySymbol middle b after) :
      SafeGoal hoApplySymbol before (.conj a b) after
  | defaultNeg (valid : IsGoal hoApplySymbol goal)
      (bound : ∀ name ∈ goal.freeVars, name ∈ known) :
      SafeGoal hoApplySymbol known (.defaultNeg goal) known

/-- Safe first-order clause templates. Head variables are fixed by a ground
query; positive body goals can supply additional, clause-local variables. -/
inductive IsClause (hoApplySymbol : Symbol) : HornClause Variable Literal Symbol → Prop where
  | definite (head : IsAtom hoApplySymbol atom)
      (body : SafeGoal hoApplySymbol atom.freeVars (.conjunction goals) after) :
      IsClause hoApplySymbol (.definite atom goals)

structure Program (Variable Literal Symbol : Type) [DecidableEq Variable]
    (hoApplySymbol : Symbol) where
  clauses : List (HornClause Variable Literal Symbol)
  wellFormed : ∀ clause ∈ clauses, IsClause hoApplySymbol clause

/-- Local facts remain ground; variables in assumptions must not be silently
reinterpreted as universally quantified clause variables. -/
abbrev Context := GroundSearch.Context

def Program.toKb (program : Program Variable Literal Symbol hoApplySymbol) :
    LogicalKb Variable Literal Symbol := fun clause => clause ∈ program.clauses

/-- A witnessed ground instance of a clause defining the given atom. One
simultaneous substitution is shared by its head and entire body. Every use may
choose a different substitution, so source variable names do not leak across
clause uses. No whole-domain enumeration is required for a success witness. -/
inductive Instance (program : Program Variable Literal Symbol hoApplySymbol)
    (atom : Term Variable Literal Symbol) : List (Term Variable Literal Symbol) → Prop where
  | intro (member : HornClause.definite head body ∈ program.clauses)
      (headInstance : Substitutes σ head atom)
      (bodyInstance : SubstitutesList σ body grounded)
      (valid : ∀ goal ∈ grounded, GroundSearch.IsGoal hoApplySymbol goal) :
      Instance program atom grounded

/-- An exhausted generator of ground body alternatives for this atom.
Generators may propose witnesses for success without this certificate, but
failure requires both soundness and complete coverage. Completeness ranges over
ALL possible ground instances, not just values emitted by a finite sample.

The value domain is not restricted to the listed values. An infinite generator
that cannot be exhausted supplies no such certificate. Symbolic refutations of
infinite instance families are a later extension. -/
structure ExhaustedInstances (program : Program Variable Literal Symbol hoApplySymbol)
    (atom : Term Variable Literal Symbol) where
  bodies : List (List (Term Variable Literal Symbol))
  sound : ∀ body ∈ bodies, Instance program atom body
  complete : ∀ body, Instance program atom body → body ∈ bodies

mutual
/-- Ground-query success using variable-bearing clause templates. -/
inductive Succeeds (program : Program Variable Literal Symbol hoApplySymbol)
    (context : Context Variable Literal Symbol hoApplySymbol) : Term Variable Literal Symbol → Prop where
  | assumption (ground : GroundSearch.IsAtom hoApplySymbol (.app symbol args))
      (member : Term.app symbol args ∈ context.assumptions) :
      Succeeds program context (.app symbol args)
  | clause (ground : GroundSearch.IsAtom hoApplySymbol (.app symbol args))
      (instantiation : Instance program (.app symbol args) body)
      (proof : Succeeds program context (.conjunction body)) :
      Succeeds program context (.app symbol args)
  | truth : Succeeds program context .truth
  | conj (left : Succeeds program context a) (right : Succeeds program context b) :
      Succeeds program context (.conj a b)
  | defaultNeg (refuted : Fails program context goal) :
      Succeeds program context (.defaultNeg goal)

/-- Failure requires a finite exhaustive generator for the ground body
alternatives and a failure certificate for each. Missing generator coverage,
recursion, and unbound NAF operands are never interpreted as failure. -/
inductive Fails (program : Program Variable Literal Symbol hoApplySymbol)
    (context : Context Variable Literal Symbol hoApplySymbol) : Term Variable Literal Symbol → Prop where
  | atom (ground : GroundSearch.IsAtom hoApplySymbol (.app symbol args))
      (absent : Term.app symbol args ∉ context.assumptions)
      (generator : ExhaustedInstances program (.app symbol args))
      (allBodies : ∀ body ∈ generator.bodies, Fails program context (.conjunction body)) :
      Fails program context (.app symbol args)
  | falsity : Fails program context .falsity
  | conjLeft (left : Fails program context a) (right : GroundSearch.IsGoal hoApplySymbol b) :
      Fails program context (.conj a b)
  | conjRight (left : GroundSearch.IsGoal hoApplySymbol a) (right : Fails program context b) :
      Fails program context (.conj a b)
  | defaultNeg (proof : Succeeds program context goal) :
      Fails program context (.defaultNeg goal)
end

variable {program : Program Variable Literal Symbol hoApplySymbol}
  {context : Context Variable Literal Symbol hoApplySymbol}
  {goal : Term Variable Literal Symbol}

/-- A non-ground query answer is one shared grounding of the query with a
success certificate. Binding safety is checked before grounding, so a free
variable under NAF cannot acquire a value merely by choosing a witness here.
Answers describe ground instances, not most-general symbolic answers. -/
inductive Answers (program : Program Variable Literal Symbol hoApplySymbol)
    (context : Context Variable Literal Symbol hoApplySymbol)
    (query : Term Variable Literal Symbol) (σ : Substitution Variable Literal Symbol) : Prop where
  | intro (safe : SafeGoal hoApplySymbol [] query known)
      (grounding : Substitutes σ query grounded)
      (valid : GroundSearch.IsGoal hoApplySymbol grounded)
      (proof : Succeeds program context grounded) : Answers program context query σ

/-- Exhaustion of the possible groundings of a query. This is a completeness
certificate, not a claim that every variable query has finitely many instances. -/
structure ExhaustedGroundings (query : Term Variable Literal Symbol) where
  goals : List (Term Variable Literal Symbol)
  sound : ∀ goal ∈ goals, ∃ σ, Substitutes σ query goal ∧ GroundSearch.IsGoal hoApplySymbol goal
  complete : ∀ σ goal, Substitutes σ query goal → GroundSearch.IsGoal hoApplySymbol goal → goal ∈ goals

/-- Exhaustion of the defining-clause alternatives for an atomic variable query.
This need not enumerate values having no matching clause: a missing predicate
has an empty candidate generator even over an infinite value domain. -/
structure ExhaustedQueryInstances (program : Program Variable Literal Symbol hoApplySymbol)
    (query : Term Variable Literal Symbol) where
  bodies : List (List (Term Variable Literal Symbol))
  sound : ∀ body ∈ bodies, ∃ σ atom, Substitutes σ query atom ∧
    GroundSearch.IsAtom hoApplySymbol atom ∧ Instance program atom body
  complete : ∀ σ atom body, Substitutes σ query atom → GroundSearch.IsAtom hoApplySymbol atom →
    Instance program atom body → body ∈ bodies

/-- All answers of a safe query are refuted, with explicit finite exhaustion.
The atomic rule exhausts matching clause instances rather than all values.
Unbound NAF operands cannot satisfy either rule and therefore flounder. -/
inductive QueryFails (program : Program Variable Literal Symbol hoApplySymbol)
    (context : Context Variable Literal Symbol hoApplySymbol) (query : Term Variable Literal Symbol) : Prop where
  | intro (safe : SafeGoal hoApplySymbol [] query known)
      (generator : ExhaustedGroundings (hoApplySymbol := hoApplySymbol) query)
      (allGoals : ∀ goal ∈ generator.goals, Fails program context goal) :
      QueryFails program context query
  | atom (valid : IsAtom hoApplySymbol query)
      (absent : ∀ σ atom, Substitutes σ query atom → GroundSearch.IsAtom hoApplySymbol atom →
        atom ∉ context.assumptions)
      (generator : ExhaustedQueryInstances program query)
      (allBodies : ∀ body ∈ generator.bodies, Fails program context (.conjunction body)) :
      QueryFails program context query

/-- Instance coverage is essential to disjointness: every successful witness
must be included by a failure generator, including clause-local witnesses. -/
theorem succeeds_not_fails (proof : Succeeds program context goal) :
    ¬ Fails program context goal := by
  refine Succeeds.rec
    (motive_1 := fun goal _ => ¬ Fails program context goal)
    (motive_2 := fun goal _ => ¬ Succeeds program context goal)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ proof
  · intro symbol args ground member refuted
    cases refuted with
    | atom _ absent _ _ => exact absent member
  · intro symbol args body ground inst bodyProof ih refuted
    cases refuted with
    | atom _ _ generator allBodies => exact ih (allBodies _ (generator.complete _ inst))
  · intro refuted; cases refuted
  · intro a b left right ihLeft ihRight refuted
    cases refuted with
    | conjLeft failed _ => exact ihLeft failed
    | conjRight _ failed => exact ihRight failed
  · intro goal refuted ih failed
    cases failed with
    | defaultNeg proof => exact ih proof
  · intro symbol args ground absent generator allBodies ih proof
    cases proof with
    | assumption _ member => exact absent member
    | clause _ inst bodyProof => exact ih _ (generator.complete _ inst) bodyProof
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

theorem fails_not_succeeds (refuted : Fails program context goal) :
    ¬ Succeeds program context goal := fun proof => succeeds_not_fails proof refuted

/-- Failure of a variable query rules out every ground answer substitution. -/
theorem queryFails_no_answer (refuted : QueryFails program context query) :
    ¬ Answers program context query σ := by
  intro answer
  cases refuted with
  | intro safe generator allGoals =>
      cases answer with
      | intro safeAnswer grounding valid proof =>
          exact succeeds_not_fails proof (allGoals _ (generator.complete _ _ grounding valid))
  | atom valid absent generator allBodies =>
      cases valid with
      | app ordinary args =>
          cases answer with
          | intro safe grounding ground proof =>
              cases grounding with
              | app argumentInstances =>
                  cases proof with
                  | assumption atom member => exact absent _ _ (.app argumentInstances) atom member
                  | clause atom inst bodyProof =>
                      exact succeeds_not_fails bodyProof
                        (allBodies _ (generator.complete _ _ _ (.app argumentInstances) atom inst))

theorem fails_isGoal (refuted : Fails program context goal) : GroundSearch.IsGoal hoApplySymbol goal := by
  refine Fails.rec
    (motive_1 := fun goal _ => GroundSearch.IsGoal hoApplySymbol goal)
    (motive_2 := fun goal _ => GroundSearch.IsGoal hoApplySymbol goal)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ refuted
  · intro symbol args ground member; exact .atom ground
  · intro symbol args body ground inst proof ih; exact .atom ground
  · exact .truth
  · intro a b left right ihLeft ihRight; exact .conj ihLeft ihRight
  · intro goal refuted ih; exact .defaultNeg ih
  · intro symbol args ground absent generator allBodies ih; exact .atom ground
  · exact .falsity
  · intro a b left right ih; exact .conj ih right
  · intro a b left right ih; exact .conj left ih
  · intro goal proof ih; exact .defaultNeg ih

/-- Adapt certified failure without changing the surrounding sequent. -/
def failureEvidence (program : Program Variable Literal Symbol hoApplySymbol)
    (context : Context Variable Literal Symbol hoApplySymbol) : NafFailure Variable Literal Symbol :=
  fun actualSymbol actualKb actualContext goal =>
    actualSymbol = hoApplySymbol ∧ actualKb = program.toKb ∧
      actualContext = context.assumptions ∧ Fails program context goal

private theorem conjunctionSubstitution {σ : Substitution Variable Literal Symbol}
    (proof : SubstitutesList σ before after) :
    Substitutes σ (.conjunction before) (.conjunction after) := by
  induction before generalizing after with
  | nil => cases proof; exact .truth
  | cons head tail ih =>
      cases proof with
      | cons first rest => exact .conj first (ih rest)

/-- Successful variable-clause search embeds in the full declarative calculus
with the original schematic KB, not a materialized replacement KB. -/
theorem succeeds_toDerives (proof : Succeeds program context goal) :
    Derives hoApplySymbol program.toKb context.assumptions goal
      (failureEvidence program context) := by
  refine Succeeds.rec
    (motive_1 := fun goal _ => Derives hoApplySymbol program.toKb context.assumptions goal
      (failureEvidence program context))
    (motive_2 := fun _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ proof
  · intro symbol args ground member; exact .assumption member
  · intro symbol args body ground inst bodyProof ih
    cases inst with
    | intro member headInstance bodyInstance valid =>
        exact .clause member headInstance (conjunctionSubstitution bodyInstance) ih
  · exact .truth
  · intro a b left right ihLeft ihRight; exact .conjIntro ihLeft ihRight
  · intro goal refuted ih
    exact .defaultNegIntro (fails_isGoal refuted).closed ⟨rfl, rfl, rfl, refuted⟩
  · intros; trivial
  · trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

/-- An answer substitution produces a derivable ground instance of its query. -/
theorem answers_toDerives (answer : Answers program context query σ) :
    ∃ grounded, Substitutes σ query grounded ∧
      Derives hoApplySymbol program.toKb context.assumptions grounded
        (failureEvidence program context) := by
  cases answer with
  | intro safe grounding valid proof => exact ⟨_, grounding, succeeds_toDerives proof⟩

end AnthillModKbSpec.VariableSearch
