import AnthillModKbSpec.Archive.InductionGoals

namespace AnthillModKbSpec.Archive.InductiveResolution

open Semantics InductiveDomains InductionGoals

/-- An ordinary logical KB plus an optional explicit induction-scheme
declaration. Scheme declarations authorize generation of constructor goals. -/
structure Program (family : FiniteFamily Domain Symbol) (Variable Literal : Type) where
  clauses : LogicalKb Variable Literal Symbol
  induction : Option (Scheme family)

variable {Domain Variable Literal Symbol Value : Type} [DecidableEq Variable] [FreshNames Variable]
variable {hoApplySymbol : Symbol} {family : FiniteFamily Domain Symbol}

/-- An executable goal-expansion step. None means no induction declaration;
some goals is the complete constructor-obligation list, not proof success. -/
def Program.inductionGoals (program : Program family Variable Literal)
    (membershipSymbol : Domain → Symbol) (predicates : Domain → Term Variable Literal Symbol) :
    Option (List (Goal Domain Variable Literal Symbol)) :=
  program.induction.map (fun scheme => scheme.obligations (hoApplySymbol := hoApplySymbol) membershipSymbol predicates)

/-- Resolution with explicit InductiveProof goals. Its constructor cases are
recursive proof/search obligations, so their subgoals may use clause search,
local hypotheses, nested induction, or certified NAF. Rigid query parameters
are never substituted by clause application. This is a proof-tree semantics;
an automatic strategy for discovering proof trees is separate. -/
inductive Proves (model : Model Literal Symbol Value hoApplySymbol)
    (program : Program family Variable Literal) (membershipSymbol : Domain → Symbol) :
    ProofContext Variable Literal Symbol → Goal Domain Variable Literal Symbol → Prop where
  | assumption (member : term ∈ context) : Proves model program membershipSymbol context (.formula term)
  | truth : Proves model program membershipSymbol context (.formula .truth)
  | conj (left : Proves model program membershipSymbol context (.formula a))
      (right : Proves model program membershipSymbol context (.formula b)) :
      Proves model program membershipSymbol context (.formula (.conj a b))
  | conjLeft (proof : Proves model program membershipSymbol context (.formula (.conj a b))) :
      Proves model program membershipSymbol context (.formula a)
  | conjRight (proof : Proves model program membershipSymbol context (.formula (.conj a b))) :
      Proves model program membershipSymbol context (.formula b)
  | impIntro (proof : Proves model program membershipSymbol (a :: context) (.formula b)) :
      Proves model program membershipSymbol context (.formula (.imp a b))
  | impElim (proof : Proves model program membershipSymbol context (.formula (.imp a b)))
      (argument : Proves model program membershipSymbol context (.formula a)) :
      Proves model program membershipSymbol context (.formula b)
  | forallIntro (freshContext : FreshForContext eigen context)
      (freshGoal : eigen ∉ (Term.forallVar binder body).freeVars)
      (opening : Substitutes (Substitution.single binder (.var eigen)) body opened)
      (proof : Proves model program membershipSymbol context (.formula opened)) :
      Proves model program membershipSymbol context (.formula (.forallVar binder body))
  | clause (member : HornClause.definite head body ∈ program.clauses)
      (headInstance : Substitutes substitution head instantiatedHead)
      (bodyInstance : Substitutes substitution (.conjunction body) instantiatedBody)
      (proof : Proves model program membershipSymbol context (.formula instantiatedBody)) :
      Proves model program membershipSymbol context (.formula instantiatedHead)
  | hoApplyIntro (proof : Proves model program membershipSymbol context (.formula (.app predicate args))) :
      Proves model program membershipSymbol context (.formula (.hoApply hoApplySymbol (.app predicate []) args))
  | hoApplyElim (proof : Proves model program membershipSymbol context
      (.formula (.hoApply hoApplySymbol (.app predicate []) args))) :
      Proves model program membershipSymbol context (.formula (.app predicate args))
  | defaultNeg (closed : term.freeVars = [])
      (refuted : CertifiedRefutation.Refutes model program.clauses context term) :
      Proves model program membershipSymbol context (.formula (.defaultNeg term))
  | declarative (proof : Derives hoApplySymbol program.clauses context term
      (CertifiedRefutation.failureEvidence model program.clauses)) :
      Proves model program membershipSymbol context (.formula term)
  | scopedSearch {scope : ScopedSearch.Context Variable Literal Symbol hoApplySymbol}
      {source : ScopedSearch.Program Variable Literal Symbol hoApplySymbol}
      (sameKb : source.toKb = program.clauses)
      (proof : CertifiedScopedSearch.Succeeds model source scope term) :
      Proves model program membershipSymbol scope.assumptions (.formula term)
  | counterexample {goal : Universal Domain Variable Literal Symbol}
      (failed : CounterexampleSearch.Fails model family.definitions context goal) :
      Proves model program membershipSymbol context (.formula (goal.toTerm membershipSymbol))
  | induction {scheme : Scheme family} (declared : program.induction = some scheme)
      (predicates : Domain → Term Variable Literal Symbol)
      (cases : ∀ rule ∈ scheme.constructors, Proves model program membershipSymbol context
        (.formula (constructorGoal (hoApplySymbol := hoApplySymbol) family membershipSymbol predicates rule))) :
      Proves model program membershipSymbol context (.inductiveProof predicates)
  | inductionApply (certificate : Proves model program membershipSymbol context (.inductiveProof predicates))
      (member : Proves model program membershipSymbol context (.formula (.app (membershipSymbol domain) [subject]))) :
      Proves model program membershipSymbol context
        (.formula (.hoApply hoApplySymbol (predicates domain) [subject]))

variable {model : Model Literal Symbol Value hoApplySymbol}
variable {program : Program family Variable Literal} {membershipSymbol : Domain → Symbol}
variable {context : ProofContext Variable Literal Symbol} {goal : Goal Domain Variable Literal Symbol}

theorem Proves.induction_from_obligations {scheme : Scheme family}
    (declared : program.induction = some scheme) (predicates : Domain → Term Variable Literal Symbol)
    (solved : ∀ goal ∈ scheme.obligations (hoApplySymbol := hoApplySymbol) membershipSymbol predicates,
      Proves model program membershipSymbol context goal) :
    Proves model program membershipSymbol context (.inductiveProof predicates) := by
  apply Proves.induction declared predicates
  intro rule member
  exact solved _ (List.mem_map.mpr ⟨rule, member, rfl⟩)

omit [FreshNames Variable] in
private theorem instanceRule {head after result : Term Variable Literal Symbol}
    {body : List (Term Variable Literal Symbol)} {substitution : Substitution Variable Literal Symbol}
    (member : HornClause.definite head body ∈ program.clauses)
    (headInstance : Substitutes substitution head result)
    (bodyInstance : Substitutes substitution (.conjunction body) after) :
    Derives hoApplySymbol program.clauses [] (.imp after result) :=
  .impIntro (.clause member headInstance bodyInstance (.assumption (by simp)))

theorem Proves.sound (validKb : model.Models program.clauses)
    (realizes : Realizes model family.definitions membershipSymbol) (negation : model.ComplementNAF)
    (proof : Proves model program membershipSymbol context goal) :
    ∀ environment, model.ContextHolds environment context → goal.Holds model family environment := by
  induction proof with
  | assumption member => intro environment assumptions; exact assumptions _ member
  | truth => intro environment assumptions; simpa only [Goal.Holds, Model.Satisfies, Model.eval] using model.holds_top
  | conj left right ihLeft ihRight =>
      intro environment assumptions
      simp only [Goal.Holds, Model.Satisfies, Model.eval, model.holds_conjunction]
      exact ⟨ihLeft environment assumptions, ihRight environment assumptions⟩
  | conjLeft proof ih =>
      intro environment assumptions
      have result := ih environment assumptions
      simp only [Goal.Holds, Model.Satisfies, Model.eval, model.holds_conjunction] at result
      exact result.1
  | conjRight proof ih =>
      intro environment assumptions
      have result := ih environment assumptions
      simp only [Goal.Holds, Model.Satisfies, Model.eval, model.holds_conjunction] at result
      exact result.2
  | impIntro proof ih =>
      intro environment assumptions
      simp only [Goal.Holds, Model.Satisfies, Model.eval, model.holds_implication]
      intro premise
      apply ih environment
      intro term member
      rcases List.mem_cons.mp member with rfl | member
      · exact premise
      · exact assumptions _ member
  | impElim proof argument ih ihArgument =>
      intro environment assumptions
      have result := ih environment assumptions
      simp only [Goal.Holds, Model.Satisfies, Model.eval, model.holds_implication] at result
      exact result (ihArgument environment assumptions)
  | forallIntro freshContext freshGoal opening proof ih =>
      intro environment assumptions
      simp only [Goal.Holds, Model.Satisfies, Model.eval, model.holds_universal]
      intro value
      have result := ih (update environment _ value) (model.context_fresh environment freshContext value assumptions)
      simp only [Goal.Holds, Model.Satisfies] at result
      rw [model.eval_open_fresh freshGoal opening environment value] at result
      exact result
  | clause member headInstance bodyInstance proof ih =>
      intro environment assumptions
      have rule := instanceRule member headInstance bodyInstance (hoApplySymbol := hoApplySymbol)
      have result := model.positive_sound validKb rule environment (by intro term impossible; cases impossible)
      simp only [Model.Satisfies, Model.eval, model.holds_implication] at result
      exact result (ih environment assumptions)
  | hoApplyIntro proof ih =>
      intro environment assumptions
      simp only [Goal.Holds, Model.Satisfies, Term.hoApply, Model.eval, List.map_cons, List.map_nil]
      have result := ih environment assumptions
      simp only [Goal.Holds, Model.Satisfies, Model.eval] at result
      exact (model.holds_hoApply _ _).mpr result
  | hoApplyElim proof ih =>
      intro environment assumptions
      have result := ih environment assumptions
      simp only [Goal.Holds, Model.Satisfies, Term.hoApply, Model.eval, List.map_cons, List.map_nil] at result ⊢
      exact (model.holds_hoApply _ _).mp result
  | defaultNeg closed refuted => exact refuted.naf negation
  | declarative proof => exact CertifiedRefutation.sound model validKb negation proof
  | scopedSearch sameKb proof =>
      apply proof.sound (negation := negation)
      rw [sameKb]
      exact validKb
  | counterexample failed => exact failed.sound realizes
  | @induction context scheme declared predicates cases ih =>
      intro environment assumptions
      have inductionCases : Induction family.definitions (fun domain tree => model.holds
          (model.application hoApplySymbol [model.eval environment (predicates domain), denote model tree])) := by
        constructor
        intro rule member children members childIH
        exact constructorGoal_sound family model realizes predicates rule environment
          (ih rule ((scheme.exact rule).mp member) environment assumptions) children members childIH
      intro domain tree member
      exact member.induct inductionCases
  | inductionApply certificate member ihCertificate ihMember =>
      intro environment assumptions
      have belongs := ihMember environment assumptions
      simp only [Goal.Holds, Model.Satisfies, Model.eval, List.map_cons, List.map_nil] at belongs
      obtain ⟨tree, generated, same⟩ := (realizes _ _).mp belongs
      have result := ihCertificate environment assumptions _ tree generated
      simpa only [Goal.Holds, Model.Satisfies, Term.hoApply, Model.eval, List.map_cons, List.map_nil, same] using result

theorem Proves.generalize (proof : Proves model program membershipSymbol context (.formula term))
    (binder : Variable) (fresh : FreshForContext binder context) :
    Proves model program membershipSymbol context (.formula (.forallVar binder term)) := by
  apply Proves.forallIntro (eigen := binder) (opened := term) fresh
  · simp [Term.freeVars]
  · have same : Substitution.single binder (.var binder) = (Term.var : Substitution Variable Literal Symbol) := by
      funext name
      by_cases same : name = binder <;> simp [Substitution.single, Substitution.bind, same]
    rw [same]
    exact Substitutes.identity _
  · exact proof

/-- Formula search using induction can itself establish an antecedent for
later certified refutations. This retains the exact original assumptions. -/
theorem Proves.established (validKb : model.Models program.clauses)
    (realizes : Realizes model family.definitions membershipSymbol) (negation : model.ComplementNAF)
    (proof : Proves model program membershipSymbol context (.formula term)) :
    CertifiedRefutation.Established model context term := proof.sound validKb realizes negation

theorem no_falsity (validKb : model.Models program.clauses)
    (realizes : Realizes model family.definitions membershipSymbol) (negation : model.ComplementNAF) :
    ¬ Proves model program membershipSymbol [] (.formula .falsity) := by
  intro proof
  have result := proof.sound validKb realizes negation (fun _ => model.inhabitant)
    (by intro assumption member; cases member)
  exact model.holds_bottom (by simpa only [Goal.Holds, Model.Satisfies, Model.eval] using result)

end AnthillModKbSpec.Archive.InductiveResolution
