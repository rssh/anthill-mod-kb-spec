import AnthillModKbSpec.Resolution.CertifiedScopedSearch
import AnthillModKbSpec.Foundation.MembershipClauses

namespace AnthillModKbSpec.InductiveDomains

open Semantics

variable {Variable Literal Symbol Value Domain : Type} [DecidableEq Variable]
variable {hoApplySymbol : Symbol}

/-- Search for a generated witness whose property fails by NAF. The domain
generator precedes NAF; a fresh rigid parameter is not an enumerated witness. -/
def Universal.counterexample (goal : Universal Domain Variable Literal Symbol)
    (membershipSymbol : Domain → Symbol) : Term Variable Literal Symbol :=
  .existsVar goal.binder (.conj (guard membershipSymbol goal.domains (.var goal.binder)) (.defaultNeg goal.body))

theorem Universal.counterexample_iff (goal : Universal Domain Variable Literal Symbol)
    (model : Model Literal Symbol Value hoApplySymbol) (realizes : Realizes model sigma membershipSymbol)
    (environment : Environment Variable Value) :
    model.Satisfies environment (goal.counterexample membershipSymbol) ↔
      ∃ tree, InUnion sigma goal.domains tree ∧
        model.Satisfies (update environment goal.binder (denote model tree)) (.defaultNeg goal.body) := by
  simp only [Universal.counterexample, Model.Satisfies, Model.eval, model.holds_existential,
    model.holds_conjunction]
  constructor
  · rintro ⟨value, guardTrue, negative⟩
    obtain ⟨domain, selected, member⟩ := (guard_eval model membershipSymbol goal.domains _ (.var goal.binder)).mp guardTrue
    simp only [Model.eval, update, ite_true] at member
    obtain ⟨tree, member, same⟩ := (realizes domain value).mp member
    exact ⟨tree, ⟨domain, selected, member⟩, by simpa only [same] using negative⟩
  · rintro ⟨tree, ⟨domain, selected, member⟩, negative⟩
    refine ⟨denote model tree, ?_, negative⟩
    apply (guard_eval model membershipSymbol goal.domains _ (.var goal.binder)).mpr
    refine ⟨domain, selected, (realizes domain _).mpr ⟨tree, member, ?_⟩⟩
    simp [Model.eval, update]

/-- Logical equivalence underlying the search interpretation. Absence here is
semantic absence of a witness; obtaining it from a search requires coverage. -/
theorem Universal.satisfies_iff_no_counterexample (goal : Universal Domain Variable Literal Symbol)
    (model : Model Literal Symbol Value hoApplySymbol) (realizes : Realizes model sigma membershipSymbol)
    (negation : model.ComplementNAF) (environment : Environment Variable Value) :
    model.Satisfies environment (goal.toTerm membershipSymbol) ↔
      ¬ model.Satisfies environment (goal.counterexample membershipSymbol) := by
  classical
  rw [goal.satisfies_iff model realizes environment, goal.counterexample_iff model realizes environment]
  constructor
  · intro universal ⟨tree, member, negative⟩
    exact model.defaultNegation_coherent _
      (by simpa only [Model.Satisfies, Model.eval] using negative) (universal tree member)
  · intro absent tree member
    apply Classical.byContradiction
    intro missing
    apply absent
    refine ⟨tree, member, ?_⟩
    simp only [Model.Satisfies, Model.eval]
    exact (negation _).mpr missing

theorem Universal.satisfies_iff_counterexample_naf (goal : Universal Domain Variable Literal Symbol)
    (model : Model Literal Symbol Value hoApplySymbol) (realizes : Realizes model sigma membershipSymbol)
    (negation : model.ComplementNAF) (environment : Environment Variable Value) :
    model.Satisfies environment (goal.toTerm membershipSymbol) ↔
      model.Satisfies environment (.defaultNeg (goal.counterexample membershipSymbol)) := by
  rw [goal.satisfies_iff_no_counterexample model realizes negation environment]
  simp only [Model.Satisfies, Model.eval]
  exact (negation _).symm

namespace CounterexampleSearch

/-- A checked failure of the inner NAF query at one generated value: its
positive operand was established. No "unknown" or truncated outcome qualifies. -/
structure Rejected (model : Model Literal Symbol Value hoApplySymbol)
    (context : ProofContext Variable Literal Symbol)
    (goal : Universal Domain Variable Literal Symbol) (tree : Tree Symbol) : Prop where
  established : ∀ environment, model.ContextHolds environment context →
    model.Satisfies (update environment goal.binder (denote model tree)) goal.body

/-- Use a successful proof of the actual constructor instance, with the exact
original context. Substitution is capture-avoiding even for scoped properties. -/
theorem Rejected.ofEstablished {model : Model Literal Symbol Value hoApplySymbol}
    {context : ProofContext Variable Literal Symbol} {goal : Universal Domain Variable Literal Symbol}
    {tree : Tree Symbol} {instantiated : Term Variable Literal Symbol}
    (instantiation : Substitutes (Substitution.single goal.binder tree.toTerm) goal.body instantiated)
    (proof : CertifiedRefutation.Established model context instantiated) : Rejected model context goal tree := by
  constructor
  intro environment assumptions
  have result := proof environment assumptions
  unfold Model.Satisfies at result ⊢
  rw [model.eval_single instantiation, tree.eval_toTerm] at result
  exact result

theorem Rejected.naf_fails {model : Model Literal Symbol Value hoApplySymbol}
    {context : ProofContext Variable Literal Symbol} {goal : Universal Domain Variable Literal Symbol}
    {tree : Tree Symbol} (rejected : Rejected model context goal tree)
    (environment : Environment Variable Value) (assumptions : model.ContextHolds environment context) :
    ¬ model.Satisfies (update environment goal.binder (denote model tree)) (.defaultNeg goal.body) := by
  intro negative
  simp only [Model.Satisfies, Model.eval] at negative
  exact model.defaultNegation_coherent _ negative (rejected.established environment assumptions)

/-- Certified exhaustive failure of generated counterexample search. Coverage
is over every actual member, not a sample or a failed generic rigid query.
This interface admits infinite domains, but does not promise terminating search. -/
structure Fails (model : Model Literal Symbol Value hoApplySymbol)
    (sigma : Definitions Domain Symbol) (context : ProofContext Variable Literal Symbol)
    (goal : Universal Domain Variable Literal Symbol) : Prop where
  exhaustive : ∀ tree, InUnion sigma goal.domains tree → Rejected model context goal tree

theorem Fails.ofCovers {model : Model Literal Symbol Value hoApplySymbol}
    {context : ProofContext Variable Literal Symbol} {goal : Universal Domain Variable Literal Symbol}
    (covers : ∀ domain ∈ goal.domains, Cover sigma domain)
    (checked : ∀ domain selected, ∀ tree ∈ (covers domain selected).values, Rejected model context goal tree) :
    Fails model sigma context goal := by
  constructor
  intro tree ⟨domain, selected, member⟩
  exact checked domain selected tree ((covers domain selected).complete tree member)

theorem Fails.ofInduction {model : Model Literal Symbol Value hoApplySymbol}
    {context : ProofContext Variable Literal Symbol} {goal : Universal Domain Variable Literal Symbol}
    {invariant : Domain → Tree Symbol → Prop}
    (cases : Induction sigma invariant)
    (roots : ∀ domain ∈ goal.domains, ∀ tree, invariant domain tree → Rejected model context goal tree) :
    Fails model sigma context goal := by
  constructor
  intro tree ⟨domain, selected, member⟩
  exact roots domain selected tree (member.induct cases)

theorem Fails.sound {model : Model Literal Symbol Value hoApplySymbol}
    {context : ProofContext Variable Literal Symbol} {goal : Universal Domain Variable Literal Symbol}
    (failed : Fails model sigma context goal) (realizes : Realizes model sigma membershipSymbol)
    (environment : Environment Variable Value) (assumptions : model.ContextHolds environment context) :
    model.Satisfies environment (goal.toTerm membershipSymbol) := by
  apply (goal.satisfies_iff model realizes environment).mpr
  intro tree member
  exact (failed.exhaustive tree member).established environment assumptions

theorem Fails.counterexample_fails {model : Model Literal Symbol Value hoApplySymbol}
    {context : ProofContext Variable Literal Symbol} {goal : Universal Domain Variable Literal Symbol}
    (failed : Fails model sigma context goal) (realizes : Realizes model sigma membershipSymbol)
    (environment : Environment Variable Value) (assumptions : model.ContextHolds environment context) :
    ¬ model.Satisfies environment (goal.counterexample membershipSymbol) := by
  intro counterexample
  obtain ⟨tree, member, negative⟩ := (goal.counterexample_iff model realizes environment).mp counterexample
  exact (failed.exhaustive tree member).naf_fails environment assumptions negative

/-- The actual NAF reading of complete counterexample failure requires a
complement interpretation of NAF. The positive forall theorem needs only coherence. -/
theorem Fails.counterexample_naf {model : Model Literal Symbol Value hoApplySymbol}
    {context : ProofContext Variable Literal Symbol} {goal : Universal Domain Variable Literal Symbol}
    (failed : Fails model sigma context goal) (realizes : Realizes model sigma membershipSymbol)
    (negation : model.ComplementNAF) (environment : Environment Variable Value)
    (assumptions : model.ContextHolds environment context) :
    model.Satisfies environment (.defaultNeg (goal.counterexample membershipSymbol)) := by
  simp only [Model.Satisfies, Model.eval]
  exact (negation _).mpr (failed.counterexample_fails realizes environment assumptions)

theorem Fails.toSucceeds {model : Model Literal Symbol Value hoApplySymbol} [FreshNames Variable]
    {program : ScopedSearch.Program Variable Literal Symbol hoApplySymbol}
    {context : ScopedSearch.Context Variable Literal Symbol hoApplySymbol}
    {goal : Universal Domain Variable Literal Symbol}
    (failed : Fails model sigma context.assumptions goal) (realizes : Realizes model sigma membershipSymbol) :
    CertifiedScopedSearch.Succeeds model program context (goal.toTerm membershipSymbol) := by
  apply CertifiedScopedSearch.Succeeds.guarded realizes
  intro environment assumptions tree member
  exact (failed.exhaustive tree member).established environment assumptions

end CounterexampleSearch
end AnthillModKbSpec.InductiveDomains
