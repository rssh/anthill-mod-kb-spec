import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Semantics AnthillModKbSpec.InductiveDomains
open AnthillModKbSpec.InductionModel

private def interpretation : InductiveSoundness.Interpretation family kb Value .hoApply :=
  ⟨model, membershipSymbol, realizes, kb_models, complement⟩

-- The advertised example contains membership, induction, and predicate rules.
example : natZero ∈ kb ∧ natSucc ∈ kb ∧ inductionRule ∈ kb ∧ evenSuccSucc ∈ kb := by simp [kb]

example : Nonempty (InductiveSoundness.Interpretation family kb Value .hoApply) := ⟨interpretation⟩

private theorem base : Derives .hoApply kb [] (reachable zero)
    (CertifiedRefutation.failureEvidence model kb) :=
  .clause (head := reachable zero) (body := []) (σ := Term.var)
    (by simp [kb, reachableZero]) (Substitutes.identity _) .truth .truth

example (environment : Environment String Value) : model.Satisfies environment (reachable zero) :=
  InductiveSoundness.declarative_sound interpretation base environment (by intro assumption member; cases member)

example (environment : Environment String Value) : model.Satisfies environment (.defaultNeg (.falsity : T)) :=
  InductiveSoundness.declarative_sound interpretation
    ((CertifiedRefutation.Refutes.falsity (model := model) (kb := kb) (context := [])).toDerives
      (by simp [Term.freeVars])) environment
    (by intro assumption member; cases member)

example : ¬ Derives .hoApply kb [] .falsity (CertifiedRefutation.failureEvidence model kb) :=
  InductiveSoundness.declarative_consistent interpretation

example : ¬ Derives .hoApply kb [] .falsity :=
  InductiveSoundness.positive_consistent_of_model_exists ⟨interpretation⟩

-- The same headline theorem applies before adding predicate definitions.
example : ¬ Derives .hoApply inductionKb [] .falsity :=
  InductiveSoundness.positive_consistent_of_model_exists (family := family)
    ⟨⟨model, membershipSymbol, realizes, inductionKb_models, complement⟩⟩

example (environment : Environment String Value) :
    model.Satisfies environment ((family.forallAll "x" (even (.var "x"))).toTerm membershipSymbol) ↔
      ∀ value : family.Generated, model.Satisfies
        (update environment "x" (denote model value.val)) (even (.var "x")) :=
  InductiveSoundness.forallAll_iff interpretation "x" (even (.var "x")) environment

private theorem noCounterexample : CounterexampleSearch.Fails model sigma []
    (family.forallAll "x" (reachable (.var "x"))) := by
  constructor
  intro tree ⟨domain, selected, member⟩
  obtain ⟨n, same⟩ := member_denote member
  constructor
  intro environment assumptions
  simp only [FiniteFamily.forallAll, reachable, Model.Satisfies, Model.eval,
    List.map_cons, List.map_nil, update, ite_true, same]
  exact reachable_at_nat n

example (environment : Environment String Value) :
    model.Satisfies environment ((family.forallAll "x" (reachable (.var "x"))).toTerm membershipSymbol) :=
  InductiveSoundness.forall_of_counterexample_failure interpretation "x" (reachable (.var "x"))
    noCounterexample environment (by intro assumption member; cases member)

-- Scoped success has the same theorem when its program represents the KB.
example {D V L S A : Type} [DecidableEq V] [FreshNames V] {ha : S}
    {family : FiniteFamily D S} {program : ScopedSearch.Program V L S ha}
    (meaning : InductiveSoundness.Interpretation family program.toKb A ha)
    {scope : ScopedSearch.Context V L S ha} {goal : Term V L S}
    (proof : CertifiedScopedSearch.Succeeds meaning.model program scope goal) :
    ∀ environment, meaning.model.ContextHolds environment scope.assumptions →
      meaning.model.Satisfies environment goal :=
  InductiveSoundness.scoped_sound meaning rfl proof
