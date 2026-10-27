import AnthillModKbSpec.Foundation.Derivation

namespace AnthillModKbSpec

variable {Variable Literal Symbol : Type} [DecidableEq Variable] {hoApplySymbol : Symbol}

/-- Growing the KB preserves a derivation, provided every NAF premise used under
the old KB is still accepted under the new one. No rule inspects the KB except
by membership, and the local context and freshness conditions are unchanged.
The NAF condition is where closed-world evidence differs: a provider indexed by
the exact KB (as `GroundSearch.failureEvidence` is) does not satisfy it. -/
theorem Derives.mono {kb kb' : LogicalKb Variable Literal Symbol}
    {naf naf' : NafFailure Variable Literal Symbol}
    (clauses : ∀ clause, clause ∈ kb → clause ∈ kb')
    (failures : ∀ context goal, naf hoApplySymbol kb context goal → naf' hoApplySymbol kb' context goal)
    {context : ProofContext Variable Literal Symbol} {goal : Formula Variable Literal Symbol}
    (proof : Derives hoApplySymbol kb context goal naf) : Derives hoApplySymbol kb' context goal naf' := by
  induction proof with
  | assumption member => exact .assumption member
  | truth => exact .truth
  | conjIntro _ _ left right => exact .conjIntro (left failures) (right failures)
  | conjLeft _ ih => exact .conjLeft (ih failures)
  | conjRight _ ih => exact .conjRight (ih failures)
  | disjLeft _ ih => exact .disjLeft (ih failures)
  | disjRight _ ih => exact .disjRight (ih failures)
  | disjElim _ _ _ choice left right =>
      exact .disjElim (choice failures) (left failures) (right failures)
  | impIntro _ ih => exact .impIntro (ih failures)
  | impElim _ _ rule argument => exact .impElim (rule failures) (argument failures)
  | falsityElim _ ih => exact .falsityElim (ih failures)
  | forallIntro freshContext freshGoal opening _ ih =>
      exact .forallIntro freshContext freshGoal opening (ih failures)
  | forallElim _ instantiation ih => exact .forallElim (ih failures) instantiation
  | existsIntro instantiation _ ih => exact .existsIntro instantiation (ih failures)
  | existsElim _ freshContext freshBody freshGoal opening _ existence ih =>
      exact .existsElim (existence failures) freshContext freshBody freshGoal opening (ih failures)
  | clause member headInstance bodyInstance _ ih =>
      exact .clause (clauses _ member) headInstance bodyInstance (ih failures)
  | goalClause member bodyInstance _ ih => exact .goalClause (clauses _ member) bodyInstance (ih failures)
  | defaultNegIntro ground refuted => exact .defaultNegIntro ground (failures _ _ refuted)
  | hoApplyIntro _ ih => exact .hoApplyIntro (ih failures)
  | hoApplyElim _ ih => exact .hoApplyElim (ih failures)
  | equalRefl => exact .equalRefl
  | equalSymm _ ih => exact .equalSymm (ih failures)
  | equalTrans _ _ left right => exact .equalTrans (left failures) (right failures)
  | equalSubst _ leftInstance rightInstance _ equality ih =>
      exact .equalSubst (equality failures) leftInstance rightInstance (ih failures)

/-- Positive derivations are monotonic: clause and assumption evidence remains
valid in every larger KB. -/
theorem Derives.positive_mono {kb kb' : LogicalKb Variable Literal Symbol}
    (clauses : ∀ clause, clause ∈ kb → clause ∈ kb')
    {context : ProofContext Variable Literal Symbol} {goal : Formula Variable Literal Symbol}
    (proof : Derives hoApplySymbol kb context goal) : Derives hoApplySymbol kb' context goal :=
  proof.mono clauses (fun _ _ refuted => refuted)

end AnthillModKbSpec
