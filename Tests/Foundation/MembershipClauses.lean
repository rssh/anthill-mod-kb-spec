import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Semantics AnthillModKbSpec.InductiveDomains
open AnthillModKbSpec.InductionModel

namespace MembershipClausesTests

-- Nat rules have at most one field, so a single argument name is distinct.
def names : Nat → String := fun _ => "x"

theorem distinct : DistinctNames sigma names := by
  rintro rule (rfl | rfl) i j _
  all_goals
    apply Fin.ext
    have bound := i.isLt
    have other := j.isLt
    simp only [zeroRule, succRule, List.length_nil, List.length_cons] at bound other
    omega

def membership : K := membershipKb sigma membershipSymbol names

-- The generated clauses are exactly the hand-written Nat membership clauses.
example : membershipClause membershipSymbol names zeroRule = natZero := rfl
example : membershipClause membershipSymbol names succRule = natSucc := rfl

-- Realization alone makes the generated KB valid.
theorem valid : model.Models membership := models_membershipKb model realizes names

-- Membership of a generated value is derivable from the generated KB alone.
theorem two : Derives Symbol.hoApply membership [] (isNat (succ (succ zero))) := by
  have proof : Derives Symbol.hoApply membership [] (.app (membershipSymbol .nat) [(natTree 2).toTerm]) :=
    (natTree_member 2).derives distinct (fun _ => mem_membershipKb)
  simpa [natTree, Tree.toTerm, membershipSymbol, isNat, succ, zero] using proof

-- A name supply that is distinct only per rule still instantiates independently.
def pairRule : Rule Unit Symbol := ⟨(), .succ, [(), ()]⟩
def pairNames : Nat → String := fun i => if i = 0 then "a" else "b"

theorem pairDistinct : DistinctNames (fun rule => rule = pairRule) pairNames := by
  rintro rule rfl i j same
  apply Fin.ext
  have bound := i.isLt
  have other := j.isLt
  simp only [pairRule, List.length_cons, List.length_nil] at bound other
  by_cases left : i.val = 0 <;> by_cases right : j.val = 0 <;>
    simp [pairNames, left, right] at same <;> omega

example : membershipClause (fun _ : Unit => Symbol.isNat) pairNames pairRule =
    (.definite (isNat (.app .succ [.var "a", .var "b"])) [isNat (.var "a"), isNat (.var "b")] :
      HornClause String Unit Symbol) := rfl

-- Repeated names are not distinct for a binary rule.
example : ¬ DistinctNames (fun rule => rule = pairRule) names := by
  intro distinct
  have same := distinct pairRule rfl ⟨0, by decide⟩ ⟨1, by decide⟩ rfl
  simp at same

open Lean Meta in
run_meta do
  for declaration in [``membershipClause_valid, ``models_membershipKb, ``Member.derives,
      ``InUnion.derives, ``guard_derives, ``Tree.eval_toTerm, ``valid, ``two, ``pairDistinct] do
    for axiomName in ← collectAxioms declaration do
      unless axiomName ∈ [`propext, `Classical.choice, `Quot.sound] do
        throwError "unexpected axiom in membership clauses: {axiomName}"

end MembershipClausesTests
