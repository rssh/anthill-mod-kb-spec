import AnthillModKbSpec.Foundation.InductiveDomains

namespace AnthillModKbSpec.InductiveDomains

/-- A Lean data type presented exactly by a constructor-generated domain.
The family may include other data types used by constructor fields. Generating
this presentation does not assert Realizes for an arbitrary logical model. -/
class InductiveDomain (α : Type) where
  Domain : Type
  Symbol : Type
  family : FiniteFamily Domain Symbol
  root : Domain
  encode : α → Tree Symbol
  encode_member : ∀ value, Member family.definitions root (encode value)
  member_complete : ∀ tree, Member family.definitions root tree →
    ∃ value, encode value = tree

namespace InductiveDomain

variable {α : Type} [presentation : InductiveDomain α]

theorem member_iff (tree : Tree presentation.Symbol) :
    Member presentation.family.definitions presentation.root tree ↔
      ∃ value : α, presentation.encode value = tree := by
  constructor
  · exact presentation.member_complete tree
  · rintro ⟨value, rfl⟩
    exact presentation.encode_member value

/-- The generated domain has precisely the original type's inhabitants, so a
property over its trees can be proved by quantifying over Lean data values. -/
theorem holds_iff (property : Tree presentation.Symbol → Prop) :
    Holds presentation.family.definitions [presentation.root] property ↔
      ∀ value : α, property (presentation.encode value) := by
  constructor
  · intro all value
    exact all _ ⟨presentation.root, by simp, presentation.encode_member value⟩
  · rintro all tree ⟨domain, selected, member⟩
    have same : domain = presentation.root := by simpa using selected
    subst domain
    obtain ⟨value, rfl⟩ := presentation.member_complete tree member
    exact all value

end InductiveDomain
end AnthillModKbSpec.InductiveDomains
