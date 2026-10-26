import AnthillModKbSpec.Foundation.Syntax

namespace AnthillModKbSpec

/-- A logical knowledge base is a set of Horn clauses, represented by its
membership predicate. Order and multiplicity carry no information, and finiteness
is not required. Membership uses raw clause equality, not alpha-equivalence or
logical equivalence. This is a logical collection, not a resolver or term store. -/
def LogicalKb (Variable Literal Symbol : Type) :=
  HornClause Variable Literal Symbol → Prop

namespace LogicalKb

instance : Membership (HornClause Variable Literal Symbol) (LogicalKb Variable Literal Symbol) :=
  ⟨fun kb clause => kb clause⟩

instance : EmptyCollection (LogicalKb Variable Literal Symbol) :=
  ⟨fun _ => False⟩

instance : Singleton (HornClause Variable Literal Symbol) (LogicalKb Variable Literal Symbol) :=
  ⟨fun clause candidate => candidate = clause⟩

instance : Insert (HornClause Variable Literal Symbol) (LogicalKb Variable Literal Symbol) :=
  ⟨fun clause kb candidate => candidate = clause ∨ candidate ∈ kb⟩

@[simp] theorem mem_empty (clause : HornClause Variable Literal Symbol) :
    clause ∈ (∅ : LogicalKb Variable Literal Symbol) ↔ False := Iff.rfl

@[simp] theorem mem_singleton (candidate clause : HornClause Variable Literal Symbol) :
    candidate ∈ ({clause} : LogicalKb Variable Literal Symbol) ↔ candidate = clause := Iff.rfl

@[simp] theorem mem_insert (candidate clause : HornClause Variable Literal Symbol)
    (kb : LogicalKb Variable Literal Symbol) :
    candidate ∈ insert clause kb ↔ candidate = clause ∨ candidate ∈ kb := Iff.rfl

/-- Knowledge bases are equal exactly when they contain the same clauses. -/
theorem ext {left right : LogicalKb Variable Literal Symbol}
    (membership : ∀ clause, clause ∈ left ↔ clause ∈ right) : left = right :=
  funext (fun clause => propext (membership clause))

end LogicalKb
end AnthillModKbSpec
