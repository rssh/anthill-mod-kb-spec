import AnthillModKbSpec.Foundation.ClauseInstantiation
import AnthillModKbSpec.Foundation.Derivation
import AnthillModKbSpec.Foundation.OperationDictionaries

namespace AnthillModKbSpec

open OperationDictionaries (lookup lookup_eq_none)

/-! # Freshening a clause use

A use of a clause instantiates exactly the names its quantifiers own. For a KB
clause these are its free names, bound by the implicit universal closure; for a
local rule they are its explicit leading binders. Every other free name is a
captured parameter and is never renamed. Inner quantifiers keep their bound
occurrences; one is renamed only if a fresh name would otherwise be captured. -/

variable {Variable Literal Symbol : Type}

/-- `count` distinct names, none of them in `avoid`. -/
def freshNames [FreshNames Variable] (avoid : List Variable) : Nat → List Variable
  | 0 => []
  | count + 1 =>
      let name := FreshNames.fresh avoid
      name :: freshNames (name :: avoid) count

section Fresh

variable [FreshNames Variable]

theorem freshNames_length (avoid : List Variable) (count : Nat) : (freshNames avoid count).length = count := by
  induction count generalizing avoid with
  | zero => rfl
  | succ count ih => simp [freshNames, ih]

theorem freshNames_avoid (avoid : List Variable) (count : Nat) :
    ∀ name ∈ freshNames avoid count, name ∉ avoid := by
  induction count generalizing avoid with
  | zero => intro _ member; cases member
  | succ count ih =>
      intro name member
      simp only [freshNames, List.mem_cons] at member
      rcases member with rfl | member
      · exact FreshNames.fresh_not_mem avoid
      · exact fun inside => ih _ name member (List.mem_cons_of_mem _ inside)

theorem freshNames_nodup (avoid : List Variable) (count : Nat) : (freshNames avoid count).Nodup := by
  induction count generalizing avoid with
  | zero => exact .nil
  | succ count ih =>
      simp only [freshNames, List.nodup_cons]
      exact ⟨fun member => freshNames_avoid _ count _ member List.mem_cons_self, ih _⟩

/-- Fresh names for the given templates, in order, avoiding `avoid` and the
templates themselves. -/
def freshenNames (avoid templates : List Variable) : List (Variable × Variable) :=
  templates.zip (freshNames (templates ++ avoid) templates.length)

theorem freshenNames_fst (avoid templates : List Variable) :
    (freshenNames avoid templates).map Prod.fst = templates := by
  simp [freshenNames, List.map_fst_zip, freshNames_length]

theorem freshenNames_snd (avoid templates : List Variable) :
    (freshenNames avoid templates).map Prod.snd = freshNames (templates ++ avoid) templates.length := by
  simp [freshenNames, List.map_snd_zip, freshNames_length]

end Fresh

variable [DecidableEq Variable]

/-- The names a KB clause instantiates on each use: its free names. -/
def HornClause.templates : HornClause Variable Literal Symbol → List Variable
  | .definite head body => (head.freeVars ++ (Term.conjunction body).freeVars).eraseDups
  | .goal body => (Term.conjunction body).freeVars.eraseDups

/-- The name a renaming gives: its fresh name for a template name, and the name
itself for a captured one. -/
def renamed (pairs : List (Variable × Variable)) (name : Variable) : Variable :=
  (lookup pairs name).getD name

/-- Rename template names by variables; captured names are kept. -/
def Substitution.rename (pairs : List (Variable × Variable)) : Substitution Variable Literal Symbol :=
  fun name => .var (renamed pairs name)

theorem renamed_captured {pairs : List (Variable × Variable)} {name : Variable}
    (captured : name ∉ pairs.map Prod.fst) : renamed pairs name = name := by
  simp [renamed, lookup_eq_none.mpr captured]

theorem renamed_template {pairs : List (Variable × Variable)} (distinct : (pairs.map Prod.fst).Nodup)
    {name fresh : Variable} (member : (name, fresh) ∈ pairs) : renamed pairs name = fresh := by
  induction pairs with
  | nil => cases member
  | cons entry rest ih =>
      obtain ⟨template, other⟩ := entry
      simp only [List.map_cons, List.nodup_cons] at distinct
      simp only [List.mem_cons, Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩ | member
      · simp [renamed, lookup]
      · have different : template ≠ name := fun same =>
          distinct.1 (same ▸ List.mem_map.mpr ⟨_, member, rfl⟩)
        simp only [renamed, lookup, different, ite_false] at ih ⊢
        exact ih distinct.2 member


/-- Renaming fixes the captured names and maps each template name to its fresh
name. A free name of the result is the renaming of a free name of the term,
and conversely: no inner binder captures a renamed name, and no bound name
becomes free. -/
theorem Term.rename_freeVars [FreshNames Variable] (pairs : List (Variable × Variable))
    (term : Term Variable Literal Symbol) (other : Variable) :
    other ∈ (term.instantiate (Substitution.rename pairs)).freeVars ↔
      ∃ name ∈ term.freeVars, other = renamed pairs name := by
  have instantiated := term.instantiate_substitutes (Substitution.rename pairs)
  constructor
  · intro member
    obtain ⟨name, nameMember, inside⟩ := instantiated.freeVars_cover other member
    simp only [Substitution.rename, Term.freeVars, List.mem_singleton] at inside
    exact ⟨name, nameMember, inside⟩
  · rintro ⟨name, member, rfl⟩
    exact instantiated.freeVars_subset name member _ (by simp [Substitution.rename, Term.freeVars])

/-! ## Local rules -/

/-- Instantiate a local rule's leading universal binders, one witness each.
The rule's free names are captured parameters and are kept. `none` if the rule
has fewer leading binders than witnesses. -/
def Term.instantiateLeading [FreshNames Variable] :
    Term Variable Literal Symbol → List (Term Variable Literal Symbol) → Option (Term Variable Literal Symbol)
  | term, [] => some term
  | .forallVar binder body, witness :: rest =>
      (body.instantiate (Substitution.single binder witness)).instantiateLeading rest
  | _, _ :: _ => none

section Leading

variable [FreshNames Variable]

/-- An instance of a derived local rule is derived by universal elimination. -/
theorem Derives.instantiateLeading {hoApplySymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
    {context : ProofContext Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}
    {rule : Term Variable Literal Symbol} (witnesses : List (Term Variable Literal Symbol))
    {instantiated : Term Variable Literal Symbol} (computed : rule.instantiateLeading witnesses = some instantiated)
    (proof : Derives hoApplySymbol kb context rule naf) : Derives hoApplySymbol kb context instantiated naf := by
  induction witnesses generalizing rule with
  | nil => cases computed; exact proof
  | cons witness rest ih =>
      cases rule with
      | forallVar binder body =>
          exact ih computed (.forallElim proof (body.instantiate_substitutes _))
      | _ => cases computed

/-- Instantiation keeps every captured parameter free. -/
theorem Term.instantiateLeading_captured {rule : Term Variable Literal Symbol}
    (witnesses : List (Term Variable Literal Symbol)) {instantiated : Term Variable Literal Symbol}
    (computed : rule.instantiateLeading witnesses = some instantiated) :
    ∀ name ∈ rule.freeVars, name ∈ instantiated.freeVars := by
  induction witnesses generalizing rule with
  | nil => cases computed; exact fun _ member => member
  | cons witness rest ih =>
      cases rule with
      | forallVar binder body =>
          intro name member
          simp only [Term.freeVars, List.mem_filter, bne_iff_ne, ne_eq] at member
          apply ih computed
          exact (body.instantiate_substitutes _).freeVars_subset name member.1 name
            (by simp [Substitution.single, Substitution.bind, member.2, Term.freeVars])
      | _ => cases computed

/-- A free name of an instantiated is a captured parameter or comes from a witness. -/
theorem Term.instantiateLeading_freeVars {rule : Term Variable Literal Symbol}
    (witnesses : List (Term Variable Literal Symbol)) {instantiated : Term Variable Literal Symbol}
    (computed : rule.instantiateLeading witnesses = some instantiated) :
    ∀ other ∈ instantiated.freeVars, other ∈ rule.freeVars ∨ ∃ witness ∈ witnesses, other ∈ witness.freeVars := by
  induction witnesses generalizing rule with
  | nil => cases computed; exact fun _ member => .inl member
  | cons witness rest ih =>
      cases rule with
      | forallVar binder body =>
          intro other member
          rcases ih computed other member with inside | ⟨found, foundMember, occurs⟩
          · rcases Term.freeVars_instantiate_single inside with ⟨inBody, different⟩ | ⟨_, inWitness⟩
            · exact .inl (by simp [Term.freeVars, inBody, different])
            · exact .inr ⟨witness, List.mem_cons_self, inWitness⟩
          · exact .inr ⟨found, List.mem_cons_of_mem _ foundMember, occurs⟩
      | _ => cases computed

end Leading

end AnthillModKbSpec
