import AnthillModKbSpec.Resolution.AdmissionSignature
import AnthillModKbSpec.Foundation.UniversalIntroduction
import AnthillModKbSpec.Foundation.MembershipClauses

namespace AnthillModKbSpec.Elaboration

open Semantics InductiveDomains AdmissionSignature

variable {Domain Variable Literal Symbol Value : Type} [DecidableEq Variable]
  {hoApplySymbol : Symbol}

/-- Sidecar binder annotations, addressed by paths through the existing Term.
Unary bodies use child 0, binary terms use 0/1, application arguments use their
indices, and dictionary calls use 0 for the dictionary and 1 onward for arguments.
Only entries at quantifiers are read. Names are never used as annotation keys. -/
abbrev Ranges (Domain : Type) := List Nat → Range Domain

def child (ranges : Ranges Domain) (index : Nat) : Ranges Domain :=
  fun path => ranges (index :: path)

/-- The executable profile defaults to all declared generated data (D_all).
Predicate binders must explicitly select `.predicate n`; `.carrier` explicitly
opts out. `predicateRanged` rejects a binder applied by `ho_apply` that keeps a
data range. -/
def defaultRanges : Ranges Domain := fun _ => .allData

/-- Guards are atoms over the naming's membership symbols, except an explicit
domain list, which is the existing disjunction over named domains. They never
enumerate the registry or the domain catalog, so lowering reads only `naming`
and lowered terms keep their meaning as the registry grows. -/
def rangeGuard (naming : Naming Domain Symbol) (range : Range Domain)
    (subject : Term Variable Literal Symbol) : Term Variable Literal Symbol :=
  match range with
  | .carrier => .truth
  | .allData => .app naming.dataSymbol [subject]
  | .data domains => guard naming.membershipSymbol domains subject
  | .predicate arity => .app (naming.predicateSymbol arity) [subject]

def forallRange (naming : Naming Domain Symbol) (range : Range Domain)
    (binder : Variable) (body : Term Variable Literal Symbol) : Term Variable Literal Symbol :=
  .forallVar binder (.imp (rangeGuard naming range (.var binder)) body)

def existsRange (naming : Naming Domain Symbol) (range : Range Domain)
    (binder : Variable) (body : Term Variable Literal Symbol) : Term Variable Literal Symbol :=
  .existsVar binder (.conj (rangeGuard naming range (.var binder)) body)

mutual
/-- Recursively elaborate already represented terms. This adds no binders or
names, and preserves application symbols, dictionary selectors, and argument order. -/
def elaborate (naming : Naming Domain Symbol) (ranges : Ranges Domain) :
    Term Variable Literal Symbol → Term Variable Literal Symbol
  | .var name => .var name
  | .lit value => .lit value
  | .app symbol args => .app symbol (elaborateArgs naming ranges 0 args)
  | .truth => .truth
  | .falsity => .falsity
  | .conj a b => .conj (elaborate naming (child ranges 0) a) (elaborate naming (child ranges 1) b)
  | .disj a b => .disj (elaborate naming (child ranges 0) a) (elaborate naming (child ranges 1) b)
  | .imp a b => .imp (elaborate naming (child ranges 0) a) (elaborate naming (child ranges 1) b)
  | .equal a b => .equal (elaborate naming (child ranges 0) a) (elaborate naming (child ranges 1) b)
  | .defaultNeg body => .defaultNeg (elaborate naming (child ranges 0) body)
  | .forallVar name body => forallRange naming (ranges []) name (elaborate naming (child ranges 0) body)
  | .existsVar name body => existsRange naming (ranges []) name (elaborate naming (child ranges 0) body)
  | .dictionaryCall dictionary path operation args =>
      .dictionaryCall (elaborate naming (child ranges 0) dictionary) path operation
        (elaborateArgs naming ranges 1 args)

def elaborateArgs (naming : Naming Domain Symbol) (ranges : Ranges Domain)
    (offset : Nat) : List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol)
  | [] => []
  | head :: tail => elaborate naming (child ranges offset) head :: elaborateArgs naming ranges (offset + 1) tail
end

/-- A name applied by `ho_apply` to `arity` arguments must range over predicate
references of exactly that arity, or explicitly over the whole carrier. A data
range, in particular the D_all default, is never admitted in this position. -/
def admitsPredicate : Range Domain → Nat → Bool
  | .predicate declared, arity => declared == arity
  | .carrier, _ => true
  | .allData, _ => false
  | .data _, _ => false

/-- The head of an explicit `ho_apply` argument list, when it is a governed name. -/
def headRanged (scope : Variable → Option (Range Domain)) : List (Term Variable Literal Symbol) → Bool
  | .var name :: rest => (scope name).all (admitsPredicate · rest.length)
  | _ => true

mutual
/-- Check each `ho_apply(P, args)` whose head `P` this lowering guards. `scope`
gives the range of each name's nearest binder; names it maps to none are fixed
parameters, governed by their own declarations. Paths are read as in `elaborate`,
so the check sees exactly the ranges that lowering will turn into guards. -/
def predicateRanged [DecidableEq Symbol] (hoApplySymbol : Symbol) (ranges : Ranges Domain)
    (scope : Variable → Option (Range Domain)) : Term Variable Literal Symbol → Bool
  | .var _ => true
  | .lit _ => true
  | .app symbol args =>
      (if symbol = hoApplySymbol then headRanged scope args else true) &&
        predicateRangedArgs hoApplySymbol ranges scope 0 args
  | .truth => true
  | .falsity => true
  | .conj a b => predicateRanged hoApplySymbol (child ranges 0) scope a &&
      predicateRanged hoApplySymbol (child ranges 1) scope b
  | .disj a b => predicateRanged hoApplySymbol (child ranges 0) scope a &&
      predicateRanged hoApplySymbol (child ranges 1) scope b
  | .imp a b => predicateRanged hoApplySymbol (child ranges 0) scope a &&
      predicateRanged hoApplySymbol (child ranges 1) scope b
  | .equal a b => predicateRanged hoApplySymbol (child ranges 0) scope a &&
      predicateRanged hoApplySymbol (child ranges 1) scope b
  | .defaultNeg body => predicateRanged hoApplySymbol (child ranges 0) scope body
  | .forallVar name body =>
      predicateRanged hoApplySymbol (child ranges 0) (update scope name (some (ranges []))) body
  | .existsVar name body =>
      predicateRanged hoApplySymbol (child ranges 0) (update scope name (some (ranges []))) body
  | .dictionaryCall dictionary _ _ args =>
      predicateRanged hoApplySymbol (child ranges 0) scope dictionary &&
        predicateRangedArgs hoApplySymbol ranges scope 1 args

def predicateRangedArgs [DecidableEq Symbol] (hoApplySymbol : Symbol) (ranges : Ranges Domain)
    (scope : Variable → Option (Range Domain)) (offset : Nat) :
    List (Term Variable Literal Symbol) → Bool
  | [] => true
  | head :: tail => predicateRanged hoApplySymbol (child ranges offset) scope head &&
      predicateRangedArgs hoApplySymbol ranges scope (offset + 1) tail
end

/-- Executable-profile lowering of a goal or assumption. It rejects, rather than
D_all-guards, a predicate binder left at a data range; accepted output is `elaborate`. -/
def elaborate? [DecidableEq Symbol] (hoApplySymbol : Symbol) (naming : Naming Domain Symbol)
    (ranges : Ranges Domain) (term : Term Variable Literal Symbol) : Option (Term Variable Literal Symbol) :=
  if predicateRanged hoApplySymbol ranges (fun _ => none) term then some (elaborate naming ranges term) else none

theorem elaborate?_eq_some [DecidableEq Symbol] (hoApplySymbol : Symbol)
    (naming : Naming Domain Symbol) (ranges : Ranges Domain)
    (term result : Term Variable Literal Symbol) :
    elaborate? hoApplySymbol naming ranges term = some result ↔
      predicateRanged hoApplySymbol ranges (fun _ => none) term = true ∧ elaborate naming ranges term = result := by
  unfold elaborate?
  split <;> simp_all

theorem rangeGuard_satisfies (snapshot : SignatureSnapshot Domain Symbol)
    (model : Model Literal Symbol Value hoApplySymbol) (valid : AdmissionSignature.Realizes snapshot model)
    (environment : Environment Variable Value) (range : Range Domain)
    (subject : Term Variable Literal Symbol) :
    model.Satisfies environment (rangeGuard snapshot.naming range subject) ↔
      range.Contains snapshot model (model.eval environment subject) := by
  cases range with
  | carrier => simp [rangeGuard, Range.Contains, Model.Satisfies, Model.eval, model.holds_top]
  | allData =>
      simpa only [rangeGuard, Model.Satisfies, Model.eval, List.map_cons, List.map_nil,
        SignatureSnapshot.naming, Signature.naming] using valid.allData _
  | data domains =>
      exact (guard_eval model _ domains environment subject).trans (valid.data_iff domains _).symm
  | predicate arity =>
      simpa only [rangeGuard, Model.Satisfies, Model.eval, List.map_cons, List.map_nil,
        SignatureSnapshot.naming, Signature.naming, Range.Contains] using valid.predicates arity _

theorem forallRange_satisfies (snapshot : SignatureSnapshot Domain Symbol)
    (model : Model Literal Symbol Value hoApplySymbol) (valid : AdmissionSignature.Realizes snapshot model)
    (environment : Environment Variable Value) (range : Range Domain) (binder : Variable)
    (body : Term Variable Literal Symbol) :
    model.Satisfies environment (forallRange snapshot.naming range binder body) ↔
      ∀ value, range.Contains snapshot model value → model.Satisfies (update environment binder value) body := by
  simp only [forallRange, Model.Satisfies, Model.eval, model.holds_universal, model.holds_implication]
  have guards (value : Value) := rangeGuard_satisfies snapshot model valid
    (update environment binder value) range (.var binder)
  simp only [Model.Satisfies, Model.eval, update, ite_true] at guards
  simp only [guards]

theorem existsRange_satisfies (snapshot : SignatureSnapshot Domain Symbol)
    (model : Model Literal Symbol Value hoApplySymbol) (valid : AdmissionSignature.Realizes snapshot model)
    (environment : Environment Variable Value) (range : Range Domain) (binder : Variable)
    (body : Term Variable Literal Symbol) :
    model.Satisfies environment (existsRange snapshot.naming range binder body) ↔
      ∃ value, range.Contains snapshot model value ∧ model.Satisfies (update environment binder value) body := by
  simp only [existsRange, Model.Satisfies, Model.eval, model.holds_existential, model.holds_conjunction]
  have guards (value : Value) := rangeGuard_satisfies snapshot model valid
    (update environment binder value) range (.var binder)
  simp only [Model.Satisfies, Model.eval, update, ite_true] at guards
  simp only [guards]

omit [DecidableEq Variable] in
/-- Data universals are exactly the existing foundation translation. -/
theorem forallRange_data (naming : Naming Domain Symbol) (domains : List Domain)
    (binder : Variable) (body : Term Variable Literal Symbol) :
    forallRange naming (.data domains) binder body =
      (Universal.mk domains binder body).toTerm naming.membershipSymbol := rfl

/-- General bounded introduction reuses the existing eigenvariable derivation. -/
theorem forallRange_intro (naming : Naming Domain Symbol) (range : Range Domain)
    {kb : LogicalKb Variable Literal Symbol} {context : ProofContext Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol} {body : Term Variable Literal Symbol}
    (binder : Variable) (fresh : FreshForContext binder context)
    (proof : Derives hoApplySymbol kb (rangeGuard naming range (.var binder) :: context) body naf) :
    Derives hoApplySymbol kb context (forallRange naming range binder body) naf :=
  (Derives.impIntro proof).generalize binder fresh

/-- The explicit list of every declared domain lowers to `FiniteFamily.forallAll`. -/
theorem forallAll_intro (snapshot : SignatureSnapshot Domain Symbol)
    {kb : LogicalKb Variable Literal Symbol} {context : ProofContext Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol} {body : Term Variable Literal Symbol}
    (binder : Variable) (fresh : FreshForContext binder context)
    (proof : Derives hoApplySymbol kb
      (rangeGuard snapshot.naming (.data snapshot.signature.data.domains) (.var binder) :: context) body naf) :
    Derives hoApplySymbol kb context
      (forallRange snapshot.naming (.data snapshot.signature.data.domains) binder body) naf :=
  Derives.forallAll_intro snapshot.signature.data binder fresh proof

theorem rangeGuard_substitutes (naming : Naming Domain Symbol) (range : Range Domain)
    {σ : Substitution Variable Literal Symbol} {before after : Term Variable Literal Symbol}
    (proof : Substitutes σ before after) :
    Substitutes σ (rangeGuard naming range before) (rangeGuard naming range after) := by
  cases range with
  | carrier => exact .truth
  | allData => exact .app (.cons proof .nil)
  | predicate arity => exact .app (.cons proof .nil)
  | data domains =>
      induction domains with
      | nil => exact .falsity
      | cons domain domains ih => exact .disj (.app (.cons proof .nil)) ih

theorem rangeGuard_freeVars (naming : Naming Domain Symbol) (range : Range Domain)
    (subject : Term Variable Literal Symbol) (name : Variable)
    (member : name ∈ (rangeGuard naming range subject).freeVars) : name ∈ subject.freeVars := by
  cases range with
  | carrier => simp [rangeGuard, Term.freeVars] at member
  | allData => simpa [rangeGuard, Term.freeVars] using member
  | predicate arity => simpa [rangeGuard, Term.freeVars] using member
  | data domains =>
      induction domains with
      | nil => simp [rangeGuard, InductiveDomains.guard, Term.freeVars] at member
      | cons domain domains ih =>
          simp only [rangeGuard, InductiveDomains.guard, List.map_cons, List.foldr_cons, Term.freeVars,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at member
          exact member.elim id ih

theorem forallRange_freeVars (naming : Naming Domain Symbol) (range : Range Domain)
    (binder : Variable) (body : Term Variable Literal Symbol) (name : Variable) :
    name ∈ (forallRange naming range binder body).freeVars ↔
      name ∈ (.forallVar binder body : Term Variable Literal Symbol).freeVars := by
  simp only [forallRange, Term.freeVars, List.mem_filter, List.mem_append, bne_iff_ne]
  constructor
  · rintro ⟨member | member, different⟩
    · have same := rangeGuard_freeVars naming range (.var binder) name member
      simp only [Term.freeVars, List.mem_singleton] at same
      exact False.elim (different same)
    · exact ⟨member, different⟩
  · rintro ⟨member, different⟩; exact ⟨Or.inr member, different⟩

theorem existsRange_freeVars (naming : Naming Domain Symbol) (range : Range Domain)
    (binder : Variable) (body : Term Variable Literal Symbol) (name : Variable) :
    name ∈ (existsRange naming range binder body).freeVars ↔
      name ∈ (.existsVar binder body : Term Variable Literal Symbol).freeVars :=
  by simpa only [forallRange, existsRange, Term.freeVars] using
    forallRange_freeVars naming range binder body name

/-- Elaboration preserves exactly the free names, even for empty ranges. -/
theorem freeVars (naming : Naming Domain Symbol) (term : Term Variable Literal Symbol) :
    ∀ ranges name, name ∈ (elaborate naming ranges term).freeVars ↔ name ∈ term.freeVars := by
  refine Term.rec
    (motive_1 := fun term => ∀ ranges name,
      name ∈ (elaborate naming ranges term).freeVars ↔ name ∈ term.freeVars)
    (motive_2 := fun args => ∀ ranges offset name,
      name ∈ (elaborateArgs naming ranges offset args).flatMap Term.freeVars ↔
        name ∈ args.flatMap Term.freeVars)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ term
  · intros; rfl
  · intros; rfl
  · intro symbol args ih ranges name; simpa only [elaborate, Term.freeVars] using ih ranges 0 name
  · intros; rfl
  · intros; rfl
  · intro a b left right ranges name; simp only [elaborate, Term.freeVars, List.mem_append, left, right]
  · intro a b left right ranges name; simp only [elaborate, Term.freeVars, List.mem_append, left, right]
  · intro a b left right ranges name; simp only [elaborate, Term.freeVars, List.mem_append, left, right]
  · intro body ih ranges name; simpa only [elaborate, Term.freeVars] using ih (child ranges 0) name
  · intro binder body ih ranges name
    simp only [elaborate, forallRange_freeVars, Term.freeVars, List.mem_filter, ih]
  · intro binder body ih ranges name
    simp only [elaborate, existsRange_freeVars, Term.freeVars, List.mem_filter, ih]
  · intro dictionary path operation args left right ranges name
    simp only [elaborate, Term.freeVars, List.mem_append, left, right]
  · intro a b left right ranges name; simp only [elaborate, Term.freeVars, List.mem_append, left, right]
  · intros; rfl
  · intro head tail left right ranges offset name
    simp only [elaborateArgs, List.flatMap_cons, List.mem_append, left, right]

/-- Any capture-avoiding substitution in the lowered formula has the existing
foundation semantics, including arbitrary formula-valued replacement terms. -/
theorem satisfies_substitutes (naming : Naming Domain Symbol) (ranges : Ranges Domain)
    (model : Model Literal Symbol Value hoApplySymbol) {term result : Term Variable Literal Symbol}
    {σ : Substitution Variable Literal Symbol}
    (proof : Substitutes σ (elaborate naming ranges term) result)
    (environment : Environment Variable Value) :
    model.Satisfies environment result ↔ model.Satisfies
      (fun name => model.eval environment (σ name)) (elaborate naming ranges term) := by
  unfold Model.Satisfies
  rw [model.eval_substitutes proof]

/-- Source substitutions may be moved through elaboration when their images
need no further elaboration (in particular, ordinary data and variable images).
Formula-valued replacements are elaborated first, then substituted in the target;
`satisfies_substitutes` applies without this stability condition. -/
def Stable (naming : Naming Domain Symbol) (σ : Substitution Variable Literal Symbol) : Prop :=
  ∀ name ranges, elaborate naming ranges (σ name) = σ name

private theorem stable_bind (naming : Naming Domain Symbol)
    {σ : Substitution Variable Literal Symbol} (stable : Stable naming σ) (binder renamed : Variable) :
    Stable naming (Substitution.bind σ binder (.var renamed)) := by
  intro name ranges
  by_cases same : name = binder
  · simp [Substitution.bind, same, elaborate]
  · simpa only [Substitution.bind, ite_eq_right same] using stable name ranges

theorem elaboration_substitutes (naming : Naming Domain Symbol)
    {σ : Substitution Variable Literal Symbol} {before after : Term Variable Literal Symbol}
    (proof : Substitutes σ before after) :
    Stable naming σ → ∀ ranges,
      Substitutes σ (elaborate naming ranges before) (elaborate naming ranges after) := by
  refine Substitutes.rec
    (motive_1 := fun σ before after _ => Stable naming σ → ∀ ranges,
      Substitutes σ (elaborate naming ranges before) (elaborate naming ranges after))
    (motive_2 := fun σ before after _ => Stable naming σ → ∀ ranges offset,
      SubstitutesList σ (elaborateArgs naming ranges offset before) (elaborateArgs naming ranges offset after))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ proof
  · intro σ name stable ranges
    simpa only [elaborate, stable name ranges] using (Substitutes.var (σ := σ) (name := name))
  · intros; exact .lit
  · intros; exact .truth
  · intros; exact .falsity
  · intro σ before after symbol args ih stable ranges
    simpa only [elaborate] using Substitutes.app (ih stable ranges 0)
  · intro σ a a' b b' left right ihLeft ihRight stable ranges
    exact .conj (ihLeft stable (child ranges 0)) (ihRight stable (child ranges 1))
  · intro σ a a' b b' left right ihLeft ihRight stable ranges
    exact .disj (ihLeft stable (child ranges 0)) (ihRight stable (child ranges 1))
  · intro σ a a' b b' left right ihLeft ihRight stable ranges
    exact .imp (ihLeft stable (child ranges 0)) (ihRight stable (child ranges 1))
  · intro σ before after body ih stable ranges
    exact .defaultNeg (ih stable (child ranges 0))
  · intro binder σ renamed body result fresh bodySubst ih stable ranges
    apply Substitutes.forallVar
    · intro name member different
      have occurs : name ∈ body.freeVars := by
        simp only [Term.freeVars, List.mem_append] at member
        rcases member with member | member
        · have same := rangeGuard_freeVars naming (ranges []) (.var binder) name member
          simp only [Term.freeVars, List.mem_singleton] at same
          exact False.elim (different same)
        · exact (freeVars naming body _ name).mp member
      exact fresh name occurs different
    · apply Substitutes.imp
      · apply rangeGuard_substitutes
        simpa [Substitution.bind] using
          (Substitutes.var (σ := Substitution.bind σ binder (.var renamed)) (name := binder))
      · exact ih (stable_bind naming stable binder renamed) (child ranges 0)
  · intro binder σ renamed body result fresh bodySubst ih stable ranges
    apply Substitutes.existsVar
    · intro name member different
      have occurs : name ∈ body.freeVars := by
        simp only [Term.freeVars, List.mem_append] at member
        rcases member with member | member
        · have same := rangeGuard_freeVars naming (ranges []) (.var binder) name member
          simp only [Term.freeVars, List.mem_singleton] at same
          exact False.elim (different same)
        · exact (freeVars naming body _ name).mp member
      exact fresh name occurs different
    · apply Substitutes.conj
      · apply rangeGuard_substitutes
        simpa [Substitution.bind] using
          (Substitutes.var (σ := Substitution.bind σ binder (.var renamed)) (name := binder))
      · exact ih (stable_bind naming stable binder renamed) (child ranges 0)
  · intro σ beforeDictionary afterDictionary before after path operation dictionary args
      ihDictionary ihArgs stable ranges
    exact .dictionaryCall (ihDictionary stable (child ranges 0)) (ihArgs stable ranges 1)
  · intro σ a a' b b' left right ihLeft ihRight stable ranges
    exact .equal (ihLeft stable (child ranges 0)) (ihRight stable (child ranges 1))
  · intros; exact .nil
  · intro σ a b as bs head tail ihHead ihTail stable ranges offset
    exact .cons (ihHead stable (child ranges offset)) (ihTail stable ranges (offset + 1))

/-- Opening commutes with elaboration, with the existing freshness condition.
Sidecar annotations stay at their lexical sites when a binder is alpha-renamed. -/
theorem opening_substitutes (naming : Naming Domain Symbol) (ranges : Ranges Domain)
    (term : Term Variable Literal Symbol) (binder eigen : Variable)
    (fresh : eigen ∉ term.binderNames) :
    Substitutes (Substitution.single binder (.var eigen)) (elaborate naming ranges term)
      (elaborate naming ranges (term.openFree binder eigen)) := by
  apply elaboration_substitutes naming (term.openFree_substitutes binder eigen fresh)
  intro name policy
  simp only [Substitution.single, Substitution.bind]
  split <;> rfl

/-- `D_all(x) :- member_D(x)` for one declared domain. -/
def dataClause (naming : Naming Domain Symbol) (name : Variable) (domain : Domain) :
    HornClause Variable Literal Symbol :=
  .definite (.app naming.dataSymbol [.var name]) [.app (naming.membershipSymbol domain) [.var name]]

/-- `P_n(s).` for one registered declaration of `s` at arity n. -/
def predicateFact (naming : Naming Domain Symbol) (declaration : PredicateDeclaration Symbol) :
    HornClause Variable Literal Symbol :=
  .definite (.app (naming.predicateSymbol declaration.arity) [.app declaration.symbol []]) []

/-- Clauses generated from the signature: domain membership, D_all from each
domain, and one fact per registered predicate. `Realizes` makes guards true, but
`Derives` proves them only from KB clauses, so `E(KB)` includes these. The
registry enters the KB, not guard syntax: registering a predicate adds a fact. -/
def signatureKb (snapshot : SignatureSnapshot Domain Symbol) (names : Nat → Variable) :
    LogicalKb Variable Literal Symbol := fun clause =>
  clause ∈ membershipKb snapshot.signature.data.definitions snapshot.signature.membershipSymbol names ∨
    (∃ domain, dataClause snapshot.naming (names 0) domain = clause) ∨
    ∃ declaration ∈ snapshot.signature.predicates, predicateFact snapshot.naming declaration = clause

omit [DecidableEq Variable] in
/-- Registering more predicates only adds generated facts. With the same domains
and naming, a grown registry's signature clauses include the old ones, so
derivations from them stay valid (`Derives.mono`); lowered formulas, which read
only the naming, are unchanged. -/
theorem signatureKb_mono {snapshot grown : SignatureSnapshot Domain Symbol}
    (data : grown.signature.data = snapshot.signature.data) (naming : grown.naming = snapshot.naming)
    (registered : ∀ declaration ∈ snapshot.signature.predicates, declaration ∈ grown.signature.predicates)
    (names : Nat → Variable) (clause : HornClause Variable Literal Symbol)
    (member : clause ∈ signatureKb snapshot names) : clause ∈ signatureKb grown names := by
  have membership : grown.signature.membershipSymbol = snapshot.signature.membershipSymbol :=
    congrArg Naming.membershipSymbol naming
  rcases member with member | ⟨domain, rfl⟩ | ⟨declaration, declared, rfl⟩
  · left
    rw [data, membership]
    exact member
  · exact Or.inr (Or.inl ⟨domain, by rw [naming]⟩)
  · exact Or.inr (Or.inr ⟨declaration, registered _ declared, by rw [naming]⟩)

/-- A realizing model satisfies every generated clause. -/
theorem models_signatureKb (snapshot : SignatureSnapshot Domain Symbol)
    (model : Model Literal Symbol Value hoApplySymbol) (valid : AdmissionSignature.Realizes snapshot model)
    (names : Nat → Variable) : model.Models (signatureKb (Literal := Literal) snapshot names) := by
  rintro clause (member | ⟨domain, rfl⟩ | ⟨declaration, declared, rfl⟩) environment
  · exact models_membershipKb model valid.data names clause member environment
  · simp only [dataClause, HornClause.toFormula, Term.conjunction, List.foldr_cons, List.foldr_nil,
      Model.Satisfies, Model.eval, List.map_cons, List.map_nil, model.holds_implication,
      model.holds_conjunction]
    rintro ⟨holds, _⟩
    obtain ⟨tree, member, same⟩ := (valid.data domain _).mp holds
    exact (valid.allData _).mpr ⟨tree, ⟨domain, snapshot.signature.data.complete domain, member⟩, same⟩
  · simp only [predicateFact, HornClause.toFormula, Term.conjunction, List.foldr_nil, Model.Satisfies,
      Model.eval, List.map_cons, List.map_nil, model.holds_implication]
    intro _
    exact (valid.predicates _ _).mpr ⟨declaration.symbol, declared, rfl⟩

theorem rangeGuard_derives_data (snapshot : SignatureSnapshot Domain Symbol) {names : Nat → Variable}
    (distinct : DistinctNames snapshot.signature.data.definitions names)
    {kb : LogicalKb Variable Literal Symbol}
    (contains : ∀ clause, clause ∈ signatureKb snapshot names → clause ∈ kb)
    {context : ProofContext Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}
    {domains : List Domain} {tree : Tree Symbol}
    (member : InUnion snapshot.signature.data.definitions domains tree) :
    Derives hoApplySymbol kb context (rangeGuard snapshot.naming (.data domains) tree.toTerm) naf :=
  member.derives distinct (fun _ declared => contains _ (Or.inl (mem_membershipKb declared)))

theorem rangeGuard_derives_allData (snapshot : SignatureSnapshot Domain Symbol) {names : Nat → Variable}
    (distinct : DistinctNames snapshot.signature.data.definitions names)
    {kb : LogicalKb Variable Literal Symbol}
    (contains : ∀ clause, clause ∈ signatureKb snapshot names → clause ∈ kb)
    {context : ProofContext Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}
    {domain : Domain} {tree : Tree Symbol} (member : Member snapshot.signature.data.definitions domain tree) :
    Derives hoApplySymbol kb context (rangeGuard snapshot.naming .allData tree.toTerm) naf := by
  have clause : (dataClause snapshot.naming (names 0) domain : HornClause Variable Literal Symbol) ∈ kb :=
    contains _ (Or.inr (Or.inl ⟨domain, rfl⟩))
  have argument : SubstitutesList (Substitution.single (names 0) tree.toTerm)
      [(.var (names 0) : Term Variable Literal Symbol)] [tree.toTerm] := .cons (.singleVar _ _) .nil
  exact .clause clause (.app argument) (SubstitutesList.conjunction (.cons (.app argument) .nil))
    (.conjIntro (member.derives distinct (fun _ declared => contains _ (Or.inl (mem_membershipKb declared))))
      .truth)

/-- A registered reference derives its predicate guard from its generated fact.
This is lookup by symbol; no enumeration of the registry is involved. -/
theorem rangeGuard_derives_predicate (snapshot : SignatureSnapshot Domain Symbol) {names : Nat → Variable}
    {kb : LogicalKb Variable Literal Symbol}
    (contains : ∀ clause, clause ∈ signatureKb snapshot names → clause ∈ kb)
    {context : ProofContext Variable Literal Symbol} {naf : NafFailure Variable Literal Symbol}
    {symbol : Symbol} {arity : Nat} (declared : snapshot.Registered symbol arity) :
    Derives hoApplySymbol kb context
      (rangeGuard snapshot.naming (.predicate arity) (.app symbol [] : Term Variable Literal Symbol)) naf := by
  have fact : (predicateFact snapshot.naming ⟨symbol, arity⟩ : HornClause Variable Literal Symbol) ∈ kb :=
    contains _ (Or.inr (Or.inr ⟨⟨symbol, arity⟩, declared, rfl⟩))
  exact .clause (σ := Term.var) fact (Substitutes.identity _) (Substitutes.identity _) .truth

/-- Existential introduction checks the guard and body using one substitution.
The witness can be data, a predicate reference, or an arbitrary carrier term. -/
theorem existsRange_intro (naming : Naming Domain Symbol) (range : Range Domain)
    {kb : LogicalKb Variable Literal Symbol} {context : ProofContext Variable Literal Symbol}
    {naf : NafFailure Variable Literal Symbol} (binder : Variable)
    {body witness instanceBody : Term Variable Literal Symbol}
    (instantiation : Substitutes (Substitution.single binder witness) body instanceBody)
    (membership : Derives hoApplySymbol kb context (rangeGuard naming range witness) naf)
    (proof : Derives hoApplySymbol kb context instanceBody naf) :
    Derives hoApplySymbol kb context (existsRange naming range binder body) naf :=
  .existsIntro (.conj (rangeGuard_substitutes naming range (.singleVar binder witness)) instantiation)
    (.conjIntro membership proof)

mutual
/-- Value semantics of an annotated source term. Logical values can occur in
arguments, equality, and dictionary positions, so preservation must be value
equality, not merely equivalence of truth at the outermost formula. Quantifiers
use the foundation model's implication/conjunction values with exact range
guards; they do not assume extensionality of logical values. -/
def eval (naming : Naming Domain Symbol) (ranges : Ranges Domain)
    (model : Model Literal Symbol Value hoApplySymbol) (environment : Environment Variable Value) :
    Term Variable Literal Symbol → Value
  | .var name => environment name
  | .lit value => model.literal value
  | .app symbol args => model.application symbol (evalArgs naming ranges model environment 0 args)
  | .truth => model.top
  | .falsity => model.bottom
  | .conj a b => model.conjunction (eval naming (child ranges 0) model environment a)
      (eval naming (child ranges 1) model environment b)
  | .disj a b => model.disjunction (eval naming (child ranges 0) model environment a)
      (eval naming (child ranges 1) model environment b)
  | .imp a b => model.implication (eval naming (child ranges 0) model environment a)
      (eval naming (child ranges 1) model environment b)
  | .equal a b => model.equality (eval naming (child ranges 0) model environment a)
      (eval naming (child ranges 1) model environment b)
  | .defaultNeg body => model.defaultNegation (eval naming (child ranges 0) model environment body)
  | .forallVar binder body => model.universal (fun value =>
      model.implication (model.eval (update environment binder value) (rangeGuard naming (ranges []) (.var binder)))
        (eval naming (child ranges 0) model (update environment binder value) body))
  | .existsVar binder body => model.existential (fun value =>
      model.conjunction (model.eval (update environment binder value) (rangeGuard naming (ranges []) (.var binder)))
        (eval naming (child ranges 0) model (update environment binder value) body))
  | .dictionaryCall dictionary path operation args =>
      model.dictionaryCall (eval naming (child ranges 0) model environment dictionary) path operation
        (evalArgs naming ranges model environment 1 args)

def evalArgs (naming : Naming Domain Symbol) (ranges : Ranges Domain)
    (model : Model Literal Symbol Value hoApplySymbol) (environment : Environment Variable Value)
    (offset : Nat) : List (Term Variable Literal Symbol) → List Value
  | [] => []
  | head :: tail => eval naming (child ranges offset) model environment head ::
      evalArgs naming ranges model environment (offset + 1) tail
end

theorem eval_elaborate (naming : Naming Domain Symbol)
    (model : Model Literal Symbol Value hoApplySymbol) (term : Term Variable Literal Symbol) :
    ∀ ranges environment, model.eval environment (elaborate naming ranges term) =
      eval naming ranges model environment term := by
  refine Term.rec
    (motive_1 := fun term => ∀ ranges environment,
      model.eval environment (elaborate naming ranges term) = eval naming ranges model environment term)
    (motive_2 := fun args => ∀ ranges environment offset,
      (elaborateArgs naming ranges offset args).map (model.eval environment) =
        evalArgs naming ranges model environment offset args)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ term
  · intros; simp only [elaborate, Model.eval, eval]
  · intros; simp only [elaborate, Model.eval, eval]
  · intro symbol args ih ranges environment; simp only [elaborate, Model.eval, eval, ih]
  · intros; simp only [elaborate, Model.eval, eval]
  · intros; simp only [elaborate, Model.eval, eval]
  · intro a b left right ranges environment; simp only [elaborate, Model.eval, eval, left, right]
  · intro a b left right ranges environment; simp only [elaborate, Model.eval, eval, left, right]
  · intro a b left right ranges environment; simp only [elaborate, Model.eval, eval, left, right]
  · intro body ih ranges environment; simp only [elaborate, Model.eval, eval, ih]
  · intro binder body ih ranges environment; simp only [elaborate, forallRange, Model.eval, eval, ih]
  · intro binder body ih ranges environment; simp only [elaborate, existsRange, Model.eval, eval, ih]
  · intro dictionary path operation args left right ranges environment
    simp only [elaborate, Model.eval, eval, left, right]
  · intro a b left right ranges environment; simp only [elaborate, Model.eval, eval, left, right]
  · intros; simp only [elaborateArgs, List.map_nil, evalArgs]
  · intro head tail left right ranges environment offset
    simp only [elaborateArgs, List.map_cons, evalArgs, left, right]

theorem satisfies (naming : Naming Domain Symbol) (ranges : Ranges Domain)
    (model : Model Literal Symbol Value hoApplySymbol) (environment : Environment Variable Value)
    (term : Term Variable Literal Symbol) :
    model.Satisfies environment (elaborate naming ranges term) ↔
      model.holds (eval naming ranges model environment term) := by
  unfold Model.Satisfies
  rw [eval_elaborate]

theorem forall_satisfies (snapshot : SignatureSnapshot Domain Symbol) (ranges : Ranges Domain)
    (model : Model Literal Symbol Value hoApplySymbol) (valid : AdmissionSignature.Realizes snapshot model)
    (environment : Environment Variable Value) (binder : Variable) (body : Term Variable Literal Symbol) :
    model.Satisfies environment (elaborate snapshot.naming ranges (.forallVar binder body)) ↔
      ∀ value, (ranges []).Contains snapshot model value →
        model.holds (eval snapshot.naming (child ranges 0) model (update environment binder value) body) := by
  rw [elaborate, forallRange_satisfies snapshot model valid]
  simp only [satisfies]

theorem exists_satisfies (snapshot : SignatureSnapshot Domain Symbol) (ranges : Ranges Domain)
    (model : Model Literal Symbol Value hoApplySymbol) (valid : AdmissionSignature.Realizes snapshot model)
    (environment : Environment Variable Value) (binder : Variable) (body : Term Variable Literal Symbol) :
    model.Satisfies environment (elaborate snapshot.naming ranges (.existsVar binder body)) ↔
      ∃ value, (ranges []).Contains snapshot model value ∧
        model.holds (eval snapshot.naming (child ranges 0) model (update environment binder value) body) := by
  rw [elaborate, existsRange_satisfies snapshot model valid]
  simp only [satisfies]

/-- Context entries retain fixed free parameters; they acquire no implicit
universal closure. Entry i uses annotation child i, permitting distinct binder
ranges in different assumptions. -/
def elaborateContext (naming : Naming Domain Symbol) (ranges : Ranges Domain)
    (context : ProofContext Variable Literal Symbol) : ProofContext Variable Literal Symbol :=
  elaborateArgs naming ranges 0 context

theorem context_satisfies (naming : Naming Domain Symbol) (ranges : Ranges Domain)
    (model : Model Literal Symbol Value hoApplySymbol) (environment : Environment Variable Value)
    (context : ProofContext Variable Literal Symbol) :
    model.ContextHolds environment (elaborateContext naming ranges context) ↔
      ∀ value ∈ evalArgs naming ranges model environment 0 context, model.holds value := by
  have aux (terms : List (Term Variable Literal Symbol)) : ∀ offset,
      model.ContextHolds environment (elaborateArgs naming ranges offset terms) ↔
        ∀ value ∈ evalArgs naming ranges model environment offset terms, model.holds value := by
    induction terms with
    | nil => intro offset; simp [elaborateArgs, evalArgs, Model.ContextHolds]
    | cons head tail ih =>
        intro offset
        simp only [Model.ContextHolds] at ih ⊢
        simp only [elaborateArgs, evalArgs, List.forall_mem_cons, ih, satisfies]
  exact aux context 0

theorem context_fresh (naming : Naming Domain Symbol) (ranges : Ranges Domain)
    (context : ProofContext Variable Literal Symbol) (name : Variable) :
    FreshForContext name (elaborateContext naming ranges context) ↔ FreshForContext name context := by
  have aux (terms : List (Term Variable Literal Symbol)) : ∀ offset,
      FreshForContext name (elaborateArgs naming ranges offset terms) ↔ FreshForContext name terms := by
    induction terms with
    | nil => intro offset; simp [elaborateArgs, FreshForContext]
    | cons head tail ih =>
        intro offset
        simp only [FreshForContext] at ih ⊢
        simp only [elaborateArgs, List.forall_mem_cons, freeVars, ih]
  exact aux context 0

/-- Explicit binder metadata for each free clause variable. Repetitions in the
free-variable list are harmless: they repeat the same guard. `rangeOf` is
trusted here; `clausePredicateRanged` rejects a predicate template variable
that `rangeOf` leaves at a data range, so it gets its P_n guard, never D_all. -/
def clauseGuards (naming : Naming Domain Symbol) (rangeOf : Variable → Range Domain)
    (clause : HornClause Variable Literal Symbol) : List (Term Variable Literal Symbol) :=
  clause.toFormula.freeVars.map (fun name => rangeGuard naming (rangeOf name) (.var name))

/-- Head uses child 0, body formulas use children 1 onward. Guards share the
implicit universal closure of the original clause; head/body instances must use
the same capture-avoiding substitution. -/
def elaborateClause (naming : Naming Domain Symbol) (ranges : Ranges Domain)
    (rangeOf : Variable → Range Domain) (clause : HornClause Variable Literal Symbol) :
    HornClause Variable Literal Symbol :=
  match clause with
  | .definite head body => .definite (elaborate naming (child ranges 0) head)
      (clauseGuards naming rangeOf clause ++ elaborateArgs naming ranges 1 body)
  | .goal body => .goal (clauseGuards naming rangeOf clause ++ elaborateArgs naming ranges 1 body)

/-- Free clause variables are governed by `rangeOf`, bound names by `ranges`. -/
def clausePredicateRanged [DecidableEq Symbol] (hoApplySymbol : Symbol) (ranges : Ranges Domain)
    (rangeOf : Variable → Range Domain) : HornClause Variable Literal Symbol → Bool
  | .definite head body => predicateRanged hoApplySymbol (child ranges 0) (some ∘ rangeOf) head &&
      predicateRangedArgs hoApplySymbol ranges (some ∘ rangeOf) 1 body
  | .goal body => predicateRangedArgs hoApplySymbol ranges (some ∘ rangeOf) 1 body

/-- Executable-profile lowering of a rule template; see `elaborate?`. -/
def elaborateClause? [DecidableEq Symbol] (hoApplySymbol : Symbol)
    (naming : Naming Domain Symbol) (ranges : Ranges Domain)
    (rangeOf : Variable → Range Domain) (clause : HornClause Variable Literal Symbol) :
    Option (HornClause Variable Literal Symbol) :=
  if clausePredicateRanged hoApplySymbol ranges rangeOf clause then
    some (elaborateClause naming ranges rangeOf clause)
  else none

theorem elaborateClause?_eq_some [DecidableEq Symbol] (hoApplySymbol : Symbol)
    (naming : Naming Domain Symbol) (ranges : Ranges Domain)
    (rangeOf : Variable → Range Domain) (clause result : HornClause Variable Literal Symbol) :
    elaborateClause? hoApplySymbol naming ranges rangeOf clause = some result ↔
      clausePredicateRanged hoApplySymbol ranges rangeOf clause = true ∧
        elaborateClause naming ranges rangeOf clause = result := by
  unfold elaborateClause?
  split <;> simp_all

theorem clauseGuards_satisfies (snapshot : SignatureSnapshot Domain Symbol)
    (model : Model Literal Symbol Value hoApplySymbol) (valid : AdmissionSignature.Realizes snapshot model)
    (environment : Environment Variable Value) (rangeOf : Variable → Range Domain)
    (clause : HornClause Variable Literal Symbol) :
    model.Satisfies environment (.conjunction (clauseGuards snapshot.naming rangeOf clause)) ↔
      ∀ name ∈ clause.toFormula.freeVars, (rangeOf name).Contains snapshot model (environment name) := by
  rw [Model.satisfies_conjunction]
  simp only [clauseGuards, List.mem_map]
  constructor
  · intro all name member
    simpa only [Model.eval] using (rangeGuard_satisfies snapshot model valid environment (rangeOf name) (.var name)).mp
      (all _ ⟨name, member, rfl⟩)
  · rintro all _ ⟨name, member, rfl⟩
    simpa only [Model.eval] using (rangeGuard_satisfies snapshot model valid environment (rangeOf name) (.var name)).mpr (by simpa only [Model.eval] using all name member)

/-- This is the per-environment contract under the KB's ordinary implicit
universal closure. Guards restrict that environment without assuming coverage. -/
theorem clause_satisfies (snapshot : SignatureSnapshot Domain Symbol) (ranges : Ranges Domain)
    (model : Model Literal Symbol Value hoApplySymbol) (valid : AdmissionSignature.Realizes snapshot model)
    (environment : Environment Variable Value) (rangeOf : Variable → Range Domain)
    (clause : HornClause Variable Literal Symbol) :
    model.Satisfies environment (elaborateClause snapshot.naming ranges rangeOf clause).toFormula ↔
      ((∀ name ∈ clause.toFormula.freeVars, (rangeOf name).Contains snapshot model (environment name)) →
        ((∀ term ∈ elaborateArgs snapshot.naming ranges 1 (match clause with | .definite _ body | .goal body => body),
            model.Satisfies environment term) →
          model.Satisfies environment (match clause with
            | .definite head _ => elaborate snapshot.naming (child ranges 0) head | .goal _ => .falsity))) := by
  have guards := clauseGuards_satisfies snapshot model valid environment rangeOf clause
  rw [Model.satisfies_conjunction] at guards
  cases clause <;>
    simp only [elaborateClause, HornClause.toFormula, Model.Satisfies, Model.eval, model.holds_implication]
  all_goals
    change ((model.Satisfies environment (.conjunction (_ ++ _))) → _) ↔ _
    rw [Model.satisfies_conjunction]
    simp only [List.mem_append, or_imp, forall_and]
    rw [guards]
    exact and_imp

end AnthillModKbSpec.Elaboration
