import AnthillModKbSpec.Resolution.Elaboration

/-! # Structural induction principles (S12)

Every declared inductive domain `D` has a structural induction principle, an
ordinary KB clause with a compound head selected by its whole head (S11's
`headMatch`). For each constructor rule `c : D₁ × … × Dₖ → D` of `D` it has one
case, binding the fields, each guarded by its domain, with an induction
hypothesis for every field of `D` itself:

```text
(G_D(x) → ho_apply(P, x)) :-
    …, ∀y₁:D₁ … ∀yₖ:Dₖ. (ho_apply(P, yᵢ) → … → ho_apply(P, c(y₁, …, yₖ))), …
```

For Nat this is the base `ho_apply(P, zero)` and the step
`∀n:Nat. (ho_apply(P, n) → ho_apply(P, succ(n)))`; for Bool, two bases; for a
list, a base and a case with a guarded element and a hypothesis for the tail.
A field of another domain, also of a mutually recursive one, is guarded and
gets no hypothesis: the principle is for `D` alone.

The source clause is lowered by `elaborateClause?` with `P` at `.predicate 1`:
lowering adds the guard `P_1(P)` and each field's guard; a range on `P` that
does not admit a unary predicate, a data range or `D_all`, is rejected
(`lower_rejects`). `principle` is the lowered clause, built with the
guards in place; admission checks that lowering the source gives it.

Validity is a theorem, not an assumption: in every model realizing the
signature, exact membership makes the members of `D` the values built by its
rules, so a property satisfying every case holds of every member
(`principle_valid`). Only the realization of the data is used; the predicate
guard and the registry play no part. -/

namespace AnthillModKbSpec.Induction

open Semantics InductiveDomains AdmissionSignature Elaboration

variable {Domain Variable Literal Symbol Value : Type}

/-- The principle's names: its predicate `P`, its target `x`, and the bound
fields of a case, the i-th field `field i`. -/
structure Names (Variable : Type) where
  predicate : Variable
  target : Variable
  field : Nat → Variable

section Clause

variable [DecidableEq Domain]

/-- The listed rules with this result. -/
def rulesOf (rules : List (Rule Domain Symbol)) (domain : Domain) : List (Rule Domain Symbol) :=
  rules.filter fun rule => decide (rule.result = domain)

theorem mem_rulesOf {rules : List (Rule Domain Symbol)} {domain : Domain} {rule : Rule Domain Symbol} :
    rule ∈ rulesOf rules domain ↔ rule ∈ rules ∧ rule.result = domain := by
  simp [rulesOf]

/-- `ho_apply(P, t)`. -/
def applied (hoApplySymbol : Symbol) (predicate : Variable) (subject : Term Variable Literal Symbol) :
    Term Variable Literal Symbol :=
  .hoApply hoApplySymbol (.var predicate) [subject]

/-- The fields `field i, …, field (i + count - 1)` as terms. -/
def fieldVars (field : Nat → Variable) : Nat → Nat → List (Term Variable Literal Symbol)
  | _, 0 => []
  | index, count + 1 => .var (field index) :: fieldVars field (index + 1) count

/-- The hypotheses of the fields of the domain, from index `index`, then the
conclusion. -/
def hypotheses (hoApplySymbol : Symbol) (domain : Domain) (predicate : Variable) (field : Nat → Variable) :
    List Domain → Nat → Term Variable Literal Symbol → Term Variable Literal Symbol
  | [], _, conclusion => conclusion
  | fieldDomain :: rest, index, conclusion =>
      if fieldDomain = domain then
        .imp (applied hoApplySymbol predicate (.var (field index)))
          (hypotheses hoApplySymbol domain predicate field rest (index + 1) conclusion)
      else hypotheses hoApplySymbol domain predicate field rest (index + 1) conclusion

/-- A case's matrix: its hypotheses, then `P(c(y₀, …))`. -/
def matrix (hoApplySymbol : Symbol) (domain : Domain) (names : Names Variable) (rule : Rule Domain Symbol) :
    Term Variable Literal Symbol :=
  hypotheses hoApplySymbol domain names.predicate names.field rule.fields 0
    (applied hoApplySymbol names.predicate (.app rule.symbol (fieldVars names.field 0 rule.fields.length)))

/-- Bind the fields from index `index`, without guards: the source. -/
def bindFields (field : Nat → Variable) : List Domain → Nat → Term Variable Literal Symbol → Term Variable Literal Symbol
  | [], _, body => body
  | _ :: rest, index, body => .forallVar (field index) (bindFields field rest (index + 1) body)

/-- Bind the fields from index `index`, each guarded by its domain: the lowered form. -/
def guardFields (naming : Naming Domain Symbol) (field : Nat → Variable) :
    List Domain → Nat → Term Variable Literal Symbol → Term Variable Literal Symbol
  | [], _, body => body
  | fieldDomain :: rest, index, body =>
      forallRange naming (.data [fieldDomain]) (field index) (guardFields naming field rest (index + 1) body)

/-- The head `G_D(x) → ho_apply(P, x)`. -/
def head (hoApplySymbol : Symbol) (naming : Naming Domain Symbol) (domain : Domain) (names : Names Variable) :
    Term Variable Literal Symbol :=
  .imp (rangeGuard naming (.data [domain]) (.var names.target)) (applied hoApplySymbol names.predicate (.var names.target))

variable [DecidableEq Variable]

/-- The source clause: one unguarded case per rule of the domain, the fields'
ranges given by `ranges`. -/
def source (hoApplySymbol : Symbol) (naming : Naming Domain Symbol) (domain : Domain) (rules : List (Rule Domain Symbol))
    (names : Names Variable) : HornClause Variable Literal Symbol :=
  .definite (head hoApplySymbol naming domain names)
    ((rulesOf rules domain).map fun rule => bindFields names.field rule.fields 0 (matrix hoApplySymbol domain names rule))

/-- Binder ranges: the i-th binder of the j-th case, at the path
`(j + 1) :: [0, …, 0]` with i zeros, ranges over the rule's i-th field. -/
def ranges (domain : Domain) (rules : List (Rule Domain Symbol)) : Ranges Domain := fun path =>
  match path with
  | (case + 1) :: rest =>
      match (rulesOf rules domain)[case]? with
      | some rule =>
          if rest = List.replicate rest.length 0 then
            (rule.fields[rest.length]?.map fun fieldDomain => Range.data [fieldDomain]).getD .allData
          else .allData
      | none => .allData
  | _ => .allData

/-- The ranges of the clause's free names: `P` over the unary predicate
references, the target over the carrier, since the head's premise guards it. -/
def rangeOf (names : Names Variable) (predicateRange : Range Domain := .predicate 1) : Variable → Range Domain :=
  fun name => if name = names.predicate then predicateRange else .carrier

/-- The lowered principle: the guards lowering adds for the free names, then one
guarded case per rule. -/
def principle (hoApplySymbol : Symbol) (naming : Naming Domain Symbol) (domain : Domain)
    (rules : List (Rule Domain Symbol)) (names : Names Variable) : HornClause Variable Literal Symbol :=
  .definite (head hoApplySymbol naming domain names)
    (clauseGuards naming (rangeOf names) (source hoApplySymbol naming domain rules names) ++
      (rulesOf rules domain).map fun rule => guardFields naming names.field rule.fields 0
        (matrix hoApplySymbol domain names rule))

variable [DecidableEq Symbol]

/-- Lowering with a range on `P` that does not admit a unary predicate, a data
range or `D_all` among them, rejects the source clause: the head applies `P` by
`ho_apply`. -/
theorem lower_rejects (hoApplySymbol : Symbol) (naming : Naming Domain Symbol) (domain : Domain)
    (rules : List (Rule Domain Symbol)) (names : Names Variable) {range : Range Domain}
    (rejects : admitsPredicate range 1 = false) :
    elaborateClause? hoApplySymbol naming (ranges domain rules) (rangeOf names range)
      (source (Literal := Literal) hoApplySymbol naming domain rules names) = none := by
  simp [elaborateClause?, clausePredicateRanged, source, head, applied, predicateRanged, headRanged,
    rangeOf, Term.hoApply, Function.comp, rejects]

end Clause

/-! ## Admissible names -/

section Names

/-- The fields of every rule are distinct names, none the predicate; the target
is not the predicate; no constructor is `ho_apply`. -/
structure Admissible (hoApplySymbol : Symbol) (rules : List (Rule Domain Symbol)) (names : Names Variable) : Prop where
  fields_distinct : ∀ rule ∈ rules, ∀ first second, first < rule.fields.length → second < rule.fields.length →
    names.field first = names.field second → first = second
  fields_free : ∀ rule ∈ rules, ∀ index, index < rule.fields.length → names.field index ≠ names.predicate
  target_free : names.target ≠ names.predicate
  constructors_ordinary : ∀ rule ∈ rules, rule.symbol ≠ hoApplySymbol

variable [DecidableEq Variable] [DecidableEq Symbol]

/-- The decision of `Admissible`. -/
def admissible? (hoApplySymbol : Symbol) (rules : List (Rule Domain Symbol)) (names : Names Variable) : Bool :=
  rules.all (fun rule =>
    (List.range rule.fields.length).all (fun first => (List.range rule.fields.length).all fun second =>
      !decide (names.field first = names.field second) || first == second) &&
    (List.range rule.fields.length).all (fun index => !decide (names.field index = names.predicate)) &&
    !decide (rule.symbol = hoApplySymbol)) &&
  !decide (names.target = names.predicate)

theorem admissible?_spec {hoApplySymbol : Symbol} {rules : List (Rule Domain Symbol)} {names : Names Variable}
    (holds : admissible? hoApplySymbol rules names = true) : Admissible hoApplySymbol rules names := by
  simp only [admissible?, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, beq_iff_eq] at holds
  obtain ⟨perRule, target⟩ := holds
  refine ⟨fun rule member first second firstLt secondLt same => ?_, fun rule member index lt same => ?_, target,
    fun rule member => (perRule rule member).2⟩
  · rcases (perRule rule member).1.1 first firstLt second secondLt with different | equal
    · exact absurd same different
    · exact equal
  · exact (perRule rule member).1.2 index lt same

end Names

/-! ## Validity -/

section Validity

variable [DecidableEq Domain] [DecidableEq Variable] {hoApplySymbol : Symbol}

/-- Assign values to the fields from index `index`, in order. -/
def assign (environment : Environment Variable Value) (field : Nat → Variable) :
    Nat → List Value → Environment Variable Value
  | _, [] => environment
  | index, value :: rest => assign (update environment (field index) value) field (index + 1) rest

theorem assign_other {environment : Environment Variable Value} {field : Nat → Variable} {name : Variable} :
    ∀ {index : Nat} {values : List Value}, (∀ offset < values.length, field (index + offset) ≠ name) →
      assign environment field index values name = environment name
  | _, [], _ => rfl
  | index, value :: rest, other => by
      simp only [assign]
      rw [assign_other (fun offset lt => by
        simpa [Nat.add_assoc, Nat.add_comm 1 offset] using other (offset + 1) (by simp; omega))]
      have different : name ≠ field index := by simpa using (other 0 (by simp)).symm
      simp [update, different]

theorem assign_field {environment : Environment Variable Value} {field : Nat → Variable} :
    ∀ {index : Nat} {values : List Value},
      (∀ first second, first < values.length → second < values.length →
        field (index + first) = field (index + second) → first = second) →
      ∀ offset (lt : offset < values.length), assign environment field index values (field (index + offset)) = values[offset]
  | _, [], _, offset, lt => by simp at lt
  | index, value :: rest, distinct, offset, lt => by
      simp only [assign]
      cases offset with
      | zero =>
          rw [assign_other (fun later laterLt same => by
            have := distinct (later + 1) 0 (by simp; omega) (by simp)
              (by simpa [Nat.add_assoc, Nat.add_comm 1 later] using same)
            omega)]
          simp [update]
      | succ offset =>
          have shifted := assign_field (environment := update environment (field index) value)
            (index := index + 1) (values := rest)
            (fun first second firstLt secondLt same => by
              have := distinct (first + 1) (second + 1) (by simp; omega) (by simp; omega)
                (by simpa [Nat.add_assoc, Nat.add_comm 1 first, Nat.add_comm 1 second] using same)
              omega)
            offset (by simpa using lt)
          simpa [Nat.add_assoc, Nat.add_comm 1 offset] using shifted

theorem fieldVars_eval {model : Model Literal Symbol Value hoApplySymbol} {environment : Environment Variable Value}
    {field : Nat → Variable} :
    ∀ {index : Nat} {values : List Value},
      (∀ offset (lt : offset < values.length), environment (field (index + offset)) = values[offset]) →
      (fieldVars (Literal := Literal) (Symbol := Symbol) field index values.length).map (model.eval environment) = values
  | _, [], _ => rfl
  | index, value :: rest, read => by
      simp only [List.length_cons, fieldVars, List.map_cons, Model.eval]
      have first := read 0 (by simp)
      rw [Nat.add_zero] at first
      rw [show environment (field index) = value from first]
      rw [fieldVars_eval (index := index + 1) fun offset lt => by
        have later := read (offset + 1) (by simp; omega)
        rw [show index + (offset + 1) = index + 1 + offset by omega] at later
        exact later]

variable (snapshot : SignatureSnapshot Domain Symbol) (model : Model Literal Symbol Value hoApplySymbol)
  (valid : AdmissionSignature.Realizes snapshot model)

omit [DecidableEq Domain] in
include valid in
/-- A guarded case holds at values of the fields' domains. -/
theorem guardFields_satisfies {field : Nat → Variable} {body : Term Variable Literal Symbol} :
    ∀ {fields : List Domain} {index : Nat} {environment : Environment Variable Value},
      model.Satisfies environment (guardFields snapshot.naming field fields index body) →
      ∀ (values : List Value) (lengths : values.length = fields.length),
        (∀ offset (lt : offset < fields.length), (Range.data [fields[offset]]).Contains snapshot model
          (values[offset]'(lengths ▸ lt))) →
        model.Satisfies (assign environment field index values) body
  | [], _, _, holds, [], _, _ => holds
  | [], _, _, _, _ :: _, lengths, _ => by simp at lengths
  | _ :: _, _, _, _, [], lengths, _ => by simp at lengths
  | fieldDomain :: rest, index, environment, holds, value :: values, lengths, contained => by
      simp only [guardFields] at holds
      rw [forallRange_satisfies snapshot model valid] at holds
      exact guardFields_satisfies (holds value (contained 0 (by simp))) values (by simpa using lengths)
        fun offset lt => contained (offset + 1) (by simp; omega)

/-- A case's hypotheses give its conclusion. -/
theorem hypotheses_satisfies {domain : Domain} {predicate : Variable} {field : Nat → Variable}
    {conclusion : Term Variable Literal Symbol} :
    ∀ {fields : List Domain} {index : Nat} {environment : Environment Variable Value},
      model.Satisfies environment (hypotheses hoApplySymbol domain predicate field fields index conclusion) →
      (∀ offset (lt : offset < fields.length), fields[offset] = domain →
        model.Satisfies environment (applied hoApplySymbol predicate (.var (field (index + offset))))) →
      model.Satisfies environment conclusion
  | [], _, _, holds, _ => holds
  | fieldDomain :: rest, index, environment, holds, hypothesis => by
      have shifted : ∀ offset (lt : offset < rest.length), rest[offset] = domain →
          model.Satisfies environment (applied hoApplySymbol predicate (.var (field (index + 1 + offset)))) :=
        fun offset lt same => by
          simpa [Nat.add_assoc, Nat.add_comm 1 offset] using hypothesis (offset + 1) (by simp; omega) (by simpa using same)
      unfold hypotheses at holds
      split at holds
      · rename_i same
        simp only [Model.Satisfies, Model.eval, model.holds_implication] at holds
        exact hypotheses_satisfies (holds (by simpa using hypothesis 0 (by simp) (by simpa using same) :
          model.Satisfies environment (applied hoApplySymbol predicate (.var (field index))))) shifted
      · exact hypotheses_satisfies holds shifted

include valid in
/-- In every model realizing the signature, the principle is true for every
value of `P` and `x`: the members of the domain are the values its rules
build, so a property satisfying every case holds of every member. Only the
domain's realization is used; the predicate guard and the registry are not. -/
theorem principle_valid {rules : List (Rule Domain Symbol)}
    (complete : ∀ rule, snapshot.signature.data.definitions rule → rule ∈ rules) {domain : Domain}
    {names : Names Variable} (admissible : Admissible hoApplySymbol (rulesOf rules domain) names)
    (environment : Environment Variable Value) :
    model.Satisfies environment (principle hoApplySymbol snapshot.naming domain rules names).toFormula := by
  simp only [principle, HornClause.toFormula, Model.Satisfies, Model.eval, model.holds_implication]
  intro bodyHolds
  have cases : ∀ rule ∈ rulesOf rules domain, model.Satisfies environment
      (guardFields snapshot.naming names.field rule.fields 0 (matrix hoApplySymbol domain names rule)) := by
    intro rule member
    have all := (Model.satisfies_conjunction model environment _).mp bodyHolds
    exact all _ (List.mem_append_right _ (List.mem_map_of_mem member))
  let holdsAt := fun value => model.holds (model.application hoApplySymbol [environment names.predicate, value])
  have members : ∀ {member : Domain} {tree : Tree Symbol}, Member snapshot.signature.data.definitions member tree →
      member = domain → holdsAt (denote model tree) := by
    intro member tree inside
    induction inside with
    | construct declared children members ih =>
        rename_i rule
        intro result
        have inside := mem_rulesOf.mpr ⟨complete rule declared, result⟩
        let values := List.ofFn fun index => denote model (children index)
        have lengths : values.length = rule.fields.length := by simp [values]
        have assigned := guardFields_satisfies snapshot model valid (cases rule inside) values lengths
          fun offset lt => ⟨children ⟨offset, lt⟩,
            ⟨rule.fields[offset], List.mem_singleton_self _, by simpa using members ⟨offset, lt⟩⟩, by simp [values]⟩
        have readField : ∀ offset (lt : offset < values.length),
            assign environment names.field 0 values (names.field (0 + offset)) = values[offset] :=
          assign_field (fun first second firstLt secondLt same =>
            admissible.fields_distinct rule inside first second (lengths ▸ firstLt) (lengths ▸ secondLt)
              (by simpa using same))
        have readPredicate : assign environment names.field 0 values names.predicate = environment names.predicate :=
          assign_other fun offset lt => admissible.fields_free rule inside (0 + offset) (by simpa [lengths] using lt)
        have concluded := hypotheses_satisfies model assigned fun offset lt same => by
          have child := ih ⟨offset, lt⟩ same
          simp only [applied, Model.Satisfies, Model.eval, Term.hoApply, List.map_cons, List.map_nil]
          rw [readPredicate, readField offset (lengths ▸ lt)]
          simpa [values, holdsAt] using child
        simp only [applied, Model.Satisfies, Model.eval, Term.hoApply, List.map_cons, List.map_nil, ← lengths]
          at concluded
        rw [readPredicate, fieldVars_eval readField] at concluded
        simpa [denote, values, holdsAt, List.map_ofFn, Function.comp_def] using concluded
  simp only [head, applied, Model.eval, Term.hoApply, model.holds_implication]
  intro guarded
  have contained := (rangeGuard_satisfies snapshot model valid environment (.data [domain]) (.var names.target)).mp
    guarded
  obtain ⟨tree, ⟨member, selected, inside⟩, same⟩ := contained
  simp only [List.mem_singleton] at selected
  have result := members inside selected
  rw [same] at result
  simpa [holdsAt, Model.eval] using result

end Validity

end AnthillModKbSpec.Induction
