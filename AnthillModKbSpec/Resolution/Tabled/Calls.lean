import AnthillModKbSpec.Resolution.Tabled.Admission

/-! # Calls of complete predicates (S23)

The guarantee S24 runs on: a complete predicate makes finitely many distinct
calls from any ground input. The calls are those of an evaluation of the
predicate's clauses (`Binds`, `CallIn`) against any answer relation whose
predicates with data-term outputs (`dataOutputs`) answer data terms
(`AnswersBounded`), as every derivable answer does (`outputs_bounded`, by
induction on derivations).

- **Data terms** (`InData`): the subterms of a call's inputs and of ground
  terms covering the program's (`constants`; a query's `queryConstants` adds
  its context's and goal's, which its context facts answer). They form an
  explicit finite list (`dataTerms`).
- **Soundness of the analysis** (`flow_sound`, `site_of_call`): every name
  `flow` marks holds a data term, and every call `sites` marks small has
  data-term inputs; one it marks decreasing has inputs of smaller size.
- **Finitely many calls** (`calls_bounded`): from a ground input `ū`, every
  call a complete predicate's component makes, transitively, has inputs among
  the data terms of `ū`: at most `|component| · |dataTerms ū|ᵃ` calls of
  arity `a`.
- **Finitely many answers**: in a component with data-term outputs, every
  answer is a data term of its call (`outputs_bounded`); in a decreasing
  component, every recursive call's inputs are smaller (`calls_decrease`), so
  no call repeats.

Calls into a lower component are its own entries: the theorem applies to
them in turn, along the component order. -/

namespace AnthillModKbSpec.Tabled

open Admission

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]

attribute [local instance] Machine.termEq

/-! ## Values -/

/-- The values of names: a partial environment. -/
abbrev Env (Variable Literal Symbol : Type) := Variable → Option (Term Variable Literal Symbol)

/-- Rebind one name. -/
def Env.set (env : Env Variable Literal Symbol) (name : Variable) (value : Option (Term Variable Literal Symbol)) :
    Env Variable Literal Symbol :=
  fun other => if other = name then value else env other

omit [DecidableEq Literal] [DecidableEq Symbol] in
@[simp] theorem Env.set_same (env : Env Variable Literal Symbol) (name : Variable) (value : Option (Term Variable Literal Symbol)) :
    env.set name value name = value := by simp [Env.set]

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem Env.set_other (env : Env Variable Literal Symbol) {name other : Variable} (value : Option (Term Variable Literal Symbol))
    (different : other ≠ name) : env.set name value other = env other := by simp [Env.set, different]

mutual
/-- Instantiate a data term: names by their values. A name without a value,
or a term that is not data, gives none. -/
def inst (env : Env Variable Literal Symbol) : Term Variable Literal Symbol → Option (Term Variable Literal Symbol)
  | .var name => env name
  | .lit value => some (.lit value)
  | .app symbol args => (instAll env args).map (.app symbol)
  | _ => none

def instAll (env : Env Variable Literal Symbol) : List (Term Variable Literal Symbol) →
    Option (List (Term Variable Literal Symbol))
  | [] => some []
  | arg :: rest =>
      match inst env arg, instAll env rest with
      | some value, some values => some (value :: values)
      | _, _ => none
end

/-- The subterm relation of data terms. -/
inductive Subterm : Term Variable Literal Symbol → Term Variable Literal Symbol → Prop
  | refl (term : Term Variable Literal Symbol) : Subterm term term
  | arg {part arg : Term Variable Literal Symbol} {symbol : Symbol} {args : List (Term Variable Literal Symbol)} :
      arg ∈ args → Subterm part arg → Subterm part (.app symbol args)

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem Subterm.trans {first second third : Term Variable Literal Symbol} (inner : Subterm first second)
    (outer : Subterm second third) : Subterm first third := by
  induction outer with
  | refl => exact inner
  | arg member _ ih => exact .arg member ih

mutual
/-- The size of a term: its nodes. -/
def size : Term Variable Literal Symbol → Nat
  | .app _ args => sizeAll args + 1
  | _ => 1

def sizeAll : List (Term Variable Literal Symbol) → Nat
  | [] => 0
  | arg :: rest => size arg + sizeAll rest
end

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem size_pos (term : Term Variable Literal Symbol) : 0 < size term := by
  cases term <;> simp [size]

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem size_le_sizeAll {arg : Term Variable Literal Symbol} :
    ∀ {args : List (Term Variable Literal Symbol)}, arg ∈ args → size arg ≤ sizeAll args
  | [], member => by cases member
  | first :: rest, member => by
      rcases List.mem_cons.mp member with rfl | inside
      · simp only [sizeAll]; omega
      · have := size_le_sizeAll inside
        simp only [sizeAll]; omega

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem Subterm.size_le {part term : Term Variable Literal Symbol} (sub : Subterm part term) : size part ≤ size term := by
  induction sub with
  | refl => exact Nat.le_refl _
  | arg member _ ih =>
      have := size_le_sizeAll member
      simp only [size]; omega


/-! ## Instantiation lemmas -/

omit [DecidableEq Literal] [DecidableEq Symbol] in
mutual
theorem inst_congr {first second : Env Variable Literal Symbol} :
    ∀ (term : Term Variable Literal Symbol), (∀ name ∈ term.freeVars, first name = second name) →
      inst first term = inst second term
  | .var name, same => by simp only [inst]; exact same name (by simp [Term.freeVars])
  | .lit _, _ => rfl
  | .app symbol args, same => by
      simp only [inst]
      rw [instAll_congr args fun name member => same name (by simpa [Term.freeVars] using member)]
  | .truth, _ | .falsity, _ => rfl
  | .conj _ _, _ | .disj _ _, _ | .imp _ _, _ | .defaultNeg _, _ | .forallVar _ _, _ | .existsVar _ _, _ => rfl
  | .dictionaryCall _ _ _ _, _ | .equal _ _, _ => rfl

theorem instAll_congr {first second : Env Variable Literal Symbol} :
    ∀ (terms : List (Term Variable Literal Symbol)), (∀ name ∈ terms.flatMap Term.freeVars, first name = second name) →
      instAll first terms = instAll second terms
  | [], _ => rfl
  | term :: rest, same => by
      simp only [instAll]
      rw [inst_congr term fun name member => same name (List.mem_append_left _ member),
        instAll_congr rest fun name member => same name (List.mem_append_right _ member)]
end

/-- `env'` keeps every value of `env`. -/
def Extends (env env' : Env Variable Literal Symbol) : Prop :=
  ∀ name value, env name = some value → env' name = some value

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem Extends.refl (env : Env Variable Literal Symbol) : Extends env env := fun _ _ same => same

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem Extends.trans {first second third : Env Variable Literal Symbol} (left : Extends first second)
    (right : Extends second third) : Extends first third := fun name value same => right name value (left name value same)

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
mutual
theorem inst_extends {env env' : Env Variable Literal Symbol} (more : Extends env env') :
    ∀ {term : Term Variable Literal Symbol} {value : Term Variable Literal Symbol}, inst env term = some value →
      inst env' term = some value
  | .var name, _, found => more name _ found
  | .lit _, _, found => found
  | .app symbol args, value, found => by
      simp only [inst] at found ⊢
      cases instEq : instAll env args with
      | none => rw [instEq] at found; cases found
      | some values =>
          rw [instEq] at found
          rw [instAll_extends more instEq]
          exact found
  | .truth, _, found | .falsity, _, found => by cases found
  | .conj _ _, _, found | .disj _ _, _, found | .imp _ _, _, found => by cases found
  | .defaultNeg _, _, found | .forallVar _ _, _, found | .existsVar _ _, _, found => by cases found
  | .dictionaryCall _ _ _ _, _, found | .equal _ _, _, found => by cases found

theorem instAll_extends {env env' : Env Variable Literal Symbol} (more : Extends env env') :
    ∀ {terms : List (Term Variable Literal Symbol)} {values : List (Term Variable Literal Symbol)},
      instAll env terms = some values → instAll env' terms = some values
  | [], _, found => found
  | term :: rest, values, found => by
      simp only [instAll] at found ⊢
      cases first : inst env term with
      | none => rw [first] at found; cases found
      | some value =>
          cases second : instAll env rest with
          | none => rw [first, second] at found; cases found
          | some more' =>
              rw [first, second] at found
              rw [inst_extends more first, instAll_extends more second]
              exact found
end

omit [DecidableEq Literal] [DecidableEq Symbol] in
mutual
/-- A name of an instantiated term holds a subterm of the result. -/
theorem inst_name {env : Env Variable Literal Symbol} :
    ∀ {term value : Term Variable Literal Symbol}, inst env term = some value → ∀ name ∈ term.freeVars,
      ∃ part, env name = some part ∧ Subterm part value
  | .var name, value, found, other, member => by
      simp only [Term.freeVars, List.mem_singleton] at member
      subst member
      exact ⟨value, found, .refl _⟩
  | .lit _, _, _, _, member => by simp [Term.freeVars] at member
  | .app symbol args, value, found, name, member => by
      simp only [inst] at found
      cases instEq : instAll env args with
      | none => rw [instEq] at found; cases found
      | some values =>
          rw [instEq] at found
          cases found
          obtain ⟨part, bound, arg, argMember, sub⟩ := instAll_name instEq name (by simpa [Term.freeVars] using member)
          exact ⟨part, bound, .arg argMember sub⟩
  | .truth, _, found, _, _ | .falsity, _, found, _, _ => by cases found
  | .conj _ _, _, found, _, _ | .disj _ _, _, found, _, _ | .imp _ _, _, found, _, _ => by cases found
  | .defaultNeg _, _, found, _, _ | .forallVar _ _, _, found, _, _ | .existsVar _ _, _, found, _, _ => by cases found
  | .dictionaryCall _ _ _ _, _, found, _, _ | .equal _ _, _, found, _, _ => by cases found

theorem instAll_name {env : Env Variable Literal Symbol} :
    ∀ {terms values : List (Term Variable Literal Symbol)}, instAll env terms = some values →
      ∀ name ∈ terms.flatMap Term.freeVars, ∃ part, env name = some part ∧ ∃ value ∈ values, Subterm part value
  | [], _, _, _, member => by cases member
  | term :: rest, values, found, name, member => by
      simp only [instAll] at found
      cases first : inst env term with
      | none => rw [first] at found; cases found
      | some value =>
          cases second : instAll env rest with
          | none => rw [first, second] at found; cases found
          | some more =>
              rw [first, second] at found
              cases found
              rcases List.mem_append.mp member with here | there
              · obtain ⟨part, bound, sub⟩ := inst_name first name here
                exact ⟨part, bound, value, List.mem_cons_self, sub⟩
              · obtain ⟨part, bound, other, otherMember, sub⟩ := instAll_name second name there
                exact ⟨part, bound, other, List.mem_cons_of_mem _ otherMember, sub⟩
end

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem instAll_mem {env : Env Variable Literal Symbol} :
    ∀ {terms values : List (Term Variable Literal Symbol)}, instAll env terms = some values →
      ∀ value ∈ values, ∃ term ∈ terms, inst env term = some value
  | [], values, found, value, member => by simp only [instAll] at found; cases found; cases member
  | term :: rest, values, found, value, member => by
      simp only [instAll] at found
      cases first : inst env term with
      | none => rw [first] at found; cases found
      | some head =>
          cases second : instAll env rest with
          | none => rw [first, second] at found; cases found
          | some more =>
              rw [first, second] at found
              cases found
              rcases List.mem_cons.mp member with rfl | inside
              · exact ⟨term, List.mem_cons_self, first⟩
              · obtain ⟨other, otherMember, otherInst⟩ := instAll_mem second value inside
                exact ⟨other, List.mem_cons_of_mem _ otherMember, otherInst⟩

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
/-- Every term with a value gives one: `instAll` succeeds. -/
theorem instAll_of_mem {env : Env Variable Literal Symbol} :
    ∀ {terms : List (Term Variable Literal Symbol)}, (∀ term ∈ terms, ∃ value, inst env term = some value) →
      ∃ values, instAll env terms = some values
  | [], _ => ⟨[], rfl⟩
  | term :: rest, every => by
      obtain ⟨value, first⟩ := every term List.mem_cons_self
      obtain ⟨values, second⟩ := instAll_of_mem (terms := rest) fun other member => every other (List.mem_cons_of_mem _ member)
      exact ⟨value :: values, by simp only [instAll, first, second]⟩

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
mutual
/-- A ground data term is its own value. -/
theorem inst_closed {env : Env Variable Literal Symbol} :
    ∀ {term : Term Variable Literal Symbol}, closedData term = true → inst env term = some term
  | .lit _, _ => rfl
  | .app symbol args, closed => by
      simp only [closedData] at closed
      simp only [inst, instAll_closed closed, Option.map_some]
  | .var _, closed | .truth, closed | .falsity, closed => by simp [closedData] at closed
  | .conj _ _, closed | .disj _ _, closed | .imp _ _, closed => by simp [closedData] at closed
  | .defaultNeg _, closed | .forallVar _ _, closed | .existsVar _ _, closed => by simp [closedData] at closed
  | .dictionaryCall _ _ _ _, closed | .equal _ _, closed => by simp [closedData] at closed

theorem instAll_closed {env : Env Variable Literal Symbol} :
    ∀ {terms : List (Term Variable Literal Symbol)}, closedDataIn terms = true → instAll env terms = some terms
  | [], _ => rfl
  | term :: rest, closed => by
      simp only [closedDataIn, Bool.and_eq_true] at closed
      simp only [instAll, inst_closed closed.1, instAll_closed closed.2]
end

mutual
/-- A subterm of a pattern instantiates to a subterm of the pattern's value,
a strict one to a strictly smaller value. -/
theorem occurs_inst {env : Env Variable Literal Symbol} {part : Term Variable Literal Symbol} :
    ∀ {term value : Term Variable Literal Symbol}, occurs part term = true → inst env term = some value →
      ∃ partValue, inst env part = some partValue ∧ Subterm partValue value
  | .app symbol args, value, found, instEq => by
      simp only [occurs, Bool.or_eq_true, decide_eq_true_eq] at found
      rcases found with same | deeper
      · subst same; exact ⟨value, instEq, .refl _⟩
      · simp only [inst] at instEq
        cases valuesEq : instAll env args with
        | none => rw [valuesEq] at instEq; cases instEq
        | some values =>
            rw [valuesEq] at instEq
            cases instEq
            obtain ⟨partValue, partInst, arg, argMember, sub⟩ := occursIn_inst deeper valuesEq
            exact ⟨partValue, partInst, .arg argMember sub⟩
  | .var name, value, found, instEq | .lit name, value, found, instEq => by
      simp only [occurs, decide_eq_true_eq] at found
      subst found; exact ⟨value, instEq, .refl _⟩
  | .truth, _, _, instEq | .falsity, _, _, instEq => by cases instEq
  | .conj _ _, _, _, instEq | .disj _ _, _, _, instEq | .imp _ _, _, _, instEq => by cases instEq
  | .defaultNeg _, _, _, instEq | .forallVar _ _, _, _, instEq | .existsVar _ _, _, _, instEq => by cases instEq
  | .dictionaryCall _ _ _ _, _, _, instEq | .equal _ _, _, _, instEq => by cases instEq

theorem occursIn_inst {env : Env Variable Literal Symbol} {part : Term Variable Literal Symbol} :
    ∀ {terms values : List (Term Variable Literal Symbol)}, occursIn part terms = true → instAll env terms = some values →
      ∃ partValue, inst env part = some partValue ∧ ∃ value ∈ values, Subterm partValue value
  | [], _, found, _ => by simp [occursIn] at found
  | term :: rest, values, found, instEq => by
      simp only [instAll] at instEq
      cases first : inst env term with
      | none => rw [first] at instEq; cases instEq
      | some value =>
          cases second : instAll env rest with
          | none => rw [first, second] at instEq; cases instEq
          | some more =>
              rw [first, second] at instEq
              cases instEq
              simp only [occursIn, Bool.or_eq_true] at found
              rcases found with here | there
              · obtain ⟨partValue, partInst, sub⟩ := occurs_inst here first
                exact ⟨partValue, partInst, value, List.mem_cons_self, sub⟩
              · obtain ⟨partValue, partInst, other, otherMember, sub⟩ := occursIn_inst there second
                exact ⟨partValue, partInst, other, List.mem_cons_of_mem _ otherMember, sub⟩
end

theorem inside_inst {env : Env Variable Literal Symbol} {part term value : Term Variable Literal Symbol}
    (found : inside part term = true) (instEq : inst env term = some value) :
    ∃ partValue, inst env part = some partValue ∧ size partValue < size value := by
  cases term with
  | app symbol args =>
      simp only [inside] at found
      simp only [inst] at instEq
      cases valuesEq : instAll env args with
      | none => rw [valuesEq] at instEq; cases instEq
      | some values =>
          rw [valuesEq] at instEq
          cases instEq
          obtain ⟨partValue, partInst, arg, argMember, sub⟩ := occursIn_inst found valuesEq
          refine ⟨partValue, partInst, ?_⟩
          have := sub.size_le
          have := size_le_sizeAll argMember
          simp only [size]; omega
  | _ => simp [inside] at found

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem instAll_values {env : Env Variable Literal Symbol} :
    ∀ {terms values : List (Term Variable Literal Symbol)}, instAll env terms = some values →
      ∀ term ∈ terms, ∃ value ∈ values, inst env term = some value
  | [], _, _, _, member => by cases member
  | term :: rest, values, found, other, member => by
      simp only [instAll] at found
      cases first : inst env term with
      | none => rw [first] at found; cases found
      | some head =>
          cases second : instAll env rest with
          | none => rw [first, second] at found; cases found
          | some more =>
              rw [first, second] at found
              cases found
              rcases List.mem_cons.mp member with rfl | inside
              · exact ⟨head, List.mem_cons_self, first⟩
              · obtain ⟨value, valueMember, valueInst⟩ := instAll_values second other inside
                exact ⟨value, List.mem_cons_of_mem _ valueMember, valueInst⟩

mutual
theorem occurs_freeVars {part : Term Variable Literal Symbol} :
    ∀ {term : Term Variable Literal Symbol}, occurs part term = true → ∀ name ∈ part.freeVars, name ∈ term.freeVars
  | .app symbol args, found, name, member => by
      simp only [occurs, Bool.or_eq_true, decide_eq_true_eq] at found
      rcases found with same | deeper
      · subst same; exact member
      · simp only [Term.freeVars]; exact occursIn_freeVars deeper name member
  | .var _, found, name, member | .lit _, found, name, member | .truth, found, name, member
  | .falsity, found, name, member | .conj _ _, found, name, member | .disj _ _, found, name, member
  | .imp _ _, found, name, member | .defaultNeg _, found, name, member | .forallVar _ _, found, name, member
  | .existsVar _ _, found, name, member | .dictionaryCall _ _ _ _, found, name, member
  | .equal _ _, found, name, member => by
      simp only [occurs, decide_eq_true_eq] at found
      subst found; exact member

theorem occursIn_freeVars {part : Term Variable Literal Symbol} :
    ∀ {terms : List (Term Variable Literal Symbol)}, occursIn part terms = true →
      ∀ name ∈ part.freeVars, name ∈ terms.flatMap Term.freeVars
  | [], found, _, _ => by simp [occursIn] at found
  | term :: rest, found, name, member => by
      simp only [occursIn, Bool.or_eq_true] at found
      rcases found with here | there
      · exact List.mem_append_left _ (occurs_freeVars here name member)
      · exact List.mem_append_right _ (occursIn_freeVars there name member)
end

/-! ## Data terms -/

mutual
/-- The ground data terms occurring in a term, at any depth. -/
def grounds : Term Variable Literal Symbol → List (Term Variable Literal Symbol)
  | .app symbol args => (if closedData (.app symbol args) then [.app symbol args] else []) ++ groundsAll args
  | .lit value => [.lit value]
  | .conj left right | .disj left right | .imp left right | .equal left right => grounds left ++ grounds right
  | .defaultNeg body | .forallVar _ body | .existsVar _ body => grounds body
  | .dictionaryCall dictionary _ _ args => grounds dictionary ++ groundsAll args
  | _ => []

def groundsAll : List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol)
  | [] => []
  | term :: rest => grounds term ++ groundsAll rest
end

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem mem_grounds_self {term : Term Variable Literal Symbol} (closed : closedData term = true) : term ∈ grounds term := by
  cases term with
  | lit _ => simp [grounds]
  | app symbol args => simp [grounds, closed]
  | _ => simp [closedData] at closed

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem groundsAll_sub {term : Term Variable Literal Symbol} :
    ∀ {terms : List (Term Variable Literal Symbol)}, term ∈ terms → ∀ found ∈ grounds term, found ∈ groundsAll terms
  | [], member => by cases member
  | first :: rest, member => by
      intro found inside
      simp only [groundsAll, List.mem_append]
      rcases List.mem_cons.mp member with rfl | there
      · exact .inl inside
      · exact .inr (groundsAll_sub there found inside)

/-- The ground terms of the program's clauses. -/
def Program.constants (program : Program Variable Literal Symbol) : List (Term Variable Literal Symbol) :=
  program.clauses.flatMap fun (_, clause) =>
    match clause with
    | .definite head body => grounds head ++ body.flatMap grounds
    | .goal body => body.flatMap grounds

/-- The data terms of a call with input values `inputs`: subterms of its
inputs and of the program's ground terms `ground`. -/
def InData (ground inputs : List (Term Variable Literal Symbol)) (value : Term Variable Literal Symbol) : Prop :=
  (∃ input ∈ inputs, Subterm value input) ∨ ∃ constant ∈ ground, Subterm value constant

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem InData.sub {ground inputs : List (Term Variable Literal Symbol)} {part value : Term Variable Literal Symbol}
    (inData : InData ground inputs value) (sub : Subterm part value) : InData ground inputs part := by
  rcases inData with ⟨input, member, inside⟩ | ⟨constant, member, inside⟩
  · exact .inl ⟨input, member, sub.trans inside⟩
  · exact .inr ⟨constant, member, sub.trans inside⟩

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
/-- Data terms of data terms are data terms. -/
theorem InData.trans {ground first second : List (Term Variable Literal Symbol)} {value : Term Variable Literal Symbol}
    (inData : InData ground second value) (every : ∀ other ∈ second, InData ground first other) :
    InData ground first value := by
  rcases inData with ⟨input, member, inside⟩ | ⟨constant, member, inside⟩
  · exact (every input member).sub inside
  · exact .inr ⟨constant, member, inside⟩

mutual
/-- The subterms of a term, the term included. -/
def subterms : Term Variable Literal Symbol → List (Term Variable Literal Symbol)
  | .app symbol args => .app symbol args :: subtermsAll args
  | term => [term]

def subtermsAll : List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol)
  | [] => []
  | term :: rest => subterms term ++ subtermsAll rest
end

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem mem_subtermsAll {part arg : Term Variable Literal Symbol} :
    ∀ {terms : List (Term Variable Literal Symbol)}, arg ∈ terms → part ∈ subterms arg → part ∈ subtermsAll terms
  | [], member, _ => by cases member
  | first :: rest, member, inside => by
      simp only [subtermsAll, List.mem_append]
      rcases List.mem_cons.mp member with rfl | there
      · exact .inl inside
      · exact .inr (mem_subtermsAll there inside)

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem self_mem_subterms (term : Term Variable Literal Symbol) : term ∈ subterms term := by
  cases term <;> simp [subterms]

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem mem_subterms {part term : Term Variable Literal Symbol} (sub : Subterm part term) : part ∈ subterms term := by
  induction sub with
  | refl => exact self_mem_subterms _
  | arg member _ ih =>
      simp only [subterms, List.mem_cons]
      exact .inr (mem_subtermsAll member ih)

/-- The data terms of a call, as a finite list. -/
def dataTerms (ground inputs : List (Term Variable Literal Symbol)) : List (Term Variable Literal Symbol) :=
  subtermsAll inputs ++ subtermsAll ground

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem InData.mem {ground inputs : List (Term Variable Literal Symbol)} {value : Term Variable Literal Symbol}
    (inData : InData ground inputs value) : value ∈ dataTerms ground inputs := by
  rcases inData with ⟨input, member, inside⟩ | ⟨constant, member, inside⟩
  · exact List.mem_append_left _ (mem_subtermsAll member (mem_subterms inside))
  · exact List.mem_append_right _ (mem_subtermsAll member (mem_subterms inside))

/-! ## Evaluation -/

namespace Program

variable (program : Program Variable Literal Symbol)

/-- Evaluating a goal against an answer relation, from the values before it
to the values after it. `answers predicate inputs outputs`: a call with these
input values has an answer with these output values. A guard or a marker is
checked and binds nothing; NAF binds nothing; a binder's name is rebound in
its body, an eigenvariable to any value. The antecedent of an implication
adds facts, which `answers` already holds. -/
inductive Binds (answers : Symbol → List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) → Prop) :
    Env Variable Literal Symbol → Term Variable Literal Symbol → Env Variable Literal Symbol → Prop
  | truth {env : Env Variable Literal Symbol} : Binds answers env .truth env
  | call {env env' : Env Variable Literal Symbol} {goal : Term Variable Literal Symbol} {predicate : Symbol}
      {args inputs outputs values results : List (Term Variable Literal Symbol)} :
      program.callOf? goal = some (predicate, args) → program.io? predicate args = some (inputs, outputs) →
      instAll env inputs = some values → answers predicate values results → Extends env env' →
      instAll env' outputs = some results → Binds answers env goal env'
  | check {env : Env Variable Literal Symbol} {symbol : Symbol} {args : List (Term Variable Literal Symbol)} :
      program.callOf? (.app symbol args) = none → Binds answers env (.app symbol args) env
  | conj {env middle env' : Env Variable Literal Symbol} {left right : Term Variable Literal Symbol} :
      Binds answers env left middle → Binds answers middle right env' → Binds answers env (.conj left right) env'
  | disjLeft {env env' : Env Variable Literal Symbol} {left right : Term Variable Literal Symbol} :
      Binds answers env left env' → Binds answers env (.disj left right) env'
  | disjRight {env env' : Env Variable Literal Symbol} {left right : Term Variable Literal Symbol} :
      Binds answers env right env' → Binds answers env (.disj left right) env'
  | negation {env : Env Variable Literal Symbol} {operand : Term Variable Literal Symbol} :
      Binds answers env (.defaultNeg operand) env
  | equal {env env' : Env Variable Literal Symbol} {left right value : Term Variable Literal Symbol} :
      Extends env env' → inst env' left = some value → inst env' right = some value → Binds answers env (.equal left right) env'
  | exists {env env' : Env Variable Literal Symbol} {name : Variable} {body : Term Variable Literal Symbol} :
      Binds answers (env.set name none) body env' → Binds answers env (.existsVar name body) (env'.set name (env name))
  | forall {env env' : Env Variable Literal Symbol} {name : Variable} {body value : Term Variable Literal Symbol} :
      Binds answers (env.set name (some value)) body env' → Binds answers env (.forallVar name body) (env'.set name (env name))
  | imp {env env' : Env Variable Literal Symbol} {antecedent conclusion : Term Variable Literal Symbol} :
      Binds answers env conclusion env' → Binds answers env (.imp antecedent conclusion) env'

/-- A call an evaluation of a goal makes: a predicate and its input values. -/
inductive CallIn (answers : Symbol → List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) → Prop) :
    Env Variable Literal Symbol → Term Variable Literal Symbol → Symbol × List (Term Variable Literal Symbol) → Prop
  | call {env : Env Variable Literal Symbol} {goal : Term Variable Literal Symbol} {predicate : Symbol}
      {args inputs outputs values : List (Term Variable Literal Symbol)} :
      program.callOf? goal = some (predicate, args) → program.io? predicate args = some (inputs, outputs) →
      instAll env inputs = some values → CallIn answers env goal (predicate, values)
  | conjLeft {env : Env Variable Literal Symbol} {left right : Term Variable Literal Symbol} {call} :
      CallIn answers env left call → CallIn answers env (.conj left right) call
  | conjRight {env middle : Env Variable Literal Symbol} {left right : Term Variable Literal Symbol} {call} :
      program.Binds answers env left middle → CallIn answers middle right call → CallIn answers env (.conj left right) call
  | disjLeft {env : Env Variable Literal Symbol} {left right : Term Variable Literal Symbol} {call} :
      CallIn answers env left call → CallIn answers env (.disj left right) call
  | disjRight {env : Env Variable Literal Symbol} {left right : Term Variable Literal Symbol} {call} :
      CallIn answers env right call → CallIn answers env (.disj left right) call
  | negation {env : Env Variable Literal Symbol} {operand : Term Variable Literal Symbol} {call} :
      CallIn answers env operand call → CallIn answers env (.defaultNeg operand) call
  | exists {env : Env Variable Literal Symbol} {name : Variable} {body : Term Variable Literal Symbol} {call} :
      CallIn answers (env.set name none) body call → CallIn answers env (.existsVar name body) call
  | forall {env : Env Variable Literal Symbol} {name : Variable} {body value : Term Variable Literal Symbol} {call} :
      CallIn answers (env.set name (some value)) body call → CallIn answers env (.forallVar name body) call
  | imp {env : Env Variable Literal Symbol} {antecedent conclusion : Term Variable Literal Symbol} {call} :
      CallIn answers env conclusion call → CallIn answers env (.imp antecedent conclusion) call

/-- Evaluating a clause body goal by goal. -/
inductive BindsBody (answers : Symbol → List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) → Prop) :
    Env Variable Literal Symbol → List (Term Variable Literal Symbol) → Env Variable Literal Symbol → Prop
  | nil {env : Env Variable Literal Symbol} : BindsBody answers env [] env
  | cons {env middle env' : Env Variable Literal Symbol} {goal : Term Variable Literal Symbol}
      {rest : List (Term Variable Literal Symbol)} :
      program.Binds answers env goal middle → BindsBody answers middle rest env' → BindsBody answers env (goal :: rest) env'

/-- A call an evaluation of a clause body makes. -/
inductive CallInBody (answers : Symbol → List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) → Prop) :
    Env Variable Literal Symbol → List (Term Variable Literal Symbol) → Symbol × List (Term Variable Literal Symbol) → Prop
  | here {env : Env Variable Literal Symbol} {goal : Term Variable Literal Symbol} {rest : List (Term Variable Literal Symbol)} {call} :
      program.CallIn answers env goal call → CallInBody answers env (goal :: rest) call
  | later {env middle : Env Variable Literal Symbol} {goal : Term Variable Literal Symbol}
      {rest : List (Term Variable Literal Symbol)} {call} :
      program.Binds answers env goal middle → CallInBody answers middle rest call → CallInBody answers env (goal :: rest) call

end Program

/-- An answer relation is bounded for `info` when every predicate `info`
marks answers data terms of its call. -/
def AnswersBounded (info : Symbol → Bool)
    (answers : Symbol → List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) → Prop)
    (ground : List (Term Variable Literal Symbol)) : Prop :=
  ∀ predicate values results, info predicate = true → answers predicate values results →
    ∀ result ∈ results, InData ground values result

namespace Program

variable (program : Program Variable Literal Symbol)

/-! ## The analysis is sound -/

theorem select_sub {α : Type} (mode : Mode) : ∀ (modes : List Mode) (args : List α), ∀ arg ∈ select mode modes args, arg ∈ args
  | [], _, _, member => by simp [select] at member
  | _ :: _, [], _, member => by simp [select] at member
  | first :: modes, arg :: args, other, member => by
      simp only [select] at member
      split at member
      · rcases List.mem_cons.mp member with rfl | inside
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (select_sub mode modes args other inside)
      · exact List.mem_cons_of_mem _ (select_sub mode modes args other member)

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem io?_sub {predicate : Symbol} {args inputs outputs : List (Term Variable Literal Symbol)}
    (io : program.io? predicate args = some (inputs, outputs)) :
    (∀ term ∈ inputs, term ∈ args) ∧ ∀ term ∈ outputs, term ∈ args := by
  unfold io? at io
  split at io
  · split at io
    · cases io
      exact ⟨select_sub _ _ _, select_sub _ _ _⟩
    · cases io
  · cases io

omit [DecidableEq Variable] [DecidableEq Literal] in
/-- A predicate call is an application, and its arguments are the goal's, or
all but the predicate of a concrete `ho_apply`. -/
theorem callOf?_app {goal : Term Variable Literal Symbol} {predicate : Symbol} {args : List (Term Variable Literal Symbol)}
    (found : program.callOf? goal = some (predicate, args)) :
    ∃ symbol goalArgs, goal = .app symbol goalArgs ∧ ∀ term ∈ args, term ∈ goalArgs := by
  cases goal with
  | app symbol goalArgs =>
      refine ⟨symbol, goalArgs, rfl, ?_⟩
      simp only [callOf?] at found
      split at found
      · split at found
        · split at found
          · cases found
          · cases found; exact fun term member => List.mem_cons_of_mem _ member
        · cases found
      · split at found
        · cases found
        · cases found; exact fun _ member => member
  | _ => simp [callOf?] at found

omit [DecidableEq Variable] [DecidableEq Literal] in
/-- The ground terms of a call's arguments are the goal's. -/
theorem callOf?_grounds {goal : Term Variable Literal Symbol} {predicate : Symbol}
    {args : List (Term Variable Literal Symbol)} (found : program.callOf? goal = some (predicate, args)) :
    ∀ term ∈ args, ∀ part ∈ grounds term, part ∈ grounds goal := by
  obtain ⟨symbol, goalArgs, rfl, sub⟩ := program.callOf?_app found
  intro term member part inside
  simp only [grounds, List.mem_append]
  exact .inr (groundsAll_sub (sub term member) part inside)

end Program

/-- What the analysis assumes of the values at a point of a clause body:
`base` gives the frame's head inputs the values `inputs`, the head terms keep
those values where no binder rebinds them, and every name in `small` holds a
data term of the call. -/
structure Holds (ground inputs : List (Term Variable Literal Symbol)) (frame : Frame Variable Literal Symbol)
    (base env : Env Variable Literal Symbol) (small : List Variable) : Prop where
  heads : instAll base frame.heads = some inputs
  agree : ∀ name ∈ frame.heads.flatMap Term.freeVars, name ∉ frame.shadow → env name = base name
  small : ∀ name ∈ small, ∃ value, env name = some value ∧ InData ground inputs value

section Holds

variable {ground inputs : List (Term Variable Literal Symbol)} {frame : Frame Variable Literal Symbol}
  {base env : Env Variable Literal Symbol} {small : List Variable}

omit [DecidableEq Literal] [DecidableEq Symbol] in
/-- The start of a clause: the head's inputs, nothing else known. -/
theorem Holds.start {heads : List (Term Variable Literal Symbol)} (found : instAll base heads = some inputs) :
    Holds ground inputs ⟨heads, []⟩ base base [] :=
  ⟨found, fun _ _ _ => rfl, fun _ member => by cases member⟩

omit [DecidableEq Literal] [DecidableEq Symbol] in
theorem Holds.extend (holds : Holds ground inputs frame base env small) {env' : Env Variable Literal Symbol}
    (more : Extends env env') : Holds ground inputs frame base env' small := by
  refine ⟨holds.heads, fun name member free => ?_, fun name member => ?_⟩
  · obtain ⟨part, bound, _⟩ := instAll_name holds.heads name member
    have same := holds.agree name member free
    rw [more name part (by rw [same]; exact bound), bound]
  · obtain ⟨value, bound, inData⟩ := holds.small name member
    exact ⟨value, more name value bound, inData⟩

/-- A term the analysis accepts holds a data term of the call. -/
theorem Holds.value (holds : Holds ground inputs frame base env small) {term : Term Variable Literal Symbol}
    (accepted : frame.small small term = true) (grounded : closedData term = true → term ∈ ground) :
    ∃ value, inst env term = some value ∧ InData ground inputs value := by
  unfold Frame.small at accepted
  simp only [Bool.or_eq_true] at accepted
  rcases accepted with (headTerm | closed) | named
  · unfold Frame.headTerm at headTerm
    simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.contains_eq_mem, decide_eq_false_iff_not] at headTerm
    obtain ⟨⟨head, headMember, found⟩, unshadowed⟩ := headTerm
    obtain ⟨input, inputMember, headInst⟩ := instAll_values holds.heads head headMember
    obtain ⟨value, partInst, sub⟩ := occurs_inst found headInst
    refine ⟨value, ?_, .inl ⟨input, inputMember, sub⟩⟩
    rw [inst_congr term fun name member => holds.agree name
      (List.mem_flatMap.mpr ⟨head, headMember, occurs_freeVars found name member⟩) (unshadowed name member)]
    exact partInst
  · exact ⟨term, inst_closed closed, .inr ⟨term, grounded closed, .refl _⟩⟩
  · cases term with
    | var name =>
        simp only [List.contains_eq_mem, decide_eq_true_eq] at named
        exact holds.small name named
    | _ => simp at named

/-- Inputs the analysis accepts give data-term values. -/
theorem Holds.values (holds : Holds ground inputs frame base env small) {terms values : List (Term Variable Literal Symbol)}
    (accepted : terms.all (frame.small small) = true) (grounded : ∀ term ∈ terms, closedData term = true → term ∈ ground)
    (found : instAll env terms = some values) : ∀ value ∈ values, InData ground inputs value := by
  intro value member
  obtain ⟨term, termMember, termInst⟩ := instAll_mem found value member
  obtain ⟨other, otherInst, inData⟩ := holds.value (List.all_eq_true.mp accepted term termMember) (grounded term termMember)
  rw [termInst] at otherInst
  cases otherInst
  exact inData

omit [DecidableEq Literal] [DecidableEq Symbol] in
/-- Under a binder: the name is rebound, the rest is kept. -/
theorem Holds.enter (holds : Holds ground inputs frame base env small) (name : Variable)
    (value : Option (Term Variable Literal Symbol)) :
    Holds ground inputs (frame.enter name) base (env.set name value) (small.filter (· != name)) := by
  refine ⟨holds.heads, fun other member free => ?_, fun other member => ?_⟩
  · have different : other ≠ name := fun same => free (by simp [Frame.enter, same])
    rw [Env.set_other _ _ different]
    exact holds.agree other member fun inside => free (by simp [Frame.enter, inside])
  · simp only [List.mem_filter, bne_iff_ne, ne_eq] at member
    rw [Env.set_other _ _ member.2]
    exact holds.small other member.1

omit [DecidableEq Literal] [DecidableEq Symbol] in
/-- Leaving a binder: the name gets its value from outside it back. -/
theorem Holds.leave (outer : Holds ground inputs frame base env small) {name : Variable} {env' : Env Variable Literal Symbol}
    {inner : List Variable} (holds : Holds ground inputs (frame.enter name) base env' inner) :
    Holds ground inputs frame base (env'.set name (env name))
      (inner.filter (· != name) ++ (if small.contains name then [name] else [])) := by
  refine ⟨outer.heads, fun other member free => ?_, fun other member => ?_⟩
  · by_cases same : other = name
    · subst same; rw [Env.set_same]; exact outer.agree other member free
    · rw [Env.set_other _ _ same]
      exact holds.agree other member fun inside => by
        simp only [Frame.enter, List.mem_cons] at inside
        rcases inside with here | there
        · exact same here
        · exact free there
  · rcases List.mem_append.mp member with kept | back
    · simp only [List.mem_filter, bne_iff_ne, ne_eq] at kept
      rw [Env.set_other _ _ kept.2]
      exact holds.small other kept.1
    · split at back
      · rename_i present
        simp only [List.mem_singleton] at back
        subst back
        rw [Env.set_same]
        exact outer.small other (by simpa using present)
      · cases back

end Holds

namespace Program

variable (program : Program Variable Literal Symbol)

theorem flow_app (info : Symbol → Bool) (frame : Frame Variable Literal Symbol) (small : List Variable) (symbol : Symbol)
    (args : List (Term Variable Literal Symbol)) :
    program.flow info frame small (.app symbol args) =
      match program.callOf? (.app symbol args) with
      | some (predicate, args) =>
          match program.io? predicate args with
          | some (inputs, outputs) =>
              if info predicate && inputs.all (frame.small small) then small ++ outputs.flatMap Term.freeVars
              else small
          | none => small
      | none => small := rfl

/-- Every name `flow` marks holds a data term of the call, after any
evaluation of the goal against bounded answers. -/
theorem flow_sound {info : Symbol → Bool}
    {answers : Symbol → List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) → Prop}
    {ground inputs : List (Term Variable Literal Symbol)} (bounded : AnswersBounded info answers ground)
    {env : Env Variable Literal Symbol} {goal : Term Variable Literal Symbol} {env' : Env Variable Literal Symbol}
    (run : program.Binds answers env goal env') :
    ∀ {frame : Frame Variable Literal Symbol} {base : Env Variable Literal Symbol} {small : List Variable},
      (∀ term ∈ grounds goal, term ∈ ground) → Holds ground inputs frame base env small →
        Holds ground inputs frame base env' (program.flow info frame small goal) := by
  induction run with
  | @call env env' goal predicate args callInputs outputs values results callEq ioEq valuesEq answered more resultsEq =>
      intro frame base small grounded holds
      obtain ⟨symbol, goalArgs, rfl, _⟩ := program.callOf?_app callEq
      rw [flow_app, callEq]
      simp only [ioEq]
      have extended := holds.extend more
      split
      · rename_i accepted
        simp only [Bool.and_eq_true] at accepted
        have inputsData := holds.values accepted.2 (fun term member closed => grounded term
          (program.callOf?_grounds callEq term ((program.io?_sub ioEq).1 term member) term (mem_grounds_self closed)))
          valuesEq
        refine ⟨holds.heads, extended.agree, fun name member => ?_⟩
        rcases List.mem_append.mp member with old | new
        · exact extended.small name old
        · obtain ⟨part, bound, result, resultMember, sub⟩ := instAll_name resultsEq name new
          exact ⟨part, bound, ((bounded predicate values results accepted.1 answered result resultMember).trans
            inputsData).sub sub⟩
      · exact extended
  | check _ =>
      intro frame base small _ holds
      rw [flow_app]
      split
      · rename_i found; simp_all
      · exact holds
  | truth => intro _ _ _ _ holds; exact holds
  | negation => intro _ _ _ _ holds; exact holds
  | conj _ _ left right =>
      intro frame base small grounded holds
      simp only [grounds, List.mem_append] at grounded
      exact right (fun term member => grounded term (.inr member)) (left (fun term member => grounded term (.inl member)) holds)
  | disjLeft _ inner =>
      intro frame base small grounded holds
      simp only [grounds, List.mem_append] at grounded
      have result := inner (fun term member => grounded term (.inl member)) holds
      simp only [flow]
      exact ⟨result.heads, result.agree, fun name member => result.small name (List.mem_filter.mp member).1⟩
  | disjRight _ inner =>
      intro frame base small grounded holds
      simp only [grounds, List.mem_append] at grounded
      have result := inner (fun term member => grounded term (.inr member)) holds
      simp only [flow]
      exact ⟨result.heads, result.agree, fun name member => result.small name (by
        simpa [List.contains_eq_mem] using (List.mem_filter.mp member).2)⟩
  | @equal env env' left right value more leftInst rightInst =>
      intro frame base small grounded holds
      simp only [grounds, List.mem_append] at grounded
      have extended := holds.extend more
      simp only [flow]
      refine ⟨holds.heads, extended.agree, fun name member => ?_⟩
      simp only [List.mem_append] at member
      rcases member with (old | fromLeft) | fromRight
      · exact extended.small name old
      · split at fromLeft
        · rename_i accepted
          obtain ⟨found, foundInst, inData⟩ := holds.value accepted fun closed =>
            grounded _ (.inl (mem_grounds_self closed))
          rw [inst_extends more foundInst] at leftInst
          cases leftInst
          obtain ⟨part, bound, sub⟩ := inst_name rightInst name fromLeft
          exact ⟨part, bound, inData.sub sub⟩
        · cases fromLeft
      · split at fromRight
        · rename_i accepted
          obtain ⟨found, foundInst, inData⟩ := holds.value accepted fun closed =>
            grounded _ (.inr (mem_grounds_self closed))
          rw [inst_extends more foundInst] at rightInst
          cases rightInst
          obtain ⟨part, bound, sub⟩ := inst_name leftInst name fromRight
          exact ⟨part, bound, inData.sub sub⟩
        · cases fromRight
  | «exists» _ inner =>
      intro frame base small grounded holds
      simp only [grounds] at grounded
      simp only [flow]
      exact holds.leave (inner grounded (holds.enter _ none))
  | «forall» _ inner =>
      intro frame base small grounded holds
      simp only [grounds] at grounded
      simp only [flow]
      exact holds.leave (inner grounded (holds.enter _ _))
  | imp _ inner =>
      intro frame base small grounded holds
      simp only [grounds, List.mem_append] at grounded
      simp only [flow]
      exact inner (fun term member => grounded term (.inr member)) holds

theorem flowBody_sound {info : Symbol → Bool}
    {answers : Symbol → List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) → Prop}
    {ground inputs : List (Term Variable Literal Symbol)} (bounded : AnswersBounded info answers ground)
    {env : Env Variable Literal Symbol} {body : List (Term Variable Literal Symbol)} {env' : Env Variable Literal Symbol}
    (run : program.BindsBody answers env body env') :
    ∀ {frame : Frame Variable Literal Symbol} {base : Env Variable Literal Symbol} {small : List Variable},
      (∀ term ∈ body.flatMap grounds, term ∈ ground) → Holds ground inputs frame base env small →
        Holds ground inputs frame base env' (program.flowBody info frame small body) := by
  induction run with
  | nil => intro _ _ _ _ holds; exact holds
  | cons first _ ih =>
      intro frame base small grounded holds
      simp only [List.flatMap_cons, List.mem_append] at grounded
      exact ih (fun term member => grounded term (.inr member))
        (program.flow_sound bounded first (fun term member => grounded term (.inl member)) holds)

end Program

/-- Decreasing inputs have smaller values: each is a subterm of the head input
at its position, one strictly, so the sum of the sizeAll drops. -/
theorem zip_sizes {base env : Env Variable Literal Symbol} {shadow : List Variable} :
    ∀ {terms heads values inputs : List (Term Variable Literal Symbol)},
      (∀ name ∈ heads.flatMap Term.freeVars, name ∉ shadow → env name = base name) →
      terms.length ≤ heads.length →
      ((terms.zip heads).all fun pair => occurs pair.1 pair.2 && pair.1.freeVars.all fun name => !shadow.contains name) = true →
      instAll env terms = some values → instAll base heads = some inputs →
        sizeAll values ≤ sizeAll inputs ∧ (((terms.zip heads).any fun pair => inside pair.1 pair.2) = true → sizeAll values < sizeAll inputs)
  | [], heads, values, inputs, _, _, _, found, _ => by
      simp only [instAll] at found; cases found
      exact ⟨by simp [sizeAll], by simp⟩
  | _ :: _, [], _, _, _, short, _, _, _ => by simp at short
  | term :: terms, head :: heads, values, inputs, agree, short, pairs, found, headsFound => by
      simp only [instAll] at found headsFound
      cases termInst : inst env term with
      | none => rw [termInst] at found; cases found
      | some value =>
          cases restInst : instAll env terms with
          | none => rw [termInst, restInst] at found; cases found
          | some rest =>
              rw [termInst, restInst] at found
              cases found
              cases headInst : inst base head with
              | none => rw [headInst] at headsFound; cases headsFound
              | some input =>
                  cases headsRest : instAll base heads with
                  | none => rw [headInst, headsRest] at headsFound; cases headsFound
                  | some more =>
                      rw [headInst, headsRest] at headsFound
                      cases headsFound
                      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, List.all_eq_true,
                        Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_mem, decide_eq_false_iff_not] at pairs
                      obtain ⟨⟨found, unshadowed⟩, restPairs⟩ := pairs
                      have same : inst env term = inst base term := inst_congr term fun name member =>
                        agree name (List.mem_append_left _ (occurs_freeVars found name member)) (unshadowed name member)
                      obtain ⟨partValue, partInst, sub⟩ := occurs_inst found headInst
                      rw [same, partInst] at termInst
                      cases termInst
                      have restAgree : ∀ name ∈ heads.flatMap Term.freeVars, name ∉ shadow → env name = base name :=
                        fun name member free => agree name (List.mem_append_right _ member) free
                      obtain ⟨le, lt⟩ := zip_sizes restAgree (by simpa using short)
                        (List.all_eq_true.mpr fun pair member => by
                          have := restPairs pair member
                          simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
                            List.contains_eq_mem, decide_eq_false_iff_not]
                          exact this)
                        restInst headsRest
                      have headLe := sub.size_le
                      simp only [sizeAll] at le lt ⊢
                      refine ⟨by omega, fun strict => ?_⟩
                      simp only [List.zip_cons_cons, List.any_cons, Bool.or_eq_true] at strict
                      rcases strict with here | there
                      · obtain ⟨other, otherInst, smaller⟩ := inside_inst here headInst
                        rw [partInst] at otherInst
                        cases otherInst
                        omega
                      · have := lt there
                        omega

theorem Holds.decreasing {ground inputs : List (Term Variable Literal Symbol)} {frame : Frame Variable Literal Symbol}
    {base env : Env Variable Literal Symbol} {small : List Variable} (holds : Holds ground inputs frame base env small)
    {terms values : List (Term Variable Literal Symbol)} (decreasing : frame.decreasing terms = true)
    (found : instAll env terms = some values) : sizeAll values < sizeAll inputs := by
  unfold Frame.decreasing at decreasing
  simp only [Bool.and_eq_true, decide_eq_true_eq] at decreasing
  obtain ⟨⟨short, pairs⟩, strict⟩ := decreasing
  exact (zip_sizes holds.agree short pairs found holds.heads).2 strict

namespace Program

variable (program : Program Variable Literal Symbol)

/-- A call an evaluation makes is at a call site of the goal; if the site's
inputs are data terms, so are the call's values, and if they decrease, so do
the call's values. -/
theorem site_of_call {info : Symbol → Bool}
    {answers : Symbol → List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) → Prop}
    {ground inputs : List (Term Variable Literal Symbol)} (bounded : AnswersBounded info answers ground)
    {env : Env Variable Literal Symbol} {goal : Term Variable Literal Symbol}
    {call : Symbol × List (Term Variable Literal Symbol)} (made : program.CallIn answers env goal call) :
    ∀ {frame : Frame Variable Literal Symbol} {base : Env Variable Literal Symbol} {small : List Variable}
      {path : List Nat}, (∀ term ∈ grounds goal, term ∈ ground) → Holds ground inputs frame base env small →
        ∃ site ∈ program.sites info frame small path goal, site.callee = call.1 ∧
          (site.small = true → ∀ value ∈ call.2, InData ground inputs value) ∧
          (site.decreasing = true → sizeAll call.2 < sizeAll inputs) := by
  induction made with
  | @call env goal predicate args callInputs outputs values callEq ioEq valuesEq =>
      intro frame base small path grounded holds
      obtain ⟨symbol, goalArgs, rfl, _⟩ := program.callOf?_app callEq
      refine ⟨⟨path, predicate, .app symbol goalArgs, callInputs.all (frame.small small), frame.decreasing callInputs⟩,
        ?_, rfl, fun accepted => ?_, fun decreasing => holds.decreasing decreasing valuesEq⟩
      · simp only [sites, callEq, ioEq, List.mem_singleton]
      · exact holds.values accepted (fun term member closed => grounded term
          (program.callOf?_grounds callEq term ((program.io?_sub ioEq).1 term member) term (mem_grounds_self closed)))
          valuesEq
  | conjLeft _ ih =>
      intro frame base small path grounded holds
      simp only [grounds, List.mem_append] at grounded
      obtain ⟨site, member, facts⟩ := ih (path := path ++ [0]) (fun term member => grounded term (.inl member)) holds
      exact ⟨site, by simp only [sites, List.mem_append]; exact .inl member, facts⟩
  | conjRight first _ ih =>
      intro frame base small path grounded holds
      simp only [grounds, List.mem_append] at grounded
      obtain ⟨site, member, facts⟩ := ih (path := path ++ [1]) (fun term member => grounded term (.inr member))
        (program.flow_sound bounded first (fun term member => grounded term (.inl member)) holds)
      exact ⟨site, by simp only [sites, List.mem_append]; exact .inr member, facts⟩
  | disjLeft _ ih =>
      intro frame base small path grounded holds
      simp only [grounds, List.mem_append] at grounded
      obtain ⟨site, member, facts⟩ := ih (path := path ++ [0]) (fun term member => grounded term (.inl member)) holds
      exact ⟨site, by simp only [sites, List.mem_append]; exact .inl member, facts⟩
  | disjRight _ ih =>
      intro frame base small path grounded holds
      simp only [grounds, List.mem_append] at grounded
      obtain ⟨site, member, facts⟩ := ih (path := path ++ [1]) (fun term member => grounded term (.inr member)) holds
      exact ⟨site, by simp only [sites, List.mem_append]; exact .inr member, facts⟩
  | negation _ ih =>
      intro frame base small path grounded holds
      simp only [grounds] at grounded
      obtain ⟨site, member, facts⟩ := ih (path := path ++ [0]) grounded holds
      exact ⟨site, by simpa only [sites] using member, facts⟩
  | «exists» _ ih =>
      intro frame base small path grounded holds
      simp only [grounds] at grounded
      obtain ⟨site, member, facts⟩ := ih (path := path ++ [0]) grounded (holds.enter _ none)
      exact ⟨site, by simpa only [sites] using member, facts⟩
  | «forall» _ ih =>
      intro frame base small path grounded holds
      simp only [grounds] at grounded
      obtain ⟨site, member, facts⟩ := ih (path := path ++ [0]) grounded (holds.enter _ _)
      exact ⟨site, by simpa only [sites] using member, facts⟩
  | imp _ ih =>
      intro frame base small path grounded holds
      simp only [grounds, List.mem_append] at grounded
      obtain ⟨site, member, facts⟩ := ih (path := path ++ [1]) (fun term member => grounded term (.inr member)) holds
      exact ⟨site, by simpa only [sites] using member, facts⟩

theorem site_of_callBody {info : Symbol → Bool}
    {answers : Symbol → List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) → Prop}
    {ground inputs : List (Term Variable Literal Symbol)} (bounded : AnswersBounded info answers ground)
    {env : Env Variable Literal Symbol} {body : List (Term Variable Literal Symbol)}
    {call : Symbol × List (Term Variable Literal Symbol)} (made : program.CallInBody answers env body call) :
    ∀ {frame : Frame Variable Literal Symbol} {base : Env Variable Literal Symbol} {small : List Variable} {index position : Nat},
      (∀ term ∈ body.flatMap grounds, term ∈ ground) → Holds ground inputs frame base env small →
        ∃ pair ∈ program.sitesBody info frame index position small body, pair.2.callee = call.1 ∧
          (pair.2.small = true → ∀ value ∈ call.2, InData ground inputs value) ∧
          (pair.2.decreasing = true → sizeAll call.2 < sizeAll inputs) := by
  induction made with
  | here first =>
      intro frame base small index position grounded holds
      simp only [List.flatMap_cons, List.mem_append] at grounded
      obtain ⟨site, member, facts⟩ := program.site_of_call bounded first (path := [])
        (fun term member => grounded term (.inl member)) holds
      exact ⟨(.body index position, site), by
        simp only [sitesBody, List.mem_append, List.mem_map]; exact .inl ⟨site, member, rfl⟩, facts⟩
  | later first _ ih =>
      intro frame base small index position grounded holds
      simp only [List.flatMap_cons, List.mem_append] at grounded
      obtain ⟨pair, member, facts⟩ := ih (index := index) (position := position + 1)
        (fun term member => grounded term (.inr member))
        (program.flow_sound bounded first (fun term member => grounded term (.inl member)) holds)
      exact ⟨pair, by simp only [sitesBody, List.mem_append]; exact .inr member, facts⟩

/-! ## Finitely many calls -/

omit [DecidableEq Variable] [DecidableEq Literal] in
theorem headOf?_app {head : Term Variable Literal Symbol} {predicate : Symbol} {args : List (Term Variable Literal Symbol)}
    (found : program.headOf? head = some (predicate, args)) : head = .app predicate args := by
  cases head with
  | app symbol headArgs =>
      simp only [headOf?] at found
      split at found
      · cases found
      · cases found; rfl
  | _ => simp [headOf?] at found

omit [DecidableEq Variable] [DecidableEq Literal] in
/-- A defining clause's ground terms are the program's. -/
theorem definition_grounds {predicate : Symbol} {index : Nat} {args body : List (Term Variable Literal Symbol)}
    (member : (index, args, body) ∈ program.definitions predicate) :
    (∀ term ∈ body.flatMap grounds, term ∈ program.constants) ∧
      ∀ arg ∈ args, ∀ term ∈ grounds arg, term ∈ program.constants := by
  obtain ⟨head, clause, headEq⟩ := program.mem_definitions.mp member
  have headIs := program.headOf?_app headEq
  subst headIs
  have inClause : ∀ term, term ∈ grounds (.app predicate args) ++ body.flatMap grounds → term ∈ program.constants :=
    fun term inside => List.mem_flatMap.mpr ⟨(index, .definite (.app predicate args) body), clause, inside⟩
  refine ⟨fun term inside => inClause term (List.mem_append_right _ inside), fun arg argMember term inside => ?_⟩
  apply inClause
  simp only [grounds, List.mem_append]
  exact .inl (.inr (groundsAll_sub argMember term inside))

/-- The ground terms of a query: the program's, its context's, and its
goal's. A query's context facts answer them, so the call bound for a query
takes them as its ground terms. -/
def queryConstants (query : Query Variable Literal Symbol) : List (Term Variable Literal Symbol) :=
  program.constants ++ query.context.flatMap grounds ++ grounds query.goal

omit [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] in
theorem constants_query (query : Query Variable Literal Symbol) :
    ∀ term ∈ program.constants, term ∈ program.queryConstants query :=
  fun _ member => List.mem_append_left _ (List.mem_append_left _ member)

/-- A call a defining clause of the caller's predicate makes, evaluated on the
caller's input values. -/
def Makes (answers : Symbol → List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) → Prop)
    (caller callee : Symbol × List (Term Variable Literal Symbol)) : Prop :=
  ∃ index args body inputs outputs, ∃ env : Env Variable Literal Symbol,
    (index, args, body) ∈ program.definitions caller.1 ∧ program.io? caller.1 args = some (inputs, outputs) ∧
      instAll env inputs = some caller.2 ∧ program.CallInBody answers env body callee

end Program

/-- Chains of steps: the reflexive-transitive closure. -/
inductive Chain {α : Type} (step : α → α → Prop) : α → α → Prop
  | refl (first : α) : Chain step first first
  | tail {first middle last : α} : Chain step first middle → step middle last → Chain step first last

namespace Program

variable (program : Program Variable Literal Symbol)

/-- The recursive call site behind a call a component member makes to a
component member: with its smallness and decrease. -/
theorem recursive_site {answers : Symbol → List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) → Prop}
    {ground : List (Term Variable Literal Symbol)}
    (covers : ∀ term ∈ program.constants, term ∈ ground) (bounded : AnswersBounded program.dataInfo answers ground) {predicate : Symbol}
    {caller callee : Symbol × List (Term Variable Literal Symbol)} (callerMember : caller.1 ∈ program.component predicate)
    (makes : program.Makes answers caller callee) (calleeMember : callee.1 ∈ program.component predicate) :
    ∃ pair ∈ program.recursiveSites caller.1,
      (pair.2.small = true → ∀ value ∈ callee.2, InData ground caller.2 value) ∧
      (pair.2.decreasing = true → sizeAll callee.2 < sizeAll caller.2) := by
  obtain ⟨index, args, body, inputs, outputs, env, definition, ioEq, start, made⟩ := makes
  obtain ⟨pair, member, callee', small, decreasing⟩ := program.site_of_callBody bounded made (index := index) (position := 0)
    (fun term member => covers term ((program.definition_grounds definition).1 term member)) (Holds.start (ground := ground) start)
  have frameEq : program.frameOf caller.1 args = some ⟨inputs, []⟩ := by simp [frameOf, ioEq]
  have inSites : pair ∈ program.callSites caller.1 := by
    simp only [callSites, List.mem_flatMap]
    exact ⟨(index, args, body), definition, by rw [frameEq]; exact member⟩
  have edge := program.edge_of_definition definition (callee' ▸ program.sitesBody_callee member)
  refine ⟨pair, List.mem_filter.mpr ⟨inSites, ?_⟩, small, decreasing⟩
  rw [callee']
  exact program.recursive_of_component callerMember calleeMember edge

/-- **Finitely many calls.** From a ground input, every call a complete
predicate's component makes, transitively, is of a component member, with
inputs among the data terms of the first call's inputs: at most
`|component| · |dataTerms|ᵃ` distinct calls of arity `a`. -/
theorem calls_bounded {answers : Symbol → List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) → Prop}
    {ground : List (Term Variable Literal Symbol)}
    (covers : ∀ term ∈ program.constants, term ∈ ground) (bounded : AnswersBounded program.dataInfo answers ground) {predicate : Symbol}
    (complete : program.complete predicate = true) {inputs : List (Term Variable Literal Symbol)}
    {call : Symbol × List (Term Variable Literal Symbol)}
    (chain : Chain (fun caller callee => program.Makes answers caller callee ∧ callee.1 ∈ program.component predicate)
      (predicate, inputs) call) :
    call.1 ∈ program.component predicate ∧ ∀ value ∈ call.2, InData ground inputs value := by
  induction chain with
  | refl => exact ⟨List.mem_cons_self, fun value member => .inl ⟨value, member, .refl _⟩⟩
  | @tail caller callee _ step ih =>
      obtain ⟨callerMember, callerData⟩ := ih
      obtain ⟨makes, calleeMember⟩ := step
      obtain ⟨pair, recursiveMember, small, _⟩ := program.recursive_site covers bounded callerMember makes calleeMember
      have own : program.localComplete caller.1 = true :=
        List.all_eq_true.mp complete caller.1 (program.component_closure callerMember)
      simp only [localComplete, Bool.and_eq_true, List.all_eq_true] at own
      refine ⟨calleeMember, fun value member => ?_⟩
      exact (small (own.1.1 pair recursiveMember) value member).trans callerData

/-- The calls' inputs are in the explicit finite list of data terms. -/
theorem calls_dataTerms {answers : Symbol → List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) → Prop}
    {ground : List (Term Variable Literal Symbol)}
    (covers : ∀ term ∈ program.constants, term ∈ ground) (bounded : AnswersBounded program.dataInfo answers ground) {predicate : Symbol}
    (complete : program.complete predicate = true) {inputs : List (Term Variable Literal Symbol)}
    {call : Symbol × List (Term Variable Literal Symbol)}
    (chain : Chain (fun caller callee => program.Makes answers caller callee ∧ callee.1 ∈ program.component predicate)
      (predicate, inputs) call) :
    call.1 ∈ program.component predicate ∧ ∀ value ∈ call.2, value ∈ dataTerms ground inputs :=
  let bound := program.calls_bounded covers bounded complete chain
  ⟨bound.1, fun value member => (bound.2 value member).mem⟩

/-- **Bounded answers.** A defining clause of a predicate with data-term
outputs, evaluated against bounded answers, answers data terms of its call:
every derivable answer is bounded, by induction on derivations. -/
theorem outputs_bounded {answers : Symbol → List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) → Prop}
    {ground : List (Term Variable Literal Symbol)}
    (covers : ∀ term ∈ program.constants, term ∈ ground) (bounded : AnswersBounded program.dataInfo answers ground) {predicate : Symbol}
    (member : predicate ∈ program.dataOutputs) {index : Nat} {args body inputs outputs : List (Term Variable Literal Symbol)}
    (definition : (index, args, body) ∈ program.definitions predicate)
    (ioEq : program.io? predicate args = some (inputs, outputs)) {env env' : Env Variable Literal Symbol}
    {values results : List (Term Variable Literal Symbol)} (start : instAll env inputs = some values)
    (run : program.BindsBody answers env body env') (resultsEq : instAll env' outputs = some results) :
    ∀ result ∈ results, InData ground values result := by
  have ok := greatest_post _ member
  simp only [outputsOk, List.all_eq_true] at ok
  have clause := ok (index, args, body) definition
  simp only [clauseOutputs, ioEq, List.all_eq_true] at clause
  have holds := program.flowBody_sound bounded run
    (fun term member => covers term ((program.definition_grounds definition).1 term member)) (Holds.start (ground := ground) start)
  intro result resultMember
  obtain ⟨output, outputMember, outputInst⟩ := instAll_mem resultsEq result resultMember
  obtain ⟨value, valueInst, inData⟩ := holds.value (clause output outputMember) fun closed =>
    covers _ ((program.definition_grounds definition).2 output ((program.io?_sub ioEq).2 output outputMember) output
      (mem_grounds_self closed))
  rw [outputInst] at valueInst
  cases valueInst
  exact inData

/-- **Decreasing calls.** In a component whose recursive calls all decrease,
every call a member makes to a member has inputs of smaller total size: no
call repeats. -/
theorem calls_decrease {answers : Symbol → List (Term Variable Literal Symbol) → List (Term Variable Literal Symbol) → Prop}
    {ground : List (Term Variable Literal Symbol)}
    (covers : ∀ term ∈ program.constants, term ∈ ground) (bounded : AnswersBounded program.dataInfo answers ground) {predicate : Symbol}
    (decreasing : (program.component predicate).all (fun member => (program.recursiveSites member).all (·.2.decreasing)) = true)
    {caller callee : Symbol × List (Term Variable Literal Symbol)} (callerMember : caller.1 ∈ program.component predicate)
    (makes : program.Makes answers caller callee) (calleeMember : callee.1 ∈ program.component predicate) :
    sizeAll callee.2 < sizeAll caller.2 := by
  obtain ⟨pair, recursiveMember, _, smaller⟩ := program.recursive_site covers bounded callerMember makes calleeMember
  exact smaller (List.all_eq_true.mp (List.all_eq_true.mp decreasing caller.1 callerMember) pair recursiveMember)

end Program

end AnthillModKbSpec.Tabled
