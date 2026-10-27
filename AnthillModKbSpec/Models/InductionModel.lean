import AnthillModKbSpec.Foundation.InductiveDomains
import AnthillModKbSpec.Foundation.Opening
import AnthillModKbSpec.Models.HerbrandModel

namespace AnthillModKbSpec.InductionModel

open Semantics InductiveDomains

inductive Symbol where
  | zero | succ | isNat | reachable | even | hoApply
  /-- Membership in the registered predicate references of one arity. -/
  | isPred (arity : Nat)
  deriving DecidableEq, Repr

inductive Domain where
  | nat
  deriving DecidableEq

abbrev Key := DataKey Unit Symbol
abbrev Value := Key × Prop
abbrev T := Term String Unit Symbol
abbrev K := LogicalKb String Unit Symbol

def natKey : Nat → Key
  | 0 => .app .zero []
  | n + 1 => .app .succ [natKey n]

/-- Data values carry false as their proposition component. Membership tests
the whole value, so a logical value sharing a data key cannot become a Nat. -/
def natValue (n : Nat) : Value := (natKey n, False)

def zeroRule : Rule Domain Symbol := ⟨.nat, .zero, []⟩
def succRule : Rule Domain Symbol := ⟨.nat, .succ, [.nat]⟩
def sigma : Definitions Domain Symbol := fun rule => rule = zeroRule ∨ rule = succRule
def family : FiniteFamily Domain Symbol := ⟨sigma, [.nat], by intro domain; cases domain; simp⟩
def membershipSymbol : Domain → Symbol := fun _ => .isNat

def natTree : Nat → Tree Symbol
  | 0 => .node .zero []
  | n + 1 => .node .succ [natTree n]

theorem natTree_member (n : Nat) : Member sigma .nat (natTree n) := by
  induction n with
  | zero =>
      simpa [zeroRule, natTree] using Member.construct (rule := zeroRule)
        (Or.inl rfl) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  | succ n ih =>
      simpa [succRule, natTree] using Member.construct (rule := succRule)
        (Or.inr rfl) (fun _ => natTree n) (fun i => by
          have same : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) i 0
          subst i
          exact ih)

/-- The predicate references this model registers, as symbol/arity pairs. -/
def predicateRegistry : List (Symbol × Nat) := [(.reachable, 1), (.reachable, 2), (.even, 1)]

def ordinaryTruth (symbol : Symbol) (args : List Value) : Prop :=
  match symbol, args with
  | .isNat, [value] => ∃ n, value = natValue n
  | .isPred arity, [value] => ∃ symbol, (symbol, arity) ∈ predicateRegistry ∧ value = (.app symbol [], False)
  | .reachable, [value] => ∃ n, value = natValue n
  | .even, [value] => ∃ n, value = natValue n ∧ n % 2 = 0
  | _, _ => False

/-- Higher-order application resolves a nullary symbol value and removes one
argument per step. Predicate variables remain ordinary values of the carrier. -/
def atomTruth (symbol : Symbol) (args : List Value) : Prop :=
  match args with
  | (.app predicate [], _) :: rest =>
      if symbol = .hoApply then atomTruth predicate rest else ordinaryTruth symbol args
  | _ => ordinaryTruth symbol args
termination_by args.length

theorem atomTruth_ordinary (symbol : Symbol) (ordinary : symbol ≠ .hoApply) (args : List Value) :
    atomTruth symbol args ↔ ordinaryTruth symbol args := by
  cases args with
  | nil => simp [atomTruth]
  | cons value rest =>
      rcases value with ⟨key, truth⟩
      cases key with
      | lit value => simp [atomTruth]
      | app predicate args => cases args <;> simp [atomTruth, ordinary]

/-- A free constructor-key model with exact Nat membership and nontrivial
predicate truth. Logical values still inhabit the same untyped carrier. -/
def model : Model Unit Symbol Value .hoApply :=
  { Model.herbrand .hoApply (fun _ _ => False) with
    application := fun symbol args => (.app symbol (args.map Prod.fst), atomTruth symbol args)
    holds_hoApply := by
      intro predicate args
      change atomTruth .hoApply ((.app predicate [], atomTruth predicate []) :: args) ↔ atomTruth predicate args
      simp [atomTruth] }

theorem complement : model.ComplementNAF := by intro value; rfl

theorem application_nat (value : Value) :
    model.holds (model.application .isNat [value]) ↔ ∃ n, value = natValue n :=
  atomTruth_ordinary .isNat (by decide) _

theorem application_reachable (value : Value) :
    model.holds (model.application .reachable [value]) ↔ ∃ n, value = natValue n :=
  atomTruth_ordinary .reachable (by decide) _

theorem application_even (value : Value) :
    model.holds (model.application .even [value]) ↔ ∃ n, value = natValue n ∧ n % 2 = 0 :=
  atomTruth_ordinary .even (by decide) _

/-- Like data values, symbol references carry false as their proposition. -/
theorem application_reference (symbol : Symbol) (ordinary : symbol ≠ .hoApply) :
    model.application symbol [] = (.app symbol [], False) := by
  apply Prod.ext
  · rfl
  · exact propext ((atomTruth_ordinary symbol ordinary []).trans (by cases symbol <;> simp [ordinaryTruth]))

/-- `isPred n` holds exactly on references of symbols registered at arity n. -/
theorem application_isPred (arity : Nat) (value : Value) :
    model.holds (model.application (.isPred arity) [value]) ↔
      ∃ symbol, (symbol, arity) ∈ predicateRegistry ∧ model.application symbol [] = value := by
  have ordinary : ∀ symbol, (symbol, arity) ∈ predicateRegistry → symbol ≠ .hoApply := by
    intro symbol member
    simp only [predicateRegistry, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at member
    rcases member with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  refine (atomTruth_ordinary (.isPred arity) Symbol.noConfusion [value]).trans ⟨?_, ?_⟩
  · rintro ⟨symbol, member, rfl⟩
    exact ⟨symbol, member, application_reference symbol (ordinary symbol member)⟩
  · rintro ⟨symbol, member, rfl⟩
    exact Exists.intro symbol ⟨member, application_reference symbol (ordinary symbol member)⟩

@[simp] theorem application_zero : model.application .zero [] = natValue 0 := by
  apply Prod.ext
  · rfl
  · exact propext (atomTruth_ordinary .zero (by decide) _)

@[simp] theorem application_succ (n : Nat) :
    model.application .succ [natValue n] = natValue (n + 1) := by
  apply Prod.ext
  · rfl
  · exact propext (atomTruth_ordinary .succ (by decide) _)

theorem natTree_denote (n : Nat) : denote model (natTree n) = natValue n := by
  induction n with
  | zero => simpa only [natTree, denote, List.map_nil] using application_zero
  | succ n ih => simpa only [natTree, denote, List.map_cons, List.map_nil, ih] using application_succ n

theorem member_denote {domain : Domain} {tree : Tree Symbol} (member : Member sigma domain tree) :
    ∃ n, denote model tree = natValue n := by
  induction member with
  | construct declared children members ih =>
      rcases declared with rfl | rfl
      all_goals dsimp only [zeroRule, succRule] at children members ih ⊢
      · exact ⟨0, by simp [denote]⟩
      · obtain ⟨n, same⟩ := ih 0
        refine ⟨n + 1, ?_⟩
        simp [denote, same]

theorem realizes : Realizes model sigma membershipSymbol := by
  intro domain value
  cases domain
  change model.holds (model.application .isNat [value]) ↔ _
  rw [application_nat]
  constructor
  · rintro ⟨n, rfl⟩; exact ⟨natTree n, natTree_member n, natTree_denote n⟩
  · rintro ⟨tree, member, same⟩
    obtain ⟨n, equation⟩ := member_denote member
    exact ⟨n, same.symm.trans equation⟩

def zero : T := .app .zero []
def succ (value : T) : T := .app .succ [value]
def isNat (value : T) : T := .app .isNat [value]
def reachable (value : T) : T := .app .reachable [value]
def even (value : T) : T := .app .even [value]
def applyP (predicate value : T) : T := .hoApply .hoApply predicate [value]

/-- The step obligation is guarded: only generated Nat values need an IH. -/
def step (predicate : T) : T := .forallVar "n"
  (.imp (isNat (.var "n")) (.imp (applyP predicate (.var "n")) (applyP predicate (succ (.var "n")))))

/-- Induction is an actual KB clause, valid for every predicate value P.
Its free variables P and x are implicitly universally quantified by Models. -/
def inductionRule : HornClause String Unit Symbol :=
  .definite (applyP (.var "P") (.var "x"))
    [isNat (.var "x"), applyP (.var "P") zero, step (.var "P")]

def natZero : HornClause String Unit Symbol := .definite (isNat zero) []
def natSucc : HornClause String Unit Symbol :=
  .definite (isNat (succ (.var "x"))) [isNat (.var "x")]

def inductionKb : K := {inductionRule, natZero, natSucc}

def reachableZero : HornClause String Unit Symbol := .definite (reachable zero) []
def reachableSucc : HornClause String Unit Symbol :=
  .definite (reachable (succ (.var "x"))) [reachable (.var "x")]
def evenZero : HornClause String Unit Symbol := .definite (even zero) []
def evenSuccSucc : HornClause String Unit Symbol :=
  .definite (even (succ (succ (.var "x")))) [even (.var "x")]

/-- Predicate definitions are added to the same KB and interpreted in the same
model. These clauses do not assert model existence for arbitrary definitions. -/
def kb : K := {reachableZero, reachableSucc, evenZero, evenSuccSucc, inductionRule, natZero, natSucc}

theorem inductionRule_valid (environment : Environment String Value) :
    model.Satisfies environment inductionRule.toFormula := by
  simp only [inductionRule, HornClause.toFormula, Term.conjunction, List.foldr_cons, List.foldr_nil, isNat, applyP, Term.hoApply, zero, succ, step, Model.Satisfies, Model.eval, List.map_cons, List.map_nil,
    model.holds_implication, model.holds_conjunction]
  rintro ⟨domain, base, stepProof, _⟩
  obtain ⟨n, same⟩ := (application_nat _).mp domain
  have all : ∀ k, model.holds (model.application .hoApply [environment "P", natValue k]) := by
    intro k
    induction k with
    | zero => simpa only [zero, Model.eval, application_zero] using base
    | succ k ih =>
        have atK := (model.holds_universal _).mp stepProof (natValue k)
        have member := (application_nat _).mpr ⟨k, rfl⟩
        simp only [update, String.reduceEq, ↓reduceIte, application_succ, model.holds_implication] at atK
        exact atK member ih
  simpa only [applyP, Term.hoApply, Model.eval, List.map_cons, List.map_nil, same] using all n

theorem natZero_valid (environment : Environment String Value) : model.Satisfies environment natZero.toFormula := by
  simp only [natZero, HornClause.toFormula, Term.conjunction, List.foldr_nil, isNat, zero, Model.Satisfies, Model.eval, List.map_cons, List.map_nil, model.holds_implication]
  intro _
  exact (application_nat _).mpr ⟨0, application_zero⟩

theorem natSucc_valid (environment : Environment String Value) : model.Satisfies environment natSucc.toFormula := by
  simp only [natSucc, HornClause.toFormula, Term.conjunction, List.foldr_cons, List.foldr_nil, isNat, succ, Model.Satisfies, Model.eval, List.map_cons, List.map_nil,
    model.holds_implication, model.holds_conjunction]
  rintro ⟨member, _⟩
  obtain ⟨n, same⟩ := (application_nat _).mp member
  apply (application_nat _).mpr
  exact ⟨n + 1, by simpa only [succ, Model.eval, List.map_cons, List.map_nil, same] using application_succ n⟩

theorem inductionKb_models : model.Models inductionKb := by
  intro clause member environment
  simp only [inductionKb, LogicalKb.mem_insert, LogicalKb.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · exact inductionRule_valid environment
  · exact natZero_valid environment
  · exact natSucc_valid environment

theorem reachableZero_valid (environment : Environment String Value) :
    model.Satisfies environment reachableZero.toFormula := by
  simp only [reachableZero, HornClause.toFormula, Term.conjunction, List.foldr_nil,
    reachable, zero, Model.Satisfies, Model.eval, List.map_cons, List.map_nil, model.holds_implication]
  intro _
  exact (application_reachable _).mpr ⟨0, application_zero⟩

theorem reachableSucc_valid (environment : Environment String Value) :
    model.Satisfies environment reachableSucc.toFormula := by
  simp only [reachableSucc, HornClause.toFormula, Term.conjunction, List.foldr_cons, List.foldr_nil,
    reachable, succ, Model.Satisfies, Model.eval, List.map_cons, List.map_nil,
    model.holds_implication, model.holds_conjunction]
  rintro ⟨member, _⟩
  obtain ⟨n, same⟩ := (application_reachable _).mp member
  exact (application_reachable _).mpr ⟨n + 1, by rw [same, application_succ]⟩

theorem evenZero_valid (environment : Environment String Value) :
    model.Satisfies environment evenZero.toFormula := by
  simp only [evenZero, HornClause.toFormula, Term.conjunction, List.foldr_nil,
    even, zero, Model.Satisfies, Model.eval, List.map_cons, List.map_nil, model.holds_implication]
  intro _
  exact (application_even _).mpr ⟨0, application_zero, rfl⟩

theorem evenSuccSucc_valid (environment : Environment String Value) :
    model.Satisfies environment evenSuccSucc.toFormula := by
  simp only [evenSuccSucc, HornClause.toFormula, Term.conjunction, List.foldr_cons, List.foldr_nil,
    even, succ, Model.Satisfies, Model.eval, List.map_cons, List.map_nil,
    model.holds_implication, model.holds_conjunction]
  rintro ⟨member, _⟩
  obtain ⟨n, same, parity⟩ := (application_even _).mp member
  apply (application_even _).mpr
  exact ⟨n + 2, by rw [same, application_succ, application_succ], by omega⟩

theorem kb_models : model.Models kb := by
  intro clause member environment
  simp only [kb, LogicalKb.mem_insert, LogicalKb.mem_singleton] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reachableZero_valid environment
  · exact reachableSucc_valid environment
  · exact evenZero_valid environment
  · exact evenSuccSucc_valid environment
  · exact inductionRule_valid environment
  · exact natZero_valid environment
  · exact natSucc_valid environment

theorem natKey_injective : Function.Injective natKey := by
  intro n
  induction n with
  | zero =>
      intro m same
      cases m with
      | zero => rfl
      | succ m => cases same
  | succ n ih =>
      intro m same
      cases m with
      | zero => cases same
      | succ m =>
          injection same with symbolSame children
          injection children with child
          exact congrArg Nat.succ (ih child)

theorem natValue_injective : Function.Injective natValue := by
  intro n m same
  exact natKey_injective (congrArg Prod.fst same)

theorem reachable_at_nat (n : Nat) : model.holds (model.application .reachable [natValue n]) :=
  (application_reachable _).mpr ⟨n, rfl⟩

theorem even_at_nat (n : Nat) : model.holds (model.application .even [natValue n]) ↔ n % 2 = 0 := by
  rw [application_even]
  constructor
  · rintro ⟨m, same, parity⟩
    exact natValue_injective same ▸ parity
  · intro parity; exact ⟨n, rfl, parity⟩

/-- Least relations generated by the two recursive predicate definitions. -/
inductive Reachable : Nat → Prop where
  | zero : Reachable 0
  | succ : Reachable n → Reachable (n + 1)

inductive Even : Nat → Prop where
  | zero : Even 0
  | succSucc : Even n → Even (n + 2)

theorem reachable_generated (n : Nat) : Reachable n := by
  induction n with
  | zero => exact .zero
  | succ n ih => exact .succ ih

theorem even_generated_iff (n : Nat) : Even n ↔ n % 2 = 0 := by
  constructor
  · intro proof
    induction proof with
    | zero => rfl
    | succSucc proof ih => omega
  · have generated : ∀ k, k % 2 = 0 → Even k := by
      intro k
      induction k using Nat.strongRecOn with
      | ind k ih =>
          intro parity
          cases k with
          | zero => exact .zero
          | succ k =>
              cases k with
              | zero => omega
              | succ k => exact .succSucc (ih k (by omega) (by omega))
    exact generated n

theorem reachable_exact (value : Value) :
    model.holds (model.application .reachable [value]) ↔ ∃ n, value = natValue n ∧ Reachable n := by
  rw [application_reachable]
  constructor
  · rintro ⟨n, same⟩; exact ⟨n, same, reachable_generated n⟩
  · rintro ⟨n, same, _⟩; exact ⟨n, same⟩

theorem even_exact (value : Value) :
    model.holds (model.application .even [value]) ↔ ∃ n, value = natValue n ∧ Even n := by
  rw [application_even]
  constructor
  · rintro ⟨n, same, parity⟩; exact ⟨n, same, (even_generated_iff n).mpr parity⟩
  · rintro ⟨n, same, generated⟩; exact ⟨n, same, (even_generated_iff n).mp generated⟩

/-- A derivation actually uses the object-level induction clause. The base and
step are explicit local obligations, not added as axioms of Derives. -/
theorem induction_rule_applies (context : ProofContext String Unit Symbol)
    (domain : Derives .hoApply kb context (isNat (.var "x")))
    (base : Derives .hoApply kb context (applyP (.var "P") zero))
    (stepProof : Derives .hoApply kb context (step (.var "P"))) :
    Derives .hoApply kb context (applyP (.var "P") (.var "x")) := by
  apply Derives.clause (head := applyP (.var "P") (.var "x"))
    (body := [isNat (.var "x"), applyP (.var "P") zero, step (.var "P")]) (σ := Term.var)
  · simp [kb, inductionRule]
  · exact Substitutes.identity _
  · exact Substitutes.identity _
  · exact .conjIntro domain (.conjIntro base (.conjIntro stepProof .truth))

/-- The model is not an all-atoms-true witness. -/
theorem even_one_false (environment : Environment String Value) :
    ¬ model.Satisfies environment (even (succ zero)) := by
  intro proof
  simp only [even, succ, zero, Model.Satisfies, Model.eval, List.map_cons, List.map_nil] at proof
  rw [application_zero, application_succ] at proof
  obtain ⟨n, same, parity⟩ := (application_even _).mp proof
  have equal := natValue_injective same
  omega

/-- Existence for both stages of the nonempty KB, in the exact same model. -/
theorem model_exists : ∃ witness : Model Unit Symbol Value .hoApply,
    Realizes witness sigma membershipSymbol ∧ witness.ComplementNAF ∧
    witness.Models inductionKb ∧ witness.Models kb :=
  ⟨model, realizes, complement, inductionKb_models, kb_models⟩

end AnthillModKbSpec.InductionModel
