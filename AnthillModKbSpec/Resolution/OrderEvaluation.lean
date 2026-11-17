import AnthillModKbSpec.Resolution.DictionaryEvaluation
import AnthillModKbSpec.Resolution.OrderRegistry

/-! # Evaluators for the Nat and Bool order dictionaries (S14)

The registry of `OrderRegistry` declares `less` and `equal` with primitive
contracts (total on the dictionary's domain, Bool results) and `compare` with
none. Six evaluations are registered, one per contract: `less` and `equal`
for `natOrd`, `natDesc`, and `boolOrd`. Each reads its arguments as
constructor terms (`succ(…(zero))`, `boolTrue()`, `boolFalse()`), computes
with Lean's `Nat` and `Bool`, and answers a Bool constructor term; on any
other argument it does not answer. `compare` has no evaluation: its results
are orderings, in no declared domain, and no contract states them.

The evidence: each evaluation is sound in the order model (`evaluated`),
total on its contract's domains with results in Bool (`complete`), and the
order model separates the members of Nat and Bool (`members_separated`), so
of every result domain (`separated`), and the model
is one the route's answers are about (`models`). -/

namespace AnthillModKbSpec.OrderEvaluation

open Semantics InductiveDomains AdmissionSignature OperationDictionaries DictionaryRegistry OrderDictionaries
  OrderRegistry

/-! ## Reading constructor terms -/

/-- A Nat constructor term read as its number. -/
def natOf? : T → Option Nat
  | .app .zero [] => some 0
  | .app .succ [term] => (natOf? term).map (· + 1)
  | _ => none

/-- A Bool constructor term read as its value. -/
def boolOf? : T → Option Bool
  | .app .boolTrue [] => some true
  | .app .boolFalse [] => some false
  | _ => none

/-- The Bool constructor term of a value. -/
def boolTerm (value : Bool) : T := (boolTree value).toTerm

@[simp] theorem toTerm_natTree_zero : ((natTree 0).toTerm : T) = .app .zero [] := by
  simp [natTree, Tree.toTerm]

@[simp] theorem toTerm_natTree_succ (n : Nat) : ((natTree (n + 1)).toTerm : T) = .app .succ [(natTree n).toTerm] := by
  simp [natTree, Tree.toTerm]

@[simp] theorem toTerm_boolTree_true : ((boolTree true).toTerm : T) = .app .boolTrue [] := by
  simp [boolTree, Tree.toTerm]

@[simp] theorem toTerm_boolTree_false : ((boolTree false).toTerm : T) = .app .boolFalse [] := by
  simp [boolTree, Tree.toTerm]

theorem natOf?_tree (n : Nat) : natOf? ((natTree n).toTerm : T) = some n := by
  induction n with
  | zero => simp [natOf?]
  | succ n ih => simp [natOf?, ih]

theorem natOf?_some {term : T} {n : Nat} (found : natOf? term = some n) : term = (natTree n).toTerm := by
  induction n generalizing term with
  | zero =>
      unfold natOf? at found
      split at found
      · simp
      · simp at found
      · cases found
  | succ n ih =>
      unfold natOf? at found
      split at found
      · cases found
      · rename_i inner
        simp only [Option.map_eq_some_iff, Nat.add_right_cancel_iff] at found
        obtain ⟨_, read, rfl⟩ := found
        rw [ih read, toTerm_natTree_succ]
      · cases found

theorem boolOf?_tree (value : Bool) : boolOf? ((boolTree value).toTerm : T) = some value := by
  cases value <;> simp [boolOf?]

theorem boolOf?_some {term : T} {value : Bool} (found : boolOf? term = some value) : term = (boolTree value).toTerm := by
  unfold boolOf? at found
  split at found <;> cases found <;> simp

/-! ## The evaluations -/

/-- `less` on Nat: ascending, or descending for `natDesc`. -/
def lessRun (descending : Bool) : List T → Option T
  | [a, b] =>
      match natOf? a, natOf? b with
      | some m, some n => some (boolTerm (if descending then decide (n < m) else decide (m < n)))
      | _, _ => none
  | _ => none

/-- `equal` on Nat. -/
def natEqualRun : List T → Option T
  | [a, b] =>
      match natOf? a, natOf? b with
      | some m, some n => some (boolTerm (decide (m = n)))
      | _, _ => none
  | _ => none

/-- `less` on Bool: `false < true`. -/
def boolLessRun : List T → Option T
  | [a, b] =>
      match boolOf? a, boolOf? b with
      | some x, some y => some (boolTerm (decide (boolRank x < boolRank y)))
      | _, _ => none
  | _ => none

/-- `equal` on Bool. -/
def boolEqualRun : List T → Option T
  | [a, b] =>
      match boolOf? a, boolOf? b with
      | some x, some y => some (boolTerm (x == y))
      | _, _ => none
  | _ => none

def equalPath : List Symbol := [.weakOrd, .eqModel]

def natLess : Evaluation String Data Symbol := ⟨.natOrd, 1, [], .less, 2, lessRun false⟩
def natEqual : Evaluation String Data Symbol := ⟨.natOrd, 1, equalPath, .equal, 2, natEqualRun⟩
def descLess : Evaluation String Data Symbol := ⟨.natDesc, 1, [], .less, 2, lessRun true⟩
def descEqual : Evaluation String Data Symbol := ⟨.natDesc, 1, equalPath, .equal, 2, natEqualRun⟩
def boolLess : Evaluation String Data Symbol := ⟨.boolOrd, 1, [], .less, 2, boolLessRun⟩
def boolEqual : Evaluation String Data Symbol := ⟨.boolOrd, 1, equalPath, .equal, 2, boolEqualRun⟩

/-- One evaluation per primitive contract of the registry. -/
def evaluations : List (Evaluation String Data Symbol) := [natLess, natEqual, descLess, descEqual, boolLess, boolEqual]

/-! ## Soundness in the order model -/

theorem eval_boolTerm (environment : Environment String Value) (value : Bool) :
    model.eval environment (boolTerm value) = boolean value := by
  rw [boolTerm, Tree.eval_toTerm, boolTree_denote]

theorem eval_natOf {term : T} {n : Nat} (found : natOf? term = some n) (environment : Environment String Value) :
    model.eval environment term = nat n := by
  rw [natOf?_some found, Tree.eval_toTerm, natTree_denote]

theorem eval_boolOf {term : T} {value : Bool} (found : boolOf? term = some value) (environment : Environment String Value) :
    model.eval environment term = boolean value := by
  rw [boolOf?_some found, Tree.eval_toTerm, boolTree_denote]

/-- Two Nat arguments read off a binary evaluation. -/
theorem nat_pair {run : Nat → Nat → T} {args : List T} {value : T}
    (ran : (match args with
      | [a, b] => match natOf? a, natOf? b with
        | some m, some n => some (run m n)
        | _, _ => none
      | _ => none) = some value) :
    ∃ a b m n, args = [a, b] ∧ natOf? a = some m ∧ natOf? b = some n ∧ value = run m n := by
  match args, ran with
  | [a, b], ran =>
      simp only at ran
      split at ran
      · rename_i m n first second
        cases ran
        exact ⟨a, b, m, n, rfl, first, second, rfl⟩
      · cases ran

theorem bool_pair {run : Bool → Bool → T} {args : List T} {value : T}
    (ran : (match args with
      | [a, b] => match boolOf? a, boolOf? b with
        | some x, some y => some (run x y)
        | _, _ => none
      | _ => none) = some value) :
    ∃ a b x y, args = [a, b] ∧ boolOf? a = some x ∧ boolOf? b = some y ∧ value = run x y := by
  match args, ran with
  | [a, b], ran =>
      simp only at ran
      split at ran
      · rename_i x y first second
        cases ran
        exact ⟨a, b, x, y, rfl, first, second, rfl⟩
      · cases ran

theorem natLess_sound : natLess.Sound interp := by
  intro args value ran environment
  obtain ⟨a, b, m, n, rfl, first, second, rfl⟩ := nat_pair (run := fun m n => boolTerm (decide (m < n))) ran
  simp only [natLess, interp_model, value_natOrd, List.map_cons, List.map_nil, eval_natOf first, eval_natOf second,
    eval_boolTerm]
  exact nat_less m n

theorem descLess_sound : descLess.Sound interp := by
  intro args value ran environment
  obtain ⟨a, b, m, n, rfl, first, second, rfl⟩ := nat_pair (run := fun m n => boolTerm (decide (n < m))) ran
  simp only [descLess, interp_model, value_natDesc, List.map_cons, List.map_nil, eval_natOf first, eval_natOf second,
    eval_boolTerm]
  exact desc_less m n

theorem natEqual_sound : natEqual.Sound interp := by
  intro args value ran environment
  obtain ⟨a, b, m, n, rfl, first, second, rfl⟩ := nat_pair (run := fun m n => boolTerm (decide (m = n))) ran
  simp only [natEqual, equalPath, interp_model, value_natOrd, List.map_cons, List.map_nil, eval_natOf first,
    eval_natOf second, eval_boolTerm]
  exact nat_equality m n

theorem descEqual_sound : descEqual.Sound interp := by
  intro args value ran environment
  obtain ⟨a, b, m, n, rfl, first, second, rfl⟩ := nat_pair (run := fun m n => boolTerm (decide (m = n))) ran
  simp only [descEqual, equalPath, interp_model, value_natDesc, List.map_cons, List.map_nil, eval_natOf first,
    eval_natOf second, eval_boolTerm]
  exact desc_equality m n

theorem boolLess_sound : boolLess.Sound interp := by
  intro args value ran environment
  obtain ⟨a, b, x, y, rfl, first, second, rfl⟩ :=
    bool_pair (run := fun x y => boolTerm (decide (boolRank x < boolRank y))) ran
  simp only [boolLess, interp_model, value_boolOrd, List.map_cons, List.map_nil, eval_boolOf first, eval_boolOf second,
    eval_boolTerm]
  exact bool_less x y

theorem boolEqual_sound : boolEqual.Sound interp := by
  intro args value ran environment
  obtain ⟨a, b, x, y, rfl, first, second, rfl⟩ := bool_pair (run := fun x y => boolTerm (x == y)) ran
  simp only [boolEqual, equalPath, interp_model, value_boolOrd, List.map_cons, List.map_nil, eval_boolOf first,
    eval_boolOf second, eval_boolTerm]
  exact bool_equality x y

/-- Every registered evaluation is sound in the order model. -/
theorem evaluated : snapshot.Evaluated evaluations interp := by
  intro _ _ _ _ evaluation member _
  simp only [evaluations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact natLess_sound
  · exact natEqual_sound
  · exact descLess_sound
  · exact descEqual_sound
  · exact boolLess_sound
  · exact boolEqual_sound

/-! ## Totality and separation -/

/-- The member trees of Nat and Bool are the numerals and the two Booleans. -/
theorem member_trees {domain : Domain} {tree : Tree Symbol} (member : InductiveDomains.Member sigma domain tree) :
    (domain = .nat → ∃ n, tree = natTree n) ∧ (domain = .bool → ∃ value, tree = boolTree value) := by
  induction member with
  | construct declared children members ih =>
      rcases declared with rfl | rfl | rfl | rfl
      all_goals dsimp only [zeroRule, succRule, trueRule, falseRule] at children members ih ⊢
      · exact ⟨fun _ => ⟨0, by simp [natTree]⟩, fun same => by cases same⟩
      · refine ⟨fun _ => ?_, fun same => by cases same⟩
        obtain ⟨n, inner⟩ := (ih 0).1 rfl
        refine ⟨n + 1, ?_⟩
        simp only [natTree, List.ofFn_succ, List.ofFn_zero]
        rw [show children 0 = natTree n from inner]
      · exact ⟨(fun same => by cases same), fun _ => ⟨true, by simp [boolTree]⟩⟩
      · exact ⟨(fun same => by cases same), fun _ => ⟨false, by simp [boolTree]⟩⟩

theorem member_nat {tree : Tree Symbol} (member : InductiveDomains.Member sigma .nat tree) : ∃ n, tree = natTree n :=
  (member_trees member).1 rfl

theorem member_bool {tree : Tree Symbol} (member : InductiveDomains.Member sigma .bool tree) :
    ∃ value, tree = boolTree value :=
  (member_trees member).2 rfl

theorem natTree_injective {m n : Nat} (same : natTree m = natTree n) : m = n := by
  have read := congrArg (fun tree : Tree Symbol => natOf? (tree.toTerm : T)) same
  simpa [natOf?_tree] using read

/-- The order model separates the members of Nat and Bool. -/
theorem members_separated (domain : Domain) (first second : Tree Symbol)
    (firstMember : InductiveDomains.Member sigma domain first) (secondMember : InductiveDomains.Member sigma domain second)
    (same : denote interp.model first = denote interp.model second) : first = second := by
  cases domain
  · obtain ⟨m, rfl⟩ := member_nat firstMember
    obtain ⟨n, rfl⟩ := member_nat secondMember
    rw [interp_model, natTree_denote, natTree_denote] at same
    cases same
    rfl
  · obtain ⟨x, rfl⟩ := member_bool firstMember
    obtain ⟨y, rfl⟩ := member_bool secondMember
    rw [interp_model, boolTree_denote, boolTree_denote] at same
    cases same
    rfl

/-- The order model separates the members of every result domain. -/
theorem separated : snapshot.Separated interp :=
  fun _ _ primitive _ => members_separated primitive.result

theorem natTree_member' (n : Nat) : InductiveDomains.Member snapshot.signature.signature.data.definitions .nat (natTree n) :=
  natTree_member n

theorem boolTree_member' (value : Bool) :
    InductiveDomains.Member snapshot.signature.signature.data.definitions .bool (boolTree value) :=
  boolTree_member value

/-- Two Nat members, as trees. -/
theorem nat_trees {trees : List (Tree Symbol)} (length : trees.length = [Domain.nat, Domain.nat].length)
    (members : ∀ pair ∈ [Domain.nat, Domain.nat].zip trees, InductiveDomains.Member sigma pair.1 pair.2) :
    ∃ m n, trees = [natTree m, natTree n] := by
  match trees, length with
  | [first, second], _ =>
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at members
      obtain ⟨m, rfl⟩ := member_nat members.1
      obtain ⟨n, rfl⟩ := member_nat members.2
      exact ⟨m, n, rfl⟩

theorem bool_trees {trees : List (Tree Symbol)} (length : trees.length = [Domain.bool, Domain.bool].length)
    (members : ∀ pair ∈ [Domain.bool, Domain.bool].zip trees, InductiveDomains.Member sigma pair.1 pair.2) :
    ∃ x y, trees = [boolTree x, boolTree y] := by
  match trees, length with
  | [first, second], _ =>
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at members
      obtain ⟨x, rfl⟩ := member_bool members.1
      obtain ⟨y, rfl⟩ := member_bool members.2
      exact ⟨x, y, rfl⟩

/-- An evaluation answering Bool constructor terms is closed in Bool. -/
theorem closed_of {evaluation : Evaluation String Data Symbol} {primitive : Primitive Domain Symbol}
    (result : primitive.result = .bool) (answers : ∀ args value, evaluation.run args = some value → ∃ b, value = boolTerm b) :
    evaluation.Closed snapshot.signature primitive := by
  intro args value ran
  obtain ⟨b, rfl⟩ := answers args value ran
  exact ⟨boolTree b, result ▸ boolTree_member b, rfl⟩

theorem nat_admitted (descending : Bool) {evaluation : Evaluation String Data Symbol}
    {primitive : Primitive Domain Symbol} (arguments : primitive.arguments = [.nat, .nat]) (result : primitive.result = .bool)
    (run : evaluation.run = lessRun descending ∨ evaluation.run = natEqualRun) :
    evaluation.Admitted snapshot.signature primitive := by
  constructor
  · intro trees length members
    rw [arguments] at length members
    obtain ⟨m, n, rfl⟩ := nat_trees length members
    rcases run with run | run <;> rw [run, result]
    · exact ⟨boolTree (if descending then decide (n < m) else decide (m < n)), boolTree_member _,
        by simp [lessRun, natOf?_tree, boolTerm]⟩
    · exact ⟨boolTree (decide (m = n)), boolTree_member _, by simp [natEqualRun, natOf?_tree, boolTerm]⟩
  · apply closed_of result
    intro args value ran
    rcases run with run | run <;> rw [run] at ran
    · obtain ⟨_, _, m, n, _, _, _, rfl⟩ := nat_pair (run := fun m n => boolTerm (if descending then decide (n < m) else
        decide (m < n))) ran
      exact ⟨_, rfl⟩
    · obtain ⟨_, _, m, n, _, _, _, rfl⟩ := nat_pair (run := fun m n => boolTerm (decide (m = n))) ran
      exact ⟨_, rfl⟩

theorem bool_admitted {evaluation : Evaluation String Data Symbol} {primitive : Primitive Domain Symbol}
    (arguments : primitive.arguments = [.bool, .bool]) (result : primitive.result = .bool)
    (run : evaluation.run = boolLessRun ∨ evaluation.run = boolEqualRun) :
    evaluation.Admitted snapshot.signature primitive := by
  constructor
  · intro trees length members
    rw [arguments] at length members
    obtain ⟨x, y, rfl⟩ := bool_trees length members
    rcases run with run | run <;> rw [run, result]
    · exact ⟨boolTree (decide (boolRank x < boolRank y)), boolTree_member _,
        by simp [boolLessRun, boolOf?_tree, boolTerm]⟩
    · exact ⟨boolTree (x == y), boolTree_member _, by simp [boolEqualRun, boolOf?_tree, boolTerm]⟩
  · apply closed_of result
    intro args value ran
    rcases run with run | run <;> rw [run] at ran
    · obtain ⟨_, _, x, y, _, _, _, rfl⟩ := bool_pair (run := fun x y => boolTerm (decide (boolRank x < boolRank y))) ran
      exact ⟨_, rfl⟩
    · obtain ⟨_, _, x, y, _, _, _, rfl⟩ := bool_pair (run := fun x y => boolTerm (x == y)) ran
      exact ⟨_, rfl⟩

/-- Every evaluation registered for a contract is total on its domains and
closed in Bool. -/
theorem complete : snapshot.Complete evaluations := by
  intro registration registered primitive declared evaluation member matching
  simp only [snapshot, registry, List.mem_cons, List.not_mem_nil, or_false] at registered
  simp only [evaluations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases registered with rfl | rfl | rfl <;>
    simp only [natRegistration, descRegistration, boolRegistration, primitives, List.mem_cons, List.not_mem_nil,
      or_false] at declared <;>
    rcases declared with rfl | rfl <;>
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Evaluation.For, natLess, natEqual, descLess, descEqual, boolLess, boolEqual, natRegistration,
      descRegistration, boolRegistration, equalPath] at matching
  · exact nat_admitted false rfl rfl (.inl rfl)
  · exact nat_admitted false rfl rfl (.inr rfl)
  · exact nat_admitted true rfl rfl (.inl rfl)
  · exact nat_admitted true rfl rfl (.inr rfl)
  · exact bool_admitted rfl rfl (.inl rfl)
  · exact bool_admitted rfl rfl (.inr rfl)

/-- The order model is one the route's answers are about. -/
theorem models : snapshot.Models evaluations interp := ⟨realized, checked, evaluated, separated⟩

end AnthillModKbSpec.OrderEvaluation
