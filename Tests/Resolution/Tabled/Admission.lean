import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Tabled AnthillModKbSpec.Answers AnthillModKbSpec.Admission
  AnthillModKbSpec.AdmissionSignature AnthillModKbSpec.InductiveDomains

namespace TabledAdmissionTests

/-! Executable traces of S23: the fast fragment's admission. Each `#guard`
evaluates compiled code: the classification of every predicate into P1, P2,
or Undecided with blockers, its cost class, degree, and determinism, before
anything runs. -/

inductive Sym where
  | reachable | append | path | edge | count | p | q | r | s | nat | isZero | grow | lt
  | zero | succ | nil | cons | a | b | c | d
  | isNat | allData | unknown | ha | f
  deriving DecidableEq, Repr

abbrev T := Term Nat Nat Sym
abbrev Clause := HornClause Nat Nat Sym

def k (symbol : Sym) : T := .app symbol []
def atom (symbol : Sym) (args : List T) : T := .app symbol args
def v (name : Nat) : T := .var name
def naf (goal : T) : T := .defaultNeg goal
def fact (head : T) : Clause := .definite head []
def rule (head : T) (body : List T) : Clause := .definite head body

/-- The declared free constructors. -/
def free : Sym → Nat → Bool
  | .zero, 0 | .nil, 0 | .a, 0 | .b, 0 | .c, 0 | .d, 0 | .succ, 1 | .cons, 2 => true
  | _, _ => false

def guard : Sym → Bool
  | .isNat | .allData => true
  | _ => false

def unknownMarker : Sym → Bool := (· == .unknown)

open Mode in
/-- The mode declarations the KB generator emits. -/
def modes : Modes Sym
  | .reachable => some [input]
  | .append => some [input, input, output]
  | .path | .edge | .count | .lt => some [input, output]
  | .nat | .isZero => some [output]
  | .p | .q | .r | .s | .grow => some [input]
  | _ => none

def program (clauses : List Clause) (declared : Modes Sym := modes) : Program Nat Nat Sym :=
  ⟨clauses.zipIdx.map fun (clause, index) => (index, clause), free, guard, unknownMarker, .ha, declared⟩

def isP1 : Profile Nat Nat Sym → Bool
  | .p1 => true
  | _ => false

def isP2 : Profile Nat Nat Sym → Bool
  | .p2 _ => true
  | _ => false

/-- The reasons a profile reports, with their sites and paths. -/
def reasons : Profile Nat Nat Sym → List (Site × List Nat × Reason)
  | .p2 notes => notes.map fun note => (note.site, note.path, note.reason)
  | _ => []

def sites : Profile Nat Nat Sym → List (Option Site × List Nat)
  | .undecided blockers => blockers.map fun blocker =>
      match blocker.place with
      | .site site => (some site, blocker.path)
      | .reached _ _ => (none, blocker.path)
  | _ => []

def missing : Profile Nat Nat Sym → List Bool
  | .undecided blockers => blockers.map fun blocker =>
      match blocker.missing with
      | .mode => true
      | _ => false
  | _ => []

def profile (clauses : List Clause) (predicate : Sym) : Profile Nat Nat Sym :=
  ((program clauses).classOf predicate).profile

def classOf (clauses : List Clause) (predicate : Sym) : Class Nat Nat Sym :=
  (program clauses).classOf predicate

def succ (term : T) : T := atom .succ [term]
def cons (head tail : T) : T := atom .cons [head, tail]

/-! ## P1: complete predicates -/

/-- `reachable(zero). reachable(succ(X)) :- reachable(X).` with mode (+). -/
def reachableKb : List Clause :=
  [fact (atom .reachable [k .zero]), rule (atom .reachable [succ (v 0)]) [atom .reachable [v 0]]]

#guard isP1 (profile reachableKb .reachable)
#guard (classOf reachableKb .reachable).complete
#guard (classOf reachableKb .reachable).cyclic
#guard (classOf reachableKb .reachable).degree == 1
#guard (classOf reachableKb .reachable).deterministic

/-- `append(nil, L, L). append(cons(H, T), L, cons(H, R)) :- append(T, L, R).`
with mode (+, +, −): its output is constructed, and every recursive call
decreases. -/
def appendKb : List Clause :=
  [fact (atom .append [k .nil, v 0, v 0]),
   rule (atom .append [cons (v 1) (v 2), v 0, cons (v 1) (v 3)]) [atom .append [v 2, v 0, v 3]]]

#guard isP1 (profile appendKb .append)
#guard (classOf appendKb .append).complete
#guard !(classOf appendKb .append).dataOutputs
#guard (classOf appendKb .append).degree == 4
#guard (classOf appendKb .append).deterministic

/-- `path(X, Y) :- edge(X, Y). path(X, Y) :- edge(X, Z), path(Z, Y).` over
facts with mode (+, −): `Z` is an output of a predicate with data-term outputs. -/
def pathKb : List Clause :=
  [fact (atom .edge [k .a, k .b]), fact (atom .edge [k .b, k .a]), fact (atom .edge [k .b, k .c]),
   rule (atom .path [v 0, v 1]) [atom .edge [v 0, v 1]],
   rule (atom .path [v 0, v 1]) [atom .edge [v 0, v 2], atom .path [v 2, v 1]]]

#guard isP1 (profile pathKb .path)
#guard (classOf pathKb .path).complete
#guard (classOf pathKb .path).dataOutputs
#guard (classOf pathKb .path).degree == 3
#guard !(classOf pathKb .path).deterministic
#guard (classOf pathKb .edge).degree == 0

/-- The lowered form, with guards prepended: a guard on the output `Y` waits
until `edge` binds it. -/
def loweredPathKb : List Clause :=
  pathKb.take 3 ++
  [rule (atom .path [v 0, v 1]) [atom .allData [v 0], atom .allData [v 1], atom .edge [v 0, v 1]],
   rule (atom .path [v 0, v 1]) [atom .allData [v 0], atom .allData [v 1], atom .allData [v 2],
     atom .edge [v 0, v 2], atom .path [v 2, v 1]]]

#guard isP1 (profile loweredPathKb .path)

/-! ## P2: budgeted predicates, NAF over a cycle -/

/-- `grow(X) :- grow(succ(X))`: a recursive call that grows its input. -/
def growKb : List Clause := [rule (atom .grow [v 0]) [atom .grow [succ (v 0)]]]

#guard !(classOf growKb .grow).complete
#guard reasons (profile growKb .grow) == [(.body 0 0, [], .growingCall)]

/-- `count(X, zero). count(X, succ(Y)) :- count(X, Y).` with mode (+, −): one
call, infinitely many answers. Budgeted, naming the growing answer. -/
def countKb : List Clause :=
  [fact (atom .count [v 0, k .zero]), rule (atom .count [v 0, succ (v 1)]) [atom .count [v 0, v 1]]]

#guard !(classOf countKb .count).complete
#guard reasons (profile countKb .count) == [(.head 1, [1], .growingAnswer)]

/-- `q :- r. r :- q. p :- naf q.`: NAF over a predicate on a cycle. -/
def cycleKb : List Clause :=
  [rule (atom .q [k .a]) [atom .r [k .a]], rule (atom .r [k .a]) [atom .q [k .a]], rule (atom .p [k .a]) [naf (atom .q [k .a])]]

#guard (classOf cycleKb .p).complete
#guard reasons (profile cycleKb .p) == [(.body 2 0, [], .cyclicNegation)]
#guard isP1 (profile cycleKb .q)

-- NAF over a predicate off any cycle is P1.
#guard isP1 (profile [fact (atom .q [k .a]), rule (atom .p [v 0]) [naf (atom .q [v 0])]] .p)

/-! ## Blockers -/

/-- `p(X) :- naf nat(Y)` with `nat(−)` budgeted (`nat(succ(X)) :- nat(X)`):
the NAF needs constructive negation, and its operand may have infinitely many
answers. -/
def natKb : List Clause :=
  [fact (atom .nat [k .zero]), rule (atom .nat [succ (v 0)]) [atom .nat [v 0]],
   rule (atom .p [v 0]) [naf (atom .nat [v 1])]]

#guard !(classOf natKb .nat).complete
#guard sites (profile natKb .p) == [(some (.body 2 0), [])]

-- With `isZero(zero)` and mode `isZero(−)`, `p(X) :- naf isZero(Y)` is admitted: constructive
-- negation over a complete operand.
#guard isP1 (profile [fact (atom .isZero [k .zero]), rule (atom .p [v 0]) [naf (atom .isZero [v 1])]] .p)

-- An unsafe NAF goal: `p(X) :- naf q(Y)` with `q(+)`: the operand's input is unbound.
#guard sites (profile [fact (atom .q [k .a]), rule (atom .p [v 0]) [naf (atom .q [v 1])]] .p) ==
  [(some (.body 1 0), [0])]

/-- A compound head concluding `p`: the completion leaves `p` open. -/
def compoundKb : List Clause :=
  [.definite (.conj (atom .p [k .a]) (atom .q [k .a])) [], fact (atom .p [k .b])]

#guard sites (profile compoundKb .p) == [(some (.head 0), [])]
#guard sites (profile compoundKb .q) == [(some (.head 0), [])]
#guard isP1 (profile [fact (atom .r [k .a])] .r)

-- A call with an unbound input, a predicate without a mode, a head output never bound.
#guard missing (profile [rule (atom .p [v 0]) [atom .q [v 1]]] .p) == [true]
#guard missing (profile [rule (atom .p [v 0]) [atom .f [v 0]]] .p) == [true]
#guard missing (profile [rule (atom .lt [v 0, v 1]) [atom .q [v 0]]] .lt) == [true]

/-! ## Contexts, denials, and heads concluding any predicate -/

-- A generic universal goal is P2: a failure is Undecided.
#guard reasons (profile [fact (atom .q [k .a]), rule (atom .p [v 0]) [.forallVar 5 (atom .q [v 5])]] .p) ==
  [(.body 1 0, [], .universal)]

-- A hypothesis with a name bound from the data is P2 and budgeted; a closed
-- atomic one is decided, read materially.
#guard reasons (profile [rule (atom .p [v 0]) [.imp (atom .q [v 0]) (atom .q [v 0])]] .p) ==
  [(.body 0 0, [], .hypothesis)]
#guard !(classOf [rule (atom .p [v 0]) [.imp (atom .q [v 0]) (atom .q [v 0])]] .p).complete
#guard isP1 (profile [rule (atom .p [v 0]) [.imp (atom .q [k .a]) (atom .q [v 0])]] .p)

-- A non-Harrop antecedent is outside the fragment.
#guard sites (profile [rule (atom .p [v 0]) [.imp (.disj (atom .q [k .a]) (atom .q [k .b])) (atom .q [v 0])]] .p) ==
  [(some (.body 0 0), [0])]

-- A denial over a predicate on a cycle makes P2 every predicate it constrains.
def denialKb : List Clause := cycleKb.take 2 ++ [.goal [atom .q [k .a]], fact (atom .s [k .a])]

#guard reasons (profile denialKb .q) == [(.head 2, [], .cyclicDenial)]
#guard isP1 (profile denialKb .s)

-- A head that may conclude any predicate blocks every predicate: a formula
-- variable head, and `ho_apply` of a predicate variable.
#guard sites (profile [fact (atom .r [k .a]), .definite (v 0) []] .r) == [(some (.head 1), [])]
#guard sites (profile [fact (atom .r [k .a]), .definite (atom .ha [v 0, k .a]) []] .r) == [(some (.head 1), [])]

-- An equation is a statement: it blocks no predicate.
#guard isP1 (profile [fact (atom .r [k .a]), .definite (.equal (k .a) (k .a)) []] .r)
#guard (program [.definite (.equal (k .a) (k .a)) []]).statements.length == 1

-- A defined operation in data is outside the fragment.
#guard sites (profile [fact (atom .r [atom .f [k .a]])] .r) == [(some (.head 0), [0])]

-- A concrete indirect call `ho_apply(q, x)` is the call `q(x)`.
#guard isP1 (profile [fact (atom .q [k .a]), rule (atom .p [v 0]) [atom .ha [k .q, v 0]]] .p)
#guard sites (profile [rule (atom .p [v 0]) [atom .ha [v 1, v 0]]] .p) == [(some (.body 0 0), [])]

-- An open predicate is P1: its Unknown is a decided answer.
#guard isP1 (profile [rule (atom .q [k .a]) [k .unknown]] .q)

-- A denial written with a `false` head is a denial too.
#guard reasons (profile (cycleKb.take 2 ++ [.definite .falsity [atom .q [k .a]]]) .q) == [(.head 2, [], .cyclicDenial)]

-- A denial the module cannot check blocks every predicate and query, even
-- one whose body calls no predicate: consistency is left open.
def dictionaryCall : T := .dictionaryCall (k .a) [] .f []
#guard sites (profile [fact (atom .r [k .a]), .goal [.equal dictionaryCall (k .b)]] .r) == [(some (.body 1 0), [0])]

-- A head that is no formula blocks every predicate.
#guard sites (profile [fact (atom .r [k .a]), .definite (.lit 3) [atom .q [v 0]]] .r) == [(some (.head 1), [])]
#guard sites (profile [fact (atom .r [k .a]), .definite dictionaryCall []] .r) == [(some (.head 1), [])]

-- The bodies of the rules an antecedent or the context assumes are scanned:
-- a formula variable in one is a blocker, beside the antecedent's unbound name.
#guard sites (profile [rule (atom .p [v 0]) [.imp (.forallVar 5 (.imp (v 9) (atom .q [v 5]))) (atom .q [v 0])]] .p) ==
  [(some (.body 0 0), [0, 0, 0]), (some (.body 0 0), [0])]
-- `ho_apply` of a predicate variable in an antecedent, and a defined
-- operation in a concrete one.
#guard sites (profile [rule (atom .p [v 0]) [.imp (atom .ha [v 1, k .a]) (atom .q [v 0])]] .p) ==
  [(some (.body 0 0), [0]), (some (.body 0 0), [0])]
#guard sites (profile [rule (atom .p [v 0]) [.imp (atom .ha [k .q, atom .f [k .a]]) (atom .q [v 0])]] .p) ==
  [(some (.body 0 0), [0, 1])]

-- A guard's argument is data: a defined operation in it is a blocker.
#guard sites (profile [rule (atom .p [v 0]) [atom .isNat [atom .f [v 0]]]] .p) == [(some (.body 0 0), [0])]

-- A guard on a name a constructive NAF constrains is admitted: S21 decides
-- the guard with the constraint. A guard on a name nothing binds or
-- constrains is a blocker.
#guard isP1 (profile [fact (atom .isZero [k .zero]), rule (atom .p [v 0]) [atom .isNat [v 1], naf (atom .isZero [v 1])]] .p)
#guard missing (profile [rule (atom .p [v 0]) [atom .isNat [v 1]]] .p) == [true]

-- The degree counts the names quantifiers bind: `∃Z` joins as an implicit
-- `Z` does.
#guard (classOf (pathKb.take 4 ++ [rule (atom .path [v 0, v 1])
    [.existsVar 2 (.conj (atom .edge [v 0, v 2]) (atom .path [v 2, v 1]))]]) .path).degree == 3

/-! ## Locality -/

-- A blocker in a predicate p does not call is not p's; one in a callee is.
def localityKb : List Clause :=
  [fact (atom .q [k .a]), rule (atom .r [v 0]) [atom .f [v 0]], rule (atom .p [v 0]) [atom .q [v 0]],
   rule (atom .s [v 0]) [atom .r [v 0]]]

#guard isP1 (profile localityKb .p)
#guard sites (profile localityKb .s) == [(some (.body 1 0), [])]

-- Budgeted is inherited: a caller of a budgeted predicate is budgeted.
#guard !(classOf (growKb ++ [rule (atom .p [v 0]) [atom .grow [v 0]]]) .p).complete
#guard reasons (profile (growKb ++ [rule (atom .p [v 0]) [atom .grow [v 0]]]) .p) == [(.body 0 0, [], .growingCall)]

/-! ## Queries -/

def ask (clauses : List Clause) (goal : T) (answers : List Nat) (context : List T := []) : Profile Nat Nat Sym :=
  (program clauses).admit ⟨context, goal, answers⟩

-- `path(a, Y)` with the answer name `Y` is P1; `path(X, b)` with `X` an
-- answer name has an unbound input.
#guard isP1 (ask pathKb (atom .path [k .a, v 7]) [7])
#guard sites (ask pathKb (atom .path [v 7, k .b]) [7]) == [(some .goal, []), (some .goal, [])]
-- An answer name no goal binds is a blocker.
#guard sites (ask pathKb (atom .path [k .a, k .b]) [7]) == [(some .goal, [])]
-- A rigid parameter is an input: `path(x, Y)` with `x` a parameter.
#guard isP1 (ask pathKb (atom .path [v 8, v 7]) [7])
-- A NAF on a parameter needs constructive negation, its operand read with
-- the parameter unbound: at an output of the complete `edge` it is admitted;
-- at an input it is a blocker.
#guard isP1 (ask pathKb (naf (atom .edge [k .a, v 8])) [])
#guard sites (ask pathKb (naf (atom .edge [v 8, k .b])) []) == [(some .goal, [0])]
-- The query's profile follows the predicates it uses.
#guard isP2 (ask (pathKb ++ growKb) (.conj (atom .path [k .a, v 7]) (atom .grow [k .a])) [7])
#guard isP1 (ask (pathKb ++ growKb) (atom .path [k .a, v 7]) [7])
-- Context: facts and splits are P1, a rule is P2, a negated assumption is outside.
#guard isP1 (ask pathKb (atom .path [k .a, v 7]) [7] [atom .edge [k .c, k .d], .disj (atom .edge [k .d, k .a]) (atom .edge [k .d, k .b])])
#guard reasons (ask pathKb (atom .path [k .a, v 7]) [7] [.forallVar 3 (.imp (atom .edge [v 3, k .a]) (atom .edge [k .a, v 3]))]) ==
  [(.assumption 0, [], .localRule)]
#guard sites (ask pathKb (atom .path [k .a, v 7]) [7] [naf (atom .edge [k .a, k .d])]) == [(some (.assumption 0), [])]
-- A context rule's body is scanned: a dictionary call in it is a blocker.
#guard sites (ask pathKb (atom .path [k .a, v 7]) [7] [.forallVar 3 (.imp dictionaryCall (atom .edge [k .a, v 3]))]) ==
  [(some (.assumption 0), [0, 0])]

-- A query's own hypothesis makes it budgeted; a query over a
-- non-deterministic predicate is not deterministic.
#guard !((program pathKb).queryClass ⟨[], .imp (atom .edge [v 8, k .a]) (atom .path [k .a, v 7]), [7]⟩).complete
#guard ((program pathKb).queryClass ⟨[], atom .path [k .a, v 7], [7]⟩).complete
#guard !((program pathKb).queryClass ⟨[], atom .path [k .a, v 7], [7]⟩).deterministic

-- Undecided before anything runs, with the blockers (S22).
#guard match (program [rule (atom .p [v 0]) [atom .q [v 1]]]).answer? (Proof := Unit) (Refutation := Unit) (Witness := Unit)
    ⟨[], atom .p [k .a], []⟩ with
  | some (.undecided [_]) => true
  | _ => false
#guard ((program pathKb).answer? (Proof := Unit) (Refutation := Unit) (Witness := Unit) ⟨[], atom .path [k .a, v 7], [7]⟩).isNone

/-! ## The effective program, as lowering gives it -/

inductive Dom where
  | nat
  deriving DecidableEq, Repr

def zeroRule : Rule Dom Sym := ⟨.nat, .zero, []⟩
def succRule : Rule Dom Sym := ⟨.nat, .succ, [.nat]⟩
def family : FiniteFamily Dom Sym := ⟨fun rule => rule = zeroRule ∨ rule = succRule, [.nat], fun domain => by cases domain; simp⟩

/-- `isNat` is Nat's membership symbol and `allData` is D_all. -/
def snapshot : SignatureSnapshot Dom Sym := ⟨0, ⟨family, fun _ => .isNat, .allData, fun _ => .isNat, []⟩⟩
def names : Nat → Nat := fun index => 100 + index
def rules : List (Rule Dom Sym) := [zeroRule, succRule]

theorem listed : ∀ rule ∈ rules, snapshot.signature.data.definitions rule := by
  intro rule member
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at member
  exact member

theorem complete : ∀ rule, snapshot.signature.data.definitions rule → rule ∈ rules := by
  intro rule declared
  rcases declared with rfl | rfl <;> simp [rules]

theorem distinct : DistinctNames snapshot.signature.data.definitions names :=
  DistinctNames.of_injective fun first second same => by simpa [names] using same

/-- KB clauses lowered with every implicit variable at D_all, as
`Program.build` lays out the effective program. -/
def built (clauses : List Clause) : Machine.Program Nat Nat Sym :=
  ⟨clauses.mapIdx (fun index clause =>
      ⟨.lowered index, Elaboration.elaborateClause snapshot.naming Elaboration.defaultRanges (fun _ => .allData) clause⟩) ++
    (Machine.signatureClauses snapshot names rules).map (⟨.signature, ·⟩), Machine.guardSymbol snapshot⟩

def effective (clauses : List Clause) : ProgramInput Dom Nat Nat Sym :=
  ⟨snapshot, names, rules, listed, complete, distinct, built clauses, fun _ => Machine.guardSymbol_iff⟩

def lowered (clauses : List Clause) : Program Nat Nat Sym := Program.ofInput (effective clauses) .ha free unknownMarker modes

-- Lowering prepends a guard for every clause variable, the output `Y` of
-- `path` included: each waits until a goal binds its name, and the lowered
-- `path` is P1.
#guard ((lowered pathKb).definitions .path).all fun (_, _, body) => body.length ≥ 3
#guard isP1 ((lowered pathKb).classOf .path).profile
#guard isP1 ((lowered appendKb).classOf .append).profile
-- Constructive NAF on a clause name: lowering guards `Y` with `D_all(Y)`,
-- which the NAF constrains without binding.
#guard isP1 ((lowered [fact (atom .isZero [k .zero]), rule (atom .p [v 0]) [naf (atom .isZero [v 1])]]).classOf .p).profile
-- A guard on a name no goal binds is a blocker: `p(X) :- q(Y)` lowered.
#guard missing ((lowered [fact (atom .q [k .a]), rule (atom .p [v 0]) [atom .q [k .a], atom .q [v 1]]]).classOf .p).profile ==
  [true, true]

end TabledAdmissionTests
