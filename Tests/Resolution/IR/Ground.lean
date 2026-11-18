import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Machine AnthillModKbSpec.Admission AnthillModKbSpec.InductiveDomains
  AnthillModKbSpec.AdmissionSignature

namespace IRGroundTests

/-! Executable traces of S27: S07's ground programs in the IR. S07's
admission builds a `P0.Ground`; where the IR keeps its meaning it embeds
(`IR.embedGround`), classifies P0 (`IR.embedGround_p0`), and has its relevant
program computed. The setup is S07's (`Tests/Resolution/P0/Admission.lean`). -/

inductive Sym where
  | p | q | r | s | w | a | b | c | zero | succ | isNat | allData | isPred | call | ha
  deriving DecidableEq, Repr

abbrev T := Term Nat Nat Sym
abbrev Clause := HornClause Nat Nat Sym

def k (symbol : Sym) : T := .app symbol []
def atom (symbol : Sym) (args : List T) : T := .app symbol args
def fact (head : T) : Clause := .definite head []
def rule (head : T) (body : List T) : Clause := .definite head body
def naf (goal : T) : T := .defaultNeg goal

inductive Dom where
  | nat
  deriving DecidableEq, Repr

def zeroRule : Rule Dom Sym := ⟨.nat, .zero, []⟩
def succRule : Rule Dom Sym := ⟨.nat, .succ, [.nat]⟩
def family : FiniteFamily Dom Sym := ⟨fun rule => rule = zeroRule ∨ rule = succRule, [.nat], fun domain => by cases domain; simp⟩

def snapshot : SignatureSnapshot Dom Sym := ⟨0, ⟨family, fun _ => .isNat, .allData, fun _ => .isPred, [⟨.p, 1⟩]⟩⟩
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

def kb (clauses : List Clause) : Program Nat Nat Sym :=
  ⟨clauses.mapIdx (fun index clause => ⟨.lowered index, clause⟩) ++
    (signatureClauses snapshot names rules).map (⟨.signature, ·⟩), guardSymbol snapshot⟩

def input (clauses : List Clause) (context : List T) (goal : T) : Input Dom Nat Nat Sym :=
  ⟨snapshot, names, rules, listed, complete, distinct, kb clauses, fun _ => guardSymbol_iff, context, goal⟩

/-- The embedding of a ground input S07's admission answers Ready for, with
`q` the unknown marker when `marked`: P0, and its relevant program's calls and
instances, when it embeds. -/
def irProfile (query : Input Dom Nat Nat Sym) (marked : Bool := false) : Option (Bool × Option (Nat × Nat)) :=
  match check .ha query with
  | .ready plan =>
      (IR.embedGround plan.ground (fun symbol => marked && symbol == .q)).map fun (program, goals) =>
        let isP0 := match program.classify goals with
          | .p0 => true
          | _ => false
        (isP0, (program.relevantProgram goals 50).map fun computed => (computed.calls.length, computed.instances.length))
  | _ => none

/- `p(a) :- q(a), naf r(a). q(a).`, the goal `p(a)`: Ready in S07, P0 in the
IR; the calls `p(a)`, `q(a)`, `r(a)`, and two instances. -/
#guard irProfile (input [rule (atom .p [k .a]) [atom .q [k .a], naf (atom .r [k .a])], fact (atom .q [k .a])] []
  (atom .p [k .a])) == some (true, some (3, 2))

/- S07 ranks atoms: `p(a) :- p(b). p(b).` is Ready and P0. -/
#guard irProfile (input [rule (atom .p [k .a]) [atom .p [k .b]], fact (atom .p [k .b])] [] (atom .p [k .a])) ==
  some (true, some (2, 2))

/- A context atom becomes a fact: `p(a) :- q(a).` under the assumption
`q(a)`. -/
#guard irProfile (input [rule (atom .p [k .a]) [atom .q [k .a]]] [atom .q [k .a]] (atom .p [k .a])) == some (true, some (2, 2))

/- A conjunctive goal flattens: `q(a) ∧ ¬r(a)`. -/
#guard irProfile (input [fact (atom .q [k .a])] [] (.conj (atom .q [k .a]) (naf (atom .r [k .a])))) == some (true, some (2, 1))

/- No embedding where the IR would change the meaning: `falsity` in a body,
NAF of a compound goal, the unknown marker `q` (S07 reads it closed, the IR's
markers are free), and `p` at two arities (IR declarations are keyed by
symbol). Each is Ready in S07. -/
#guard irProfile (input [rule (atom .p [k .a]) [.falsity]] [] (atom .p [k .a])) == none
#guard irProfile (input [rule (atom .p [k .a]) [naf (.conj (atom .q [k .a]) (atom .r [k .a]))], fact (atom .q [k .a])] []
  (atom .p [k .a])) == none
#guard irProfile (input [rule (k .p) [k .q]] [] (naf (k .p))) true == none
#guard irProfile (input [rule (k .p) [k .q]] [] (naf (k .p))) == some (true, some (2, 1))
#guard irProfile (input [rule (atom .p [k .a]) [atom .p [k .a, k .b]], fact (atom .p [k .a, k .b])] [] (atom .p [k .a])) == none

end IRGroundTests
