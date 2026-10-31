import AnthillModKbSpec.Resolution.P1.Tree

/-! # Proof trees as terms, references, and `CheckedProof` (S08)

A supplied proof is an ordinary `Term`. Each structural position uses one
symbol of a `Vocabulary`, all distinct; formulas, witnesses, and evidence are
embedded as they are, at positions the decoder knows, so a formula that uses a
vocabulary symbol is not misread:

| Shape | Term |
| --- | --- |
| node | `node(rule, conclusion, list(premise₁, …))` |
| rule | `r(parameters…)` with one tag `r` per rule |
| eigenvariable, name | `x` (a variable) |
| clause `H :- B₁…Bₙ` / `:- B₁…Bₙ` | `definite(H, B₁, …, Bₙ)` / `goal(B₁, …, Bₙ)` |
| instantiation | `list(pair(x₁, t₁), …)` |
| derived rule `s`, reference `s` | `extension(s(), list(p₁, …))`, `reference(s())` |

`decode` reads exactly what `encode` writes (`decode_encode`); a term of
another shape decodes to nothing and is rejected.

References name earlier proofs in an import table, newest first. A reference
is re-checked where it is used, against the imports older than the one it
names, so the referenced proof meets the scope conditions of its use site and
no proof can justify itself. `CheckedProof` is the judgment; `checkProof`
decides it (`checkProof_accept_iff`), reports missing capabilities first, and
an accepted proof reconstructs `Derives` (`checked_toDerives`). -/

namespace AnthillModKbSpec.P1

open Machine

variable {Variable Literal Symbol : Type}

/-- The structural positions of the encoding: tree shapes and rules, the
checked membership rule, and the shapes of P0 success and failure witnesses,
which NAF evidence uses. -/
inductive Tag where
  | node | list | pair | definite | goal
  | assumption | truth | conjIntro | conjLeft | conjRight | disjLeft | disjRight | disjElim | impIntro | impElim
  | falsityElim | forallIntro | forallElim | existsIntro | existsElim | clause | goalClause | defaultNegIntro
  | hoApplyIntro | hoApplyElim | equalRefl | equalSymm | equalTrans | equalSubst | extension | reference
  | membership
  | assumed | byClause | trivially | both | refutes
  | failsAtom | failsFalsity | failsLeft | failsRight | failsNegation
  deriving DecidableEq, Repr

def Tag.all : List Tag :=
  [.node, .list, .pair, .definite, .goal, .assumption, .truth, .conjIntro, .conjLeft, .conjRight, .disjLeft,
    .disjRight, .disjElim, .impIntro, .impElim, .falsityElim, .forallIntro, .forallElim, .existsIntro, .existsElim,
    .clause, .goalClause, .defaultNegIntro, .hoApplyIntro, .hoApplyElim, .equalRefl, .equalSymm, .equalTrans,
    .equalSubst, .extension, .reference, .membership, .assumed, .byClause, .trivially, .both, .refutes, .failsAtom,
    .failsFalsity, .failsLeft, .failsRight, .failsNegation]

theorem Tag.mem_all (tag : Tag) : tag ∈ Tag.all := by cases tag <;> simp [Tag.all]

/-- The symbols of the encoding, one per tag and all distinct. -/
structure Vocabulary (Symbol : Type) where
  symbol : Tag → Symbol
  injective : ∀ first second, symbol first = symbol second → first = second

section Encoding

variable (vocab : Vocabulary Symbol)

def encodeClause : HornClause Variable Literal Symbol → Term Variable Literal Symbol
  | .definite head body => .app (vocab.symbol .definite) (head :: body)
  | .goal body => .app (vocab.symbol .goal) body

def encodePair (pair : Variable × Term Variable Literal Symbol) : Term Variable Literal Symbol :=
  .app (vocab.symbol .pair) [.var pair.1, pair.2]

def encodeRule : Rule Variable Literal Symbol → Term Variable Literal Symbol
  | .assumption => .app (vocab.symbol .assumption) []
  | .truth => .app (vocab.symbol .truth) []
  | .conjIntro => .app (vocab.symbol .conjIntro) []
  | .conjLeft => .app (vocab.symbol .conjLeft) []
  | .conjRight => .app (vocab.symbol .conjRight) []
  | .disjLeft => .app (vocab.symbol .disjLeft) []
  | .disjRight => .app (vocab.symbol .disjRight) []
  | .disjElim => .app (vocab.symbol .disjElim) []
  | .impIntro => .app (vocab.symbol .impIntro) []
  | .impElim => .app (vocab.symbol .impElim) []
  | .falsityElim => .app (vocab.symbol .falsityElim) []
  | .forallIntro eigen => .app (vocab.symbol .forallIntro) [.var eigen]
  | .forallElim witness => .app (vocab.symbol .forallElim) [witness]
  | .existsIntro witness => .app (vocab.symbol .existsIntro) [witness]
  | .existsElim eigen opened => .app (vocab.symbol .existsElim) [.var eigen, opened]
  | .clause clause instantiation =>
      .app (vocab.symbol .clause) [encodeClause vocab clause, .app (vocab.symbol .list) (instantiation.map (encodePair vocab))]
  | .goalClause clause instantiation =>
      .app (vocab.symbol .goalClause)
        [encodeClause vocab clause, .app (vocab.symbol .list) (instantiation.map (encodePair vocab))]
  | .defaultNegIntro evidence => .app (vocab.symbol .defaultNegIntro) [evidence]
  | .hoApplyIntro => .app (vocab.symbol .hoApplyIntro) []
  | .hoApplyElim => .app (vocab.symbol .hoApplyElim) []
  | .equalRefl => .app (vocab.symbol .equalRefl) []
  | .equalSymm => .app (vocab.symbol .equalSymm) []
  | .equalTrans => .app (vocab.symbol .equalTrans) []
  | .equalSubst name template => .app (vocab.symbol .equalSubst) [.var name, template]
  | .extension name parameters => .app (vocab.symbol .extension) [.app name [], .app (vocab.symbol .list) parameters]
  | .reference name => .app (vocab.symbol .reference) [.app name []]

mutual
/-- A proof tree as a term. -/
def encode : Proof Variable Literal Symbol → Term Variable Literal Symbol
  | .node rule conclusion premises =>
      .app (vocab.symbol .node) [encodeRule vocab rule, conclusion, .app (vocab.symbol .list) (encodeAll premises)]

def encodeAll : List (Proof Variable Literal Symbol) → List (Term Variable Literal Symbol)
  | [] => []
  | proof :: rest => encode proof :: encodeAll rest
end

variable [DecidableEq Symbol]

/-- The tag a symbol stands for, if any. -/
def Vocabulary.tag? (symbol : Symbol) : Option Tag := Tag.all.find? fun tag => decide (vocab.symbol tag = symbol)

theorem Vocabulary.tag?_symbol (tag : Tag) : vocab.tag? (vocab.symbol tag) = some tag := by
  unfold Vocabulary.tag?
  cases found : Tag.all.find? fun other => decide (vocab.symbol other = vocab.symbol tag) with
  | none =>
      have := List.find?_eq_none.mp found tag (Tag.mem_all tag)
      simp at this
  | some other =>
      have := List.find?_some found
      simp only [decide_eq_true_eq] at this
      rw [vocab.injective _ _ this]

def decodeClause : Term Variable Literal Symbol → Option (HornClause Variable Literal Symbol)
  | .app symbol args =>
      if symbol = vocab.symbol .definite then
        match args with
        | head :: body => some (.definite head body)
        | [] => none
      else if symbol = vocab.symbol .goal then some (.goal args) else none
  | _ => none

def decodePair : Term Variable Literal Symbol → Option (Variable × Term Variable Literal Symbol)
  | .app symbol [.var name, value] => if symbol = vocab.symbol .pair then some (name, value) else none
  | _ => none

def decodeList : Term Variable Literal Symbol → Option (List (Term Variable Literal Symbol))
  | .app symbol items => if symbol = vocab.symbol .list then some items else none
  | _ => none

/-- A clause rule's parameters: the clause and its instantiation. -/
def decodeInstance (clause pairs : Term Variable Literal Symbol) :
    Option (HornClause Variable Literal Symbol × List (Variable × Term Variable Literal Symbol)) := do
  let decoded ← decodeClause vocab clause
  let items ← decodeList vocab pairs
  let instantiation ← items.mapM (decodePair vocab)
  pure (decoded, instantiation)

def decodeRule : Term Variable Literal Symbol → Option (Rule Variable Literal Symbol)
  | .app symbol parameters =>
      match vocab.tag? symbol, parameters with
      | some .assumption, [] => some .assumption
      | some .truth, [] => some .truth
      | some .conjIntro, [] => some .conjIntro
      | some .conjLeft, [] => some .conjLeft
      | some .conjRight, [] => some .conjRight
      | some .disjLeft, [] => some .disjLeft
      | some .disjRight, [] => some .disjRight
      | some .disjElim, [] => some .disjElim
      | some .impIntro, [] => some .impIntro
      | some .impElim, [] => some .impElim
      | some .falsityElim, [] => some .falsityElim
      | some .forallIntro, [.var eigen] => some (.forallIntro eigen)
      | some .forallElim, [witness] => some (.forallElim witness)
      | some .existsIntro, [witness] => some (.existsIntro witness)
      | some .existsElim, [.var eigen, opened] => some (.existsElim eigen opened)
      | some .clause, [clause, pairs] => (decodeInstance vocab clause pairs).map fun found => .clause found.1 found.2
      | some .goalClause, [clause, pairs] =>
          (decodeInstance vocab clause pairs).map fun found => .goalClause found.1 found.2
      | some .defaultNegIntro, [evidence] => some (.defaultNegIntro evidence)
      | some .hoApplyIntro, [] => some .hoApplyIntro
      | some .hoApplyElim, [] => some .hoApplyElim
      | some .equalRefl, [] => some .equalRefl
      | some .equalSymm, [] => some .equalSymm
      | some .equalTrans, [] => some .equalTrans
      | some .equalSubst, [.var name, template] => some (.equalSubst name template)
      | some .extension, [.app name [], items] => (decodeList vocab items).map (.extension name)
      | some .reference, [.app name []] => some (.reference name)
      | _, _ => none
  | _ => none

mutual
/-- Read a term as a proof tree; other shapes decode to nothing. -/
def decode : Term Variable Literal Symbol → Option (Proof Variable Literal Symbol)
  | .app symbol [rule, conclusion, .app list premises] =>
      if symbol = vocab.symbol .node ∧ list = vocab.symbol .list then
        match decodeRule vocab rule, decodeAll premises with
        | some decoded, some subproofs => some (.node decoded conclusion subproofs)
        | _, _ => none
      else none
  | _ => none

def decodeAll : List (Term Variable Literal Symbol) → Option (List (Proof Variable Literal Symbol))
  | [] => some []
  | term :: rest =>
      match decode term, decodeAll rest with
      | some proof, some proofs => some (proof :: proofs)
      | _, _ => none
end

theorem decodeClause_encodeClause (clause : HornClause Variable Literal Symbol) :
    decodeClause vocab (encodeClause vocab clause) = some clause := by
  cases clause with
  | definite head body => simp [encodeClause, decodeClause]
  | goal body =>
      have different : vocab.symbol .goal ≠ vocab.symbol .definite := fun same => by
        cases vocab.injective _ _ same
      simp [encodeClause, decodeClause, different]

theorem decodePairs_encodePairs (instantiation : List (Variable × Term Variable Literal Symbol)) :
    instantiation.mapM (decodePair vocab ∘ encodePair vocab) = some instantiation := by
  induction instantiation with
  | nil => rfl
  | cons pair rest ih => simp [encodePair, decodePair, ih]

theorem decodeRule_encodeRule (rule : Rule Variable Literal Symbol) :
    decodeRule vocab (encodeRule vocab rule) = some rule := by
  cases rule <;>
    simp [encodeRule, decodeRule, Vocabulary.tag?_symbol, decodeInstance, decodeClause_encodeClause, decodeList,
      decodePairs_encodePairs]

mutual
/-- `decode_encode`: decoding reads back exactly the encoded tree. -/
theorem decode_encode : ∀ proof : Proof Variable Literal Symbol, decode vocab (encode vocab proof) = some proof
  | .node rule conclusion premises => by
      simp [encode, decode, decodeRule_encodeRule, decodeAll_encodeAll premises]

theorem decodeAll_encodeAll : ∀ proofs : List (Proof Variable Literal Symbol),
    decodeAll vocab (encodeAll vocab proofs) = some proofs
  | [] => rfl
  | proof :: rest => by simp [encodeAll, decodeAll, decode_encode proof, decodeAll_encodeAll rest]
end

end Encoding

/-! ## References and checked proofs -/

/-- A previously supplied proof that later proofs may reference by name: the
statement it was supplied for and its term. -/
structure Import (Variable Literal Symbol : Type) where
  name : Symbol
  context : ProofContext Variable Literal Symbol
  goal : Formula Variable Literal Symbol
  proof : Term Variable Literal Symbol

section Checked

variable [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol]
  (vocab : Vocabulary Symbol) (checker : Checker Variable Literal Symbol)

attribute [local instance] termEq

/-- A reference to `name` holds for a goal under a context when the newest
import with that name was stated for that goal, under assumptions the context
has, and its proof proves the goal there, checked against the imports older
than it. -/
def Resolves : List (Import Variable Literal Symbol) → Symbol → ProofContext Variable Literal Symbol →
    Formula Variable Literal Symbol → Prop
  | [], _, _, _ => False
  | entry :: older, name, context, goal =>
      if entry.name = name then
        entry.goal = goal ∧ (∀ assumption ∈ entry.context, assumption ∈ context) ∧
          ∃ tree, decode vocab entry.proof = some tree ∧ tree.conclusion = goal ∧
            Valid checker (Resolves older) context tree
      else Resolves older name context goal

/-- Decide `Resolves`. -/
def resolve : List (Import Variable Literal Symbol) → Symbol → ProofContext Variable Literal Symbol →
    Formula Variable Literal Symbol → Bool
  | [], _, _, _ => false
  | entry :: older, name, context, goal =>
      if entry.name = name then
        decide (entry.goal = goal) && entry.context.all (fun assumption => decide (assumption ∈ context)) &&
          match decode vocab entry.proof with
          | some tree => decide (tree.conclusion = goal) && check checker (resolve older) context tree
          | none => false
      else resolve older name context goal

theorem resolve_iff : ∀ (imports : List (Import Variable Literal Symbol)) name context goal,
    resolve vocab checker imports name context goal = true ↔ Resolves vocab checker imports name context goal
  | [], _, _, _ => by simp [resolve, Resolves]
  | entry :: older, name, context, goal => by
      unfold resolve Resolves
      by_cases same : entry.name = name
      · simp only [same, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
        cases decoded : decode vocab entry.proof with
        | none => simp
        | some tree =>
            simp only [Bool.and_eq_true, decide_eq_true_eq, Option.some.injEq, exists_eq_left', and_assoc]
            rw [check_iff (resolve_iff older)]
      · simp only [same, ↓reduceIte]
        exact resolve_iff older name context goal

omit [DecidableEq Literal] in
/-- A resolved reference is derivable where it is used. -/
theorem Resolves.derives : ∀ {imports : List (Import Variable Literal Symbol)} {name context goal},
    Resolves vocab checker imports name context goal →
      Derives checker.snapshot.hoApplySymbol checker.snapshot.kb context goal checker.provider
  | [], _, _, _, resolved => by simp [Resolves] at resolved
  | entry :: older, name, context, goal, resolved => by
      unfold Resolves at resolved
      split at resolved
      · obtain ⟨_, _, tree, _, proves, valid⟩ := resolved
        rw [← proves]
        exact valid.derives fun _ _ _ inner => Resolves.derives inner
      · exact Resolves.derives resolved

/-- What one use of a capability needs, through the import table. A
reference to a proof in the table needs what that proof needs; one to a name
the table lacks needs the proof; a malformed import needs nothing and is
rejected when checked. -/
def expand : List (Import Variable Literal Symbol) → Capability Symbol → List (Capability Symbol)
  | _, .negation => if checker.negation.isSome then [] else [.negation]
  | _, .rule name => if (checker.rule? name).isSome then [] else [.rule name]
  | [], .lemma name => [.lemma name]
  | entry :: older, .lemma name =>
      if entry.name = name then
        match decode vocab entry.proof with
        | some tree => tree.requires.flatMap (expand older)
        | none => []
      else expand older (.lemma name)

/-- The capabilities a tree needs that the checker and the import table lack,
through its references, each once. -/
def missing (imports : List (Import Variable Literal Symbol)) (tree : Proof Variable Literal Symbol) :
    List (Capability Symbol) :=
  (tree.requires.flatMap (expand vocab checker imports)).eraseDups

omit [DecidableEq Literal] in
/-- A resolved reference needs nothing the checker or the table lacks. -/
theorem expand_lemma_nil : ∀ (imports : List (Import Variable Literal Symbol)) {name context goal},
    Resolves vocab checker imports name context goal → expand vocab checker imports (.lemma name) = []
  | [], _, _, _, resolved => by simp [Resolves] at resolved
  | entry :: older, name, context, goal, resolved => by
      unfold Resolves at resolved
      unfold expand
      by_cases same : entry.name = name
      · simp only [same, ↓reduceIte] at resolved ⊢
        obtain ⟨_, _, tree, decoded, _, valid⟩ := resolved
        simp only [decoded]
        refine List.flatMap_eq_nil_iff.mpr fun capability member => ?_
        rcases valid.uses capability member with ⟨rfl, present⟩ | ⟨rule, rfl, present⟩ |
          ⟨inner, innerContext, innerGoal, rfl, innerResolved⟩
        · cases older <;> simp [expand, present]
        · cases older <;> simp [expand, present]
        · exact expand_lemma_nil older innerResolved
      · simp only [same, ↓reduceIte] at resolved ⊢
        exact expand_lemma_nil older resolved

omit [DecidableEq Literal] in
/-- A valid tree, with references resolved over the table, needs nothing the
checker or the table lacks. -/
theorem Valid.missing_nil {imports : List (Import Variable Literal Symbol)} {context : ProofContext Variable Literal Symbol}
    {tree : Proof Variable Literal Symbol} (valid : Valid checker (Resolves vocab checker imports) context tree) :
    missing vocab checker imports tree = [] := by
  have none : tree.requires.flatMap (expand vocab checker imports) = [] := by
    refine List.flatMap_eq_nil_iff.mpr fun capability member => ?_
    rcases valid.uses capability member with ⟨rfl, present⟩ | ⟨rule, rfl, present⟩ | ⟨name, _, _, rfl, resolved⟩
    · cases imports <;> simp [expand, present]
    · cases imports <;> simp [expand, present]
    · exact expand_lemma_nil vocab checker imports resolved
  simp only [missing, none]
  rfl

/-- `CheckedProof(snapshot, context, goal, proof)`: the term decodes to a tree
whose conclusion is the goal and which is valid under the context, against the
checker and the import table. -/
def CheckedProof (imports : List (Import Variable Literal Symbol)) (context : ProofContext Variable Literal Symbol)
    (goal : Formula Variable Literal Symbol) (proof : Term Variable Literal Symbol) : Prop :=
  ∃ tree, decode vocab proof = some tree ∧ tree.conclusion = goal ∧
    Valid checker (Resolves vocab checker imports) context tree

/-- What checking a supplied proof answers. `reject` concerns this proof only:
it is no evidence about the goal. -/
inductive Verdict (Symbol : Type) where
  | accept
  | reject
  /-- The tree uses capabilities the checker lacks: an evidence check, a
  derived rule, or a referenced proof. -/
  | needsEvidence (missing : List (Capability Symbol))
  deriving DecidableEq, Repr

/-- Check a supplied proof term: decode it, compare its conclusion with the
goal, report the capabilities it needs that are missing, then check the tree.
Nothing is searched. -/
def checkProof (imports : List (Import Variable Literal Symbol)) (context : ProofContext Variable Literal Symbol)
    (goal : Formula Variable Literal Symbol) (proof : Term Variable Literal Symbol) : Verdict Symbol :=
  match decode vocab proof with
  | none => .reject
  | some tree =>
      if tree.conclusion = goal then
        match missing vocab checker imports tree with
        | [] => if check checker (resolve vocab checker imports) context tree = true then .accept else .reject
        | first :: rest => .needsEvidence (first :: rest)
      else .reject

/-- `checkProof_accept_iff`: a proof is accepted exactly when it is checked. -/
theorem checkProof_accept_iff {imports : List (Import Variable Literal Symbol)}
    {context : ProofContext Variable Literal Symbol} {goal : Formula Variable Literal Symbol}
    {proof : Term Variable Literal Symbol} :
    checkProof vocab checker imports context goal proof = .accept ↔ CheckedProof vocab checker imports context goal proof := by
  unfold checkProof CheckedProof
  constructor
  · intro accepted
    split at accepted
    · cases accepted
    · rename_i tree decoded
      split at accepted
      · rename_i proves
        split at accepted
        · split at accepted
          · rename_i checked
            exact ⟨tree, decoded, proves, (check_iff (resolve_iff vocab checker imports)).mp checked⟩
          · cases accepted
        · cases accepted
      · cases accepted
  · rintro ⟨tree, decoded, proves, valid⟩
    rw [decoded]
    simp only [proves, ↓reduceIte]
    rw [valid.missing_nil vocab checker]
    simp only [(check_iff (resolve_iff vocab checker imports)).mpr valid, ↓reduceIte]

omit [DecidableEq Literal] in
/-- `checked_toDerives`: a checked proof reconstructs `Derives` for exactly the
checker's application symbol, KB, and NAF provider, under the context it was
checked for. -/
theorem checked_toDerives {imports : List (Import Variable Literal Symbol)}
    {context : ProofContext Variable Literal Symbol} {goal : Formula Variable Literal Symbol}
    {proof : Term Variable Literal Symbol} (checked : CheckedProof vocab checker imports context goal proof) :
    Derives checker.snapshot.hoApplySymbol checker.snapshot.kb context goal checker.provider := by
  obtain ⟨tree, _, proves, valid⟩ := checked
  rw [← proves]
  exact valid.derives fun _ _ _ resolved => resolved.derives vocab checker

/-- A needs-evidence verdict is for a tree of the stated goal, and lists the
capabilities it needs that are missing; it is decided before the tree is
checked. -/
theorem checkProof_needsEvidence {imports : List (Import Variable Literal Symbol)}
    {context : ProofContext Variable Literal Symbol} {goal : Formula Variable Literal Symbol}
    {proof : Term Variable Literal Symbol} {needed : List (Capability Symbol)}
    (needs : checkProof vocab checker imports context goal proof = .needsEvidence needed) :
    ∃ tree, decode vocab proof = some tree ∧ tree.conclusion = goal ∧ needed = missing vocab checker imports tree ∧
      needed ≠ [] := by
  unfold checkProof at needs
  split at needs
  · cases needs
  · rename_i tree decoded
    split at needs
    · rename_i proves
      split at needs
      · split at needs <;> cases needs
      · rename_i first rest found
        cases needs
        exact ⟨tree, decoded, proves, found.symm, List.cons_ne_nil _ _⟩
    · cases needs

end Checked

end AnthillModKbSpec.P1
