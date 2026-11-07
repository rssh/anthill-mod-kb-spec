# Left rules and compound clause heads

S09 adds the commands that use a selected assumption or a clause with a
compound head together with its continuation. It builds on the
[S06 positive execution](machine-positive.md) and the
[S08 proof checker](proof-checking.md). Each command is one step of the shared
machine. Its node is completed only after all its premises are proved, it
reconstructs `Derives` by existing rules, and it exports as S08 logical nodes.
Traces are in [Tests/Resolution/LeftRules.lean](../Tests/Resolution/LeftRules.lean).

| Module | Contents |
| --- | --- |
| [Machine/Evidence](../AnthillModKbSpec/Resolution/Machine/Evidence.lean) | `Derived`, the S09 commands with their parameters, and the machine rule `RuleApp.derived` |
| [Machine/LeftRules](../AnthillModKbSpec/Resolution/Machine/LeftRules.lean) | The command candidates (`Expansion.conjUse`, …) and their completion contracts read through the answers (`*_soundUnder`), the cut `Derives.cut`, conjuncts of a nested conjunction (`Term.component?`) |
| [Machine/LeftStrategy](../AnthillModKbSpec/Resolution/Machine/LeftStrategy.lean) | Choices and selections, the `left` strategy, `left_sound`, `left_reconstructs`; `leftCommitted`, which offers only the chosen commands where the selection chooses any (S12) |
| [P1/Derived](../AnthillModKbSpec/Resolution/P1/Derived.lean) | The logical nodes of each command (`Unfold.*`), their validity given valid premise trees (`Unfold.*_proves`), and `exportDerived` |
| [ProofLayer](../AnthillModKbSpec/Resolution/ProofLayer.lean) | Proof-layer capabilities beside P0 admission: `Request.proofLayer`, `diagnose`, `diagnose_not_ready` |

## Commands

A command is a candidate whose rule is `RuleApp.derived command`. Its premises
are exactly the obligations it leaves, in the order they run.

| Command | Selected | Premises, in order (added assumptions; opened names) | Reconstruction |
| --- | --- | --- | --- |
| `conjUse` | `A ∧ B` assumed | the goal (`A`, `B`) | a cut on `B` by `conjRight`, then on `A` by `conjLeft` |
| `disjCases` | `A ∨ B` assumed | the goal (`A`); the goal (`B`) | `disjElim` on the assumption |
| `existsOpen` | `∃x. A` assumed | the goal (`A[e/x]`; rigid `e`) | `existsElim` on the assumption |
| `forallUse` | `∀x₁…xₙ. A` assumed, witnesses `t₁…tₖ`, `k ≤ n` | the goal (the instance) | `forallElim` per witness, then a cut on the instance |
| `impUse` | `∀x̄. (A → B)` assumed, witnesses | the instance of `A`; the goal (the instance of `B`) | eliminations to `A' → B'`, `B'` by `impElim`, then a cut on `B'` |
| `headUse` | a clause `H :- body` | the renamed body; the goal (the renamed head) | the clause node for `H'`, then a cut on `H'` |
| `headProject` | a clause with a conjunctive head, a path | the renamed body, for a goal matched against the conjunct at the path | the clause node, then `conjLeft`/`conjRight` to the conjunct |
| `headDenial` | a clause with head `A → false` | the renamed body; the renamed `A`, for a goal reading as falsity | `impElim` on the clause node for `A' → false` |

A cut on `L` for the goal `C` is `impElim C [impIntro (L → C) [C under L], L]`,
in the original context (`Derives.cut`). So implication selection derives `B`
by implication elimination, discharges `B` from the continuation by
implication introduction, and applies implication elimination to obtain `C`.
No weakening is assumed, and no context-indexed NAF evidence is moved to
another context: the premise `A` is proved in the original context, and the
continuation is checked under exactly that context with `B` added.

Falsity elimination (`Expansion.falsityElim`, S04) is the contradiction
command: the goal by a proof of `false`. Logical negation `A → false` is an
implication. Assumed, it is a local rule concluding falsity (S06). As a clause
head it is conditional falsity: `headDenial` reads `¬A :- body` as
`false :- body, A`.

### Selections, readings, and scope

An assumption is selected as written in the scope, and the command is built
from its reading through the store at that point, which the node records.
Later stores read both alike (`Store.Scoped.read_refines`), so the read
assumption is an assumption of every later reading of the obligation. A command
therefore also uses an assumption written as a flexible name bound to a
formula.

- **Implication.** `impUse` proves `A` first, then makes `B` available.
  Assuming `A → B` runs nothing: `A` is a goal only once the implication is
  selected for some goal.
- **Disjunction.** `disjCases` gives two AND contexts with the same goal. The
  cases share answers in sequence, as AND siblings do. A premise's scope is
  computed from its parent's alone, so a case's assumption reaches neither the
  other case nor the parent.
- **Existential.** `existsOpen` opens the existential at a rigid name new to
  the store, in scope only in its premise. By the name invariant and
  `Store.commit_fresh_resolved` it is fresh for the read context, the read
  existential (an assumption of that context), and the read goal. A flexible
  name created outside the scope does not depend on it, so no answer or
  binding of such a name can mention it (`Store.commit_no_escape_resolved`). A
  premise outside the scope naming it is refused at the commit.
- **Universal.** `forallUse` and `impUse` instantiate only the leading binders
  they have witnesses for, by `Term.instantiateLeading`. That renames an inner
  binder that would capture a witness's names and keeps every captured
  parameter free. A witness is an explicit term, or a fresh flexible name that
  later matching may bind. The assumption stays in scope, so it can be used
  again with other witnesses. An explicit witness naming an undeclared or
  out-of-scope name is refused at the commit, a contract gap.
- **Compound heads.** A head is assumed only after its body is proved, by
  `headUse` or the split `headProject`. A disjunctive head is used by case
  analysis in the continuation, never by choosing a disjunct. A head `P → Q`
  is a local rule of the continuation, used as S06 uses one.

## The left strategy

`left hoApplySymbol program select` answers a focus as `positive` does and also
offers the commands an explicit `Selection` chooses there. A `Choice` names an
assumption as written, or a program clause, with the command's parameters. The
strategy checks it and builds the candidate:

- an assumption that is not the obligation's own, or reads with another
  shape, is a miss;
- so is a clause that is not the program's, witnesses past the leading
  binders, or a denial for a goal that does not read as falsity;
- a conjunct the matcher cannot compare with the goal is a gap.

S11 adds the choice `headMatch`: a clause selected by its whole head, matched
against the goal or against a view and converted, its body the one premise
([conversion](machine-conversion.md#whole-formula-selection)). `headProject`
compares its conjunct the same way. A head or conjunct that only a
lambda-valued answer could make the goal is a gap.

Fresh names avoid the store and the binder names read, as in S06.

The strategy differs from `positive` in three places:

- Compound assumptions are the left strategy's own. Where `positive` records a
  gap for an assumption from which the goal might follow by left rules
  (`mayConclude`), this strategy records none (`localAttempt` with
  `leftRules`) and offers what its selection chooses. A head that differs
  only by `ho_apply` is converted, as for `positive` (S11); a gap of the
  matcher stays a gap.
- A compound goal with no exact candidate is matched against assumptions with
  the same connective (`matchAttempts sameConnective`, the identity of
  `positive` with another filter), so an assumed `naf A` closes a matching
  goal with no new failure search. Exact candidates still close a goal alone.
- The chosen commands follow `positive`'s candidates as further OR
  alternatives (`atomResponse`'s `extra`). A waiting goal is `positive`'s, and
  the selection runs only where its commands are offered: at a concrete
  indirect call, whose one candidate is `ho_goal`, it runs at the direct form
  (S11).

The selection is a parameter, and the library defines no automatic one. Which
commands to try where is a search policy: an admitted P2 strategy (S15) will be
a checked plan, with its termination argument, interpreted into a `Selection`.
No ticket owns unadmitted automatic discovery, and complete propositional search
is deferred ([roadmap](resolution-implementation-plan.md)).

The traces use a heuristic selection, `relevant`, defined in the test file:

- it splits each compound assumption once per branch, unless its components,
  a disjunct, or an instance of the body are already present;
- it uses a universal or implication assumption whose non-atomic conclusion
  might conclude the goal, at fresh flexible witnesses, once per branch;
- it uses a compound head that might conclude the goal;
- it offers nothing for truth and conjunction goals, whose introductions lose
  nothing.

Traces that need explicit witnesses, falsity elimination, or a head used for a
goal it does not syntactically conclude add those choices to it. Nothing claims
that a search with it terminates.

## Proof trees

An S09 node exports as the logical nodes it stands for (`exportDerived`, called
by `exportTree`). Its parameters and goal are read through the final store,
and its subproofs are spliced in at their premises. The exported tree uses only
rules S08 already checks, each by its own procedure (`nodeCheck`), so no
`RuleCheck` is registered and no new rule is admitted. A node whose parameters
do not have its command's shape, such as a conjunct path the head does not
have, exports nothing.

`Unfold.*_proves` states that each construction is valid when its premise
trees are valid under the contexts the command gives them and its side
conditions hold:

| Construction | Side conditions | Premise trees |
| --- | --- | --- |
| `Unfold.cut` | — | the lemma under `Γ`; the goal under `L :: Γ` |
| `Unfold.conjUse` | `A ∧ B ∈ Γ` | the goal under `A :: B :: Γ` |
| `Unfold.disjCases` | `A ∨ B ∈ Γ` | the goal under `A :: Γ`; the goal under `B :: Γ` |
| `Unfold.existsOpen` | `∃x. A ∈ Γ`; `e` fresh for `Γ`, `∃x. A`, the goal; `O` is `A` opened at `e` | the goal under `O :: Γ` |
| `Unfold.forallUse` | the assumption is in `Γ`; the steps are eliminations to the instance (`Instances`) | the goal under the instance |
| `Unfold.impUse` | the assumption is in `Γ`; the steps lead to `A' → B'` | `A'` under `Γ`; the goal under `B' :: Γ` |
| `Unfold.headUse`, `Unfold.headProject`, `Unfold.headDenial` | the clause is in the snapshot, its instantiation gives the head and body instances; the conjunct at the path; the head `A' → false` | the body under `Γ`; the goal under `H' :: Γ`; `A'` under `Γ` |

`leadingSteps_instances` shows that the eliminations an exported `forallUse` or
`impUse` spells out are valid steps read through any store, and
`leadingSteps_last` that they end at `Term.instantiateLeading`'s instance.

## Proof-layer capabilities beside P0

P0 asks for evidence for every formula outside its classes (S07).
`Request.proofLayer` names the S09 commands that use a requested formula. A
compound assumption maps to its left rule, and a compound head to
`headProject`, `headDenial`, or `headUse`. A denial clause maps to
contradiction (`goalClause`, `falsityElim`), and a scoped goal to its
introduction rules. `diagnose` annotates P0's own answer.

A proof-layer capability is therefore reported only for an input that P0 does
not admit (`diagnose_not_ready`). Proofs built with these commands are checked
by the explicit-proof route, and the left strategy may try them, but neither
admits the formula for automatic execution. A proved formula enters execution
only through operational admission (`admitImports`, S08).

## Guarantees

| Property | Theorem |
| --- | --- |
| Each command's completion contract, read through the answers, by `Derives` rules | `Expansion.conjUse_soundUnder`, `disjCases_soundUnder`, `existsOpen_soundUnder`, `forallUse_soundUnder`, `impUse_soundUnder`, `headUse_soundUnder`, `headProject_soundUnder`, `headDenial_soundUnder` |
| Every chosen command is sound, whatever the selection | `Choice.attempt_sound` |
| The left strategy is sound for its program's KB, whatever the NAF provider | `left_sound` |
| A successful run reconstructs `Derives` for its answer instance | `left_reconstructs` |
| The same for the left strategy committed to its selection | `leftCommitted_sound`, `leftCommitted_reconstructs` |
| Each construction is valid given valid premise trees under the command's contexts | `Unfold.cut_proves`, `conjUse_proves`, `disjCases_proves`, `existsOpen_proves`, `forallUse_proves`, `impUse_proves`, `headUse_proves`, `headProject_proves`, `headDenial_proves` |
| Exported eliminations are valid steps through any store | `leadingSteps_instances`, `leadingSteps_last` |
| A proof-layer capability is reported only for an input P0 does not admit | `diagnose_requests`, `diagnose_not_ready` |

Scope, rollback, answer sharing, and witness non-escape are the machine's own
guarantees (`step_valid`, `Store.commit_no_escape_resolved`; see
[S04](machine-state.md)), and hold for every strategy.

## Traces

| Trace | Result |
| --- | --- |
| `q → (p ∧ s)` and the fact `q`, goal `s` | `impUse`: the first focus is `q` under the original scope; then `p ∧ s` is split. Exported as `impElim(impIntro(…), impElim(assumption, …))`, accepted, logical nodes only |
| The same without the fact `q`; `(q → p) → r` with the looping `q :- q` | Exhausted; exhausted without focusing `q` |
| `∀1. (q(1) → (p(1) ∨ s(1)))`, `q(a)`, `∀2. (s(2) → p(2))`, goal `p(a)` | Success; the fresh witness reads as `a` |
| R12: `q`, `q → (s ∨ p)`, goal `p`; with `s → p` | Exhausted, `s` and `p` never asserted together; success with both cases |
| `q → ho_apply(p, a)`, `q`, goal `p(a)` | The local rule's conclusion matched against the goal's indirect view and converted (S11); accepted; resuming is exhausted |
| `p ∧ q`, goal `r` | Exhausted |
| `q ∨ p` under `p ∨ q` | `disjCases`, each case adding exactly its disjunct; exported as `disjElim`, accepted |
| `p(X)` under `p(a) ∨ p(b)`; under `p(a) ∨ q(a)`, `∀1. (q(1) → p(1))` | Exhausted (incompatible answers); answer `a`, resuming exhausted |
| `(q ∨ p) ∧ p` under `p ∨ q` | Exhausted: no branch assumption leaks |
| `p ∨ q`, `p → false`, goal `q`, falsity elimination chosen for `q` under `p` | Success, the first case by contradiction |
| `q ∨ p` under `p ∨ q` with no command selected | Exhausted, although the goal is proved above |
| `∃2. p(2)` under `∃1. p(1)` | `existsOpen`, then the goal's witness inside its scope; the eigenvariable is fresh for context, existential, and goal |
| Root answer `p(X)` under `∃1. p(1)`; `∃2. ((∃1. p(1)) → p(2))` | Exhausted: the witness escapes neither through an answer nor through an earlier name |
| R11: `∃2. naf p(2)` under `∃1. naf p(1)` | Success by identity on the opened negative assumption, no NAF node |
| `∀1. ∀2. (p(1, 2) ∨ q(1, 2))` at `1 := 2` (a parameter), `2 := c`, goal `r(2)` | The inner binder is renamed: the instance is `p(2, c) ∨ q(2, c)`; success |
| The same for `r(c)`, with `2` declared; with `2` undeclared | Exhausted; a contract gap |
| `∀1. (p(1) ∨ q(7))` at `a`, with `q(7) → s` / `q(8) → s` | Success / exhausted: the captured `7` is kept |
| `∀1. ∀2. (p(1) ∨ q(2))` at `1 := a` | The instance `∀2. (p(a) ∨ q(2))` is still universal; an assumption outside the scope is a miss |
| `∀1. (p(1) ∨ q(1))` for `r(a) ∧ r(b)` | Two `forallUse` nodes, at `a` and at `b` |
| `p(X) ∧ q(X) :- r(X)`, `r(a)`, goal `q(a)` / `p(a)` / `q(b)` | `headProject` to the right / left conjunct; exhausted |
| `p ∨ q :- r`, `r`, `p → s`, `q → s`, goal `s`, the head chosen for `s` | `headUse` then `disjCases`; without `q → s` / without `r`: exhausted |
| `p → q :- r`, `r`, `p`, goal `q`; without `r` | `headUse` then the head as a local rule; exhausted |
| `¬p(X) :- r(X)`, `r(a)`, `p(a)`, goal `false` / `t` (falsity elimination chosen); without `p(a)` | `headDenial` / falsity elimination then `headDenial`; exhausted |
| `∃1. p(1) :- r`, `r`, goal `∃2. p(2)`, the head chosen | `headUse` then `existsOpen` |
| `p → false`, `p`, goal `q`, falsity elimination chosen | Falsity elimination; `positive` alone is exhausted |
| Hand-built constructions | Accepted; rejected when the implication's argument uses its conclusion, when a case uses the other case's assumption, when the eigenvariable occurs in the context, the existential, or the goal, and for a capturing instance |
| Diagnoses | `p ∨ q` assumed: `disjCases`; `q → (p ∧ s)`: `impUse`; `∃1. p(1)`: `existsOpen`; head `p ∧ q`: `headProject`, `headUse`; head `p → false`: `headDenial`, `headUse`; a denial clause: contradiction; a scoped goal: introduction; a P0 input: nothing |

## Boundaries

- **Export of whole runs is not proved here.** The constructions are checked
  given checked premise trees and their side conditions. The theorem that
  every successful run of the left strategy, or of any S06/P2 strategy,
  exports an accepted tree belongs to S15/S16. That theorem includes reading
  each node's side conditions through the final store across the whole run.
  The P0 case is S08's `Plan.exportProof_checked`.
- **No termination or completeness.** The library has no automatic
  selection; the left strategy runs what its selection chooses. A recursive
  body, or a selection that chooses the same command again, can make a run
  loop, and such a run is interrupted. `exhausted` is relative to the strategy
  and its selection: a failed command attempt establishes no negation, no NAF
  evidence, and no non-derivability.
- **Matching.** Compound goals and conjuncts are compared by the S05 matcher,
  which compares binders only when identical. Comparing alpha-variants is
  still a gap.
- **Capabilities owned by other tickets.** Scoped and evidence-first NAF are
  S10's ([machine-negation](machine-negation.md)): here an assumed `naf A` is
  used only by identity. `ho_apply` conversion and the whole-formula choice
  `headMatch` are S11's ([conversion](machine-conversion.md)), and equality
  and dictionary laws are S14's.
