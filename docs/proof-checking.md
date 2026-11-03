# P1 proof checking and proof imports

S08 implements the explicit-proof route of the
[admission contract](lean-admission-contract.md#explicit-proof-a-proof-tree-in-the-shared-logic).
A proof is a finite tree in the shared logic, supplied as an ordinary `Term`.
The checker decides whether the tree is valid, with a known terminating
procedure for each rule application. An accepted tree reconstructs `Derives`
for exactly the checker's application symbol, KB, context, and NAF provider.
A tree is checked the same way whether it was built by hand, produced
externally, or exported from a machine run. Traces are in
[Tests/Resolution/P1/Check.lean](../Tests/Resolution/P1/Check.lean).

| Module | Contents |
| --- | --- |
| [P1/Substitutes](../AnthillModKbSpec/Resolution/P1/Substitutes.lean) | Deciding capture-avoiding substitution with a stated result (`substitutes_iff`) |
| [P1/Tree](../AnthillModKbSpec/Resolution/P1/Tree.lean) | Rules and trees, the checker's interfaces (`NafCheck`, `RuleCheck`, `Checker`), rule applications (`Local`), tree validity (`Valid`), the checker (`nodeCheck`, `check`, `check_iff`), reconstruction (`Valid.derives`), the capabilities a tree uses (`Valid.uses`) |
| [P1/Encoding](../AnthillModKbSpec/Resolution/P1/Encoding.lean) | The `Term` encoding (`encode`, `decode`, `decode_encode`), references over an import table (`Resolves`), missing capabilities through references (`missing`), `CheckedProof`, `checkProof`, `checkProof_accept_iff`, `checked_toDerives` |
| [P1/Decision](../AnthillModKbSpec/Resolution/P1/Decision.lean) | `DecisionContract` and proof checking as one (`proofRoute`, `reject_says_nothing`) |
| [P1/Export](../AnthillModKbSpec/Resolution/P1/Export.lean) | Machine trees as supplied proofs (`exportTree`, `exportProof`), P0 witnesses as terms, the checker for a P0 plan's export, `Plan.exportProof_checked`, `Plan.exportProof_derives` |
| [P1/Import](../AnthillModKbSpec/Resolution/P1/Import.lean) | Proof imports (`ProofImport`, `Imports.Checked`, `ProofImport.checked_sound`), their operational admission (`Import.clause?`, `admitImports`, `admitImports_sound`), and admission with supplied proofs (`admit`, `admit_proved_derives`, `admit_plan`) |

## Proof trees

A tree is `Proof.node rule conclusion premises`: a rule application, its
conclusion, and one subtree per premise. The rule carries the parameters that
the conclusion and premise conclusions do not determine. The rule also fixes
each premise's context, which is the node's context extended by what the
premise assumes:

| Rule | Parameters | Premise conclusions (added assumptions) | Side conditions |
| --- | --- | --- | --- |
| `assumption` | — | — | The conclusion is in the context |
| `truth`, `equalRefl` | — | — | Conclusion `true`, `a = a` |
| `conjIntro`, `conjLeft`, `conjRight` | — | `a`, `b`; `a ∧ b`; `a ∧ b` | |
| `disjLeft`, `disjRight` | — | `a`; `b` | Conclusion `a ∨ b` |
| `disjElim` | — | `a ∨ b`, `G` (`a`), `G` (`b`) | |
| `impIntro`, `impElim` | — | `B` (`A`); `A → G`, `A` | Conclusion `A → B`; `G` |
| `falsityElim` | — | `false` | |
| `forallIntro x` | eigenvariable | the body opened at `x` | `x` fresh for the context and the conclusion |
| `forallElim t`, `existsIntro t` | witness | `∀y. B`; the body at `t` | The conclusion is the body at `t`; `∃y. B` |
| `existsElim x O` | eigenvariable, opened body | `∃y. B`, `G` (`O`) | `O` is `B` opened at `x`; `x` fresh for context, `∃y. B`, and `G` |
| `clause C σ`, `goalClause C σ` | KB clause, instantiation | the body instantiated by `σ` | `C` is in the snapshot; the conclusion is the head instantiated by `σ` (`false` for a goal clause) |
| `defaultNegIntro e` | NAF evidence | — | Conclusion `naf A` with `A` closed; `e` accepted for `A` under the context by the NAF evidence check |
| `hoApplyIntro`, `hoApplyElim` | — | `p(args)`; `ho_apply(p, args)` | |
| `equalSymm`, `equalTrans`, `equalSubst x T` | template | `a = b`; `a = b`, `b = c`; `a = b` and `T` at `a` | The conclusion is `b = a`; `a = c`; `T` at `b` |
| `extension s ps` | derived rule, parameters | as its procedure states | Its registered procedure accepts the application |
| `reference s` | name | — | The referenced proof proves the conclusion here |

Substitution results are stated in the tree and decided, not computed:
`substitutes σ before after` reads each output binder off `after`, checks that
it captures nothing the substitution introduces, and recurses. It decides
`Substitutes` exactly (`substitutes_iff`). An instantiation is a list of pairs,
and the first pair for a name wins (`ofPairs`).

## The encoding

A tree is a `Term`. Each structural position uses one symbol of a
`Vocabulary`, and the symbols are all distinct. Formulas, witnesses, and
evidence are embedded as they are, at positions the decoder knows, so a
formula that happens to use a vocabulary symbol is not misread.

| Shape | Term |
| --- | --- |
| node | `node(rule, conclusion, list(premise₁, …))` |
| rule | `r(parameters…)`, one tag per rule |
| eigenvariable, name | the variable itself |
| clause `H :- B₁…Bₙ`, `:- B₁…Bₙ` | `definite(H, B₁, …, Bₙ)`, `goal(B₁, …, Bₙ)` |
| instantiation | `list(pair(x₁, t₁), …)` |
| derived rule `s`, reference `s` | `extension(s(), list(p₁, …))`, `reference(s())` |
| P0 failure and success witnesses | `failsAtom(list(…))`, `failsLeft(…)`, `byClause(list(body), …)`, … |

`decode` reads back exactly what `encode` writes (`decode_encode`). A term of
any other shape decodes to nothing and is rejected.

## Checking

The checker has two levels. `Local` states one rule application: the side
conditions of the matching `Derives` rule, read off the node's rule,
parameters, conclusion, and premise conclusions, and the contexts the rule
gives its premises. `nodeCheck` is the known procedure for each rule. It reads
the node and never searches, and it decides `Local` exactly (`nodeCheck_sound`,
`nodeCheck_complete`). `Valid` asks for a valid application at every node, and
for each premise subtree to be valid under the context its rule gives it.
`check` decides `Valid` by recursion on the tree, so it terminates
(`check_iff`).

| Property | Theorem |
| --- | --- |
| Substitution with a stated result is decided exactly | `substitutes_iff` |
| Each rule's procedure decides its application | `nodeCheck_sound`, `nodeCheck_complete` |
| The checker decides tree validity and terminates | `check_iff` (structural recursion) |
| A valid tree reconstructs `Derives` with the checker's KB, context, and NAF provider | `Valid.derives`, `Local.derives` |
| A valid tree needs no capability the checker or the import table lacks, through its references | `Valid.uses`, `Valid.missing_nil` |
| Decoding reads back exactly the encoded tree | `decode_encode` |
| A term is accepted exactly when it is a checked proof | `checkProof_accept_iff` |
| A checked proof reconstructs `Derives` | `checked_toDerives` |
| Needs-evidence is for a tree of the stated goal, decided before the tree is checked | `checkProof_needsEvidence` |

No formula of the tree is submitted to automatic admission. The root goal and
every intermediate formula may lie outside any discovery plan (R29). Each rule
checks its application given its explicit premises, conclusion, and
parameters, and the premises are proved by their own subtrees (R30).

### Beyond the shared rules

Three things come from outside the shared rules. Each one enters through an
interface whose soundness is a proof obligation in the shared logic:

- **NAF evidence** (`NafCheck`): a procedure that decides evidence for an
  operand under a context, together with the proof that what it accepts holds
  for the checker's NAF provider. A failed search is never evidence: the
  procedure checks a certificate.
- **Derived rules** (`RuleCheck`, for S10–S14): a name, the assumptions each
  premise adds, a terminating procedure that checks one application, and a
  proof that derivations of the premises give a derivation of the conclusion
  in `Derives`. A later command adds its rule by registering a `RuleCheck`. The
  procedure checks the application, and the tree supplies the premises' proofs.
  S09's commands need none: each is a composition of the shared rules and
  exports as their nodes ([left rules](machine-left.md#proof-trees)).
- **References** to previously checked proofs, by name, over an import table
  ordered newest first. A reference stands for the statement its import was
  supplied for: its goal must be the import's goal, and the import's
  assumptions must be in the use site's context. Its proof is re-checked where
  it is used, against the imports older than the one it names, so it meets the
  scope conditions of its use site (freshness, the context's assumptions,
  context-indexed NAF evidence), and no proof can justify itself through a
  cycle.

A tree for the stated goal that needs a capability the checker lacks is not
decided: `checkProof` answers `needsEvidence` with the missing NAF check,
derived rules, or referenced proofs, each listed once, before checking the
tree. A referenced proof's needs count as the reference's, so supplying them
can turn the answer into `accept`. A tree for another goal is rejected first.

### What a verdict means

`checkProof vocab checker imports context goal proof` answers `accept`,
`reject`, or `needsEvidence missing`. `accept` holds exactly for
`CheckedProof(checker, imports, context, goal, proof)`, and it reconstructs
`Derives` for the goal under the original context. `reject` concerns this term
only. Proof checking is a P1 decision of supplied-tree validity (`proofRoute`,
a `DecisionContract` with Yes `CheckedProof` and No "this term is not a checked
proof"). A term that is no tree is rejected for every goal, derivable or not
(`reject_says_nothing`). Rejection proves no negation, NAF, or
non-derivability of the goal (R26).

## Guard premises

A guard premise is checked against the generated signature clauses, like any
clause step, when the checker's snapshot holds them:

- data and `D_all` membership follow the membership and data clauses, with
  their generated variable names in the instantiation;
- a `P_n` guard is the generated fact for the reference symbol.

For a P0 plan's export, each guard fact of the plan becomes a checked
membership node (`Plan.membership`, a `RuleCheck`). Its procedure is S07's
exact guard decision (`decideGuard`) under the node's context. Its soundness is
the guard's derivation from the generated clauses (`decideGuard_derives`), which
the program carries because an admitted input has no missing generated clause.

## Exporting machine proofs

`exportTree` turns a completed machine tree into a supplied proof. It reads
every node's goal and parameters through the final store, and turns each NAF
certificate into its evidence term. For an existential elimination it records
the opened body that its second premise assumes; a node whose premise assumes
anything else exports nothing. A derived rule's closed-world evidence travels
as its last parameter. A tree that still holds a reference to a delayed goal
is an unresolved hole and exports nothing (`exportTree_refs`). An S09 command
node exports as the logical nodes it stands for, with its subproofs spliced in
(`exportNode`, `exportDerived`). `exportProof` exports a `CompletedProof` and
encodes it.

For a Ready P0 plan (`Plan.exportProof`), the export is checked by
`Plan.checker`:

- its snapshot is the input's effective program, generated signature clauses
  included, not the plan's guard facts;
- its NAF provider is `Plan.failure`, which is complete failure in the plan's
  ground program, under exactly that snapshot's KB and the plan's context;
- its NAF evidence check is `Plan.negation`, which checks a failure witness
  structurally against the plan's ground program, under the plan's context
  only;
- its one derived rule is the membership node.

The P0 run invariant now also records that every node is a rule application
of the run (`P0.NodeOk`, `P0.Built`), and `run_correct` reports it together
with the empty final store and the tree's coherence.

| Property | Theorem |
| --- | --- |
| Every successful run of a Ready plan exports a term the plan's checker accepts, for the input's context and goal | `Plan.exportProof_checked` |
| The exported term reconstructs `Derives` in the input's effective program | `Plan.exportProof_derives` |
| Every node of a P0 run's tree is a P0 rule application | `P0.run_correct` (`Built`) |
| A tree with an unresolved hole exports nothing | `exportTree_refs` |

The exported tree of a run equals the tree built by hand for the same proof
(R28). `Plan.exportProof_derives` improves on `run_correct_of_p0`, whose
derivation is in the plan's program: the positive part is now in the input's
own program.

## Proof imports

An import keeps its statement's context, so a proof under assumptions never
becomes a global fact, and the binder ranges its source was lowered with
(`ProofImport.ranges`), as provenance: the lowered statement is what is
checked. Its KB and NAF provider are those of the checker the table is checked
with, which every check takes explicitly. `Imports.Checked` holds when each
import is a checked proof of its own statement against the imports older than
it. `checkImports` decides it. `ProofImport.checked_sound` derives the
statement under its own context.

Using an import in execution is a separate, operational check:

- `Import.clause?` yields a clause only for a closed statement proved under no
  assumptions: a fact, or a rule `B₁ ∧ … ∧ Bₙ → H` as `H :- B₁, …, Bₙ`.
- `importedClauses` collects the clauses of the accepted imports that are in
  the P0 classes; the others stay in the proof layer. Each clause states a
  checked import (`importedClauses_sound`).
- `admitImports` refuses a checker whose KB does not contain the executable
  program (`coversInput`). Otherwise it adds the clauses to the program as KB
  clauses and runs P0 admission on the result, so the extended program is
  ranked as a whole. Every clause of the extended program is in the checker's
  KB or states a checked import of it (`admitImports_sound`), so the run
  answers for that KB.

A proved recursive theorem whose clauses P0 does not admit can contribute its
checked instances. For example, `even(s(s(X))) :- even(X)` asks for evidence
in P0. Its theorem `even(4)` is checked in a proof layer whose KB is the
executable program with that clause, and becomes a fact of the executable
program, which then succeeds where it was exhausted.

`admit` is one admission check over supplied proofs, imports, and P0, in the
query's own program (`ownChecker`). A supplied term that checks for the query
answers it (`proved`) without running anything, and the query is derivable in
its own effective program (`admit_proved_derives`). Otherwise P0 decides on the
program extended with the accepted imports (`admit_plan`), and a
`needsEvidence` answer lists P0's requests together with the capabilities the
supplied proofs lack. A checker for another KB is not used. A query outside P0
asks for evidence, and once the evidence is supplied the same check answers
`proved`. At run time proofs are only checked, never discovered.

## Conservativity

An accepted tree is a `Derives` derivation in the checker's KB, so the route
adds no theorems to the shared calculus. The derived rules are conservative by
their soundness proofs, and the main theorems use only Lean's standard axioms
(`propext`, `Quot.sound`, `Classical.choice`). The NAF provider is a parameter.
That a derivation is true in a model is soundness under the adequacy of that
provider (`Semantics.lean`), which is a model assumption, not conservativity.
For P0 exports the provider is failure in the plan's ground program, whose
guard facts the generated clauses derive. Composing positive and negative
evidence into `E(KB)` under one provider is S16's.

## Traces

| Trace | Result |
| --- | --- |
| R25, R29: `∀1. p(1) → p(1)` by `forallIntro 5`, `impIntro`, assumption | Accepted; outside P0, which asks for evidence |
| R26: the same with the opened body at another eigenvariable; a term that is no tree | Rejected; the goal is still derivable |
| R27: `q` by assumption in the empty context; eigenvariable 5 under `q(5)`; a lemma proved under `q`, used in the empty context | Rejected each time; accepted under `q`, with eigenvariable 6, and under `q` respectively |
| R30: `p(X) :- q(X)` at `X := a`, then at `X := b`; a clause outside the snapshot; `∀`-elimination; `∨`-elimination with a wrong case | Accepted; rejected; rejected; accepted; rejected |
| A lemma `q(a)` referenced in a proof of `p(a)`; without the import; an import proving something else, also referenced for what its term proves; an import referencing itself | Accepted; needs evidence (`lemma`); rejected, rejected; needs evidence (a `loop` before it), never accepted |
| A referenced lemma that uses NAF, without a NAF check; two NAF nodes without one | Needs evidence (`negation`), listed once |
| `even(4)` by the recursive clause, instantiated twice | Accepted; the clause is outside P0 |
| `w :- even(4)`, `even(0)` without and with the imported `even(4)`; with a KB missing the program; with a NAF import too | Exhausted; success; refused; success, the NAF import not added |
| The identity query with no proof, then with a rejected and an accepted proof; checked against another KB; with an unregistered rule | Needs evidence; `proved`; needs evidence; needs evidence listing the rule |
| `isNat(succ(zero))`, `allData(succ(zero))`, `isPred(p)`, `isPred(q)` against the generated clauses | Accepted, accepted, accepted, rejected |
| R28: `p :- q`, `q` exported from the run, and the same tree by hand | Both accepted; the terms are equal |
| Exports with a guard fact (`isNat(succ(zero))`, `allData(succ(b))` under `isNat(b)`) | Accepted, through membership nodes |
| `p :- naf q` exported; under another context; with a forged witness; without a NAF check | Accepted; rejected; rejected; needs evidence (`negation`) |
| An unregistered derived rule, for its goal and for another | Needs evidence (`rule`); rejected |
| A tree with a delayed-goal reference; a malformed existential elimination; a derived rule with closed-world evidence; an `equalSubst` template naming a bound name | Exports nothing; exports nothing; the evidence is the last parameter; the template is read through the store |

## Limitations

- **Export of general S06 runs is defined but not proved to check.** The
  theorem that exported trees pass the checker holds for P0 runs. For other
  S06 runs (non-ground goals, quantifiers, local rules, answers read through
  the final store) it needs S06's reconstruction restated syntactically, and
  it belongs to S15/S16, where the contract places `exportProof_checked`. S09
  proves its constructions valid given valid premise trees
  (`Unfold.*_proves`); the theorem for its whole runs is S15/S16's too.
- **References are re-checked at each use.** There is no weakening lemma for
  `Derives`, so a lemma is not reused without re-checking under the use site's
  context. Nothing is memoized: a chain of lemmas each referencing the previous
  one twice is checked exponentially often.
- **Imports reach execution only as closed facts and rules in the P0 classes,
  proved under no assumptions.** A universal theorem stays in the proof layer.
  A rule's premise must be a conjunction ending in `true`, as
  `Term.conjunction` builds it; `a → h` with a bare atom `a` is read as a fact,
  which P0 then does not admit.
- **P0 NAF evidence holds only under the plan's context.** NAF under a grown or
  scoped context is S10's.
- **The encoding is internal.** There is no public proof syntax, parser, or
  serialized format; the vocabulary's symbols are a parameter.
- **The checker decides validity of the supplied tree, not derivability.**
  Finding a proof is P2's.
