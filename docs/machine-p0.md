# P0 admission and total evaluation

S07 implements the P0 profile of the [admission contract](lean-admission-contract.md):
finite ground acyclic resolution, with nested ground NAF and complete failure,
on the shared machine of [S04](machine-state.md) with the
[S06 positive strategy](machine-positive.md). Admission is decided before any
rule runs; a Ready plan's run terminates with a success certificate or a
complete-failure certificate for the original program, context, and goal.
Traces are in [Tests/Resolution/P0/Admission.lean](../Tests/Resolution/P0/Admission.lean).

| Module | Contents |
| --- | --- |
| [Machine/State](../AnthillModKbSpec/Resolution/Machine/State.lean) | `Response.negate`, NAF barriers (`ChoicePoint.barrier`), NAF entries (`Continuation.negation`), `cutNegation`, `Reaches`, `run_snapshot` |
| [Machine/Negation](../AnthillModKbSpec/Resolution/Machine/Negation.lean) | The ground NAF command `Strategy.withNegation`; what `Store.groundNegation` means for the obligation as read (`Store.groundNegation_read`) |
| [P0/Rank](../AnthillModKbSpec/Resolution/P0/Rank.lean) | Atoms of a goal, dependency edges, rank witnesses (`Ranked`), levels, totality of the certificates (`decided`), rank construction (`topoRank`, `topoRank_decreases`) |
| [P0/Witness](../AnthillModKbSpec/Resolution/P0/Witness.lean) | Finite success and failure trees, their structural checkers (`checkSuccess_sound`, `checkFailure_sound`), and the ranked evaluator that builds them (`evaluate_sound`, `evaluate_total`) |
| [P0/Strategy](../AnthillModKbSpec/Resolution/P0/Strategy.lean) | The run input (`Ground`), negative certificates with their failure witnesses, the P0 command set (`Ground.strategy`) and its exact answer on ground goals (`Ground.strategy_eq`) |
| [P0/Run](../AnthillModKbSpec/Resolution/P0/Run.lean) | The measure, the run invariant, `step_inv`, `run_total`, `run_correct`, `run_semantic`, the fuel-free run `runToEnd` (`runToEnd_finished`) |
| [P0/Admission](../AnthillModKbSpec/Resolution/P0/Admission.lean) | Inputs and program inputs (`ProgramInput`), evidence requests, guard decisions, `check`, plans, the admission theorems, `Plan.answer`, the program-level check (`checkProgram`, `ProgramResult`), `Machine.run_total_of_p0`, `Machine.run_correct_of_p0` |

## NAF in the machine

A strategy answers `Response.negate certificate` for an obligation it
evaluates by negation as failure. The machine takes the operand from the goal
as written, `naf operand`, so a strategy cannot name another one. It checks
that the obligation is ground as read (`Store.groundNegation`): the operand
and every assumption, read through the store's bindings, are closed
(`Store.groundNegation_read`). An unbound flexible name could be bound by the
operand's search, deciding the NAF for that binding only. A rigid parameter
stands for every value: in `∀X. naf p(X)` with the fact `p(a)`, `p(X)` fails
for the eigenvariable `X`, which does not show `naf p(a)`. Both stay gaps in
P0. S10 delays a flexible operand and refutes a rigid one in the Clark
completion ([machine-negation](machine-negation.md)). A name bound before the NAF is read through its
value. The machine then runs the operand in the same run, under the
obligation's own scope, behind a barrier:

| Focus | Condition | Next state |
| --- | --- | --- |
| `solve ob` | `negate c`, goal `naf operand`, ground as read | Focus `solve ⟨ob.scope, operand⟩` above an entry `negation ob ⟨ob.scope, operand⟩ n`; a barrier is saved: a choice point focused on `ob` whose one alternative is the NAF node `defaultNegIntro c`, marked with the current gap count and suspension counter `n` |
| `solve ob` | `negate` for another goal, or an obligation not ground as read | `failed`, contract gap |
| `proved t` | top entry `negation ob _ n` | `failed`: the operand succeeded, so the NAF obligation fails; the choice points through the first barrier are discarded. If a goal delayed since the entry was pushed, the obligation is also recorded as an `unsupported` gap |
| `failed` | a barrier on top, no gap recorded and no goal delayed since it was set | The NAF node is entered from the barrier's saved branch: the obligation is proved and its continuation resumes |
| `failed` | a barrier on top, a gap recorded or a goal delayed since | The barrier is dropped and the NAF obligation is recorded as an `unsupported` gap: an incomplete operand search never certifies failure |

**Ground NAF does not decide an operand whose search delays.** If any goal
delays while the operand is searched, in any branch, the NAF obligation is a
gap whether the operand is then proved or exhausted, even when every delayed
goal woke and was proved inside the operand: the run is never exhausted on its
account. The suspension counter only grows and is never restored, so comparing
it with the value marked at the barrier detects every delay. Without builtins,
delays inside a ground operand come only from range guards on the clause
variables the operand selects, and from formula-variable goals. Deciding such
NAF is S10's.

Barriers nest with their entries: the operand's own choice points sit above
its barrier, and an inner NAF is resolved before control returns to the outer
operand, so the first barrier is always the operand's own (`step_negate`,
`step_refute`, `step_abandon`, `step_backtrack`). Every transition keeps every
branch valid (`step_valid`, `Branch.Valid.negate`, `Branch.Valid.refute`); a NAF
entry's invariant records that its obligation continues the entries below and
reads `naf` of the entry's operand under the same scope (`Linked.negation`).

For generic reconstruction, `Response.alternatives` of `negate` is the NAF node,
so `Strategy.Sound` covers it: a strategy is sound only if that node is sound
on its own (`Strategy.withNegation_sound`), since reconstruction does not see
the operand's search. Only a failure provider accepting every such node meets
that, so generic reconstruction does not cover a real NAF run. The P0 node is
justified by the run instead: it is built only after the operand is exhausted,
which `run_correct` turns into a complete-failure certificate.

`Strategy.withNegation certify base` is a fallback: it keeps every answer of
`base`, and only where `base` answers `unsupported` for a goal written `naf A`
does it answer `negate`, under the machine's own condition
(`Store.groundNegation`), since the operand's search could otherwise bind a
name and decide the NAF for that binding only. So `positive`'s exact
candidates (an assumed `naf A`, ex falso) still come first, a NAF whose names
are bound by then is decided (`∃X. r(X) ∧ naf q(X)` reads `naf q(a)` once
`r(a)` binds `X`), and a NAF that is not ground as read stays a gap. Open and
scoped NAF, and evidence-first NAF beyond identity, are S10's
([machine-negation](machine-negation.md)).

## The P0 command set

A P0 run is `Machine.run` with `Ground.strategy`: the S06 `positive` strategy
over the plan's clauses, with ground NAF. No other strategy is introduced.
On every obligation of the run, in the empty store, it answers
(`Ground.strategy_eq`):

| Goal | Answer |
| --- | --- |
| `true` | `candidates [truth]` |
| `false` | `candidates []`: P0 has no denial clause and an atomic context, so falsity has no source |
| `a ∧ b` | `candidates [conjIntro a b]` |
| `naf a` | `negate` with the run's certificate for `a`: `positive` has no exact candidate and answers `unsupported`, and the scope is ground |
| an atom | One `assumption` per occurrence in the context, then one `clause` per program clause with exactly that head, in order |

So the run never answers `unsupported`, `incomplete`, or `delay`. Matching two
ground terms without `ho_apply` is decided by identity (`Store.unify_plain`),
and a ground candidate commits without changing the empty store
(`Store.commit_ground`). P0 data therefore exclude the reserved `ho_apply`
symbol everywhere, not only at the head: the shared matcher reports a
comparison against it as `unsupported`. S11 converts calls in goal positions
only, since `holds_hoApply` relates truth, not values. This refines the contract's
`GroundSearch.IsData` by `Ordinary` (`P0.Plain`).

## Admission

`Admission.check hoApplySymbol input` takes the snapshot (signature, listed
constructor rules, generated-clause naming, effective program) and the query.
The signature declares its constructor rules by a predicate, so the input
contract carries the proofs that `Input.rules` lists exactly the declared rules
(`listed`, `complete`) and that the generated clauses name arguments distinctly
(`distinct`): a rule list that adds or omits a rule cannot form an input. It
also carries that the program marks exactly the signature's guard symbols
(`marked`), as `Program.build` does (`Program.build_guard`). The check runs no
rule:

1. **Declarations.** The program must be the snapshot's effective program. A
   program clause marked as generated from the signature that the signature
   does not generate is `invalid (signatureClause position)`; a generated
   clause the program does not carry is
   `invalid (missingSignatureClause position)`, by its position in
   `signatureClauses` (`Input.unlisted`). Nothing else is invalid: being outside
   P0 never is (`check_invalid`).
2. **Classes.** Every formula outside its P0 class gets a request: its site
   (`goal`, `assumption i`, `head i`, `body i j`, with KB clause indices), its
   term path, the formula, and the capability it needs. All requests are
   listed, not only the first (`check_needsEvidence`).
3. **Rank.** The whole program's dependency graph, including edges to atoms
   under any number of NAF constructors, is ranked by peeling (`topoRank`) and
   the rank is verified on every edge. If it fails, each KB clause on a cycle
   (an atom of its body reaches its head) gets an `acyclicStrategy` request; a
   clause that only depends on a cycle gets none. Cycles are never semantic
   falsity.
4. **Ready.** Otherwise `ready plan`: the input, the decided guard facts, the
   run input with its rank witness, and what admission established about them
   (`Admits`). A plan carries that proof, so no plan pairs an input with
   another input's run, and every plan is a Ready one (`Plan.admitted`). The
   guard facts and the rank are computed once.

| Capability | Requested for |
| --- | --- |
| `groundInstance` | A variable where P0 needs ground data: an answer name or a clause template in an atom's arguments |
| `formulaVariable` | A formula variable as a goal, an assumption, or a head, where P0 needs a ground atom |
| `acyclicStrategy` | A KB clause on a dependency cycle, positive or through NAF |
| `scopedProof` | An implication, quantifier, or disjunction goal or assumption, or another non-atomic assumption |
| `equality` | An equality goal, head, or assumption |
| `dictionaryLaw` | A dictionary operation call, at any site |
| `hoApplyConversion` | An application by `ho_apply`, also inside data |
| `contradiction` | A denial clause |
| `compoundHead` | A clause concluding a compound formula, such as an induction principle |
| `guardDefinition` | A KB clause concluding a guard atom |
| `termKind` | A formula inside data, or a literal as a goal, head, or assumption |

### Guards

Guards are atoms over the signature's membership symbols (`guardSymbol`). Their
generated clauses are non-ground and recursive (`isNat(succ(X)) :- isNat(X)`),
so they are outside P0 clause search; P0 replaces them by decisions and does
not reject an input because of them. A KB clause cannot conclude a guard atom
(`guardDefinition`), so a guard atom follows only from the generated clauses
and the context's assumptions. A ground guard atom asked for by the query or a
KB clause body is decided by `guardHolds`, which follows the generated clauses
symbol by symbol on the structure of the term:

| Route | Generated clause | Decided by |
| --- | --- | --- |
| Assumption | — | The atom is assumed in the context |
| Membership | `m(c(x₁…xₖ)) :- m₁(x₁), …, mₖ(xₖ)` per declared rule of a domain with symbol `m` | A listed rule with that symbol and constructor whose fields' atoms hold for the arguments |
| D_all | `D_all(x) :- m_D(x)` per domain | The membership or another base route of some domain's symbol, on the same term |
| Predicate | `P_n(s).` per registered reference | Lookup of the reference |

Assumptions count at every level: under `isNat(b)`, `isNat(succ(b))` holds by
succ's membership clause, as in the original program. Symbols are compared, not
domains, so domains sharing a membership symbol behave as their generated
clauses do. The decision is exact: an atom holds exactly when it is in
`Generated`, the least set containing the context's guard assumptions and
closed under the generated clauses (`guardHolds_iff`, from the input
contract). Every generated atom is derivable from the generated signature
clauses under the context (`Generated.derives`, through
`membershipClause_derives`). The plan lists the decided atoms as facts (source
`signature`); an asked guard atom is a fact exactly when it is generated
(`Plan.guards_exact`), so its failure in the run is its absence from that
least set. Every fact derives from the input's own program, which carries the
generated clauses (`Plan.guards_derive`, `signatureKb_carried`).

### Admission theorems

| Property | Theorem |
| --- | --- |
| A computed Ready is the admission judgment: the program is the effective program, and the plan runs exactly this input's KB clauses with the decided guard facts, its context, and its goal, all in the P0 classes, with a rank witness | `check_ready_sound`, `P0Admitted`, `Admits` |
| Every consistent input carrying the generated clauses, in the P0 classes, with acyclic KB clauses is Ready; not completeness for arbitrary formulas | `check_p0_complete`, `topoRank_decreases` |
| No request exactly when every formula is in its class | `requests_nil_iff`, `goalRequests_nil`, `clauseRequests_nil`, `contextRequests_nil` |
| Invalid only for a contradicted declaration | `check_invalid` |
| A plan is admitted for exactly one input | `P0Admitted.unique` |
| Lowering takes only the naming, so lowered formulas survive any other change of the signature; this holds by the lowering functions' types, and the theorem records it | `lowering_naming_only` |
| An asked guard atom is a plan fact exactly when the generated clauses derive it from the context; every fact is derivable from the input's program | `Plan.guards_exact`, `guardHolds_iff`, `Plan.guards_derive`, `Generated.derives` |

## Totality and correctness

The run invariant `P0.Inv` has three parts besides `State.Valid`:

- **Shape**: the store is empty, nothing is deferred, no gap is recorded, every
  obligation is ground with the root's scope and at most the root's level,
  every frame builds a node that holds (`Holds`: success certificates for its
  premises give one for its conclusion), every proved subtree has a success
  certificate, every NAF node in it a valid negative certificate, and every
  barrier holds the run's certificate for its operand.
- **Completeness** (`Covers`): segment by segment through the barriers, if the
  segment's target (the innermost NAF operand, or the root goal) succeeds, the
  current branch or a saved alternative of the segment is live: all its pending
  goals succeed. Below a barrier the next segment's branch is the NAF goal's
  continuation, live when the operand fails. Exhaustion of a segment therefore
  means its target has no success certificate, hence a failure certificate
  (`fails_of_not_succeeds`).
- **Measure** (`measure`): `budget` bounds the steps of a goal under a
  continuation, summing one continuation per candidate of an atom, at a level
  bound that decreases into clause bodies under the rank (`budget_stable`).

| Property | Theorem |
| --- | --- |
| Every transition keeps the invariant and decreases the measure | `step_inv` |
| A ranked ground goal has a success or a failure certificate | `GroundSearch.decided` |
| A run from the plan's query finishes within its measure, with success or exhaustion | `P0.run_total`, `Machine.run_total_of_p0` |
| Success proves the original goal: a success certificate, valid certificates in every NAF node, and `Derives` with the exact ground failure provider. Exhaustion gives a complete-failure certificate. No run is `unknown` | `P0.run_correct`, `Machine.run_correct_of_p0` |
| In a model completed for the program and context with complement NAF, success makes the goal true and exhaustion false | `P0.run_semantic` |
| Every state a plan's run reaches records no gap and gets candidates or ground NAF: never a missing capability | `ready_no_missing_capability` |
| Every node of a successful run's tree is a P0 rule application, the final store is empty, and the tree is coherent; its export is checked by S08 | `P0.run_correct` (`Built`), [`Plan.exportProof_checked`](proof-checking.md#exporting-machine-proofs) |
| The completed proof records the run's snapshot, the plan's input | `run_snapshot` |
| A Ready plan's query is decided, with no fuel: `true` exactly on a success certificate, `false` exactly on a complete-failure certificate | `Plan.answer_true`, `Plan.answer_false`, `Plan.answer_spec`, `P0.runToEnd_finished` |
| On a program `checkProgram` accepts, every P0 query is Ready and decided | `checkProgram_ready`, `checkProgram_decides` |
| The program-level check's requests sit at KB clause heads and bodies; its diagnostics hold for every query | `checkProgram_needsEvidence`, `checkProgram_invalid` |

### Deciding queries, and every query of a program

`Plan.answer` answers a Ready plan's query: `true` when its run succeeds and
`false` when it is exhausted. It runs with no fuel (`P0.runToEnd`): each step
decreases the run's measure, which only the termination proof uses, so the
measure is never computed and the run is never interrupted. `true` holds
exactly when the goal has a success certificate, and `false` exactly when it
has a complete-failure certificate (`Plan.answer_true`, `Plan.answer_false`).
`false` is closed-world: failure in the plan's program under its context.

`checkProgram` admits a program for every query at once. It takes a
`ProgramInput`, an input without its query (`ProgramInput.ask` adds one), and
is `check` on the program with the empty query (goal `true`, no assumptions).
That query asks nothing of its own: every request sits at a KB clause's head or
body (`checkProgram_needsEvidence`), and a diagnostic holds for every query on
the program (`checkProgram_invalid`). On a program it accepts, every P0 query
(a ground goal of the P0 classes under a ground atomic context) is Ready and
decided (`checkProgram_ready`, `checkProgram_decides`). Each query is decided
against its own plan's program: the KB clauses with the guard facts that query
asks for. Relating a failure to the effective program itself is S16's.

The check is sufficient, not necessary: a recursive program may decide its
queries and still be rejected, and a query outside the P0 classes still asks
for evidence. Every query repeats the whole `check`, rank included, since the
program-level check keeps no reusable result; a program-level check across all
P1 routes, with a reusable admission, is S15's.

## Evidence and invalidation

A NAF node keeps a `NegativeCertificate`: the exact clause list and context it
was computed against, the operand, and a finite failure witness. A failure
tree lists, for an atom, one failing body per clause with that head in program
order; for a conjunction, the failing side; for NAF, the operand's success
tree, which names the assumption or clause used. `NegativeCertificate.check`
checks the witness on the certificate's own clauses and context by structural
recursion on the tree: it repeats no search and terminates. It is sound
(`checkFailure_sound`, `NegativeCertificate.Valid.fails`). A certificate is
valid for a program and context when it names exactly them and its check
passes (`NegativeCertificate.Valid`); evidence computed under other clauses or
another context is never valid (`NegativeCertificate.stale`).

The witness is built by `evaluate`, a decision procedure for ranked ground
goals that recurses on the level bound into clause bodies; under the rank it
always answers (`evaluate_total`) and its trees check (`evaluate_sound`). The
P0 command attaches it, unbuilt, when it hands a NAF goal to the machine: the
certificate holds it as a `Thunk`, built when first read, so a NAF whose
operand is proved, or whose node nobody checks, never builds one. The
machine's barrier decides when the node is built, after the operand's search
is exhausted, and the run then proves the witness checks (`evaluate_failure`,
`run_correct`). S08 checks these certificates with
`NegativeCertificate.check`. A completed proof also records the snapshot
(`run_snapshot`), and a plan is admitted for one input (`P0Admitted.unique`),
so a changed program, signature, context, or goal needs a new check. Lowered
formulas do not, since lowering takes only the naming
(`lowering_naming_only`).

## Traces

| Trace | Result |
| --- | --- |
| R01: `p(a) :- q(a)`, `q(a)` | Ready; success with clause and fact evidence, one clause node per use; under the context `q(a)` the body closes by assumption |
| R02: `p :- q`, `p :- r`, `r` | The first candidate fails; the second succeeds; `p` completes once |
| `p :- q`, `p :- r`, no `q`, `r` | Exhausted (complete failure); a budget of two steps interrupts it |
| R03: `p :- naf q`, no `q` | Ready; success with one NAF node whose certificate names the clauses, the empty context, and `q`, and carries the witness "no clause for q", which checks |
| `w :- naf p`, `p :- q`, `p :- r, s`, `r` | The witness lists both of p's clauses failing; it checks |
| `p :- naf naf q` with / without `q` | Success with one outer NAF node / exhausted |
| `r :- s(a), naf q(a)`, `r :- s(b), naf q(b)` with `q(a)` | The first clause fails at its NAF; the second succeeds |
| R04: `p :- p` beside `p` | `acyclicStrategy` for clause 0, before execution |
| R05: `p :- naf p` | `acyclicStrategy` for clause 0 |
| `p :- naf q`, `q :- p`; `p` with an unrelated `q :- q` | Both clauses on the cycle; the unrelated cycle is still rejected |
| `s :- p`, `p :- q`, `q :- p` | Only the clauses on the cycle, 1 and 2 |
| R06: `naf q` in the empty context, then with `q` assumed | Success with a certificate for the empty context; with `q`, a new check and run, exhausted |
| A variable, implication, disjunction, equality, call, `ho_apply` in data, non-atomic assumption, denial clause, compound head, guard definition | One request each, with its site, path, and capability; several at once are all listed |
| A built program with recursive membership clauses: `w :- isNat(succ(zero))`, `s :- isNat(b)` | Ready; `w` succeeds from the decided fact, `s` is exhausted |
| `allData(succ(succ(zero)))`; `isPred(p)` / `isPred(q)`; `naf isNat(b)` | Success; success / exhausted; success |
| Under the assumption `isNat(b)`: `isNat(succ(b))`, `naf isNat(succ(b))`, `allData(succ(b))`; under `isNat(c)`: `isNat(succ(b))` | Success, exhausted, success; exhausted |
| `Plan.answer` on R01; on `p :- q`, `p :- r`; on `p :- naf q` without and with `q` | `true`; `false`; `true`, `false` |
| `checkProgram` on `p :- q`, `q`; on `p :- p`, `p` and `p :- naf p`; on `p(X) :- q(X)`; on a forged or missing signature clause | Decides; `acyclicStrategy` for clause 0 each; `groundInstance` at head 0 and body 0 0; `invalid` with the diagnostic `check` gives |
| Queries on the accepted `p :- q`, `q`: `p ∧ naf r` under `r` and without it, `isNat(succ(zero))`, `isNat(succ(b))` under `isNat(b)`, `naf isNat(b)`, `allData(b)`; `p → q` under a variable | `false`, `true`, `true`, `true`, `true`, `false`; needs evidence |
| A rule list adding or omitting a declared rule | Cannot satisfy the input contract |
| A forged signature clause | `invalid (signatureClause 0)` |
| `w :- isNat(succ(zero))` without the generated clauses; with them | `invalid (missingSignatureClause 0)`; Ready |
| `withNegation` over `positive`: `naf q` under an assumed `false` or `naf q`, with the fact `q` | Success: exact candidates come first |
| `∃X. (p(X) → naf p(a))` | Unknown: the NAF is not ground, a gap rather than an exhaustion |
| `∀X. naf p(X)` with `p(a)`; `∀X. (p(X) → naf q(a))` with `q(a) :- p(c)`; `naf p(X)`, X a query parameter | Unknown: a rigid name in the operand or an assumption is not ground |
| `r(X) ∧ naf q(X)` with `r(a)`, X an answer name or `∃X`; with `q(a)` too; `naf q(X) ∧ r(X)` | Success; exhausted; unknown, since X is unbound at the NAF |
| `naf q` with `q :- isNat(Y), r(Y)`, `r(zero)`, `isNat(zero)`, isNat a guard | Unknown: the guard delayed inside the operand, so the NAF is a gap although q is proved |
| The same with a failing `s` after `r(Y)`; without the guard | Unknown although q is exhausted; decided (success) without the delay |

## Limitations

- **Ready is not truth.** It is admission evidence; the run may be exhausted.
  P0 rejection is not a negative answer either: P1, P2, or P3 may admit the input.
- **Exhaustion is complete failure for the plan's program**: the KB clauses
  with the decided guard facts, under the exact context. It is semantic
  falsity only under `GroundCompleted` and `ComplementNAF` for that program and
  context (`run_semantic`); S16 owns a completed-model witness for admitted
  inputs.
- **Reconstruction** is `Derives` in the plan's KB with its ground failure
  provider. Guard facts are derivable from the generated signature clauses
  (`Plan.guards_derive`); composing both into `E(KB)` under one NAF provider is
  S16's.
- **The failure witness is the evaluator's**, not a trace of the machine's
  search: both decide the same ground judgment under the rank, and the run
  proves the witness checks. A checked witness costs a second evaluation of
  the operand, with no memoization of nested NAF. Building the witness from the
  machine's own exhausted search would need failure evidence in its choice
  points.
- **Fuel.** Below the measure a `Plan.run` may be `interrupted`, which is
  neither a termination failure nor a refutation. `Plan.answer` runs with no
  fuel and is never interrupted. The measure is a bound, not a cost claim:
  search repeats work, with no memoization.
- **Runs from the query.** The theorems are about a plan's run from its query.
  The resume state of a success searches for further proofs of the same goal;
  its outcome is not covered, and its exhaustion is not a failure certificate.
- **Stricter than stratified Datalog.** Every cycle is rejected, positive or
  through NAF, even beside a fact that would prove the goal (R04). The whole
  program is ranked, not only the clauses a query reaches.
- **Generic reconstruction** (`run_reconstructs`) covers a `negate` answer only
  when the strategy makes its NAF node sound on its own; the P0 node is
  justified by `run_correct`. Open, scoped, and evidence-first NAF are S10's
  ([machine-negation](machine-negation.md)).
- **The static profile for `positive`** beyond P0 (non-ground inputs, the S06
  note's conditions) is S15's; for P0 it is `Ground.strategy_eq`.
