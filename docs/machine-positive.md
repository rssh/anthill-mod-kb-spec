# Ordinary clause selection and positive execution

S06 gives the [S04 machine](machine-state.md) its first concrete command set and
proves that a successful run reconstructs `Derives` for its answer instance. It
builds on the [S05 matching layer](machine-matching.md), the
[S18 delayed goals](machine-delay.md), and the [S19 name invariant](machine-state.md#declared-names).
Traces are in [Tests/Resolution/Positive.lean](../Tests/Resolution/Positive.lean).

| Module | Contents |
| --- | --- |
| [Machine/Reconstruction](../AnthillModKbSpec/Resolution/Machine/Reconstruction.lean) | Node contracts in every later store (`SoundFrom`), sound commands (`Command.Sound`) and the pieces every command uses to prove it (`attempt`, `respond`, `attempt_sound`), the sound-state invariant and its preservation, reconstruction of a successful run |
| [Machine/Program](../AnthillModKbSpec/Resolution/Machine/Program.lean) | The effective program and its lowering |
| [Machine/Positive](../AnthillModKbSpec/Resolution/Machine/Positive.lean) | The `positive` command, its soundness, clause selection and guard theorems |

## The effective program

`LogicalKb` is a set. The command needs a finite clause list in selection order,
so `Program` holds one, with each clause's source (`ClauseSource`: a lowered KB
clause with its index, or a generated signature clause). `Program.kb` is the KB
it denotes.

`Program.build` lowers the KB clauses in order with `elaborateClause?` and appends
the generated signature clauses. Each KB clause comes from the formula generator
as a `SourceClause`: the clause, its binder ranges, and the ranges of its
implicit variables. Lowering never infers a range. A clause `elaborateClause?`
rejects stops the build with `LoweringError.clause index`; no default range
replaces the rejected annotation. `lowerQuery` lowers a query the same way with
`elaborate?`, each assumption under its own annotation child as in
`elaborateContext`, and reports `assumption index` or `goal`.

`signatureKb` is a set over every rule of the domain definitions, which are a
predicate. `signatureClauses` lists it from an explicit list of constructor
rules, the declared domains, and the registered predicates.

| Property | Theorem |
| --- | --- |
| Every program clause is a lowered KB clause or a generated signature clause: it is in `E(KB)` (`elaboratedKb`) | `Program.build_sound`, `mem_signatureClauses` |
| With every constructor rule listed, every clause of `E(KB)` is in the program | `Program.build_complete`, `signatureClauses_complete` |
| A KB clause `elaborateClause?` rejects is reported, at the index of a rejected clause | `Program.build_rejected`, `lowerClauses_error` |
| Accepted clauses and queries are exactly their elaborations | `lowerClauses_ok`, `lowerQuery_ok` |

`Program.guard` marks the guard symbols: the naming's membership symbols for
D_all, each declared domain, and each registered predicate arity (`guardSymbol`).

## The command

`positive hoApplySymbol program` reads the focused goal and its context through
the store once per focus (`Store.readContext`; the matcher reads the sides it
compares again) and answers by the goal's form:

| Goal, as read | Response |
| --- | --- |
| Closed by an exact candidate, and otherwise waiting | The exact candidates |
| An unbound flexible name | `delay` on it |
| A range guard on an unbound flexible name: a guard atom `m(X)`, or the disjunction `m₁(X) ∨ … ∨ false` an explicit domain list lowers to (`guardSubject?`) | `delay` on it |
| Another atom, or falsity | Identity, ex falso, local rules, then program clauses, each matched against the store its commit prepares |
| A connective (`true`, `∧`, `∨`, `→`, `∀`, `∃`) | Exact candidates if any, otherwise its introduction rules |
| Equality, NAF, a call, a rigid name, a literal | Exact candidates if any, otherwise `unsupported` |

Exact candidates need no match: an assumption whose reading is identical to the
goal's, ex falso under an assumption reading as falsity (`falsityElim`), and an
exact step of a local rule, described below.

Falsity (`⊥`, the logic's `false`) is an ordinary goal, as the design asks: its
sources are an assumed falsity, a local rule concluding it (a negation
`∀x̄. (B → ⊥)`), and a denial clause `⊥ :- body`. With none of them it is a miss,
exactly like an atom without a clause. A range guard is a membership check, not a
request for contradiction search: the trailing `false` of an explicit domain
guard is never tried (`guardTail`), so an out-of-domain value is a miss whatever
denial clauses the KB holds.

For an atom or falsity, each candidate is matched with `Store.unify` against
`store.prepare`, and the commit replays the match (`Store.commit_unify`). A
`mismatch` drops the candidate. An `unsupported` or `violated` match is a gap,
never failure. Gaps keep the other candidates: the response is
`incomplete candidates`, which tries them and records an `unsupported` gap for
the focus, so the run is never `exhausted`
([machine response](machine-state.md#commands-and-candidates)). Candidates are
selected by head symbol and arity (`sameHead`), or offered to falsity when they
conclude it. A head that differs from the goal's only by `ho_apply` is matched
too (`mayMatch`): the matcher reports it `unsupported`, since conversion is
S11's, so it is a gap. So is an
assumption from which the goal might follow by rules this slice lacks
(`mayConclude`): a conjunction, disjunction, or existential (left rules), a rule
with a compound or curried conclusion, or one concluding its own binder
(`∀P. P`). Left rules and compound heads are S09's.

| Candidate | Rule | New names | Premises |
| --- | --- | --- | --- |
| Identity with assumption `A` | `assumption` | — | — |
| Universal fact `∀x₁…xₙ. H`, n ≥ 1 | `forallElim xₙ` | Fresh flexible witnesses for every binder | The fact with x₁…xₙ₋₁ instantiated |
| Local rule `∀x̄. (B → H)` | `impElim` | Fresh flexible witnesses for every binder | The instance `B' → H'` and `B'` |
| Program clause `H :- body` | `clause`, with its renaming | A fresh flexible name for every template name | The renamed body, in the obligation's own scope |
| Denial clause `⊥ :- body`, for falsity | `goalClause`, with its renaming (`Expansion.goalClause`) | A fresh flexible name for every template name | The renamed body |
| Ex falso, under an assumption reading as falsity | `falsityElim` | — | `false`, closed by the assumption |
| Connective | Its introduction rule | A fresh eigenvariable for `∀`, a fresh flexible witness for `∃` | As in [the S04 contracts](machine-state.md#named-command-contracts) |

A local rule's `impElim` has the rule's instance `B' → H'` itself as its first
premise; it is sound when the goal reads as `H'` (`impElim_soundUnder_matched`).
`goalClause_soundUnder` is the denial-clause contract. Both are in
[Commands](../AnthillModKbSpec/Resolution/Machine/Commands.lean).

Fresh names come from `Store.freshen` and `Store.freshFor`. They avoid the store's
names and the binder names the obligation reads (`Store.readBinders`); a clause's
or local rule's fresh names also avoid its own binder names as written. The
matcher therefore never meets an alpha-variant made by its own renaming. A local
rule is filtered by its matrix's head before any name is freshened.

### Clause selection and FinishClause

Selecting a clause freshens every template name (`clauseAttempt_fresh`), commits
the head match, and replaces the focus by the renamed body under the
obligation's own scope (`Expansion.clause_start`). The head is never assumed.
The frame above the body is the clause's FinishClause continuation. On the
body's proof it builds the clause node, once (`Expansion.clause_finish`;
a further subproof would be refused, `Frame.feed_overfull`). The node records the clause and its renaming. Read through
the final answers, the renaming is the clause instance (`clause_soundUnder`).

Exhausting one candidate only resumes the next. A goal whose candidates are all
exhausted is not false: `exhausted` carries no negative evidence. There is no loop
check. Under the S01 profile, P0 admission (S07) rejects cyclic programs, and P2
needs a strategy with its own termination argument. Here a looping run ends
`interrupted` by the step budget, which is no result about the goal.

### Guards delay

Lowered clause bodies begin with their range guards. A guard on an unbound
flexible name delays (`positive_guard`) instead of running ahead of the body as an
enumerating generator. That holds for each guard shape: `D_all(X)`, `Pred_n(X)`,
and an explicit domain list's `m₁(X) ∨ … ∨ false`, which delays as a whole. A
guard that an exact candidate closes, such as an identical assumption, is closed
by it instead. A later goal, possibly
the caller's after the clause returns, binds the name and wakes the guard, which
then selects the generated signature clauses as an ordinary atom. Still delayed
at the end, it flounders as a gap.

Guards are recognized by symbol, the naming's membership symbols, following
proposal 060: the conformance check and the member relation are different
functors, so a membership atom is a check, not a generator, also in a user
goal. Predicate guards are recognized for the registered arities; an atom over
the symbol of an arity with no registered predicate has no generated fact and
is an ordinary atom, so registering the first predicate of an arity makes its
atoms wait instead of missing.

The member goal a typed head appends after its body (Anthill proposal 060) uses a
member relation, not a guard symbol. It is an ordinary atom, so a domain's
enumeration is an ordinary list of candidates, not a delay. Its order in the body
is the generator's.

Reconstruction reads `CompletedProof.tree`, which the success step completed with
the deferred proofs. A delayed guard's proof sits at the guard's place in the
body's conjunction, so the order in which the conjuncts ran does not change the
derivation.

### Local rules

A local rule is an assumption `∀x₁…xₙ. M`. Its free names are captured parameters
and are kept. Only its leading binders are instantiated (`Term.instantiateLeading`).
For an atom or falsity the command eliminates all binders of the rule as written
with fresh flexible witnesses and matches the instance of the conclusion against
the goal (`localAttempt`). The intermediate instances, built from the rule as
written, are then proved by exact steps. The rule is classified and filtered by
its reading: a conclusion written as a flexible name and bound later is matched
by its reading. A rule or compound formula behind an assumption written as a
flexible name cannot be instantiated as written, so it is a gap when its
reading might conclude the goal; an atom behind one is identity's.

An exact step (`exactStep`) proves a goal that, as written, is the rule after k
binders. It reads the witnesses off the goal (`extract`), rebuilds the instance,
and requires it to be identical to the goal (`exactInstance?`). Its premise is the
rule after k − 1 binders, which the step for k − 1 closes in turn, down to the
assumption; the step is offered only when that whole chain closes
(`exactCloses`), so its premise never falls back to introduction. Both sides are
compared as written, as `localAttempt` built them, so the step always finds an
instance built for a rule use, whatever the store later binds or renames when it
is read. A binder that does not occur in the rule's matrix gets the closed
witness `true`, so no undeclared name enters a rule parameter.

The command rediscovers the witnesses rather than recording them at the rule
use: a candidate builds one node, and a premise carries no provenance. Building
the chain at once would need either of these in the machine.

S05's matcher compares binders only when identical, so it cannot match under the
remaining binders of an intermediate instance; the exact steps need no match,
and a non-atomic goal is closed only by exact candidates, never by a match. Such
a goal with an exact candidate gets only those candidates, not its introduction
rule: a rule instance `B' → H'` reopened by implication introduction would prove
the goal again under `B'` and recurse. A rule is available only inside the scope
that assumed it, because a sibling premise's scope is computed from the
parent's alone.

## Reconstruction along a run

A tree records each rule application but not the store of the commit that chose
it. A candidate's completion contract (`Expansion.SoundUnder`) holds in the
stores its branch reads afterwards, those that refine the commit. S06 carries the
contract from each commit to the final store.

| Definition | Meaning |
| --- | --- |
| `NodeSound store obligation premises` | The node's contract read through `store`: derivations of its read premises give a derivation of its read obligation. For a candidate it is `SoundUnder` |
| `SoundFrom store obligation premises` | `NodeSound` in every scoped store refining `store` |
| `CandidateSound store obligation e` | If the commit of `e` succeeds, its contract holds from the committed store on |
| `Command.Sound kb` | On a scoped store and a declared obligation, every candidate the command answers is sound |
| `ProofTree.Nodes P` | Every node of a tree satisfies `P`; a reference is checked through its record |
| `State.Sound` | Every node a branch holds or will build is sound from its store on: the proved focus, each frame's node and completed subproofs, the focus a woken entry resumes, every deferred proof, and, for each choice point, its branch and remaining candidates |

| Property | Theorem |
| --- | --- |
| The initial state is sound | `State.init_sound` |
| Under a sound command every transition keeps a valid state sound: commits refine the store, a frame builds the node its candidate promised, records and resumed foci stay sound, rollback restores a sound branch | `step_sound`, `State.enter_sound`, `Expansion.start_sound`, `Continuation.schedule_sound` |
| Filling references keeps every node sound | `ProofTree.Nodes.fill`, `ProofTree.Nodes.fillAll` |
| A coherent tree without references, each node sound in a store, derives its obligation read through that store | `ProofTree.Nodes.readDerives` |
| A successful run of a sound command derives its root read through the final answers; the resume state is valid and sound, so later answers are reconstructed too | `run_reconstructs`, `run_init_reconstructs` |
| `positive` is sound for its program's KB, whatever the NAF provider | `positive_sound` |
| A range guard on an unbound name delays, validly, unless an assumption it reads as closes it | `positive_guard`, `waiting?_guard` |
| A gap keeps the other candidates and is recorded; the run is never exhausted | `Response.incomplete`, `step_gaps`, `run_exhausted` |
| A successful run of `positive` derives its answer instance in the program's KB, and for a built program in `E(KB)` | `positive_reconstructs`, `positive_reconstructs_elaborated` |

`positive_sound` uses the S05 contracts per candidate. Matched readings come
from the commit replaying the match (`Store.commit_matched`) and survive
refinement (`Store.Refines.resolve_eq`). A goal read as a connective reads so in
every later store (`Store.Scoped.read_refines`). An eigenvariable gets its
freshness for the read obligation from `Store.commit_fresh_resolved`, with the
name invariant at the commit. A local rule's `impElim` and a denial clause need
the goal to read as their conclusion, from the match or the read goal. An exact
candidate is sound because the goal already reads as its conclusion.

The run-level theorems hold for every sound command, so later command sets
(S07, S09–S14) reuse them by proving their own `Command.Sound`.

## Traces

| Trace | Result |
| --- | --- |
| R01: `p(a) :- q(a)`, `q(a)` | The first step focuses the renamed body under the same scope, below the clause's frame; one clause node per use |
| `p ∨ q` under `q`; `(p → p) ∧ p`; `∀1. (q(1) → q(1))` | `disjRight` after rollback; exhausted, since the assumption is scoped; universal introduction |
| R02: `p :- q`, `p :- r`, `r` | The first candidate is exhausted, the second succeeds; `p` completes once; resuming is exhausted |
| `p :- q, r` | One node per clause use: the nested frames complete once each |
| `r(X) :- s(X)`, `r(X) :- t(X)` for `r(Y) ∧ u(Y)` | The first clause's bindings are rolled back; answer `b`; resuming is exhausted |
| `p(X)` over `p(a), p(b)`; `∃y. p(y)` | Answers `a`, then `b`, then exhausted; the existential witness reads `a`, then `b` |
| R16 with the clause `s(Y, Y)` | `∀x. ∃y. s(y, x)` succeeds; `∃y. ∀x. s(y, x)` is exhausted |
| `q(a) → ((∀x. (q(x) → p(x))) → p(a))` | `impElim` with an exact `forallElim` from the rule; resuming is exhausted |
| The rule's own instance `q(a) → p(a)` | Closed by one exact `forallElim`, no introduction |
| The rule in one conjunct, `q(a) → p(a)` in the other | Exhausted: the rule's scope ends with its implication |
| `∀1. (q(1, 7) → p(1))` under `q(a, 7)` / `q(a, 8)` | Success / exhausted: the captured 7 is kept |
| `∀1. ∀2. (q(1, 2) → p(2, 1))` under `q(a, b)`; the fact `∀1. ∀2. r(1, 2, 1)` | `p(b, a)` and `r(a, b, a)` by two universal eliminations; `p(a, b)` and `r(a, b, b)` exhausted |
| `∀1. ∀2. p(2)` for `p(a)` | The vacuous binder's witness is `true`; every witness names declared names |
| `∀1. (q(1) → Z)` with `Z` bound to `p(c)`; an assumption `X` bound to a rule, to `p(c) ∧ q(c)`, to `p(c)` | Success through the read head; unknown; unknown; success by identity, then exhausted |
| `∀1. (q(op(1)) → p(1))` under `q(op(a))` | Success: the instance with an operation call is found exactly |
| `∀1. ((∀2. r(1, 2)) → p(1))`, `∀3. r(2, 3)`, goal `p(2)` with 2 a parameter | Success: reading the premise renames binder 2, but the instance is closed as written |
| A curried rule `∀1. (q(1) → (r(1) → p(1)))`; a rule concluding `∀2. p(1, 2)`; the assumption `p ∧ q` for `p`; `∀1. 1` | Unknown: gaps |
| `∀1. ∀2. (q(1, 2) → p(1, 2))` for its own instance `q(2, 7) → p(2, 7)`, 2 a parameter | Success: the exact step whose premise would read renamed is not offered |
| `false` assumed, for `p(a)` and for `p ∧ q` | `falsityElim` closed by the assumption |
| A built program: `v(X) :- true`, `num(X) :- natDomain(X)`, the `natDomain` generator, and the signature clauses | Lowered bodies begin with `D_all(X)`; guard symbols exclude `natDomain` |
| `v(Y)` alone | The guard delays and flounders: unknown |
| `v(Y) ∧ q(Y)` under `q(succ(zero))` / `q(b)` | The caller binds `Y` after `v` returned and wakes the guard, proved from the signature clauses / exhausted |
| `w(X) :- true` with `X : nat` explicitly: guard `isNat(X) ∨ false` | Delays as a whole; `q(b)` exhausted, `q(succ(zero))` succeeds and resuming is exhausted; alone it flounders |
| `w(P) :- true` with `P : Pred₁`: guard `isPred(P)` | `e(p)` succeeds from the registered fact; `e(q)` is exhausted |
| The query `∃x:nat. q(x)` | The guard waits for `q(x)`; success under `q(succ(zero))`, exhausted under `q(b)` |
| A guard `D_all(Y)` under the assumption `D_all(Y)`; a formula variable `X` under `X` | Closed by the assumption, no delay |
| The explicit guard with a looping denial clause `false :- r`, `r :- r`, under `q(b)` | Exhausted: the guard's `false` is never tried |
| `num(Y)` | The appended member goal enumerates: `zero`, `succ(zero)`, `succ(succ(zero))` |
| A clause applying a data-ranged variable by `ho_apply`; the same query goal | Reported (`clause 4`, `goal`); with `.predicate 1` the clause is lowered |
| R04: `p :- p` before `p` / after it | Interrupted / an answer on every resume, never exhausted |
| Falsity under an assumed `false`; by a negation `∀1. (p(1) → false)` and `p(a)`; by a denial clause `false :- p(X), q(X)` | `assumption`; `impElim` with an exact `forallElim`; `goalClause` with answer `b`, then exhausted |
| `p(a)` with the facts `p(a)` and `p(op(b))` | Success; resuming is unknown: the call is a gap, recorded without losing `p(a)` |
| `q(X) ∧ ho_apply(X, a)` with `p(a)`, `q(p)`; `p(a)` with a flexible-head fact `ho_apply(P, a)` | Unknown; success, then unknown: `ho_apply` conversion is a gap |
| An alpha-variant argument; a plain clash; falsity with no source; NAF | Unknown (gap); exhausted (miss); exhausted (miss); unknown |

## Boundaries

- Arbitrary compound clause heads, curried local rules, and left rules on
  compound assumptions (conjunction, disjunction, existential) are S09's; where
  the goal might follow from them, the focus records a gap. Proving `false` from
  negations or denial clauses in order to close another goal is contradiction
  search, also S09's: only an assumption reading as `false` gives ex falso.
- NAF is S07's (nested ground NAF and exhaustive failure for P0) and S10's
  (evidence-first and scoped). This command builds no closed-world node.
- `ho_apply` conversion and flexible heads are S11's; equality and dictionary
  calls are S14's.
- No termination, fairness, or completeness is claimed. Depth-first selection may
  loop, and `exhausted` is relative to this command's candidates.
- Exact steps compare syntactically, as written. A user goal that is a rule's
  instance only after reading gets its introduction rule instead.
