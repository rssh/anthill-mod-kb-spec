# Delayed goals in the machine

[Machine](../AnthillModKbSpec/Resolution/Machine.lean) implements S18 on the S04
[machine](machine-state.md): a command may delay the focused obligation until a
name it waits on is bound, the commit that binds the name wakes it, and a goal
still delayed when the branch would succeed flounders as a gap. Traces are in
[Tests/Resolution/Delay.lean](../Tests/Resolution/Delay.lean).

## Why the machine needs delay

Typed clause heads compile to generated body goals (Anthill proposal 060,
`docs/proposals/060-clause-level-requirements-and-typed-heads.md` in the Anthill
checkout). A head `p(?x: T)` becomes an untyped clause whose body carries a
conformance check and a generator:

```text
rule p(?x: T) :- body    ==    rule p(?x) :- body, SortDomain[T].fill(?x)
```

The generated goals are ordinary goals that read the carried type of a value:

| `?x` when the goal is asked | Outcome |
| --- | --- |
| Bound, conforms to `T` (and is a member, where `T` defines its domain) | Holds; keep the binding |
| Bound, refuted | Fails this binding |
| Bound, under-determined | Suspends |
| Unbound, `T` defines its domain | Enumerates: a choice point over the domain |
| Unbound otherwise | Delays; asked again when a later goal binds it |
| Still unbound at the end | Flounders loudly; never a silent non-check, never NAF |

The generator goes after the body (`fill` at the end): ahead of the body, it
enumerates a recursive type forever before the body can prune it. A primitive
type's `fill` is its waiting check, so it delays rather than enumerates.

The binding a delayed goal waits for can come from any later goal, including
goals of the caller after the clause returns. Reordering a clause body therefore
does not cover it. The machine needs suspension across the
whole remaining resolvent, as in Prolog's `freeze` and λProlog's suspended
goals.

Enumeration over a domain is not delay: it is an ordinary list of candidates
with a choice point.

## Design

### Response

A command may answer `delay names` (`Response.delay`): the focused obligation
cannot proceed until one of `names` is bound. Every name must be a declared,
unbound flexible name, and the list must be nonempty (`Store.delayable`,
`Store.delayable_spec`); otherwise the answer breaks the contract and is
recorded as a gap. Waiting on a rigid name is never useful, since no transition
assigns it; a command that needs a rigid name's value takes another route (for
NAF, a scoped certificate, S10).

### State: wakeups and constraints live in the store

The store is already the branch's logical state: it is threaded through AND
siblings, saved by choice points, and restored as a whole on backtracking, and
`Store.commit` is the only place where names are bound. Delayed goals and
unresolved constraints therefore attach to the names they concern, as attributed
variables do in Prolog. Rollback restores them with the bindings, and the
commit that binds a name reports what it wakes.

| Component | Meaning |
| --- | --- |
| `Suspension` | An id, the delayed obligation with its own scope, and the names it waits on |
| `Store.wakeups` | Pending suspensions, newest first, one entry per id, each listing the names it waits on |
| `Store.constraints` | Unresolved constraints on flexible names (`Constraint`: an obligation and the names it concerns; below) |
| `Commit.committed store woken` | A commit also returns the suspensions it woke (`Store.woken`), removed from the new store (`Store.wake`). The bindings inside a commit return `Bound`: binding wakes nothing until all of the candidate's bindings are made |
| `DeferredProof` | An id, the delayed obligation, and the tree that proved it after waking |
| `State.deferred` | Proofs of woken suspensions, newest first; saved by choice points, restored on backtracking |
| `State.nextHole` | Counter for ids; not restored, so ids are unique across the run |
| `ProofTree.deferred id obligation` | A reference to the separately recorded proof of a delayed obligation, in a tree under construction or in a record; the success step replaces every reference in the returned tree |
| `Continuation.woken id obligation next` | On the continuation stack (`State.frames`), beside rule frames (`Continuation.frame`): record the woken goal's proof under `id`, then resume the focus `next` |

Deferred proofs stay out of the store: the store is the logical state the
matcher (S05) reads and commits to, while deferred proofs are evidence the
success step fills into the completed tree.

A suspension is attached to every name it waits on, but it is one entry keyed
by its id, not a copy per name; a per-name index is only a view of it. A commit
wakes each suspension at most once: binding any one of its names removes the
entry, so no stale attachment remains on its other names, and binding several
of its names in one commit returns it once (`Store.commit_wakes`). Suspensions
in the store are kept newest first, so their ids are strictly decreasing and
distinct (`Store.Scoped`), and the woken list and the remaining wakeups
partition the old ones. Every committed store is waiting again
(`Store.Waiting`: no pending suspension waits on a bound name), so a woken
suspension waits on a name this commit bound, and every suspension none of
whose names it bound stays.

Binding a name to another flexible name wakes the goals waiting on the first;
they resolve the alias when asked again and delay on the second if it is still
unbound. Moving the wakeups to the second name instead is an optimisation the
semantics does not need.

### Restrictions and constraints

Two different things are attached to names, and only one of them can block
success.

- **Restrictions are persistent invariants.** A dependency set is one: a
  flexible name's answer may mention only the rigid names it depends on. The
  commit checks it on every binding and rejects a violation. It stays attached
  after the name is bound and is never residual: it has no proof obligation
  left, so it never blocks success or causes floundering.
- **Constraints are unresolved obligations.** A wakeup is re-asked through the
  command and produces a proof. A constraint in `Store.constraints` is a
  condition the store tracks until its solver discharges it with evidence:
  disequalities, constructive-negation answers in S10, or the under-determined
  case of a type check. Each needs a decidable check at each binding, a rule
  for when it is discharged, and its own evidence for proof export, specified
  with the solver that introduces it. S18 adds the slot and no solver: commits
  keep constraints unchanged, and no transition adds one.

Success requires no pending wakeup and no unresolved constraint
(`Store.residual` is empty); restrictions are not counted.

### Transitions

| Focus | Condition | Next state |
| --- | --- | --- |
| `solve ob` | `delay names`, valid | Suspend `ob` under the id `nextHole` (`Store.suspend`); focus `proved (deferred id ob)`; increment `nextHole`. The enclosing frame continues as if `ob` were proved (`step_delay`) |
| `solve ob` | `delay names`, invalid | `failed`, contract gap (`step_delay_invalid`) |
| `solve ob` | A candidate's commit returns woken suspensions | They run oldest first, before the candidate's own continuation, each under its own scope with a `woken` continuation (`Continuation.schedule`, `State.enter_committed`, `State.enter_oldest_first`) |
| `proved t` | Top continuation `woken id ob next` | Record `(id, ob, t)` in `deferred`; focus `next` (`step_woken`) |
| `proved t` | No continuation, `Store.residual` empty | Success: the references in `t` are filled with the deferred proofs (`ProofTree.fillAll`) |
| `proved t` | No continuation, pending wakeups or unresolved constraints | One `floundered` gap per residual item; focus `failed` (`step_flounder`) |
| `failed` | A choice point with alternatives | Restore its store (with its suspensions), continuations, and deferred proofs; `nextHole` and gaps are kept (`step_backtrack`) |

A woken goal may delay again: it gets a new id, and its record holds a
reference to the new one. Bindings a woken goal commits are checked against its
own scope's rigid names and the store's dependencies, exactly as for any
obligation.

A suspension outlives the frame that created it. When the callee's frame
completes and its node returns to the caller, the suspension stays in the store
(`step_proved_store`), and the caller's later goals can wake it. The woken
obligation keeps its own scope: assumptions and rigid names that were in scope
where it delayed are available to its proof, and nothing from that scope
reaches the caller, since the woken entry resumes the focus it saved
(`step_woken`, `Linked.woken`).

Floundering abandons the branch without evidence. Its gaps survive backtracking,
so the run ends in another success or in `unknown`, never in `exhausted`
(`run_not_exhausted`). A floundered goal is never NAF evidence: it carries no
certificate, and `unknown` carries no evidence either way.

### Proof evidence: fill at the end

A delayed obligation's proof is built after its place in the tree has already
been passed, so while the run builds the tree it holds a reference and the proof
is recorded separately. The success step fills the references before it returns
the proof: `ProofTree.fill` replaces each reference by its record once, and
`fillAll` repeats it once per record. `CompletedProof.tree` is therefore the
complete proof, with no reference. `CompletedProof.deferred` keeps the records
as provenance: each delayed obligation's proof under its distinct id, as
recorded when it woke, so a record may still reference later records. The
completed tree carries no ids, so it does not say where each record was used.

A deferred proof only references delays created after its own goal woke, so
references are acyclic, and substituting all records once per record resolves
every chain. Coherence carries through: a reference stands for exactly the
premise obligation it replaced, and each record proves the obligation it was
recorded for. The branch invariant gives exactly what filling needs: record
ids are distinct, every reference resolves to a record for the same
obligation, and a record references only records with larger ids. From these,
`ProofTree.fillAll_complete` proves that the filled tree proves what the tree
proves, coherently, names only declared names, and holds no reference.

Because the completed tree holds every delayed obligation's proof, its rules
and closed-world evidence include theirs: a delayed NAF goal's certificate is
in the tree. A reference retains no evidence of its own, so a tree with
references is never `Monotonic`; a successful run's tree is monotonic exactly
when it retains no closed-world evidence (`CompletedProof.Valid.monotonic_iff`).

## Guarantees

| Property | Theorem |
| --- | --- |
| A valid delay suspends the focused obligation on declared, unbound flexible names; any other delay is a contract gap | `Store.delayable_spec`, `step_delay`, `step_delay_invalid` |
| Exactly-once wakeup: a commit returns each woken suspension once, removes it from the store with no stale attachment, keeps every suspension none of whose names it bound, and leaves a waiting store | `Store.commit_wakes` |
| `Store.Scoped` extends to wakeups and constraints: they wait only on declared flexible names, and wakeups are kept newest first, with strictly decreasing ids | `Store.Scoped`, `Store.Scoped.distinct`, `Store.commit_scoped`, `Store.Scoped.suspend` |
| Every transition keeps every branch valid (`Branch.Valid`, for the state and each choice point): continuations linked, a `woken` entry's `next` valid for the stack below it, the store scoped and waiting, every suspension, constraint, and deferred proof naming only declared names (S19), every deferred proof proving its obligation | `State.init_valid`, `step_valid` |
| Every suspension id is held exactly once (a pending wakeup, a woken continuation, or a deferred proof) and below `nextHole`; every reference stands for a held id with its obligation; references point forward | `Accounted`, `Branch.Valid.commit`, `Branch.Valid.record` |
| A success proves the root with a coherent, declared tree and scoped answers; the success step filled every reference, so the tree holds none; no wakeup is pending and no constraint unresolved (restrictions do not count); the deferred proofs, kept as provenance, have distinct ids, each proves its recorded obligation, and the references left in them resolve to later records | `run_success` (`CompletedProof.Valid`), `ProofTree.fillAll_complete` |
| Floundering adds gaps, so exhaustion still implies no gap, and a floundered run is never exhausted | `step_flounder`, `run_exhausted`, `run_not_exhausted` |
| Woken goals run before the waking candidate's continuation, oldest first: the woken list is newest first, and scheduling pushes one woken entry per suspension in reverse, so from the top of the stack their ids increase and the focus is the oldest woken obligation | `Store.commit_woken`, `Continuation.schedule_stack`, `Continuation.schedule_focus`, `State.enter_oldest_first` |
| A suspension outlives its frame; a woken goal's proof is recorded under its id and the saved focus resumes | `step_proved_store`, `step_woken` |
| Rollback restores the store with its suspensions and the deferred proofs; ids are not reused | `step_backtrack` |
| Rule frames complete exactly once, as before | `step_waiting`, `step_complete`, `Frame.feed_exact` |

## Effects on later tickets

- **S06** ([implemented](machine-positive.md)): a range guard on an unbound
  variable delays instead of enumerating ahead of the body (`positive_guard`).
  The generated `fill` or member goal is appended after the body and enumerates
  by ordinary candidates. Reconstruction reads `CompletedProof.tree`, already
  complete (`run_reconstructs`).
- **S07**: P0 is ground and never delays.
- **S08**: machine output has no reference, so the completed tree is what it
  encodes, and the records need no encoding. A supplied tree (manual, external,
  P2) that still holds a reference is an unresolved hole and is rejected.
- **S10**: NAF on a flexible operand delays until the operand is bound ("retain a
  dependency and retry after instantiation"). Waiting cannot help a rigid
  operand.

## Boundaries

- Commands decide when to delay (S06 for guards, S10 for NAF); the machine
  checks the names and owns waking, recording, and floundering.
- No constraint solver: S18 adds the slot only.
- The test driver is not S06's command set. S06 rebuilds `Derives` from a
  completed tree read through the final answers ([S06](machine-positive.md));
  S16 composes it through elaboration.
- No fairness or termination is claimed: woken goals run oldest first, before
  the waking candidate's continuation.

## Traces

In these traces `r` is a check that delays while its first argument is an
unbound flexible name and otherwise holds by an assumption; `naf r(...)` delays
the same way. Each is a `#guard` in
[Tests/Resolution/Delay.lean](../Tests/Resolution/Delay.lean).

| Trace | Expected |
| --- | --- |
| `r(X) ∧ p(X)` under `p(a), r(a)` | `r(X)` delays; `p(X)` binds `X := a` and wakes it; `r(a)` holds. Its proof is recorded under id 0 and filled in at success: the completed tree has no reference and lists the woken goal's rule |
| Same, under `p(b), p(a), r(a)` | `X := b` wakes `r(b)`, which fails; rollback restores the suspension; `X := a` succeeds |
| `r(X) ∧ p(X) ∧ q(X)` under `p(a), p(b), r(a), r(b), q(b)` | `X := a` wakes `r(a)`, whose proof is recorded; `q(a)` fails; rollback discards that record and restores the suspension; `X := b` succeeds with exactly one deferred proof, for `r(b)` |
| `r(X, Y) ∧ p(X) ∧ q(Y)` under `p(a), r(a, b), r(a, c), q(c)` | `p(X)` wakes `r(a, Y)`, which binds `Y := b`; its proof is recorded and `q(b)` fails; backtracking resumes the woken goal's own alternative `Y := c` with the woken entry restored and the record discarded |
| `r(X) ∧ r(Y) ∧ q(X, Y)` under `q(a, b), r(a), r(b)` | Both delay; `q` wakes both, the oldest first; two deferred proofs |
| A check delaying on `[X, Y]`, then a goal binding `X` only | Woken once; no stale attachment on `Y`; success without floundering |
| A check delaying on `[X, Y]`, then a goal binding `X` and `Y` in one commit | Woken once; one deferred proof |
| Commits on a store with suspensions on `[X, Y]` and on `Z` | Binding `X`, or `X` and `Y`, returns the first once and keeps the second |
| `r(X) ∧ e(X, Y) ∧ p(Y)` under `p(a), r(a)`, where `e` binds `X := Y` | The alias wakes `r(X)`, which resolves to `r(Y)` and delays again under a new id; `p(Y)` binds `Y := a` and wakes it. Two records, the first referencing the second; the completed tree has no references |
| A callee `c(X)` (a test-driver clause; S06 supplies clause selection) whose body delays `r(X)`, then the caller's `p(X)` | `c`'s frame completes with `r(X)` suspended; the caller's `p(X)` binds `X := a` and wakes `r(a)` after the callee returned |
| `(r(a) → r(X)) ∧ p(X)` under `p(a)` | `r(X)` delays under the local assumption `r(a)`; after the implication is discharged, `p(X)` wakes it and `r(a)` holds by that assumption |
| `(r(a) → r(X)) ∧ p(X) ∧ r(a)` under `p(a)` | Exhausted: the woken goal used `r(a)`, but the caller's last goal cannot |
| `r(X)` alone | Flounders: unknown with a `floundered` gap |
| `r(X) ∨ (r(X) ∧ p(X))` under `p(a), r(a)` | The first branch flounders; the second succeeds; resuming is unknown |
| A store holding an unresolved constraint, goal `true` | Flounders: unknown with a `floundered` gap |
| `r(X) ∧ p(X)` with no `p` | Exhausted: the suspension is discarded with its branch |
| `naf r(X) ∧ p(X)` under `p(a)` | `naf r(X)` delays; `p(X)` wakes it and its NAF node keeps the certificate in the deferred proof, which the success step fills in: the completed tree retains the certificate |
| `∀x. (r(x) → ∃y. (r(y) ∧ y = x))` | Success: `y` keeps its dependency set after binding, and restrictions never flounder |
| `delay []`, a delay on a rigid, undeclared, or bound name | Contract gap |
