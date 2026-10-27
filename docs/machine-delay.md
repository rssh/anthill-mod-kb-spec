# Delayed goals in the machine

Status: design for S18, not implemented. The S04 [machine](machine-state.md) has
no delay: a command can offer candidates, miss, or report a gap, and goal order
is fixed by the premise order of each candidate.

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
goals of the caller after the clause returns. Reordering a clause body (the S06
fallback) therefore does not cover it. The machine needs suspension across the
whole remaining resolvent, as in Prolog's `freeze` and λProlog's suspended
goals.

Enumeration over a domain is not delay: it is an ordinary list of candidates
with a choice point.

## Design

### Response

A command may answer `delay names`: the focused obligation cannot proceed until
one of `names` is bound. Every name must be a declared, unbound flexible name,
and the list must be nonempty; otherwise the answer breaks the contract and is
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
| `Store.wakeups` | Pending suspensions, one entry per id, each listing the names it waits on |
| `Store.constraints` | Unresolved constraints on flexible names (below) |
| `Commit.committed store woken` | A commit also returns the suspensions it woke, removed from the new store |
| `DeferredProof` | An id, the delayed obligation, and the tree that proved it after waking |
| `State.deferred` | Proofs of woken suspensions; saved by choice points, restored on backtracking |
| `State.nextHole` | Counter for ids; not restored, so ids are unique across the run |
| `ProofTree.deferred id obligation` | A reference, in a tree, to the separately recorded proof of a delayed obligation |
| `Continuation.woken id obligation next` | On the continuation stack, beside rule frames: record the woken goal's proof under `id`, then resume `next` |

Deferred proofs stay out of the store: the store is the logical state the
matcher (S05) reads and commits to, while deferred proofs are evidence for
export (S08).

A suspension is attached to every name it waits on, but it is one entry keyed
by its id, not a copy per name; a per-name index is only a view of it. A commit
wakes each suspension at most once: binding any one of its names removes the
entry, so no stale attachment remains on its other names, and binding several
of its names in one commit returns it once. Wakeup ids in the store are
distinct, and the woken list and the remaining wakeups are disjoint.

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
  with the solver that introduces it. S18 adds the slot and no solver.

Success requires no pending wakeup and no unresolved constraint; restrictions
are not counted.

### Transitions

| Focus | Condition | Next state |
| --- | --- | --- |
| `solve ob` | `delay names`, valid | Suspend `ob` under a fresh id; focus `proved (deferred id ob)`. The enclosing frame continues as if `ob` were proved |
| `solve ob` | `delay names`, invalid | `failed`, contract gap |
| `solve ob` | A candidate's commit returns woken suspensions | They run oldest first, before the candidate's own continuation, each under its own scope with a `woken` continuation |
| `proved t` | Top continuation `woken id ob next` | Record `(id, ob, t)`; focus `next` |
| `proved t` | No continuation, no pending wakeup or unresolved constraint | Success |
| `proved t` | No continuation, pending wakeups or unresolved constraints | One `floundered` gap per residual item; focus `failed` |

A woken goal may delay again: it gets a new id, and its record holds a
reference to the new one. Bindings a woken goal commits are checked against its
own scope's rigid names and the store's dependencies, exactly as for any
obligation.

A suspension outlives the frame that created it. When the callee's frame
completes and its node returns to the caller, the suspension stays in the store,
and the caller's later goals can wake it. The woken obligation keeps its own
scope: assumptions and rigid names that were in scope where it delayed are
available to its proof, and nothing from that scope reaches the caller.

Floundering abandons the branch without evidence. Its gaps survive backtracking,
so the run ends in another success or in `unknown`, never in `exhausted`.

### Proof evidence: fill at the end

A delayed obligation's proof is built after its place in the tree has already
been passed, so the tree holds a reference and the proof is recorded separately.
On success, `CompletedProof` keeps the tree and the deferred proofs, and
`CompletedProof.filled` substitutes the references.

A deferred proof only references delays created after its own goal woke, so
references are acyclic, and substituting all records once per record resolves
every chain. Coherence carries through: a reference stands for exactly the
premise obligation it replaced, and each record proves the obligation it was
recorded for. S08's checker verifies that every reference resolves to a record
for the same obligation and that references are acyclic.

### Invariants to prove

- `State.Valid` extends to the new continuation: a `woken` entry continues the
  obligation it records, and its `next` focus is valid for the stack below it.
- `Store.Scoped` extends to wakeups: each waits only on declared flexible names,
  and wakeup ids are distinct.
- Exactly-once wakeup: a commit returns each woken suspension once, removes it
  from the store, and keeps every suspension none of whose names it bound.
- Every deferred proof is coherent and proves its recorded obligation.
- A success has no pending wakeup and no unresolved constraint. Restrictions,
  including dependency sets, do not count.
- `run_exhausted`: floundering adds gaps, so exhaustion still implies no gap.
- The existing theorems (`run_success`, scope and dependency invariants,
  rollback, completion exactly once) hold unchanged for rule frames.

### Effects on later tickets

- **S06**: a range guard on an unbound variable delays instead of enumerating
  ahead of the body. The generated `fill` or member goal is appended after the
  body. Reconstruction substitutes deferred proofs before rebuilding `Derives`.
- **S07**: P0 is ground and never delays.
- **S08**: encode references and deferred proofs; check resolution, agreement,
  and acyclicity.
- **S10**: NAF on a flexible operand delays until the operand is bound ("retain a
  dependency and retry after instantiation"). Waiting cannot help a rigid
  operand.

## Traces for the implementation

| Trace | Expected |
| --- | --- |
In these traces `r` is a check that delays while its argument is an unbound
flexible name and otherwise holds by an assumption `r(t)`.

| Trace | Expected |
| --- | --- |
| `r(X) ∧ p(X)` under `p(a), r(a)` | `r(X)` delays; `p(X)` binds `X := a` and wakes it; `r(a)` holds. The filled tree has no references |
| Same, under `p(b), p(a), r(a)` | `X := b` wakes `r(b)`, which fails; rollback restores the suspension; `X := a` succeeds |
| `r(X) ∧ p(X) ∧ q(X)` under `p(a), p(b), r(a), r(b), q(b)` | `X := a` wakes `r(a)`, whose proof is recorded; `q(a)` fails; rollback discards that record and restores the suspension; `X := b` succeeds with exactly one deferred proof, for `r(b)` |
| `r(X) ∧ r(Y) ∧ q(X, Y)` under `q(a, b), r(a), r(b)` | Both delay; `q` wakes both; two deferred proofs |
| A check delaying on `[X, Y]`, then a goal binding `X` only | Woken once; no stale attachment on `Y`; success without floundering |
| A check delaying on `[X, Y]`, then a goal binding `X` and `Y` in one commit | Woken once; one deferred proof |
| `r(X) ∧ e(X, Y) ∧ p(Y)` under `p(a), r(a)`, where `e` binds `X := Y` | The alias wakes `r(X)`, which resolves to `r(Y)` and delays again under a new id; `p(Y)` binds `Y := a` and wakes it. Two records, the first referencing the second; the filled tree has no references |
| A callee `c(X)` (a test-driver clause; S06 supplies clause selection) whose body delays `r(X)`, then the caller's `p(X)` | `c`'s frame completes with `r(X)` suspended; the caller's `p(X)` binds `X := a` and wakes `r(a)` after the callee returned |
| `(r(a) → r(X)) ∧ p(X)` under `p(a)` | `r(X)` delays under the local assumption `r(a)`; after the implication is discharged, `p(X)` wakes it and `r(a)` holds by that assumption |
| `(r(a) → r(X)) ∧ p(X) ∧ r(a)` under `p(a)` | Exhausted: the woken goal used `r(a)`, but the caller's last goal cannot |
| `r(X)` alone | Flounders: unknown with a `floundered` gap |
| `r(X) ∧ p(X)` with no `p` | Exhausted: the suspension is discarded with its branch |
| A successful answer whose names carry dependency sets | Success: restrictions never flounder |
| `delay []`, or a delay on a rigid name | Contract gap |
