# Machine states, continuations, and proof evidence

[Machine](../AnthillModKbSpec/Resolution/Machine.lean) implements S04 over the
existing `Term`, `ProofContext`, and `HornClause` representations. It defines one
abstract machine for every profile: the state, its continuations and choice
points, the shared answer store, the proof trees built by successful commands,
and the outcomes of a run. It does not choose clauses, match terms, or decide
when to stop. Concrete commands supply those choices (S05 matching, S06 positive
execution, S07 P0 evaluation); the machine checks their names and bindings and
owns completion and rollback.

| Module | Contents |
| --- | --- |
| [Store](../AnthillModKbSpec/Resolution/Machine/Store.lean) | Rigid and flexible names with dependencies, triangular answer bindings, scopes and obligations, binding and commit checks, the `Scoped` invariant |
| [Evidence](../AnthillModKbSpec/Resolution/Machine/Evidence.lean) | Rule identities and parameters, proof trees, scope coherence, completed proofs, evidence classes |
| [State](../AnthillModKbSpec/Resolution/Machine/State.lean) | Candidates, frames, choice points, gaps, `step`, `run`, the machine invariant and its theorems |
| [Commands](../AnthillModKbSpec/Resolution/Machine/Commands.lean) | Named command contracts for the logical rules and their `Derives` completion lemmas |
| [Monotonicity](../AnthillModKbSpec/Foundation/Monotonicity.lean) | `Derives.mono`: KB growth preserves derivations whose NAF evidence transfers |

## State

```text
State = snapshot, root obligation, store, focus, frames, choices, gaps
Obligation = Scope; goal          Scope = rigid names, assumptions
Focus = solve(obligation) | proved(tree) | failed
```

| Component | Meaning |
| --- | --- |
| `Obligation` | `Gamma; Scope ⊢ goal`. The goal may mention flexible names and is read through the final answer bindings |
| `Scope` | The obligation's own local assumptions and the rigid names opened on its path |
| `Premise`, `Discharge` | A premise goal and what it adds to the parent scope: assumptions and rigid names discharged at the parent's node |
| `Store.names` | Every declared name: rigid (the query's parameters, eigenvariables, opened existential witnesses) or flexible (answer metavariables) with its dependencies |
| `Store.bindings` | Triangular, newest first. Each right-hand side was resolved against the older bindings when committed |
| `Frame` | A partially completed rule application: parent obligation, rule, proved premises with their subproofs in order, the current premise, pending premises. This is the AND continuation |
| `ChoicePoint` | Remaining candidates for an obligation, with the store and frames to restore. This is the OR continuation |
| `gaps` | Paths abandoned without evidence. Not restored on backtracking |

A premise's obligation is computed from its parent's scope alone
(`Obligation.premise`): `Scope.enter` prepends the premise's assumptions and
rigid names. Nothing a sibling assumes or opens reaches it.

`State.init snapshot flexibles context goal` declares every free name of the
query: the given answer names as flexible, depending on the query's
parameters, and all other free names as those rigid parameters.

### Dependencies instead of levels

A flexible name records the rigid names its answer may mention: those in scope
where it was created. Placing a flexible name inside another name's answer
narrows its dependencies to that name's. This is the exact form of universe
levels (Qi §4.2). A level number orders nested scopes, but two sibling scopes of
the same depth share a level, so a witness created under one `∀` branch could be
bound to the other branch's eigenvariable. A dependency set refuses that binding.

There is no live KB in the state. `snapshot` names the program, registry, and
context the commands were built for; closed-world nodes are relative to it.

## Commands and candidates

A command maps the focused obligation and the store to a `Response`:

| Response | Meaning |
| --- | --- |
| `candidates (e :: rest)` | OR alternatives. `e` is tried now; `rest` is saved with the current store and frames |
| `candidates []` | A miss on this path. The newest choice point resumes |
| `unsupported` | No capability for this focus. The path is abandoned and recorded as a gap, never as failure |

Each candidate (`Expansion`) fixes a rule application and its explicit
parameters, the fresh flexible names it introduces, the answer bindings it
commits, and its premises. All premises must be proved; they are an AND list.

### Commit checks

`Store.commit` checks the candidate's names, declares its flexible names
depending on the obligation's rigid names, declares its premises' rigid names,
then binds each proposed answer.

| Check | Failure |
| --- | --- |
| New names are distinct, undeclared, and absent from the obligation's free and binder names (`Obligation.names`) | `violated` |
| The obligation's rigid names are declared rigid | `violated` |
| The bound name is a declared, still unbound flexible name | `violated` (a rigid is never assigned; an answer is never rebound) |
| Every name in the value is a rigid name of this scope or an unbound flexible name | `violated` (the value must be resolved and in scope) |
| Occurs check: the bound name is not in the value | `rejected` |
| Every rigid name in the value is a dependency of the bound name | `rejected` |

Binding a name to itself changes nothing. On success, the flexible names in the
value are narrowed to the bound name's dependencies. `rejected` is an ordinary
candidate miss. `violated` means the command broke the machine contract; the
candidate is abandoned and the obligation recorded as a `contract` gap.
`Store.freshFor` picks a name that passes the freshness check.

### Transitions

| Focus | Condition | Next state |
| --- | --- | --- |
| `solve ob` | `candidates []` | `failed` |
| `solve ob` | `candidates (e :: rest)`, commit `rejected` | `failed`, with `rest` saved |
| `solve ob` | commit `violated` | `failed`, contract gap, `rest` saved |
| `solve ob` | committed, `e` has no premises | `proved (node e.rule ob [] [])` |
| `solve ob` | committed, premises `p :: ps` | push frame, focus `solve (ob.premise p)` |
| `solve ob` | `unsupported` | `failed`, unsupported gap |
| `proved t` | no frames | finished: `success`, with a resume state |
| `proved t` | top frame has pending premises | frame records `t`, focus its next premise; the store is unchanged |
| `proved t` | top frame has no pending premise | frame removed, focus `proved (node rule parent premises subproofs)` |
| `failed` | a choice point with alternatives | restore its store and frames, try the next alternative |
| `failed` | no choice point | finished: `exhausted` if there are no gaps, otherwise `unknown gaps` |

`run` takes a step budget; running out of it is `interrupted`.

## Guarantees

| Property | Theorem |
| --- | --- |
| An AND parent completes exactly once, after all its premises: `step` passes each returning subproof to `receive`; fewer subproofs leave the frame waiting, exactly one per premise completes it, more are refused | `step_waiting`, `step_complete`, `Frame.feed_partial`, `Frame.feed_exact`, `Frame.feed_overfull` |
| Every transition keeps every frame, focus, and choice point linked to the obligation it continues, and every store scoped, whatever the command answers | `State.init_valid`, `step_valid` |
| A successful run proves the root obligation, each subproof proves exactly its premise under the parent scope extended only by that premise, and the final answers are scoped | `run_success`, `ProofTree.CoherentPremises.subproof_context` |
| AND siblings share answers in sequence: a sibling starts from the store the previous one left, commits only add the candidate's bindings, and a bound answer is never rebound | `step_proved_store`, `Store.commit_extends`, `Store.bind_bound` |
| OR alternatives start from the saved store: bindings of a failed alternative are discarded | `step_backtrack`, `State.enter_store` |
| Opened names avoid the obligation's free and binder names, which gives the freshness `Derives` checks | `Store.commit_fresh`, `Obligation.fresh_of_not_mem_names` |
| `Store.Scoped`: every answer mentions only rigid names among its name's dependencies, and flexible names whose dependencies are among them | `Store.commit_scoped`, `Store.Scoped.answer_rigid` |
| A rigid name a commit opens is never a dependency of a flexible name that already existed, so it never enters that name's answer | `Store.commit_no_escape`, `Store.bind_respects_scope` |
| Only `success` carries a proof; exhaustion is reported only when no state of the run recorded a gap | `Outcome.proof?_eq_some`, `run_exhausted` |
| Resolution by the committed bindings is a chain of capture-avoiding substitutions | `Store.resolve?_sound` |

Local assumptions cannot escape because no transition copies a child's scope
into its parent: the parent's node is built from the frame's stored obligation.
Rigid names and opened existential witnesses cannot escape through answers:
an opened name is fresh, so no existing flexible name depends on it, and
dependencies only narrow. `Scoped` covers each committed binding and the
dependencies of the flexible names in it; S05 proves the resulting property of
fully resolved answers together with its matcher.

## Proof evidence

A `ProofTree` node records its rule application (`RuleApp`), the obligation it
proves (scope, context, and conclusion), the premises the rule required, and one
subproof per premise in order. Coherence (`ProofTree.Coherent`) states that each
subproof proves its premise's obligation. There is no hole constructor; frames
are the only partial nodes and are never exported.

`RuleApp` names one `Derives` rule or an `extension` and carries the parameters
that the conclusion and premises do not determine:

| Rule | Recorded parameters |
| --- | --- |
| `forallIntro`, `existsElim` | The eigenvariable (opened rigid name) |
| `forallElim`, `existsIntro` | The witness term (for a goal, a fresh flexible name read through the answers) |
| `clause`, `goalClause` | The clause template and its finite instantiation |
| `equalSubst` | The replaced name and template |
| `defaultNegIntro` | The certificate of the operand's complete failure |
| `extension` | A rule name in the symbol namespace, term parameters, and the closed-world evidence (kind and certificate) it uses, if any |
| Other `Derives` rules | None; premises and conclusion determine them |

Discharged assumptions and rigid names are each premise's `Discharge`.
`RuleApp.id` gives the rule identity alone. A `CompletedProof` holds the snapshot,
the root obligation, the tree, and the final store; `answer?` reads a root name
through the bindings. Together these are what S08's Term encoding and checker
need. Exporting a proof replays no search.

### Monotonic and snapshot-indexed evidence

Closed-world nodes retain the certificate the command produced
(`ClosedWorldEvidence`: kind and certificate). The `Certificate` type is a
parameter of the machine: S07 and S10 define the certificates and S08 checks
them, so exporting a proof never recomputes a failure or a cover. A tree carries
no snapshot of its own. Every certificate is relative to the snapshot of the run
that built it, recorded once in `CompletedProof.snapshot`, so a tree cannot mix
evidence from two snapshots.

| Class | Rules | Validity under growth |
| --- | --- | --- |
| Monotonic | Assumption, every logical rule, clause and goal-clause applications, including generated signature clauses | Survives KB growth (`Derives.mono`, `Derives.positive_mono`) and registry growth (`Elaboration.signatureKb_mono`) |
| Snapshot-indexed | `defaultNegIntro`; extensions using closed-world evidence: complete failure, finite absence, enumeration | Valid only for the run's snapshot. `GroundSearch.failureEvidence` names its exact KB and context (`groundFailure_exact`, `groundFailure_stale`) |

`RuleApp.evidenceClass` classifies one node; `ProofTree.closedWorld` lists the
closed-world evidence a tree retains, and `ProofTree.Monotonic` means there is none.
An extension's class is the one it declares: `Derives.mono` covers only
`Derives` rules, so S08 must prove that an extension declared monotonic
survives growth. Lowered formulas carry no snapshot dependency: elaboration
reads only the signature naming.

## Outcomes

| Outcome | Meaning |
| --- | --- |
| `success proof resume` | A coherent tree for the root obligation, the final store, and a state from which search resumes for further answers |
| `exhausted` | Every alternative of this command strategy was tried, and no path was abandoned. Not complete failure (P0 needs `GroundSearch.Fails`, S07), non-derivability, or refutation |
| `unknown gaps` | Some path was abandoned for lack of capability or a contract breach. No evidence either way |
| `interrupted state` | The step budget ran out |

## Named command contracts

Each contract fixes one candidate. Concrete commands decide when to offer which.
`Expansion.Sound` states the completion contract: derivations of all premises in
their own scopes give a derivation of the obligation. It is proved for every
contract below, for candidates without answer bindings; reconstruction under
committed bindings belongs to S05/S06.

| Contract | Focus | Premises and scope effects | Sound by |
| --- | --- | --- | --- |
| `truth` | `true` | None | `truth_sound` |
| `assumption bindings` | A goal in the scope's assumptions after `bindings` | None | `assumption_sound` |
| `conjIntro a b` | `a ∧ b` | `a`, `b` in the parent scope, sharing answers | `conjIntro_sound` |
| `disjLeft a`, `disjRight b` | `a ∨ b` | One disjunct; the other is a separate alternative | `disjLeft_sound`, `disjRight_sound` |
| `disjElim a b g` | `g` | `a ∨ b`; `g` assuming `a`; `g` assuming `b` | `disjElim_sound` |
| `impIntro a b` | `a → b` | `b` assuming `a` | `impIntro_sound` |
| `impElim a g` | `g` | `a → g`; `a` | `impElim_sound` |
| `falsityElim` | any `g` | `false` | `falsityElim_sound` |
| `forallIntro x body e` | `∀x. body` | `body[e/x]` with fresh rigid `e` | `forallIntro_sound`, from `e ∉ Obligation.names` |
| `existsIntro x body w` | `∃x. body` | `body[w/x]` with fresh flexible `w` depending on the scope's rigid names | `existsIntro_sound`, from `w ∉ Obligation.names` |
| `existsElim x body e g` | `g` | `∃x. body`; `g` assuming `body[e/x]` with fresh rigid `e` | `existsElim_sound`, with freshness for the opened body |

## Traces

[Tests/Resolution/Machine.lean](../Tests/Resolution/Machine.lean) runs the
machine with a test driver for logical connectives and atomic assumptions; each
outcome is checked by `#guard`.

| Trace | Result |
| --- | --- |
| `p ∧ q` under `p, q` | One `conjIntro` node with two assumption leaves |
| `p ∨ q` under `q` | `disjLeft` misses, rollback, `disjRight` succeeds |
| `p(X) ∧ q(X)` under `p(a), p(b), q(b)` | `X := a` fails at `q(a)`; rollback discards it; answer `X = b`; resuming is exhausted |
| `p(X)` under `p(a), p(b)` | Answers `a`, then `b` on resume, then exhausted |
| `p → (q → p ∧ q)` | Two nested discharges; both leaves see `q, p` |
| `(p → p) ∧ p` | Exhausted: the first conjunct's assumption does not reach the second |
| `q ∨ p` under `p ∨ q` | `disjElim` with cases proved under `p` and under `q` separately |
| `p(X) ∧ q(X)` under `p(a), q(b)` | Incompatible shared answer: exhausted, no proof tree |
| A command rebinding `X` | Refused by the store; recorded as a gap, outcome unknown |
| `∃y. (p(y) → p(y))`, `X = X`, a command binding `X := X` | Success: self-binding is no change |
| `∀x. ∃y. y = x` / `∃y. ∀x. y = x` | Success / exhausted by the dependency check |
| `∀x. X = x` with answer `X` | Exhausted: a root answer cannot capture an opened rigid name |
| `(∃x. p(x)) → ∃y. p(y)` / `∃y. ((∃x. p(x)) → p(y))` | Success through `existsElim` / exhausted: the opened witness cannot become an earlier name's answer |
| `(∀x. ∃y. true) ∧ (∀z. true)`, a command binding `y := z` | Refused; success without the binding. A level number would accept it |
| `p(1) → ∀x. p(x)` | Exhausted: the free name 1 is a declared parameter, so opening `∀x` does not reuse it |
| `naf p`; `naf q ∨ p` under `p` | Unknown; success, then unknown on resume (the gap persists) |
| `p ∧ naf q` under `p`, with a command producing a toy certificate | Success; the NAF node retains its certificate, read back from `ProofTree.closedWorld` |
| Small budget | Interrupted |
| A command binding a rigid name, or opening a name free in the obligation | Contract gap, outcome unknown |

The `#guard` checks evaluate compiled code; the kernel cannot reduce the existing
well-founded `Term.freeVars` and `Term.instantiate?`. The generic theorems above
hold for every command and need no trace.

## Boundaries

- The machine does not compare terms. Commands resolve goals against the store
  before matching (`Store.resolve?`); the machine refuses unresolved values and
  rebinding.
- `Store.resolve?` refuses capture hazards; `none` asks for alpha-renaming, which
  S05 provides. It is never failure: the test driver reports such a focus as
  unsupported.
- The test driver is not the S05 matcher or the S06 command set. In particular,
  it does not reconstruct `Derives` for answers; `Expansion.Sound` covers only
  binding-free candidates.
- Residual constraints, solver jobs, and checked success evidence (S08) are not
  part of this state.
- No termination, fairness, or completeness is claimed. `exhausted` and
  `unknown` carry no negative evidence.
