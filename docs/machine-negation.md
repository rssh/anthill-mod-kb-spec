# Evidence-first NAF by refutation in the completion

S10 gives NAF on operands with rigid parameters a sound evidence route. The
evidence for `naf G` is a refutation of `G` in the program's Clark completion,
checked by the [S08 proof checker](proof-checking.md). The search for it runs
on the shared machine with the [S09 left rules](machine-left.md) and the dual
rules of negation. A NAF goal first uses what is assumed or derivable. A
flexible operand waits, and a rigid operand is refuted for every value of its
parameters. Traces are in
[Tests/Resolution/Negation.lean](../Tests/Resolution/Negation.lean).

| Module | Contents |
| --- | --- |
| [Foundation/Derivation](../AnthillModKbSpec/Foundation/Derivation.lean) | `Derives.defaultNegIntro` without the closed-operand premise |
| [Foundation/Semantics](../AnthillModKbSpec/Foundation/Semantics.lean) | `Model.FailureAdequate`: evidence makes `naf G` true in every environment satisfying the context |
| [Foundation/Completion](../AnthillModKbSpec/Foundation/Completion.lean) | The only-if clauses (`onlyIf`), the free equality theory (`clash`, `injective`, `equality`), the completed program (`completed`), the signature a program needs (`Signature.of`), the reserved-marker check (`complete?`, `complete?_reserved`), the refutation provider (`refutation`) and its adequacy (`refutation_adequate`) |
| [P1/Refutation](../AnthillModKbSpec/Resolution/P1/Refutation.lean) | The NAF check (`refutationCheck`), the checker with refutation evidence (`refutationChecker`), and its soundness (`refutationChecker_sound`) |
| [Machine/Evidence](../AnthillModKbSpec/Resolution/Machine/Evidence.lean) | The S10 commands `Derived.onlyIfUse` and `Derived.equalJoin` |
| [Machine/Refutation](../AnthillModKbSpec/Resolution/Machine/Refutation.lean) | The commands' candidates and contracts (`Expansion.onlyIfUse_soundUnder`, `Expansion.equalJoin_soundUnder`), the refutation search `refuter`, `refuter_sound` |
| [P1/Derived](../AnthillModKbSpec/Resolution/P1/Derived.lean) | The commands' logical nodes (`Unfold.onlyIfUse`, `Unfold.equalJoin`) and their validity (`Unfold.*_proves`) |
| [P1/Negation](../AnthillModKbSpec/Resolution/P1/Negation.lean) | Evidence-first NAF (`Strategy.withRefutation`), positive witnesses first (`Strategy.withWitness`), the nested refutation run (`refute`), the strategy over a completed program (`nafByRefutation`), and their theorems |
| [ProofLayer](../AnthillModKbSpec/Resolution/ProofLayer.lean) | The refutation route as a proof-layer capability (`ProofLayer.refutation`, `Request.proofLayerIn`) |

## The rule

`Derives.defaultNegIntro` concludes `naf G` from evidence of the provider for
the context and `G`. It no longer requires `G` to be closed. A parameter of `G`
stands for every value, so the evidence must hold uniformly.
`Model.FailureAdequate` states this: evidence for `G` under a context makes
`naf G` true in every environment that satisfies the context. The existing
providers stay adequate. S07's ground provider relates only closed operands,
and a `CertifiedRefutation.Refutes` certificate is uniform.

Two readings of a rigid name were rejected. Reading it as a constant that
matches nothing, which is the eigenvariable reading of `not` in λProlog, is
unsound: with the fact `p(1)`, `p(a)` fails to match, yet `p(a)` holds when
`a` is `1`. Enumerating a finite domain is impractical and does not cover
infinite domains.

## The completion

For a predicate `p` of arity `n` with defining clauses `p(t̄ᵢ) :- Bᵢ`, the
only-if clause is:

```text
(∃ȳ₁. x̄ = t̄₁ ∧ B₁) ∨ … ∨ (∃ȳₖ. x̄ = t̄ₖ ∧ Bₖ) ∨ false  :-  p(x̄)
```

Here `ȳᵢ` are the names of the i-th clause, and `x̄` are fresh. A predicate
without clauses gets `false :- p(x̄)`. The free equality theory adds two kinds
of clause:
- `false :- f(x̄) = g(ȳ)` for each pair of distinct constructors;
- `xᵢ = yᵢ :- f(x̄) = f(ȳ)` for injectivity.

The completed program is the program together with these clauses. It is a
list of clauses, so the S08 checker checks derivations in it unchanged. Which
predicates are closed and which constructors are free is `Signature.of`'s:

- **Constructors are declared, never inferred.** An application symbol is a
  free constructor only when the caller declares it so, as the data
  signature's constructors are. A defined operation is not free: with
  `plus(zero) = zero`, a clash clause `false :- plus(x) = zero` would
  contradict the program and refute anything. Literals are always free.
- **Only predicates with atomic defining heads are closed.** A predicate that
  an S09 compound head (`p(a) ∧ q(a)`, `∀x. p(x)`, `r → p(a)`) or a `ho_apply`
  head may conclude stays open, since `definitions` sees only atomic heads. A
  head with a formula variable (`X :- B`, `∀x. x`, `X ∧ q`) or one that
  applies a predicate variable by `ho_apply` may conclude any predicate, and
  then none is closed (`headOpens`).
- **`ho_apply` is never closed.** Its atoms hold by the predicate they apply
  (`hoApplyIntro`, `hoApplyElim`).

That the intended model satisfies the completion and the equality theory is a
model hypothesis: the closed-world reading of the program, stated as concrete
clauses. Its consistency is not proved: cycles through NAF in clause bodies,
or a program equation between declared constructors, can make it
inconsistent, and then no model satisfies it.

**Open predicates.** A clause `p(x̄) :- UNKNOWN` keeps `p` open. `UNKNOWN` is
a marker with no clauses and no completion. The case it adds to `p`'s
completion is never refuted, so NAF of `p` stays a gap. `complete?` reports a
KB clause that may conclude a marker as invalid, by its position: one whose
head mentions a marker, also through a compound head or as the predicate a
`ho_apply` head applies, and, when a marker is used at all, one whose head may
conclude any predicate (`complete?_heads`). `complete?_reserved` proves that
no clause of an accepted completion concludes a marker atom: the generated
clauses conclude cases, equations, or falsity.

## Evidence and its check

The provider `refutation hoApplySymbol kb` relates a context and `G` exactly
when `Derives kb context (G → false)` holds positively. By `Model.sound`, it is
adequate in every model of the KB with complement NAF (`refutation_adequate`).
For a completed program, those are the models of the completion and the free
equality theory.

`refutationCheck` is the known terminating procedure. It checks the evidence
term as a proof of `G → false`, under the NAF node's own context, against the
same snapshot with NAF disabled. `refutationChecker` checks trees whose NAF
nodes carry such evidence, and `refutationChecker_sound` makes an accepted
tree true in every model of the snapshot with complement NAF.

Logical negation and NAF stay distinct. The evidence is a proof of `G → false`,
while the node concludes `naf G`, and the two agree only in models with
complement NAF. No contradiction elimination from `P` and `naf P` is added.

## The refutation search

`refuter` searches for a proof of `G → false` in the completed program. It is
the left strategy without a selection, plus the dual rules of negation. At a
falsity goal it tries, in order:

1. **Inversion**, committed: the first assumed conjunction or existential not
   yet split on the branch. The split is invertible and does not branch.
2. **A join**, committed: two assumed equations that, oriented, read `s = a`
   and `s = b`, give `a = b`. A join only adds a consequence, and a branch has
   finitely many joins because they add no new terms.
3. The left strategy's **closing candidates**, with each clash clause
   `false :- f(x̄) = g(ȳ)` offered only for an assumed equation between an `f`
   and a `g` term (`clashRelevant`), then **one progress step**: the first
   only-if use, replacing an assumed atom `p(s̄)` by its cases from `p`'s
   only-if clause, once per atom; else the newest disjunction split.

Only-if uses and disjunction splits only add consequences, so the search takes
one at a time and never tries them in another order. A disjunction branches
the search, so it is split only when no only-if use is left: unrelated
assumed disjunctions do not multiply a refutation that does not need them.

A rigid name is never given a value. The cases of `p(a)` keep the equation
`a = t`. A case closes only when it is contradictory for every `a`: through
the clash clauses, matched against the case's equations, or through joins of
the case equations to a clash.

| Command | Selected | Premises (added assumptions) | Reconstruction |
| --- | --- | --- | --- |
| `onlyIfUse` | an assumed atom `p(s̄)`, the only-if clause `cases :- p(x̄)` | the goal (`cases[s̄/x̄]`) | the clause node for the cases, then a cut on them |
| `equalJoin` | assumed equations `s = a` and `s = b`, each possibly flipped | the goal (`a = b`) | `equalTrans(equalSymm(s = a), s = b)`, with `equalSymm` for a flipped equation, then a cut |

Both commands are S09-style derived rules (`RuleApp.derived`): they
reconstruct `Derives` by existing rules (`*_soundUnder`) and export as S08
logical nodes (`exportDerived`, `Unfold.*_proves`). No new rule is checked.

## Evidence-first NAF

`Strategy.withRefutation check refute base` answers a goal that reads
`naf G`:

1. **Evidence first.** If the base has candidates, such as an assumed `naf G`
   that closes the goal by identity, they are the answer, and no refutation is
   searched.
2. **Flexible names delay.** If `G` or the context names an unbound flexible
   name, as read, the goal waits for its binding (`Response.delay`, S18).
   Delay comes first because a binding may make the refutation possible: in
   `naf p(X) ∧ r(X)` with `p(one)` and `r(two)`, `p(X)` cannot be refuted for
   every `X`, but `p(two)` can, once `r` binds `X`.
3. **Closing.** If the goal is still waiting when its branch is proved, the
   branch closes (`Store.close`, see [delayed goals](machine-delay.md)): the
   goal runs once more, and no name is bound from then on. The goal no longer
   waits, and the names it waited on are refuted generically, like rigid
   parameters. The answer leaves them unbound, standing for every value.
   Still not refuted, the goal is a gap; it is never NAF evidence without a
   refutation.
4. **Refutation.** Otherwise every free name is a rigid parameter, or the
   branch is closing. If `refute` finds evidence and `check` accepts it, a NAF
   node is offered with it. Otherwise the base answer stands, so the goal is a
   gap or a miss, never refuted.

`refute` runs `refuter` on `G → false`, within its fuel, with the context and
operand as read and their free names rigid. It exports the run as a proof
term. A run that is exhausted, unknown, or interrupted gives no evidence.
`nafByRefutation` puts this together over the left strategy and the completed
clauses, with `refutationCheck` as the check.

The NAF node is read the same in every later store, because rigid names are
never bound (`Store.read_rigid`) and a closing store binds nothing more
(`Store.Refines.resolve_closing`; both in `Store.read_stableNegation`). So the evidence checked when the node is
offered is still the evidence of the exported node, whose context and operand
are read through the final store (`Strategy.withRefutation_checked`).

## Positive witnesses first

A universal negative `∀x̄. g₁ → … → gₙ → naf G` is false when its witness
query `∃x̄. g₁ ∧ … ∧ gₙ ∧ G` holds. For example, with `p(one)` and `one` in the
guarded domain, `∀x. naf p(x)` is false. `Strategy.withWitness` asks the
witness query before the binders are opened as rigid parameters. Evidence the
base has for the goal itself comes first: when a base candidate closes the
goal (`Expansion.closes`: an assumption, ex falso, or a clause concluding it),
such as an assumed `∀x. naf p(x)` or an assumed falsity, the base's candidates
are the answer. Left rules on other assumptions are no such evidence. If the
query is answered, the strategy offers no candidates and the branch fails. The
opened goal could not be refuted anyway, since the rigid parameter may be
`one`, and without the witness query it would only be a gap.

`witnessSearch` runs the left strategy on the witness query, exports the run,
and checks the export against the snapshot. So a defeat it reports comes with
a checked positive proof of the witness (`witnessSearch_derives`). That proof
makes the universal negative false in every model of the snapshot that
satisfies the context (`witnessSearch_defeats`, from `Model.defeats`). The
witness check is optional: a strategy uses it only when `withWitness` is part
of it.

## Snapshots, contexts, and imports

Evidence is checked against the snapshot and the context it is given.
Refutation evidence is therefore indexed by the snapshot as closed-world
evidence:
- Adding a clause changes the only-if clause of its predicate.
- Registering a predicate adds its registry fact.
- Adding a domain member adds a case to the domain's completion.

In each case, evidence that used the changed clause is rejected against the
new snapshot, and a new run must find new evidence. The lowered formulas are
unchanged: completion only adds clauses.

Lemma imports are kept out of the completion. The completion is taken of the
program's own clauses, and an imported lemma clause is appended after it.
Completed together with the program, a derivable lemma would add a case to its
predicate's completion and change the evidence. The NAF node's context is
exact: the evidence is checked under the node's own context, so a refutation
that uses an assumption is rejected where that assumption is absent.

**Assumptions are hypotheses, not program clauses.** The completion closes the
program; an assumption of the NAF's context is a hypothesis about the values
of its names. The guarded universal relies on this: refuting `p(x)` under
`r(x)` splits on `r`'s completion. So, with no `p` clauses, `p(one) → naf
p(one)` is derivable: it is true in every model of the completion, where
`p(one)` is false. S07's ground provider differs: it evaluates NAF in the plan's
program together with its context as facts, and does not establish that
formula. The two never contradict each other; S10 establishes some formulas S07
does not.

## Proof-layer capability

P0 asks for a ground instance for every name inside a NAF operand (S07).
`Request.proofLayerIn` marks such a request with `ProofLayer.refutation`. The
NAF can be established by the refutation route, and its proof is checked by
the explicit-proof route. The input is not admitted for automatic execution,
and nothing claims that the refutation search terminates. `diagnose` still
annotates only inputs that P0 does not admit (`diagnose_not_ready`).

## Guarantees

| Property | Theorem |
| --- | --- |
| Refutation evidence is adequate for models of the KB with complement NAF, also for operands with parameters | `refutation_adequate` |
| The NAF check accepts only evidence of the provider; a tree checked with it is sound | `refutationCheck`, `refutationChecker_sound` |
| The completion closes no marker and not `ho_apply`; no KB clause of an accepted completion may conclude a marker, and no clause of it concludes a marker atom | `Signature.of_open`, `complete?_heads`, `complete?_reserved` |
| The commands' contracts, read through the answers, by `Derives` rules | `Expansion.onlyIfUse_soundUnder`, `Expansion.equalJoin_soundUnder` |
| The refutation search is sound for its program's KB | `refuter_sound` |
| The commands' constructions are valid given valid premise trees | `Unfold.onlyIfUse_proves`, `Unfold.equalJoin_proves` |
| Evidence-first NAF is sound when its base and check are; over a completed program with refutation evidence | `Strategy.withRefutation_sound`, `nafByRefutation_sound` |
| Each NAF node offered carries evidence that checks for its context and operand, as read in every later store | `Strategy.withRefutation_checked`, `Store.read_stableNegation`, `Store.read_rigid`, `Store.Refines.resolve_closing` |
| A branch proved with goals still delayed closes before floundering, and no name is bound while closing | `step_close`, `step_flounder`, `Store.bind_closing`, `Store.Refines.closed` |
| A witness found is a checked positive proof and defeats the universal negative in every model | `witnessSearch_derives`, `witnessSearch_defeats`, `Model.defeats` |
| A defeat offers nothing, so the witness check keeps the base's soundness | `Strategy.withWitness_sound` |

## Traces

| Trace | Result |
| --- | --- |
| `naf p(5)`, `5` a rigid parameter, no `p` clauses | Refuted by `false :- p(x)`; the export is accepted |
| `∀1. naf p(1)`, no `p` clauses | Refuted at the eigenvariable; accepted |
| The same tree without the completion | Rejected |
| `naf p(two)` with `p(one)` | Refuted by the clash of `two` and `one`; accepted |
| The same tree for `p(5)`; with `two` not in the signature | Rejected: `5 = one` is no clash; no clash clause |
| Assumed `naf p(5)`, goal `naf p(5)` | Success by assumption; no NAF node |
| `∀1. naf p(1)` with `p(one)` | A gap: the rigid parameter may be `one` |
| `naf p(X)`, `X` an answer name, no `p` clauses | Delays; the branch closes and `p(X)` is refuted for every `X`: success with `X` unbound; the export checks |
| The same with `p(one)` | A gap: `X` may be `one` |
| `naf p(X) ∧ r(X)` with `p(one)`, `r(two)` | `r` binds `X := two`, the NAF wakes and refutes `p(two)`; accepted |
| The same with `r(one)` | A gap |
| `q(X) :- UNKNOWN`, `naf q(5)` | A gap: the `UNKNOWN` case is never refuted |
| A KB clause concluding `UNKNOWN` | Invalid, by its position |
| `∀1. r(1) → naf p(1)`, `r(two)`, `p(one)` | The cases `x = two` and `x = one` join to `two = one`, a clash; accepted |
| The same over `r(one)`, with witnesses first; without | Exhausted: the witness `one` defeats the negative; a gap |
| `∀1. naf p(1)` with `p(one)`, witnesses first | Exhausted |
| `∀1. r(1) → naf p(1)` over `r(two)`, witnesses first | No witness; refuted as before |
| A compound head `p(one) ∧ q(one)`; a `ho_apply(p, X)` head; a head applying a predicate variable | `p` and `q` open, `naf p(one)` a gap and a closing tree rejected; `p` open; nothing closed |
| `naf ho_apply(p, one)` with `p(one)` | A gap: `ho_apply` is never closed |
| `plus(zero) = zero` with `plus` a defined operation; with `plus` declared free | No clash for `plus`, a tree through one rejected; accepted, which is why constructors are declared |
| A head `unknown ∧ q`, or `ho_apply(unknown, X)` | Invalid, by position |
| Witnesses first under an assumed `∀x. naf p(x)`, or an assumed falsity, with the witness `p(one)` | Success by the assumption: evidence first |
| The same with a selection splitting an unrelated `q(one) ∧ q(two)` | Exhausted: the witness still defeats the negative |
| A head `X`, or `X ∧ q(one)`, beside `p(one)` | Nothing closed; `naf p(two)` a gap |
| A head `X` or `ho_apply(X1, X0)`, with the marker used; without it | Invalid; accepted |
| `naf p(5)` under five unrelated `q(i) ∨ r(i)`, no `p` clauses | Refuted at once: the disjunctions are not split |
| `naf p(two)` with `p(one)` and five unrelated literals | Refuted: clash clauses only for matching equations |
| `naf p(succ(one))` with `p(one)` | Refuted by a clash under a constructor argument; accepted |
| `naf p(succ(two))` with `p(succ(one))` | A gap: injectivity is not searched. A supplied tree through the injectivity clause is accepted |
| `naf p(5)` with `p(succ(X)) :- p(X)` and no base case | A gap: the refutation needs induction, and the bounded run finds none |
| Evidence of `naf p(5)` with no `p` clauses, after adding `p(one)` | Rejected |
| Evidence of `naf registry(q)`, after registering `q` | Rejected; the NAF is now a gap |
| The guarded refutation over `r(two)`, after adding `r(zero)` | Rejected; a new run refutes again |
| The refutation of `p(5)` under `r(5)`, checked under no assumption | Rejected |
| The evidence of `naf q(two)` with `q(X) :- p(X)` and the lemma `q(one)` imported after the completion; completed with the program | Accepted; rejected |
| Diagnoses | A name in a NAF operand of the query or of a clause body: `refutation` |

## Boundaries

- **No termination or completeness.** The search is bounded by its fuel. A
  refutation that needs induction, injectivity, or the occurs check
  (`x ≠ f(x)`, which the equality theory does not include) is not found, and
  the NAF stays a gap. A supplied tree may use the injectivity clauses. A gap
  or an exhausted refutation search establishes nothing about the operand.
- **Export of whole runs is not proved here.** NAF nodes are checked
  node-wise (`Strategy.withRefutation_checked`). The theorem that every
  successful run exports an accepted tree belongs to S15/S16, as for S09.
- **The completion is a model hypothesis.** Soundness holds in models of the
  completion and the free equality theory with complement NAF. With cycles
  through NAF in clause bodies, the completion may have no model, and then
  evidence proves nothing about an intended model. Stratification is not
  checked here.
- **No constructive negation.** A flexible operand waits, and is refuted for
  every value only when its branch closes. Answers kept as constraints
  (`Store.constraints`, such as `X ≠ one`) with a solver are not implemented.
- **Closing binds nothing**, not even a name a candidate declares while
  closing. A refused binding is recorded as floundering, never as a miss
  (`State.enter`), so a NAF barrier is not opened by it. The evidence-first
  order still offers only the base's candidates when there are any, so a NAF
  goal whose base candidates all bind is a gap rather than refuted. Solvers
  that bind at the end are S21's settle stage.
- **No finite-domain enumeration.** Absence over a domain is refuted
  symbolically, through the domain's completion. Coverage by enumerating
  members is not offered.
