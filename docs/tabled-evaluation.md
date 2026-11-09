# Tabled evaluation and the fast fragment's answers (S24)

S24 implements the execution side of [fast evaluation](fast-decision-routes.md):
SLG resolution as an extension of the shared machine, and the answers Yes, No,
Unknown, and Undecided against the Clark completion. Traces are in
[Tests/Resolution/Tabled/Evaluation.lean](../Tests/Resolution/Tabled/Evaluation.lean).

| Module | Contents |
| --- | --- |
| [Tabled/Fixpoint](../AnthillModKbSpec/Resolution/Tabled/Fixpoint.lean) | Interpretations over constructor keys, the consequence operator (`consequence`), the completion's models are its fixpoints (`fixpoint_iff_models`), least and greatest fixpoints (`lfp`, `gfp`), monotonicity for positive programs (`consequence_mono`) |
| [Tabled/Abstract](../AnthillModKbSpec/Resolution/Tabled/Abstract.lean) | The universe of a query (`universeOf`), abstract values, the Kripke–Kleene iteration (`kk`, `refutes`), the abstract least fixpoint (`leastOver`), the greatest post-fixpoint over the universe and a fresh value (`greatestOver`), ground fixpoints (`groundFixpoint`) |
| [Tabled/AbstractSound](../AnthillModKbSpec/Resolution/Tabled/AbstractSound.lean) | Free constructors (`Free`, `free_of_equality`), the abstraction of values (`Abs`), commutation (`aeval_abs`), the body lemma (`body_sound`), every round sound (`kk_sound`), a refuted goal false in every model (`refutes_sound`) |
| [Tabled/Witness](../AnthillModKbSpec/Resolution/Tabled/Witness.lean) | The least and greatest witnesses of a positive program (`least_witness`, `greatest_witness`), the ground witness with NAF (`ground_witness`) |
| [Tabled/Multiset](../AnthillModKbSpec/Resolution/Tabled/Multiset.lean) | The multiset order on lists (`Lower`), well-founded for a well-founded order (`Lower.wellFounded`) |
| [Tabled/Weight](../AnthillModKbSpec/Resolution/Tabled/Weight.lean) | Goal sizes (`goalSize`), the weights of a machine state's branches (`weights`), a candidate fitting its focus (`Fits`), every machine step lowering the weights (`step_lower`) |
| [Tabled/Engine](../AnthillModKbSpec/Resolution/Tabled/Engine.lean) | Calls, tables, waiting branches, the completion stack (`Run`), the bounds of a bounded run (`Bounds`, `admits`, `inSpace`, `fit`), the engine's strategy (`Engine.strategy`), the run's transitions (`Engine.step`, `Engine.run`) |
| [Tabled/EngineSound](../AnthillModKbSpec/Resolution/Tabled/EngineSound.lean) | NAF evidence by the completion's models (`semanticNaf`), the strategy sound, fitted or not (`strategy_sound`), the run's invariant (`Run.Inv`) kept by every transition (`Run.Inv.step`), reconstruction (`run_init_reconstructs`) |
| [Tabled/Termination](../AnthillModKbSpec/Resolution/Tabled/Termination.lean) | The calls and answers of the bounds (`Bounds.calls`, `Bounds.answers`), the rank of a run (`Engine.rank`) lowered by every transition (`Engine.step_rank`), the run without fuel (`Engine.runToEnd`) |
| [Tabled/Answer](../AnthillModKbSpec/Resolution/Tabled/Answer.lean) | The setup, the checker of exported proofs (`checker`, `nafCheck`), the witnesses, a query's bounds (`Setup.bounds`) and bounded run (`Setup.decided`), the answer (`Setup.answer`), soundness (`answer_sound`), P1 without fuel (`answer_p1`), monotonicity in the fuel (`answer_mono`) |

## Tabling on the shared machine

The run (`Run`) holds the tables and a completion stack of **generators**. Each
generator is an ordinary machine state (`Machine.State`), and its transitions
are the machine's `step` with the engine's strategy, so the machine's
invariants hold for every generator unchanged.

| Event | What the run does |
| --- | --- |
| A focused atom with a declared mode, or a guard, inputs with no flexible name as read (rigid parameters are fixed for the run), and a closed context | A **call**: a predicate or a guard, its input values, its context (`Call`). A guard's one argument is its input; it is decided by the signature's generated clauses (`Setup.generated`) |
| A call with no table | Create its table and push its generator: a machine state for the atom with its outputs as fresh answer names, which resolves it against the clauses. The caller stays focused on the call until the table completes |
| A call with a complete table | Consume the table: each answer a candidate, its node a leaf naming the answer and its context |
| A call with an incomplete table (a recursive call) | Consume the answers so far, and leave a **consumer**: the branch's obligation, store, continuations, and deferred proofs |
| A generator's success | A new answer, naming only its call's rigid parameters, with the generator's completed proof; scheduled to every consumer as a choice point of the consumer's own machine state |
| `naf A`, `A` ground | Refuted over the universe (below): proved, the node carrying the universe. With an answer `A` in its table: fails. Otherwise its table first: with no table, the table is created; complete, `A` is an open atom (`GapReason.opened`); incomplete, the NAF **waits** |
| The top generators have nothing left, and none depends on a table below the lowest of theirs | They form a strongly connected component: their tables complete together and their generators are popped. A NAF waiting on one of them is resolved: it fails if an answer came, and is an open atom otherwise |
| A data equation `s = t` | Matched by the S05 matcher, the node `equalRefl` |
| Anything else | The positive strategy over the clauses (S06), unknown markers open (S22) |

A loop through NAF is delayed and resolved when its component completes, as in
SLG; under the completion a NAF that no refutation proves and no answer
refutes stays open, not true. A P2 run is bounded by fuel; running out is
`interrupted`, never an answer. A P1 run is bounded by its data and ends
without fuel (below).

## Termination: bounded runs without fuel

A **bounded run** (`Engine.bounds`) is the run of a P1 query. Its bounds
(`Setup.bounds`) are the symbols the program and the query apply; the data
terms built from them, the literals, and the query's free names (rigid
parameters included), with at most the most arguments an application has and
at most `(s + 1) ^ (p + 1)` nodes, for `s` the largest argument and `p` the
symbols (each call from a lower component's entry can grow its inputs by a
body's terms); and the assumptions (the query's context and every antecedent
the program or the query assumes). The size limit is generous: a P1 run never
comes near it, while a growing program, run bounded, would take as long. Three
runtime checks keep a run within the bounds (decided with the user,
2026-11-08):

| Check | What a bounded run does |
| --- | --- |
| A call's predicate, inputs, and context drawn from the bounds, the context without repeats (`admits`) | Otherwise the call is not tabled: it runs by the positive strategy, and is cut where `fit` drops one of its candidates; a ground NAF on it is cut too (`GapReason.bounded`) |
| An answer within the bounds (`inSpace`) | Scheduled to the consumers waiting; otherwise recorded for consumers still to come, and each consumer waiting that it would serve is a gap |
| A candidate lighter than its focus (`fit`): its premises weigh less than the goal (`Fits`), a generator's root more than every clause body (`rootWeight`) | Otherwise dropped, and the focus is a gap (`incomplete`) |

A cut is recorded where it happens, with `GapReason.bounded`: the strategy's
response carries it (`Response.incomplete kept [.bounded, …]`, from `fit`,
beside any gap the response already had, and from a NAF whose call the bounds
leave out), and so does an answer the run does not schedule to a consumer it
would serve. Its blocker is a termination limit (`Missing.termination`), not a
construct. A NAF on an unknown marker meets an open atom (`opened`).

The **rank** of a run (`Engine.rank`) falls at every transition
(`Engine.step_rank`), lexicographically:

| Component | Falls when |
| --- | --- |
| The calls of the bounds with no table (`openCalls`) | A table is opened |
| Every table's answers of the bounds still to come (`openAnswers`) | An answer is recorded and scheduled to consumers |
| Every generator's branch weights (`branches`), in the multiset order | Every machine transition (`step_lower`): one branch is replaced by lighter ones. A delayed goal is weighed once, in the store, and its waking moves the weight into the branch |
| The generators and their choice points (`points`) | A component completes and its generators are popped; an empty choice point is dropped |

The multiset order handles a call consuming a complete table: one alternative
per answer, however many, each lighter than the call. Consumers waiting on an
incomplete table get only answers within the bounds, so at most the
answers of the bounds are ever scheduled. So the run is a total function with
no fuel (`Engine.runToEnd`), never interrupted (`runToEnd_ended`), equal to the
run with some fuel (`runToEnd_fuel`), and opens at most the calls of its
bounds: the predicates, the input lists of at most `arity` data terms, and the
contexts of at most `|assumptions|` assumptions (`Bounds.calls`), S23's count
of distinct calls. The termination proof needs no invariant of the run and
holds for every program: the checks, not the program, bound it. For a P1
query, S23's theorems (`calls_bounded`, `outputs_bounded`, `calls_decrease`)
say the checks never fire; that lifting is S15's, with completeness.

## Invariants and reconstruction

`Run.Inv` is the machine's invariant for every generator (`State.Valid`,
`State.Sound`) with what the run adds:

| Part | Statement |
| --- | --- |
| Owners | Generators have distinct tables, below the table count; the query's generator proves the query |
| Waiting branches | Each is a valid, sound branch of its owner's machine state, so an answer scheduled to it is a valid, sound choice point; a consumer is in its table's context |
| Tables | Contexts closed; every answer closed and derivable in its table's context; a generator's root is in its table's context |

| Property | Theorem |
| --- | --- |
| The engine's strategy is sound: table answers by the tables, NAF nodes by the refutation, equations by reflexivity, the rest by the positive strategy | `Engine.strategy_sound` |
| The machine's counter only grows, and a success's resume state keeps the root | `step_nextHole`, `step_success_resume` |
| Opening a table, leaving a branch waiting, scheduling an answer, recording it, completing a component, and every machine transition keep the invariant | `Run.Inv.opened`, `Run.Inv.waited`, `Run.Inv.scheduled`, `Run.Inv.answered`, `Run.Inv.completed`, `Run.Inv.advanced` |
| Every transition keeps the invariant; a success of the query reconstructs it | `Run.Inv.step`, `Run.Inv.run` |
| A successful run's goal and context, read through its final answers, are derivable | `Engine.run_init_reconstructs` |

## Answers over the completion

The answers are against the Clark completion (decided with the user,
2026-11-07): a goal cut on a positive cycle is Unknown, not the least-model No
that tabling alone gives. They are about the models of the completed program
with complement NAF that realize the admission signature (`Setup.meaning`).

| Answer | When | Evidence |
| --- | --- | --- |
| **Yes** | The run succeeds | The proof exported as an S08 term, each table answer expanded from its own proof (`exportWith`), and checked (`checks`) against the completion and the guards' generated clauses (`checkSnapshot`), which every model realizing the admission signature satisfies (`models_checkSnapshot`). NAF evidence is a universe over which the operand is refuted, checked by computing the refutation again (`nafCheck`) |
| **No** | The run completed, and the goal is refuted over the universe | The universe (`refutesIn`) |
| **Unknown** | The run completed, and two witnesses check | `greatest` and `least` for a positive program, two `assignment`s for a ground one |
| **Undecided** | Admission's blockers; a denial (`⊥ :- body` or `false :- body`) with an instance of its body proved, or its run unsettled (`constraints`, `violation`); fuel exhausted (P2), naming the call being evaluated; no witness, naming the run's gaps; a ground program none of whose assignments of its undecided atoms is a model, all of them tried, the KB's consistency naming those atoms | Blockers |

A P1 query runs bounded, without fuel (`Setup.decided`); a P2 query with the
fuel (`Setup.runOf`). Beside a P1 query each denial body is admitted as a
query of its own (`denialQuery`, decided with the user, 2026-11-09): a P1 body
runs bounded, any other with the fuel (`denialFor`), so a bounded run is only
ever given a P1 goal, and a P1 answer depends on the fuel only through its
KB's denials that are not P1. A denial run that met open atoms is unsettled,
since denials checked one at a time miss a joint inconsistency, unless a
checked model of the KB shows it consistent (`modelShown`: a ground program's
assignment that is a fixpoint, or a positive program's closed least fixpoint,
every denial body failing; decided with the user, 2026-11-09). Every answer's
evidence is checked independently of the run, so soundness holds for both.

The Kripke–Kleene iteration and the two fixpoints stop once a round changes
nothing (`untilStable`, at most `rounds`); every round is sound, so the round
they stop at is (`kleene_round`, `untilStable_round`). The engine computes the
iteration once, when a refutation first needs it, and the checker once per
query's universe for all the NAF nodes of a proof.

### No: the Kripke–Kleene iteration over abstract values

The **universe** is the ground data subterms of the program and the query. An
**abstract value** is a term of the universe or ⋆, every other value. In a
model whose declared constructors are free, as the completion's equality
theory makes them, every value has exactly one abstraction, and abstract
evaluation commutes with the model's (`aeval_abs`).

The iteration (`kk`) computes **definitely true** ground atoms (true in every
model) and **possibly true** abstract atoms (over-approximating every model's
true atoms), Fitting's Kripke–Kleene semantics of the completion. NAF reads the
other set. Every round is sound in every model of the completion
(`kk_sound`); a goal not possibly true under any abstract value of its names is
false in every model (`refutes_sound`). For a positive program the possibly
true atoms are the greatest fixpoint, abstracted: this is the rule decided
with the user, 2026-11-08, replacing "outside the greatest fixpoint over the
finitely many calls", which is unsound: in
`r(X) :- r(X). q(X) :- r(X). p(X). s :- q(Y), p(Y).` the greatest fixpoint
over the data terms gives `r` no answer, yet `s` holds in the model where `r`
holds of a value no data term denotes. ⋆ stands for that value.

### Unknown: the least and the greatest fixpoint

The completion's models over keys are exactly the fixpoints of the consequence
operator (`fixpoint_iff_models`). For a positive program the operator is
monotone, so the least and the greatest fixpoints exist and both are models.

| Witness | Model | Check |
| --- | --- | --- |
| `least` | The least fixpoint, unknown markers false | A closed abstract least fixpoint (`closedLeast`) bounds its true atoms (`lowInterp_pre`); the goal and every denial body fail over it (`failsLeast`) |
| `greatest` | The greatest fixpoint, unknown markers true | A post-fixpoint of atoms over the universe and one fresh value, a key no data term has (`postGreatest`), lies below it (`highInterp_post`); the goal is true over it (`vtrue`); every denial body is refuted |
| `assignment` | A ground program's fixpoint, NAF included | The assignment is a fixpoint of the ground clauses and makes every denial body false (`groundFixpoint`, `ground_witness`); candidates are the definitely true atoms with every subset of the undecided ones (all, none, and each one alone when there are more than eight) |

The guards are interpreted exactly (`Open.guardTruth`), so every witness model
realizes a separated admission signature (`realizes`).

## Guarantees

| Property | Theorem |
| --- | --- |
| The completion's models over keys are the fixpoints of the consequence operator, denials false | `fixpoint_iff_models`, `models_of_fixpoint`, `fixpoint_of_models` |
| Positive programs have a least and a greatest fixpoint | `consequence_mono`, `lfp_pre`, `lfp_post`, `gfp_pre`, `gfp_post` |
| The equality theory makes the declared constructors free; values have one abstraction | `free_of_equality`, `Abs.unique`, `Abs.exists` |
| Every Kripke–Kleene round is sound; a refuted goal is false in every model of the completion | `kk_sound`, `refutes_sound`, `notPossible_sound` |
| The witnesses are models of the completion with the goal's value | `least_witness`, `greatest_witness`, `ground_witness` |
| The run keeps the machine's invariants and reconstructs its answer | `Run.Inv.step`, `Engine.run_init_reconstructs` |
| Every answer is sound | `Setup.answer_sound`, `answerFrom_sound`, `witnesses_sound`, `refutesIn_sound`, `proved_sound` |
| Unknown only after a completed run | `Setup.answer_unknown` |
| Only Undecided changes with more fuel | `Setup.answer_mono`, `Engine.run_more` |
| Every machine step, with alternatives lighter than the focus, lowers the branch weights | `step_lower` |
| Every transition of a bounded run lowers its rank; the rank is well-founded | `Engine.step_rank`, `RunLower.wellFounded`, `Lower.wellFounded` |
| A bounded run ends without fuel, is never interrupted, and is the run with some fuel | `Engine.runToEnd`, `Engine.runToEnd_ended`, `Engine.runToEnd_fuel` |
| A P1 answer is the same for every fuel when its KB's denials are P1 too; its run is never interrupted | `Setup.answer_p1`, `Setup.decided_ended` |

## Traces

| Trace | Result |
| --- | --- |
| `path(+, −)` over the cycle `a ↔ b`: `path(a, b)`; `path(a, c)`; `∃Y. path(a, Y)` | Yes, checked; Unknown, the greatest and the least fixpoint its witnesses; Yes |
| The same over `a → b → c`: `path(a, c)`; `path(a, d)` | Yes; No |
| Left recursion `path(X, Y) :- path(X, Z), edge(Z, Y)`: over the cycle `path(a, a)`, `path(a, c)`; over the chain `path(a, c)` | Yes, No (no `edge(Z, c)` for any `Z`); Yes. The run terminates: the recursive call waits on its own table |
| `top :- left, right`, both calling `mid(a)` | One table per call, `mid(a)` once; Yes |
| `∃Y. path(a, Y)` over the cycle | Four tables, `path(a)` and `path(b)` with two answers each |
| `p :- ¬q. q :- ¬p.` | Unknown, the assignments `{p}` and `{q}` |
| `p :- ¬p.` | Undecided: the KB's consistency |
| `p :- ¬q.`; with the fact `q` | Yes, the refutation of `q` checked again; No |
| Lowered `path` with its range guards first, over `a → b → c`, nodes declared: `path(a, b)`, `path(a, c)`; `path(a, d)` | Yes, the guards decided by the generated clauses; No |
| `p(X) :- q(succ(X)). q(Y).`, P1: `p(a)` | Yes: the constructed input `succ(a)` is within the bounds |
| `p(a). q(a). ⊥ :- p(X), q(X).`; `false :- p.` with `p`; a denial body needing a constructed input | Every answer Undecided, the KB's consistency |
| Five independent NAF loops | Not inconsistent: not every assignment of the ten undecided atoms is tried |
| `p(X) :- p(succ(X))`, `p(zero)` with fuel 300 | Undecided, lacking a termination argument, naming a call `p(succ(…))` |
| `path(a, b)`, P1, with fuel 0; 9000 | Yes; Yes: no fuel needed |
| `p :- ¬q. q :- ¬p.`, P2, with fuel 5; 300; 9000 | Undecided; Unknown; Unknown |
| The bounded run of `p(X) :- p(succ(X))` from `p(zero)`, its terms cut at six nodes | Ends, abandoned: the growing call leaves the bounds; the blocker is a termination limit |
| `∃Y. path(a, Y)` over the cycle, bounded | Four tables, one per distinct call |
| `p(X) :- ¬q(succ⁶(X)). q(Y).`, its terms cut at six nodes | The NAF is cut: a termination limit, not a construct |
| A call cut beside an unsupported match (an `ho_apply` datum in a head); an answer outside the bounds with a consumer waiting | Both name the termination limit |
| `p :- naf unknown` | An open atom: witnesses missing, not a construct |
| `p :- ¬q. q :- ¬p. ⊥ :- ¬p. ⊥ :- ¬q.` with `r`; `q(a) :- unknown. ⊥ :- q(a).` with `r` | Undecided, the KB's consistency: no model shown; Yes: an assignment is a model |
| Beside a P1 query: a growing denial `⊥ :- p(zero)` over `p(X) :- p(succ(X))`; `⊥ :- (∀X. q(X)), t.` with `q(Y)`; `⊥ :- (s → (s → s)), t.` | Undecided by the fuel, naming the growing call; Yes; Yes: each denial body checked as its own profile says |
| `path(X, c)`, `X` a rigid parameter, left recursion over the cycle | P1; the run ends (plain SLD on the call looped); No |
| `path(X, a)`, `X` rigid | The run ends; Undecided: neither derived for every `X` nor refuted, and witnesses with parameters are S26's |
| `q(a) :- unknown`: `q(a)`; `¬q(a)` | Unknown; Unknown, with no refutation run |
| `r(X) :- r(X). q(X) :- r(X). p(X). s :- q(Y), p(Y).`, goal `s` | Unknown: the fresh value supports `s` in the greatest fixpoint |
| A denial `⊥ :- p` with the fact `p`; with no `p` | Every answer Undecided, the KB's consistency; the query answered |
| A predicate without a mode | Undecided before anything runs |

## Boundaries

- **The checks never fire for P1.** A bounded run ends for every program, but
  a call, an answer, or a candidate outside the bounds is a gap, so the answer
  may be Undecided. S23 bounds a complete predicate's calls
  (`calls_bounded`) and answers (`outputs_bounded`, `calls_decrease`) per
  component, an entry's calls by its own inputs; that every call and scheduled
  answer of a P1 run is within the bounds' size, composing those bounds along
  the component order, and every candidate fits (clause bodies weighed by
  their connectives, goals without formula variables), is S15's, with the
  completeness below (decided with the user, 2026-11-08; noted there). S15 may
  need to raise the size limit.
- **Completeness and exactness.** An atom in the least fixpoint of a P1
  program answering Yes (the engine's completeness), and the cases in which
  the answer is never Undecided, are S15's ("P1 decisions are total, sound,
  and complete"). The decision between No, Unknown, and Undecided is exact
  where the abstract and the concrete greatest fixpoints agree on the goal,
  and the abstract least fixpoint is exact on it. Abstraction can still leave
  a goal between them: `s :- r(X), r(Y), g(X, Y)` with `g(f(Z), Z)` needs two
  related fresh values. Then the answer is Undecided, never a wrong one.
- **Export.** A Yes is exported and checked; a run whose export does not
  check is Undecided. That every successful run's export checks is S15/S16's,
  as for S06 runs ([S08](proof-checking.md)).
- **Witness classes.** Positive covered programs (no NAF, no implication, data
  arguments), with unknown markers, and ground programs with NAF. A non-ground
  program with NAF has no witnesses: an open goal there is Undecided.
  Contexts: a query with assumptions has no witnesses (S26). Neither has a
  goal with rigid parameters. The greatest witness's check reads a guard atom
  as false, so a positive program whose clauses use guards, as lowering emits
  them, gets no greatest witness: its open goals are Undecided.
- **Tabled calls.** Inputs with no flexible name as read, rigid parameters
  included, and contexts closed. A call with a flexible name at an input, or a
  context with a rigid parameter, and NAF on a non-ground operand, run by the
  positive strategy, or are gaps in a bounded run: constructive negation is
  S21's, contexts S26's.
- **Calls through `ho_apply`** are not tabled themselves: a concrete
  `ho_apply(p, args)` is read as `p(args)`, which is.
