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
| [Tabled/Engine](../AnthillModKbSpec/Resolution/Tabled/Engine.lean) | Calls, tables, waiting branches, the completion stack (`Run`), the engine's strategy (`Engine.strategy`), the run's transitions (`Engine.step`, `Engine.run`) |
| [Tabled/EngineSound](../AnthillModKbSpec/Resolution/Tabled/EngineSound.lean) | NAF evidence by the completion's models (`semanticNaf`), the strategy sound (`strategy_sound`), the run's invariant (`Run.Inv`) kept by every transition (`Run.Inv.step`), reconstruction (`run_init_reconstructs`) |
| [Tabled/Answer](../AnthillModKbSpec/Resolution/Tabled/Answer.lean) | The setup, the checker of exported proofs (`checker`, `nafCheck`), the witnesses, the answer (`Setup.answer`), soundness (`answer_sound`), monotonicity in the fuel (`answer_mono`) |

## Tabling on the shared machine

The run (`Run`) holds the tables and a completion stack of **generators**. Each
generator is an ordinary machine state (`Machine.State`), and its transitions
are the machine's `step` with the engine's strategy, so the machine's
invariants hold for every generator unchanged.

| Event | What the run does |
| --- | --- |
| A focused atom with a declared mode, closed inputs as read, and a closed context | A **call**: a predicate, its input values, its context (`Call`) |
| A call with no table | Create its table and push its generator: a machine state for the atom with its outputs as fresh answer names, which resolves it against the clauses. The caller stays focused on the call until the table completes |
| A call with a complete table | Consume the table: each answer a candidate, its node a leaf naming the answer and its context |
| A call with an incomplete table (a recursive call) | Consume the answers so far, and leave a **consumer**: the branch's obligation, store, continuations, and deferred proofs |
| A generator's success | A new answer, with the generator's completed proof; scheduled to every consumer as a choice point of the consumer's own machine state |
| `naf A`, `A` ground | Refuted over the universe (below): proved, the node carrying the universe. With an answer `A` in its table: fails. Otherwise its table first: with no table, the table is created; complete, `A` is an open atom (`GapReason.opened`); incomplete, the NAF **waits** |
| The top generators have nothing left, and none depends on a table below the lowest of theirs | They form a strongly connected component: their tables complete together and their generators are popped. A NAF waiting on one of them is resolved: it fails if an answer came, and is an open atom otherwise |
| A data equation `s = t` | Matched by the S05 matcher, the node `equalRefl` |
| Anything else | The positive strategy over the clauses (S06), unknown markers open (S22) |

A loop through NAF is delayed and resolved when its component completes, as in
SLG; under the completion a NAF that no refutation proves and no answer
refutes stays open, not true. Fuel bounds the run's transitions; running out
is `interrupted`, never an answer.

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
| **Yes** | The run succeeds | The proof exported as an S08 term, each table answer expanded from its own proof (`exportWith`), and checked (`checks`). NAF evidence is a universe over which the operand is refuted, checked by computing the refutation again (`nafCheck`) |
| **No** | The run completed, and the goal is refuted over the universe | The universe (`refutesIn`) |
| **Unknown** | The run completed, and two witnesses check | `greatest` and `least` for a positive program, two `assignment`s for a ground one |
| **Undecided** | Admission's blockers; a denial's body proved or unsettled; fuel exhausted, naming the call being evaluated; no witness, naming the run's gaps; a ground program none of whose assignments is a model, the KB's consistency | Blockers |

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
| `p(X) :- p(succ(X))`, `p(zero)` with fuel 300 | Undecided, lacking a termination argument, naming a call `p(succ(…))` |
| `path(a, b)` with fuel 5; 300; 9000 | Undecided; Yes; Yes |
| `q(a) :- unknown`: `q(a)`; `¬q(a)` | Unknown; Unknown, with no refutation run |
| `r(X) :- r(X). q(X) :- r(X). p(X). s :- q(Y), p(Y).`, goal `s` | Unknown: the fresh value supports `s` in the greatest fixpoint |
| A denial `⊥ :- p` with the fact `p`; with no `p` | Every answer Undecided, the KB's consistency; the query answered |
| A predicate without a mode | Undecided before anything runs |

## Boundaries

- **Termination without fuel.** S23 bounds a complete predicate's distinct
  calls (`calls_bounded`) and answers (`outputs_bounded`, `calls_decrease`);
  the run's tables are keyed by exactly these calls. That every P1 run ends
  within a bound computed from them, with no fuel, is not yet proved: the run
  is given fuel, and only Undecided depends on it (`answer_mono`).
- **Exactness.** The decision between No, Unknown, and Undecided is exact
  where the abstract and the concrete greatest fixpoints agree on the goal,
  and the abstract least fixpoint is exact on it. Abstraction can still leave
  a goal between them: `s :- r(X), r(Y), g(X, Y)` with `g(f(Z), Z)` needs two
  related fresh values. Then the answer is Undecided, never a wrong one. No
  theorem yet states the cases in which the answer is never Undecided.
- **Export.** A Yes is exported and checked; a run whose export does not
  check is Undecided. That every successful run's export checks is S15/S16's,
  as for S06 runs ([S08](proof-checking.md)).
- **Witness classes.** Positive covered programs (no NAF, no implication, data
  arguments), with unknown markers, and ground programs with NAF. A non-ground
  program with NAF has no witnesses: an open goal there is Undecided.
  Contexts: a query with assumptions has no witnesses (S26).
- **Tabled calls.** Inputs and contexts closed as read. A call with a rigid
  parameter or a flexible name at an input, and NAF on a non-ground operand,
  run by the positive strategy or are gaps: constructive negation is S21's.
- **Calls through `ho_apply`** are not tabled; they run by the positive
  strategy.
