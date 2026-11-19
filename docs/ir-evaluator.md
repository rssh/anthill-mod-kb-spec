# The IR evaluator (S28)

S28 implements the evaluator of the [decision IR](decision-ir.md): it answers
a query of P0 or P1 with S22's results, exactly and with no fuel, on the query's
relevant program ([S27](ir-programs.md)), and a query of P2 soundly within the
fuel. Yes means truth in every model of the completion realizing the
signature, No falsity in each, Unknown a model of each kind, as decided with
the user (2026-11-17). Traces are in
[Tests/Resolution/IR/Evaluate.lean](../Tests/Resolution/IR/Evaluate.lean) (P0
and P1) and [Tests/Resolution/IR/Budgeted.lean](../Tests/Resolution/IR/Budgeted.lean)
(P2).

Status: in part. Done: exact P1 decisions with no fuel, queries with rigid
parameters through their split, the KB-level consistency check, certificates
checked by recomputation and by two witnesses, cost classes, and P2 within the
fuel (S24's refutation and witnesses, checked derivations, monotone in the
fuel). Pending: the export of a Yes derivation as an S08 tree (a theorem of
the KB when it has no closed-world step), and the evaluation of the
polynomial class by two fixpoints (boundaries, below).

| Module | Contents |
| --- | --- |
| [IR/Possible](../AnthillModKbSpec/Resolution/IR/Possible.lean) | Possible answers computed by recursion on the rank, checked at run time (`Program.answersOf`); passing instances enumerated and checked (`Program.checked`, `Program.instancesAt`); both sound with no hypothesis and complete with the evidence |
| [IR/Exact](../AnthillModKbSpec/Resolution/IR/Exact.lean) | The exact relevant program without fuel: its calls (`Program.relevantCalls`), atoms, instances as heads and ground bodies, the denials' and the query's ground bodies, each exactly S27's |
| [IR/GroundModels](../AnthillModKbSpec/Resolution/IR/GroundModels.lean) | The ground relevant program (`Program.groundProgram`), the body lemma, closure, every key fixpoint a model of it; the Kripke–Kleene iteration and the enumeration of its models |
| [IR/Extension](../AnthillModKbSpec/Resolution/IR/Extension.lean) | The check that the rules outside the relevant program are stratified, and a model of the relevant program extended to a key fixpoint (`extends_model`) |
| [IR/Evaluate](../AnthillModKbSpec/Resolution/IR/Evaluate.lean) | The answer (`Program.answer`): the KB-level check, the instances, their combination; soundness, Undecided only for inconsistency, exactness; certificates and their checks |
| [IR/Cost](../AnthillModKbSpec/Resolution/IR/Cost.lean) | Cost classes before anything runs (`Program.cost`) |
| [IR/Budgeted](../AnthillModKbSpec/Resolution/IR/Budgeted.lean) | P2 within the fuel: S24's iteration on the rules a goal reads (scopes), its refutation and witnesses on the IR's rendering, the KB-level gate of P2's Yes and No, derivations and their checker, the search, the decision (`Program.decideWithin`) and its certificates' check |

## The relevant program, exact and without fuel

S27 proves a closed P1 query's relevant program finite (`relevant_finite`) and
computes a superset of it with fuel, holding calls a later literal of a body
rules out. S28 computes the relevant program itself, with no fuel:

- **Possible answers by rank** (`Program.answersOf`). A call that leaves an
  output free answers the heads of its vertex's passing instances; the calls
  of those instances that leave an output free are answered by recursion, made
  only when the callee's rank (its vertex's level, then the size of its bound
  values) is lower (`lowerRank`). The recursion is well founded on the rank
  with no fuel, and with the evidence the check always passes (S27's
  `call_rank`).
- **Checked instances** (`Program.instancesAt`). S27's enumeration
  (`bodyEnvs`) gives the candidates; each is kept only once checked
  (`Program.checked`): its names hold ground data terms, its head's bound
  arguments are the call's values, and it passes against the answer lists
  (`passesWith`: fixed literals true, every free call at a listed answer). So
  the enumeration needs no soundness theorem: the checks give soundness with no
  hypothesis (`answersOf_sound`, `instancesAt_sound`), the enumeration's
  completeness (S27's `walk_at`) and the evidence give completeness
  (`answersOf_complete`, `instancesAt_complete`).
- **Calls by rounds** (`Program.callRounds`). From the roots (the calls of the
  query's checked instances, of its conditions, and of the denials' checked
  instances), each round adds the calls of the found calls' checked instances.
  Every call found is relevant (`callRounds_sound`); the rounds stay inside
  S27's finite relevant calls and grow until one closes (`closes`). They run
  each from the one before until one closes (`Program.roundsFrom`), with no
  fuel: the loop's termination is that existence. The closed round holds
  every relevant call (`callRounds_complete`). Each definition that computes
  with the answer lists builds the vertices' level table once
  (`Program.answersWith`).

| Property | Theorem |
| --- | --- |
| Every computed answer is a possible answer; with the evidence, every possible answer is computed | `answersOf_sound`, `answersOf_complete` |
| Every kept instance passes; a passing instance is kept | `instancesAt_sound`, `instancesAt_passes`, `instancesAt_complete`, `instance_kept` |
| The rounds close; the calls found are exactly S27's relevant calls | `closes`, `relevantCalls_iff` |
| The atoms are exactly the relevant atoms; the instances exactly the relevant instances, each as its head and ground body | `relevantAtoms_iff`, `relevantInstances_iff` |
| The denials' and the query's ground bodies are exactly their passing instances' | `denialBodies_iff`, `goalBodies_iff` |

A **ground body** is the atoms of an instance's calls, of its NAF literals,
and of its markers; its fixed literals are true at a passing instance and are
dropped. The **ground relevant program** (`Program.groundProgram`) holds the
relevant atoms, the relevant instances, the denials' and the query's ground
bodies, and the query's ground conditions with the truth of their fixed
literals.

## Its models

A **model** of the ground program (`GroundProgram.Model`) is an assignment of
the relevant atoms and the markers in which each relevant atom holds exactly
when one of its instances' bodies does, and no denial body holds: S27's
relevant program's completion with the denials read on their passing
instances.

| Property | Theorem |
| --- | --- |
| At a ground instance, a body holds in a key model exactly when its ground body holds and its fixed literals are true | `body_holds_iff`, `passing_holds_iff` |
| Every body of the ground program reads only relevant atoms | `groundProgram_closed` |
| Every key fixpoint, restricted to the relevant atoms and the markers, is a model | `fixpoint_model` |
| The query's conditions and formula have the same truth in a key fixpoint and in its restriction | `context_iff`, `formula_iff` |
| The Kripke–Kleene iteration on the ground program is sound: its definitely true atoms hold, its definitely false ones fail, in every model | `GroundProgram.kk_sound` |
| Every model agrees with one the enumeration finds: the definitely true atoms with a subset of the undefined ones, and a subset of the markers | `GroundProgram.models_complete` |

The iteration (`GroundProgram.kleene`) is S24's `kk` on the ground relevant
program, where no abstract value is needed, run once per enumeration; the
enumeration (`GroundProgram.models`) tries each subset of the atoms it leaves
undefined and of the markers, keeping the models (`isModel`, every one a
model: `models_model`). Whether a model exists is decided with early exit
(`GroundProgram.hasModel`): the subsets are tried one at a time
(`anySubset`), never built as a list (`hasModel_iff`).

## The rest of the KB

A model of the relevant program is a restriction of a model of the whole
completion only when the rest of the KB extends it: an unreached rule
`r(a) :- p(a), naf r(a)` forces `p(a)` false on a consistent KB. Yes and No
need no extension, since every key fixpoint restricts to a model. Unknown
needs both its witnesses to extend.

- **The check** (`Program.outsideStratified`). A rule is *computed* when its
  head's arguments have no name and its head is a relevant atom: its one
  instance is relevant. Every other rule must respect ranks of the
  predicates: its calls no higher than its head, its NAF literals strictly
  lower (`Program.stratifiedBy`). The ranks are computed by rounds
  (`Program.ranks`); when the check fails, the answer names the first rule
  outside whose head is on a cycle through NAF among the rules outside and
  that the ranks do not respect (`Program.unstratified`, `nafCycleSymbols`).
- **The extension** (`extends_model`). With the check, a model of the relevant
  program extends to a key fixpoint agreeing with it on the relevant atoms and
  the markers: every other atom is decided stratum by stratum, each stratum's
  atoms by the least fixpoint of their rules given the strata below
  (`Strata.strata`, Knaster–Tarski by S24's `lfp`). A stratum reads itself only
  positively and the strata below and the relevant atoms as fixed
  (`consequence_reads`), so each stratum's operator is monotone
  (`stratumOp_mono`) and the result is a fixpoint outside
  (`strata_fixpoint`); S27's splitting theorem (`fixpoint_of_relevant`) and
  its reading of the denials (`denied_iff`) give the key fixpoint.

The check reads the predicate graph, so it is stricter than the decision of
2026-11-18 ("no rule outside the relevant program reads a relevant atom under
NAF on a cycle"): a NAF cycle outside blocks Unknown whether or not it reaches
a relevant atom, and a non-ground rule on a NAF cycle blocks it even when its
instances outside read no relevant atom. Yes and No are never blocked.

**The KB-level check** (`Program.kbCheck`, decided with the user,
2026-11-18). The ground heads of the rules on cycles through NAF whose bodies
read an atom (`Program.cycleRoots`; a fact is on no cycle of atoms), with the
denials, get a relevant program of their own (`Program.consistencyQuery`),
decided once per KB beside the queries. It is split into **pieces**, its
atoms and markers linked by its rules and denials (`pieces`), each checked
closed at run time (`pieceClosed`) and searched for one model with early exit
(`GroundProgram.hasModel`); a denial with no atom holds in every assignment
(`emptyDenial`). When the joint query is not P1, the roots whose own query is
P1 (`Program.checkableRoots`) are checked jointly, with the denials, and each
alone (`rootQuery`) when that query is not P1 either. A piece with no model
shows the KB has none (a model of the program is one of each piece:
`restrict_model`), and every query answers Undecided, naming the piece's
atoms and markers; a KB with a model passes (`kbCheck_of_consistent`).
Outside NAF cycles that pass the check still block Unknown. The cycles through
NAF are found per NAF edge, two reachability computations each, none when
there is no NAF (`nafCycleSymbols`).

## The answer

`Program.answer` runs the KB-level check, then decides a query of P0 or P1 on
its **instances** (`Program.instances`): the closed query's ground relevant
program, or one per instance of the split of its rigid parameters
(`Program.splitValues`). The combination (`Program.combine`) reads the models
that satisfy the conditions:

| Answer | When | Certificate |
| --- | --- | --- |
| Undecided, the KB's consistency | The KB-level check finds a piece with no model, or an instance has no model; the blocker names that piece's or instance's atoms and markers | — |
| Yes | The goal holds in every such model of every instance (also when none satisfies the conditions: then Yes and No both hold) | The instances' ground programs |
| No | The goal fails in every such model of every instance | The instances' ground programs |
| Unknown | One model where the goal holds and one where it fails, each from an instance whose rules outside are stratified, chosen among all such instances | The two models, each with its instance's position |
| Undecided, the witnesses | No such pair: the blocker names a rule outside at its head, with the instance's undefined atoms and markers | — |
| Undecided, the profile's blockers | The query is P2 or Undecided before anything runs: its notes and blockers (`decideWithin` answers P2 within the fuel, below) | — |

A closed query is read over the key fixpoints by the Herbrand reduction
(`herbrand`), a split one through its instances (`meaning_classify`): Yes when
every instance's truth holds, No when every instance's falsity holds, Unknown
when one is not No and another not Yes.

| Property | Theorem |
| --- | --- |
| Every answer means what it says over the models of the completion realizing the signature, with no hypothesis | `answer_sound`, `decideQuery_sound` |
| A query of P0 or P1, its instances' rules outside stratified, is Undecided only when the KB has no model | `answer_decided` |
| **Exactness**: then Yes exactly when the goal holds in every model and fails in none, No exactly when it fails in every one and holds in none, Unknown exactly when both occur | `answer_exact` |
| A KB with a model passes the KB-level check | `kbCheck_of_consistent` |

The soundness of Unknown rests on the extension (`instances_witness`); that
of Yes and No on every key fixpoint restricting to a model
(`instances_truth`, `instances_falsity`).

## Certificates and their checks

| Answer | Certificate | Check |
| --- | --- | --- |
| Yes, No | The instances' ground relevant programs | Recomputed and compared, each with a model, the KB-level check passing, and the goal true (false) in every model of each that satisfies the conditions (`Program.checkByPrograms`) |
| Unknown | Two assignments, each with its instance's position | Each assigns only its instance's relevant atoms and markers, is a model of the instance's recomputed relevant program (a fixpoint of its ground clauses with every denial body false), satisfies the conditions, with the goal true and false respectively; the rules outside both instances stratified (`Program.checkUnknown`) |
| Yes, P2 | A derivation: rule instances in order, by their rules' indices and their names' values, and an instance of the goals | The query passes the checker and is closed; every step's values its rule's names' (a name's repeats agreeing) and derived from the atoms before it, the goals' instance likewise from them all (`Program.checkDerivation`); the KB-level check passing and nothing unsettled (`Program.kbUnsettled`). The round is the search's, not checked |
| No, P2 | S24's refutation, by its universe | The query passes the checker; the Kripke–Kleene iteration on the goals' scope run again over the universe, the universe valid, the goal refuted; the KB-level check passing and nothing unsettled |
| Unknown, P2 | S24's greatest and least fixpoint witnesses | The query passes the checker; both computed again and compared |

A checked certificate is sound with no other hypothesis
(`checkByPrograms_sound`, `checkUnknown_sound`, `checkAnswer_sound`;
`checkDerivation_sound`, `checkDecision_sound` with P2's); a tampered one is
rejected (traces). Every answer is indexed by the snapshot:
its certificate is checked against the program it was computed from.

## Cost classes

`Program.cost` reports a query's class before anything runs, on the predicate
graph:

| Class | When |
| --- | --- |
| Polynomial, of degree `k` | P0 or P1, and no NAF literal of the query's dependency closure or its goals, no denial, and no condition reads a predicate whose dependency closure reaches a cycle or a marker; `k` is S23's degree: the most names a rule of the closure, a denial, or the query's goals other than its rigid parameters join, and one more per rigid parameter the query splits |
| Exponential | P0 or P1 otherwise |
| Budgeted | P2: the derivation search is bounded by the fuel; S24's iteration on the goals' scope and on the denials' runs once, and so do its witnesses, on the whole KB |
| Blocked | Undecided before anything runs |

In the polynomial class every model lies between the least fixpoint with the
markers false and the greatest with them true. The evaluator does not use that
yet: it decides both classes by the enumeration, exponential in the atoms the
iteration leaves undefined (boundaries).

## P2 within the fuel

A query of P2 lacks the finiteness evidence: its relevant program may be
infinite, or its names unguarded, outside the Herbrand reduction. The
decision (`Program.decideWithin`) runs the KB-level check, answers a query of
P0 or P1 exactly with no fuel as above (the profile read once), and a query of
P2 by `Program.budgeted`, in this order:

| Answer | When | Evidence |
| --- | --- | --- |
| Unknown | S24's two witnesses (`Program.witnessesOver`), for a positive program and goal with no condition: a closed abstract least fixpoint where the goal fails, the markers false, and a post-fixpoint over the universe and ⋆ where it holds, the markers true; every denial body failing in the first and refuted for the second | The two fixpoints |
| Undecided, the KB's consistency | What P2's Yes and No assume of the KB is unsettled (`Program.kbUnsettled`, below) | — |
| No | S24's refutation on the goals' scope, over its universe and one abstract value ⋆ for every other value: the formula is not possibly true under any abstract value of its names (`Program.refutedIn`) | The universe |
| Yes | The first derivation the search finds within the fuel, checked; only for a closed query, the only kind a derivation shows | The derivation and its round |
| Undecided | Otherwise | The profile's notes: the growing call, the call with a free output, the unguarded name, or the unsplit parameter, each lacking a termination argument |

**Scopes.** S24's Kripke–Kleene iteration runs on a scope: the rules of the
predicates the goals read and of every predicate they reach
(`Program.readClosure`), with the signature restricted to the closed ones
among them (`Program.scopeSignature`). A predicate's only-if half reads only
its own rules (`definitions_scope`), so every model of the completion has on a
scope what the iteration needs (`completes_scope`), and refutation on a scope
is sound (`refutedIn_sound`). Predicates outside it are read as open. The rest
of the KB costs nothing: the universe and the iteration are the scope's.
Refutation and the witnesses need no fuel. The witnesses are key fixpoints of
the whole completion, so an Unknown needs no check of the rules outside and
nothing of the KB-level check: its witnesses are models. They run on the whole
KB, the cheap tests first, the least fixpoint only for a positive program and
goal, the greatest only once the least shows the goal false; the denials are
refuted once per KB, on their own scope (`Program.denialsRefuted`).

**What P2 assumes of the KB.** Every answer assumes a model (S24's policy,
decided with the user, 2026-11-09). P1 answers on the KB-level check alone,
keeping its guarantee that it is Undecided only for the KB's inconsistency. A
P2 Yes or No also needs the check to have settled what it reads
(`Program.kbUnsettled`): nothing when the KB-level query is P1; otherwise the
roots whose own query is not P1, which `kbCheck` left unchecked, are checked
together on their ground closure when every rule they reach is ground
(`Program.groundClosure`: then it is their relevant program, whatever the rest
of the KB is), and are unsettled otherwise; and the denials, when no P1 query
read them, must each be refuted (S24). An unguarded rule anywhere makes every
query P2, the KB-level ones included, so this is what keeps `s :- ¬s` beside
`q(X) :- r(X)` from a Yes. The gate needs no proof: Undecided is always
sound.

**Derivations.** A derivation (`Derivation`) lists rule instances in order,
each by its rule's index and its names' values, and an instance of the goals
by their names' values. A step is derived when its values are its rule's
names' (`Rule.names`' repeats agreeing), its names hold ground terms, its calls
are at atoms derived before it, its NAF operands are refuted, its fixed
literals are true, and it reads no marker (`Program.stepHead`, shared by the
search and the checker). The checker (`Program.checkDerivation`) needs only the
program and the query; a checked derivation's goal holds in every model of the
completion realizing the signature (`checkDerivation_sound`): calls by
induction on the steps, NAF literals by the refutation and complement NAF,
fixed literals by the realized guards and primitives and the free
constructors, each head by its rule's clause (`stepHead_holds`).

**The search** (`Program.searchFrom`) runs S27's saturation from the goals
alone (a derivation reads no condition and no denial), one round at a time, up
to the fuel, stopping once a round adds nothing. At each table it takes the
checked instances at the table's calls (`Program.tableSteps`, S28's
`instancesAt` on the table's answers) round by round, the calls found last
first, each derived head available at once, until a round takes none
(`Program.deriveRound`), and looks for an instance of the goals they derive
(`Program.derivationIn`). The first table that gives one gives the
derivation, with its round; the evaluator checks it before answering Yes, so
soundness rests on the check, not on the search or the table.

| Property | Theorem |
| --- | --- |
| A scope's predicates have the program's definitions; a model has on a scope what S24's iteration needs | `definitions_scope`, `completes_scope` |
| A refuted formula is false in every model, under every environment | `refutedIn_sound`, `refutedIn_falsity` |
| Refuted denials are false in every model with what the iteration needs | `denialsRefuted_sound` |
| S24's witnesses are two models, the goal true in one and false in the other | `witnessesOver_independence` |
| A checked derivation is a Yes | `stepHead_holds`, `derivedAtoms_holds`, `derivationHolds_truth`, `checkDerivation_sound` |
| More fuel finds the same derivation | `searchFrom_mono` |
| Every decision is sound | `budgeted_sound`, `decideWithin_sound` |
| A query of P0 or P1 gets its exact answer whatever the fuel | `decideWithin_evidence` |
| **Monotone in the fuel**: once a decision is not Undecided, more fuel gives the same one | `budgeted_mono`, `decideWithin_mono` |
| A checked certificate is sound | `checkDecision_sound` |

P2's traces
([Tests/Resolution/IR/Budgeted.lean](../Tests/Resolution/IR/Budgeted.lean)):

| Trace | Decision |
| --- | --- |
| A growing call `p(X) :- allData(X), p(succ(X))`: `p(zero)`, at fuel 0 and 20 | Undecided, a termination argument, at the call `p(succ(X))` (rule 0, literal 1) |
| The same with the fact `p(succ(succ(zero)))`: `p(zero)` at fuel 2; 3; 50 | Undecided; Yes by a derivation of round 3; the same derivation |
| `q(X) :- r(X).`, no rule for `r` (`X` unguarded): `q(a)` | No, by refutation, at fuel 0 |
| `p(X). s :- p(a).`; with `s :- p(a), ¬r(a)` and no rule for `r`; with `r(a).` too | Yes by derivation; Yes, `r(a)` refuted; No by refutation |
| S24's `r(X) :- r(X). q(X) :- r(X). p(X). s :- q(Y), p(Y).`: `s` | Unknown by S24's two fixpoints, at fuel 0 |
| Left recursion with `Z` free on the recursive call, over the chain: `path(a, c)`; `path(c, a)` | Yes by derivation (round 5); No by refutation |
| `p(a) :- ¬q(a). q(a) :- ¬p(a).` at fuel 0 and 100; `p(a).`; `s. ⊥ :- s.` | Unknown by assignments both; Yes by the relevant program; Undecided, the KB's consistency |
| `s :- ¬s.` beside `p(a).` and the unguarded `q(X) :- r(X).`: `p(a)` | Undecided, the KB's consistency: the root `s`, unchecked by the KB-level check, has no model on its ground closure |
| A consistent `t :- ¬u. u :- ¬t.` beside `p(X). s :- p(a).`: `s`; with `t :- ¬u, p(a)` | Yes by derivation (the ground closure has a model); Undecided, the KB's consistency (the closure reaches `p(X)`, with a name) |
| `p(X). s :- p(a).` with `⊥ :- r(a).` and no rule for `r`; with `r(a).` too | Yes by derivation (the denial refuted); Undecided, the KB's consistency |
| The growing rule's KB with `u :- ¬w, p(zero). w :- ¬u. s. ⊥ :- s.`: `p(zero)` | Undecided, the KB's consistency: the denials' own query is P1 and has no model |
| Every certificate above | Checks |
| A derivation with its first step dropped, offered for another goal or for a larger atom, a repeat of its values changed, or a goal value with no name; a refutation that refutes nothing; S24's witnesses swapped; a derivation and a refutation on `s. ⊥ :- s.`; a refutation for a query the checker rejects | Rejected |

## Traces

| Trace | Answer |
| --- | --- |
| `path` over the cycle `a ↔ b`, lowered with its guards first: `path(a, b)`; `path(a, c)` | Yes; Unknown, the greatest and the least fixpoint over the relevant atoms its witnesses, where S24 answers Undecided |
| The same with the guards over `D_all` | Yes; Unknown |
| `path` over the chain `a → b → c`: `path(a, c)`; `path(c, a)` | Yes; No |
| Left recursion with `Z` bound from `node` first: over the cycle `path(a, a)`, `path(a, c)`; over the chain `path(a, c)` | Yes, No, Yes |
| Left recursion with `Z` left free on the recursive call | Undecided before anything runs (P2), a termination argument; `decideWithin` answers it within the fuel (P2's traces) |
| `p :- ¬q. q :- ¬p.` | Unknown |
| `p :- ¬p.`; `p. ⊥ :- p.` | Undecided, the KB's consistency |
| `p :- q. p :- ¬q. q :- q.` | Yes, with no derivation |
| `p :- ¬q. q :- ¬p. ⊥ :- p.` | No: the denial rules out the model `{p}` |
| `p :- ¬s. s :- ¬p.` with an unreached `r :- p, ¬r` | Undecided, the witnesses, at the head of the `r` rule |
| The same with `t :- p, ¬q` instead | Unknown |
| `p :- ¬s. s.` with the `r` rule | No: Yes and No need no extension |
| An unrelated `t :- ¬t` | Every query Undecided, the KB's consistency (the KB-level check) |
| An unrelated `t :- ¬r. r :- ¬t.`: `p.`; `p :- q. q :- q.` | Yes; Undecided, the witnesses, at the cycle's first rule |
| `q(X) :- node(X), unknown(X)` (opened), `p(X) :- node(X), naf q(X)`: `p(a)`; `q(a)`; `r(a)`; `naf r(a)` | Unknown; Unknown; No; Yes |
| Conditions with `p :- q. q :- q.`: under `q`; under `¬q`; under `r` (no rule) | Yes; No; Yes (vacuous) |
| `path(x, ·)` with `item(x)` (members `a`, `b`): over the cycle `path(x, a)`, `path(x, c)`; over the chain `path(x, c)`, `path(x, a)` | Yes, Unknown; Yes, No |
| `path(x, c)` with `node(x)` over the chain | Unknown, its witnesses from the instances `a` and `c` |
| `path(x, c)` with `node(x), item(x)` over the chain | Yes, on the two instances `a` and `b` the guards share |
| A parameter no finite guard splits; a growing call `p(X) :- p(succ(X))`; an undeclared predicate | Undecided before anything runs |
| The certificates the evaluator gives for the traced queries | Check |
| An Unknown's witnesses swapped; one with an atom dropped; one padded with an atom outside its relevant program; a No's programs offered for Yes; programs with their goals dropped; a Yes with no program; a Yes and a No on `p :- ¬p` with the recomputed programs | Rejected |
| `p :- ¬s. s :- ¬p.` with `t :- r.` reading the unreached `r :- p, ¬r` | Undecided, the witnesses, at the head of `r :- p, ¬r` |
| `p :- node(X), ¬q. q :- node(Y), ¬p.`: body-only names, ground heads | Unknown |
| `p(b) :- ¬s. s :- ¬p(b).` with `p(x)` under `item(x)`, the members `a, b` and `b, a` | Unknown both ways: the witnesses come from the instance `b`, whose rules outside are stratified |
| `s :- ¬s.` beside a NAF cycle reaching a growing call (the joint KB-level query P2) | Every query Undecided, the KB's consistency: the roots whose own query is P1, here `s`, checked jointly |
| `p. ⊥ :- p.` beside a consistent cycle `t :- ¬r. r :- ¬t.` | Undecided, the KB's consistency, naming `p` only |
| Cost: a denial `⊥ :- node(X), node(Y), edge(X, Y)` beside the query `p` | Polynomial of degree 2 |
| Cost: `path` over the cycle; `p :- ¬q. q :- ¬p.`; the open program; `p(a) :- q(a), ¬r(a). q(a).`; `p :- q. p :- ¬q. q :- q.`; a split without a finite guard; an undeclared predicate | Polynomial of degree 3; exponential; exponential; polynomial of degree 0; exponential; budgeted; blocked |

## Boundaries and open points

- **P2's reach.** Unknown comes only from S24's positive witnesses: a
  program and goal with no NAF, no condition, and a goal shown true in the
  greatest fixpoint only through closed predicates and markers (guard,
  primitive, and other declared atoms are read as false there; S24's
  ground-program witnesses are not used). Refutation evaluates a formula's
  free names only at the universe's terms and ⋆, and reads every atom outside
  the scope's closed predicates as possibly true. Yes needs a closed query (a
  P2 query with a rigid parameter answers No or Unknown only) and a derivation
  through instances the saturation's table enumerates. So one P2 note
  anywhere in the KB (an unguarded rule makes every query P2) can turn an
  exact No or Unknown of P1 into Undecided. The Undecided blockers are the
  profile's notes, read before anything runs, not the frontier the saturation
  reached; the derivation's steps list every derived instance, not only those
  the goal needs, and each table of the search derives again from the start.
- **P2's gate is conservative.** A P2 Yes or No needs the KB-level check to
  have settled the KB: a NAF-cycle root whose own query is not P1 and whose
  closure reaches a rule with a name, or a denial no P1 query read and S24's
  refutation does not refute, leaves every P2 Yes and No Undecided, even on a
  consistent KB. An Unknown is not gated.
- **The S08 export of a Yes derivation**, its NAF nodes refutations, and the
  mark of a Yes with no closed-world step as a theorem of the KB: pending. A
  P0 or P1 Yes is certified by its relevant programs, checked by
  recomputation; a P2 Yes by its derivation, checked by its checker.
- **The polynomial class's evaluation.** The class is reported, but the
  evaluator enumerates in both classes: the two-fixpoint route (least with the
  markers false, greatest with them true) and its proof are pending.
- **The outside check reads predicates.** A NAF cycle outside the relevant
  program blocks Unknown even when it reaches no relevant atom, and so does a
  non-ground rule on a NAF cycle whose instances outside read none; so does
  NAF between distinct ground atoms of one predicate, `p(a) :- naf p(b)` read
  as a cycle on `p` (it also makes `p(a)` a KB-level root). The KB-level
  check makes ground cycles' inconsistency an Undecided for every query, but
  a consistent one still blocks Unknown. That the computed ranks satisfy the
  check whenever no cycle through NAF exists among the rules outside is not
  proved: `answer_decided` takes the check as its hypothesis.
- **Inconsistency outside the KB-level check** (a non-ground NAF cycle, a
  root whose own query is not P1, or P1 roots jointly inconsistent only with
  a root whose query is not P1) is not detected by `answer`: its Yes and No
  are then sound vacuously, and its Unknown is blocked. P2's gate checks a
  root whose query is not P1 on its ground closure, or leaves P2's Yes and No
  Undecided; but it checks those roots apart from the ones `kbCheck` checked,
  so roots inconsistent only across the two groups, and a non-ground NAF
  cycle (no root), go undetected there too.
- **The pieces link through every atom.** The KB-level check's pieces are
  linked through the atoms the Kripke–Kleene iteration decides too (facts), so
  independent loops that share a fact are searched as one piece: exponential
  in their union, not in each.
- **Cost of the implementation.** The check of a kept instance evaluates its
  free calls' answer lists again, so possible answers through a chain of free
  calls cost `(1 + k)^depth` for `k` answers per call: exponential in the
  recursion's depth even where `cost` reports a polynomial class. Each round
  reads the instances of every call found, not only the new ones. `answer`
  runs the KB-level check at each query, its pieces each exponential in
  their own atoms; a host computes it once per snapshot, and `decideWithin`
  computes P2's gate, with its own classifications of the KB-level queries,
  for each P2 query. S24's witnesses run on the whole KB, for a positive
  program and goal. The relevant program's calls and the level table are
  computed once per ground program, and the models' search stops at the first
  model. S17 owns performance.
