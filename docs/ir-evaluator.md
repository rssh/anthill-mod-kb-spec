# The IR evaluator (S28)

S28 implements the evaluator of the [decision IR](decision-ir.md): it answers
a query of P0 or P1 with S22's results, exactly and with no fuel, on the query's
relevant program ([S27](ir-programs.md)). Yes means truth in every model of
the completion realizing the signature, No falsity in each, Unknown a model of
each kind, as decided with the user (2026-11-17). Traces are in
[Tests/Resolution/IR/Evaluate.lean](../Tests/Resolution/IR/Evaluate.lean).

Status: in part. Done: exact P1 decisions with no fuel, queries with rigid
parameters through their split, the KB-level consistency check, certificates
checked by recomputation and by two witnesses, and cost classes. Pending: P2
within the fuel, the export of a Yes derivation as an S08 tree (a theorem of
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
program, where no abstract value is needed; the enumeration
(`GroundProgram.models`) tries each subset of the atoms it leaves undefined
and of the markers, keeping the models (`isModel`).

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
2026-11-18). The ground heads of the rules on cycles through NAF
(`Program.cycleRoots`), with the denials, get a relevant program of their own
(`Program.consistencyQuery`), decided once per KB beside the queries. It is
split into **pieces**, its atoms and markers linked by its rules and denials
(`pieces`), each checked closed at run time (`pieceClosed`) and searched for
one model with early exit (`GroundProgram.hasModel`); a denial with no atom
holds in every assignment (`emptyDenial`). When the joint query is not P1,
each root's own query is checked instead (`rootQuery`). A piece with no model
shows the KB has none (a model of the program is one of each piece:
`restrict_model`), and every query answers Undecided, naming the piece's
atoms and markers; a KB with a model passes (`kbCheck_of_consistent`).
Outside NAF cycles that pass the check still block Unknown.

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
| Undecided, the profile's blockers | The query is P2 or Undecided before anything runs: its notes and blockers | — |

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

A checked certificate is sound with no other hypothesis
(`checkByPrograms_sound`, `checkUnknown_sound`, `checkAnswer_sound`); a
tampered one is rejected (traces). Every answer is indexed by the snapshot:
its certificate is checked against the program it was computed from.

## Cost classes

`Program.cost` reports a query's class before anything runs, on the predicate
graph:

| Class | When |
| --- | --- |
| Polynomial, of degree `k` | P0 or P1, and no NAF literal of the query's dependency closure or its goals, no denial, and no condition reads a predicate whose dependency closure reaches a cycle or a marker; `k` is S23's degree: the most names a rule of the closure, a denial, or the query's goals join, and one more per rigid parameter the query splits |
| Exponential | P0 or P1 otherwise |
| Budgeted | P2 |
| Blocked | Undecided before anything runs |

In the polynomial class every model lies between the least fixpoint with the
markers false and the greatest with them true. The evaluator does not use that
yet: it decides both classes by the enumeration, exponential in the atoms the
iteration leaves undefined (boundaries).

## Traces

| Trace | Answer |
| --- | --- |
| `path` over the cycle `a ↔ b`, lowered with its guards first: `path(a, b)`; `path(a, c)` | Yes; Unknown, the greatest and the least fixpoint over the relevant atoms its witnesses, where S24 answers Undecided |
| The same with the guards over `D_all` | Yes; Unknown |
| `path` over the chain `a → b → c`: `path(a, c)`; `path(c, a)` | Yes; No |
| Left recursion with `Z` bound from `node` first: over the cycle `path(a, a)`, `path(a, c)`; over the chain `path(a, c)` | Yes, No, Yes |
| Left recursion with `Z` left free on the recursive call | Undecided before anything runs (P2), a termination argument |
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
| A parameter no finite guard splits; a growing call `p(X) :- p(succ(X))`; an undeclared predicate | Undecided before anything runs |
| Every certificate the evaluator gives | Checks |
| An Unknown's witnesses swapped; one with an atom dropped; one padded with an atom outside its relevant program; a No's programs offered for Yes; programs with their goals dropped; a Yes with no program; a Yes and a No on `p :- ¬p` with the recomputed programs | Rejected |
| `p :- ¬s. s :- ¬p.` with `t :- r.` reading the unreached `r :- p, ¬r` | Undecided, the witnesses, at the head of `r :- p, ¬r` |
| `p :- node(X), ¬q. q :- node(Y), ¬p.`: body-only names, ground heads | Unknown |
| `p(b) :- ¬s. s :- ¬p(b).` with `p(x)` under `item(x)`, the members `a, b` and `b, a` | Unknown both ways: the witnesses come from the instance `b`, whose rules outside are stratified |
| `s :- ¬s.` beside a NAF cycle reaching a growing call (the joint KB-level query P2) | Every query Undecided, the KB's consistency: `s` checked on its own |
| `p. ⊥ :- p.` beside a consistent cycle `t :- ¬r. r :- ¬t.` | Undecided, the KB's consistency, naming `p` only |
| Cost: a denial `⊥ :- node(X), node(Y), edge(X, Y)` beside the query `p` | Polynomial of degree 2 |
| Cost: `path` over the cycle; `p :- ¬q. q :- ¬p.`; the open program; `p(a) :- q(a), ¬r(a). q(a).`; `p :- q. p :- ¬q. q :- q.`; a split without a finite guard; an undeclared predicate | Polynomial of degree 3; exponential; exponential; polynomial of degree 0; exponential; budgeted; blocked |

## Boundaries and open points

- **P2** within the fuel (No by S24's refutation over the data terms and one
  abstract value, Unknown by S24's witnesses, Undecided naming the growing
  call, monotone in the fuel): pending. A P2 query answers Undecided now,
  with its notes as termination blockers.
- **The S08 export of a Yes derivation**, its NAF nodes refutations, and the
  mark of a Yes with no closed-world step as a theorem of the KB: pending. A
  Yes is certified by its relevant programs, checked by recomputation.
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
  root whose own query is not P1, or roots jointly inconsistent whose joint
  query is not P1) is not detected: Yes and No are then sound vacuously, and
  Unknown is blocked.
- **Cost of the implementation.** The check of a kept instance evaluates its
  free calls' answer lists again, so possible answers through a chain of free
  calls cost `(1 + k)^depth` for `k` answers per call: exponential in the
  recursion's depth even where `cost` reports a polynomial class. Each round
  reads the instances of every call found, not only the new ones. `answer`
  runs the KB-level check at each query, its pieces each exponential in
  their own atoms; a host computes it once per snapshot. The traces run in
  under two minutes; S17 owns performance.
