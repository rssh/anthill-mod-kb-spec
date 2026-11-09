## Attributes

- id: WI-20261107-R9YMZ-s24-tabled-backtracking-on-the
- created: 2026-11-07T14:54:18Z

- status: Claimed
- status_agent: claude
- status_at: 2026-11-08T09:56:57Z

- acceptance: lake build

- depends_on: WI-20261107-7PQMQ-s23-moded-structural-recursion, WI-20261107-JA6WZ-s22-answers-yes-no-unknown-and, WI-20261026-ANXY6-s10-implement-evidence-first

- tags: resolution-machine

## Description

S24: Tabled backtracking on the shared machine

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: the execution side of docs/fast-decision-routes.md: tabling as an extension of the shared machine, answering S22's four results against the Clark completion for S23's P1 and P2 predicates.

Decided form (2026-11-07, with the user): answers are against the completion, so a goal cut on a positive cycle is Unknown, not a least-model No. Fuel bounds term growth, and running out of fuel is Undecided, never Unknown.

Acceptance:
- Machine: a table per distinct call (a variant, as read) and context. A repeated call consumes its table; a recursive call waits for answers instead of looping; tables complete per strongly connected component; a loop through NAF is delayed and resolved when its component completes (SLG resolution). Table answers keep their derivations. The run invariants (step_valid, step_sound, run_success) and reconstruction are extended.
- Termination: a P1 predicate's run ends without needing fuel, within a bound from S23's count of distinct calls; a P2 run is bounded by fuel.
- Answers: Yes with Derives; No for a completed search whose failure depends on no cycle; Unknown for a completed search the completion leaves open, with two checked witness models; Undecided for fuel exhaustion (naming the growing call), an inconsistent completion (p :- ¬p), or witnesses that do not check. Each answer's soundness is proved, and answers are monotone in the fuel: only Undecided changes with more fuel.
- Exact Unknown in P1: for positive recursion, the completion's models are the fixpoints of the clauses' consequence operator (a theorem); over the finitely many calls, an atom in the least fixpoint is Yes, one outside the greatest No, one in between Unknown with the two fixpoints as witnesses.
- An open predicate reached gives Unknown, as S22 specifies, without a refutation run.
- Export: a Yes exports as an S08 tree, table answers expanded from their derivations; the exported trees are proved to pass checking.
- docs/resolution-implementation-plan.md's route table: this route replaces the deferred "finite rule saturation" and "stratified NAF over finite rules".
- Traces: path over a cyclic graph (path(a, b) Yes; path(a, c) with c unreachable Unknown with its fixpoint witnesses; the same over an acyclic graph No); left recursion terminating; p :- ¬q, q :- ¬p Unknown; p :- ¬p Undecided; p(x) :- p(succ(x)) Undecided by fuel, naming the call; a trace showing each distinct call evaluated once.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs.
Design references: docs/fast-decision-routes.md, docs/machine-state.md, docs/machine-delay.md, docs/machine-negation.md.

## Changes

### 2026-11-07T16:32:59Z — feedback — user

From S22 (2026-11-07, decided with the user): S22 checks Unknown witnesses, and builds their models, only for ground acyclic programs with P0 bodies, open markers, and denials, for queries without assumptions (Open.check, Open.check_model in Resolution/P0/Open.lean, on the constructor-key model of Models/KeyModel.lean). S24 extends the witness check to its tabled fragment: non-ground clauses, positive cycles (least and greatest fixpoints as the two witnesses), loops through NAF, and contexts. Outside the covered class, an opened run is Undecided naming the open atoms (Setup.answer in Resolution/P1/Answer.lean). Doing this in S24 rather than S22 is only a sequencing choice: nothing is built on top before the whole current language is.

### 2026-11-07T22:34:07Z — feedback — claude

From S23 (2026-11-08): admission proves the call bound per component, for any answer relation in which predicates with data-term outputs answer data terms (AnswersBounded): calls_bounded (from a ground input, a complete predicate's component calls have inputs among dataTerms), outputs_bounded (data-term outputs give data-term answers: the step of an induction on answers), calls_decrease (a decreasing component's recursive calls have smaller inputs). S24 composes them along the component order for whole-run termination without fuel, and shows its tables answer only bounded answers. The complete class is data-term inputs on recursive calls with data-term outputs or decreasing recursion (decided with the user, 2026-11-07: count(+, -) is budgeted). P1 assumes a consistent KB: a denial whose body is Yes is S24's runtime check.

### 2026-11-08T17:21:40Z — feedback — user

Progress (claude, 2026-11-08): implemented in Tabled/Fixpoint, Abstract, AbstractSound, Witness, Engine, EngineSound, Answer (docs/tabled-evaluation.md, Tests/Resolution/Tabled/Evaluation.lean). Decided with the user: SLG as an extension of the machine (the run holds the tables, waiting branches, and one machine state per generator; the core step is unchanged), and No by the abstract greatest fixpoint over the data terms plus one value standing for every other value (Kripke-Kleene), Unknown by the least and greatest fixpoints (or ground fixpoints with NAF). Open: (1) termination of a P1 run without fuel, within a bound from S23's calls; (2) a theorem stating when the answer is never Undecided (exactness); (3) that every successful run's export checks is S15/S16's (noted there).

### 2026-11-08T17:56:59Z — feedback — user

Decided with the user (2026-11-08), for the remaining work: (1) S24 proves termination of P1 runs without fuel; engine completeness (least fixpoint => Yes) and the exactness theorem (when the answer is never Undecided) move to S15, which already plans total, sound, complete P1 decisions. (2) A call whose inputs and context hold no flexible name as read is tabled, rigid parameters included: a P1 query such as path(X, c) with X rigid over a left-recursive cyclic graph otherwise runs plain SLD and loops (found by a probe: admitted P1, interrupted). Table answers then have no flexible name rather than being closed. (3) Tables and scheduled answers are bounded by runtime checks in a bounded mode for P1 runs, not by lifting S23's theorems onto the engine: a call is tabled only when its inputs lie in the query's data terms (rigid names included) and its context is drawn from the query's and the program's assumptions without repeats, otherwise it is a gap; only answers within the data terms are scheduled to waiting consumers, another one with consumers waiting records a gap. The run then ends for every program, without fuel. That the checks never fire for P1 (S23's calls_bounded and outputs_bounded lifted to runs) is S15's, with completeness.

### 2026-11-08T19:59:32Z — feedback — user

Progress (claude, 2026-11-08): termination done. Calls with rigid parameters at inputs are tabled (contexts stay closed; answers name only their call's names). A P1 query runs bounded (Setup.bounds, Setup.decided): calls tabled only within the bounds, answers scheduled only within them, alternatives kept only when lighter than their focus (Engine.fit, goal sizes in Tabled/Weight). Every machine step lowers the branch weights in the multiset order (step_lower, Tabled/Multiset), every run transition lowers the rank (openCalls, openAnswers, branches, points; Engine.step_rank), so Engine.runToEnd is total with no fuel, never interrupted (runToEnd_ended), and equals the fuelled run (runToEnd_fuel); the termination proof needs no run invariant and holds for every program. A P1 answer is the same for every fuel (Setup.answer_p1); P2 keeps fuel (answer_mono). Answers stay sound: their evidence is checked independently of the run. Docs: tabled-evaluation.md (termination section), fast-decision-routes.md, lean-admission-contract.md, plan, README. Traces: P1 path with fuel 0, P2 NAF loop by fuel, a bounded run of p(X) :- p(succ(X)) abandoned, tables among the bounds' calls, path(X, c) with X rigid ending with No.

### 2026-11-08T21:59:56Z — feedback — user

Review fixes (claude, 2026-11-08, after /code-review of the two S24 commits): guards are tabled calls decided by the signature's generated clauses (Setup.generated), which the checker reads too (checkSnapshot; sound since realizing models satisfy them, models_checkSnapshot), so lowered P1 programs answer Yes; denials are closed existentially (violation), include false :- body (constraints), and an unsettled or unexported denial run blocks; the consistency claim needs every assignment tried and names the undecided atoms; bounds are size-bounded terms ((s+1)^(p+1) nodes) so constructed inputs across components stay in; a cut is GapReason.bounded, its blocker a termination limit; out-of-bounds answers gap only the waiters they serve; the growing blocker names the generator being stepped; the Kripke-Kleene iteration runs once per engine. Still open from the review: the greatest witness reads guard atoms as false, so guarded positive programs get no greatest witness (Undecided, sound); stepAt repeats the strategy's NAF decision.

### 2026-11-09T15:38:04Z — feedback — user

Second review fixes (claude, 2026-11-09): beside a P1 query each denial body is admitted as its own query (denialQuery) and checked bounded only when P1, with the fuel otherwise (denialFor; decided with the user), so a bounded run is only ever given a P1 goal: a growing or universal denial no longer hangs or falsely blocks; answer_p1 takes the hypothesis that the KB's denials are P1. mark records a cut only where fit drops a candidate, or for a ground NAF cut by the bounds; an unsupported match of an out-of-bounds answer keeps its gap; namedGaps compares the whole obligation and trail. The Kripke-Kleene iteration is lazy per engine (Thunk) and shared by the refutation, the run's NAF, and the consistency path (refutesInWith, assignmentsWith, inconsistentWith). Not done: recording .bounded inside the machine instead of mark (needs a Response variant), and mark re-runs the strategy per bounded step.

### 2026-11-09T15:49:38Z — feedback — user

Bounded gaps in the machine (claude, 2026-11-09, decided with the user): Response.incomplete carries its gap reason (default unsupported); fit records what it drops as GapReason.bounded, a NAF whose call the bounds leave out answers incomplete [] bounded, and the machine records the gap where the cut happens. Engine.mark, cutAt, cut, and Setup.namedGaps are gone, with the per-step strategy rerun.

### 2026-11-09T16:28:56Z — feedback — user

Third review fixes (claude, 2026-11-09): Response.incomplete carries an explicit list of reasons (no default), so fit adds .bounded beside an unsupported match and no wrapper can lose it; NAF on an unknown marker answers opened; a denial run that met open atoms blocks unless a checked model shows the KB consistent (modelShown; decided with the user); the Kripke-Kleene iteration and the two fixpoints stop once a round changes nothing (untilStable, kleene_round), the engine computes it once on first use and the checker once per query universe. Correction to the earlier note: the iteration was not shared by the checker before this. Left: the duplicated NAF decision in stepAt and strategyCore, and answer's copy of schedule's consume match; Tests/ is outside lake build.

