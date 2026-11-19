## Attributes

- id: WI-20261117-HYJ2C-s28-the-ir-evaluator-exact-p1
- created: 2026-11-17T20:24:05Z

- status: Claimed
- status_agent: claude
- status_at: 2026-11-18T17:16:34Z

- acceptance: lake build

- depends_on: WI-20261117-06YN9-s27-decision-ir-syntax-checker, WI-20261026-ZPV53-s08-define-checked-proof, WI-20261107-R9YMZ-s24-tabled-backtracking-on-the

- tags: resolution-machine

## Description

S28: The IR evaluator: exact P1 decisions, P2 within fuel, certificates and their checks

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: the evaluator of docs/decision-ir.md, answering S22's results for IR queries. Decided with the user, 2026-11-17: Yes means truth in every model of the completion realizing the signature, with a checkable certificate, so that P1 decisions are exact; P2 is the same evaluator with fuel.

Acceptance:
- P1: build the relevant program; compute the definitely and the possibly true atoms (the Kripke–Kleene iteration, S24's kk); decide the atoms left undefined by enumerating the completion's models over them. A total function with no fuel and no gap, answering Yes, No, or Unknown, and Undecided only for the KB's inconsistency.
- Exactness, with S27's lemmas: Yes exactly when the query holds in every model of the completion realizing the signature, No exactly when it fails in each, Unknown exactly when both occur.
- P2: the same within the fuel over a relevant program that may be infinite; No by S24's refutation over the data terms and one abstract value, Unknown by S24's witnesses, Undecided naming the growing call; monotone in the fuel; with evidence supplied, the P1 answer.
- Certificates and checks: a Yes derivation over the relevant program, its NAF nodes refutations, exported as an S08 tree and checked; a Yes or a No by the relevant program, checked by recomputation; an Unknown by two fixpoint assignments (S24's groundFixpoint). A Yes with no closed-world step is marked a theorem of the KB; every other answer is indexed by the snapshot.
- Cost classes, reported before anything runs: polynomial of degree k when no NAF or denial reads a predicate whose dependency closure reaches a cycle or a marker (every model then lies between the least fixpoint with the markers false and the greatest with them true); exponential otherwise; budgeted for P2.
- Consistency: denials and NAF cycles checked at the KB level beside the queries; an inconsistent KB answers Undecided, naming it.
- Traces: S24's traces on the evaluator (path over a cycle and over a chain, left recursion, p :- ¬q with q :- ¬p Unknown, p :- ¬p Undecided, growing recursion Undecided by the fuel, naming the call); p :- q, p :- naf q, q :- q answering Yes with no derivation; a lowered path over a cycle answering Unknown where S24 gives Undecided; a non-ground program with NAF and an open predicate answering Unknown; a tampered certificate rejected.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs.
Design references: docs/decision-ir.md, docs/tabled-evaluation.md, docs/answers.md, docs/proof-checking.md.

## Changes

### 2026-11-18T10:49:07Z — feedback — user

From S27's review (2026-11-18), decided with the user: constraints outside a query's relevant program can rule out its models even on a consistent KB (an unreached rule r(a) :- p(a), naf r(a) forces p(a) false). S28 answers Unknown only when no rule outside the relevant program reads a relevant atom under NAF on a cycle; otherwise Undecided, naming that rule. Denials are S27's: they join the relevant program and its evidence graph. S27's splitting theorem (relevant_of_fixpoint, fixpoint_of_relevant) assumes the rest of the KB extends a relevant model; S28's exactness must discharge that, by the check above. Also: a split instance whose conditions no model satisfies is both Yes and No (vacuous); combine instances as S27's meaning_split states (Yes when every instance's truth holds, No when every instance's falsity holds, Unknown when one is not No and one is not Yes).

### 2026-11-18T12:57:53Z — feedback — user

From S27 (2026-11-18): S27 proves the relevant program finite under P1 (relevant_finite, instances_finite in IR/RelevantProgram) and computes one by saturation (Program.relevantProgram), complete when its table is stable (stable_complete). The computed program can hold more than the relevant one: calls are made reading a body left to right, before later literals that rule an instance out, and the enumeration (stepEnvs, bodyEnvs) has no soundness theorem. S28, which builds the relevant program a decision runs on, owns its soundness and exactness (or reads the computed superset as a splitting set closed under passing instances).

### 2026-11-18T14:33:01Z — feedback — user

Update from S27's review (2026-11-18): Program.relevantProgram now returns none unless the query is closed and the saturated table stable within the fuel; when computed it lists the calls, the rule instances, and the denials' passing instances (denials join the relevant program), each instance by its rule's or denial's index and the values of its names, without repeats (relevantProgram_complete); stable_answers gives the listed possible answers at free calls. The over-approximation and the missing soundness stay S28's.

### 2026-11-18T18:13:56Z — feedback — user

Progress (2026-11-18, in the working tree, not committed): P1 core done and proved. IR/Possible (possible answers by rank, checked; answersOf_sound/complete), IR/Exact (exact relevant program without fuel: callRounds closed via relevant_finite and a first-closed-round search; relevantCalls_iff, relevantAtoms_iff, relevantInstances_iff, denialBodies_iff, goalBodies_iff), IR/GroundModels (body lemma, closure, fixpoint_model, context_iff, formula_iff, KK and enumeration: kk_sound, models_complete), IR/Extension (outside rules stratified by ranks; extends_model via strata of least fixpoints), IR/Evaluate (answer with the KB-level check beside the queries, split instances; answer_sound, answer_decided, answer_exact; checkUnknown/checkByPrograms/checkAnswer_sound). Traces in Tests/Resolution/IR/Evaluate.lean. Decided with the user: KB-level check beside the queries (ground NAF-cycle rules' relevant program, once per KB); outside NAF cycles block Unknown. Remaining: cost classes (and the two-fixpoint route for the polynomial class), P2 with fuel, the S08 export of Yes derivations (theorem-of-the-KB mark), docs.

### 2026-11-18T21:56:54Z — feedback — user

/code-review of the S28 work in part (2026-11-18): 15 findings, no wrong answer. Fixed: KB-level check split into pieces with early exit and a per-root fallback when the joint query is not P1 (one P2 root no longer disables it); Unknown's witnesses chosen among instances whose outside is stratified (no dependence on member order); computedRule by head arguments only; the blamed rule restricted to NAF-cycle rules among the rules outside; certificate checks require a model per instance and the KB check (Yes/No) and witnesses within their instance (Unknown); blockers name the inconsistent piece's or instance's atoms and markers; models enumerated once per instance; kleene, marker subsets, ranks, and reachability hoisted; level table built once per definition (answersWith); rounds run incrementally (roundsFrom, no quadratic search); degree counts denials and parameters; docs and module docs corrected; traces added. Documented, not fixed: the check of a kept instance re-evaluates its free calls' answers ((1+k)^depth, S17), ground NAF between atoms of one predicate read as a predicate cycle.

### 2026-11-19T07:31:09Z — feedback — user

Progress (2026-11-19, in the working tree, not committed): P2 within the fuel done and proved, in IR/Budgeted (traces in Tests/Resolution/IR/Budgeted.lean). No by S24's refutation over the query's universe and one abstract value (refutedOver_sound, refuted_falsity). Unknown by S24's least and greatest fixpoint witnesses on the IR's rendering, for positive programs and goals with no condition (witnessesWith_independence): both are key fixpoints of the whole completion, so no outside check is needed. Yes by a derivation certificate (Derivation: rule instances by index and name values in order, then an instance of the goals; calls at earlier heads, NAF operands refuted, fixed literals true, no marker), checked before the answer (checkDerivation_sound, over every model realizing the signature, not only key fixpoints; no Herbrand reduction needed). The search runs S27's saturation one round at a time within the fuel and takes the first derivation (searchFrom_mono). Undecided carries the profile's notes (the growing call at its body site). Program.decideWithin: the KB-level check, P0/P1 exact whatever the fuel (decideWithin_evidence), P2 by budgeted; decideWithin_sound; decideWithin_mono (once not Undecided, more fuel gives the same decision); checkDecision_sound covers the P2 certificates (derivation, refutation, S24 witnesses recomputed). Limits: Yes needs a closed query; Unknown only S24's positive witnesses; blockers are the static notes, not the saturation's frontier. Remaining: the S08 export of a Yes derivation with the theorem-of-the-KB mark; the polynomial class's two-fixpoint evaluation.

### 2026-11-19T10:17:27Z — feedback — user

/code-review of S27, S28 P1, and the P2 working tree (2026-11-19): 15 findings, no wrong answer (every Yes and No found was vacuously sound). Fixed: P2's Yes and No now need the KB-level check to have settled the KB (Program.kbUnsettled, following S24's policy that every answer assumes a model, decided with the user 2026-11-09): NAF-cycle roots whose own query is not P1 are checked on their ground closure when every rule they reach is ground, unsettled otherwise; denials no P1 query read must be refuted. Before, one unguarded rule made every KB-level query P2 and P2 answered Yes on inconsistent KBs. P1 keeps its guarantee (Undecided only for inconsistency) and its documented boundary. checkDecision's P2 arms require the KB check, the gate, and the checker; derivation values are shape-checked (Rule.names repeats agree, no extra values; the goal's likewise). S24's iteration runs on the rules the goal reads (scopes: definitions_scope, completes_scope), so unrelated rules cost nothing (the reviewer's 138 s case now under 2 s); witnesses lazy, denials refuted once per KB; the search saturates from the goals alone, skips queries with parameters, derives callees first; one step function for search and checker (stepHead); decideWithin reads the profile once. P1-era: the KB-level check classifies its query once and checks the P1 roots jointly when the joint query is P2; roots exclude facts; nafCycleSymbols per NAF edge; hasModel with early exit (anySubset) and Kripke-Kleene once per enumeration; groundProgram computes calls and the level table once; roundsFrom each round's calls once; Program.ground's rank last; the split takes the members the finite guards share (Splits strengthened, splits_of_context via free constructors); the degree no longer counts parameters twice; three unused theorems removed; docs and stale passages corrected. Documented, not fixed: P2's reach (positive witnesses only; refutation at the universe's terms and one abstract value; Yes for closed queries), the gate's conservatism, pieces linked through decided atoms, witnesses on the whole KB, free calls' answers re-evaluated (S17), a derivation's round not checked.

