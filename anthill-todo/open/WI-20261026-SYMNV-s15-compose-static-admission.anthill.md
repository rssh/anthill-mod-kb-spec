## Attributes

- id: WI-20261026-SYMNV-s15-compose-static-admission
- created: 2026-10-26T08:32:37Z

- status: Open
- status_agent: user
- status_at: 2026-10-26T08:32:37Z

- acceptance: lake build

- depends_on: WI-20261026-ANXY6-s10-implement-evidence-first, WI-20261026-P6JQV-s12-admit-explicit-induction, WI-20261026-5G8F5-s14-implement-dictionary-law, WI-20261107-JA6WZ-s22-answers-yes-no-unknown-and, WI-20261107-7PQMQ-s23-moded-structural-recursion, WI-20261107-R9YMZ-s24-tabled-backtracking-on-the, WI-20261107-Q3FVM-s26-contexts-in-tabled, WI-20261107-SFQPM-s25-regular-unary-predicates, WI-20261103-2QMVP-s20-use-checked-lemmas-inside, WI-20261103-N17GV-s21-constraint-solvers-on-the

- tags: resolution-machine

## Description

S15: Compose static admission across the profiles

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: compose admission over P0, P1 (embedded P0, supplied proofs, the tabled fragment's exact part, regular predicates, dictionary evaluators), P2 (budgeted tabled evaluation), imports and checked lemmas, answering with S22's results (docs/fast-decision-routes.md, docs/lean-admission-contract.md). Define the final Ready-plan invariant across dynamic and local contexts and admitted dictionary calls. Reorganized 2026-11-07 for the four profiles.

Acceptance:
- Ready plans cannot encounter a missing logical capability under their checked input contracts; Undecided blockers identify the originating formula and dependency path before evaluation.
- Distinguish using existing evidence from discovering it, particularly for NAF and rigid predicate applications.
- Profile inclusion: P0 ⊂ P1 ⊂ P2 ⊂ P3 admission, with one syntax and one run, and embedded plans preserved. P1 decisions are total, sound, and complete for a named problem, answering Yes, No, or the logical Unknown; P2 runs may end Undecided by fuel; P3 strategies are proof producers whose results enter as checked proofs. A decision request never silently falls back to P2 or P3.
- Recheck on KB, registry, proof, or primitive-contract changes; reject stale plans. Lowered formulas need no recheck: they read only the signature naming, and registry changes reach the KB as generated facts.
- A matrix of admitted and proof-required examples spanning every implemented construct.
- Integrate S08's supplied-Term proof route and S14's evaluator contracts as P1 routes. Check available rule-checking capabilities without requiring automatic P1 admission of a proof tree's formulas.
- Prove successful P3 runs export finite Term proof trees accepted by the P1 checker for the same answer instance, snapshot, and context, including the tracked NAF provider. Export records successful choices and does not replay search; exhausted or interrupted runs produce no completed proof tree.
- Maintain the route ownership table in docs/resolution-implementation-plan.md.
- Document what remains in the broader proof layer; no completeness claim for arbitrary Term formulas.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/fast-decision-routes.md, docs/lean-admission-contract.md, docs/resolution-state-machine.md, docs/resolution-implementation-plan.md.

## Changes

### 2026-10-31T19:37:46Z — feedback — user

Add a program-level admission check across the P1 routes (requested 2026-10-31): for a program and a declared query class, decide statically that some admitted route answers every query in the class with Yes/No, and prove it (the P1 analogue of Admission.checkProgram / checkProgram_decides from S07). It is sufficient, not complete; it must state the query class (ground vs open queries); explicit-proof routes do not count, but imported facts do (admitImports changes the program).

### 2026-10-31T20:10:39Z — feedback — user

For the program-level check: split Admission.Input into a program/snapshot part and a query part, so a program-level check reads no query by its type (today checkProgram takes a whole Input and runs check on input.ask [] .truth).

### 2026-10-31T20:41:25Z — feedback — user

For the program-level check, keep a reusable admission: today checkProgram discards the plan of the empty query, so every query re-runs the whole check (requests over all KB clauses, topoRank, cycle search). A program-level artifact (consistency, KB classes, rank witness) from which each query's plan is built, checking only that query's classes and guard facts, would avoid it.

### 2026-11-07T11:21:09Z — feedback — user

NAF in induction cases (from S12, 2026-11-07): S12's Induction.check reports NAF in the query's context or in a clause the cases may select as a negation need (CaseGap .negation), because Plan.run is the left strategy alone. Run the plan's selection under S10's nafByRefutation (completion + vocabulary), so such NAF is admitted rather than reported, with soundness through S10's NAF provider, and include that provider in the P3 export theorem.

### 2026-11-07T13:03:20Z — feedback — user

Correction to the 2026-11-07 NAF note: only NAF as a goal in a clause the S12 cases may select is a negation need (CaseGap .negation). NAF assumed in the query's context is a hypothesis, reported as P0's scopedProof request, and is not a route for nafByRefutation.
### 2026-11-07T18:44:39Z — feedback — user

From S13 (dictionary registry): S13 classifies one call at a time (Registry.access? with its Position); it does not traverse formulas. Composition runs Registry.WellFormed (Invalid on failure: an inconsistent registry) and access? at every dictionaryCall site with that site's position, turning non-declared accesses into blockers via Access.blocker?.

### 2026-11-07T21:18:59Z — feedback — user

Correction to the S13 note after review: the consistency check is Snapshot.WellFormed (the registry's own consistency plus separation of its symbols from the signature's membership symbols and D_all; separation from P_n stays a naming hypothesis). Each access has a Verdict (Access.verdict): runs, blocked with its reason (Missing.mode for a dictionary variable, construct (dictionary reason) otherwise), or inconsistent (an invalid input, impossible in a well-formed registry: access?_consistent). Plan reuse is Snapshot.Unchanged (signature, naming, and the names read); Registration.Checked.transfer carries evidence across it.

### 2026-11-08T17:17:34Z — feedback — user

From S24 (2026-11-08): a tabled Yes is exported as an S08 term with every table answer expanded from its own proof (Setup.exportWith) and filtered by the S08 checker, whose NAF evidence is a universe the checker refutes the operand over again (Setup.nafCheck). That every successful tabled run's export checks is S15/S16's, as for S06 runs.

