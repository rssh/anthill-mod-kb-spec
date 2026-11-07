## Attributes

- id: WI-20261026-SYMNV-s15-compose-static-admission
- created: 2026-10-26T08:32:37Z

- status: Open
- status_agent: user
- status_at: 2026-10-26T08:32:37Z

- acceptance: lake build

- depends_on: WI-20261026-ANXY6-s10-implement-evidence-first, WI-20261026-P6JQV-s12-admit-explicit-induction, WI-20261026-5G8F5-s14-implement-dictionary-law

- tags: resolution-machine

## Description

S15: Compose static admission across proof imports, NAF, induction, and dictionaries

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: extend the initial admission checker with capability summaries and evidence dependencies for all implemented commands. Define the final Ready-plan invariant across dynamic/local contexts and admitted dictionary calls.
Acceptance:
- Ready plans cannot encounter a missing logical capability under their checked input contracts; NeedsEvidence identifies the originating formula and dependency path before evaluation.
- Distinguish using existing evidence from discovering it, particularly for NAF and rigid predicate applications.
- Verify recurrence/stratification/strategy conditions chosen in S01; cycles among true dictionary laws or induction rules are not automatically admitted.
- Recheck on KB, registry, proof, or primitive-contract changes; reject stale plans. Lowered formulas need no recheck: they read only the signature naming, and registry changes reach the KB as generated facts.
- Add a matrix of admitted and proof-required examples spanning every implemented construct.
- Integrate S08's supplied-Term proof route and S14's complete evaluator contracts as P1 routes alongside embedded P0. Check available rule-checking capabilities without requiring automatic P1 admission of a proof tree's formulas.
- Prove successful P2 runs export finite Term proof trees accepted by the P1 checker for the same answer instance, snapshot, and context, including the tracked NAF provider. Export records successful choices and does not replay search; exhausted/Unknown runs produce no completed proof tree.
- Maintain the P1 route ownership/deferment table in docs/resolution-implementation-plan.md. Finite saturation, stratified finite-rule evaluation, finite quantifier/reference decisions, complete finite-answer enumeration, and complete propositional search are deferred procedures in this sequence; their absence yields NeedsEvidence for a decision request, never a P2 fallback. Generic contract support alone does not enable them.
- Document what remains in the broader proof layer; no completeness claim for arbitrary Term formulas.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.

Profile composition acceptance (S01 revision): use one syntax and one Step/run. Prove P0-to-P1-to-P2 admission inclusion and preservation of embedded plans. P1 requires totality, soundness, and completeness for a named decision problem, with no completed Unknown result. P2 may exhaust a terminating proof strategy with Unknown. A decision request cannot silently fall back to P2. Generic induction/law search is P2 unless a complete decision contract is supplied; keep non-derivability distinct from semantic refutation and NAF evidence. See docs/lean-admission-contract.md.
## Changes

### 2026-10-31T19:37:46Z — feedback — user

Add a program-level admission check across the P1 routes (requested 2026-10-31): for a program and a declared query class, decide statically that some admitted route answers every query in the class with Yes/No, and prove it (the P1 analogue of Admission.checkProgram / checkProgram_decides from S07). It is sufficient, not complete; it must state the query class (ground vs open queries); explicit-proof routes do not count, but imported facts do (admitImports changes the program).

### 2026-10-31T20:10:39Z — feedback — user

For the program-level check: split Admission.Input into a program/snapshot part and a query part, so a program-level check reads no query by its type (today checkProgram takes a whole Input and runs check on input.ask [] .truth).

### 2026-10-31T20:41:25Z — feedback — user

For the program-level check, keep a reusable admission: today checkProgram discards the plan of the empty query, so every query re-runs the whole check (requests over all KB clauses, topoRank, cycle search). A program-level artifact (consistency, KB classes, rank witness) from which each query's plan is built, checking only that query's classes and guard facts, would avoid it.

### 2026-11-07T11:21:09Z — feedback — user

NAF in induction cases (from S12, 2026-11-07): S12's Induction.check reports NAF in the query's context or in a clause the cases may select as a negation need (CaseGap .negation), because Plan.run is the left strategy alone. Run the plan's selection under S10's nafByRefutation (completion + vocabulary), so such NAF is admitted rather than reported, with soundness through S10's NAF provider, and include that provider in the P2 export theorem.

