## Attributes

- id: WI-20261026-VJVCB-s01-define-the-first
- created: 2026-10-26T08:32:16Z

- status: Delivered
- status_agent: codex
- status_at: 2026-10-26T10:09:02Z

- acceptance: lake build

- tags: resolution-machine

## Description

S01: Specify the Lean admission and operational-semantics contract

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: define the next Lean formalization layer in anthill-mod-kb-spec: the abstract state-machine semantics, static admission judgments, evidence contracts, and their relationship to the existing declarative calculus. Reuse Term, Derives, substitution/scope machinery, domain models, and current certificates. Anthill docs/proposals may clarify requirements but production API mapping is not a deliverable.
Acceptance:
- Specify Ready, NeedsEvidence, Invalid, and execution/evidence outcomes, distinguishing branch failure, non-derivability, and semantic refutation.
- Specify P0, P1, and P2 as nested admission rules for the same syntax and state machine. P1 requires terminating, sound, complete decision procedures for an explicit problem; P2 admits proof strategies that may return Unknown. State admission conditions and negative-result meanings, preserve embedded plans, and prohibit silent fallback from a decision request to P2.
- Identify the precise Lean definitions and theorem obligations for transition preservation, reconstruction, and no-missing-capability admission.
- Inventory existing lemmas that can be reused and genuine proof gaps, especially scoped NAF and compound induction heads.
- Define a small set of mathematical regression examples covering ordinary resolution, data/predicate quantification, induction, and dictionary laws.
- Do not design a parser, serialized proof format, Rust API, term storage representation, or crate layout. No external repository changes or Rust builds are needed.
Deliver the formal contract and a Lean-oriented implementation breakdown, not a production bootstrap.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.

## Changes

### 2026-10-26T09:17:40Z — feedback — user

Delivered S01 as docs/lean-admission-contract.md. It selects P0 (finite ground acyclic resolution), specifies Ready/NeedsEvidence/Invalid and evidence outcomes, gives the dependency-rank termination argument and exact model/NAF assumptions, names future Lean definitions and theorem obligations, inventories existing lemmas and gaps, and defines R01-R16 mathematical regressions. Updated the design, roadmap, and implementation notes to link the contract. This is the requested specification deliverable: no new checker or theorem is claimed implemented, no Term redesign, parser, or Rust work. Validation passed: lake build; lake env lean Tests/CompletedGround.lean; lake env lean Tests/ScopedNafBoundary.lean; lake env lean Tests/UniversalIntroduction.lean; git diff --check.

### 2026-10-26T10:09:01Z — feedback — user

Revised S01 after user review: P0 is only the ground acyclic baseline, P1 collects certified decidable routes (termination plus soundness and completeness for an explicit decision problem), and P2 covers incomplete proof strategies with Unknown permitted. All share Term, Step, and run. Added the P1 procedure catalog, negative-result semantics, profile inclusion/preservation obligations, requested-guarantee admission, and R17-R24 regressions. Generic induction/law search is P2 unless given a complete decision contract. Updated roadmap/design notes and S15/S16 acceptance criteria. Validation: lake build, git diff --check, and anthill-todo fsck passed. This remains a specification; decision procedures are not claimed implemented.

### 2026-10-26T14:03:14Z — feedback — user

Updated the contract and S04-S17 tickets after proof-tree review: explicit proofs are finite trees in the shared logic passed as Term; P1 checks each rule application by a known terminating procedure without requiring P1 discovery admission of its formulas. S07 owns the full P0 evaluator including ranked termination, nested ground NAF, and exhaustive failure. S08 owns tree encoding/checking; S09-S14 construct checkable nodes; S15-S17 prove and test P2 export followed by P1 checking. The roadmap now assigns the implemented P1 routes and explicitly defers the remaining catalog procedures, with NeedsEvidence for unsupported decision requests. Ticket IDs, statuses, and dependencies are preserved. Validation: anthill-todo fsck and documentation consistency checks.
