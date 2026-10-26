## Attributes

- id: WI-20261026-GGP59-s05-implement-capture-safe
- created: 2026-10-26T08:32:22Z

- status: Open
- status_agent: user
- status_at: 2026-10-26T08:32:22Z

- acceptance: lake build

- depends_on: WI-20261026-265RZ-s03-elaborate-scoped-data-and, WI-20261026-53V6D-s04-define-machine-states

- tags: resolution-machine

## Description

S05: Prove scope-safe matching and instantiation for machine transitions

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: reuse and extend the existing Lean substitution and head-matching operations for the initial profile, keeping clause-template variables separate from rigid query parameters and shared existential metavariables. Define how committed substitutions reach pending goals and captured local contexts.
Acceptance:
- Freshening preserves local captured parameters and explicit quantifier ownership.
- Instantiation handles alpha-renaming rather than treating capture hazards as logical failure.
- Scope constraints propagate through metavariable aliases; occurs/dependency checks prevent escaping witnesses.
- Tests distinguish forall x exists y y=x from exists y forall x y=x, and confirm rollback after a rejected candidate.
- Matching outcomes distinguish mismatch from a capability not admitted by the profile.
Reuse existing Substitution, Opening, ClauseInstantiation and certificate code; preserve its soundness contracts.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.
