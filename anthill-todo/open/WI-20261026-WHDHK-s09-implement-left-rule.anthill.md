## Attributes

- id: WI-20261026-WHDHK-s09-implement-left-rule
- created: 2026-10-26T08:32:28Z

- status: Open
- status_agent: user
- status_at: 2026-10-26T08:32:28Z

- acceptance: lake build

- depends_on: WI-20261026-9CQKX-s06-implement-ordinary-clause, WI-20261026-ZPV53-s08-define-checked-proof

- tags: resolution-machine

## Description

S09: Formalize left-rule commands and compound clause-head proof construction

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: implement explicit assumption selection and continuations for general formulas in the proof layer, exposing core admission only for justified cases. Cover conjunction/disjunction, existential/universal assumptions, implication-left, compound heads, falsity, and logical negation.
Acceptance:
- Implication selection proves A then makes B available while resuming C; adding A->B alone does not automatically evaluate A.
- Disjunctive assumptions use two AND contexts; existential assumptions introduce local rigid witnesses.
- Conjunctive heads may split into conditional clauses; disjunctive heads branch only after their body is established.
- A head P->Q remains a local rule after the condition succeeds; logical-not heads compile to conditional falsity.
- Each command reconstructs existing Derives rules and has success/failure traces and scope tests.
- Each successful command constructs a proof tree encoded as Term through S08, with a known terminating checker for its rule application. Prove exported nodes pass checking, including both disjunction-elimination branches and discharged local assumptions; automatic P1 discovery of these formulas is not required.
- Static diagnostics distinguish proof-layer capabilities from admitted automatic execution; no assertion that general search terminates.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.
