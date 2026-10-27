## Attributes

- id: WI-20261026-44E32-s17-validate-performance-and
- created: 2026-10-26T08:32:40Z

- status: Open
- status_agent: user
- status_at: 2026-10-26T08:32:40Z

- acceptance: lake build

- depends_on: WI-20261026-0AA47-s16-prove-composed-machine

- tags: resolution-machine

## Description

S17: Complete Lean regression examples and document formal guarantees

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: complete the Lean example/regression suite and document exactly what the formalization proves. Consolidate reusable semantic and transition contracts for a separately scoped Rust implementation; do not implement that component here.
Acceptance:
- Run lake build and the relevant positive/negative Lean regressions, including model-backed induction, guarded NAF, compound assumptions, dictionary laws, and admission diagnostics.
- Include reproducible Lean-level transition traces showing focus, local context, generated obligations, continuations, and proof reconstruction.
- Run P2-to-Term-to-P1 round-trip regressions for induction, compound local assumptions, dictionaries, and every enabled NAF route. Check manually supplied and externally supplied example trees with the same checker, including formulas outside P1 discovery, invalid rule applications, stale references, and scope escape (contract R25-R30).
- Cover the full P0 baseline R01-R06 and distinguish deferred P1 decision routes from implemented ones. A request for a deferred route must yield NeedsEvidence; no completed P1 decision may silently use P2 or return Unknown.
- Audit theorem assumptions and axioms; document the boundary among soundness, termination, completeness for an admitted profile, and static capability coverage.
- Document which evidence is snapshot-indexed (closed-world) and which is monotonic in KB and registry growth.
- State any remaining admitted-profile or certificate limitations explicitly.
- Summarize formal interfaces and invariants a future implementation must satisfy, without choosing runtime term representation, parser, wire format, crate organization, or production APIs.
- Preserve the existing soundness/model regression suite; no Rust benchmark or Anthill integration is required.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.
