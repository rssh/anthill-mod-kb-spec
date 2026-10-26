## Attributes

- id: WI-20261026-9C19E-s13-specify-checked-typeless
- created: 2026-10-26T08:32:34Z

- status: Open
- status_agent: user
- status_at: 2026-10-26T08:32:34Z

- acceptance: lake build

- depends_on: WI-20261026-3AAXX-s02-specify-data-ranges-and, WI-20261026-ZPV53-s08-define-checked-proof

- tags: resolution-machine

## Description

S13: Specify checked typeless dictionary registration and domain connections

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: define the effective registry of dictionary values, interface names, nested operation paths, supported arities, associated inductive-domain membership, law proofs, and admitted primitive contracts. Reuse OperationDictionaries and OrderDictionaries.
Acceptance:
- OrdDictionary(d) and DomainMember(d,x) have checked interpretation in the existing untyped carrier.
- Each connection to D_i membership is evidence-backed, not an unchecked table assertion.
- Registry supports multiple dictionaries for one domain and guarded generic interface laws.
- Unknown dictionaries and invalid accesses are distinguished from logical falsity; Boolean values are not conflated with logical truth.
- Provide Nat and Bool registry examples connected to existing models.
- Registration/version changes invalidate affected plans and evidence as specified.
No polymorphic type system or unverified runtime evaluator is introduced.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.
