## Attributes

- id: WI-20261026-265RZ-s03-elaborate-scoped-data-and
- created: 2026-10-26T08:32:19Z

- status: Open
- status_agent: user
- status_at: 2026-10-26T08:32:19Z

- acceptance: lake build

- depends_on: WI-20261026-3AAXX-s02-specify-data-ranges-and

- tags: resolution-machine

## Description

S03: Formalize guarded quantifier elaboration over the existing Term syntax

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: formalize capture-safe guarded elaboration of already represented formulas, contexts, and rule templates using existing Term and domain structures. No concrete surface syntax or parser is required. Universal ranges become implication guards; existential ranges become conjunction guards. Preserve ho_apply and explicit dictionary calls. Guard implicitly quantified clause variables consistently with their declared ranges.
Acceptance:
- Reuse Universal.toTerm and forallAll_intro; add the missing general elaboration/exists support.
- Prove relevant satisfaction, substitution, and scope properties against the foundation model.
- Test shadowing, predicate ranges, empty/overlapping data domains, and semantic carrier values outside generated data.
- No assumption of whole-carrier coverage unless explicitly required.
- Clarify the default range of an unannotated binder in the executable profile; do not guard predicate variables with D_all.
Files: InductiveDomains, Opening, Substitution, UniversalIntroduction and new focused modules as appropriate.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.
