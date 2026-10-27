## Attributes

- id: WI-20261026-9CQKX-s06-implement-ordinary-clause
- created: 2026-10-26T08:32:23Z

- status: Open
- status_agent: user
- status_at: 2026-10-26T08:32:23Z

- acceptance: lake build

- depends_on: WI-20261026-GGP59-s05-implement-capture-safe

- tags: resolution-machine

## Description

S06: Formalize ordinary clause selection and positive execution

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: implement the first executable slice using the machine IR: truth, assumptions, conjunction/disjunction, scoped implication introduction, quantifier introduction where admitted, ordinary atomic clause selection, body execution, and FinishClause continuations. Supply an effective program representation rather than relying on semantic set membership.
Acceptance:
- Candidate selection freshens a clause and replaces the focused goal with its instantiated body; it never adds an unproved head.
- The effective program includes the generated signature clauses (`Elaboration.signatureKb`) alongside the lowered KB clauses. Range annotations come from the formula generator; a rejection by `elaborate?` or `elaborateClause?` is reported, never replaced by a default.
- Lowered clause bodies begin with range guards. Do not run a guard on a still-unbound variable as an enumerating generator ahead of the body; schedule it after binding or justify the order. Reconstruction is unaffected, since conjunct order does not change `Derives`.
- Local rule provenance and captured names are preserved; explicit binders are instantiated correctly.
- A successful trace reconstructs Derives for its answer instance.
- Successful commands construct proof-tree nodes through the S04 interfaces, retaining clause instances, substitutions, and scoped assumptions for later Term export and checking in S08.
- Exhausting one candidate does not declare the goal false; loops are handled according to the S01 profile.
- Focused regressions cover candidate backtracking, local-rule lifetime, existential answers, and single completion of nested goals.
Keep arbitrary compound-head search and NAF out of this initial runtime slice. S07 owns the complete P0 evaluator, including nested ground NAF and exhaustive failure; S10 later adds evidence-first and scoped NAF routes.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.
