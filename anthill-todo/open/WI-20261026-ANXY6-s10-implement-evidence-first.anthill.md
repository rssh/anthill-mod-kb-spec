## Attributes

- id: WI-20261026-ANXY6-s10-implement-evidence-first
- created: 2026-10-26T08:32:29Z

- status: Open
- status_agent: user
- status_at: 2026-10-26T08:32:29Z

- acceptance: lake build

- depends_on: WI-20261026-WHDHK-s09-implement-left-rule, WI-20261026-NG07C-s07-build-the-initial-static

- tags: resolution-machine

## Description

S10: Formalize evidence-first NAF and guarded-universal refutation

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: implement NAF goal dispatch that first uses assumptions/clauses, then requests certified failure where admitted. Specify and prove any new scoped/domain certificate rule needed for forall x:D_i naf-not p(x).
The total ground P0 NAF evaluator and failure certificates are delivered by S07. Reuse that baseline here; S07 must not depend on this ticket.
Acceptance:
- An assumed naf-not p(a) can be used with rigid a without initiating failure search.
- For a guarded universal negative, a specialized positive-witness query exists x D_i(x) and p(x) precedes rigid opening when its certified strategy is selected.
- The positive fact p(1) defeats a universal negative over a domain containing 1; rigid matching failure cannot establish it.
- Exhaustive finite-domain absence includes coverage evidence; infinite-domain absence needs a justified symbolic certificate or static NeedsEvidence.
- Exact KB/context dependencies are checked, including after lemma imports.
- NAF and absence certificates are snapshot-indexed closed-world evidence. Registering a predicate, adding a domain, or adding a clause invalidates them; lowered formulas stay unchanged.
- Supply Term proof-tree nodes and known terminating rule-checking procedures through S08 for every enabled NAF route, including its negative-evidence certificate. Prove successful nodes pass checking; Unknown or incomplete absence searches cannot export a completed NAF proof.
- Logical-not and NAF remain distinct. If contradiction elimination for proved P plus naf-not P is added, prove its semantic soundness explicitly.
- NAF on a flexible operand delays until the operand is bound (`Response.delay`, S18, docs/machine-delay.md: retain a dependency and retry after instantiation). Still delayed at the end it flounders as a gap, never as NAF evidence. Waiting cannot help a rigid operand, which needs a scoped certificate. Constructive-negation answers kept as unresolved constraints (`Store.constraints`) come with their solver: a check at each binding, a discharge rule, and evidence for export.
Reuse CertifiedRefutation and CounterexampleSearch; do not claim existing ground-only Derives already admits scoped NAF.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.
