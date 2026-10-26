## Attributes

- id: WI-20261026-NG07C-s07-build-the-initial-static
- created: 2026-10-26T08:32:25Z

- status: Open
- status_agent: user
- status_at: 2026-10-26T08:32:25Z

- acceptance: lake build

- depends_on: WI-20261026-9CQKX-s06-implement-ordinary-clause

- tags: resolution-machine

## Description

S07: Formalize P0 admission, total evaluation, and Ready plans

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: implement the full ground acyclic P0 baseline specified by docs/lean-admission-contract.md, extending S06's shared machine with nested ground NAF and complete-failure evaluation. Check admission before rule evaluation and emit Ready(plan), NeedsEvidence(obligations with formula/obligation identifiers and reasons), or Invalid. Broader command admission is composed in S15.
Acceptance:
- Check the exact P0 data/atom/goal/clause/context restrictions and the entire finite program's dependency graph, including dependencies under nested NAF. Construct and verify a topological rank; cycles yield NeedsEvidence for another route, never semantic falsity.
- Prove check_ready_sound and check_p0_complete for structurally valid acyclic P0 inputs. No speculative proof search is used to classify capabilities.
- Extend the same Step/run with P0 NAF operand evaluation and exhaustive candidate failure. Prove every completed P0 run returns GroundSearch.Succeeds or GroundSearch.Fails for the original program/context/goal, and prove totality using the checked rank and structural goal measure.
- Track exact snapshot/context in negative certificates; reconstruct successful proofs with the correct ground NAF provider. Semantic failure adequacy retains the completed-model hypotheses; S16 owns the general P0 completed-model witness.
- Preserve evidence through the S04 proof-tree interfaces, including negative certificates required by NAF nodes, for S08 export/checking.
- Ready is capability/admission evidence, not proof that the goal is true.
- State and prove the initial no-missing-capability invariant for plans run under their input contracts, and establish the profile's promised termination property.
- Tests admit ordinary examples and reject unsupported operations with actionable evidence requests before execution.
- Changes to program/signature/contracts invalidate affected plans.
- Document completeness/negative-answer limitations precisely; bounded fuel is not a proof of termination or refutation.
- Cover contract regressions R01-R06: nested NAF, all-candidate failure, success after a failed candidate, positive/negative cycle rejection, and stale context evidence. This ticket is executable without S10; scoped/open NAF remains S10's responsibility.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.
