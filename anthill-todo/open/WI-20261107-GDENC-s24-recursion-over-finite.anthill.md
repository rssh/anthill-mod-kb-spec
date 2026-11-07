## Attributes

- id: WI-20261107-GDENC-s24-recursion-over-finite
- created: 2026-11-07T13:58:08Z

- status: Open
- status_agent: user
- status_at: 2026-11-07T13:58:08Z

- acceptance: lake build

- depends_on: WI-20261107-7PQMQ-s23-moded-structural-recursion, WI-20261107-JA6WZ-s22-answers-yes-no-unknown-and

- tags: resolution-machine

## Description

S24: Recursion over finite domains with a loop check

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: the second fast decision route of docs/fast-decision-routes.md. Decided with the user (2026-11-07): answers are against the Clark completion, so a goal cut on a positive cycle is Unknown, not a least-model No.

Acceptance:
- Admission: recursion whose recursive arguments range over finite domains (a domain is finite when, by its rules, no constructor of it takes it, directly or through other domains), calls ground by S23's modes, and stratified NAF (no NAF inside a cycle).
- Machine: a loop check: a goal identical, as read, to one of its ancestors on the current branch is cut, and the cut is recorded in the branch's outcome. The run invariants and reconstruction are kept.
- Termination: finitely many distinct ground goals, so every admitted run ends without fuel exhaustion.
- Answers: a proof is Yes; a failure that depends on no cut is No (finite failure is sound for the completion); a failure that depends on a cut is Unknown, with S22's two witnesses (the cycle's atoms all true and all false, checked against the KB's clauses and denials); witnesses that do not check give Undecided naming the cycle. Each answer's soundness is proved.
- docs/resolution-implementation-plan.md's route table: this route replaces the deferred "finite rule saturation" and "stratified NAF over finite rules", which assumed a least-relation decision.
- Traces: path over a cyclic graph, path(a, b) Yes and path(a, c) with c unreachable Unknown with its witnesses; the same query over an acyclic graph No; a denial forcing an atom of the cycle answered without Unknown.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs.
Design references: docs/fast-decision-routes.md, docs/machine-negation.md, docs/lean-admission-contract.md (finite saturation and stratified NAF entries).

