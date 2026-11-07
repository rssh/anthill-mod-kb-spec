## Attributes

- id: WI-20261107-7PQMQ-s23-moded-structural-recursion
- created: 2026-11-07T13:58:00Z

- status: Open
- status_agent: user
- status_at: 2026-11-07T13:58:00Z

- acceptance: lake build

- depends_on: WI-20261107-JA6WZ-s22-answers-yes-no-unknown-and, WI-20261026-NG07C-s07-build-the-initial-static

- tags: resolution-machine

## Description

S23: Moded structural recursion as a P1 route

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: the first fast decision route of docs/fast-decision-routes.md. Under its admission condition the shared machine's depth-first search terminates and decides, with no machine change. Answers are S22's.

Acceptance:
- Mode declarations per predicate (input and output argument positions) and a decreasing input for each recursive predicate, as admission input the KB generator emits, like explicit binder ranges; never inferred.
- Admission checks, local and syntactic: well-moded bodies read left to right (each call's inputs ground by the head's inputs and earlier outputs; NAF and guards only on calls ground by mode); every call into the predicate's recursive group, NAF included, with its decreasing argument a strict subterm of the head's; determinism as a speed class (non-overlapping input patterns), not a blocker.
- Termination: an admitted query's run ends in success or a complete failure, never needing more fuel than a bound computed from the query's inputs (stated as P0's run_total_of_p0 is).
- Decision: success is Yes by Derives; a complete failure is No, the goal false in every model of the completion, with failure evidence like P0's; an open predicate reached is Unknown with S22's witnesses.
- Determinism: with non-overlapping input patterns, at most one clause is a candidate for each call (a theorem), and traces show no choice points.
- Blockers (S22 Undecided), each with site and path: a call not ground by mode, a recursive call not on a smaller input, NAF on a call not ground by mode.
- Traces: reachable(+) on a numeral (Yes), even(+) on succ(zero) (No), append(+, +, -) computing its output, a non-decreasing recursion reported as a blocker, an open predicate answered Unknown.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs.
Design references: docs/fast-decision-routes.md, docs/machine-p0.md, docs/lean-admission-contract.md (decision contracts).

