## Attributes

- id: WI-20261107-R9YMZ-s24-tabled-backtracking-on-the
- created: 2026-11-07T14:54:18Z

- status: Open
- status_agent: user
- status_at: 2026-11-07T14:54:18Z

- acceptance: lake build

- depends_on: WI-20261107-7PQMQ-s23-moded-structural-recursion, WI-20261107-JA6WZ-s22-answers-yes-no-unknown-and, WI-20261026-ANXY6-s10-implement-evidence-first

- tags: resolution-machine

## Description

S24: Tabled backtracking on the shared machine

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: the execution side of docs/fast-decision-routes.md: tabling as an extension of the shared machine, answering S22's four results against the Clark completion for S23's P1 and P2 predicates.

Decided form (2026-11-07, with the user): answers are against the completion, so a goal cut on a positive cycle is Unknown, not a least-model No. Fuel bounds term growth, and running out of fuel is Undecided, never Unknown.

Acceptance:
- Machine: a table per distinct call (a variant, as read) and context. A repeated call consumes its table; a recursive call waits for answers instead of looping; tables complete per strongly connected component; a loop through NAF is delayed and resolved when its component completes (SLG resolution). Table answers keep their derivations. The run invariants (step_valid, step_sound, run_success) and reconstruction are extended.
- Termination: a P1 predicate's run ends without needing fuel, within a bound from S23's count of distinct calls; a P2 run is bounded by fuel.
- Answers: Yes with Derives; No for a completed search whose failure depends on no cycle; Unknown for a completed search the completion leaves open, with two checked witness models; Undecided for fuel exhaustion (naming the growing call), an inconsistent completion (p :- ¬p), or witnesses that do not check. Each answer's soundness is proved, and answers are monotone in the fuel: only Undecided changes with more fuel.
- Exact Unknown in P1: for positive recursion, the completion's models are the fixpoints of the clauses' consequence operator (a theorem); over the finitely many calls, an atom in the least fixpoint is Yes, one outside the greatest No, one in between Unknown with the two fixpoints as witnesses.
- An open predicate reached gives Unknown, as S22 specifies, without a refutation run.
- Export: a Yes exports as an S08 tree, table answers expanded from their derivations; the exported trees are proved to pass checking.
- docs/resolution-implementation-plan.md's route table: this route replaces the deferred "finite rule saturation" and "stratified NAF over finite rules".
- Traces: path over a cyclic graph (path(a, b) Yes; path(a, c) with c unreachable Unknown with its fixpoint witnesses; the same over an acyclic graph No); left recursion terminating; p :- ¬q, q :- ¬p Unknown; p :- ¬p Undecided; p(x) :- p(succ(x)) Undecided by fuel, naming the call; a trace showing each distinct call evaluated once.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs.
Design references: docs/fast-decision-routes.md, docs/machine-state.md, docs/machine-delay.md, docs/machine-negation.md.

