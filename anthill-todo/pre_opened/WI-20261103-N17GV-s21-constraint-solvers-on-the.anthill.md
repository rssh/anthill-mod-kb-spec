## Attributes

- id: WI-20261103-N17GV-s21-constraint-solvers-on-the
- created: 2026-11-03T17:07:09Z

- status: PreOpened
- status_agent: user
- status_at: 2026-11-07T14:55:33Z

- acceptance: lake build

- depends_on: WI-20261026-ANXY6-s10-implement-evidence-first

- tags: resolution-machine

## Description

S21: Constraint solvers on the machine store

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: turn S18's `Store.constraints` slot into a general constraint mechanism, of which delay is the degenerate solver (check at binding = wake; at the end = flounder). S10 added the end-of-branch closing phase (`Store.close`, `step_close`): residual suspensions run once more with `Store.closing` set and no binding allowed, and evidence-first NAF refutes generically there. This ticket generalizes it.

Decided form (2026-11-03, with the user): closing has two stages, replacing `Store.closing : Bool` by a phase `running | settling | final`.
- Settle: at the end of a proved branch with residual goals or constraints, the phase becomes `settling` and the solvers receive them. A solver may bind (e.g. labeling a name over a finite domain, with choice points). A binding is an ordinary commit: it wakes what waits on the bound names (`Store.commit_wakes`), and a commit that binds while settling resets the phase to `running`, so the branch runs normally and closes again when it is proved again.
- Final: when settling binds nothing, the phase becomes `final`, frozen as S10's closing is now: no binding (`Store.Refines.closed` holds only for `final`); generic NAF on names still unbound (S10) runs only here; residual constraints are discharged with evidence or reported as conditional answers; what is left flounders.
- Ordering is the soundness argument for generic NAF: a closing NAF node is valid only if its names are never bound afterwards, so no binding may follow it. A substitution lemma for checked evidence is not needed for this design.
- Termination: settle rounds may repeat; the run is bounded by fuel, and a solver admitted by P3 states a progress measure (e.g. each round binds a name over a finite domain).

Acceptance:
- A solver interface for constraints: a decidable check at every binding (consistency; a failed check fails the commit), a discharge rule (entailment) with evidence that exports as S08 nodes or checked certificates, and a residual form at the end.
- Constraints introduced by strategies through a response (not only by hand), attached to the names they concern and restored by rollback like suspensions; `Store.Scoped` and the run invariants extended.
- The two-stage closing as decided above: the phase in the store, the transitions running → settling → (running after a binding | final) → flounder, `step_*` characterizations for each, and the run invariants (`step_valid`, `step_sound`, `step_success`, `run_exhausted`) extended. `Store.Refines.closed` and `Store.read_stableNegation` restated for `final`; S10's closing NAF moved to `final` with its traces kept.
- A settling solver's binding is a candidate with `CandidateSound`, and returning to running keeps the branch valid; a trace where labeling in settle binds a name, wakes a delayed goal, and the branch closes again.
- Conditional answers: a success that leaves solver-owned residual constraints is reported as an answer under those constraints, with a semantic statement (the answer holds in every environment satisfying them), not as floundering.
- First solvers: disequality (`X ≠ t`, checked at each binding, discharged by the free equality theory) and constructive negation for NAF on flexible operands (`naf p(X)` with `p(one)` answers `X ≠ one`), with evidence from the S10 completion.
- Traces: a conditional answer, a constraint failing a later binding with rollback, a discharged constraint exported and checked, and floundering kept for goals no solver owns.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs.
Design references: docs/machine-delay.md (Restrictions and constraints, Closing), docs/machine-negation.md, docs/resolution-state-machine.md.

## Changes

### 2026-11-07T14:55:34Z — feedback — user

Moved to the backlog (2026-11-07 reorganization): not needed for the fast fragment (docs/fast-decision-routes.md). Constructive negation would later relax the fragment's ground-NAF safety condition, and constraints would then need to live in S24's tables; disequality is a candidate first solver there.

