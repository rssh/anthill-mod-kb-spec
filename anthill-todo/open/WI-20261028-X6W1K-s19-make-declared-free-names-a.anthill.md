## Attributes

- id: WI-20261028-X6W1K-s19-make-declared-free-names-a
- created: 2026-10-28T17:15:25Z

- status: Open
- status_agent: user
- status_at: 2026-10-28T17:15:25Z

- acceptance: lake build

- depends_on: WI-20261026-GGP59-s05-implement-capture-safe

- tags: resolution-machine

## Description

S19: Make declared free names a machine invariant

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: every free name of every committed obligation (the focus, every frame's parent and premises, every choice point's obligation and frames under its saved store) is declared in its store: `store.info? name ≠ none`. Enforce it at commit and preserve it by every transition. Use it to replace the obligation-name freshness check by store freshness and to discharge the freshness hypotheses of the S05 opening contracts once, instead of per term at every node.
Acceptance:
- Define `Obligation.Declared store obligation` over `Term.freeVars` of the goal and assumptions (bound names excluded); add it to `State.Valid`; prove `State.init_valid` and `step_valid` preserve it, including rollback to a choice point's saved store.
- `Store.commit` checks that every premise goal and discharged assumption names only names declared in the prepared store (old names plus the candidate's flexible and rigid names); otherwise `violated`, a contract gap. Bindings already name only usable names.
- Replace the `∉ obligation.names` check by store freshness: remove `Obligation.names`, `Obligation.fresh_of_not_mem_names`, and the obligation argument of `Store.freshFor`/`Store.freshen`; simplify `Store.commit_fresh`, `prepare_scoped`, `prepare_refines`, `commit_prepared`, and `commit_unify`. Openings rename inner binders, so binder names impose nothing.
- One lemma: a rigid name opened by a commit is unbound and absent from the read goal, context, and opened body in every later scoped store refining the commit. It replaces the per-term `declared` hypothesis of `Store.commit_fresh_resolved` and bundles the freshness hypotheses of `forallIntro_soundUnder` and `existsElim_soundUnder`.
- Extend `run_success`: every node of a successful tree names only names declared in the final store.
- Regressions: a command putting an undeclared name in a premise is a contract gap (for example, a clause body variable left unfreshened); a new name equal to a binder name of the obligation is accepted; existing S04/S05 traces are unchanged.
- Update docs/machine-state.md and docs/machine-matching.md, and the S06/S16 notes on opening freshness.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/machine-state.md, docs/machine-matching.md.

