## Attributes

- id: WI-20261107-Q3FVM-s26-contexts-in-tabled
- created: 2026-11-07T14:54:20Z

- status: Open
- status_agent: user
- status_at: 2026-11-07T14:54:20Z

- acceptance: lake build

- depends_on: WI-20261107-R9YMZ-s24-tabled-backtracking-on-the, WI-20261107-JA6WZ-s22-answers-yes-no-unknown-and

- tags: resolution-machine

## Description

S26: Contexts in tabled evaluation: case splits, Harrop implications, universals

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: the contexts section of docs/fast-decision-routes.md, on S24's tabled evaluation.

Acceptance:
- Case splits: a disjunctive assumption is split eagerly, once per branch (disjunction elimination is invertible, so nothing backtracks over the split). Branch answers combine: all Yes is Yes, all No is No, Yes and No is Unknown with the branches as witnesses, each branch consistent. A split whose count depends on the data is P2, as S23 reports.
- An existential assumption is opened at a fresh name.
- An implication goal D → G with D a Harrop clause: D is a scoped local clause used by backchaining, tables keyed by the context. A ground antecedent the fragment decides is read materially (D false gives Yes, otherwise G decides); otherwise a failure is Undecided. Data-dependent antecedents are P2.
- A universal goal ∀x. G at a fresh eigenvariable: success is Yes; a failure is Undecided, except over a finite domain (expanded) or for regular predicates (S25).
- The two readings (docs/fast-decision-routes.md): goals run by hereditary Harrop execution, answers about the completion (Lloyd–Topor), so a success is Yes and other failures Undecided.
- NAF inside an implication's or a split's scope is judged against the program extended by that scope's assumptions. Theorem: every model of the original completion satisfying an assumed Harrop clause is a model of the extended completion, so a Yes is sound for the original KB.
- The soundness of each combination, with the run invariants extended.
- Traces: a split whose branches agree (Yes; No) and one whose branches disagree (Unknown); a hypothetical goal with a local rule; the material reading answering No; a generic universal Yes and its failure Undecided; ∀x:Bool. p(x) expanded.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs.
Design references: docs/fast-decision-routes.md, docs/machine-left.md, docs/machine-positive.md.
## Changes

### 2026-11-08T17:17:33Z — feedback — user

From S24 (2026-11-08): tables are keyed by the call and its context, and only closed contexts are tabled; the witnesses (Setup.witnesses) need a query with no assumptions, so a query with a context gets No or Yes but never Unknown. S26 extends the witnesses to contexts (the assumed facts and Harrop clauses as part of the witness programs) and the tables to contexts with names.

