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

S23: The fast fragment's admission: modes, safety, cost classes, blockers

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: the admission side of docs/fast-decision-routes.md. Before anything runs, each predicate of a KB program is classified into P1, P2, or a blocker, for S24's tabled evaluation. No machine change.

Acceptance:
- Mode declarations per predicate (input and output argument positions), as admission input the KB generator emits, like explicit binder ranges; never inferred.
- Safety, the one hard condition: reading each body left to right, every variable a NAF goal, a guard, or an output uses is bound by an input or an earlier positive goal. A violation is an Undecided blocker (S22) with its site and path.
- Cost classes: complete when every recursive call's arguments are subterms of the head's inputs or data constants, budgeted otherwise. A complete predicate's degree k (roughly the free variables a clause joins) is reported, and non-overlapping input patterns are reported as determinism.
- Profiles: P1 for complete predicates with no NAF or denial over a predicate on a cycle of the dependency graph; P2 for the rest of the fragment; each construct outside the fragment (docs/fast-decision-routes.md, "Outside the fragment") a blocker.
- The classification is local: a predicate's class and blockers follow from its own clauses and the classes of the predicates they call, and a query's profile from the predicates it uses.
- Theorems: each condition is decided (spec theorems), and a complete predicate has finitely many distinct calls from any ground input, the bound S24 uses.
- Traces: reachable(+), append(+, +, -), and path(+, -) over facts classified P1 with their degrees; p(x) :- p(succ(x)) budgeted (P2); NAF over a predicate on a cycle P2; an unsafe NAF goal and a compound head as blockers.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs.
Design references: docs/fast-decision-routes.md, docs/lean-admission-contract.md (profiles), docs/machine-p0.md.

