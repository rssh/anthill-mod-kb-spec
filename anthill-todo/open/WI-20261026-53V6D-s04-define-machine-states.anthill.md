## Attributes

- id: WI-20261026-53V6D-s04-define-machine-states
- created: 2026-10-26T08:32:20Z

- status: Open
- status_agent: user
- status_at: 2026-10-26T08:32:20Z

- acceptance: lake build

- depends_on: WI-20261026-VJVCB-s01-define-the-first

- tags: resolution-machine

## Description

S04: Formalize machine states, continuations, proof evidence, and branch isolation

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: define the abstract executable machine state and certificate representation: focused obligation, per-obligation local context, rigid/flexible names, dependency levels, substitution, AND/OR continuations, candidate alternatives, and rollback state. Use named command contracts independent of Lean syntax.
Acceptance:
- Specify transition input/output and completion behavior; an AND parent completes exactly once after all children.
- AND branches maintain compatible shared answer substitutions; OR alternatives restore candidate-local changes.
- Local assumptions, existential witnesses, and rigids cannot escape their scopes.
- Represent success evidence and unsuccessful/incomplete outcomes separately.
- Define proof-tree construction interfaces for successful commands: rule identity, conclusion, premise trees, explicit instantiations/witnesses, discharged assumptions, and snapshot/context dependencies. S08 supplies the encoding as Term and checker; S04 does not depend on their implementation.
- Record which evidence is monotonic and which is snapshot-indexed. Derivations from clauses, including the generated signature clauses, stay valid when the KB or registry grows; NAF and finite absence or enumeration evidence is closed-world and snapshot-indexed. Lowered formulas carry no snapshot dependency: they read only the signature naming.
- Preserve successful choices and all required premise branches so a completed proof can be exported without replaying search. Unknown/exhaustion must not produce a completed proof tree.
- Include executable or formal traces for conjunction, disjunction, nested implication, and an incompatible shared-answer case.
This ticket defines the state/evidence foundation, not an unrestricted search scheduler.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.
