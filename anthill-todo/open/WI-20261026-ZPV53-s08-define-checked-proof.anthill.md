## Attributes

- id: WI-20261026-ZPV53-s08-define-checked-proof
- created: 2026-10-26T08:32:26Z

- status: Open
- status_agent: user
- status_at: 2026-10-26T08:32:26Z

- acceptance: lake build

- depends_on: WI-20261026-265RZ-s03-elaborate-scoped-data-and, WI-20261026-NG07C-s07-build-the-initial-static

- tags: resolution-machine

## Description

S08: Formalize P1 proof-tree checking as Term and proof imports

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: define a finite proof-tree encoding using the existing Term carrier, an executable checker, and CheckedProof(snapshot, context, goal, proof : Term) for the shared logic. Connect checked trees to the foundation calculus and proof imports. Reuse existing derivation/certificate objects to prove checker correctness; accepting an already constructed Lean Derives object alone does not satisfy this ticket. This is an internal formal encoding, without a public proof syntax, parser, or serialized proof format.
Acceptance:
- Specify nodes, premise subtrees, rule parameters, witnesses/substitutions, scoped assumptions, and checked-proof references. Implement recursive checking with a known terminating procedure for each supported rule application; prove termination and acceptance iff the encoded tree is valid under those rules.
- Prove accepted trees reconstruct the shared logic's Derives judgment, preserving the exact KB/context and NAF provider. New rules require explicit soundness proofs and known checking procedures in this same logic; accepting external semantic assertions alone is not the explicit-proof route.
- Cover foundation logical rules and S06-S07 evidence. Define how S09-S14 add derived-rule checks/certificates without requiring automatic discovery of their premises. Separate the generic P1 DecisionContract and rule-checking interfaces from particular search procedures.
- Neither root nor intermediate formulas require automatic P1 admission. A rule procedure checks its application given explicit premises, conclusion, and parameters; it does not search for proofs of those premises. Missing checking capabilities yield NeedsEvidence before running the plan; invalid trees are rejected.
- Provide Term export for S06-S07 successful proof trees and prove the exported trees pass checking. Manual, external, and P2-produced trees use the same checking rules; unresolved holes, circular references, scope escape, and unsupported NAF evidence cannot be accepted.
- Classify this route as a P1 decision of supplied-tree validity. Acceptance establishes the requested goal; rejection proves no negation, NAF, or non-derivability of that goal.
- Imported statements retain context, range, and KB dependencies; local proofs cannot become unconditional global facts.
- Check guard premises against the generated signature clauses: data and D_all membership through clause steps (or S07's checked membership node), and `Pred_n` guards by fact lookup on the reference symbol.
- A second operational check admits only facts/rules/primitive contracts preserving the executable profile.
- Rechecking can turn NeedsEvidence into Ready without invoking unbounded proof discovery at runtime.
- Checkers and certified primitive computations terminate; forged/stale evidence is rejected.
- Strict conservativity is distinguished from soundness under additional model assumptions; no new unchecked axioms.
Test a valid lemma import, an unproved claim, and a true recursive theorem whose direct execution is not admitted. Cover contract R25-R30, including a tree with formulas outside P1 discovery and checking of an explicit rule application. Later S09-S14 examples extend this suite as their commands become available.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.
