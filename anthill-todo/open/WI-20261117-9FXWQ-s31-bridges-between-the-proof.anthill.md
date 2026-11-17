## Attributes

- id: WI-20261117-9FXWQ-s31-bridges-between-the-proof
- created: 2026-11-17T20:24:33Z

- status: Open
- status_agent: user
- status_at: 2026-11-17T20:24:33Z

- acceptance: lake build

- depends_on: WI-20261117-HYJ2C-s28-the-ir-evaluator-exact-p1, WI-20261117-A0H19-s29-admission-as-translation, WI-20261103-2QMVP-s20-use-checked-lemmas-inside, WI-20261026-P6JQV-s12-admit-explicit-induction

- tags: resolution-machine

## Description

S31: Bridges between the proof machine and the decision IR: the oracle and derived rules

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: docs/decision-ir.md, "The proof machine and the bridges": proof search on the shared machine uses the evaluator's decisions as checked evidence, and checked proofs return to the translation as derived rules.

Acceptance:
- Oracle: a strategy of the shared machine may ask the evaluator about a subgoal the translator accepts. A Yes with a derivation is spliced in as its exported S08 tree; any other Yes is a decision node checked by recomputation (a new S08 RuleCheck); a No is NAF evidence (a NafCheck recomputing it). Soundness through S28's exactness and S29's translation theorem.
- Derived rules: a checked lemma (an S08 import, S20) whose statement normalizes to rules becomes derived rules of the IR, never part of the completion. S12's induction cases may use the oracle for NAF in the clauses they select (S15's note of 2026-11-07).
- Traces: an induction case closing a NAF subgoal through the oracle; a decision node checked, and a tampered one rejected; ∀x∈C. P(x) proved, then used as a derived rule; the derived rule leaving an Unknown's witnesses unchanged.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs.
Design references: docs/decision-ir.md, docs/proof-checking.md, docs/machine-lemmas.md, docs/machine-induction.md.

