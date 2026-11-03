## Attributes

- id: WI-20261103-2QMVP-s20-use-checked-lemmas-inside
- created: 2026-11-03T12:17:57Z

- status: Open
- status_agent: user
- status_at: 2026-11-03T12:17:57Z

- acceptance: lake build

- depends_on: WI-20261026-WHDHK-s09-implement-left-rule, WI-20261026-ZPV53-s08-define-checked-proof

- tags: resolution-machine

## Description

S20: Use checked lemmas inside machine runs

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: let a run close a subgoal with a checked lemma instead of rediscovering it (the P2 row "Assumption or supplied theorem: return its proof"). Today checked proofs reach execution only as closed facts and rules in the P0 classes (`admitImports`) or answer a whole query (`admit`). A universal theorem, one proved under assumptions, or one outside the P0 classes stays in the proof layer, and the machine has no node for a lemma: `RuleApp` has no counterpart of S08's `Rule.reference`.

Decided form: a lemma is declared as its own kind of input entry beside clauses (name, statement, its context, checked proof term), building on S08's `ProofImport` and import table. Statements stay ordinary formulas: no citation marker in formulas, no new `Term` constructor, no surface syntax. Only exported trees mention `reference`.

Acceptance:
- Strategies receive the lemma table. A lemma is offered only once it is checked against the run's checker (`Imports.Checked`); an unchecked lemma, one checked against another snapshot, or a stale one is never offered.
- A machine candidate closes a focus by a lemma. An atomic conclusion is used by backchaining at fresh flexible witnesses, as `positive` uses a local rule; a universal lemma `∀x̄. (B → H)` is instantiated with its premise `B` as an obligation; S09's left commands apply to a lemma with a compound conclusion.
- A lemma proved under assumptions is not a global fact: its context must be among the use site's assumptions, as S08's `Resolves` requires.
- The lemma node is a machine rule with a `SoundUnder` contract from the lemma's checked derivation, and the extended strategy proves `Strategy.Sound`.
- Export: the node exports as `Rule.reference` with the eliminations of its instance. The checker re-checks the referenced proof under the use site's context: context-indexed NAF evidence is re-checked there, and no weakening is assumed. Prove the construction passes checking when the reference resolves.
- Traces: a universal lemma used twice with different witnesses; a lemma with assumptions where its context is absent (not offered / rejected); a lemma whose NAF evidence holds only under another context (rejected at the use site); a self-referencing lemma (never accepted); exported runs accepted.
- Static diagnostics: a formula usable through a checked lemma is a proof-layer capability, never P0-Ready; `admitImports` remains the only route of a lemma into a P0 program.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md, docs/resolution-implementation-plan.md, docs/proof-checking.md, docs/machine-left.md.

