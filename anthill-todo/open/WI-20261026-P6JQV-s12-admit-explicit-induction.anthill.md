## Attributes

- id: WI-20261026-P6JQV-s12-admit-explicit-induction
- created: 2026-10-26T08:32:32Z

- status: Open
- status_agent: user
- status_at: 2026-10-26T08:32:32Z

- acceptance: lake build

- depends_on: WI-20261026-DABJW-s11-add-ho-apply-conversion, WI-20261026-ZPV53-s08-define-checked-proof, WI-20261026-NG07C-s07-build-the-initial-static

- tags: resolution-machine

## Description

S12: Formalize admitted induction and prove the Nat example

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: supply a model-valid Nat induction principle over registered predicate references and a checked strategy/proof application that produces the base and scoped-step obligations. Extend admission for this justified path, not unrestricted recursive induction selection.
Acceptance:
- Execute or check forall x:Nat reachable(x) by whole-formula induction-head selection.
- The step uses a fresh n, Nat membership, and local induction hypothesis; scope restoration is demonstrated.
- Registry membership does not substitute for proving the induction principle valid in the shared model.
- Lower the induction rule through `elaborateClause?` with P at `.predicate 1`; a D_all range on P is rejected.
- Repeated selection of induction on its own subgoals cannot evade the selected strategy's termination/admission contract.
- Base/step dependencies requiring extensions are reported before execution.
- Result reconstructs the original guarded universal, reusing InductionModel and InductiveSoundness.
- Export a successful induction proof as a Term tree containing the principle application, predicate instantiation, base proof, and scoped step proof. Prove P1 checks this tree via known rule procedures even when the universal and intermediate formulas have no P1 discovery plan; induction search remains P2 unless a separate complete decision contract applies.
Include rejected forged induction evidence and a domain mismatch; no automatic generic induction axiom for arbitrary domains.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.
