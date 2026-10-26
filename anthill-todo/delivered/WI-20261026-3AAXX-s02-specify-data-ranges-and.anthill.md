## Attributes

- id: WI-20261026-3AAXX-s02-specify-data-ranges-and
- created: 2026-10-26T08:32:17Z

- status: Delivered
- status_agent: codex
- status_at: 2026-10-26T14:16:45Z

- acceptance: lake build

- depends_on: WI-20261026-VJVCB-s01-define-the-first

- tags: resolution-machine

## Description

S02: Specify data ranges and arity-indexed predicate-reference registries

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: add a typeless signature/registry specification for data domains D_i and predicate-reference ranges P_n, interpreted over the existing shared model carrier. Distinguish flexible metavariables and rigid proof parameters from object-level values. Register predicate arities and membership evidence without introducing a polymorphic type system.
Acceptance:
- Contracts connect P_n membership to registered reference values and concrete-symbol ho_apply behavior.
- Cover permitted arity overlap, unknown references, and registry versioning; do not silently assume injective references or disjoint carriers.
- Supply a concrete model witness and tests for data versus predicate quantification, including unary reachable.
- Induction validity remains a separate model obligation.
Reuse InductiveDomains, Semantics, and OperationDictionaries; avoid changing raw forall semantics.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.

## Changes

### 2026-10-26T14:16:44Z — feedback — codex

Implemented S02 in AnthillModKbSpec/RangeRegistry.lean and imported it from the library root. Added typeless data/predicate range metadata, finite decidable symbol/arity lookup, exact semantic reference membership and snapshot-indexed ReferenceEvidence, ho_apply and existing-Term application lemmas, reference-alias coherence, full-snapshot reuse/rebase contracts, rigid/flexible name metadata, exact data interpretation via InductiveDomains, and an explicit compatibility bridge to OperationDictionaries references. Added Tests/RangeRegistry.lean with a concrete InductionModel witness, unary reachable and overlapping arities, data/predicate quantification, unchanged raw forall semantics, data/predicate overlap, aliased unknown references, compatible and incompatible dictionary references, and stale evidence including unchanged revision numbers. Key results pass the standard-axiom audit. Documented interfaces and later-ticket boundaries in docs/range-registry.md and linked the implementation inventory. Validation passed: lake build; lake env lean Tests/RangeRegistry.lean; Tests/InductiveDomains.lean; Tests/OperationDictionaries.lean; Tests/InductionModel.lean; Tests/UniversalIntroduction.lean; git diff --check. Registry evidence does not assert induction validity; guarded elaboration, scope enforcement, and executable admission remain S03-S15 work.

### 2026-10-26T18:19:00Z — feedback — codex

Follow-up after the module reorganization: AnthillModKbSpec/RangeRegistry.lean is now AnthillModKbSpec/Resolution/AdmissionSignature.lean; Tests/RangeRegistry.lean is now Tests/Resolution/AdmissionSignature.lean; docs/range-registry.md is now docs/admission-signature.md. Other tests named in the delivery note now live at Tests/Foundation/InductiveDomains.lean, Tests/Foundation/OperationDictionaries.lean, Tests/Models/InductionModel.lean, and Tests/Foundation/UniversalIntroduction.lean. The original delivery note records the paths at delivery time and is preserved.
