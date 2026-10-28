## Attributes

- id: WI-20261026-0AA47-s16-prove-composed-machine
- created: 2026-10-26T08:32:38Z

- status: Open
- status_agent: user
- status_at: 2026-10-26T08:32:38Z

- acceptance: lake build

- depends_on: WI-20261026-SYMNV-s15-compose-static-admission

- tags: resolution-machine

## Description

S16: Prove composed machine soundness through elaboration and the declarative calculus

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: assemble local reconstruction lemmas into the end-to-end theorem for accepted executions/proofs: foundation derivability of the elaborated answer, then semantic soundness via existing Model.sound or InductiveSoundness.declarative_sound.
Acceptance:
- Handle contexts, substitutions, scopes, domain/predicate guards, imported lemmas, and operation equations.
- Compose the S05 per-node read-through contracts (`Expansion.SoundUnder`) along a successful run: the final store refines each commit's store (`Store.Refines`), so matched readings persist (`Store.Refines.resolve_eq`) and opened names stay fresh for read obligations (`Store.commit_fresh_resolved`, applied at each commit step from the S19 name invariant `Obligation.Declared` that `State.Valid` carries there). `run_success` gives every obligation of the tree declared in the final store, but the tree does not record each commit's store and an eigenvariable is declared in the final store, so per-node freshness must be carried along the run (for example by extending the frame invariant), not read off the final tree.
- E(KB) includes the generated signature clauses (`Elaboration.signatureKb`). The model witness must satisfy them, via `models_signatureKb` under `AdmissionSignature.Realizes`, including the exact `D_all` and `Pred_n` interpretations.
- Prove the composed proof-export/check theorem: successful admitted P2 execution yields a finite proof tree encoded as Term accepted by P1 for the permitted answer instance under the same snapshot/context and NAF provider. Compose the S08-S14 local checker correctness lemmas; impose no automatic P1 discovery requirement on the tree's formulas.
- Separate any genuinely new semantic certificate rules from reconstruction into unchanged Derives and prove their added obligations.
- A positive execution proof is not presented as a decision/completeness theorem; negative answers retain their precise adequacy hypotheses.
- Add model-backed end-to-end regressions for induction, guarded NAF, dictionary asymmetry, and local compound assumptions.
- Run lake build, affected existing tests, new regressions, and an axiom audit consistent with the project's current standard.
- Establish concrete model witnesses where new contracts require them; do not finish with an unjustified model-existence assumption hidden as implementation.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.

Profile composition acceptance (S01 revision): use one syntax and one Step/run. Prove P0-to-P1-to-P2 admission inclusion and preservation of embedded plans. P1 requires totality, soundness, and completeness for a named decision problem, with no completed Unknown result. P2 may exhaust a terminating proof strategy with Unknown. A decision request cannot silently fall back to P2. Generic induction/law search is P2 unless a complete decision contract is supplied; keep non-derivability distinct from semantic refutation and NAF evidence. See docs/lean-admission-contract.md.
