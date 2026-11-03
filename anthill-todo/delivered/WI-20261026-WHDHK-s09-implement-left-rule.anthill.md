## Attributes

- id: WI-20261026-WHDHK-s09-implement-left-rule
- created: 2026-10-26T08:32:28Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-01T11:34:04Z

- acceptance: lake build

- depends_on: WI-20261026-9CQKX-s06-implement-ordinary-clause, WI-20261026-ZPV53-s08-define-checked-proof

- tags: resolution-machine

## Description

S09: Formalize left-rule commands and compound clause-head proof construction

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: implement explicit assumption selection and continuations for general formulas in the proof layer, exposing core admission only for justified cases. Cover conjunction/disjunction, existential/universal assumptions, implication-left, compound heads, falsity, and logical negation.
Acceptance:
- Implication selection proves A then makes B available while resuming C; adding A->B alone does not automatically evaluate A. Reconstruct the continuation in the original context using existing Derives rules: derive B by impElim, discharge B from the continuation by impIntro, then apply impElim to obtain C. Any alternative proof-substitution construction must prove its required context/NAF compatibility; do not assume unrestricted weakening or transport of context-sensitive NAF evidence.
- Disjunctive assumptions use two AND contexts and reconstruct disjElim. Both cases must prove the same continuation goal with compatible shared answer substitutions; branch-local assumptions must not leak into sibling branches or the resumed outer context.
- Existential assumptions introduce fresh local rigid witnesses, fresh for the original context, existential formula, and conclusion. Discharge their scope and reject witness escape through answers or constraints.
- Universal assumptions support explicit capture-safe instantiation, including repeated uses of the same assumption with different witnesses. Preserve captured free parameters; only explicit binders are instantiated.
- Conjunctive heads may split into conditional clauses. After a disjunctive head's body is established, use the resulting disjunction by case analysis: both cases must prove the continuation via disjElim; never select one disjunct as an established fact.
- A head P->Q remains a local rule after the condition succeeds; logical-not heads compile to conditional falsity.
- Each command reconstructs existing Derives rules and has success/failure traces and scope tests. Include incompatible answers across disjunction branches, branch-assumption leakage, existential witness escape, capture-safe universal instantiation, and repeated universal use with different witnesses. Failed command attempts do not establish negation or non-derivability.
- Each successful command constructs a proof tree encoded as Term through S08, with a known terminating checker for its rule application. Prove S09 command constructions pass checking given checked premise trees under the command's specified contexts and side conditions, including both disjunction-elimination branches and discharged local assumptions. Reuse S08 logical nodes where sufficient; any derived-rule extension must provide its terminating RuleCheck and reconstruction proof. Automatic P1 discovery of these formulas is not required.
- Export boundary: S08 establishes checked export for P0 runs. S09 owns checking the constructions for its commands under the checked-premise assumptions above; the theorem that arbitrary successful S06/P2 runs export checked proofs, including final-store substitution across the whole run, remains S15/S16 work.
- Static diagnostics distinguish proof-layer capabilities from admitted automatic execution; no assertion that general search terminates.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.

