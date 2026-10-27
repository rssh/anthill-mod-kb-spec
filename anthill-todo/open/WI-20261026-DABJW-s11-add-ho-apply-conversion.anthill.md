## Attributes

- id: WI-20261026-DABJW-s11-add-ho-apply-conversion
- created: 2026-10-26T08:32:31Z

- status: Open
- status_agent: user
- status_at: 2026-10-26T08:32:31Z

- acceptance: lake build

- depends_on: WI-20261026-3AAXX-s02-specify-data-ranges-and, WI-20261026-WHDHK-s09-implement-left-rule

- tags: resolution-machine

## Description

S11: Prove ho_apply conversion and whole-formula induction-head matching

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: implement ho_goal and ho_elim proof commands and checked selection of heads containing ho_apply. Include the user's intended whole-formula match: D_nat(a)->reachable(a) against D_nat(x)->ho_apply(P,x), not only an atomic reachable(a) matcher.
Acceptance:
- Match x:=a and P:=the registered unary reachable reference, without assigning rigids or enumerating arbitrary predicates.
- Discharge P's `Pred_1` guard from its generated fact (`Elaboration.rangeGuard_derives_predicate`), a lookup by symbol. A predicate range supplies no case analysis over the registry. Any per-predicate resolution procedure is selected by lookup on the matched reference symbol; a flexible P is bound only by matching or by resolving its guard against the generated facts.
- Preserve predicate-range guards and independently bound induction-step variables.
- Prove the conversion under implication using foundation rules; extend certificates beyond the current UnaryMatch/Expansion coverage without assuming their existing theorem handles compound heads.
- Direct and indirect calls share a canonical candidate view without rewrite loops.
- Emit Term proof-tree nodes for conversion and explicitly supplied whole-formula instantiations. Provide known terminating rule checks through S08 and prove export/check correctness without repeating matcher search.
- Selecting the principle exposes base and universally quantified step obligations and finishes the original formula exactly once.
- Unsupported lambda-valued answers are statically classified; distinguish structural reference matching from general higher-order unification.
Tests cover direct/indirect assumptions, compound heads, arity mismatch, and wrong-domain rejection.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.
