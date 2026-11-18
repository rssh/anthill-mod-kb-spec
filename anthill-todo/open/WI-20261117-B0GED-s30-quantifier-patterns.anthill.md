## Attributes

- id: WI-20261117-B0GED-s30-quantifier-patterns
- created: 2026-11-17T20:24:25Z

- status: Open
- status_agent: user
- status_at: 2026-11-17T20:24:25Z

- acceptance: lake build

- depends_on: WI-20261117-A0H19-s29-admission-as-translation, WI-20261117-HYJ2C-s28-the-ir-evaluator-exact-p1

- tags: resolution-machine

## Description

S30: Quantifier patterns: universals by Lloyd–Topor, compound NAF operands

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: the first patterns beyond the core (docs/decision-ir.md), deciding guarded quantification over ranges that enumerate finitely: the deferred "finite guarded quantification" route of docs/resolution-implementation-plan.md.

Acceptance:
- A universal goal or body ∀x∈C. φ is naf aux, with aux(ȳ) :- C(x), naf φ' (Lloyd–Topor), ȳ its other names; correct in every model of the completion with complement NAF; it applies when C(x) enumerates x (S27's checker).
- NAF of a compound operand, or of one with local names, is naf aux with aux's rules.
- Patterns compose: ∀x∈C. ∃y∈D. R(x, y) as a goal; a universal inside a clause body.
- Traces: ∀x∈C. p(x) Yes, and No with its counterexample, over a finite C; ∀x:Bool. p(x) over the Bool domain; ∀x:Nat. p(x) a blocker naming a proof (S25's class, or induction); a nested universal and existential; a body universal.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs.
Design references: docs/decision-ir.md, docs/guarded-elaboration.md.

## Changes

### 2026-11-18T14:32:35Z — feedback — user

From S27 (2026-11-18): S07's P0.Ground embeds in the IR only where the IR keeps its meaning (IR/Ground: embedGround refuses an input with falsity, NAF of a compound goal, an unknown marker, or a predicate symbol at two arities; embedGround_p0, satisfies_ofBody). Compound NAF operands are S30's (the catalog's 'compound NAF operands'): naf G with G compound lowers to naf aux with aux :- G (a separate rule, not aux :- G, naf aux); falsity to a call of a predicate with no rule. With that lowering S07's inputs embed whole.

