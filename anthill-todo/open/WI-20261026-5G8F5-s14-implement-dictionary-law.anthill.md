## Attributes

- id: WI-20261026-5G8F5-s14-implement-dictionary-law
- created: 2026-10-26T08:32:35Z

- status: Open
- status_agent: user
- status_at: 2026-10-26T08:32:35Z

- acceptance: lake build

- depends_on: WI-20261026-9C19E-s13-specify-checked-typeless, WI-20261026-WHDHK-s09-implement-left-rule

- tags: resolution-machine

## Description

S14: Formalize dictionary-law selection and checked evaluation contracts

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: implement select_dictionary_law and FinishDictionaryLaw, plus a separate operation-evaluation action returning checked equations. Index by dictionary/interface, path/name, arity, and conclusion shape; verify full matching and guards after retrieval.
Acceptance:
- For goal less(myOrd,b,a)=False_Boolean, the proved asymmetry law generates OrdDictionary(myOrd), both DomainMember obligations, and less(myOrd,a,b)=True_Boolean.
- All conditions must succeed before closing the goal; rollback restores rejected candidates.
- A bare operation term is evaluated on value demand, not by firing all laws.
- Equality reconstruction uses existing equation/implication rules or the explicit equation-oracle contract; preserve exact-KB NAF dependencies.
- Emit Term proof trees for law application and checked evaluation equations, with known terminating rule/certificate checks through S08. Prove exported trees pass checking; merely trusting an evaluator callback or an oracle assertion is insufficient.
- Own the initial P1 dictionary operation/equality route: provide a registered total concrete evaluator (using the Nat ordering example), its declared decision problem, and termination/soundness/completeness proofs. Keep partial dictionary-law search in P2 and missing evaluator contracts as NeedsEvidence.
- Complete tests with a concrete Nat ordering example, unmet domain guards, nested dictionary paths, and missing evaluator evidence.
- Structural dictionary matching is not mislabeled general higher-order unification; symmetric laws do not silently become unrestricted rewriting.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.
