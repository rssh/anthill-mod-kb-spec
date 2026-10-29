## Attributes

- id: WI-20261026-9CQKX-s06-implement-ordinary-clause
- created: 2026-10-26T08:32:23Z

- status: Open
- status_agent: user
- status_at: 2026-10-26T08:32:23Z

- acceptance: lake build

- depends_on: WI-20261026-GGP59-s05-implement-capture-safe, WI-20261027-YY6XN-s18-formalize-delayed-goals, WI-20261028-X6W1K-s19-make-declared-free-names-a

- tags: resolution-machine

## Description

S06: Formalize ordinary clause selection and positive execution

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: implement the first executable slice using the machine IR: truth, assumptions, conjunction/disjunction, scoped implication introduction, quantifier introduction where admitted, ordinary atomic clause selection, body execution, and FinishClause continuations. Supply an effective program representation rather than relying on semantic set membership.
Acceptance:
- Candidate selection freshens a clause and replaces the focused goal with its instantiated body; it never adds an unproved head.
- The effective program includes the generated signature clauses (`Elaboration.signatureKb`) alongside the lowered KB clauses. Range annotations come from the formula generator; a rejection by `elaborate?` or `elaborateClause?` is reported, never replaced by a default.
- Lowered clause bodies begin with range guards. Do not run a guard on a still-unbound variable as an enumerating generator ahead of the body: it delays (`Response.delay`, S18, docs/machine-delay.md) until a later goal, possibly the caller's, binds it, and still delayed at the end it flounders as a gap. For a typed head the generated fill or member goal is appended after the body (Anthill proposal 060); a domain's enumeration is an ordinary list of candidates, not a delay. Reconstruction reads `CompletedProof.tree`, which the success step has already completed with the deferred proofs (`CompletedProof.Valid.complete`); conjunct order does not change `Derives`.
- Local rule provenance and captured names are preserved; explicit binders are instantiated correctly.
- A successful trace reconstructs Derives for its answer instance.
- Use the S05 layer (docs/machine-matching.md): freshen with `Store.freshen`/`HornClause.templates` and local rules with `Term.instantiateLeading`; match with `Store.unify` against `Store.prepare`, which the commit replays (`Store.commit_unify`); report `unsupported`/`violated` as gaps and `mismatch` as a miss. For the commit, fresh names need only be new to the store (`Store.freshFor`, `Store.freshen`; S19). The matcher is syntactic, so also avoid the read binder names (`Store.readBinders`); otherwise an opening may rename a binder into an alpha-variant that `Store.unify` reports as unsupported. The commit refuses a premise naming an undeclared or out-of-scope name as a contract gap. It cannot detect a leftover template name that equals a declared name in scope, so freshen every template name. Reconstruct nodes with the `Expansion.*_soundUnder` contracts. Take the freshness of opened names from `Store.commit_fresh_resolved`: from the name invariant at the commit (`Obligation.Declared`, carried by `State.Valid`), it gives `Obligation.FreshUnder` for the read obligation and freshness for the read existential of `existsElim`. Openings rename inner binders, so binder names impose nothing. Take matched readings from `Store.Refines.resolve_eq`.
- Successful commands construct proof-tree nodes through the S04 interfaces, retaining clause instances, substitutions, and scoped assumptions for later Term export and checking in S08.
- Exhausting one candidate does not declare the goal false; loops are handled according to the S01 profile.
- Focused regressions cover candidate backtracking, local-rule lifetime, existential answers, and single completion of nested goals.
Keep arbitrary compound-head search and NAF out of this initial runtime slice. S07 owns the complete P0 evaluator, including nested ground NAF and exhaustive failure; S10 later adds evidence-first and scoped NAF routes.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.

