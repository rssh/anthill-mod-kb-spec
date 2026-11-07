## Attributes

- id: WI-20261107-SFQPM-s25-regular-unary-predicates
- created: 2026-11-07T13:58:09Z

- status: Open
- status_agent: user
- status_at: 2026-11-07T13:58:09Z

- acceptance: lake build

- depends_on: WI-20261107-7PQMQ-s23-moded-structural-recursion, WI-20261107-JA6WZ-s22-answers-yes-no-unknown-and, WI-20261026-P6JQV-s12-admit-explicit-induction, WI-20261107-R9YMZ-s24-tabled-backtracking-on-the

- tags: resolution-machine

## Description

S25: Regular unary predicates: deciding guarded universals and existentials

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: regular unary predicates in docs/fast-decision-routes.md, a P1 route. A guarded universal over a declared domain, which S12 proves by P3 induction search, is decided when its predicates are regular.

Acceptance:
- Admission: unary predicates over declared domains defined by flat clauses p(c(x1, …, xn)) :- body, with distinct head variables and body atoms unary on the fields (other regular predicates, guards, NAF of regular predicates, stratified); nested patterns flattened by generated auxiliary predicates. Goals: ∀x:D. φ(x) and ∃x:D. φ(x), with φ a Boolean combination of regular predicates on x.
- Ground atoms decided by S24's tabled evaluation: they are in S23's complete class, since the fields are strict subterms. The state of a term is the set of regular predicates true of it.
- Evidence: Yes for ∀ is the finite set of states reachable from D's constructors, closed under its rules, all satisfying φ; No for ∀ is a counterexample term no deeper than the number of states, refuted by S24; ∃ dually. Both checked.
- Search: a bounded backtracking search over the finite state space on the shared machine, with a visited check and a bound fixed at admission. The visited check is justified by the domain's exact realization (members are the least set built by the rules), not by the completion of KB predicates.
- Theorems: Yes sound by induction on membership, as principle_valid is; No sound by the counterexample's membership and its S24 refutation; an open predicate gives Unknown with S22's witnesses.
- Cost is exponential in the number of predicates in the worst case; traces report state counts.
- S12's induction path stays the P3 route for predicates outside this class and for supplied proofs.
- Traces: ∀x:Nat. reachable(x) Yes; ∀x:Nat. even(x) No with the counterexample succ(zero); ∀x:Nat. even(x) ∨ odd(x) Yes; ∀x:List. allNat(x) Yes; ∃x:Bool. defined(x) Yes; an open predicate Unknown.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs.
Design references: docs/fast-decision-routes.md, docs/machine-induction.md, docs/admission-signature.md (exact realization).

