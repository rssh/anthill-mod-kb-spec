## Attributes

- id: WI-20261117-HYJ2C-s28-the-ir-evaluator-exact-p1
- created: 2026-11-17T20:24:05Z

- status: Open
- status_agent: user
- status_at: 2026-11-17T20:24:05Z

- acceptance: lake build

- depends_on: WI-20261117-06YN9-s27-decision-ir-syntax-checker, WI-20261026-ZPV53-s08-define-checked-proof, WI-20261107-R9YMZ-s24-tabled-backtracking-on-the

- tags: resolution-machine

## Description

S28: The IR evaluator: exact P1 decisions, P2 within fuel, certificates and their checks

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: the evaluator of docs/decision-ir.md, answering S22's results for IR queries. Decided with the user, 2026-11-17: Yes means truth in every model of the completion realizing the signature, with a checkable certificate, so that P1 decisions are exact; P2 is the same evaluator with fuel.

Acceptance:
- P1: build the relevant program; compute the definitely and the possibly true atoms (the Kripke–Kleene iteration, S24's kk); decide the atoms left undefined by enumerating the completion's models over them. A total function with no fuel and no gap, answering Yes, No, or Unknown, and Undecided only for the KB's inconsistency.
- Exactness, with S27's lemmas: Yes exactly when the query holds in every model of the completion realizing the signature, No exactly when it fails in each, Unknown exactly when both occur.
- P2: the same within the fuel over a relevant program that may be infinite; No by S24's refutation over the data terms and one abstract value, Unknown by S24's witnesses, Undecided naming the growing call; monotone in the fuel; with evidence supplied, the P1 answer.
- Certificates and checks: a Yes derivation over the relevant program, its NAF nodes refutations, exported as an S08 tree and checked; a Yes or a No by the relevant program, checked by recomputation; an Unknown by two fixpoint assignments (S24's groundFixpoint). A Yes with no closed-world step is marked a theorem of the KB; every other answer is indexed by the snapshot.
- Cost classes, reported before anything runs: polynomial of degree k when no NAF or denial reads a predicate whose dependency closure reaches a cycle or a marker (every model then lies between the least fixpoint with the markers false and the greatest with them true); exponential otherwise; budgeted for P2.
- Consistency: denials and NAF cycles checked at the KB level beside the queries; an inconsistent KB answers Undecided, naming it.
- Traces: S24's traces on the evaluator (path over a cycle and over a chain, left recursion, p :- ¬q with q :- ¬p Unknown, p :- ¬p Undecided, growing recursion Undecided by the fuel, naming the call); p :- q, p :- naf q, q :- q answering Yes with no derivation; a lowered path over a cycle answering Unknown where S24 gives Undecided; a non-ground program with NAF and an open predicate answering Unknown; a tampered certificate rejected.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs.
Design references: docs/decision-ir.md, docs/tabled-evaluation.md, docs/answers.md, docs/proof-checking.md.

## Changes

### 2026-11-18T10:49:07Z — feedback — user

From S27's review (2026-11-18), decided with the user: constraints outside a query's relevant program can rule out its models even on a consistent KB (an unreached rule r(a) :- p(a), naf r(a) forces p(a) false). S28 answers Unknown only when no rule outside the relevant program reads a relevant atom under NAF on a cycle; otherwise Undecided, naming that rule. Denials are S27's: they join the relevant program and its evidence graph. S27's splitting theorem (relevant_of_fixpoint, fixpoint_of_relevant) assumes the rest of the KB extends a relevant model; S28's exactness must discharge that, by the check above. Also: a split instance whose conditions no model satisfies is both Yes and No (vacuous); combine instances as S27's meaning_split states (Yes when every instance's truth holds, No when every instance's falsity holds, Unknown when one is not No and one is not Yes).

