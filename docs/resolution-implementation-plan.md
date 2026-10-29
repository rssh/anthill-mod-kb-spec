# Lean resolution-machine formalization roadmap

The design is in [Decidable core and proof extensions](resolution-state-machine.md).
The dependency-linked tickets are tracked here under the `resolution-machine` tag.
This sequence implements the Lean specification and proofs. Rust-model/component
development belongs to its own separate scope.

The [S01 admission contract](lean-admission-contract.md) defines P0 (finite ground
acyclic resolution), P1 (certified decidable extensions), and P2 (proof strategies
that may return Unknown) as nested admission rules for one syntax and one state
machine. It specifies the proposed Lean
interfaces and theorem obligations and inventories reusable results and gaps.

## Scope

Reuse the existing `Term`, `Derives`, semantic model, substitution and scope
machinery, domain definitions, and certificates. Define and prove abstract-machine
transitions, admission judgments/checkers, and evidence reconstruction in Lean.

Place generic logic and model contracts in `AnthillModKbSpec/Foundation/`,
concrete model witnesses in `AnthillModKbSpec/Models/`, and shared operational,
matching, certificate, and admission code in `AnthillModKbSpec/Resolution/`.
Ground-profile modules live in `Resolution/P0/`; add `Resolution/P1/` and
`Resolution/P2/` when their specific implementations are introduced. Shared
machinery remains in `Resolution/`. Foundation modules must not import models
or resolution, and concrete models must not import resolution. Profile-specific
bridges using a concrete model belong in `Resolution/`, as with
`InductionCertificates.lean`. Preserve the shared logic and declaration namespaces.

Parsing, concrete frontend syntax, runtime term-representation design, Rust crate
bootstrapping, serialization, production APIs, and Anthill integration are outside
these tickets. Anthill documentation and proposals may inform the requirements;
they do not introduce external implementation dependencies. No work in
`/Users/rssh/work/oss/anthill-mod-kb-rust` is required by this sequence.

Executable definitions below mean Lean functions used to support the formalization
and examples, not a production runtime. Guarded elaboration operates on existing
represented formulas; it does not require implementing a parser or replacing Term.

## Milestones

1. **Foundation and baseline formal machine slice (S01–S07, S18, S19).** Specify P0/P1/P2
   admission contracts, formalize quantifier ranges and guarded elaboration, define
   state, delayed goals, and matching relations, prove ordinary resolution steps, and define an
   P0 admission checker and total evaluator, including nested ground NAF and
   exhaustive failure. State and prove the profile's guarantees.
2. **Decision and proof command rules (S08–S14).** Formalize the P1 checker for
   proof trees encoded as Term, proof imports, left rules,
   and compound heads, followed by NAF, induction, and dictionary-law contracts.
   Each motivating example should have concrete transitions and checked evidence.
   Distinguish P1 total sound/complete decisions from P2 incomplete proof strategies;
   termination alone does not establish a P1 decision contract.
3. **Composition and verification (S15–S17).** Compose static admission, prove
   reconstruction and semantic soundness, and complete Lean regressions and
   theorem/assumption documentation. Prove successful P2 runs export Term proof
   trees accepted by P1, without replaying discovery. No Rust performance or
   integration milestone.

## Work items

The S numbers are stable roadmap labels. Dependencies, rather than numeric order
alone, control execution; for example S13 need not wait for S12. Existing IDs and
dependencies are preserved after this scope correction.

| Ticket | Deliverable | Depends on |
| --- | --- | --- |
| [S01](../anthill-todo/delivered/WI-20261026-VJVCB-s01-define-the-first.anthill.md) | Specify the Lean admission and operational-semantics contract (delivered) | — |
| [S02](../anthill-todo/delivered/WI-20261026-3AAXX-s02-specify-data-ranges-and.anthill.md) | Data ranges and arity-indexed predicate-reference registries ([implemented](admission-signature.md), delivered) | S01 |
| [S03](../anthill-todo/delivered/WI-20261026-265RZ-s03-elaborate-scoped-data-and.anthill.md) | Guarded quantifier elaboration over existing Term, contexts, and rule templates; symbolic guards and generated signature clauses ([implemented](guarded-elaboration.md), delivered and revised) | S02 |
| [S04](../anthill-todo/delivered/WI-20261026-53V6D-s04-define-machine-states.anthill.md) | Machine states, AND/OR continuations with rollback, answer store with scope dependencies, proof trees and evidence classes ([implemented](machine-state.md), delivered) | S01 |
| [S05](../anthill-todo/delivered/WI-20261026-GGP59-s05-implement-capture-safe.anthill.md) | Scope-safe matching and instantiation: alpha-renaming instantiation, freshening with captured parameters kept, reading through answers, the matcher's outcomes, read-through contracts ([implemented](machine-matching.md), delivered) | S03, S04 |
| [S19](../anthill-todo/delivered/WI-20261028-X6W1K-s19-make-declared-free-names-a.anthill.md) | Declared free names as a machine invariant: commits check premise names, store freshness replaces obligation-name freshness, one freshness lemma for opened names ([implemented](machine-state.md#declared-names), delivered) | S05 |
| [S18](../anthill-todo/delivered/WI-20261027-YY6XN-s18-formalize-delayed-goals.anthill.md) | Delayed goals: wakeups and constraints in the store, exactly-once wakeup, woken continuations, deferred proofs filled at the end, floundering as gaps ([implemented](machine-delay.md), delivered) | S04, S19 |
| [S06](../anthill-todo/open/WI-20261026-9CQKX-s06-implement-ordinary-clause.anthill.md) | Formalize ordinary clause selection and positive execution | S05, S18, S19 |
| [S07](../anthill-todo/open/WI-20261026-NG07C-s07-build-the-initial-static.anthill.md) | Formalize P0 admission, total evaluation, and Ready plans | S06 |
| [S08](../anthill-todo/open/WI-20261026-ZPV53-s08-define-checked-proof.anthill.md) | Formalize P1 proof-tree checking as Term and proof imports | S03, S07 |
| [S09](../anthill-todo/open/WI-20261026-WHDHK-s09-implement-left-rule.anthill.md) | Formalize left-rule commands and compound clause-head proof construction | S06, S08 |
| [S10](../anthill-todo/open/WI-20261026-ANXY6-s10-implement-evidence-first.anthill.md) | Formalize evidence-first NAF and guarded-universal refutation | S09, S07 |
| [S11](../anthill-todo/open/WI-20261026-DABJW-s11-add-ho-apply-conversion.anthill.md) | Prove ho_apply conversion and whole-formula induction-head matching | S02, S09 |
| [S12](../anthill-todo/open/WI-20261026-P6JQV-s12-admit-explicit-induction.anthill.md) | Formalize admitted induction and prove the Nat example | S11, S08, S07 |
| [S13](../anthill-todo/open/WI-20261026-9C19E-s13-specify-checked-typeless.anthill.md) | Specify checked typeless dictionary registration and domain connections | S02, S08 |
| [S14](../anthill-todo/open/WI-20261026-5G8F5-s14-implement-dictionary-law.anthill.md) | Formalize dictionary-law selection and checked evaluation contracts | S13, S09 |
| [S15](../anthill-todo/open/WI-20261026-SYMNV-s15-compose-static-admission.anthill.md) | Compose static admission across proof imports, NAF, induction, and dictionaries | S10, S12, S14 |
| [S16](../anthill-todo/open/WI-20261026-0AA47-s16-prove-composed-machine.anthill.md) | Prove composed machine soundness through elaboration and the declarative calculus | S15 |
| [S17](../anthill-todo/open/WI-20261026-44E32-s17-validate-performance-and.anthill.md) | Complete Lean regression examples and document formal guarantees | S16 |

## P1 route ownership and delivery boundary

The admission contract's catalog describes possible P1 routes. This sequence
implements the following subset; the other catalog procedures remain deferred.
Generic interfaces for a decision contract do not implement a decision procedure.

| P1 route | Owner and required delivery |
| --- | --- |
| Embedded P0 | S07: whole-program acyclicity/rank checker, total shared-machine evaluation, nested ground NAF, and exact success/complete-failure certificates; S15: profile embedding |
| Explicit proof tree supplied as Term | S04: construction interfaces; S06-S07: baseline evidence; S08: encoding, recursive checker, known terminating rule checks, and correctness; S09-S14: nodes/checks for their commands; S15-S17: composed export/check theorem and regressions |
| Dictionary operation/equality decision | S13: registry contracts; S14: total concrete evaluator and full decision contract, including the Nat ordering example; S15: composition |
| Finite rule saturation | Deferred: no saturation implementation or least-relation decision theorem in S01-S17 |
| Stratified NAF over finite rules | Deferred: no stratified cyclic evaluator; S07 ground acyclic NAF and S10 scoped certificates do not supply this procedure |
| Finite guarded quantification | Deferred as a general complete decision procedure; S03 elaboration and S10 finite absence certificates remain in scope |
| Finite predicate-reference quantification | Deferred as a complete enumeration/decision procedure; S02 reference registration remains in scope. The symbolic `Pred_n` guard and its generated facts give no closure over the registry; such a decision would be snapshot-indexed closed-world evidence |
| Finite-answer variable queries | Deferred as a complete answer-set procedure; S05-S06 matching and individual successful answers remain in scope |
| Propositional logical reasoning | Deferred as complete derivability search; S08 proof checking and S09 logical commands remain in scope |
| Additional certified decision procedure | S08/S15 define contract and composition interfaces; concrete additional procedures require follow-up tickets before enablement |

A decision request that requires a deferred procedure returns NeedsEvidence.
An available P2 proof attempt does not satisfy that request. Successful P2 search
can instead produce a proof tree that the P1 explicit-proof route checks. Its
root and intermediate formulas need no automatic P1 discovery plan. S17 records
the final implemented/deferred route matrix and any remaining limitations.

S07 owns the full P0 baseline before S08 begins; S10 extends NAF beyond that
baseline. S08 defines checker interfaces for later commands, and S09-S14 provide
their corresponding nodes and checks. This preserves the existing dependency
graph without requiring S08 to depend on later search implementations.

## Working the sequence

Run from this repository:

```sh
anthill-todo -d "$PWD" list --tag resolution-machine
anthill-todo -d "$PWD" next
anthill-todo -d "$PWD" show WI-20261026-VJVCB
```

Each ticket specifies scope and acceptance criteria. The baseline check is
`lake build`, with focused Lean regressions and theorem checks as appropriate.
Documentation-only contract work is reviewed against its explicit deliverables.
No Cargo commands or external implementation work are acceptance prerequisites.

Key boundaries carried through the sequence:

- Admission decides executable capability, not the truth of the query.
- KB formulas and their range annotations are generated. Lowering rejects a
  predicate binder left at a data range; it never infers ranges.
- Guards are atoms over the signature's membership symbols. The registry and
  domain rules enter `E(KB)` as generated clauses (`signatureKb`), so lowered
  formulas depend only on the symbol naming.
- Snapshots index closed-world evidence (NAF, finite absence and enumeration)
  and plans. Derivations from clauses and generated facts stay valid as the
  registry grows.
- A predicate range supplies no case analysis over registered predicates. A
  bound reference is resolved by lookup on its symbol, including any future
  per-predicate resolution procedure.
- Whole-formula induction matching is explicit; an atomic matcher is insufficient.
- Predicate-reference matching is distinguished from general lambda unification.
- Dictionary laws remain guarded proved statements, separate from value evaluation.
- Failed candidates and incomplete searches never become unearned negative proofs.
- Delayed goals wake when a name they wait on is bound; still delayed at the end,
  they flounder as gaps, never as failure or NAF evidence.
- Proof validity and admissibility of an imported rule are separate checks.
- Explicit proofs are trees in the shared logic encoded as Term. P1 checks each
  rule application via a known terminating procedure; the tree's formulas need
  no automatic P1 admission.
- Successful P2 runs export trees accepted by the same P1 checker used for
  manual and external proofs; checking does not repeat discovery.
- Reuse foundation soundness through reconstruction; justify new certificate rules.
- Soundness, termination, completeness, and admission coverage are separate claims.
- Completed P1 decisions return Yes/No for their declared problem; P2 may return
  Unknown. A decision request must not silently fall back to an incomplete strategy.
