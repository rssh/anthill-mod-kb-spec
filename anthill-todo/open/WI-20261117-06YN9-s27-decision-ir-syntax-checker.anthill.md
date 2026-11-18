## Attributes

- id: WI-20261117-06YN9-s27-decision-ir-syntax-checker
- created: 2026-11-17T20:23:45Z

- status: Open
- status_agent: user
- status_at: 2026-11-17T20:23:45Z

- acceptance: lake build

- depends_on: WI-20261107-7PQMQ-s23-moded-structural-recursion, WI-20261107-R9YMZ-s24-tabled-backtracking-on-the, WI-20261107-JA6WZ-s22-answers-yes-no-unknown-and, WI-20261026-NG07C-s07-build-the-initial-static

- tags: resolution-machine

## Description

S27: Decision IR: syntax, checker, finiteness evidence, and semantics

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: the IR of docs/decision-ir.md (decided with the user, 2026-11-17): the Lean type of the programs decisions run on, its checker and evidence classes (P0 ⊂ P1 ⊂ P2), and its semantics, connected to the models the answers are about. The IR is a type for admitted programs; Term stays the representation of the KB, the queries, and the proofs.

Acceptance:
- Types: predicates with arities, declared modes, and kinds (defined, open by a marker case, guard, primitive); rules (definitions); derived rules (from checked lemmas, never in the completion); denials; literals (a call with inputs and outputs, NAF of an atom with every name bound, data equality and disequality, a guard, a primitive, a marker atom); queries (the context's conditions, the atoms to decide, the answer names).
- The checker, decidable: every literal's inputs bound, read left to right (S23's scan on the IR); every data name guarded; a guard binds its name only over a finite domain. Finiteness evidence for P1: data-term inputs on every call of the dependency closure (calls_bounded), finitely many derivable answers (outputs_bounded, calls_decrease), and no free output on a recursive call of a component that does not decrease. P2 without the evidence. S07's P0.Ground embeds as the ground acyclic case.
- Semantics: key interpretations and the consequence operator (S24's Tabled/Fixpoint) extended to guards (exact), primitives (by their evaluators), and markers (free); the completion's models over keys are its fixpoints.
- Herbrand reduction: for a program and a closed query whose data names are all guarded, truth in every model of the completion realizing the admission signature is truth in every key fixpoint.
- Relevance: the relevant program of a query (the ground rule instances its calls can use, for derived and for possible answers), finite under the P1 evidence; the completion's models restricted to it are the models of its completion, given a model of the rest of the KB.
- Rigid parameters: settle which queries with parameters are P1 (genericity over values outside the relevant data terms, or a split by domain closure) and prove it; the others are P2.
- Traces: path over a cycle, a ground query P1 and ∃Y. path(a, Y) P2; append(+, +, −) P1, decreasing; a self-supporting cycle with a free output P2; a lowered program with its guards P1; a P0 input as P0; the size of each relevant program.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs.
Design references: docs/decision-ir.md, docs/fast-admission.md, docs/tabled-evaluation.md, docs/answers.md.

## Changes

### 2026-11-18T05:47:01Z — feedback — user

From S24's review (2026-11-18), for the finiteness evidence: (1) compose S23's per-component bounds along the component order, since a body may construct a lower component's input: p(X) :- q(succ(X)). q(Y). is S23-P1 and S24 answers it Yes, but calls_bounded read per component would make it P2 (this composition was S15's in the 2026-11-08 S24 notes). (2) Bound term growth by the bodies, not the symbols: thirteen calls dup(X, Y) :- Y = pair(X, X) in a row reach 8191 nodes, past S24's (s+1)^(p+1) limit of 4096. (3) Contexts are sets: an assumption repeated along a recursion (p(succ(X)) :- (r → p(X))) makes no new call; S24's repeat-free contexts cut it. (4) S23-P1 queries that leave an output free on a recursive call of a component that does not decrease (path(a, Y) over a cycle) are P2 here; say so where the profiles move.

