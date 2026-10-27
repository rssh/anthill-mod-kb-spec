# Implementation experiments: finding and checking derivations

The objective of the project is [logic soundness](../overview_anthill.tex).
The theorem about `Derives` does not require an automatic search algorithm.
This note describes separate experiments for discovering derivations and
checking that proposed resolution steps belong to the logic.

[Decidable core and proof extensions](resolution-state-machine.md) is the proposed
next design: a terminating core decision procedure, a broader proof language, and
checked admission of proved statements. Its transition catalogue also records
proof-search actions that are not yet classified as core operations.

The [implementation roadmap](resolution-implementation-plan.md) tracks the ordered
work as dependency-linked `anthill-todo` tickets under the `resolution-machine` tag.
The [S01 contract](lean-admission-contract.md) defines P0, decidable extensions P1,
and proof strategies P2 (which may return Unknown), using one syntax and state
machine. It specifies result meanings and the Lean definitions and proofs to implement.

The [S02 admission signature](admission-signature.md) implements typeless data and predicate
reference ranges over the existing carrier, with checked arity declarations,
snapshot-indexed evidence, concrete-reference application laws, and model-backed
examples. [S03 guarded elaboration](guarded-elaboration.md) lowers recursively
annotated quantifiers, contexts, and rule templates into the existing calculus,
with exact range semantics and capture-safe substitution proofs. Its guards are
atoms over the signature's membership symbols, derived from generated signature
clauses, so lowered formulas do not depend on the predicate registry. Machine scope
enforcement remains later work.

## Resolution steps and their justification

`MillerResolution.Proves` records formula-resolution proof trees. Forall opens
a fresh rigid parameter, implication extends local assumptions for its body,
and conjunction requires its components. For an atomic goal, a candidate clause
can be selected, matched, instantiated, and justified by proofs of its body.
This is recursive resolution with alternatives, not a linear execution pipeline.
A complete clause-selection and backtracking scheduler is not implemented.

`Proves.toDerives` translates an accepted resolution proof into the declarative
calculus. Applying logic soundness gives the resolution soundness corollary
`InductiveSoundness.sound`; `consistent` is its corresponding consistency result.
Those are consequences of the logic theorem, not prerequisites for it. A running
resolver need not construct a model or execute the soundness proof for each query.

Induction remains an ordinary KB clause. In the native-backed example, opening
`forall x : Nat. reachable(x)` produces rigid `a` and a local `isNat(a)` assumption.
Backward matching of the induction head computes `P := reachable`, `x := a`.
The instantiated base and scoped-step obligations are ordinary formulas; their
proofs use certified NAF and a local IH, respectively.

## Optional native matcher and pure certificate checker

`LeanCoreMatcher` calls the installed `Lean.Meta.Sym.isDefEqS` implementation on
actual Lean application and abstraction over an opaque carrier. It is called
when a supported clause-head match is requested. It protects caller metavariables,
restores candidate state, and decodes representable substitution data. This does
not add a typed sort dependency to the model.

`CoreMatcherCertificate` independently validates that proposal against the
original head, atomic query, and rigid scope. `ClauseInstantiation` computes a
capture-safe instance of the whole clause body. `MillerCertificates` specifies
the checked head/expansion contracts and proves their translation to `Derives`.
`Proves.certifiedClause` uses those contracts to justify a resolution step.
No correctness axiom about the native matcher is needed for logic soundness.

The current bridge accepts unary symbol-valued matches. General lambda-valued
answers are not reflected into `Term`; the partial instantiator rejects cases
requiring alpha-renaming. Unsupported or undecided output never supplies NAF
evidence. Candidate-state rollback is not a complete search backtracking engine.

[Tests/Resolution/LeanCoreMatcher.lean](../Tests/Resolution/LeanCoreMatcher.lean) executes the native
solver, emits only proposal data as a safe definition, reconstructs its
kernel-checked expansion proof, and proves the forall. It also checks forged
proposals, undeclared rigids, caller-state isolation, and a binary permutation
solved by the native engine. The end-to-end proof's axioms are audited against
the standard logical axioms.

## Historical experiments

Superseded designs are opt-in under
[AnthillModKbSpec/Archive](../AnthillModKbSpec/Archive/README.md), with tests in
`Tests/Archive`. They are excluded from the main import graph and checked by a
separate CI job.
