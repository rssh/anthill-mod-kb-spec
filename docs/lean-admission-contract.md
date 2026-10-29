# Lean admission and operational-semantics contract

S01 / WI-20261026-VJVCB. This document specifies P0, P1, and P2 and
the obligations for subsequent tickets. It defines a contract, not an already
implemented admission checker or a new soundness theorem. The broader design is
[resolution-state-machine.md](resolution-state-machine.md); the delivery sequence
is [resolution-implementation-plan.md](resolution-implementation-plan.md).

## Scope and decisions

Work in `anthill-mod-kb-spec`, using the existing `Term`, `HornClause`, `Derives`,
and semantic model. Describe quantifier ranges and machine metadata alongside
these structures; do not replace the term representation. No parser, concrete
surface syntax, serialized proofs, Rust work, or production API is required.

There are two distinct judgments to formalize:

```text
Admitted(snapshot, context, goal, plan)
CheckedProof(snapshot, context, goal, proof : Term)
```

The first justifies automatic execution under checked admission conditions. The
second checks a supplied proof tree in the same logic used by P0/P1/P2, encoded
as a `Term`. The tree may be constructed manually, produced by an external
system, or found by P2 search, including through nondeterministic choices. This
allows a proved formula to be used without repeating its discovery. A theorem
can enter automatic execution only after its use also passes operational admission.

**There is one syntax and one interpreter/state machine.** The deductive and
proof-oriented parts both use the existing formulas. P0, P1, and P2 are nested sets
of admission rules for that same machine; they are not languages, engines, or
different interpretations of truth. Every Ready result contains a plan for the
same command semantics. Profile information is evidence for admission, not an
instruction to switch interpreters.

- **P0: finite ground acyclic resolution.** A small baseline whose certificates
  reuse `GroundSearch`; this is not the intended deductive language boundary.
- **P1: certified decidable extensions.** Includes P0 and additional supported
  decision procedures with checked termination, soundness, and completeness,
  including checking an explicit proof supplied as a `Term`.
- **P2: scoped proof strategies, with Unknown permitted.** Includes P1 and
  sound proof attempts for broader formulas, including generic induction and
  dictionary-law reasoning without a complete decision procedure.

The common syntax also represents formulas requiring supplied proofs or further
extensions. Such formulas are not rewritten into another language. Admission
depends on the formula, program, context, and available strategy/evidence contracts.

## P0 inputs and admission

Assume decidable equality of variable, literal, and symbol identifiers. All input
lists and `Term` trees are finite. Identifiers need not form a finite universe.

Use exactly these existing syntactic classes:

| Component | P0 condition |
| --- | --- |
| Data | `GroundSearch.IsData`: literals and finite application trees |
| Atom | `GroundSearch.IsAtom ha`: ordinary symbol applied to ground data |
| Goal | `GroundSearch.IsGoal ha`: atom, truth, falsity, conjunction, nested NAF |
| Clause | `GroundSearch.IsClause ha`: ground atomic head and a list of P0 goals |
| Program | Finite clause list, interpreted by `GroundSearch.Program.toKb` |
| Context | Fixed finite list of ground atomic facts, `GroundSearch.Context` |

No runtime generator or primitive evaluator is invoked. Data applications are
opaque constructor syntax in this profile; ordinary atomic calls are resolved
only from the explicit program/context. There is no implicit dictionary lookup,
arithmetic evaluation, semantic equality test, or external clause provider.

P0 excludes variable-bearing templates, flexible query answers, quantified goals,
disjunction, scoped implication, compound heads, denial clauses, equality goals,
dictionary calls, and goal-position `ho_apply`. These remain well-formed foundation
formulas: they are outside the P0 admission rule, not outside the language. The
checker considers the enabled P1/P2 rules and the requested result guarantee
before returning `NeedsEvidence`. Profile exclusion
alone never produces `Invalid`.

### Acyclicity check

For every clause with head H, collect all atomic goal occurrences B in its body,
including atoms under any number of NAF constructors. Add an edge `H -> B`.
Do not collect applications inside an atom's data arguments as separate goals.
Include the atoms from the query and context in the finite vertex set.

Check the entire submitted program, not just one guessed successful branch. The
graph must be acyclic. A topological ranking supplies a natural number `rank(A)`
for every relevant atom, with `rank(B) < rank(H)` for every dependency edge.
Duplicate clauses are allowed; absence of a defining clause is allowed.

Both `p :- p` and `p :- naf-not p` fail P0 admission. This does not claim that
every rejected cyclic program is undecidable. A different certified strategy may
admit it later. This first profile is stricter than stratified Datalog and avoids
changing the existing meaning of finite failure to a fixed-point semantics.

### Finite names are not finite domains

P0 matches complete ground atoms by syntactic identity. It does not enumerate
inhabitants, even if data domains or predicate references have been registered.
There is no domain-coverage assumption and no implicit universal closure to
instantiate during P0 execution. Quantifier compilation in P1 or P2 must
justify its range, instance coverage, and resulting program dependencies.

## P1: certified decidable extensions

P1 collects supported decidable cases beyond P0. It is an extensible catalog of
procedures, not a claim to recognize every decidable mathematical problem.
Admitting all decidable problems by one complete static test is not our goal.

A P1 plan must have a **decision contract** for the exact problem it answers:

```text
DecisionContract(problem, inputConditions, plan):
    execution terminates for every input satisfying inputConditions
    Yes evidence establishes problem
    No evidence establishes not problem
    the two cases cover every admitted input
```

Ordinary completed P1 execution never returns Unknown. Admission checking is
decidable because it checks input restrictions and supplied finite certificates;
it does not synthesize arbitrary termination/completeness proofs. A missing
contract yields NeedsEvidence. Merely proving successful steps sound, bounding
search depth, or specifying a decreasing recursion measure is not enough.

### State the decision problem, including the meaning of No

A contract identifies whether it decides a closed-world relation/answer set in a
specified interpretation, or derivability in a specified restricted calculus.
Those problems must not be silently interchanged. For example:

- Complete finite program evaluation can decide truth under a stated completed
  interpretation, with negative evidence tied to that interpretation.
- Complete intuitionistic propositional proof search can decide derivability.
  Its No result is non-derivability, not a proof of logical negation and not an
  adequate NAF certificate by itself.

Both use the common syntax and foundation model. Positive evidence reconstructs
foundation proofs or goes through an explicit proved semantic extension. The
decision specification and negative evidence remain visible to the machine and
its callers. An incompatible negative result cannot be coerced into NAF.

### Initial catalog of P1 decision routes

These entries specify procedures to formalize, not existing implementations.
Each needs its full decision contract before it is enabled.
The [roadmap's route ownership table](resolution-implementation-plan.md#p1-route-ownership-and-delivery-boundary)
assigns the implemented subset to S01-S17 and explicitly defers the other
catalog procedures; listing a route here does not enable it.

| Route | Admission conditions | Decision/action |
| --- | --- | --- |
| Embedded P0 | Existing P0 assumptions and evidence | Unchanged ground success/complete-failure decision |
| Explicit proof | Goal and finite proof tree encoded as `proof : Term`, fixed snapshot/context, and a known terminating checking procedure for each rule used | Check each rule application and its premise subtrees; return the checked proof of the goal; rejection rejects this tree only |
| Finite rule saturation | Finite, effectively enumerable ground instance/atom set, with a proof of instance coverage and closure; positive recursion allowed | Saturate the finite set; decide membership in the specified least relation |
| Stratified NAF over finite rules | The finite saturation conditions plus checked stratification, closure/negative-evidence contracts for the fixed KB/context | Evaluate strata; no odd negative cycles or open-ended generators |
| Finite guarded quantification | Exact finite domain cover and compatible P1 decisions for every instance | Decide all instances for forall or witness existence for exists, with complete negative coverage |
| Finite predicate-reference quantification | Exact finite P_n cover, arity/application contracts, and compatible instance decisions | Enumerate references, not arbitrary mathematical predicates |
| Finite-answer variable queries | Complete finite ground-instance coverage, or a separately certified complete symbolic answer procedure | Compute the represented answer set; empty answers have the declared coverage meaning |
| Propositional logical reasoning | A finite propositional fragment of formulas/context and an explicitly chosen complete proof procedure, with matching calculus semantics | Decide derivability, including implication, disjunction, and logical negation; do not interpret No as semantic falsity |
| Dictionary operation/equality decision | Registered total evaluator or complete equality procedure, checked domain conditions, and evidence that results decide the declared equation | Decide the operation's value or equation; selecting some true laws alone is insufficient |
| Additional certified decision procedure | Effective input check plus terminating, sound, complete procedure and foundation interpretation theorem | Extend the catalog without changing syntax or the shared command semantics |

Finite rule saturation does not assume that a finite list of domain names has
finite inhabitants. If grounding would generate infinitely many constructor
terms, this route is not admitted. Symbolic or infinite-domain decision methods
need their own explicit contract; infinite domains are not categorically forbidden.

The least/completed interpretation of a saturation route must be related to the
shared model. Completion alone need not select a least solution for positive
cycles. Existing P0 finite-failure certificates cannot be reused to justify
failure of cyclic programs without the new procedure's coverage/adequacy proof.

The propositional route proves completeness for its declared calculus, not for
arbitrary surrounding KB clauses, NAF operations, equality theories, or hidden
quantified dependencies. Such dependencies must be excluded, supplied as checked
facts, or handled by another contract with a proved composition rule.

### Explicit proof: a proof tree in the shared logic

An explicit proof is a finite proof tree in the same logic used by P0/P1/P2,
passed as a `Term`. It is needed when a result is proved manually, obtained from
an external system, or found by P2 search whose successful choices we want to
retain. Once the tree is supplied, P1 checks its steps without repeating the
search that discovered them. The source of the tree does not change its meaning
or the rules it must satisfy.

Neither the root goal nor the intermediate formulas need to be admitted for
automatic P1 discovery. The checker verifies applications of the shared logical
rules; it does not run P1 goal admission on each node or require a P1 decision
procedure for each premise. P1 describes the decidability of checking the supplied
tree. The tree may prove any formula supported by the shared logic, provided all
its inference steps and side conditions are explicitly justified.

P1 must be able to check each rule application via a known procedure. For each
rule used by the tree, that procedure takes the stated premises, conclusion,
context, and explicit rule parameters, and decides whether this is a valid
application of the rule. Its correctness is established against the shared
logic. The checker recursively verifies the premise subtrees and invokes the
rule's checking procedure at the node. Thus checking a rule application does
not require deciding its premise or conclusion by automatic proof search.
A rule without a known checking procedure needs that capability before this
route can be admitted; merely naming the rule is insufficient.

Each node records an inference rule, its conclusion, the premise subtrees, and
the choices needed to check that rule: for example, a clause instance, witness,
substitution, or discharged assumption. Leaves are justified by the shared
logic's rules, such as an in-scope assumption or a KB fact. The root must establish
the requested goal in the original context. For example, a proof of `A and B`
has a conjunction-introduction root with subtrees proving A and B; a proof of
`A -> B` contains a subtree proving B under local assumption A, discharged at
the root.

```text
checkProof(snapshot, context, goal, proof : Term) : Accept | Reject
checkProof(...) = Accept iff CheckedProof(snapshot, context, goal, proof)
CheckedProof(...) -> Derives(snapshot, context, goal)
```

The reconstruction line is schematic: it preserves the application symbol,
KB, local assumptions, and exact NAF evidence provider of the foundation judgment.
The proof-tree encoding and executable checker remain to be formalized against
the shared inference rules represented by `Derives`. Any new inference rule
needs the same soundness justification as when used by P0/P1/P2; an external
system must supply a tree in this logic. No concrete encoding or new `Term`
constructor is fixed here.

Checking proceeds over the finite tree, verifying every premise and side
condition, including substitution, freshness, non-escape, guards, and NAF
evidence. References to previously checked proofs must resolve in the fixed
snapshot and preserve scope; cyclic references cannot justify themselves. A
NAF node must include the required complete-failure/coverage evidence: a failed
P2 search is insufficient. The tree contains all required branches, including
both cases for disjunction elimination, and no unresolved proof-search holes.

This route belongs to P1 because checking a supplied finite tree terminates and
decides whether it is a valid proof of the goal. Reject yields no negative
evidence about the goal. A checked tree can establish a formula beyond automatic
P1 discovery, including an induction theorem, and can then be reused. Its use as
an automatically selected fact or rule still needs operational admission.

### Composing P1 decisions

A plan remains P1 only when the composed decision problem and coverage theorem
are established. Decidable subgoals do not automatically make an inference rule
a decision procedure for its conclusion.

In particular, deciding an induction base and step does not decide an arbitrary
universal statement: failure of the step for the chosen invariant does not
refute the universal. Generic induction proof search therefore belongs to P2
unless a complete decision procedure for that restricted problem is supplied.
A supplied induction proof tree is checked by the P1 explicit-proof route and
can be imported as a fact and used by a P1 plan.

Likewise, failure of one dictionary-law premise does not refute the target
equation. A total complete evaluator may supply a P1 decision, while incomplete
law-based proof search is P2. A supplied theorem can settle a specific goal
positively without making every formula of that shape decidable.

## P2: scoped proof strategies with Unknown

P2 includes P1 and extends admission for the existing shared syntax, including all
its logical constructors. It does not admit every program using those constructors. A plan
can use ordinary deduction, checked lemmas, and registered strategies; unresolved
requirements are reported before evaluation, not discovered by a solver at runtime.

### What constitutes an admitted strategy

A strategy is a finite description of commands and control flow, potentially with
recursion justified by a checked well-founded measure. It is not a successful
proof tree: it may contain clause alternatives, symbolic matching, domain traversal,
and subgoals whose outcome is not known when admission succeeds.

For every reachable command schema, P2 requires:

1. A finite candidate source or admitted terminating generator, including the
   effect of local assumptions on candidate availability.
2. A terminating match/constraint operation, with declared modes, rigid dependencies,
   and representable substitutions. No hidden general higher-order oracle.
3. Admission of all generated obligations under the command's input contracts,
   including every dictionary implementation permitted by those contracts.
4. Termination of the entire strategy, including backtracking and repeated local
   rule selection. Acyclic control, checked structural decrease, or a supplied
   well-founded strategy contract can establish this. Cyclic predicate dependencies
   alone do not reject P2.
5. Successful-step reconstruction into the declarative calculus, or a separately
   proved semantic extension. Negative results require their own coverage and
   semantic evidence; positive-step soundness alone is insufficient.

The checker validates finite strategy descriptions and supplied evidence; it does
not discover arbitrary termination proofs. Built-in strategies may synthesize
simple rank/decrease certificates. Certificate validators and evaluators must
themselves terminate. A semantic truth assertion or arbitrary callback is not an
admission certificate. One checked strategy may serve all inputs satisfying its
modes without requiring a precomputed successful proof of each query.

### Admission and transitions by form

In this table, an admitted subgoal has a valid plan for every input/substitution
allowed by its command's contract; it is not necessarily already proved. Every
row also satisfies the strategy conditions above.

| Form/use | Static requirement | Same-machine action |
| --- | --- | --- |
| P0/P1 input | Existing decision-contract evidence | Execute the unchanged admitted plan |
| Assumption or supplied theorem | Checked formula/instance, context, and scope | Return its proof, without rediscovering it |
| Variable-bearing clause/query | Scope-safe matching, answer modes, finite candidate source, terminating body strategy | Freshen, match, instantiate body, save completion frame |
| Conjunction goal | Admitted children and compatible shared answers | AND obligations |
| Disjunction goal | Admitted alternatives and rollback | OR alternatives |
| Implication goal A -> B | B admitted under local A, including its effects on rule selection | Extend context, prove B, discharge A |
| Conjunctive assumption | Continuation admitted with both components | Project both |
| Disjunctive assumption | Both case contexts admitted with compatible answers | AND of two proofs of the original goal |
| Implication assumption A -> B | Admitted rule selection, premise, and resumed goal; repeated use terminates | Prove A, make B available, resume original goal |
| Existential assumption | Fresh rigid opening and non-escape invariant | Add body with branch-local witness |
| Universal assumption | Admitted instance selection/matching | Obtain an instance; preserve captured parameters |
| Guarded universal goal | Admitted generic rigid proof, certified finite cover, or checked induction strategy | Open/discharge scope, traverse cover, or apply principle |
| Existential goal | Admitted symbolic witness search, finite traversal, or supplied witness; guard/scope checked | Introduce flexible witness or instantiate candidate; prove body |
| Quantification over P_n | Reference registry, arity/application contract, and generic or finite-range strategy | Use predicate-valued witnesses/parameters with the symbolic `Pred_n` guard, discharged by its generated fact; not D_all guards |
| Concrete ho_apply | Reference/application contract and admitted direct call | Direct goal with saved proof conversion |
| Flexible predicate head | Admitted reference matching or supplied richer matcher contract | Bind clause predicate parameter and instantiate body |
| Rigid ho_apply | Admitted evidence/rule use for opaque application | Use evidence without assigning rigid predicate |
| Compound clause head | Admitted whole-formula matching, body, and consequent-use strategy | Prove body then use consequent's logical structure |
| Induction | Model-valid principle, registration guards, whole-head match, admitted base/step strategies | Generate base and scoped step, then close original guarded goal |
| Equality | Admitted reflexivity/matching, planned replacements, proved equations, or certified evaluator | Checked equality steps; no unrestricted rewriting loop |
| Dictionary operation/law | Registry/domain evidence, evaluator or proved law, admitted conditions and law-use strategy | Evaluate on demand or prove guarded law premises |
| Logical negation A -> false | Admitted implication/contradiction strategy | Assume A; search for contradiction under the plan |
| Falsity / denial | Admitted contradiction candidates/premises or existing falsity evidence | Derive falsity or use falsity elimination |
| Existing NAF evidence | Checked assumption/theorem and scope | Use it without new failure search or groundness requirement |
| NAF through failure | Exact KB/context, terminating operand procedure, exhaustive coverage, adequate negative evidence | Execute the certified negative procedure |
| Guarded universal negative | Certified positive-witness absence strategy or uniform scoped certificate | Seek exists x. D(x) and p(x), with justified complement-NAF conversion |

Existential witness search can succeed without covering the domain; concluding
absence needs a separate coverage argument. Generic rigid proof can establish
a universal over an infinite domain without enumeration; failure of that strategy
is not a counterexample. Raw falsity is not immediately failed in P2 merely because
P0 has such a transition: the P0 restrictions must still hold to use that shortcut.

Closed NAF can reuse existing certificate rules. New open/scoped NAF introduction
requires its own soundness proof before that route is admitted. The table does
not assert that such a rule already exists or identify NAF with logical negation.

### Outcomes and profile inclusion

P2 guarantees termination of its admitted plan and no missing-capability requests,
not completeness of arbitrary proof discovery. A plan can finish with a proof or
**strategy exhausted**: that strategy did not establish the goal. Exhaustion is
Unknown at the logical-result level unless further coverage/refutation evidence
establishes more; it is not non-derivability in `Derives`. External interruption
is a separate way to have an unresolved result.

P0 remains a special case with success/complete-failure certificates, and P1
preserves a binary answer for its declared decision problem. Require:

```text
P0Admitted(input, plan) -> P1Admitted(input, plan)
P1Admitted(input, plan) -> P2Admitted(input, plan)
run(input, embedded plan) = run(input, original plan)
```

There is one `run` and one `Step`; embedding preserves the actual plan and its
evidence. Another P2 strategy for the same input may have a different trace but
must remain sound under the same declared semantic contracts.

For example, P0 rejects a program containing `p :- p` even alongside a fact p.
P2 can admit a finite strategy selecting that fact to prove p; it does not thereby
claim exhaustive failure coverage for other goals. Recursion on a constructor
input may also be admitted with a checked decreasing measure.

One admission check considers the enabled P0/P1/P2 rules and available proofs. It
does not return NeedsEvidence just because P0 does not apply. Profile evidence
does not change formula syntax or select a different interpreter.

## Admission and result interfaces

These are proposed Lean interfaces; the names below reserve responsibilities for
later tickets rather than asserting that declarations already exist.

```text
Admission.check(snapshot, context, goal, requiredGuarantee,
                explicitProof : Option Term) : AdmissionResult

AdmissionResult =
    Ready(plan, guarantee, admission evidence)
  | NeedsEvidence(nonempty list of obligations)
  | Invalid(diagnostic)
```

The requested guarantee is either a Decision for a named problem or a ProofAttempt
which may return Unknown. A decision request must not silently fall back to P2:
report NeedsEvidence and identify the available proof-attempt route. All plans
use the same interpreter. The guarantee is an evidence contract, not another
syntax or execution engine.

For the explicit-proof route, the named Decision problem is validity of the
supplied tree in the shared logic for the goal. Acceptance returns the checked
proof of that goal. This must not silently substitute for a request to
decide provability of the goal. `explicitProof = none` leaves discovery to the
other routes; `some proof` makes that term available for checking.

`Ready` is not a proof of the query. `NeedsEvidence` identifies the exact formula
or dependency, the capability/strategy needed, and the available evidence route.
For P0, examples are `GroundInstanceRequired`, `AcyclicStrategyRequired`,
`ScopedProofRequired`, `InductionStrategyRequired`, and `DictionaryLawRequired`.
Use clause indices and term paths; no parser source locations are needed.

`Invalid` is reserved for violated declared input/evidence contracts, such as a
forged certificate, inconsistent registry declaration, or plan paired with the
wrong snapshot. A legal formula outside P0 is never invalid just for being outside
P0. Raw `Term` permits more expressions than any admitted profile.

The checker terminates by structural inspection, finite graph analysis, and
terminating verification of the supplied P1 decision/P2 strategy contracts; it
does not execute the KB or attempt to decide a semantic model's validity. Required
semantic facts are explicit proof parameters or checked certificates, not Boolean
queries to an assumed semantic oracle.

### Outcome distinctions

| Outcome | Meaning and evidence |
| --- | --- |
| Candidate miss | One selected clause cannot discharge the goal; try remaining candidates |
| Success | A `GroundSearch.Succeeds program context goal` certificate in P0 |
| Complete failure | A `GroundSearch.Fails program context goal` certificate in P0 |
| Decision Yes / No | P1 evidence for the named problem or its negation; No has the contract's specified meaning |
| Strategy exhausted | A P2 plan finished without establishing the goal; not automatically complete failure or refutation |
| Semantic refutation | Evidence that the formula is false under the declared model/context contracts |
| Unknown | An interrupted or incomplete broader proof attempt; no negative evidence |

A complete, unbounded P0 execution must return Success or Complete failure.
A completed P1 decision returns Yes or No for its declared problem, never Unknown.
An externally interrupted run may report Unknown without contradicting mathematical
termination. A general proof-layer search may remain incomplete. Its exhausted
strategy is not automatically complete failure, non-derivability in `Derives`,
or semantic refutation.

Complete failure excludes success of the P0 judgment via
`GroundSearch.fails_not_succeeds`. To interpret it as semantic falsity, require
`Model.GroundCompleted program context` and `Model.ComplementNAF`; then use
`Model.ground_certificates_sound`. These are properties of the same model,
program, and fixed context. Merely satisfying Horn implications is insufficient.

P0 success reconstructs `Derives` through `GroundSearch.succeeds_toDerives`, with
its exact ground failure provider. Its semantic soundness uses that provider's
adequacy, supplied by `Model.ground_failure_adequate` under the completed-model
contracts. Do not silently replace it with another NAF provider.

The package must eventually exhibit a completed model for admitted P0 inputs,
using acyclic truth evaluation and a suitable existing constructor-key model,
or state and check any additional necessary assumptions. A universal existence
theorem is not supplied by `CompletedGround` today. Existing concrete examples
already witness that the contract is non-vacuous. This is a separate obligation
from checking the acyclic dependency graph.

## Abstract state and command boundary

Use the current `Term` for goals and existing contexts/substitutions for their
logical content. `Machine.State` ([S04](machine-state.md)) records:

- a focused obligation tied to a program/context snapshot;
- finite pending goal lists and continuation frames;
- candidate alternatives with rollback points;
- in the general machine, rigid parameters, flexible-variable dependencies, and
  committed substitutions; these are empty/identity in P0;
- evidence for completed children and obligations for unfinished children.

`Plan` records admitted command choices and their dependencies, not a successful
proof path. It contains the finite candidate source and rank witness in P0. There
is no live mutable KB behind an admitted snapshot. Any change to program, context,
registry, or evidence dependencies requires a new admission result. Shared
substitution changes in later profiles must preserve their checked modes/scopes.

S04 supplies `Machine.State`, `Frame`, and `step`, and the scope-coherence part of
`Machine.WellScoped` as `State.Valid`, preserved by `step_valid` for any command.
`run_success` gives a coherent proof tree for the root obligation. Flexible names
carry dependency sets; `Store.Scoped` and `Store.commit_no_escape` keep an opened
rigid name out of the answers of names created outside its scope. S05 proves the
property of fully resolved answers (`Store.Scoped.resolve_answer`,
`Store.commit_no_escape_resolved`). It adds a matcher whose commit replays it and
read-through completion contracts (`Expansion.SoundUnder`)
([details](machine-matching.md)). S19 adds declared free names to `State.Valid`.
The opening contracts then take their freshness from one commit lemma
(`Store.commit_fresh_resolved`) ([details](machine-state.md#declared-names)).
S18 adds delayed goals: suspensions and a constraint slot in the store, woken
continuations beside frames, and deferred proofs. `State.Valid` covers every
branch (`Branch.Valid`), `Store.commit_wakes` wakes each suspension exactly
once, and `run_success` gives a completed proof with nothing pending whose
tree has no reference ([details](machine-delay.md)).

### P0 commands

| Focus | State action | Completion evidence |
| --- | --- | --- |
| truth | Return success to the saved continuation | `Succeeds.truth` |
| falsity | Return complete failure in P0 | `Fails.falsity` |
| A and B | Check both children; retain original goal/context | `Succeeds.conj`, or an applicable `Fails.conjLeft/conjRight` |
| naf-not A | Run the operand under the exact same snapshot/context | Operand failure gives `Succeeds.defaultNeg`; operand success gives `Fails.defaultNeg` |
| Atom A in context | Complete by assumption | `Succeeds.assumption` |
| Other atom A | Select each clause with exactly that ground head; focus its body conjunction | Successful body gives `Succeeds.clause` |
| All candidates for A fail | Check that A is absent from context and every matching clause was covered | `Fails.atom` |

`FinishClause` retains the original goal and selected clause membership proof.
It completes the original goal once, after the body succeeds. No selected head
becomes a fact before its body succeeds. Candidate rollback never deletes other
alternatives or turns a matcher/solver limitation into failure.

Immediate failure of falsity is valid here because P0 excludes contradiction
sources such as denial clauses and non-atomic contexts. The general proof machine
must instead search for proofs of falsity; it cannot reuse this transition without
the P0 restriction.

### Termination and cost obligations

Give an atom A level `rank(A) + 1`; goals without atoms have level zero. The level
of a compound goal is the maximum atom level in it. Recursive evaluation decreases
the lexicographic pair `(level(goal), structuralSize(goal))`: entering a clause
body reduces level; entering a conjunction or NAF operand reduces size without
increasing level. Traversing a finite candidate/body list also has its own finite
structural recursion. Prove the corresponding measure for explicit continuation
steps; do not assume every administrative step decreases the goal pair.

Finite acyclic search may still repeat work and be expensive. Memoization by
ground goal and exact snapshot/context is a later optimization. This contract
requires termination, not a polynomial-time or production-performance claim.

## Named formalization obligations

The following names are proposed future declarations, not checked signatures in
this ticket. `P`, `C`, `G` refer to the same program, context, and goal throughout.

| Proposed definition/theorem | Contract | Ticket |
| --- | --- | --- |
| `Admission.P0Input`, `P0Ranked` | Existing ground syntax plus finite rank evidence | S01 specification; S07 implementation |
| `Admission.check`, `check_ready_sound` | Computed Ready entails the actual admission judgment | S07 |
| `Admission.check_p0_complete` | Every structurally valid acyclic P0 input is Ready; not completeness for arbitrary formulas | S07 |
| `Machine.State`, `Frame`, `Step` | Explicit focus, context, continuation, and choice-point semantics | S04, S06 |
| `Machine.WellScoped`, `step_preserves_scope` | No captured-name mutation or witness escape | S04–S06, S09 |
| `Machine.ResidualProof`, `step_reconstruct` | Evidence for the next obligations plus saved frames yields evidence for the previous obligations | S06, S09–S14 |
| `Machine.step_preserves_admission` | Every reachable obligation has an admitted capability/strategy | S07, S15 |
| `Machine.progress` | An admitted nonterminal state has a next step, never a missing-capability state | S07, S15 |
| `Admission.P1Admitted`, `DecisionContract` | Check procedure input restrictions, totality, soundness, completeness, and negative-result meaning | S07–S15 |
| `Admission.P2Admitted`, `StrategyContract` | Check command modes, scopes, evidence reconstruction, and whole-plan termination; permit Unknown | S08–S15 |
| `Admission.p0_to_p1`, `p1_to_p2`, `Machine.embedding_preserves_run` | Nested admission and unchanged execution of embedded plans | S15 |
| `Machine.run`, `run_total_of_p0`, `run_total_of_p1`, `run_total_of_p2` | One interpreter with termination theorems under each admission contract | S06–S07, S15 |
| `Machine.run_decides_of_p1` | Sound and complete Yes/No decision for the specified problem; no completed Unknown result | S15–S16 |
| `Machine.run_correct_of_p0` | Returned certificate corresponds to the original P, C, G; use consistency to obtain completeness for these certificate judgments | S07 |
| `Machine.success_toDerives` | Instantiate/compose the existing ground or general reconstruction lemmas | S06, S16 |
| `Admission.ready_no_missing_capability` | Progress plus preservation for an entire run under its declared input contracts | S15 |
| `Elaboration.satisfies`, `elaboration_substitutes` | Preserve range semantics and capture-safe substitution over existing Term | S03 |
| `ProofImport.checked_sound`, `admit_import` | Separate logical validity from safe automatic use of a proved statement | S08 |
| `ProofTree.check`, `check_accepts_iff`, `checked_toDerives` | Term-encoded finite trees; known terminating rule checks; validity independent of automatic P1 discovery | S08; rule-specific nodes/checks S09-S14 |
| `Machine.exportProof`, `exportProof_checked` | Successful P2 execution exports a Term tree accepted by P1 for the same answer instance, snapshot/context, and NAF provider | S04 interfaces; S06-S14 construction/checking; S15-S16 composition; S17 regressions |
| `Machine.p0_model_exists`, `Machine.sound` | Supply the model witness and compose with existing soundness, distinguishing new certificate rules | S16 |

For general answer substitutions the reconstruction conclusion is derivability
of the permitted instantiated query under the correspondingly tracked context,
not derivability of an uninstantiated existential placeholder. Frame invariants
must specify this explicitly. P0 has no answer metavariables.

The general safety theorem is conditional on accepted extension contracts. A
contract must contain a terminating checker/strategy or checkable proof object;
an arbitrary callback or an assumption that a semantic proposition is decidable
cannot establish Ready. Proof checking and proof discovery are distinct tasks.

## Reuse inventory and known gaps

| Existing source | Reuse | Remaining gap |
| --- | --- | --- |
| `Syntax`, `LogicalKb`, `Derivation` | Common terms, clauses, contexts, introduction/elimination and equality rules | Admission/signature layer and machine transitions |
| `AdmissionSignature` (S02) | Data/predicate range contracts, finite arity declarations, snapshot-indexed reference evidence, ho_apply/dictionary compatibility laws | Machine scope enforcement and operational admission; no automatic induction validity |
| `Elaboration` (S03) | Recursive range guards, universal/existential semantics, free-name preservation, capture-safe substitution/opening, context and clause-template contracts, rejection of data ranges at `ho_apply` heads, symbolic guards that read only the signature naming, generated signature clauses (`signatureKb`) deriving every guard ([details](guarded-elaboration.md)) | Admitted quantifier strategies and machine reconstruction |
| `Machine` (S04) | State, AND frames, OR choice points with rollback, answer store with dependency sets and triangular bindings, commit checks, proof trees with rule parameters and scope coherence, evidence classes, outcomes, logical command contracts; `step_valid`, `run_success`, `Frame.feed_exact`, `Store.commit_no_escape`, `run_exhausted`, `Derives.mono` ([details](machine-state.md)) | P0 termination and failure certificates (S07), Term encoding and checker (S08) |
| `Machine` matching (S05) | Total `Store.resolve` with alpha-renaming, triangular bindings, store refinement and the scope of resolved answers, clause and local-rule freshening, the matcher with `unified`/`mismatch`/`unsupported`/`violated` outcomes, read-through contracts; `Store.unify_sound`, `Store.commit_unify`, `Store.unify_supported`, `Store.commit_no_escape_resolved`, `Store.commit_fresh_resolved`, `Expansion.clause_soundUnder` ([details](machine-matching.md)) | Matching up to alpha-equivalence, operation evaluation (S14), `ho_apply` conversion (S11); no completeness of the matcher |
| `Machine` declared names (S19) | Every free name of every committed obligation is declared in its store: the commit checks that every name a premise mentions is within its scope, store freshness replaces obligation-name freshness, and one lemma gives opened names their freshness for read obligations; `State.Valid`, `Store.commit_declared`, `Store.commit_fresh_resolved`, `run_success` ([details](machine-state.md#declared-names)) | — |
| `Machine` delayed goals (S18) | Delay responses, suspensions and constraint slots in the store, exactly-once wakeup at the binding commit, woken continuations under their own scopes, deferred proofs filled at the end, floundering as gaps; suspended and woken obligations declared; `Store.commit_wakes`, `step_valid`, `run_success`, `ProofTree.fillAll_complete`, `run_not_exhausted` ([details](machine-delay.md)) | Constraint solvers (S10 and later); rejection of references in supplied trees (S08) |
| `Machine` positive execution (S06) | Effective programs with generated signature clauses and reported lowering rejections, the `positive` command (introductions, identity, local rules by exact universal elimination, clause and denial-clause selection, falsity as an ordinary goal, delaying guards, gaps recorded beside the remaining candidates by `Response.incomplete`), sound commands and their reconstruction along a run; `Program.build_sound`, `positive_sound`, `run_reconstructs`, `positive_reconstructs_elaborated` ([details](machine-positive.md)) | Compound heads, curried rules, and left rules (S09), NAF and exhaustive failure (S07, S10), `ho_apply` conversion (S11); no termination or completeness |
| `Substitution`, `Opening` | Capture-avoiding substitution and rigid-name opening proofs; free names of instances, agreement, and cancellation (S05) | — |
| `ClauseInstantiation` | `instantiate?_sound` validates a partial computed instance; `Term.instantiate` (S05) renames binders on capture hazards, agrees with `instantiate?` when it succeeds, and composes | — |
| `Freshening` (S05) | Clause template names, fresh names, renaming with captured names kept, local-rule binder instantiation | — |
| `GroundSearch.Program`, `Context`, `Succeeds`, `Fails` | P0 finite presentation and evidence judgments | No terminating evaluator, rank checker, or totality theorem |
| `GroundSearch.succeeds_toDerives`, `succeeds_not_fails` | Reconstruction and certificate consistency | No general `Derives` completeness conclusion |
| `CompletedGround` | `ground_certificates_sound`, `ground_failure_adequate`, `ground_completed_sound` | Completion is a hypothesis, not generic model existence or search termination |
| `VariableSearch`, `ScopedSearch` | Instances, answers, freshness, `LocalInstance.toDerives`, `answers_toDerives` | Exhaustive-instance covers are evidence, not a general enumeration algorithm; raw scoped failure is inadequate |
| `CertifiedRefutation` | `Refutes.sound`, `failureAdequate`, `Refutes.toDerives` | NAF introduction still requires closed operands; semantic certificates are not automatically proofs in unchanged `Derives` |
| `InductiveDomains`, `UniversalIntroduction` | `Universal.toTerm`, `forallAll_satisfies_iff`, `Derives.forallAll_intro`; generalized by S03 | An admitted quantifier strategy |
| `MembershipClauses` | Constructor-membership clauses generated from domain definitions, valid under `Realizes` and deriving every generated member and its guard | Elaborated KBs must include them (through `Elaboration.signatureKb`); values outside generated data stay underivable |
| `CounterexampleSearch`, `CertifiedScopedSearch` | Finite covers/induction evidence and guarded semantic success | Domain certificates do not generally reconstruct KB-only `Derives` |
| `MillerCertificates`, `CoreMatcherCertificate`, `MillerResolution` | `UnaryMatch`, `Expansion.toDerives`, `certifiedClause`, `Proves.toDerives` | Unary symbol-valued atomic matching only; no whole-implication-head expansion certificate or complete scheduler |
| `InductionModel` | `inductionRule_valid`, `induction_rule_applies`, `model_exists` | Registry-guarded whole-formula principle and a statically admitted induction strategy |
| `OperationDictionaries`, `OrderDictionaries` | Callable-value equality, nested lookup contracts, Nat/Bool witnesses | Effective law registry, selection command, and operational admission |
| `EquationOracle` | `models_extension`, `derive`, `sound_with_equation_oracle` | Oracle acceptance is a semantic specification, not a total executable evaluator |
| `Semantics.Model.sound`, `InductiveSoundness.declarative_sound` | Final truth-preservation theorem | Reconstruction for new commands and separate proofs for genuinely new rules |

In particular, a model interpreting `ho_apply` is not itself a higher-order
unification algorithm. The current unary matcher and proof certificate do not
justify conversion under an arbitrary compound head without a new derived proof.
Likewise, a predicate's arity declaration is not a proof of an induction principle.

## Mathematical regression specification

These are the acceptance examples for later implementations, not assertions that
S01 has already added a checker. P0 outcomes refer to a fixed ground atomic context;
a P0 rejection alone does not determine the combined P0/P1/P2 admission result.

| ID | Input/case | Required result |
| --- | --- | --- |
| R01 | `p(a) :- q(a)` and `q(a)`; query `p(a)` | Ready; success with clause and assumption/fact evidence |
| R02 | `p :- q`, `p :- r`, and `r`; query `p` | First candidate fails; second succeeds; original p completes once |
| R03 | `p :- naf-not q`, no defining q; query p | Ready; success with exact-program q failure; semantic reading requires completion |
| R04 | `p :- p`, with a separate fact p | P0 rejects the cycle; P2 admits a finite fact-selection plan for p |
| R05 | `p :- naf-not p` | NeedsEvidence; never silently construct a two-valued completed model |
| R06 | `naf-not p` established in one context, then add p | Old evidence cannot be reused; new snapshot/context required |
| R07 | Query `p(X)` over an exactly covered finite predicate definition containing `p(c)` | P1 finite-answer route includes X:=c and covers all answers; a partial match-only strategy is P2 |
| R08 | `forall x:D. p(x)` with an exact finite cover and compatible P1 instance decisions | P1 decides the guarded formula; every member is covered |
| R09 | `forall P:P_1. ...`, instantiated with reachable | Predicate-membership evidence required; do not add D_all(reachable) |
| R10 | `forall x:D. naf-not p(x)` with `p(1)` and `1 in D` | Positive witness defeats the universal negative; rigid matching failure is irrelevant |
| R11 | `exists x. naf-not p(x)` used as an assumption | Open a local rigid witness; using its negative assumption needs no new NAF search |
| R12 | Goal C with assumptions A and `A -> (B or C)` | Use implication-left, then prove C in both cases; do not assert B and C together |
| R13 | Goal `D_nat(a)->reachable(a)` and the valid induction principle | Explicit proof/strategy path binds P:=reachable; prove base and separately quantified step |
| R14 | `less(d,b,a)=False_Boolean` from proved asymmetry and `less(d,a,b)=True_Boolean` | Preserve dictionary/domain guards; derive the focused equation only after conditions |
| R15 | Empty KB, failed search for `p -> q` | Not a semantic refutation; preserve `Tests/Resolution/ScopedNafBoundary.lean` counterexample |
| R16 | Scope tests `forall x exists y y=x` versus `exists y forall x y=x` | Later matching permits the first witness dependency and forbids the second's escape |
| R17 | P0-admitted input embedded through P1 into P2 | Same machine run and success/failure evidence; no interpreter switch |
| R18 | P2 induction strategy on infinite Nat with admitted base/step plans | Ready without finite-domain enumeration; the strategy's subgoal control must terminate |
| R19 | P2 finishes a finite proof attempt for a logical negation without contradiction | Strategy exhausted/Unknown, not NAF success |
| R20 | A plan can select an undeclared dictionary evaluator at runtime | NeedsEvidence in P1 and P2; a predicate name alone does not prove capability |
| R21 | Finite positive cyclic program with complete grounding and a certified saturation contract | P1 decision despite P0 cycle rejection; use the least-relation semantic contract |
| R22 | Decision requested for a goal with only an incomplete induction strategy | NeedsEvidence; do not silently return a P2 plan |
| R23 | Complete propositional procedure answers No for derivability | No NAF evidence is obtained without a separate semantic adequacy argument |
| R24 | Registered total dictionary comparison versus partial law search | Complete comparison is P1; partial law search is P2 |
| R25 | Goal G with a valid explicit proof supplied as a Term, even outside automatic P1 discovery | P1 proof checking accepts and reconstructs evidence for G under the original snapshot/context |
| R26 | Goal G with a rejected explicit proof Term | Reject this proof only; no evidence for logical negation, NAF, or non-derivability of G |
| R27 | Supplied proof context merely assumes G, or a proof reference escapes its scope | Cannot establish G under the original context; reject the invalid proof |
| R28 | The same proof tree is constructed manually, produced externally, or found by P2 search and passed as a Term | The P1 checker uses the same shared inference rules and accepts independently of how the tree was found |
| R29 | Valid supplied proof tree whose root and intermediate formulas lack P1 discovery plans | Accept by checking the shared inference rules; do not require automatic P1 admission of the tree's formulas |
| R30 | Proof-tree node with explicit premises, conclusion, and rule parameters | P1 checks the rule application via its known terminating procedure and recursively checks the premise subtrees |

Existing regression anchors: `Tests/Resolution/P0/GroundSearch.lean`, `Tests/Resolution/P0/CompletedGround.lean`,
`Tests/Resolution/ScopedNafBoundary.lean`, `Tests/Foundation/UniversalIntroduction.lean`,
`Tests/Resolution/LeanCoreMatcher.lean`, `Tests/Models/InductionModel.lean`,
`Tests/Foundation/OperationDictionaries.lean`, and `Tests/Foundation/EquationRules.lean`.

## Delivery boundary

S01 specifies P0, P1, and P2. S02–S07 implement shared definitions and the full P0
baseline, including ranked total evaluation and nested ground NAF; S08–S14
implement P1 proof-tree checking, dictionary decision contracts, and P2
evidence/command contracts. Other P1 catalog procedures are explicitly deferred
in the roadmap's route ownership table. S15–S17 compose admission, prove profile
inclusions and P2 proof-export/P1 checking, and establish the shared machine's
guarantees. The deductive and proof-oriented layers retain the same syntax and foundation
model. Intermediate proof commands need not be automatically admitted before
their strategies satisfy these contracts.
