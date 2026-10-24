# Historical development notes

Preserved from before the source consolidation. Some module paths and theorem
names below describe earlier versions. Use the [current README](../../README.md)
and [archive index](../../AnthillModKbSpec/Archive/README.md) for current locations.

# Detailed model notes

For the main theorem and current entry points, see the [README](../../README.md)
and [overview](../../overview_anthill.tex).


## Formula-only backward induction (current route)

The primary logic is now `MillerResolution.Proves`, with ordinary `Term` goals
and ordinary KB clauses. `MillerMatching.matchUnary?` computes the supported
rigid-spine match of `ho_apply(P,x)` to `f(a)`. P and x must be distinct clause
variables fresh for the rigid scope; a must be rigid. Its successful result
satisfies the existing Miller restrictions and fixes every rigid parameter.

`Term.instantiate?` computes a capture-safe instance using that substitution.
It shadows binders and refuses cases needing alpha-renaming. `expandUnary?`
combines the head match and scoped body instance. None means unmatched or
unsupported, not logical failure. This prototype is limited to concrete unary
symbol predicates and does not implement general Miller unification or lambda
abstraction.

`Proves.millerClause` selects the actual ordinary KB clause and requires the
computed expansion. `Proves.toDerives` translates every step into the original
calculus, so the resolution rule introduces no new logical axiom. The main
`InductiveSoundness.sound` and `consistent` now concern this formula-only logic.
`Tests/MillerResolution.lean` checks the full forall/rigid/matching/induction path,
with NAF in its base case and a local IH in its scoped step. It also checks the
D_all form, unsupported matches, preserved rigids, shadowing, and capture refusal.
There is no separate InductiveProof goal or scheme registry on this route.

## Lean-core proposer and checked certificates

`LeanCoreMatcher.lean` is the optional metaprogramming backend. It imports
`Lean.Meta.Sym.Pattern`; the logical calculus does not. Actual Lean application
and lambda abstraction over an opaque carrier encode the supported pattern,
without adding typed sorts to the model. `solveAbstracted?` runs native Miller
unification, protects outer metavariables with a new context depth, restores
search state, and rejects unresolved answers. `proposeUnary?` reflects only
answers eta-reducible to a known symbol and the original rigid argument.

`CoreMatcherCertificate.UnaryCandidate` is raw data. Its pure checker validates
the proposed predicate, argument, head shape, scope, and capture-safe body
instantiation independently of the native solver. `Proves.certifiedClause`
accepts the resulting existing `Expansion` certificate and translates to
`Derives`. The main soundness theorem is unchanged; it assumes no correctness
axiom for the proposer or encoding. The handwritten matcher remains available.

`Tests/LeanCoreMatcher.lean` executes the core solver, emits its proposal as a
kernel-checked data definition, reconstructs the expansion proof, and proves the
Nat forall using NAF in the base case and a scoped IH in the step. The proof's
axioms are audited against the standard logical axioms. Tests reject forged
proposals and undeclared rigids, check caller-metavariable isolation, and exercise
a binary argument-permutation solution in the native engine. That lambda answer
is intentionally outside the current model decoder. Errors and unsupported
answers remain undecided, not certified failure.

Candidate-state isolation is not an implementation of full search backtracking.
A resolver must also save alternative clauses, continuations, substitutions,
and delayed constraints at branch choice points. The inspected Elpi implementation
uses an explicit trail to undo assignments and suspended-constraint changes;
our prototype restores Lean metavariable state within each candidate attempt.

## Separate induction goals (comparison experiment)

The comparison logic is `InductiveResolution.Proves`; its theorem is
`InductiveSoundness.explicit_induction_sound`. A program has ordinary clauses and an optional
`InductionGoals.Scheme`, whose finite constructor list must be exactly Sigma.
`Program.inductionGoals` computes the list of scoped constructor obligations.
It returns `none` without a declaration, and a list of goals rather than a
success result when induction is enabled.

Goals are either `.formula term` or `.inductiveProof predicates`. The predicate
family uses ordinary untyped terms; the certificate goal is a control construct,
not a new arbitrary atomic predicate. For each constructor, the generated goal
universally quantifies its fields, assumes their domain memberships and the
matching predicate IHs, and asks for the predicate at the constructor result.
The field binders avoid all free predicate parameters. Eigenvariable opening
separately checks freshness against the actual local context.

`Proves.induction` recursively proves every constructor obligation, using the
same logic as the surrounding goal. `Proves.inductionApply` combines the resulting
certificate with membership of a subject, which may be a rigid parameter.
It does not instantiate or destruct that parameter. The soundness proof uses
least-generated membership induction to justify this new inference rule.

Constructor cases may use clause search, local hypotheses, nested induction,
and closed certified NAF. Legacy declarative proofs, certified scoped successes,
and exhaustive counterexample certificates also embed in this judgment. The
new logic does not accept arbitrary raw failure as negation and does not relax
the closed-operand gate. `Proves.established` allows an induction-based formula
proof to support a later certified implication refutation in the same context.

`Tests/InductiveResolution.lean` contains the complete rigid-parameter proof of
all-Nat reachability. The zero constructor case uses a clause requiring NAF of
falsity; the successor case uses its local IH through the recursive clause.
The example has no legacy generic induction clause. It also checks the D_all
version, absence of a declaration, incomplete constructor coverage, freshness,
false evenness certificates, and consistency of the extended logic.

The previous headline KB-only theorems are now named `declarative_sound` and
`declarative_consistent`. The comparison results `explicit_induction_sound` and
`explicit_induction_consistent` cover that separate-goal judgment. The notes below describe the individual sublogics, which remain
available. No automatic proof-discovery scheduler, higher-order unification
algorithm, or production-resolver correctness theorem is claimed.


# anthill-mod-kb-spec

A minimal Lean logical mirror of the Anthill KB for researching language
extensions. Data, goals, and scoped logical terms share `Term Variable Literal
Symbol`. Predicate values and object variables share a binding namespace.
`Formula` and `Atom` are aliases of `Term`; neither introduces another carrier.
The `Atom` alias does not enforce atomicity.

```lean
import AnthillModKbSpec
open AnthillModKbSpec

example : HornClause String Nat String :=
  .definite (.app "Nat.induction" [.var "P"])
    [.hoApply "ho_apply" (.var "P") [.app "zero" []],
     .forallImpl ["n"]
       [.hoApply "ho_apply" (.var "P") [.var "n"]]
       [.hoApply "ho_apply" (.var "P") [.app "succ" [.var "n"]]]]
```

The core constructors include variables, literals, symbol applications, truth,
falsity, conjunction, disjunction, implication, negation as failure, and
universal/existential binders.
A symbol value is a nullary application such as `.app "zero" []`. Constructor,
function, and predicate names use the same `Symbol` parameter. Raw syntax does
not enforce types, arities, callability, or a goal/formula grammar.

`Term.hoApply hoApplySymbol predicate args` builds an ordinary application whose
first argument is the predicate value. The derivability relation below specifies
its logical behavior; there is no application lowering or evaluation function.

Scopes and implication are explicit term structure. `.forallVar "x" body` binds
all occurrences of `x` in `body`, including predicate positions. The nearest
binder shadows outer ones. `.imp premise conclusion` represents implication;
in goal position its premise supplies local assumptions for its conclusion.
Scopes and implications can nest and appear inside ordinary application arguments.
There is no separate predicate quantifier.

`.defaultNeg body` represents negation as failure (`not body`). It is distinct
from `.imp body .falsity`, and explicit negation is not included. Free-variable
collection, capture-avoiding substitution, and the optional Miller check traverse
the body. The `defaultNegIntro` rule below introduces it from groundness and
separate evidence of complete failure. Absence of a proof alone is insufficient.

`Term.forallImpl binders antecedents consequents` is only a syntax-building helper
for the KB discharge shape `forall_impl(tuple(binders), tuple(antecedents),
tuple(consequents))`. It constructs:

```text
∀ binders. (conjunction antecedents → conjunction consequents)
```

The binders scope both assumptions and consequents. Empty conjunctions are truth.
In Anthill, discharge opens these binders with fresh rigid witnesses and restores
the assumption context after proving the consequent. The relation below models
the logical scopes and fresh witnesses, without implementing resolver execution.

`HornClause` retains a head/body interface, with scoped goals and nested
implications allowed in the body. `HornClause.toFormula` translates connectives
without inserting implicit universal closure. The general term syntax can also
express the induction axiom:

```text
∀P. (ho_apply(P, zero) ∧
     ∀n. (ho_apply(P, n) → ho_apply(P, succ(n)))) →
    ∀n. ho_apply(P, n)
```

`LogicalKb Variable Literal Symbol` is a set of Horn clauses, represented by a
membership predicate `HornClause Variable Literal Symbol → Prop`. Use `clause ∈ kb`,
`∅`, `{clause}`, and `insert clause kb` (or `{clause₁, clause₂}`) to describe it.
Order and duplicates do not matter; finiteness is not required. `LogicalKb.ext`
identifies knowledge bases with the same members. Clause identity is raw syntax,
without quotienting by alpha-equivalence or logical equivalence. This collection
type is independent of the derivability relation.

`AnthillModKbSpec/Derivation.lean` defines declarative derivability:

```text
Derives hoApplySymbol kb context goal naf   -- KB ; Γ ⊢ G, relative to naf
```

The final `naf` argument defaults to `NafFailure.disabled`, preserving the
positive-only calculus and the shorter `Derives hoApplySymbol kb context goal`.
It is an inductive natural-deduction relation. Its constructors cover assumptions,
truth, conjunction, disjunction, implication, universal/existential quantification,
clause application, falsity, and explicit predicate application. To prove an
implication, prove its conclusion with the premise added to the local context.
The premise is available only in that subproof. Logical elimination rules allow
conjunctive, quantified, or implicational assumptions to be used.

Negation as failure uses a separate evidence relation, `NafFailure`, indexed by
the application symbol, KB, context, and operand. Its intended meaning is that
the operand's search completed with no solution and no unresolved branches:

```text
freeVars(G) = []       naf hoApplySymbol KB Γ G
────────────────────────────────────────────── defaultNegIntro
              KB ; Γ ⊢ not G
```

Every premise of a derivation uses the same `naf` relation. The rule conservatively
blocks operands containing free parameters, including eigenvariables and unknown
predicate variables. Residual, floundered, open-world, or depth-limited searches
must not provide failure evidence. The exact context matters: failure observed
before adding an assumption does not automatically remain valid afterwards.
There is no default-negation elimination rule equating `not G` with `G → ⊥`.

`NafFailure` is an interface, not an executable or automatically verified oracle.
Its name does not certify an arbitrary supplied predicate as correct. The ground
search fragment below supplies a concrete relation for finite ground programs;
`Tests/Derivation.lean` also retains narrow fixtures that exercise the interface.
Negating `Derives` directly would not express complete search and would make its
inductive definition non-positive. Ordinary Horn-model entailment also does not
by itself justify negation as failure.

Each clause use chooses one simultaneous substitution for its free variables,
shared by that use's head and body. Different uses choose independently.
Substitutions never modify the current goal or local assumptions. Universal
introduction opens the body with an eigenvariable fresh for both the context and
the quantified goal's free variables. It stays rigid because no inference rule
substitutes into an existing sequent. Existential elimination additionally checks
that its witness parameter does not escape into the conclusion. Free KB variables
are implicitly universally quantified; context variables are fixed parameters.

`AnthillModKbSpec/Substitution.lean` defines free-variable collection and the
capture-avoiding `Substitutes` relation. Under a binder it can choose a new binder
name, provided that name captures no substituted free variable. The binder then
shadows the corresponding substitution entry. This is relational substitution,
not a substitution or fresh-name search algorithm. The generic name type needs
decidable equality; existence of enough fresh names is a separate assumption
when proving completeness properties.

The `hoApplyIntro` and `hoApplyElim` rules connect `ho_apply(p, args…)` with
`p(args…)` when the predicate value is a nullary symbol. They also permit explicit
applications from local hypotheses to be used. No application rule resolves an
unbound predicate variable, literal, or compound predicate value. An unresolved
application can still be assumed and used unchanged as a local hypothesis.

A goal clause derives falsity when its instantiated body is provable. Falsity
has its ordinary logical elimination rule; it does not mean unsuccessful search.
In particular, a KB containing the empty goal clause is contradictory.

This is a logical proof specification, not an implementation-equivalence result.
There is no explicit negation, open/closed policy, implemented search strategy,
unification algorithm, or discrimination tree.
Well-formedness restrictions on
the raw syntax and a signature for reserved symbols remain to be specified.
The semantic model and soundness theorem are described below. Correspondence
with the Anthill resolver remains future work. Explicit negation is still a
later extension; adequacy of the concrete NAF providers remains to be established
against a chosen closed-world semantics.

`AnthillModKbSpec/Semantics.lean` gives a compositional interpretation of the
shared term carrier. A `Model` supplies a nonempty value domain, literal and
application operations, logical operations, and a truth predicate. Formulas
stored as data also denote values. Quantifiers range over the value domain;
their truth laws are ordinary universal and existential quantification.
Concrete-symbol `ho_apply` agrees in truth with ordinary predicate application.
NAF has a separate operation with a coherence law: a value and its default
negation cannot both hold. The general model does not require default negation
to be the truth complement or identify it with an explicit-negation constructor.

`Model.eval_congr` proves that evaluation depends only on free names.
`Model.eval_substitutes` proves capture-avoiding substitution agrees with
composition of environments, including alpha-renaming and formulas in argument
positions. These are proved from evaluation, not assumed as model laws.
`Model.Models kb` means every clause's formula holds under every environment,
including all implicit universal instances and any goal-clause constraints.
`Model.ContextHolds` checks the current local assumptions under one environment.

`Model.sound` proves: if a model validates the KB and its failure provider is
adequate, every `Derives` proof preserves truth from the local assumptions.
It covers every constructor, including nested implication, both quantifiers,
clause instantiation, falsity elimination, and `ho_apply`. `Model.positive_sound`
requires only KB validity because the default provider supplies no evidence.
`Model.consistent` and `Model.positive_consistent` rule out a derivation of
falsity from the empty context under the corresponding hypotheses. They do not
assert consistency for arbitrary KBs. `Model.not_both` additionally rules out
deriving a goal and its default negation together when the local context holds
in the model.

`Model.FailureAdequate` is an explicit remaining obligation: for each supplied
ground failure certificate under the exact KB and local context, default
negation must hold in the model whenever those assumptions hold. `SearchSoundness.lean`
transfers success and answer certificates to semantic truth using the existing
bridges, conditional on the matching provider's adequacy. `CompletedGround.lean`
now discharges this condition for ground search in completed models, as described
below. The variable and scoped providers do not yet have an adequacy theorem.
Finite failure cannot establish falsity in every Horn-clause model: the empty KB
permits `p` to be true, although empty-program search fails on `p`. A regression
test proves this counterexample.

`AnthillModKbSpec/BooleanModel.lean` constructs `Model.trueAtoms`, a concrete
Boolean model in which all applications hold. It validates every atomic-headed
definite clause, so it can witness positive consistency without prescribing
constructor semantics. The induction example proves that its KB has this
model and therefore cannot derive falsity in the positive calculus. This is a
consistency witness, not a proof of induction in the intended standard Nat
model. `Tests/Soundness.lean` also checks semantic substitution, nontrivial
quantification, adequate evidence for `not False`, and exclusion of a model for
an explicitly contradictory KB.

`AnthillModKbSpec/CompletedGround.lean` supplies a closed-world semantics for
finite ground search. `Model.GroundCompleted program context` requires every
ordinary ground atom to hold exactly when it is a local fact or has a defining
clause with a true body. `Model.ComplementNAF` makes default negation true exactly
when its operand is false. Mutual induction on the success/failure certificates
proves `ground_certificates_sound`: success implies semantic truth and complete
failure implies semantic falsity. Completion also validates every original KB
clause. Consequently `ground_failure_adequate` proves the existing
`FailureAdequate` condition for `GroundSearch.failureEvidence`; it no longer has
to be assumed separately. `ground_completed_sound` applies the general
soundness theorem using these proved obligations.

Completion is a condition on the model, not a total decision procedure or a
claim that every program has such a model. Positive recursion such as `p :- p`
can have completed models while finite search supplies neither certificate.
The odd cycle `p :- not p` has no completed model with truth-complement NAF.
The proof never turns a missing success certificate, recursion, or a depth
limit into complete-failure evidence. This is two-valued completion semantics;
a semantics retaining undefined atoms for all programs is a separate task.

`AnthillModKbSpec/HerbrandModel.lean` builds concrete compositional models from
an interpretation of ground-atom constructor keys. Values pair a constructor
key with a proposition, allowing formula values in the shared carrier as well.
Concrete-symbol `ho_apply` is resolved by a terminating operation that removes
one argument per resolution. This is a model construction, not a resolver for
unknown predicates, and it does not choose a canonical least or stable model.
`Tests/CompletedGround.lean` supplies a completed model of `p :- not q`, proves
its actual failure provider adequate, derives `p` using NAF, and establishes
consistency with that provider. It also checks positive recursion and proves
that the odd negative cycle has no complement-completed model.

There is a distinct obstruction for the current scoped provider.
`Tests/ScopedNafBoundary.lean` proves that no `Model` can validate all of its
failure evidence even for the empty KB. Search fails both on `p` and on
`p -> q` (because `q` fails under the temporary assumption `p`). Adequacy of
the first failure makes `p` false by NAF coherence; the model's implication law
then makes `p -> q` true. Adequacy of the second failure contradicts that truth.
Thus hypothetical proof failure cannot generally be treated as semantic
falsity. The existing scoped behavior remains unchanged. The domain-guarded layer below
supplies a separate sound counterexample rule for its restricted universals;
unrestricted hypothetical-failure NAF still requires a restriction or a
different semantics and corresponding soundness condition.

`AnthillModKbSpec/InductiveDomains.lean` supplies the new domain-guarded
universal layer. `Definitions Domain Symbol` represents the set Sigma of
constructor rules. Each rule names its result domain, constructor symbol, and
finite list of argument domains. `Member` is the least inductively generated
membership relation on canonical constructor trees. Rules may be mutually
recursive; domains may overlap. This is distinct from merely asserting Horn
constructor-closure clauses, which would permit additional unsupported members.

`Universal` records a finite domain list, binder, and property body. Its
`toTerm` keeps the existing raw syntax and produces:

```text
forall x. (is_D1(x) or ... or is_DN(x) or False) -> P(x)
```

`FiniteFamily` packages Sigma with a finite, exhaustive catalog of domain
identifiers, independently of any typed layer. Its `Generated` universe consists
of constructor trees belonging to at least one declared domain. `forallAll`
builds the formula above using every domain in the catalog; finiteness of the
catalog does not require finite domains. `holds_iff` and
`forallAll_satisfies_iff` prove that this is universal quantification over the
generated universe. Abstract sorts can still use a smaller union through
`Universal`.

Raw `Term.forallVar` continues to quantify over the entire semantic carrier,
which may contain extra values. `FiniteFamily.Covers` explicitly requires every
carrier value to be denoted by a generated tree. Under this additional condition,
`forallAll_iff_forall` proves equivalence to raw universal quantification.
Without it, the all-domain quantifier intentionally ranges only over data.

`AnthillModKbSpec/UniversalIntroduction.lean` connects KB clauses and derived
implications to these universal goals. `Derives.forallAll_intro` is the derived
introduction rule: from `Gamma, D_all(x) |- F(x)`, conclude
`Gamma |- forall x. D_all(x) -> F(x)`, provided x is absent from the free
variables of every assumption remaining in Gamma. `Derives.generalize` supplies
the corresponding unrestricted rule, derived from the existing eigenvariable
rule. Neither adds an axiom to the calculus.

`Derives.forallAll_of_single_clause` turns a stored `p(x) :- g(x)` clause into
the exact goal `forall x. D_all(x) -> (g(x) -> p(x))`.
`forallAll_of_clause` handles conjunctions of arbitrary clause bodies. Other
free variables remain parameters and can be generalized in turn. These logical
steps need neither enumeration nor carrier coverage. The semantic corollaries
`Model.forallAll_of_single_clause` and `Model.forallAll_of_derives` prove truth
in a model of the KB; the latter additionally requires adequate NAF evidence
when the derivation uses NAF. `forallAll_of_established` accepts an established
formula directly, with the same freshness requirement. Tests cover a stored
successor clause, a derived implication using two recursive clause applications,
and rejection of generalization from a fixed local assumption about x.

`AnthillModKbSpec/CounterexampleSearch.lean` adds forall introduction from
certified exhaustive failure of a generated counterexample search:

```text
counterexample := exists x. D_all(x) and not P(x)
```

`Universal.counterexample` builds this syntax. With exact domain realization
and complement NAF, `satisfies_iff_no_counterexample` and
`satisfies_iff_counterexample_naf` prove the equivalences between the guarded
universal, semantic absence of a counterexample, and NAF of the counterexample
query. These equivalences do not identify raw search failure with semantic
absence. This existential query is a semantic representation, not a new
executable exists handler in `ScopedSearch`.

`CounterexampleSearch.Rejected` certifies that an individual inner NAF query
fails because its positive operand is established at that generated value.
`Rejected.ofEstablished` accepts a proof of the actual constructor instance via
capture-avoiding substitution; `Tree.eval_toTerm` connects its syntax to the
denotation. `Fails` requires such rejection for every actual domain member.
`Fails.ofCovers` builds it from exhaustive finite covers and checked instances;
`Fails.ofInduction` supplies an alternative for infinite inductive domains.
Unknown, floundered, interrupted, or merely sampled results provide no certificate.

`Fails.sound` proves the guarded universal, and `Fails.toSucceeds` feeds the
certificate into the existing certified scoped success judgment.
`counterexample_fails` excludes a semantic counterexample; `counterexample_naf`
also proves NAF of the counterexample query under complement NAF. This is a
certificate interface, not an automatic counterexample finder or a translation
of arbitrary raw `ScopedSearch.Fails` proofs. The positive forall conclusion
does not automatically become a KB-only `Derives` proof, since finite coverage
and inductive-domain evidence remain external to that calculus.

`Tests/CounterexampleSearch.lean` checks finite coverage with positive KB proofs,
an infinite Nat induction certificate, empty unions, the certified-success
bridge, rejection of incomplete coverage, and real counterexamples preventing
false forall certificates. The finite witness model identifies constructor
denotations, while the Nat example uses the distinct constructor model above.

`Holds` quantifies over the union of the generated domains. `Induction` supplies
a family of constructor cases; `Member.induct` and `holds_by_induction` support
proofs over infinite domains and mutually recursive definitions. Alternatively,
`holds_by_covers` uses finite `Cover` values with sound membership and exhaustive
coverage. A sample without coverage is not a universal proof. Empty unions and
empty constituent domains are vacuously true; repeating or overlapping domains
requires no disjointness proof.

`Refutes` requires a selected constituent domain, a constructor-generated
member, and semantic falsity of its property. `refutes_not_holds` proves that
such a certificate contradicts universality. No generic implication-failure
rule is used. `Realizes` connects each `is_D` predicate to exactly the
denotations of its generated trees in the existing compositional model.
`Universal.satisfies_iff` then proves that `toTerm` has precisely the intended
union-domain meaning. Semantic denotations may identify constructor trees;
the canonical trees themselves remain distinct.

`Universal.naf_of_refutation` introduces semantic NAF in a model with complement
NAF. The new `InductiveDomains.failureEvidence` adapter requires certified
counterexamples under every environment satisfying the actual local context,
and is indexed by the exact KB and application symbol. `failureAdequate`
proves the existing adequacy condition for this adapter. It is a certified
interface, not an implemented counterexample finder: connecting body refutations
to executable search remains separate. It does not replace the existing
`ScopedSearch` provider or remove the scoped counterexample described above.

`Tests/InductiveDomains.lean` defines Nat and Boolean constructor domains plus
an empty domain. It checks an induction proof for their union, exhaustive finite
coverage, rejection of an incomplete sample, duplicate domains, empty-domain
behavior, and counterexample refutation. A concrete compositional model realizes
the domains and exercises the syntax equivalence, adequate NAF adapter, a
`Derives` proof of NAF for a guarded universal, and consistency with that adapter.
The test model identifies constructor denotations and is a consistency witness,
not the standard free Nat interpretation.
The tests also give an explicit existential model witness for the finite family
and example KB: membership is realized, the KB is valid, complement NAF holds,
the all-domain goal succeeds, every certified success is true, and falsity
cannot succeed. This establishes existence for this example; general soundness
still assumes a model satisfying the chosen KB. The same witness has a carrier
value outside every generated domain, demonstrating why coverage cannot be
omitted from the unrestricted-forall equivalence.

`AnthillModKbSpec/CertifiedRefutation.lean` unifies the sound negative-evidence
routes into `CertifiedRefutation.Refutes model kb context goal`. Ground leaves
use actual finite-failure certificates in a completed model of the exact KB.
Guarded-universal leaves use the generated-domain counterexamples above.
Falsity is directly refutable; conjunction needs one refuted side, disjunction
needs both, and default negation is refuted by established truth of its operand.

Implication uses a different rule from operational hypothetical failure:

```text
Established(model, Gamma, A)    Refutes(model, KB, Gamma, B)
----------------------------------------------------------
              Refutes(model, KB, Gamma, A -> B)
```

Both premises use the original Gamma. `Established` is checked semantic truth
under all environments satisfying Gamma; `ofPositive` obtains it from a positive
`Derives` proof, and `ofDerives` permits a NAF proof when its provider is already
proved adequate. It cannot be supplied simply by assuming A in a new context.
Established antecedents may themselves be implications. Consequent refutations
compose recursively, including guarded quantifiers and nested implications.

`Refutes.sound` proves semantic falsity of every certificate. `failureEvidence`
accepts these certificates, rather than arbitrary `ScopedSearch.Fails` results;
`failureAdequate` discharges the general adequacy condition. `Refutes.toDerives`
introduces NAF for a closed certified operand, retaining the existing free-name
gate. `sound` and `consistent` connect this provider to the full declarative
calculus. This is the certified route; the legacy scoped failure adapter remains
available for the boundary regression and is still not generally adequate.
No automatic refutation search is claimed. The scoped-atom bridge below
handles explicit instance covers with certified body refutations; it does not
make arbitrary operational body failures sound.

`Tests/CertifiedRefutation.lean` checks a positive atom established through
adequate ground NAF, refutation of `p -> q`, recursive and higher-level
implications, compound negative goals, provider adequacy, and consistency.
It rejects the empty-KB implication refutation and checks that a temporary
assumption cannot be reused as root establishment. The inductive-domain tests
also exercise guarded universals through the unified provider.

`AnthillModKbSpec/ScopedAtomSemantics.lean` supplies per-atom completion in an
exact scoped context. `Model.ScopedAtomCompleted program context atom` states
that, under environments satisfying the local assumptions, the atom holds iff
it is a local atomic assumption or has a true instantiated body. The support
relation is `ScopedSearch.Instance`, so it includes global schematic clauses
and local definite clauses, not only global rules. This is a condition on the
chosen model and exact scope, not a proof that one completed model works in all
hypothetical extensions.

`Model.scoped_atom_refuted` proves semantic falsity from absence as a local fact,
an `ExhaustedInstances` cover, and semantic refutations of every covered body.
The positive direction, `scoped_atom_supported`, establishes an atom from an
applicable instance with an established body. These theorems do not assume the
legacy scoped failure provider is adequate.

`CertifiedRefutation.Refutes.scopedAtom` integrates the negative direction into
the certified NAF provider. It retains the existing closed-atom and closed-local-
context gates, checks the exact KB, and recursively requires a certified
refutation of each body in the cover. `Refutes.ofScopedAtomFailure` adapts the
atomic case of an existing operational failure only when clients independently
certify all applicable bodies. Its old recursive `Fails` premises alone are
insufficient: an atomic failure can hide an unsound hypothetical failure in a
clause body. `Established.ofScopedInstance` supplies positive support without
passing through legacy scoped NAF.

`Tests/ScopedAtoms.lean` checks a schematic global rule with shared head/body
variables, a local implication rule, exhaustive local alternatives, actual
atom-failure adaptation, NAF derivations, and a supported local fact that blocks
refutation. It checks closed queries in an active rigid scope and retains the
free-parameter restriction. A hypothetical clause whose body is semantically
true cannot be certified false, and therefore cannot be used to refute its
supported atomic head.

`AnthillModKbSpec/CertifiedScopedSearch.lean` provides the coherent certified
scoped execution path. `CertifiedScopedSearch.Succeeds model program context
goal` retains positive clause selection, local assumptions, conjunction,
hypothetical implication, and universal introduction with a fresh rigid
parameter. Every recursive clause body uses certified success. Its NAF rule
requires a closed operand and a `CertifiedRefutation.Refutes` certificate;
operational `ScopedSearch.Fails` is never accepted directly. Its dedicated
`guarded` constructor also accepts positive generated-domain proofs, obtained
through induction or certified exhaustive covers.

`Succeeds.sound` proves semantic truth for the whole judgment assuming the
model validates the logical KB and interprets NAF as complement. Adequacy of the
legacy provider is not an assumption. Negative leaves retain their own
completion/domain conditions inside their certificates. Positive instance
soundness is justified by a positive `Derives` implication from body to head,
including local definite clauses, so positive clause application needs no
completion assumption. `Succeeds.established` lets a certified success supply
an antecedent to `Refutes.imp`; `Succeeds.refutes_imp` performs that composition
in the original context. `Succeeds.not_refuted` proves disjointness when the
context holds in the model; `no_falsity` excludes certified success of falsity
at the empty context under the soundness hypotheses.

`CertifiedScopedSearch.Answers` mirrors scoped answer validation using certified
success: it checks binding safety, capture-avoiding instantiation, preservation
of rigid parameters, and runtime validity in the original context.
`Answers.sound` establishes truth of each reported instance. These judgments
are proof-certificate interfaces, not an implemented search strategy, and no
termination or completeness result is claimed. The guarded-domain success rule
uses Sigma's model interpretation directly; no general translation of those
domain proofs into the existing KB-only `Derives` calculus is asserted.

`Tests/CertifiedScopedSearch.lean` checks the empty-KB distinction: atomic NAF
can succeed under completion while `not (p -> q)` cannot. It checks certified
NAF in a global clause body, higher-level implication refutation using a newly
established antecedent, nested local scopes, context restoration, local rule
backchaining, fresh-parameter universal introduction, schematic clauses, and
query answers. The inductive-domain examples also check positive guarded
success and certified NAF of a refuted guarded universal through the new path.
The old `ScopedSearch` judgments remain as operational specifications and for
the unsound-adapter regression. New semantic scoped results should use
`CertifiedScopedSearch`, not the legacy NAF adapter.

`AnthillModKbSpec/GroundSearch.lean` starts the complete-failure semantics with
finite ground programs. It uses the existing `Term` and `HornClause` types,
restricting them through `IsData`, `IsAtom`, `IsGoal`, and `IsClause` predicates.
`Program` stores a finite clause list with a well-formedness proof; `Program.toKb`
forgets the presentation and gives its logical set of clauses. `Context` contains
only ground atomic facts. There is no discrimination tree or unification step:
ground heads match by equality.

Supported goals are ordinary ground atoms, truth, falsity, conjunction, and
negation as failure. Atom arguments are literal/constructor trees. The designated
`ho_apply` symbol is reserved and excluded as a goal head in this fragment.
Variables, quantifiers, scoped implications, disjunctions, higher-order application,
and goal clauses are not yet part of this search fragment; they remain available
in the broader syntax and derivability relation.

`GroundSearch.Succeeds program context goal` and `GroundSearch.Fails program
context goal` are mutually inductive finite certificates. An atom succeeds by a
local fact or one successful defining clause. It fails only when absent from the
local facts and every defining clause has a failing body. No defining clauses
makes that last condition vacuous. Conjunction succeeds when both sides succeed
and fails when either well-formed side fails. Truth succeeds and falsity fails.
Negation exchanges the two judgments: `not G` succeeds from failure of `G` and
fails from success of `G`. No rule interprets an unfinished search as failure.
These certificates describe search independently of a particular evaluation order
and are not a runnable evaluator.

Lean verifies the following results without additional axioms or placeholders:

- `succeeds_not_fails` and `fails_not_succeeds`: the two certificate judgments
  cannot both hold for a goal.
- `fails_isGoal` and `IsGoal.closed`: failure certificates concern well-formed
  ground goals, satisfying the NAF groundness gate.
- `succeeds_toDerives`: a success certificate gives a `Derives` proof, using
  `failureEvidence program context` as the NAF relation. This adapter checks the
  exact application symbol, logical KB, and local context.

The certificate results alone do not establish NAF adequacy, correspondence with
the Rust resolver, or that failure excludes every proof in the broader
natural-deduction calculus. The variable extension below adds clause instances;
scopes and the remaining soundness connections are separate steps. This
finite-failure semantics is not well-founded loop completion: both `p :- p` and
`p :- not p` have neither certificate, as verified in the examples.

`AnthillModKbSpec/VariableSearch.lean` adds first-order clause templates using the
same term syntax. `VariableSearch.Program` retains the original variable-bearing
clauses, for example `p(x) :- q(x)`. `Instance` uses one simultaneous substitution
for a clause's head and entire body; every use chooses its own substitution.
Repeated occurrences of a variable share one value. Body-local variables can
have witness values supplied by positive goals. Local assumptions remain ground
atomic facts, rather than implicit universal clauses.

`SafeGoal` checks binding safety before any grounding. Head variables start
known when answering a ground query. Positive atoms supply their variables to
the following conjunct, and NAF can use only variables already known. Thus
`p(x) :- q(y), not r(y)` is allowed, but `p(x) :- not r(y)` is outside this safe
fragment. For a query, the initial known-variable list is empty: choosing an
answer substitution must not make an unbound `not p(x)` succeed. Such a query
has neither an answer nor a query-failure certificate. Quantifiers, nested
implications, higher-order application, and most-general unifiers remain outside
this search extension.

`VariableSearch.Succeeds` and `Fails` concern ground goals against these schematic
clauses. `Answers program context query substitution` supplies ground answers to
non-ground safe queries, sharing the answer substitution across the whole query.
For example, `q(x) ∧ not r(x)` may have an answer `x := 1`; its positive conjunct
must succeed for that same value. These judgments are relational specifications,
not an executable search or value-enumeration algorithm.

Failure requires an exhausted generator, represented by a finite list and proofs
of soundness and completeness. `ExhaustedInstances` covers all matching ground
body alternatives for a ground atom, including all body-local witness values.
`ExhaustedQueryInstances` similarly covers matching clause alternatives of an
atomic variable query, and query failure also excludes matching local facts.
This can certify failure of a missing predicate `r(x)` without enumerating an
infinite value domain. `ExhaustedGroundings` is an alternative interface for
exhausting the groundings of a more general safe query.

A generator's finite sample cannot be declared exhausted while it omits a valid
instance. The value domain has not been restricted to the listed values. Some
infinite instance families have no finite cover; the current rules then provide
no failure certificate, even if a future symbolic procedure could refute the
whole family uniformly. Full symbolic unification and uniform refutation of
infinite families remain future work. This limitation is deliberate: incomplete
enumeration never becomes evidence for NAF.

Lean proves `VariableSearch.succeeds_not_fails`, its symmetric form, and
`queryFails_no_answer`. `succeeds_toDerives` and `answers_toDerives` connect
successful instances and answers to the original schematic logical KB, using
the new certified failure relation. These do not yet establish full resolver
equivalence or model-theoretic soundness.

`AnthillModKbSpec/ScopedSearch.lean` adds universal and nested implication goals
to the first-order search model. Its `Context` explicitly records active rigid
parameter names and local definite formulas. Runtime variables must refer to those parameters; flexible
clause variables are instantiated independently, using the same simultaneous
head/body substitution as before. `forallVar` introduces a fresh parameter,
opens its body, and searches in the extended context. It never proves a
universal goal merely by trying some generated concrete values. Clause bodies
and query answers can contain universal goals, including nested binders.

`AnthillModKbSpec/Opening.lean` supplies lawful fresh names for `Nat` and `String`.
Other name types can supply a `FreshNames` instance. The scope avoids active
parameters, free names in assumptions and the body, and every nested binder.
`Term.openFree` respects shadowing; `openFree_substitutes` proves that opening
with a name absent from nested binders is the existing capture-avoiding
substitution relation. Its Lean function builds syntax rather than executing a
logical goal. Canonical fresh choices and openings let success and failure
certificates refer to the same scope without assuming an alpha-renaming theorem.

Entering a universal scope preserves existing assumptions and adds one parameter.
Its bindings do not escape. Source binding safety drops names learned inside
`forall` before checking following conjuncts. Scoped answer substitutions must
preserve all already-active parameters, and the resulting answer is validated
in the original context. This prevents a future universal witness from leaking
into an answer outside its scope.

An implication `A → G` searches `G` in `Context.assume A`. The premise is
available only in that subproof, including to nested implications and NAF.
`IsLocal` admits atoms, truth, conjunctions, explicit universal quantifiers,
and implications with definite conclusions. `LocalInstance` decomposes those
formulas into atomic heads and goal bodies: conjunctions supply alternatives,
implications add body obligations, and universal assumptions take explicit
capture-avoiding instances. Free names remain fixed parameters. This supports
`p → q → p`, `(p ∧ (p → q)) → q`, and `∀x. (p(x) → p(x))`.
Hypothetical goals also work in global clause bodies. Source safety requires
free names of the premise to be already fixed; names learned inside the
conclusion do not escape the implication.

The universal failure rule searches the same canonically opened body. It is conservative
about opaque parameters: atomic closed-world failure and both NAF rules require
an operand with no free parameter names. Thus a missing `p(eigen)` provides no
failure certificate, and `forall x. not p(x)` cannot succeed just because no
rule matches that opaque witness. A single concrete fact `p(0)` yields neither
certificate for `forall x. p(x)`. Structural failures such as `forall x. False`
can still be certified, and closed NAF such as `forall x. not False` remains
usable. Atomic failure additionally requires `Context.Closed`: every local
assumption must have no free parameter names. Otherwise a syntactic mismatch
between a hypothesis `p(eigen)` and a concrete goal `p(0)` could be mistaken for
absence. This conservative guard can withhold failures even for unrelated
predicates. Closed, explicitly universally quantified assumptions remain usable;
all their applicable instances must still be covered by the generator. This does not add enumeration-based universal counterexamples or claim
complete refutation of universal goals.

`ScopedSearch.succeeds_not_fails` and its symmetric theorem cover nested universal
and implication scopes.
`succeeds_toDerives` checks the eigenvariable freshness and opening conditions
against the existing universal-introduction rule, and maps hypothetical proofs
to implication introduction. `LocalInstance.toDerives` checks local backchaining
using conjunction elimination, implication elimination, and universal instantiation. Its NAF adapter retains the
exact KB and assumptions while packaging the internal rigid scope, allowing one
evidence relation across nested universal proofs. `answers_toDerives` connects
parameter-preserving query instances as well. Exhausted clause-instance
generators remain explicit and cover both global and local instances;
omitting a hypothetical clause cannot justify NAF. Alpha-normalization of scoped
instances, higher-order matching, and an operational use of the Miller
restriction remain later steps. These results establish certificate disjointness
and the bridge to `Derives`. The semantic corollaries additionally require a
model and adequate failure evidence; resolver completeness is not established.

`Tests/Induction.lean` supplies an example KB containing an explicit induction
principle. It uses constructor terms `zero` and `succ(n)`, a domain predicate
`Nat(n)`, and a property `reachable(n)`. The KB contains the following clauses,
where `apply(P, n)` denotes `ho_apply(P, n)`:

```text
reachable(zero).
reachable(succ(x)) :- reachable(x).
Nat(zero).
Nat(succ(x)) :- Nat(x).
Nat.induction(P) :- apply(P, zero),
                    forall n. (apply(P, n) -> apply(P, succ(n))).
apply(P, x) :- Nat(x), Nat.induction(P).
```

`inductionCertificate` substitutes the symbol value `reachable` for `P` and
proves both obligations. Its step introduces a fresh parameter and a local
induction hypothesis, then uses the successor clause. `allNaturalsReachable`
uses the second induction clause to derive `forall n. Nat(n) -> reachable(n)`.
`reachableTwo` instantiates that result at `succ(succ(zero))` and discharges its
`Nat` guard. These are derivations in the object calculus with NAF disabled;
Lean's own natural-number induction is not used to supply the missing rule.
The induction principle is an assumption of this KB. The example checks its
application, rather than proving that it follows from arbitrary Horn clauses
or establishing a model-theoretic justification for it.

The same file gives scoped-search certificates for the concrete base and
hypothetical successor obligations. Generic induction application is checked
with `Derives`: `ScopedSearch` currently excludes `ho_apply`, so this example
does not extend its resolver or claim a higher-order search implementation.

`AnthillModKbSpec/InductionModel.lean` adds a model-theoretic induction example
with an actual nonempty KB. Sigma declares Nat's zero and successor constructors;
`family` is its complete finite domain catalog. The first KB contains constructor
membership clauses and this induction clause:

```text
apply(P, x) :- Nat(x), apply(P, zero),
               forall n. (Nat(n) -> (apply(P, n) -> apply(P, succ(n)))).
```

`inductionRule_valid` proves this clause true for every environment, including
arbitrary values assigned to P, by induction on the generated natural number.
`induction_rule_applies` uses the clause in `Derives` with explicit base and step
obligations. The rule is in the object KB; it is not a new inference rule of
`Derives`. This example specializes the domain schema to Nat, rather than
generating induction clauses for arbitrary mutually recursive Sigma.

The second KB adds the recursive `reachable` clauses above and:

```text
even(zero).
even(succ(succ(x))) :- even(x).
```

The same model validates both stages (`inductionKb_models`, `kb_models`, and
the existential theorem `model_exists`). Its carrier pairs free constructor keys
with propositions, so different naturals have different denotations and logical
values remain available in the untyped universe. Membership checks the entire
value, not just its key. `realizes` proves exact Nat membership, while
`reachable_exact` and `even_exact` identify the predicate interpretations with
their least generated relations. In particular, `even_one_false` refutes
`even(succ(zero))`; this is not an all-atoms-true model.

`sound` and `consistent` apply to this KB with the certified NAF provider.
`Tests/InductionModel.lean` also checks a generated counterexample to “all Nat
values are even” and derives its NAF through that provider. These are existence
and soundness results for these concrete definitions. They do not imply model
existence for arbitrary predicate definitions, adequacy of legacy scoped search
failure, or an executable higher-order induction resolver.

`AnthillModKbSpec/Miller.lean` is an optional syntactic experiment. A `ho_apply`
with a free variable predicate must have pairwise distinct bare bound variables
as arguments. Bound predicates are treated as rigid for this check and may
receive compound arguments. The check traverses scopes, nested implications,
and application arguments, carrying their lexical binding context. It checks
neither typing nor arities and establishes no full higher-order pattern calculus
or unification theorem. It is not a restriction imposed by the KB mirror.

Named argument rows, bounded quantifiers, literal families, name-resolution
scopes, hash-consing, and other KB storage details are omitted. Lexical variable
binding here is distinct from Anthill's symbol-table/domain scopes.

`Tests/Syntax.lean` checks the induction-rule shape, scoped terms as arguments,
nested implications, shared binding, optional Miller restrictions, and clause
translation. These are syntax checks, not proofs of induction's validity.
`Tests/Derivation.lean` constructs proofs using clause instances, local assumptions,
quantifiers, and `ho_apply`, and checks capture avoidance, shadowing, and freshness.
It also checks NAF rule application, clause bodies using NAF, the groundness
gate, and failure evidence indexed by the KB and local context.
`Tests/GroundSearch.lean` checks concrete success/failure certificates, all-clause
coverage, local facts, NAF in rule bodies, the bridge to `Derives`, fragment
restrictions, and the absence of both certificates for positive and negative
self-recursion.
`Tests/VariableSearch.lean` checks shared variables, independent clause uses,
non-ground query answers, clause-local witnesses, NAF binding safety, complete
generators, rejection of incomplete samples, and variable-query failure.
`Tests/ScopedSearch.lean` checks universal facts, concrete-fact rejection,
quantified clause bodies, nested scopes, shadowing, freshness, parameter escape,
opaque-parameter NAF, structural failure, and the connection to `Derives`.

`Tests/ImplicationSearch.lean` checks nested hypothetical facts and rules,
conjunctive and universal premises, both orders of `forall` and implication,
assumption isolation, NAF in extended contexts, exhaustive local alternatives,
local rule failure, opaque-hypothesis failure restrictions, hypothetical global
clause bodies, and the connection to `Derives`.

Build with `lake build`; check the twenty-one example files using `lake env lean`:

```sh
lake env lean Tests/Syntax.lean
lake env lean Tests/Derivation.lean
lake env lean Tests/GroundSearch.lean
lake env lean Tests/VariableSearch.lean
lake env lean Tests/ScopedSearch.lean
lake env lean Tests/ImplicationSearch.lean
lake env lean Tests/Induction.lean
lake env lean Tests/InductionModel.lean
lake env lean Tests/UniversalIntroduction.lean
lake env lean Tests/CounterexampleSearch.lean
lake env lean Tests/InductiveSoundness.lean
lake env lean Tests/InductiveResolution.lean
lake env lean Tests/MillerResolution.lean
lake env lean Tests/LeanCoreMatcher.lean
lake env lean Tests/Soundness.lean
lake env lean Tests/CompletedGround.lean
lake env lean Tests/ScopedNafBoundary.lean
lake env lean Tests/InductiveDomains.lean
lake env lean Tests/CertifiedRefutation.lean
lake env lean Tests/ScopedAtoms.lean
lake env lean Tests/CertifiedScopedSearch.lean
```

CI runs all twenty-one example files.
