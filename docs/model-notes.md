# Logic, semantics, and proof boundaries

The project's objective is soundness of the declarative logic. Start with
[the overview](../overview_anthill.tex). Matching and proof discovery are described
separately in [the implementation note](implementation.md).

Source modules are organized as `AnthillModKbSpec/Foundation/` for the generic
logic and model, `Models/` for concrete witnesses, and `Resolution/` for search
and admission groundwork (with ground certificates in `Resolution/P0/`).
Foundation and concrete-model imports are independent of resolution. The
`Foundation`, `Models`, and `Resolution` aggregate modules can be imported
separately; declaration namespaces are preserved.

`Foundation.InductiveDomain` provides exact constructor-domain presentations for
Lean data types. The separate `Deriving.InductiveDomain` metaprogram generates
these definitions and their proofs for supported first-order inductives; see
[the deriving guide](inductive-domain-deriving.md). Its tree correspondence is
separate from interpreting those trees in a logical model.

## Syntax and inference rules

`Syntax` defines `Term`: variables, data, applications, dictionary operation calls,
value equality, connectives, and quantifiers.
Predicate variables use the same variable constructor. `ho_apply` is a designated
ordinary application symbol. `LogicalKb` is a set of clauses with implicit
universal closure of their free variables; local assumptions retain fixed parameters.

`Derivation.Derives` is the declarative judgment, indexed by the KB, local
assumptions, goal, and NAF evidence provider. It has the usual logical rules,
capture-avoiding clause instances, concrete-symbol application rules, and
closed-operand NAF introduction. `Substitution` and `Opening` formalize scope
and freshness. A derivation is a proof tree, independent of search strategy.

`HornClause.equation left right body` is a definite clause with an equality head.
`Derives.equation` instantiates both sides and the condition body together.
`equalRefl`, `equalSymm`, `equalTrans`, and `equalSubst` supply value equality
and capture-avoiding replacement. All concrete models implement `holds_equality`.
`Model.sound` includes these rules. See [conditional equations](conditional-equations.md)
for the semantic condition and a nonempty KB with a consistency proof.

## Model and theorem

`Semantics.Model` interprets the shared value carrier, including formulas as data.
An environment assigns each free parameter a value; freshness permits changing
an eigenparameter's value without affecting the local assumptions. Raw forall
ranges over the entire carrier.

`Model.sound` proves that all `Derives` rules preserve truth, assuming KB validity
and `Model.FailureAdequate` for the chosen NAF provider. The proof is by induction
on derivations. The substantive steps use substitution correctness, preservation
of local assumptions under fresh environment updates, and NAF adequacy.

`CertifiedRefutation` proves adequacy of its exact-KB, exact-context certificates
under complement NAF. `InductiveSoundness.declarative_sound` packages the logic
result for `InductiveSoundness.Interpretation`; `declarative_consistent` excludes
falsity. `positive_consistent_of_model_exists` gives the model-existence
corollary for the positive calculus. These results require no native matcher.

`EquationOracle` packages positive acceptance of conditional equations with the
proof that every accepted claim preserves value equality under all environments
satisfying its body. `models_extension` validates the KB enlarged by these
ordinary clauses. `Model.sound_with_equation_oracle` and its consistency
corollary then reuse `Model.sound`; NAF adequacy refers to the enlarged KB.
`Interpretation.withEquationOracle` preserves exact inductive realization and
complement NAF, and the packaged `declarative_sound_with_equation_oracle` theorem
covers this extension. See [the oracle note](equation-oracle.md) for the contract
and a concrete closed-computation specification.

## Inductive domains and model existence

`InductiveDomains` defines least constructor-generated membership and exact
realization of each membership predicate. `FiniteFamily` gives the domain catalog.
`D_all` is their disjunction, and bounded forall abbreviates
`forall x. D_all(x) -> P(x)`. Equivalence to unrestricted forall additionally
requires carrier coverage.

`InductionModel` exhibits a nonempty KB/model with exact Nat membership, distinct
Nat denotations, a valid ordinary induction clause, and least-generated
`reachable` and `even` predicate interpretations. `inductionRule_valid` validates
its induction clause for arbitrary predicate values. `model_exists` supplies
existence for these examples, not arbitrary predicate definitions.

## Operation dictionary contract

`OperationDictionaries.Extension` adds explicit callable references, application,
dictionary construction, and projection over an existing model. Its central law
is value equality: `call (reference f) args = model.application f args`.
Consequently indirect calls can replace direct calls inside data expressions.
A dictionary is a finite tree with callable leaves and named subdictionaries
representing required models. A callable entry contains a predicate/operation
role, a symbol, and captured values; checked lookup validates both the entry tag
and the symbol's declared role. Paths follow nested required models.
`Interface` and `Implements` express callable fields, recursively required model
interfaces, and semantic laws at every node without depending on Anthill's typed
sorts. A parent interface proof supplies interface proofs for its required children.

`Term.dictionaryCall dictionary path operation args` evaluates through
`Model.dictionaryCall`. `Extension.withDictionaryCalls` supplies checked nested
lookup and invocation, with an explicit value for invalid accesses. Substitution,
opening, and model soundness cover the new constructor. Existing models need
additional structure to implement the intended dictionary contract; the old
`holds_hoApply` truth equivalence alone does not imply value equality. The finite
search fragments retain their existing restrictions on data and atoms.
See [the dictionary note](operation-dictionaries.md) for examples and boundaries.

`OrderDictionaries` constructs Nat and Bool order dictionaries in one shared
carrier. Each has a nested WeakOrd dictionary and required Eq dictionary.
`nat_implements` and `bool_implements` prove interface satisfaction, exact
domain membership, equality correctness, and total-order laws. Comparisons
return `Ordering` values, and Bool is ordered `false < true`. See
[the order example](order-dictionaries.md) for the syntax and scope of this model.

## Certificate support and limits

Atomic refutation uses `ScopedAtomSemantics` completion and exhaustive instance
coverage. `GroundSearch`, `VariableSearch`, `ScopedSearch`, `SearchSoundness`,
and `CompletedGround` supply supporting operational fragments and certificates.
Raw scoped search failure is not adequate in general; `Tests/Resolution/ScopedNafBoundary.lean`
formalizes that boundary.

`UniversalIntroduction` supplies generalization lemmas. `CounterexampleSearch`
and `CertifiedScopedSearch` provide additional semantic certificate interfaces
for guarded universals. Their soundness lemmas do not imply that every external
domain certificate translates into KB-only `Derives`.

The logic theorem establishes neither completeness nor correctness of Anthill's
production search. A failed, unsupported, suspended, or truncated attempt is
not automatically NAF evidence. Explicit negation and open/closed predicate
policies remain future work.

Historical designs and chronological notes are indexed in
[Archive](../AnthillModKbSpec/Archive/README.md).
