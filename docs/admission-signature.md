# Admission signatures and quantified-variable ranges

S02 / WI-20261026-3AAXX is implemented in
[AdmissionSignature.lean](../AnthillModKbSpec/Resolution/AdmissionSignature.lean), with model-backed
examples in [Tests/Resolution/AdmissionSignature.lean](../Tests/Resolution/AdmissionSignature.lean).
The registry lives in `Resolution/` because it specifies admission ranges and
machine-name roles; its model contracts reuse the independent `Foundation/`.

`Signature` combines an existing `InductiveDomains.FiniteFamily`, its membership
symbols, and a finite list of predicate symbol/arity declarations. A finite
catalog of domain names does not assert finite inhabitants. The signature adds
no semantic sorts, Term constructors, or changes to raw quantifier semantics.

`SignatureSnapshot.Registered` checks a symbol/arity pair in that finite list.
`registered?` implements this check using decidable symbol equality, with an
acceptance equivalence theorem. Duplicate declarations and multiple arities for
one symbol are allowed. A miss is an absent capability declaration, with no
logical falsity or NAF consequence.

`reference model symbol` is `model.application symbol []`, the value already
denoted by `.app symbol []`. `SignatureSnapshot.PredicateMember model n value` means that
the value is the reference of some declared n-ary symbol. `ReferenceEvidence`
records that representative, its declaration, and its denotation equation.
`predicateMember_iff_evidence` connects the range predicate and this evidence.
`ReferenceEvidence.hoApply` uses the existing model law to relate application
of the reference to direct application of its representative, at the declared
arity. `satisfies_hoApply_reference` states the corresponding existing-Term law.
These application laws concern truth; they do not assert equality of the
direct and indirect returned values.

No injectivity, unique arity, or separation from data is assumed. Two symbols
with equal references necessarily agree in predicate truth (`reference_alias`).
An unregistered symbol can alias a registered reference, so an unknown name does
not imply that its value lies outside P_n. `not_predicateMember` requires ruling
out all registered representatives. Data and predicate ranges may also overlap.

`Range` records unrestricted carrier, data-domain union, or predicate arity.
Here "range" means the allowed values of a quantified variable.
`Range.Contains` gives their meanings over the same model carrier.
`AdmissionSignature.Realizes` requires the existing exact constructor-generated data
interpretation; `Realizes.data_iff` connects data ranges to membership predicates.
`ForallPredicates` and `forallPredicates_iff` specify quantification over precisely
the registered reference values. S03 owns guarded formula elaboration and the
default range of unannotated binders. These semantic range definitions supply
neither a general decision procedure on values nor complete quantifier search.

`NameDeclaration` attaches a range and rigid/flexible role to a name as machine
metadata. Both roles use ordinary carrier values. S04-S05 own scope levels,
dependency constraints, substitution, and the enforcement of rigidity.

`SignatureSnapshot` contains the full signature and a revision, without KB facts
or local proof context. `ReusableAt` requires
equality of whole snapshots; `ReferenceEvidence.rebase` transports evidence only
with that equality. Different revisions preclude reuse, and equal revisions do
not authorize reuse after declaration changes. This is a logical reuse contract,
not an executable equality test for domain definitions or semantic propositions.
S07/S15 own operational admission and invalidation of plans.

Dictionary extensions may represent references differently from nullary symbol
values. `DictionaryCompatible` explicitly requires agreement for registered
references before `dictionary_hoApply` connects their invocation and ho_apply.
The existing dictionary extension contract alone does not establish this
agreement. Dictionary registration, lookup guards, and evaluator admission remain
S13-S14 obligations.

The concrete witness reuses `InductionModel.model`, its exact generated Nat
domain, and its KB model theorem. Regressions cover unary reachable, an overlapping
second arity, data versus predicate quantification, unrestricted raw forall,
overlap with data, aliased/unknown references, dictionary compatibility, and stale
snapshots (including a changed registry with an unchanged revision). The registry
does not assert induction validity; that remains a separate model theorem.
The tests audit key results against the standard logical axioms.
