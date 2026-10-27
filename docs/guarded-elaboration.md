# Guarded quantifier elaboration

[Elaboration](../AnthillModKbSpec/Resolution/Elaboration.lean) implements S03 over
the existing `Term`, `ProofContext`, and `HornClause` representations. It adds
range guards using foundation constructors; it needs no parser, new term
constructors, or extension of `Derives` or `Semantics.Model`.

For a binder with range `R`, lowering is:

```text
forall x:R. body  ->  forall x. rangeGuard(R, x) -> E(body)
exists x:R. body  ->  exists x. rangeGuard(R, x) and E(body)
```

Binder ranges are generated with the formulas, never inferred. `defaultRanges`
assigns every unannotated binder D_all, the union of all declared generated data
domains. This is the executable profile's default; raw foundation
`Term.forallVar` and `Term.existsVar` still quantify over the whole carrier. To
quantify over predicate references, explicitly annotate `.predicate n`. To
quantify over the full carrier, explicitly use `.carrier`. The default never
infers a predicate range from a variable's name or usage.

`Ranges` is total, so an unannotated binder looks the same as one annotated with
data. The executable profile therefore checks usage instead. `predicateRanged`
rejects a binder applied by `ho_apply` to n arguments unless its range is
`.predicate n` or `.carrier`; a data range, including the default, is never
accepted there. `elaborate?` and `elaborateClause?` lower only checked input and
return `none` otherwise. `elaborate?_eq_some` and `elaborateClause?_eq_some`
identify accepted output with `elaborate` and `elaborateClause`, so the theorems
below apply to it unchanged. Without the check, `forall P. ho_apply(P, zero)`
would lower to `forall P. D_all(P) -> ...`, a guard no registered predicate
satisfies. The check reads annotations at the same paths as lowering and follows
shadowing. Fixed parameters get no guard from lowering, so their machine
declarations govern them instead.

## Symbolic guards and the snapshot boundary

Lowering takes an `AdmissionSignature.Naming`: one membership symbol per data
domain, one for D_all, and one per predicate arity. `rangeGuard` builds:

| Range | Guard |
| --- | --- |
| `.allData` (the default) | `D_all(x)`, an atom over the naming's data symbol |
| `.data domains` | Existing disjunction of the named domains' membership atoms |
| `.predicate n` | `Pred_n(x)`, an atom over the naming's arity-n symbol |
| `.carrier` | Truth |

No guard lists the predicate registry or the domain catalog. An explicit
`.data domains` list names its domains, so it is stable as well. Lowering
therefore never reads the registry, domain definitions, or revision of a
snapshot, and its output depends on nothing but the naming. Registering a
predicate adds a generated fact to the KB and leaves every lowered term
unchanged; a regression checks this with a grown registry.

Snapshots remain the index for closed-world evidence: NAF failure, finite
absence and enumeration certificates, and admission plans. A predicate range
provides no case analysis over registered predicates. A bound predicate value
is resolved by lookup on its symbol, and a flexible one by matching or by
resolving its guard against the generated facts.

`AdmissionSignature.Realizes` requires each membership symbol to have its exact
meaning: domain membership as before, D_all on all generated data, and `Pred_n`
on exactly the references of predicates registered at arity n. With it,
`rangeGuard_satisfies` identifies each guard with `Range.Contains`. Aliases and
overlapping arities work as in [AdmissionSignature](admission-signature.md). An
empty range produces a vacuous universal and an unsatisfied existential. Neither
data domains nor predicate ranges need to be disjoint.

## Binder annotations

`Ranges Domain` is sidecar metadata of type `List Nat -> Range Domain`. A path
identifies a lexical site in the **source** term, independently of binder names:

- The root has path `[]`.
- A unary constructor's body uses child `0`; binary operands use children `0`
  and `1`.
- Application arguments use their indices, starting at `0`.
- A dictionary call uses child `0` for its dictionary and children `1` onward
  for its arguments. Its selector path and operation symbol are preserved.

Only paths at quantifiers are read. For example, for
`forall x. exists x. body`, the binders are at `[]` and `[0]`. They may have
different ranges despite sharing a name. Override the default at those paths:

```lean
def ranges : Elaboration.Ranges Domain := fun path =>
  if path = [0] then .predicate 1 else Elaboration.defaultRanges path
```

`elaborate naming ranges term` traverses every constructor, including formulas
stored in application arguments, dictionary expressions, equality, and NAF.
It preserves `ho_apply` symbols and arguments. The same naming supplies all
guards. Annotation paths remain attached to source sites during alpha-renaming;
paths in the expanded output include guard nodes and must not be reused as
source annotation paths. Lower each source once.

## Semantic, substitution, and scope guarantees

`eval` defines the compositional value semantics of an annotated source term.
`eval_elaborate` proves equality with foundation evaluation of the target, and
`satisfies` gives the corresponding truth equivalence. Value equality matters:
the shared carrier allows formulas in arguments and equality, and a model's
logical laws do not identify every pair of equally true values.

`forall_satisfies` and `exists_satisfies` characterize quantification over
exactly the selected semantic values, using `rangeGuard_satisfies`. These results
require no whole-carrier coverage, finite member enumeration, or reference
injectivity.

`freeVars` proves exact preservation of the free-name set. Guards refer only to
the binder they restrict and introduce no names. `opening_substitutes` proves
that source opening and elaboration agree through the existing capture-avoiding
`Substitutes` relation, with the existing freshness condition on nested binders.

`elaboration_substitutes` moves a source substitution through lowering when its
images are `Stable`: elaboration leaves every image unchanged at every site.
This includes variable renaming and ordinary constructor-data substitutions.
It supports alpha-renaming and shadowing. For formula-valued replacements that
need their own range annotations, first elaborate the replacement separately,
then substitute it into the lowered target. `satisfies_substitutes` applies to
arbitrary target substitutions without the stability condition. The lowerer
does not invent a fresh-name algorithm or guess annotations inside replacement
formulas.

`forallRange_data` identifies data universals with the existing
`Universal.toTerm`, and `forallAll_intro` reuses `Derives.forallAll_intro` for the
explicit list of every declared domain. `forallRange_intro` and
`existsRange_intro` reconstruct general guarded introductions from the existing
inference rules; existential introduction checks the guard and body with the
same witness substitution. Its guard premise comes from the derivations below.

## Contexts and rule templates

`elaborateContext` traverses local assumptions without adding implicit
quantifiers or guarding their free parameters. Assumption i uses annotation
child i, so different assumptions can declare different binder ranges. `context_satisfies` and
`context_fresh` preserve their semantic interpretation and eigenvariable
freshness conditions.

`elaborateClause naming ranges rangeOf clause` compiles a rule template's head
and body and prepends guards for all its free variables to its body. It applies
to definite and goal clauses, including equation heads. The head uses annotation
child `0`; body formulas use children `1` onward. `rangeOf` supplies each implicit
variable's declared range. For an unannotated data variable, return `.allData`;
a predicate variable must instead return its declared `.predicate n`.
`clausePredicateRanged` checks this, treating free clause variables as bound by
`rangeOf`. For example, `elaborateClause?` rejects the induction rule when its
`P` keeps the data default, since the guard `D_all(P)` would keep the rule from
ever firing. Repeated free names repeat the same guard.

The resulting clause keeps the KB's ordinary implicit universal closure.
`clause_satisfies` proves its per-environment meaning: if all free variables
belong to their declared ranges and the compiled body holds, the compiled head
holds (or falsity for a goal clause). It makes no domain-coverage assumption.
Subsequent clause application substitutes into the **entire lowered clause**,
including its guards, using one substitution. Guard collection is done before
instantiation; recollecting guards from an instantiated clause could lose a
variable's original range obligation.

## Derivable guards and generated clauses

`Realizes` makes guards true, but `Derives` proves a membership atom only from
KB clauses. The signature therefore contributes generated clauses, collected in
`Elaboration.signatureKb`:

```text
member_D(c(x_1, ..., x_k)) :- member_D_1(x_1), ..., member_D_k(x_k)   -- per constructor rule
D_all(x) :- member_D(x)                                              -- per declared domain
Pred_n(s).                                                           -- per registered s at arity n
```

The constructor clauses come from
[MembershipClauses](../AnthillModKbSpec/Foundation/MembershipClauses.lean).
`Member.derives` derives the membership atom of every generated tree using only
the existing clause rule, provided argument names are distinct within each rule
(`DistinctNames`). For the Nat domain, these clauses are exactly the hand-written
`natZero` and `natSucc`.

`models_signatureKb` proves that a realizing model satisfies every generated
clause, with no coverage or disjointness assumption. `rangeGuard_derives_data`,
`rangeGuard_derives_allData`, and `rangeGuard_derives_predicate` derive each kind
of guard from them. A predicate guard comes from its fact, by lookup.

The elaborated KB `E(KB)` must therefore include `signatureKb`. Without it,
data-ranged existential introduction and guarded rule bodies have no derivation,
even where they are semantically true.

The [regressions](../Tests/Resolution/Elaboration.lean) exercise exact Nat data,
carrier values outside that data, predicate references and arity overlap,
same-name nested binders, alpha-renaming, dictionary traversal, context freshness,
an actual empty domain, two distinct domains both generating Nat, rule guards,
and guarded derivation reconstruction. They also check that predicate-position
binders reject the data default, a mismatched arity, and a shadowing data binder,
and that the induction rule is rejected under D_all. D_all, data, and predicate
guards, including those in a lowered rule body, are derived from generated
clauses rather than assumed
([membership regressions](../Tests/Foundation/MembershipClauses.lean)). A grown
registry leaves lowered terms unchanged. Key results are audited for standard
logical axioms. Search, machine scope enforcement, and operational admission
remain later tickets.
