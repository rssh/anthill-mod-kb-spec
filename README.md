# Anthill KB logic: soundness model

The objective is to **prove soundness of an untyped KB logic**. We define its
syntax, inference rules, and model, then prove that every derivation preserves
truth. Induction principles are ordinary KB clauses validated in the model.
Automatic proof discovery is a separate implementation concern.

The logic theorem says:

$$
KB;\Gamma\vdash_N G
\quad\Longrightarrow\quad
\forall\rho.\;M,\rho\models\Gamma\Rightarrow M,\rho\models G.
$$

It requires a compositional model satisfying the KB and an adequate NAF evidence
provider. For our certified provider, adequacy is proved under complement NAF.
A model with exact inductive-domain membership packages these assumptions in
`InductiveSoundness.Interpretation`. The resulting logic theorem is
**`InductiveSoundness.declarative_sound`**, with consistency corollary
`declarative_consistent`.

With a sound positive equation oracle, the extended theorem is
**`InductiveSoundness.declarative_sound_with_equation_oracle`**. Accepted
conditional equations extend the same KB set; their bodies must still be proved.
[The oracle theorem](docs/equation-oracle.md) states its semantic contract and
requires NAF adequacy for the extended KB.

## Where to start

Modules are grouped under `AnthillModKbSpec/`:

| Directory | Contents |
| --- | --- |
| `Foundation/` | Common syntax, derivations, generic model and soundness, substitution, domains, and dictionary contracts |
| `Models/` | Concrete Boolean, constructor-key, induction, and ordering model witnesses |
| `Deriving/` | Generation of constructor-domain presentations from Lean inductive data |
| `Resolution/` | Shared matching, search certificates, admission signatures, and reconstruction proofs |
| `Resolution/P0/` | Ground success/failure certificates and completed-model semantics used by P0 |
| `Archive/` | Opt-in historical approaches |

`import AnthillModKbSpec.Foundation` loads the generic logic independently of
resolution. `AnthillModKbSpec.Models` adds concrete witnesses, and
`AnthillModKbSpec.Resolution.P0` loads the ground layer. The primary
`import AnthillModKbSpec` still loads all current modules. Declaration namespaces
such as `Semantics.Model` and `GroundSearch` are unchanged.

Lean inductive data can supply domain definitions and exact-membership proofs
using [`deriving InductiveDomain`](docs/inductive-domain-deriving.md). The generic
class is in the foundation; its generation metaprogram is imported separately.

| Part | Source |
| --- | --- |
| Syntax and set of KB clauses | [Syntax](AnthillModKbSpec/Foundation/Syntax.lean), [LogicalKb](AnthillModKbSpec/Foundation/LogicalKb.lean) |
| Inference rules: `Derives` | [Derivation](AnthillModKbSpec/Foundation/Derivation.lean) |
| Compositional model and general `Model.sound` theorem | [Semantics](AnthillModKbSpec/Foundation/Semantics.lean) |
| Certified NAF and its adequacy proof | [CertifiedRefutation](AnthillModKbSpec/Resolution/CertifiedRefutation.lean) |
| Packaged logic soundness and consistency | [InductiveSoundness](AnthillModKbSpec/Resolution/InductiveSoundness.lean) |
| Nonempty KB with valid induction and predicate definitions | [InductionModel](AnthillModKbSpec/Models/InductionModel.lean) |
| Semantic contract for callable references and operation dictionaries | [OperationDictionaries](AnthillModKbSpec/Foundation/OperationDictionaries.lean) |
| Guarded quantifier, context, and rule-template elaboration | [Elaboration](AnthillModKbSpec/Resolution/Elaboration.lean), [range and substitution contracts](docs/guarded-elaboration.md) |
| Generated domain-membership clauses for derivable guards | [MembershipClauses](AnthillModKbSpec/Foundation/MembershipClauses.lean) |
| Lawful Nat and Bool order dictionaries | [OrderDictionaries](AnthillModKbSpec/Models/OrderDictionaries.lean) |
| Conditional operation equations and replacement | [Equation rule note](docs/conditional-equations.md), [examples](Tests/Foundation/EquationRules.lean) |
| Soundness with an equation oracle | [EquationOracle](AnthillModKbSpec/Foundation/EquationOracle.lean), [theorem and examples](docs/equation-oracle.md) |

Fresh rigid parameters are proof-level names interpreted by environments, not
new model elements. Domain guards restrict forall to generated values. The
concrete Nat model distinguishes values and makes `even(1)` false; it supplies
a consistency witness for the example KBs.

The result covers certified NAF, not arbitrary unsuccessful search. Explicit
negation and open/closed predicate policies remain future work.

Dictionary operation calls have [syntax and a semantic contract](docs/operation-dictionaries.md):
explicit callable references, uniform application, and predicate/operation roles
on callable entries. Dictionaries are finite trees containing required-model
subdictionaries, with paths and recursive interface validation. The contract
proves value agreement between direct and indirect calls.
`Term.dictionaryCall dictionary path operation args` uses checked lookup in
models built with `Extension.withDictionaryCalls`. Substitution, scope handling,
and the logic's soundness theorem cover this constructor.

[The Ord example](docs/order-dictionaries.md) implements Nat's usual order and
Bool's `false < true` in one untyped model. Both dictionaries include a required
Eq model and satisfy proved domain, equality, and total-order laws.

[Conditional equations](docs/conditional-equations.md), `left <=> right :- body`,
are clauses with value-equality heads in the same KB. Their conditions must be
proved before using the equality. Equations can also occur as goals in rule
bodies, proved from other equation rules. Equality replacement, including inside
dictionary calls, is covered by the soundness theorem.

## Check and read

Lean 4.35.0 is managed by Lake/Elan.

Tests mirror the source layers in `Tests/Foundation/`, `Tests/Models/`,
`Tests/Deriving/`, and `Tests/Resolution/` (including `P0/`). Historical tests
remain under `Tests/Archive/`. The current-test CI job recursively discovers
tests while excluding the archive, which has its own job.

```sh
lake build
lake env lean Tests/Resolution/InductiveSoundness.lean
lake env lean Tests/Models/InductionModel.lean
while IFS= read -r -d '' test; do
  lake env lean "$test" || exit 1
done < <(find Tests -path Tests/Archive -prune -o -name '*.lean' -print0)
```

Read [the overview](overview_anthill.tex) for the logic and proof, and
[the module notes](docs/model-notes.md) for formalization details.
[Implementation experiments](docs/implementation.md) describe matching and
resolution-proof reconstruction; their soundness corollaries build on the logic
theorem. Superseded designs remain in
[Archive](AnthillModKbSpec/Archive/README.md), outside the main import graph.


Most of proof is LLM-generated.
