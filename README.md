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
| `Resolution/P0/` | Ground success/failure certificates and completed-model semantics, ranks, the P0 command set, total P0 runs, the P0 admission checker, and witnesses for open atoms in ground programs |
| `Resolution/P1/` | Supplied proof trees as `Term`, their checker and reconstruction, proof imports, checked exports of machine runs, the logical nodes of S09 and S10 commands, evidence-first NAF, and the module's answers over the completion |
| `Resolution/P3/` | Proof strategies that may end Undecided: structural induction principles, the admitted induction path, and its answers |
| `Archive/` | Opt-in historical approaches |

`import AnthillModKbSpec.Foundation` loads the generic logic independently of
resolution. `AnthillModKbSpec.Models` adds concrete witnesses, and
`AnthillModKbSpec.Resolution.P0` loads the ground layer with P0 evaluation on
the shared machine and the P0 admission checker; `AnthillModKbSpec.Resolution.P1`
adds proof checking on top of it, and `AnthillModKbSpec.Resolution.P3` the
admitted induction path. The primary
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
| Abstract machine states, continuations, and proof evidence | [Machine](AnthillModKbSpec/Resolution/Machine.lean), [state and evidence contracts](docs/machine-state.md) |
| Delayed goals: suspension, exactly-once wakeup, deferred proofs, the closing phase, floundering | [State](AnthillModKbSpec/Resolution/Machine/State.lean), [delayed goals](docs/machine-delay.md), [traces](Tests/Resolution/Delay.lean) |
| Alpha-renaming instantiation, clause freshening, and scope-safe matching | [Freshening](AnthillModKbSpec/Foundation/Freshening.lean), [Unification](AnthillModKbSpec/Resolution/Machine/Unification.lean), [matching contracts](docs/machine-matching.md) |
| Ordinary clause selection and positive execution; reconstruction of successful runs | [Positive](AnthillModKbSpec/Resolution/Machine/Positive.lean), [Reconstruction](AnthillModKbSpec/Resolution/Machine/Reconstruction.lean), [strategy and guarantees](docs/machine-positive.md), [traces](Tests/Resolution/Positive.lean) |
| P0 admission and total evaluation: NAF in the same run, guard decisions, ranks, Ready plans, runs from the query that end in `Succeeds` or `Fails` | [Admission](AnthillModKbSpec/Resolution/P0/Admission.lean), [Run](AnthillModKbSpec/Resolution/P0/Run.lean), [Negation](AnthillModKbSpec/Resolution/Machine/Negation.lean), [design and guarantees](docs/machine-p0.md), [traces](Tests/Resolution/P0/Admission.lean) |
| P1 proof checking: supplied trees as `Term`, a terminating checker that decides validity and reconstructs `Derives`, proof imports, checked exports of P0 runs | [Tree](AnthillModKbSpec/Resolution/P1/Tree.lean), [Encoding](AnthillModKbSpec/Resolution/P1/Encoding.lean), [Export](AnthillModKbSpec/Resolution/P1/Export.lean), [Import](AnthillModKbSpec/Resolution/P1/Import.lean), [design and guarantees](docs/proof-checking.md), [traces](Tests/Resolution/P1/Check.lean) |
| Left rules and compound clause heads: selected conjunction, disjunction, existential, universal, and implication assumptions with their continuations, compound heads, the left strategy, constructions in S08 logical nodes, proof-layer diagnostics beside P0 | [LeftRules](AnthillModKbSpec/Resolution/Machine/LeftRules.lean), [LeftStrategy](AnthillModKbSpec/Resolution/Machine/LeftStrategy.lean), [P1/Derived](AnthillModKbSpec/Resolution/P1/Derived.lean), [ProofLayer](AnthillModKbSpec/Resolution/ProofLayer.lean), [design and guarantees](docs/machine-left.md), [traces](Tests/Resolution/LeftRules.lean) |
| Evidence-first NAF by refutation in the Clark completion: NAF on rigid parameters, open predicates marked by a reserved symbol, the refutation search with only-if uses and equation joins, positive witnesses first, checked evidence indexed by the snapshot | [Completion](AnthillModKbSpec/Foundation/Completion.lean), [Machine/Refutation](AnthillModKbSpec/Resolution/Machine/Refutation.lean), [P1/Refutation](AnthillModKbSpec/Resolution/P1/Refutation.lean), [P1/Negation](AnthillModKbSpec/Resolution/P1/Negation.lean), [design and guarantees](docs/machine-negation.md), [traces](Tests/Resolution/Negation.lean) |
| `ho_apply` conversion and whole-formula head matching: concrete indirect goals normalized (`ho_goal`), candidates applying a predicate by `ho_apply` matched against a direct goal's indirect view and converted, also under implications, rigid predicates never assigned, lambda-valued answers classified as gaps, a clause selected by its whole head (induction principles), conversion nodes checked by S08 | [Conversion](AnthillModKbSpec/Resolution/Machine/Conversion.lean), [LeftStrategy](AnthillModKbSpec/Resolution/Machine/LeftStrategy.lean), [P1/Derived](AnthillModKbSpec/Resolution/P1/Derived.lean), [design and guarantees](docs/machine-conversion.md), [traces](Tests/Resolution/Conversion.lean) |
| Admitted induction: the structural principle of every declared domain, one case per constructor, lowered with `P` at `.predicate 1` and proved valid, static admission reporting what the cases cannot run in the query's context and the clauses they may select, the principle selected once by its whole head, `∀x:Nat. reachable(x)` reconstructed and true in the induction model, the exported tree checked by S08 | [P3/Principle](AnthillModKbSpec/Resolution/P3/Principle.lean), [P3/Induction](AnthillModKbSpec/Resolution/P3/Induction.lean), [design and guarantees](docs/machine-induction.md), [traces](Tests/Resolution/P3/Induction.lean) |
| Answers Yes, No, Unknown, and Undecided(blockers): the logical Unknown of open predicates kept apart from the machine's gaps and from operational outcomes, two checked witnesses as models of the completion, admission requests as blockers before anything runs, the combination rule | [Answer](AnthillModKbSpec/Resolution/Answer.lean), [OpenAtoms](AnthillModKbSpec/Resolution/Machine/OpenAtoms.lean), [P0/Open](AnthillModKbSpec/Resolution/P0/Open.lean), [P1/Answer](AnthillModKbSpec/Resolution/P1/Answer.lean), [KeyModel](AnthillModKbSpec/Models/KeyModel.lean), [design and guarantees](docs/answers.md), [traces](Tests/Resolution/Answer.lean) |
| Lawful Nat and Bool order dictionaries | [OrderDictionaries](AnthillModKbSpec/Models/OrderDictionaries.lean) |
| Conditional operation equations and replacement | [Equation rule note](docs/conditional-equations.md), [examples](Tests/Foundation/EquationRules.lean) |
| Soundness with an equation oracle | [EquationOracle](AnthillModKbSpec/Foundation/EquationOracle.lean), [theorem and examples](docs/equation-oracle.md) |

Fresh rigid parameters are proof-level names interpreted by environments, not
new model elements. Domain guards restrict forall to generated values. The
concrete Nat model distinguishes values and makes `even(1)` false; it supplies
a consistency witness for the example KBs.

The result covers certified NAF, not arbitrary unsuccessful search: S07's
ground certificates, and S10's refutations in the Clark completion, which also
cover operands with rigid parameters. A predicate is kept open by a clause
`p(x̄) :- UNKNOWN` with a reserved symbol; a goal it leaves open is answered
Unknown only with two checked witnesses, models of the completion in which it
holds and fails ([answers](docs/answers.md)). Explicit negation remains future
work.

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
`Tests/Deriving/`, and `Tests/Resolution/` (including `P0/`, `P1/`, and `P3/`). Historical tests
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
