# Dictionary operations by evaluators; laws as checked lemmas (S14)

S14 is the dictionary operation/equality route of the
[admission contract](lean-admission-contract.md): a P1 decision of
`call = result` by a registered total evaluator, and dictionary laws used
only as checked lemmas. It builds on the [S13 registry](dictionary-registry.md),
the [equation oracle](equation-oracle.md), [S08 proof checking](proof-checking.md),
and [S20 checked lemmas](machine-lemmas.md). Traces are in
[Tests/Resolution/DictionaryEvaluation.lean](../Tests/Resolution/DictionaryEvaluation.lean).

An operation's value is its evaluator's; laws are statements about it. A bare
operation term is evaluated where its value is demanded, never by firing laws.
Law search is P3: a law is used only through a checked lemma, and a failed law
candidate refutes nothing.

| Module | Contents |
| --- | --- |
| [DictionaryEvaluation](../AnthillModKbSpec/Resolution/DictionaryEvaluation.lean) | Registered evaluators (`Evaluation`, `Evaluation.For`, `Target`, `Snapshot.target?`, `Snapshot.evaluate`), their evidence (`Evaluation.Sound`, `Snapshot.Evaluated`, `Evaluation.Total`, `Evaluation.Closed`, `Snapshot.Complete`, `Snapshot.Separated`, `Snapshot.Models`), soundness and totality (`evaluate_sound`, `evaluate_member`, `evaluate_total`), the evaluated equations as an equation oracle (`Snapshot.oracle`, `Snapshot.checkSnapshot`, `checkSnapshot_kb`, `models_evaluated`), the decision (`Equation`, `Snapshot.Decides`, `Snapshot.decide`, `decide_found`, `decide_sound`, `separates`, `Snapshot.decision`, `decide_derives`, `decide_refutes`) |
| [OrderEvaluation](../AnthillModKbSpec/Resolution/OrderEvaluation.lean) | The Nat and Bool evaluators of the order registry (`evaluations`): `less` and `equal` for `natOrd`, `natDesc`, `boolOrd`; their soundness in the order model (`evaluated`), totality (`complete`), separation of Nat and Bool members (`separated`), and the model the answers are about (`models`) |
| [DictionaryLaws](../AnthillModKbSpec/Resolution/DictionaryLaws.lean) | Laws in the proof layer (`Law.clause`, `Registry.lawClauses`, `models_lawClauses`), conditional views (`ViewStep`, `View`, `viewsOf`, `Law.views`, `View.statement`), their proofs from the law (`premiseProof`, `replay`, `introduce`, `View.proof`), lemma entries (`View.lemma`, `Law.lemmas`), the laws a goal may need (`callShape`, `compatible`, `View.mayConclude`, `Registry.lawsFor`) |
| [Machine/Dictionary](../AnthillModKbSpec/Resolution/Machine/Dictionary.lean) | Evaluation on value demand (`Expansion.evaluation`, `Expansion.orient`, `evaluable`, `Strategy.withEvaluation`, `withEvaluation_sound`); laws matched structurally (`callShape`, `lawInstance?`, `lawAttempt`, `Response.prepend`, `Strategy.withLaws`, `withLaws_sound`) |
| [P1/Evaluation](../AnthillModKbSpec/Resolution/P1/Evaluation.lean) | The evaluation rule (`Snapshot.evaluates`, `evaluationRule`), its node (`Unfold.evaluation`, `Unfold.evaluation_proves`), and the export of a run's evaluation node (`exportNode_evaluation`) |
| [P1/Tree](../AnthillModKbSpec/Resolution/P1/Tree.lean) | S08 snapshots with registered evaluators (`Evaluator`, `Snapshot.evaluators`, `Snapshot.Evaluates`, `Snapshot.kb`, `Snapshot.mem_kb`, `Snapshot.kb_of_evaluators`, `Snapshot.evaluated_derives`) |
| [DictionaryRoute](../AnthillModKbSpec/Resolution/DictionaryRoute.lean) | Member trees (`memberOf?`, `membersOf?`, `memberOf?_sound`, `memberOf?_complete`), admission (`Target.admits`, `Snapshot.admits?`, `admits?_decides`, `admits?_complete`), the decision as run (`Snapshot.check?`, `check?_some`, `check?_decide`, `check?_true`, `check?_false`, `check?_complete`), the setup (`Route`: `program`, `checkSnapshot`, `checker`, `offered`, `strategy`, `covers`, `strategy_sound`), blockers (`Route.outside`, `Route.blockers`, `Blocker.repeats`, `Blocker.once`), answers (`Route.decision?`, `Route.evaluationProof`, `Route.answer`, `Route.meaning`, `answer_sound`, `answer_definite`, `answer_accepted`) |

## Evaluators

An evaluator is registered per dictionary operation (`Evaluation`): the
dictionary's name and version, the operation's path, field, and argument
count, and a Lean function from argument terms to a value term, `none` where
it does not evaluate. It is used only where S13 admits the call (`Snapshot.target?`):

- the access is declared: a registered name, an operation of its interface at
  this path, field, and argument count (`Registry.access?`);
- the registration states a primitive contract for the operation with the
  call's argument count (`Primitive`), found among its contracts by that count;
- an evaluation is registered for the registration's name and version, and the
  operation at that argument count (`Evaluation.For`). A new version needs its
  own, and so does each contract of one operation.

`Snapshot.evaluate` is the registry's evaluator: the target's evaluation, run
on the call's arguments. Its claims are evidence, proved, not trusted:

| Claim | Evidence |
| --- | --- |
| Wherever it answers, the answer is the call's value | `Evaluation.Sound`, per interpretation; `Snapshot.Evaluated` for every evaluation registered for a registration's name, version, and contract (path, field, argument count). An evaluation for another version, or for no contract, is never used and claims nothing |
| On member trees of the contract's argument domains it answers | `Evaluation.Total`, syntactic |
| Its answers are member trees of the contract's result domain | `Evaluation.Closed`, syntactic |

In the Nat and Bool registry, `less` and `equal` have contracts and
evaluations for `natOrd`, `natDesc`, and `boolOrd`: each reads its arguments
as constructor terms (`succ(…(zero))`, `boolTrue()`, `boolFalse()`), computes
with Lean's `Nat` and `Bool`, and answers a Bool constructor term. `compare`
has no contract, since its orderings lie in no declared domain, and so no
evaluation.

## The KB with the evaluated equations

The evaluated equations `call = value` are a sound equation oracle
(`Snapshot.oracle`): unconditional, each an evaluation. The KB they extend
keeps its models (`models_evaluated`). An S08 snapshot now lists registered
evaluators beside its clauses (`P1.Snapshot.evaluators`), and its KB is the
clauses and the evaluated equations (`P1.Snapshot.kb`): exactly the oracle's
extension (`checkSnapshot_kb`). So:

- an evaluation is derived by the clause rule on its evaluated equation
  (`P1.Snapshot.evaluated_derives`); no evaluator callback is trusted beyond
  its registration in the KB;
- NAF evidence for such a snapshot is evidence for that exact KB: a
  `NafCheck`'s soundness is indexed by `snapshot.kb`, the oracle's extension.
  Evidence for the clauses alone does not transfer to it;
- a snapshot with no evaluator is its clause list (`kb_of_evaluators`). A
  checker with an evaluator is not the input's own (`ownChecker`).

## The decision

The route decides the equation `call = result` (`Snapshot.decision`, a P1
`DecisionContract`), for an interpretation the answers are about:

| Part | Content |
| --- | --- |
| Problem | `call` and `result` have the same value under every environment |
| No | They differ under every environment |
| Conditions (`Snapshot.Decides`) | The call has a target; its arguments are member trees of the contract's argument domains; `result` is a member tree of its result domain |
| Decision (`Snapshot.decide`) | The evaluator's value is `result` |
| Termination | A Lean function: the evaluator and a syntactic comparison |
| Soundness | Yes by `Evaluation.Sound` (`decide_sound`), also as `Derives` in the KB with the evaluated equations (`decide_derives`); No by separation (`decide_refutes`) |
| Completeness | An admitted call is always evaluated (`evaluate_total`), so every admitted equation gets Yes or No |

The interpretations the answers are about (`Snapshot.Models`) realize the
snapshot, with checked registrations (S13) and evaluations, and separate the
members of each contract's result domain (`Snapshot.Separated`: distinct member
trees denote distinct values). Separation is what makes `less(natOrd, 2, 3) =
false` false: a model identifying `true` and `false` would make it true. Only
result domains are asked, so a domain no contract returns never empties the
class. The order model is one of them (`OrderEvaluation.models`).
`Snapshot.admits?` decides the conditions from the listed rules: the call's
target admits the result (`Target.admits`) when the arguments and the result
read as member trees of the contract's domains (`memberOf?`, which tries every
listed rule of the domain with the term's symbol). The check is sound
(`admits?_decides`), and complete when every rule of the signature is listed
(`admits?_complete`, by `memberOf?_complete`).

The route decides as run (`Snapshot.check?`): an equation `admits?` admits,
the evaluator's value read as a member tree of the result domain, then whether
it is the result. Every condition is checked there, so its Yes needs only the
evaluations' soundness (`check?_true`) and its No only soundness and
separation (`check?_false`), not `Snapshot.Complete`. An evaluator that does
not answer, or answers outside the result domain, leaves the equation to a run,
never to No. Where it answers, it is the contract's decision (`check?_decide`).
With `Snapshot.Complete` and every rule of the signature listed it answers
every equation the contract decides (`check?_complete`).

An operation with no contract, no evaluation, or arguments outside its
domains is not admitted: nothing is decided, and nothing is refuted. Bool
arguments to the Nat order are not evaluated, and `less(natOrd, true, 3) =
false` is Undecided, not No.

## On the machine

### Evaluation where the value is demanded

An equation goal demands the value of a dictionary call on one of its sides.
`Strategy.withEvaluation` answers it before any other strategy:

| Goal, as read | Candidates |
| --- | --- |
| `call = r`, the call ground and evaluated to a ground value | The goal matched against `call = value` (`Expansion.evaluation`): `r` a flexible name is bound to the value, an identical term closes, a different constructor term is a miss; then the goal's exact candidates |
| `r = call`, only the right side evaluated | `equalSymm`, then `call = r` (`Expansion.orient`); then the exact candidates |
| Any other | The inner strategy's |

The exact candidates are an assumption the goal reads as, ex falso, and exact
steps from local rules: an evaluator never hides a proof the context gives. The
evaluation node is a derived rule with the call and the value as parameters
and no premise. A goal whose call is evaluated has no other candidate: no law
is fired for it. The strategy is sound in every KB containing the evaluated
equations (`withEvaluation_sound`).

### Laws matched structurally

The S05 matcher compares two different dictionary calls as `unsupported`:
different calls may have the same value, so a mismatch beneath a call would be
no refutation. A law's view is therefore matched one way (`lawInstance?`): its
binders are read off the goal, as read, by a structural match of its
conclusion against the goal's call with the same path and field (`extract`),
the dictionary and the arguments as first-order terms; a binder the conclusion
does not mention gets a fresh flexible witness, bound by the premises; the
instance must be identical to the goal. No higher-order unification is
involved, and no name of the goal is assigned. `Strategy.withLaws` offers these
candidates for an equation goal with the call on the left, before the inner
strategy's (`Response.prepend`, which passes a delay, an open atom, or a NAF
evaluation on unchanged), with S20's use-site checks (`Store.lemmaSite`, a gap
where the use site may still change, a gap where the lemma applies but does
not hold). A goal with the call on the right only is turned around, after its
exact candidates. It is sound where the lemmas are (`withLaws_sound`).

## Laws as checked lemmas

A law `∀d. I(d) → body` is a statement, valid by `law_valid`. It is not a
clause of the executable program and adds no inference rule.

- **In the proof layer.** The law's formula is a fact of the checker's KB
  (`Law.clause`, a compound head with no body), true in every realizing
  interpretation with checked registrations (`models_lawClauses`). The
  program never selects it.
- **Its views.** A law compiles into conditional views (`Law.views`): its
  binders, the dictionary's first; its premises in order, the interface guard
  first; a conclusion; one view per conjunct of a conjunctive body. Asymmetry
  has one, read as a conditional rule:

  ```text
  less(d,y,x) = false :- OrdDictionary(d), DomainMember(d,x), DomainMember(d,y), less(d,x,y) = true
  ```

  stated `∀d x y. (OrdDictionary(d) ∧ DomainMember(d,x) ∧ DomainMember(d,y) ∧
  less(d,x,y) = true ∧ true) → less(d,y,x) = false`. A symmetric law has two
  views, one per direction, each a separate lemma.
- **Their proofs.** A view's proof (`View.proof`) introduces its binders at
  themselves, assumes its premises, and replays the law: the law's clause,
  universal eliminations at the binders, implication eliminations against the
  assumed premises, conjunct projections, all shared S08 rules. Compilation
  keeps the law's own proof and reconstructs each use by instantiation and
  implication elimination. The proof is checked by the run's checker like any
  lemma (`lemmasFor`).
- **Use.** For the goal `less(myOrd, b, a) = false`, the asymmetry view
  matches with `d := myOrd`, `y := b`, `x := a`. Its premise is the one
  obligation of `lemmaRule`, its conjuncts proved in order:
  `OrdDictionary(myOrd)`, both `DomainMember` guards, and
  `less(myOrd, a, b) = true`. The goal closes once they all succeed. A failed
  candidate is rolled back; a dictionary that is a flexible name tries each
  `OrdDictionary` fact in turn.

## Answers

`Route` fixes a registry snapshot with its evaluations, the KB's own clauses,
the lemmas, and the vocabulary. Its program is the KB's clauses and the
generated clauses (the signature's, then `I(n)` and `DomainMember(n, X) :-
D(X)` per registration); its checker's KB is the program, the laws' facts, and
the evaluated equations, with the evaluation rule and no NAF; its strategy is
evaluation, then laws, then the left strategy with the lemmas
(`Route.strategy`, sound for the checker's KB: `strategy_sound`).

| Query | Answer (`Route.answer`) |
| --- | --- |
| An equation the run-time decision covers (`Snapshot.check?`), the call on the left or, failing that, on the right | The decision: Yes, the evaluation node, turned around by `equalSymm` when the call is on the right, with no run; No once a run under the context does not prove the goal |
| A run that succeeds, its export accepted by the checker | Yes, the checked proof term |
| A run interrupted by its fuel | Undecided: termination |
| A run with gaps | Undecided, per gap at an equation on a dictionary operation: the access S13 blocks, alone; for a declared access, a missing evaluator (`dictionary evaluator`) or a call outside its contract (`dictionary domain`), then each law with a view that may conclude it and is not offered (`lemma law`); otherwise the gap's own blocker. A gap keeps its goal as written, so a dictionary written as a name the run may have bound is classified by its laws only. What a call lacks is named once, at the first place a run reached it |
| An exhausted run | Undecided: a proof |

The decision's No waits for a run because of the context. A context no
interpretation satisfies, such as one assuming the goal itself, makes both Yes
and No true; the route then answers Yes, a term its checker accepts. With an
empty context the run has no candidate for the evaluated goal and is exhausted.

A law may conclude the goal when a view applies the same operation on the
same side, its other side not a different closed term (`Registry.lawsFor`).
No law is named where S13 blocks the access: every view's first premise is the
interface guard, which an unregistered dictionary never meets. A call is
outside its contract (`Route.outside`) when an argument is a member tree of
some domain but not of the contract's at its position, like `true` given to
the Nat order. An argument that reads as no member tree, a name or another
call, may still be a member, and is not outside. A blocker naming a law or
dictionary evidence lacks the same thing wherever the run reached the call, so
it is kept once per formula (`Blocker.once`): one candidate dictionary or
three, the missing law is named once.
The route never answers Unknown. Its answers are about the interpretations of
`Snapshot.Models` satisfying the KB's own clauses (`Route.meaning`); every
answer means what it says (`answer_sound`), and every Yes is a term the route's
checker accepts (`answer_accepted`). With `Snapshot.Complete` and every rule of
the signature listed, every equation the decision contract decides, the call on
either side, is answered Yes or No (`answer_definite`).

## Guarantees

| Property | Theorem |
| --- | --- |
| An evaluated call has the evaluation's value; its value is a member tree of the result domain | `Snapshot.evaluate_sound`, `Snapshot.evaluate_member` |
| An admitted call with member-tree arguments is evaluated | `Snapshot.evaluate_total` |
| The evaluated equations are a sound oracle, and its extension is the S08 snapshot's KB | `Snapshot.oracle`, `checkSnapshot_kb`, `models_evaluated` |
| An evaluation is derived by the clause rule in every KB listing the evaluator | `P1.Snapshot.evaluated_derives`, `decide_derives` |
| The decision is a P1 decision contract: Yes true, No false, every admitted equation decided | `Snapshot.decision`, `decide_sound`, `separates`, `decide_refutes` |
| The admission check of the decision is sound, and complete when the signature's rules are listed; listed rules read every member tree | `admits?_decides`, `admits?_complete`, `memberOf?_complete` |
| The decision as run needs no completeness evidence; where it answers it is the contract's decision; with that evidence it answers every equation the contract decides | `check?_true`, `check?_false`, `check?_decide`, `check?_complete` |
| Evaluation on value demand is sound in every KB with the evaluated equations | `Strategy.withEvaluation_sound` |
| Structurally matched laws are sound where the lemmas are | `lawAttempt_sound`, `Strategy.withLaws_sound` |
| An exported evaluation node is checked by re-running the snapshot's evaluators | `evaluationRule`, `Unfold.evaluation_proves`, `exportNode_evaluation` |
| The laws' facts are true where the registry is realized and checked | `models_lawClauses` |
| The route's strategy is sound for its checker's KB; every answer means what it says; every equation the contract decides is answered Yes or No; every Yes is accepted by the route's checker | `Route.strategy_sound`, `Route.answer_sound`, `Route.answer_definite`, `Route.answer_accepted` |
| The Nat and Bool evaluators are sound, total, closed in Bool; the order model separates its members | `OrderEvaluation.evaluated`, `complete`, `separated`, `models` |

## Traces

| Trace | Result |
| --- | --- |
| `less(natOrd, 2, 3)`, `less(natOrd, 9, 2)`, `less(natDesc, 2, 3)`, `less(boolOrd, false, true)` | `true`, `false`, `false`, `true` |
| `equal` under `weakOrd.eqModel` (nested path) at Nat and Bool | Evaluated |
| `less(natOrd, 2, 3) = true`, `= false`; `equal(natOrd, 4, 5) = false`; `less(natDesc, 2, 3) = true` | Yes, No, Yes, No, by the decision; the Yes node accepted by S08 |
| `false = less(natOrd, 3, 2)`, `true = less(natOrd, 3, 2)` | Yes, No: the call on the right |
| An evaluation not answering `less(natOrd, 0, 0)`; the same at `0, 1` | Undecided, never No; No |
| Two contracts for `less`, at three and two arguments; an evaluation for three listed before `natLess` | The call with two finds the second; it runs `natLess` |
| `less(natOrd, 2, 3) = false`, decided as run | The contract's decision |
| `less(natOrd, 2, 3) = false` under itself; under `isNat(a)` | Yes by the assumption, accepted; No |
| `less(natOrd, 2, 3) = c`, `c` rigid, under itself; under `false` | Yes by the assumption; Yes by ex falso |
| `less(natOrd, 2, 3) = R`; `true = less(natOrd, 2, 3)`; `less(natOrd, 3, 2) = true` in a run | `R := true`, accepted; `equalSymm` then the evaluation, accepted; exhausted, never No |
| `OrdDictionary(D) ∧ less(D, 3, 2) = true` | natOrd rolled back, `D := natDesc`, accepted |
| The export without the evaluation rule; an evaluation node with a wrong value | Needs evidence (`rule evaluation`); rejected |
| Unmet guards: `less(natOrd, true, 3)`, `less(boolOrd, 2, 3)`; `less(natOrd, 2, 3) = 2`; `DomainMember(natOrd, true)`, `DomainMember(natOrd, 2)` | Not evaluated, Undecided; not admitted; exhausted, success |
| `less(natOrd, true, 3) = false`; `less(natOrd, a, 3) = false`, `a` rigid | Undecided: `dictionary domain` and `lemma asymmetric`; `lemma asymmetric` only |
| An evaluation answering `less(natOrd, true, 3)` with `false`, goal `less(natOrd, true, 3) = true` | Not admitted, so not decided: Undecided, never No |
| Missing evaluator: `compare(natOrd, 2, 3) = lt`; an evaluation for another version; the unknown `aliasOrd` | Undecided: `dictionary evaluator` and `lemma lessCompare`; `dictionary evaluator` and `lemma lessCompare`; `dictionary unknown` only |
| Asymmetry's view; the views of `lessCompare` | Binders `d, x, y`, four premises; two views; all checked |
| `less(natOrd, b, a) = false` under `isNat(a)`, `isNat(b)`, `less(natOrd, a, b) = true` | One `lemmaRule` at `natOrd, a, b`, the guards and the premise proved in order, accepted, Yes; without the lemma Undecided, `lemma asymmetric` |
| `false = less(natOrd, b, a)` under the same context | Turned around, then the same law: Yes; without the lemma, `lemma asymmetric` |
| `∃D. OrdDictionary(D) ∧ less(D, b, a) = false`, no lemma | `lemma asymmetric` once for the three candidate dictionaries, never a missing binding |
| Only `less = true :- compare = lt` offered, goal `compare(natOrd, 2, 3) = lt` | `dictionary evaluator` and `lemma lessCompare`: the direction concluding it is missing |
| A view `∀d x y z. (less(d,x,y) = true ∧ less(d,y,z) = true) → less(d,x,z) = true` at `less(natOrd, a, e) = true` | `y` at a fresh flexible witness |
| `less(natOrd, true, a) = false` | The guard `DomainMember(natOrd, true)` fails: Undecided, `dictionary domain` |
| `less(D, b, a) = false` under `less(natDesc, a, b) = true` | natOrd rolled back, `D := natDesc`, accepted |
| `compare(natOrd, 2, 3) = lt` with `compare(d,x,y) = lt :- …, less(d,x,y) = true` | The law, its premise evaluated; accepted |
| Both views of `lessCompare`, goal `less(natOrd, a, b) = true` | Interrupted by the fuel: Undecided, termination; never Yes |

## Boundaries

- **Composition.** The fast fragment still reports dictionary calls as
  blockers (`dictionaryLaw`, S23). Under the [decision IR](decision-ir.md)
  (2026-11-17), a call with a registered evaluator becomes a primitive literal
  of the IR, admitted by S13's access check and this route's contracts (S29);
  running the access check and the decision at every call site is S15's.
- **Value demand is an equation side.** A call inside an atom's arguments, or
  inside another call, is not evaluated (it would need `equalSubst` at the
  call's position), and an equation between two calls is a gap. A call whose
  arguments are not yet bound is not evaluated and does not wait.
- **No NAF in the route.** Its checker has no NAF check. Composing NAF with
  evaluators keeps the evidence indexed by the KB with the evaluated
  equations, as the snapshot fixes it.
- **Export of whole runs is not proved here.** As for S09 and S20, each
  construction is valid given valid premise trees; the route checks each
  run's export before answering Yes. The theorem that every successful run
  exports an accepted tree is S15/S16's.
- **Law diagnosis over-approximates.** `lawsFor` names laws by the operation
  and the other side's shape; it routes the blocker and decides nothing. It
  does not check a view's guards at the goal: beside `dictionary domain` it
  may name a law whose domain guard the call cannot meet.
- **Views conclude with the call on the left**, as the registry's laws do; a
  goal is turned around to meet them. A view with the call on the right is not
  matched.
- **Premises with fresh witnesses inside a call.** A binder only the premises
  mention gets a fresh flexible witness, but the S05 matcher does not compare
  two calls, so a premise such as `less(d, a, Y) = true` with `Y` unbound
  cannot meet an assumption `less(d, a, b) = true`: a gap, never a miss.
- **Symmetric laws loop.** Offering both directions of a symmetric law lets
  backchaining cycle; the run is interrupted. Nothing orients or rewrites.
- **Proofs are checked as written.** A view's proof introduces its binders at
  their own names; a use site whose context names one of them does not check
  it (S20).
