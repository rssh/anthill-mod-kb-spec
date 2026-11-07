# Answers: Yes, No, Unknown, and Undecided (S22)

The KB module either computes an answer or stops and says what it cannot
compute. S22 gives it four answers and keeps two unknowns apart:

- **Unknown** is logical: the KB leaves the goal open, because it depends on
  an open predicate (`p(x̄) :- UNKNOWN`, [S10](machine-negation.md)). It is a
  decided answer about the KB, the same for every correct engine, and it is
  sound: the goal holds in one model of the completion and fails in another.
- **Undecided(blockers)** is the module's own: it did not decide the goal.
  Each blocker gives its site, path, and formula, and what is missing. It
  says nothing about the KB.
- **Operational outcomes** (fuel, an exhausted or interrupted search,
  floundering, an unsupported formula) are never Unknown. They give
  Undecided.

Traces are in [Tests/Resolution/Answer.lean](../Tests/Resolution/Answer.lean),
with the P0 and S12 answers in
[Tests/Resolution/P0/Admission.lean](../Tests/Resolution/P0/Admission.lean) and
[Tests/Resolution/P3/Induction.lean](../Tests/Resolution/P3/Induction.lean).

| Module | Contents |
| --- | --- |
| [Machine/State](../AnthillModKbSpec/Resolution/Machine/State.lean) | `Response.opened`, `GapReason.opened`, the outcomes `opened` and `abandoned` (formerly `unknown`); each gap's provenance (`Origin`, `trailOf`) |
| [Machine/OpenAtoms](../AnthillModKbSpec/Resolution/Machine/OpenAtoms.lean) | Open atoms by syntax: `openAtomsOf` through the clauses, `mayMatch` with the declared free constructors |
| [P1/Negation](../AnthillModKbSpec/Resolution/P1/Negation.lean) | The open check in evidence-first NAF (`Strategy.withRefutation opens`), open goals (`Strategy.withOpenGoals`), `nafByRefutation` with a marker |
| [Answer](../AnthillModKbSpec/Resolution/Answer.lean) | `Answer`, `Blocker`, `Missing`, `Meaning`, `Answer.Sound`, the combination rule (`Answer.combine`), supplying evidence; the P0 answer (`Admission.answer`, `Plan.decision`) |
| [Models/KeyModel](../AnthillModKbSpec/Models/KeyModel.lean) | The constructor-key model: values are constructor trees and truth values, so the free equality theory holds |
| [P0/Open](../AnthillModKbSpec/Resolution/P0/Open.lean) | Witnesses for ground programs: the check (`Open.check`), the model of a checked witness (`Open.check_model`), the exact guard truth and the realization of a separated admission signature (`guardTruth`, `Separated`, `realizes_guards`) |
| [P1/Answer](../AnthillModKbSpec/Resolution/P1/Answer.lean) | The module's answer over the completion (`Setup.answer`) and its soundness (`Setup.answer_sound`) |
| [P3/Answer](../AnthillModKbSpec/Resolution/P3/Answer.lean) | The induction path's answer: S12's needs as blockers (`Induction.answer`) |

## The answers

| Answer | Evidence | Meaning |
| --- | --- | --- |
| **Yes** | A proof: a `Derives` tree, exportable as an S08 term | The goal holds in every model of the KB, with the tracked NAF provider |
| **No** | A failure certificate, or a refutation in the completion | The goal fails in every model of the completion |
| **Unknown** | Two witnesses: assignments of the open atoms reached | A model of the completion, realizing the signature, in which the goal holds, and one in which it fails |
| **Undecided** | Blockers: place, path, formula, and what is missing | Nothing |

`Answer` is generic in its evidence: each route chooses what its answers
carry and what they mean (`Meaning`, three propositions: truth, falsity,
independence). `Answer.Sound` states that an answer means what it says.
`Meaning.ofModels` builds a meaning from a class of models, a context, and a
goal. Its independence excludes both truth and falsity once some model
satisfies the context (`Meaning.ofModels_independent`).

A blocker sits at a place (`Place`): an admission site with a term path,
before anything runs, or an obligation a run reached. A reached obligation
keeps its context and its provenance (`Origin`): the frames from the root
down, each with its rule, the clause it selected if it is a clause node, and
the premise position; a NAF whose operand was searched is a step too. Its path
is the premise positions along that trail. So two blockers with the same
formula in different clauses, or under different assumptions, stay apart. The
machine records the provenance with each gap (`trailOf`); a goal still delayed
when its branch ends was suspended away from its frames and has none.

A blocker lacks one of these (`Missing`):

| Missing | Examples |
| --- | --- |
| `proof` | A guarded universal over an infinite domain, a goal implication, a goal no search proved or refuted |
| `mode` | A name that must be bound before the formula runs (a P0 ground instance); a goal still waiting at the end of its branch (floundering) |
| `termination` | A dependency cycle; a run interrupted by its fuel |
| `construct` | A construct the route has no route for: a P0 capability, NAF in an induction case, an unsupported focus, a contract breach |
| `witnesses` | Open atoms whose two witnesses were not both found |

Supplying checked evidence for a blocker turns Undecided into Yes or No
(`Answer.supplyProof`, `Answer.supplyRefutation`): a proof term, a lemma, or a
failure certificate. The supplied check's soundness carries over
(`supplyProof_sound`).

## Combining results

`Answer.combine` combines two results for the same goal:

1. A definite Yes or No wins, the first when both are definite
   (`combine_definite`, `combine_definite_right`).
2. Otherwise a remaining blocker gives Undecided with all the blockers,
   since evidence for it could still give Yes, No, or Unknown
   (`combine_undecided`).
3. Unknown only when no blocker remains (`combine_unknown`), so Unknown is a
   statement about the KB alone.

Undecided with no blocker is no result: it is the unit of the combination
(`combine_none_left`, `combine_none_right`), and `combineAll` of no results.
Combining keeps soundness (`combine_sound`, `combineAll_sound`).

## Open atoms

The open atoms are the marker atoms. In the completion, the case that
`p(x̄) :- UNKNOWN` adds to `p` makes every atom of `p` it covers hold exactly
when the marker atom holds. A nullary marker ties all of these atoms to one
proposition. A marker with arguments, `p(x̄) :- UNKNOWN(x̄)`, keeps each atom
apart. The KB generator chooses which form to emit; it is never inferred.

The open case is marked syntactically, so no search finds it
(`Completion.openAtomsOf`). A formula reaches the marker atoms among its own
atoms in goal positions and, for any other atom, those its covering clauses
reach, wherever their bodies mention them, through any number of
predicates. A clause covers an atom when its head may match it
(`mayMatch`): no literal clash, and no clash of declared free constructors,
separates them. A defined operation may equal any value, and a name matches
anything. Head arguments are matched independently, so the result may
over-approximate: it routes the search, and never decides an answer.

The machine records an obligation that reaches an open atom as `opened`, not
as a gap:

- A NAF goal whose operand reaches an open atom, a marker atom included, is
  reported `opened` once it is stable (its names rigid, or its branch
  closing), and no refutation is searched for it at first
  (`Strategy.withRefutation opens`). Evidence first and delay first still
  come before it.
- A goal that reads as a marker atom is reported `opened`
  (`Strategy.withOpenGoals`).

`Response.opened` records the obligation with `GapReason.opened`. That entry
blocks exhaustion and NAF barriers, like a gap, but the outcome reports it
apart: a run with no alternative left is `exhausted` with no entry, `opened`
when every entry is an open atom, and otherwise `abandoned`. Floundering,
unsupported formulas, lambda-valued answers, and contract breaches stay gaps;
running out of fuel stays `interrupted`. `abandoned` was called `unknown`
before S22, a name now kept for the logical answer only.

## Witnesses

A witness is a finite assignment of the open atoms reached: the marker atoms
it lists are true, and every other marker atom is false, its canonical
extension. `Open.check` checks one for a goal and an expected value:

- the program is covered: ground definite clauses with an atomic head that
  is no marker atom and P0 bodies, and denials with P0 bodies; no atom of
  the program, the assignment, or the goal is of a guard symbol;
- the witness program, the definite clauses with the true marker atoms as
  facts, is ranked;
- every denial body evaluates false, and the goal evaluates to the expected
  value, by the ranked P0 evaluator. The goal may also use disjunction and
  implication.

A checked witness has a model (`Open.check_model`). It is the
constructor-key model in which a guard atom holds by the admission
signature's exact guard truth (`guardTruth`: a domain's members, every
domain's for `D_all`, the registered references for `P_n`), and any other
atom exactly when the witness program gives it a success certificate. Under
the rank, a P0 goal with no guard atom holds exactly when it succeeds
(`Open.goal_iff`). The model satisfies every clause of the completed program,
for any signature that closes no marker, not `ho_apply`, and no guard
predicate:

- the KB's clauses, through success certificates;
- its denials, by the check;
- every only-if clause, since a success certificate names a defining clause
  whose head equations hold for the keys;
- the clash and injectivity clauses, since equality is identity of
  constructor trees.

NAF is complement. When each guard symbol has one role and none is
`ho_apply` (`Separated`), the exact guard truth realizes the admission
signature (`realizes_guards`): both witnesses are models realizing it. The
candidates assign every open atom the goal reaches,
whether or not a run visited it. For a goal whose open atoms occur only
positively, the all-true and all-false assignments are the witnesses.

## The module's answer

`Setup.answer` answers a query against a completed program (`Setup`: the
clauses, a signature that closes no marker and not `ho_apply`, the admission
signature with a decision of its guard symbols and the proof that they are
separated, and the run bounds; `Setup.ofComplete?` builds one from a program
`complete?` accepts):

1. **The fast run**: the left strategy with evidence-first NAF and the open
   marker. A success, exported and checked against the completed snapshot,
   is Yes.
2. **Witnesses**: after a run that ended `opened`, for a query with no
   assumptions, the module tries these candidate assignments of the open atoms
   the goal reaches: all true, all false, each one alone true, each one alone
   false. The program's class is checked once and each candidate evaluated
   once. Two that check with opposite values are Unknown, and nothing else
   runs.
3. **The full run**: otherwise, after a run that met an open atom, alone or
   beside other gaps, the same run without the marker, in which every stable
   NAF is refuted. A denial may force an open atom, and an operand that
   reaches one may still be refuted through another of its atoms. A checked
   success is Yes.
4. **Refutation**: a checked refutation of the goal in the completion,
   within the query's fuel, is No.
5. Otherwise Undecided, with the fast run's blockers.

The setup builds the completion once, the one `complete?` accepted
(`complete?_ok`). All answers are about the models of the completion with
complement NAF that realize the admission signature (`Setup.meaning`), and
`Setup.answer_sound` proves each sound. Yes follows from
`refutationChecker_sound`, No from positive soundness of the refutation, and
Unknown from `Open.check_model` and `realizes_guards`. A witness is checked
only when the completion closes no guard predicate. `Setup.answer_unknown`
proves that Unknown comes only from a fast run that ended `opened`, recording
no gap.

## P0 and the induction path

- **P0** (`Admission.answer`): admission's requests are Undecided blockers at
  their sites and paths, reported before anything runs
  (`answer_needsEvidence`). P0 reads a marker as an atom without clauses, so
  every formula of the input that mentions a marker atom (the goal, an
  assumption, a clause's body goal) is a blocker too, the construct
  `openPredicate`, and P0 decides no such input (`answer_marked`). A Ready plan is decided with no fuel
  (`Plan.decision`): Yes with the run's proof, or No with the root's
  complete-failure certificate (`Plan.decision_spec`). It is never Undecided
  or Unknown (`Plan.decision_decided`), the P1 contract, and it is sound for
  the plan's completion (`Plan.decision_sound`).
- **Induction** (`Induction.answer`): S12's needs are blockers before
  anything runs, the case gaps at their sites and paths, a missing
  registration naming the predicate (`answer_needsEvidence`). A Ready plan's
  success is Yes (`answer_yes`, then `Plan.sound`). An interrupted run is
  Undecided lacking a termination argument, an abandoned one Undecided with
  its gaps; the route never answers No or Unknown (`answer_decided`).

## Guarantees

| Property | Theorem |
| --- | --- |
| Combining keeps soundness; a definite answer wins; Undecided when a blocker remains; Unknown only when none does; no result is the unit | `Answer.combine_sound`, `combine_definite`, `combine_definite_right`, `combine_undecided`, `combine_unknown`, `combine_none_left`, `combine_none_right`, `combineAll_sound` |
| Supplied evidence that checks gives Yes or No, soundly | `supplyProof_yes`, `supplyRefutation_no`, `supplyProof_sound`, `supplyRefutation_sound` |
| Unknown excludes Yes and No | `Meaning.ofModels_independent` |
| A checked witness has a model of the completion with complement NAF in which the goal has the expected value; it realizes a separated admission signature | `Open.check_model`, `Open.goal_iff`, `Open.value_sound`, `Open.realizes_guards`, `Setup.check_model` |
| The module's answers are sound over the completion | `Setup.answer_sound`, `checks_sound`, `refuted_sound`, `witnesses_sound` |
| Unknown never comes from an operational outcome | `Setup.answer_unknown` |
| Reporting open atoms keeps soundness | `Strategy.withOpenGoals_sound`, `Strategy.withRefutation_sound`, `nafByRefutation_sound` |
| P0's requests are blockers before anything runs; it decides no input that mentions a marker; a Ready plan answers Yes or No, soundly | `Admission.answer_needsEvidence`, `Admission.answer_marked`, `Plan.decision_decided`, `Plan.decision_spec`, `Plan.decision_sound`, `Admission.answer_sound` |
| S12's needs are blockers before anything runs; its Yes is a successful run | `Induction.answer_needsEvidence`, `Induction.answer_yes`, `Induction.answer_decided` |

## Traces

| Trace | Result |
| --- | --- |
| `q(a) :- unknown`, `naf q(a)` | The fast run is `opened`, with no refutation. Unknown: `unknown` false makes it true, `unknown` true false |
| The same, goal `q(a)` | Unknown, the witnesses swapped |
| `q(a) :- unknown(a)`: `naf q(b)`; `naf q(a)` | Yes, by the clash of `b` and `a`; Unknown |
| `q :- unknown(a), unknown(b)`, goal `q`; `unknown(a) ∧ unknown(b)` | Unknown: both open atoms assigned, though the run stopped at the first |
| `naf unknown`; `q(a) :- naf unknown`, goal `q(a)` | Unknown; Unknown |
| `q :- r`, `r :- unknown`, `naf q` | Opened through `r`; Unknown |
| `p(b) :- unknown`, `naf p(o(a))`, `o` no declared constructor | Opened: `o(a)` may equal `b` |
| `q(a) :- unknown, r(a)`, `p(a)`, goal `(∀x. naf p(x)) ∨ naf q(a)` | The fast run is abandoned, an open atom beside a gap; the full run refutes `q(a)` through `r(a)`: Yes |
| `q(X, X) :- unknown`, `naf q(a, b)` | Opened by the independent match; the full run refutes it: Yes |
| `p(a) :- unknown`, `p(a) ∨ naf p(a)` | Undecided, naming `unknown`: no witness makes it false |
| `q(X) :- unknown`, `naf q(a)` | Undecided, naming `unknown`: a non-ground program is outside the witness check |
| `q(a) :- unknown` and the denial `false :- q(a)`: `naf q(a)`; `q(a)` | Yes; No: the denial forces `unknown` false, and the witness making `q(a)` true does not check |
| `o(a) :- unknown`, `o(a) ∧ r(b)`, no `r` clauses | No, by the refutation of `r(b)` |
| `p(a)`: `p(a)`; `p(b)`; `naf p(b)` | Yes; No; Yes |
| `p(a)` with fuel 1 | Undecided, lacking a termination argument |
| `∀x. p(x)` with `p(q(X)) :- p(X)` | Undecided |
| A clause concluding the marker | Invalid, no answer |
| `∀x:Nat. reachable(x)` in P0 | Undecided before anything runs, its first blocker the goal lacking a proof; Yes once the exported induction proof is supplied and checked; a tampered proof stays Undecided |
| The same on the induction path; without the principle; with fuel 3; `∀x:List. defined(x)` | Yes; Undecided, lacking a proof; Undecided, lacking a termination argument; Undecided |
| NAF in a clause an induction case selects | Undecided before anything runs: the construct `negation` at the clause body's site |
| P0: a Ready success, a complete failure, NAF; the cycle `p :- p` | Yes; No with a checked failure certificate; Yes; Undecided, lacking a termination argument at the clause's head |
| P0 with the marker `q`: `p :- q`, goal `naf p`; without the marker | Undecided, the construct `openPredicate` at the clause's body goal; Yes |
| `∀x:Nat. zero(x)`, `zero` not registered | Undecided, the blocker naming `zero` |
| `naf q(5)` with `q(X) :- unknown` in S10's traces; without the marker | `opened`; `abandoned` |
| `q(a) :- unknown`, goal `naf q(a) ∧ naf isUnit(a)` with `isUnit` a guard | Undecided: a goal mentioning a guard symbol is outside the witness check |
| `q :- r, ∀x. naf p(x)` with `p(a)` and `r` | Undecided; the blocker names the clause and the premise position along its trail |
| `r → ∀x. naf p(x)` with `p(a)`: without `r`; with the fact `r` | Yes, the completion refuting `r`; Undecided, the blocker's context holding `r` and its trail the implication's introduction |
| A fuel interruption | Undecided at the query's context, lacking a termination argument |
| The combination rule on numbers | Yes beside No is Yes; Unknown beside Undecided is Undecided; two Undecided join their blockers; two Unknown keep the first; Unknown beside no result stays Unknown |

## Boundaries

- **Witnesses for ground acyclic programs.** The witness check covers ground
  programs with P0 bodies, markers, and denials, and queries with no
  assumptions. A non-ground or cyclic program, or a query with assumptions,
  gives Undecided naming the open atoms. Tabled evaluation (S24) extends the
  witnesses to its fragment.
- **Guards in witness programs.** A witness program and its goal mention no
  guard symbol, and the completion closes none: a guard atom would need its
  exact truth decided inside the witness program. The admission signature's
  guard symbols must have one role each (`Separated`): a naming that shares
  a symbol between roles, such as `D_all` and the only domain's membership,
  gets no witness. S24 extends the witnesses.
- **Candidates, not search.** The module tries all-true, all-false, and
  single-atom assignments. Open atoms that interact can need another
  assignment; then the answer is Undecided, never a wrong Unknown.
- **Open atoms by syntax.** `openAtomsOf` follows atomic clause heads, not
  `ho_apply` heads or goals, and may over-approximate. An over-approximated
  NAF is refuted by the full run; one it misses is refuted as before, and an
  unrefuted one stays a gap.
- **Barriers.** An open atom inside a `negate` barrier's operand abandons the
  barrier as a gap. S10's NAF uses no barrier.
- **P0 reads markers closed.** P0 reads `UNKNOWN` as an atom without
  clauses, so it reports every formula mentioning a marker atom as a blocker
  and leaves the input to the completion route (`Setup.answer`). Choosing
  the route for an input is S15's composition of the profiles.
