# `ho_apply` conversion and whole-formula head matching

S11 admits `ho_apply` conversion on the shared machine and adds selection of a
clause by its whole head, the path an induction principle takes. It builds on
the [S05 matcher](machine-matching.md), the [S06 positive strategy](machine-positive.md),
the [S09 left strategy](machine-left.md), and the [S08 checker](proof-checking.md).
A direct call `p(args)` and the indirect call `ho_apply(p, args)` are
interderivable (`Derives.hoApplyIntro`, `Derives.hoApplyElim`). The machine uses
this as a proof step, never as a goal rewrite, and the S05 matcher is
unchanged. Traces are in [Tests/Resolution/Conversion.lean](../Tests/Resolution/Conversion.lean).

| Module | Contents |
| --- | --- |
| [Machine/Conversion](../AnthillModKbSpec/Resolution/Machine/Conversion.lean) | Indirect views (`Indirect`, `Term.indirect?`, `Converts`), concrete indirect calls (`Term.call?`), conversion in `Derives` (`Derives.ofIndirect`, `Derives.toIndirect`), the static classification (`Comparison`, `compareAtom`, `compare`, `compareAtom_lambda`), `ho_goal` (`Expansion.hoGoal`), a conclusion's candidate, direct or converted (`Expansion.convert`, `conclusionAttempt`), and their contracts |
| [Machine/Evidence](../AnthillModKbSpec/Resolution/Machine/Evidence.lean) | The machine rule `RuleApp.converted conclusion inner` |
| [Machine/Positive](../AnthillModKbSpec/Resolution/Machine/Positive.lean) | Conversion in identity, local rules, and clause selection (`clauseUse`); `ho_goal` in `atomResponse`; `atomResponse_indirect`; `Program.predicateGuard_derives` |
| [Machine/LeftStrategy](../AnthillModKbSpec/Resolution/Machine/LeftStrategy.lean) | The whole-formula choice `Choice.headMatch`; conversion for a projected conjunct (`headProject`) |
| [P1/Derived](../AnthillModKbSpec/Resolution/P1/Derived.lean), [P1/Export](../AnthillModKbSpec/Resolution/P1/Export.lean) | The conversion's S08 nodes (`Unfold.convert`, `Unfold.convert_proves`), the export of converted nodes (`exportNode_converted_proves`) |
| [ProofLayer](../AnthillModKbSpec/Resolution/ProofLayer.lean) | The S11 commands for P0's `ho_apply` requests (`Request.conversionLayer`) |

## One candidate view

**Indirect views.** `view` is the indirect view of `goal` when the two differ
only in their conclusion, the formula itself or the conclusion of its
implications: a direct call `p(args)` in `goal`, with `p` not `ho_apply`, and
`ho_apply(p, args)` in `view` (`Indirect`). `Term.indirect?` computes it.
`Converts` holds when either formula is the other's view.

**Conversion in the logic.** A proof of the view proves the goal
(`Derives.ofIndirect`), and a proof of the goal proves the view
(`Derives.toIndirect`). At the call these are `hoApplyElim` and
`hoApplyIntro`. Under an implication `A → V`, conversion is a cut on it: `A → G`
by implication introduction, and under `A` the inner `V` by implication
elimination, converted in turn. No weakening is assumed and no
context-indexed evidence moves to another context.

**`ho_goal`.** A goal reading as a concrete indirect call `ho_apply(p, args)`
(`Term.call?`) has the one candidate `Expansion.hoGoal`: the direct goal
`p(args)`, its node `hoApplyIntro`. The direct goal is the canonical form:
it is answered like any other, and a selection (S09) is consulted there, not
at the indirect form, so a chosen command runs once. It is never normalized
again (`atomResponse_indirect`), so the two directions cannot form a rewrite
loop. Direct and indirect calls therefore share their candidates.

**Converted candidates.** A candidate concluding a call by `ho_apply` meets a
direct goal through the goal's indirect view: the S05 matcher compares the
candidate's conclusion with the view. The candidate built for the view is
wrapped as `converted view`: its node proves the view, and the goal follows by
elimination. In the reverse direction, a direct conclusion meets a goal whose
conclusion applies, by `ho_apply`, an assignable name or a reference. The goal
is matched against the conclusion's view, and the node is converted by
introduction. A goal applying a rigid name or a compound term gets no
introduction: nothing assigns or converts it, so a direct candidate is a miss
there. The wrapper
changes no premise, name, or binding (`Expansion.convert`). The commit replays
the match exactly, so `Store.unify_sound` and `Store.commit_unify` hold as in
S05.

| Candidate | Direct goal `p(args)` | Goal `ho_apply(X, args)` with a flexible `X` |
| --- | --- | --- |
| An assumption | An indirect assumption, against the view, converted by elimination | A direct assumption: the goal against its view, `X := q`, converted by introduction |
| A local rule's conclusion (`ruleUse`, `factUse`) | Likewise | Likewise |
| A program clause's head | An indirect head, concrete or flexible, against the view, converted | A direct head: a gap, since it would choose a predicate among the program's clauses |
| An explicitly chosen clause (`headMatch`, `headProject`) | Likewise, for the whole head or the projected conjunct | Matched: the selection chose the clause |

Binding a predicate name is structural reference matching. A flexible clause
name, such as an induction clause's `P`, is bound to the goal's predicate
symbol by the match. A rigid predicate parameter is never assigned: against a
reference it is a mismatch. A flexible goal name `X` is bound by matching local
evidence, or by a clause a selection chose. Choosing it among all program
clauses needs an admitted finite candidate set
([state machine](resolution-state-machine.md), section 9), which no ticket
provides, so that comparison is a gap.

## Static classification

`compareAtom hoApplySymbol binds assignable goal conclusion` reads an atomic
conclusion against an atomic or falsity goal, both as read. `compare` reads
whole formulas through their implications, leaving the premises to the
matcher, so it classifies the goal's conclusion. Formulas of the same kind
(binders included), a conclusion that is a name, and operation calls go to the
matcher as they are; it reports differently named binders and calls as gaps.
Calls are compared by `compareAtom`. `assignable` admits the names the goal
may bind, the store's assignable names, and `binds` those the candidate may
bind:

- clause template names;
- a local rule's leading binders, or assignable names it captures;
- an assumption's assignable names.

| Comparison | When | Machine use |
| --- | --- | --- |
| `direct` | The same head, or for whole formulas the same kind | The S05 matcher, as before |
| `elim` | An indirect conclusion and a direct goal of the matching arity | Against the goal's view, converted by elimination |
| `intro` | A direct conclusion and an indirect goal of the matching arity applying an assignable name or a reference | The goal against the conclusion's view, converted by introduction; a gap for clauses the strategy enumerates |
| `lambda` | Two calls, nothing above holds, and the conclusion applies a name `binds` admits or the goal one `assignable` admits | A gap: only a lambda-valued answer could match |
| `apart` | Otherwise, an indirect goal applying a rigid name or a compound term included | A miss |

`compareAtom_lambda`: whatever the substitution, a `lambda` conclusion and the
goal have no common instance, directly or through either one's indirect view
(`calls_apart`). Structural reference matching has nothing to propose. A higher-order unifier might bind the name to
`λx̄. …`, but `Term` has no lambda and this is not general higher-order
unification. The case is therefore an unsupported gap, never a miss: an arity
mismatch such as `ho_apply(P, x)` against `p(a, b)`, or the goal
`ho_apply(X, a)` against `q(a, b)`. Nested under a local rule's premises, such
a conclusion is the same gap (`mayConclude`). A goal that is no call,
falsity included, is never an instance of an application, and a
lambda-valued formula is not considered for it: `apart`. One flexible head
thus leaves contradiction search exhaustive. A concrete reference of another
arity, or a rigid predicate name, is `apart` too.

## Whole-formula selection

`Choice.headMatch clause` is an explicit choice of the left strategy. The
clause's whole head, compound or not, is compared with the goal by `compare`.
It is matched directly, or against a view with the clause node converted. The
renamed body is the one premise, and the node finishes the goal itself: no
continuation premise assumes the head. S09's `headProject` compares its
projected conjunct the same way.

For the induction principle

```text
(isNat(x) → ho_apply(P, x)) :- isPred1(P), ho_apply(P, zero),
                               ∀n. isNat(n) → (ho_apply(P, n) → ho_apply(P, succ(n)))
```

and the focus `isNat(a) → reachable(a)`, with `a` rigid:

- the view is `isNat(a) → ho_apply(reachable, a)`; matching binds `x := a` and
  `P := reachable`, and assigns no rigid name;
- the premise is the body instance, whose guard `isPred1(reachable)` is kept.
  The generated fact for `reachable` discharges it, a lookup by the reference's
  symbol (`Program.predicateGuard_derives`, by `Elaboration.rangeGuard_derives_predicate`);
- `ho_goal` turns the base `ho_apply(reachable, zero)` into `reachable(zero)`;
- the step keeps its own binder `n`: it is opened by universal introduction at
  a fresh rigid name, independent of `a`. Instantiating the head never captures
  it, since `Term.instantiate` renames;
- inside the step, the assumed `ho_apply(reachable, n)` proves `reachable(n)`
  through the view, converted by elimination;
- the clause node, converted under the implication, finishes the focus once.

Nothing selects the principle automatically. Under `positive`, an implication
goal has only its introduction rule, and a compound head never matches an
atomic goal: the same focus is exhausted. When to choose which principle is a
search policy. The admitted induction plan, which applies the principle once
at its focus, is S12's ([induction](machine-induction.md)).

## Proof trees

A converted node exports as its conclusion's node, read through the final store,
followed by the conversion's S08 nodes (`Unfold.convert`):

- at the call, `hoApplyElim` or `hoApplyIntro`, decided by which side has the
  extra argument;
- under an implication, the cut `impElim(impIntro(impIntro(…)), proof)`, with
  the inner `impElim` from the two assumptions.

The checker decides each node by its own procedure (`nodeCheck`), so no
`RuleCheck` is registered. The tree records the clause and its instantiation
explicitly, so checking repeats no matcher search. `Unfold.convert_proves` and
`exportNode_converted_proves` show the converted construction is valid when
the conclusion's tree is valid and the read conclusion converts to the goal.

## Proof-layer capabilities beside P0

P0 asks for evidence for every application by `ho_apply` (`hoApplyConversion`).
`Request.conversionLayer` names the S11 commands for it:

- a goal gets `hoApplyIntro` (`ho_goal`) and `converted`;
- an assumption or a clause head gets `converted`;
- a non-atomic assumption or a compound head with a conclusion, through
  implications, quantifiers, conjunctions, and disjunctions, applying a
  predicate by `ho_apply` gets its S09 commands and `converted`: a local rule's
  conclusion, a projected conjunct, an induction principle's head;
- inside data nothing converts. `holds_hoApply` relates truth, not values, so
  an indirect call as an argument is compared only with an indirect call;
- inside a NAF operand nothing converts either: conversion gives positive
  evidence, never failure, and the completion closes no `ho_apply` (S10).

The input stays outside P0 (`diagnose_not_ready`).

## Guarantees

| Property | Theorem |
| --- | --- |
| Conversion by elimination and introduction, under implications, by `Derives` rules | `Derives.ofIndirect`, `Derives.toIndirect`, `Converts.derives` |
| Views read through the answers are views of the read goals | `Indirect.resolve`, `Converts.resolve` |
| `ho_goal` and every conclusion's candidate, direct or converted, are sound in every later store | `Expansion.hoGoal_soundUnder`, `Expansion.convert_soundUnder`, `hoGoal_sound`, `conclusionAttempt_sound`, `clauseUse_sound` |
| `positive` and `left`, with conversion and `headMatch`, stay sound; their runs reconstruct `Derives` | `positive_sound`, `left_sound`, `Choice.attempt_sound`, `positive_reconstructs`, `left_reconstructs` |
| An indirect goal has the one candidate `ho_goal`, and its direct premise is never normalized again | `atomResponse_indirect` |
| A `lambda` comparison has no common instance, directly or through either view | `compareAtom_lambda`, `calls_apart` |
| A registered reference's predicate guard holds by its generated fact | `Program.predicateGuard_derives` |
| The conversion's nodes are valid given a valid tree of the conclusion; so is a converted node's export | `Unfold.convert_proves`, `exportNode_converted_proves` |
| A clause candidate is the clause use or its conversion, with fresh names | `clauseAttempt_fresh` |
| The matcher is unchanged | `Store.unify_sound`, `Store.commit_unify` (S05) |

## Traces

| Trace | Result |
| --- | --- |
| `ho_apply(p, a)` with the fact `p(a)`; under `p(a)` | `hoApplyIntro`, then the fact; then identity. Exported, accepted |
| `ho_apply(p, a)` or `p(a)` with no evidence | Exhausted, not interrupted: no rewrite loop |
| `ho_apply(p, a)` under `ho_apply(p, a) ∨ ho_apply(p, a)`, `disjCases` chosen at `p(a)`; contradiction chosen at both forms with a denial | Success; one answer, then exhausted: the selection runs at the direct form only |
| `p(a)` under `ho_apply(p, a)`; under `ho_apply(q, a)` | `converted` assumption, exported as `hoApplyElim(assumption)`; exhausted |
| `ho_apply(q, x) :- r(x)`, `r(a)`, goal `q(a)` / `p(a)` | The converted clause node; exhausted |
| `q(a)`, `ho_apply(P, x) :- q(x)`, goal `r(a)` | `P := r` by the view; the node records the view; with the clauses reversed the run is interrupted (no termination claim) |
| Answer name `X` in `ho_apply(X, a)` under `q(a)`; the fact `q(a)` instead | `X := q`, converted by introduction; unknown (a predicate choice among clauses is a gap) |
| `∀P. ho_apply(P, a)` under `q(a)`; `q(a)` under a rigid `ho_apply(P, a)` | Exhausted both: rigid predicates are never assigned |
| `∀P. ho_apply(P, a)` with the fact `q(b)`; `ho_apply(r(b), a)` with `q(a)` | Exhausted: no introduction for a rigid or compound predicate, so no gap |
| A flexible clause head for a goal applying a rigid name | The S05 match binds the clause name to the rigid name |
| `compareAtom` on direct, indirect, reference, rigid, mismatched-arity (both sides), compound, falsity, and concrete cases; `compare` on implications and binders | `direct`, `elim`, `intro` ×2, `apart`, `lambda` ×2, `apart` ×4; `elim`, `intro`, `apart`, `direct`, `apart` |
| A flexible fact for `p(a, b)`; a concrete `ho_apply(q, a)` for it; a flexible head for `false` | Unknown (lambda gap); exhausted; exhausted |
| `ho_apply(X, a)` under `q(a, b)` or with that fact; local rules `∀P. s → ho_apply(P, a)` and `∀P. s → (r → ho_apply(P, a))` for `p(a, b)` | Unknown: lambda gaps on the goal's side and at any nesting depth |
| The matcher on `ho_apply(p, a)` against `p(a)` | Still `unsupported` |
| The induction focus `isNat(a) → reachable(a)` with `headMatch`, on a program with the generated signature clauses and guard symbols | `converted` clause node with `x := a`, `P := reachable`; the guard by the generated fact `isPred1(reachable)`, a signature clause; base by `ho_goal`; the step opened at a fresh name, its hypothesis converted; the focus finished once; the export accepted |
| The same focus without the choice; the universal `∀x. isNat(x) → reachable(x)` with it | Exhausted; success |
| A guard of another domain; `r2` registered at arity 2 only; `zero`; `reachable(a, b)` | Exhausted ×3; unknown (lambda gap) |
| A conjunctive head for a conjunctive goal, by `headMatch`; a quantified head for the same universal | Matched as a whole, without conversion; accepted; matched |
| `headProject` of `ho_apply(P, x)` from `ho_apply(P, x) ∧ q(x)` for `p(a)`; of `p(x)` for `ho_apply(X, a)` | Converted by elimination; converted by introduction, `X := p`; both accepted |
| `headMatch` of `s → q(a)` for `s → ho_apply(X, a)` and for `s → ho_apply(q, a)` | `X := q`; converted by introduction under the implication; both accepted |
| Hand-built conversions | Accepted; rejected for another predicate and for another implication premise |
| Diagnoses | An indirect goal: `hoApplyIntro`, `converted`; an indirect assumption or head: `converted`; inside data or a NAF operand: nothing; the induction principle's head: `headUse`, `converted`; a local rule `q → ho_apply(p, a)`: `impUse`, `converted`; a head `ho_apply(P, x) ∧ q(x)`: `headProject`, `headUse`, `converted` |

## Boundaries

- **No termination or completeness.** A flexible head concludes every call of
  its arity, its own body's included, and a selection may choose a principle
  again on its subgoals. Admitted induction is S12's
  ([induction](machine-induction.md)). `exhausted` stays relative to the strategy.
- **No general higher-order unification.** Predicate names are bound only to
  what structural matching finds: a reference, or a name. Lambda-valued answers
  for calls are classified and reported as gaps. A flexible goal predicate is
  not chosen among program clauses unless a selection chose the clause.
- **An unbound goal predicate does not wait.** A goal `ho_apply(X, a)` with `X`
  unbound is answered at once, so `ho_apply(X, a) ∧ q(X)` meets its direct
  clauses as gaps while the reversed conjunction succeeds. Delaying on `X`, as
  range guards delay (S18), is a possible follow-up.
- **Conversion is of truth, not values.** Inside data, `ho_apply` is compared
  syntactically: the matcher still reports an indirect call against a direct
  one as `unsupported`, and P0 data still exclude `ho_apply`.
- **Views are of conclusions.** Conversion reaches the conclusion of a formula
  and of its implications. Calls in premises, conjuncts, or under quantifiers
  are compared as written.
- **Whole-run export.** The constructions are checked given checked premise
  trees. That every successful run exports an accepted tree belongs to S15/S16,
  as for S09.
