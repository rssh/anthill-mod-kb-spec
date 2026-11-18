# Decision IR: admission as translation

Status: design, decided with the user on 2026-11-17. S27's part, the IR, its
checker and evidence, its semantics, the Herbrand reduction, relevance with
the relevant program finite under P1, and S07's ground programs as the P0
case where the IR expresses them, is [implemented](ir-programs.md). It revises the
[S01 contract](lean-admission-contract.md)'s "one syntax and one
interpreter/state machine": there is still one syntax and one meaning, but
decisions run on an intermediate representation (IR) of their own, which
admission translates the KB into, and the shared machine is the proof search.
Its work items are S27–S31, with S15, S21, S25, and S26 re-scoped, in the
[plan](resolution-implementation-plan.md).

## Why: two kinds of execution

A **decision** computes every answer of a call: its tables are the result, the
order of its steps changes nothing, and its meaning is the Clark completion
(the closed world). A **proof search** needs one derivation: its choices
matter, and an exhausted search proves nothing (the open world). P0 and P1 are
decisions; P3 is proof search. Running both on the shared machine means that
the guarantee admission gives is not carried by what runs: it has to be proved
again about a machine that can do far more than the admitted fragment. The
code shows it:

- P0 already decides on its own ground form. Admission builds `P0.Ground`,
  `GroundSearch.decided` decides it, and `Ground.strategy_eq` and
  `P0.run_correct` prove that the machine agrees. `Plan.answer` still maps
  `opened`, `abandoned`, and `interrupted`, which only a theorem rules out, to
  `false`.
- The tabled engine re-derives at every focus what S23 decided
  (`Engine.callOfAtom`: modes, rigidity, closedness, bounds) and guards itself
  with cuts (`admits`, `inSpace`, `fit`, `GapReason.bounded`) that S15 would
  have to prove never fire for P1.
- The decision is already split. In `Setup.answerFrom` the machine run gives
  only Yes; No comes from the Kripke–Kleene refutation and Unknown from the
  fixpoint witnesses.
- The P1 label is not backed. S23 puts lowered programs (guards first) and
  non-ground programs with NAF in P1, but S24 has no greatest witness for
  guarded programs and no witness for non-ground NAF, so goals the completion
  leaves open end Undecided there.

## The architecture

```text
snapshot + query (Term)
  └─ admission = translation ─┬─► IR program + query ─► IR evaluator ─► Yes | No | Unknown
                              └─► Undecided(blockers): a proof, a mode, a termination argument, a construct
formula that needs a proof ─► proof search (shared machine) ─► S08 tree ─► checked lemma ─► derived rules
```

- **One syntax, one meaning.** The KB, queries, and proofs stay `Term`.
  Answers are about the models of the completion with complement NAF that
  realize the admission signature (`Meaning.ofModels`, as S22's); proofs are
  `Derives`.
- **Admission translates.** Before anything runs, it turns the snapshot and
  the query into an IR program and query, or reports what is missing at its
  site and path. No missing capability is discovered at run time.
- **Two machines.** The IR evaluator decides; the shared machine (S04–S20)
  searches for proofs, which S08 checks.
- **Bridges.** Proof search may ask the evaluator about a subgoal; a checked
  proof returns to the translation as derived rules (below).

## The IR

A separate Lean type (proposed names: `IR.Program`, `IR.Rule`, `IR.Literal`,
`IR.Query`), in which only decidable constructs are expressible.
Connectives, quantifiers, and compound NAF operands compile to rules of
auxiliary predicates.

| Element | Form |
| --- | --- |
| Predicate | A symbol, its arity, its declared modes, and its kind: *defined* (the completion closes it), *open* (a marker case, `p(x̄) :- UNKNOWN`), *guard* (a domain's membership), *primitive* (a registered total evaluator, S14) |
| Rule | `p(inputs; outputs) :- literals`: a definition; the completion is over the rules |
| Derived rule | The same form, from a checked lemma: used to derive, never part of the completion |
| Denial | `⊥ :- literals` |
| Literal | A call `q(inputs; outputs)`; `naf q(args)` with every name bound; `x = t` and `x ≠ t`; a guard `D(x)`, decided by the constructor of `x`, or binding `x` over a finite domain; a primitive `f(inputs) = output`; a marker atom |
| Query | The context's conditions, the atoms to decide, the answer names |

**Well-formedness** (`IR.check`, decidable). Read left to right, every
literal's inputs are bound (S23's `scan`, on the IR). The translator orders a
conjunction's literals so that names are bound from finite sources first;
conjunction commutes in the completion, so the order changes no meaning. A
data name no guard literal guards is carrier-ranged: the program is
well formed, and P2 (decided with the user, 2026-11-18; see the boundaries).

**Finiteness evidence** makes a program **P1**: the query's *relevant
program*, the ground rule instances its calls and the denials' calls can use,
is finite, both for the answers a call derives and for the answers it may
have in some model (S27's `relevant_finite`, `instances_finite`). The denials join every query's relevant program (decided
with the user, 2026-11-18): a denial can rule out a model of the query's
part on a consistent KB (`p(a) :- naf q(a). q(a) :- naf p(a). ⊥ :- p(a).`
makes `p(a)` No), so its instances that the relevant atoms meet are decided
with the query, and a denial without the evidence makes the query P2.
Admission establishes it from S23's analyses, on the IR, per call pattern
(S27):

1. Every call in the dependency closure has bounded inputs: within a
   component, data terms of its entry's inputs (`calls_bounded`); across
   components, those bounds composed along the component order, since a body
   may construct the input of a lower component (`p(X) :- q(succ(X))`), and
   many calls in one body can grow a term at each step. Contexts are sets: an
   assumption repeated along a recursion adds nothing. S24's bounded run, with
   a size limit and repeat-free contexts, cuts both cases (its
   [boundaries](tabled-evaluation.md)).
2. Every call has finitely many derivable answers: data-term outputs, or a
   decreasing component (`outputs_bounded`, `calls_decrease`).
3. In a component that does not decrease, no recursive call leaves an output
   free: as checked (S27), from a vertex that leaves an output free, every
   call that leaves one free goes to a lower level or decreases. A
   self-supporting cycle holds of unboundedly many values in the greatest
   fixpoint: `path(X, Y) :- edge(X, Z), path(Z, Y)` over a cycle, with `Y`
   free, holds of every `Y`. A ground query binds `Y`; `∃Y. path(a, Y)` does
   not, and is P2.

A program without the evidence is **P2**: the same evaluator, with fuel
(decided with the user, 2026-11-17). A measure or a reordering supplied later
makes it P1 with nothing else changing.

**Semantics.** Interpretations over constructor keys and the consequence
operator, as in S24's `Tabled/Fixpoint`, extended to guards (exact, by the
domains' constructors), primitives (by their evaluators), and markers (free).
Two lemmas connect it to the models the answers are about (S27):

- **Herbrand reduction.** When every data name of the program and the query is
  guarded (lowering guards every data binder), a closed formula holds in every
  model of the completion realizing the signature exactly when it holds in
  every key fixpoint. A closed predicate holds only of values of constructor
  terms, and the free equality theory makes those values keys.
- **Relevance.** The relevant atoms are a splitting set: an interpretation is
  a model of the completion exactly when its relevant atoms satisfy the
  relevant program's completion, the other atoms the rest of the completion,
  and the denials hold, which they do exactly at their passing instances
  (S27). So the completion's models restricted to the relevant program are
  models of its completion, and a model of its completion is such a
  restriction when the rest of the KB extends it. Consistency is not enough
  for that: an unreached rule `r(a) :- p(a), naf r(a)` forces `p(a)` false on
  a consistent KB. S28 answers Unknown only when no rule outside the relevant
  program reads a relevant atom under NAF on a cycle, and Undecided naming
  that rule otherwise (decided with the user, 2026-11-18).

## The evaluator

| Profile | How it runs | What it answers |
| --- | --- | --- |
| P1 | Build the relevant program, which is finite. Compute the definitely and the possibly true atoms (the Kripke–Kleene iteration, S24's `kk`). Decide the atoms left undefined by enumerating the completion's models over them | Yes, No, or Unknown, exactly, with no fuel and no gap; Undecided only for the KB's inconsistency |
| P2 | The same over a relevant program that may be infinite, within the fuel. No by the Kripke–Kleene refutation over the data terms and one abstract value (S24's `refutes`), Unknown by S24's witnesses | Sound answers; Undecided naming the growing call; monotone in the fuel |

**Cost classes**, reported by admission before anything runs:

| Class | When | Why |
| --- | --- | --- |
| Polynomial, of degree k (S23) | No NAF or denial reads a predicate whose dependency closure reaches a cycle or a marker | Every model lies between two computable ones: the least fixpoint with the markers false and the greatest with them true |
| Exponential | Otherwise | Deciding the completion's models is NP-hard (supported models); the enumeration is exact |
| Budgeted | P2 | Bounded by the fuel |

So NAF through a cycle, or a split that depends on the data, is decidable but
expensive: a cost class, not Undecided.

## Answers and certificates

Yes means truth in every model of the completion, not a `Derives` proof
(decided with the user, 2026-11-17), so that the evaluator can be exact.

| Answer | Meaning | Certificate | Check |
| --- | --- | --- | --- |
| Yes | Holds in every model of the completion realizing the signature | A derivation over the relevant program, its NAF nodes refutations; or the relevant program, the goal true in all its completion models | S08 for a derivation; recomputation otherwise |
| No | Fails in every such model | A Kripke–Kleene refutation, or the relevant program, the goal false in all its models | Recomputation |
| Unknown | Holds in one such model and fails in another | Two assignments of the relevant program's atoms, each a fixpoint | The fixpoint check (S24's `groundFixpoint`) |
| Undecided | Nothing about the KB | Blockers | — |

In `p :- q. p :- naf q. q :- q.`, `p` holds in every model, whichever value
`q` takes, and has no derivation: Yes, certified by the relevant program. A Yes
whose derivation has no closed-world step (no NAF node, no use of the
completion's only-if half) is a theorem of the KB: it stays valid as the KB
grows, exports as an S08 tree, and can serve as a checked lemma. Every other
answer is indexed by the snapshot, as NAF evidence is now.

## Admission as translation

The translator (S29) reads the snapshot (the lowered KB with its generated
signature clauses, modes, registry, and checked lemmas) and the query. It
produces an IR program and query, with the correspondence from IR rules to KB
clauses (for blockers and exports), or Undecided with blockers. Its theorem:
every model of the KB's completion realizing the signature extends, by the
auxiliary predicates' definitions, to a model of the IR program's completion,
and back; and in it the query and its translation agree.

A formula's translation depends on its **position**: a KB statement (a
definition), a checked lemma (derived), the query's context (a condition), a
goal or a clause body, a NAF operand, a denial body.

### Patterns

A **pattern** is a recognizer (a shape at a position, with its side
conditions), an emitter (IR rules, auxiliary predicates with fresh names,
literals), and a correctness lemma: the emitted IR has the source formula's
meaning in every model of the completion realizing the signature. It is a
structure that carries its proof, as S08's `RuleCheck` is, and the translator
is correct for any set of correct patterns.

**Patterns are responsible for meaning; the IR checker for decidability.**
Emitted IR is checked like any other, so a pattern cannot weaken a guarantee,
and patterns compose: `∀x∈C. ∃y∈D. R(x, y)` as a goal is the universal
pattern over the existential one. New decision procedures are a second, rarer
extension point, **IR primitives**: each comes with its evaluator and a proof
of exactness (an automaton for regular predicates, disunification for
constructive negation, a dictionary evaluator).

A formula with no pattern at its position, or whose emitted IR the checker
rejects, is a blocker naming what is missing: a **proof** (the formula is
named, so a checked proof of it can be supplied), a **mode**, a
**termination** argument, or a **construct**.

### Statements: normalization defines the completion

Definition patterns decide how a KB statement enters the completion. The
user's example (2026-11-17): when `C` is a collection, the statement
`∀x∈C. P(x)` is the rule `P(x) :- x ∈ C`, and so is `∀x̄∈C̄. B → A`, with
`A` an atom and every range a collection, the rule `A :- x̄ ∈ C̄, B`. The KB
defines no collections yet. This changes today's reading, where
`Completion.headOpens` leaves the predicates of such a head open: under
normalization they are defined.

**A declared data domain is special, and undecided** (the user, 2026-11-17:
"for D_i: need think"). Whether `∀x:D_i. P(x)` defines `P`, constrains it, or
states a theorem about it is open. Until it is decided, such a head keeps
today's reading: its predicates opened, and the statement a denial
(`⊥ :- D_i(x), naf P(x)`). A conjunction of atomic heads (`p(a) ∧ q(a)`) as
one rule each is proposed, not yet confirmed.

Other compound heads (a disjunction, an existential, a formula variable, a
predicate variable under `ho_apply`) keep opening their predicates, a marker
case each, and the statement becomes a denial: `A ∨ B :- body` is
`⊥ :- body, naf A, naf B`.

Derived statements never enter the completion: checked lemmas, S12's
principles, and dictionary laws. A proved `∀x∈C. P(x)` is the derived rule
`P(x) :- x ∈ C`, over a collection or a declared domain alike. As a
definition it would widen `P`'s completed definition and
admit models that are not models of the KB's completion, so a witness of
Unknown could be wrong. As a derived rule it is valid in every model and
changes no exact answer; it gives a derivation where the definitions give only
a model check, and a Yes within less fuel in P2.

### Conditions and implications

A query's context is a condition on the models (`Meaning.ofModels`): Yes when
every model satisfying it satisfies the goal, No when none does. So the context
translates as goals, and the answer is read from the statuses of `Γ ∧ G` and
`Γ ∧ naf G`. An implication goal `A → G` is `naf A ∨ G`; a disjunctive or an
existential assumption is a disjunction or an existential conjunct of `Γ`.
This reading is exact over the completion.

Adding the context as local clauses (the hereditary Harrop reading, S26's
original design) is the proof machine's: sound, since every model of the
completion that satisfies `Γ` is a model of the extended completion, but not
exact once NAF is involved. With `g :- naf a` and no clause for `a`, the goal
`a → g` is Yes (no model has `a`), yet `g` fails once `a` is added as a
clause.

### The initial catalog

The checker verifies what a column "Needs" names; a pattern whose IR it
rejects does not apply.

| Shape | Position | IR | Needs | Ticket |
| --- | --- | --- | --- | --- |
| A clause with an atomic head and a fragment body | Definition | A rule | — | S29 |
| `∀x̄∈C̄. B → A`, every `C` a collection | Definition | A rule | — | S29 |
| `∀x:D_i. …` over a declared data domain | Definition | Until decided, as today: its predicates opened, and a denial | — | S29 |
| A disjunctive or existential head | Definition | Its predicates opened, and a denial | — | S29 |
| A concrete `ho_apply(p, args)` | Any | The call `p(args)` (S11's `ho_goal`) | — | S29 |
| A dictionary call | Data | A primitive literal | S13's access check, S14's contract | S29 |
| `∃x∈C. φ` | Goal, body | A conjunction, `x` local | — | S29 |
| `∀x∈C. φ` | Goal, body | `naf aux`, with `aux(ȳ) :- C(x), naf φ'` (Lloyd–Topor) | `C(x)` enumerates `x` | S30 |
| `naf φ`, `φ` compound or with local names | Goal, body | `naf aux` with `aux`'s rules | `φ`'s other names bound | S30 |
| `A → G`; a query's context | Goal, condition | `naf A ∨ G`; `Γ ∧ G` and `Γ ∧ naf G` | `Γ` translates as a goal | S26 |
| `∀x:D. φ`, `D` an inductive domain, `φ` regular | Goal | The regular primitive | S25's class | S25 |
| `naf q(X)`, `X` free | Goal, body | Constructive negation | `q`'s answers finite | S21 |
| A checked lemma that normalizes to rules | Derived | Derived rules | Checked by S08 or S20 | S31 |
| `∀x:D. φ`, otherwise | Goal | A blocker: a proof (induction, S12) | — | — |

## Profiles

| Profile | What admission produced | Guarantee |
| --- | --- | --- |
| P0 | A ground, acyclic IR program (S07's `P0.Ground`) | Yes or No, with no fuel |
| P1 | An IR program with the finiteness evidence | Yes, No, or Unknown, exactly, with no fuel; polynomial or exponential cost |
| P2 | An IR program without it | Sound answers within the fuel, monotone in it |
| P3 | No translation for some part | Proof search on the shared machine; inside the module, Undecided naming the formula that needs a proof |

P0 ⊂ P1 ⊂ P2 are evidence classes of one IR and one evaluator. Checking a
supplied proof tree (S08) stays a P1 decision of its own kind: it decides the
validity of the tree, not the goal. P3 is not a class of the IR: it is the
proof layer, whose results return as checked proofs and derived rules.

## The proof machine and the bridges

The shared machine is the proof search: left rules, conversion, induction,
checked lemmas, law search, delayed goals, and constraint solvers. Exhaustion
means nothing there; only proofs come out, checked by S08.

- **Oracle.** A strategy may ask the evaluator about a subgoal the translator
  accepts. A Yes with a derivation is spliced in as its exported tree; any
  other Yes is a decision node, checked by recomputation (a new S08
  `RuleCheck`); a No is NAF evidence (a `NafCheck` recomputing it, as S24's
  `nafCheck` does). S10's refutation search stays for operands the translator
  does not accept.
- **Lemmas back.** A checked proof of a statement that normalizes to rules
  becomes derived rules of the next snapshot's IR: S20's lemmas, and instances
  of S12's principles.

## What carries over

| Role | Existing work |
| --- | --- |
| The IR and its evaluator | `P0.Ground` and `GroundSearch.decided` (S07); S23's program, modes, `scan`, classes, and call bounds, as the IR's well-formedness and evidence; S24's `Fixpoint`, `Abstract`, `AbstractSound`, and `Witness`, as its semantics and P2's abstraction; S14's evaluators, as primitives; S22's `Answer`, `Blocker`, and `Missing` |
| Patterns and primitives | S21's constructive negation, S25's regular predicates, S26's contexts, the deferred finite guarded quantification route |
| The proof machine | S04–S06, S09–S12, S18–S20, S14's law search, S10's refutation search |
| No longer the decision path | S24's engine on the shared machine (`Engine`, `EngineSound`, `Weight`, `Termination`, `Multiset`): kept until S28 replaces it, then tabling for proof search if that needs it |
| Re-scoped | S15 composes the translation, the evaluator, and the bridges; its obligation that a bounded run's checks never fire for P1 disappears |

## Boundaries and open points

- **Statements over a declared data domain.** Whether `∀x:D_i. P(x)` in the
  KB defines `P`, constrains it, or states a theorem is open (the user,
  2026-11-17); so is a conjunction of atomic heads as one rule each. Until
  decided, both keep today's reading.
- **Free outputs on cycles** (point 3 above) are P2, unless the translator
  binds them from a finite source. Deciding them exactly over infinite domains
  would need possible answers as constrained terms; not planned.
- **Rigid parameters.** A query's parameters range over their binders' ranges.
  Exactness over every value needs genericity (values outside the relevant
  data terms behave alike when no rule matches them against a constructor) or
  a split by domain closure (S21). Settled with the user, 2026-11-18: a
  parameter that a finite guard among the query's conditions guards splits
  into one ground query per member, and the query is P1 when every instance
  is; every other parameter is P2 ([S27](ir-programs.md#rigid-parameters)).
  The query is Yes exactly when every instance's truth holds, No exactly when
  every instance's falsity holds, Unknown exactly when one instance is not No
  and another not Yes. An instance whose conditions no model satisfies is
  both Yes and No (vacuous contexts, below), so "Unknown when neither all
  are Yes nor all are No" holds only when no instance is vacuous. Genericity
  is not taken.
- **Carrier-ranged binders** are outside the Herbrand reduction: P2, with
  S24's abstract value.
- **Vacuous contexts.** A context that no model of the completion satisfies
  makes Yes and No both true, and a context fact on a closed predicate that
  the KB does not derive is such a context. S24 already shows it: with
  `q(X) :- r(X)` and no clause for `r`, `q(x)` under `r(x)`, `x` rigid, answers
  No by the refutation, and `q(a)` under `r(a)` answers Yes by its run, both
  vacuously sound. Read as additions to the program instead, as the
  hereditary Harrop reading does, a Yes or a No over the extended completion
  is sound under the condition reading (every model of the completion
  satisfying the context is a model of the extended one), but an Unknown is
  not. Which reading a context gets is S26's to settle with the user.
- **Consistency.** Exactness is relative to the KB having a model, and, for
  an Unknown, to the rest of the KB extending the relevant program's models
  (relevance, above). A KB-level check (denials, NAF cycles) runs beside the
  queries, as S24's denial checks do now; an inconsistent KB answers
  Undecided, naming it.
- **Answer sets.** The evaluator computes every answer of a call, so returning
  the answers of a query with answer names, the deferred finite-answer route,
  becomes a small step.
- **The contract.** This note revises "one syntax and one interpreter/state
  machine" and R17 ([contract](lean-admission-contract.md)), Yes as a
  `Derives` proof ([answers](answers.md), [fast evaluation](fast-decision-routes.md)),
  and the tabled engine as the decision path ([tabled evaluation](tabled-evaluation.md)).
  P1's catalog routes become patterns and primitives.
