# Fast evaluation by tabled backtracking

The Anthill KB module should either compute an answer or stop fast and say
what it cannot compute. Its answers are S22's: **Yes**, **No**, **Unknown** (the
KB leaves the goal open), and **Undecided(blockers)** (the module did not decide
it). Today the decided set is P0's: ground, non-recursive programs.

This note specifies a larger fragment: a Prolog-like language, run by tabled
backtracking on the shared machine, whose cost is polynomial in the data for a
fixed program wherever recursion does not grow terms, and bounded by fuel
where it does. Its exact part is in P1, the rest is P2, and proof search
beyond clause selection is P3 ([profiles](lean-admission-contract.md)). It is
a design; its work items are S22–S26 in the
[plan](resolution-implementation-plan.md).

## The model

- **Language.** Clauses with atomic heads. Bodies with conjunction,
  disjunction, NAF, data equality, and guarded quantifiers. λProlog-style
  implication goals with Harrop antecedents and generic universal goals. Open
  predicates `p(x̄) :- UNKNOWN`.
- **Execution.** Depth-first backtracking with **tabling** (SLG resolution, as
  in XSB): each distinct call, in its context, has a table of answers. A
  repeated call consumes its table instead of recomputing; a recursive call
  waits for answers instead of looping; tables complete per strongly connected
  component; a loop through NAF is delayed and resolved when its component
  completes.
- **Fuel** bounds every run.
- **One machine.** Tabling is an extension of the shared machine, and the
  fragment's conditions are admission conditions. There is no separate engine.

Backtracking, disjunction, several matching clauses, nondeterministic outputs,
and loops, positive or through NAF, all stay.

## Conditions and cost classes

**Safety** is the one hard condition: every variable a NAF goal, a guard, or an
output uses is bound by an input or by an earlier positive goal, so nothing
enumerates an infinite domain. Predicates declare their input and output
arguments (modes), which the KB generator emits as it emits explicit binder
ranges; they are never inferred.

**Term growth** decides a predicate's cost class, not its admission:

| Class | Condition | Guarantee |
| --- | --- | --- |
| **Complete** | Every recursive call's arguments are subterms of the head's inputs or data constants | Finitely many distinct calls: the run ends without needing fuel, in time O(nᵏ) for n data terms, with the degree k from the program (roughly the free variables a clause joins), reported per predicate |
| **Budgeted** | Some recursion grows terms (`p(x) :- p(succ(x))`) | Bounded by the fuel; may answer Undecided, naming the growing call |

Non-overlapping input patterns refine the complete class: at most one clause
applies to each call, so the run has no choice points there.

| Profile | Predicates |
| --- | --- |
| **P1** | Complete, with no NAF or denial over a predicate on a cycle: answers Yes, No, or Unknown, never Undecided |
| **P2** | The rest of the fragment: budgeted predicates, NAF or denials over a predicate on a cycle, splits or hypotheses that depend on the data |
| **P3** | Proof search beyond clause selection (S09's left rules, S12's induction run, S14's law search): proof producers, whose results enter as checked proofs |

## Answers

| Answer | When | Evidence |
| --- | --- | --- |
| **Yes** | A proof is found | `Derives`, exportable as an S08 tree |
| **No** | The search completed, and the failure depends on no cycle | Finite failure, sound for the completion |
| **Unknown** | The search completed, and the completion leaves the goal open: an open predicate reached; a failure through a positive cycle (`path(a, c)` over a cycle a ↔ b, c unreachable); a loop through NAF with models both ways (`p :- ¬q`, `q :- ¬p`); case-split branches that disagree | Two witness models, checked against the KB's clauses and denials |
| **Undecided** | The fuel ran out; the completion is inconsistent (`p :- ¬p`); the witnesses do not check; a construct outside the fragment | Blockers: the growing call, the cycle, or the construct, with site and path |

The answers are against the Clark completion, as S10's NAF is (decided with
the user, 2026-11-07): a goal cut on a positive cycle is Unknown, not the
least-model No that tabling alone would give.

For positive recursion, cycles included, the completion's models are exactly
the fixpoints of the clauses' consequence operator, all between the least and
the greatest. Over the finitely many calls of a complete predicate both are
computed: an atom in the least fixpoint is Yes, one outside the greatest is
No, and one in between is Unknown, the two fixpoints its witnesses. So Unknown
is exact in P1. With NAF or a denial over an atom the completion leaves open,
exactness is NP-hard in general (supported models); in P2 the witness check
keeps the run polynomial, at the cost of Undecided in the hard cases.

Answers are **monotone in the fuel**: a Yes, a No, or an Unknown never changes
with more fuel; only Undecided can.

## Contexts: case splits, implications, universals

| Construct | How it runs | Answer and cost |
| --- | --- | --- |
| A disjunctive assumption `A ∨ B` | Split eagerly, once per branch: disjunction elimination is invertible, so nothing backtracks over the split | Every branch Yes: Yes. Every branch No: No. Yes in one, No in another: Unknown, the branches its witnesses. Each split doubles the remaining work, so the number of splits must not grow with the data: disjunctive Datalog is coNP-complete in the data |
| An existential assumption `∃x. A` | Opened at a fresh name | One branch |
| An implication goal `D → G`, `D` a Harrop clause | `D` added as a scoped local clause, used by backchaining; tables keyed by the context | Success is Yes. With a ground antecedent the fragment decides, `D → G` is read materially: `D` false gives Yes, otherwise `G` decides. Otherwise a failure is Undecided. Antecedents that depend on the data can reach PSPACE (hypothetical Datalog): budgeted |
| A universal goal `∀x. G` | At a fresh eigenvariable, never by enumeration | Success is Yes. A failure is Undecided, since the goal may hold by induction, unless a decided reading exists: expansion over a finite domain, or regular predicates (below) |

NAF inside an implication's or a split's scope is judged against the program
extended by that scope's assumptions.

## Regular unary predicates

A unary predicate over a declared domain is **regular** when each clause is
flat, `p(c(x₁, …, xₙ)) :- body`, with distinct head variables and body atoms
unary on the fields: other regular predicates, guards, and NAF of regular
predicates. Nested patterns are flattened by generated auxiliary predicates.
Such a definition is a tree automaton over the domain's constructors.

Its ground atoms are in the complete class: the fields are strict subterms.
The **state** of a term is the set of regular predicates true of it. A goal
`∀x:D. φ(x)` or `∃x:D. φ(x)`, with `φ` a Boolean combination of regular
predicates on `x`, is decided over the finitely many states:

- **Yes** for `∀`: the states reachable from `D`'s constructors, closed under
  its rules, all satisfy `φ`. Sound by induction on membership, as
  `principle_valid` is: the domain's exact realization makes its members the
  least set built by its rules. This, not the completion of KB predicates,
  justifies the search's visited check.
- **No** for `∀`: a counterexample term no deeper than the number of states.
- `∃` dually; an open predicate gives Unknown, with witnesses.

`∀x:Nat. reachable(x)`, `∀x:Bool. defined(x)`, and `∀x:List. allNat(x)` are Yes;
`∀x:Nat. even(x)` is No, with the counterexample `succ(zero)`. The cost is
exponential in the number of predicates in the worst case. S12's induction
path stays the P3 route for predicates outside this class.

## Outside the fragment

These constructs need search beyond clause selection. A query that needs one is
Undecided, with the construct as its blocker. They stay in the KB language as
statements, used through a checked proof (S08) or a checked lemma (S20):

| Construct | Why it needs search |
| --- | --- |
| Compound heads (`A ∧ B :- …`, induction principles) | Whole-head matching and projections |
| Heads applying a predicate by `ho_apply(P, x)` | Meet every unary call |
| Formula variables, as goals or as heads | `call(G)`, a head that matches anything |
| A flexible predicate in `ho_apply(P, args)` | Choosing a predicate |
| Term-choosing uses of non-Harrop assumptions | Choosing an instance of `∀x. A(x)`, or using a compound conclusion |
| Conditional equations as replacement | Equational reasoning; operations run by total evaluators instead |
| Dictionary-law reasoning | Choosing laws; laws are statements |
| NAF on a goal not ground by mode | Refutation search (S10) or constructive negation |

Denials `⊥ :- body` are never selected as clauses: ex falso would make every
goal a candidate. They constrain the witnesses, and a denial whose body is Yes
makes the KB inconsistent, so its answers are Undecided.

## Limits

- **Relations.** Multi-argument relations such as `less(x, y)` are outside the
  regular class. Presburger arithmetic for Nat and the H1 or shallow Horn
  classes are larger decidable classes, not planned.
- **Exact Unknown.** The witness check may fail where the completion does leave
  a goal open; the answer is then Undecided.
- **Data-dependent hypotheses and disjunctions.** Budgeted, not complete.
