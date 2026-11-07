# Fast decision routes

The Anthill KB module should either compute an answer or stop fast and say
what it cannot compute. Its answers are S22's: **Yes**, **No**, **Unknown** (the
KB leaves the goal open), and **Undecided(blockers)** (the module did not decide
it). Today the decided set is P0's: ground, non-recursive programs. This note
specifies three P1 routes that decide a much larger set of programs. It is a
design; the routes are S23–S25 in the [plan](resolution-implementation-plan.md).

## Principles

- **One machine.** A route is an admission condition, not an engine. Under it,
  the shared machine's depth-first backtracking search terminates and
  decides, with at most the machine extension the route names. There is no
  bottom-up saturation and no separate automata algorithm.
- **The completion decides.** Yes, No, and Unknown are against the Clark
  completion, as S10's NAF is. A goal the completion leaves undetermined is
  Unknown, shown by S22's two witness models, never No. In particular a goal
  cut on a positive cycle is Unknown, not a least-model No (decided with the
  user, 2026-11-07).
- **Classes per predicate.** Local checks give each predicate a class, and a
  query's class follows from the predicates it uses. Outside every class, the
  answer is Undecided with a blocker naming the predicate, its site, and the
  condition it breaks.
- **Fast is terminating and deterministic.** Termination comes from a
  structural decrease or a finite domain. Speed comes from non-overlapping
  input patterns: at most one clause applies to each call, so the search has
  no choice points and is linear in its depth. A terminating predicate with
  overlapping patterns is still decided, without the speed guarantee.
- **Declared, not inferred.** Modes (input and output arguments) and a
  decreasing argument are declarations, which the KB generator emits as it
  emits explicit binder ranges. A domain's finiteness follows from its rules,
  and the regular shape of a definition is recognized.

## The routes

| Route | Admission condition | Machine | Answers |
| --- | --- | --- | --- |
| [Moded structural recursion](#moded-structural-recursion-s23) (S23) | Well-moded calls; every recursive call, NAF included, on a strict subterm of a declared decreasing input | Unchanged | Yes, No, Unknown for open predicates |
| [Recursion over finite domains](#recursion-over-finite-domains-s24) (S24) | Recursion through arguments over finite domains; ground calls; stratified NAF | A loop check on the current branch | Yes, No, Unknown for a goal cut on a cycle |
| [Regular unary predicates](#regular-unary-predicates-s25) (S25) | Unary predicates defined by flat constructor clauses; goals `∀x:D. φ(x)` and `∃x:D. φ(x)` | A bounded search over finitely many states | Yes, No with a counterexample, Unknown for open predicates |

### Moded structural recursion (S23)

A predicate declares its input and output arguments and, if recursive, a
decreasing input. Admission checks, clause by clause:

- **Well-moded bodies.** Read left to right, each call's inputs are ground by
  the head's inputs and the earlier goals' outputs; NAF and guards apply only
  to calls ground by mode.
- **Structural decrease.** Every call into the predicate's recursive group,
  NAF included, has its decreasing argument a strict subterm of the head's: a
  level mapping by term size.
- **Determinism** (a speed class, not a blocker). The input patterns of a
  predicate's clauses do not overlap.

On such programs depth-first SLDNF terminates and decides against the
completion (Apt & Bezem, *Acyclic programs*, 1991). A success is Yes, by
`Derives`; a complete failure is No, with failure evidence like P0's; an open
predicate reached is Unknown, with S22's witnesses. Examples: `reachable(+)`,
`even(+)`, `append(+, +, -)`, `length(+, -)`.

### Recursion over finite domains (S24)

Recursion whose recursive arguments range over finite domains, such as
transitive closure over a finite graph, needs no decrease: ground calls over
finite domains have finitely many distinct goals. A domain is finite when, by
its rules, no constructor of it takes it, directly or through other domains.
NAF must be stratified: no NAF inside a cycle.

The machine gets a **loop check**: a goal identical, as read, to one of its
ancestors on the current branch is cut, and the cut is recorded. Cutting a
repeated goal loses no proof, so the run terminates and every proof is found.

- A proof is Yes.
- A failure that depends on no cut is No: finite failure is sound for the
  completion.
- A failure that depends on a cut is Unknown. For `path` over a graph with a
  cycle a ↔ b and a node c reachable from neither, the completion has a model
  where `path(a, c)` and `path(b, c)` are both true and one where both are
  false. The witnesses are the cycle's atoms all true and all false, checked
  against the KB's clauses and denials. If they do not check, as when a denial
  forces an atom of the cycle, the answer is Undecided, naming the cycle.

This route replaces the catalog's "finite rule saturation" and "stratified
NAF over finite rules", which assumed a least-relation decision.

### Regular unary predicates (S25)

A unary predicate over a declared domain is **regular** when each of its
clauses is flat, `p(c(x₁, …, xₙ)) :- body`, with distinct head variables and
body atoms that are unary on the fields: other regular predicates, guards,
and NAF of regular predicates, stratified. Nested patterns are flattened by
generated auxiliary predicates (`even(succ(succ(x))) :- even(x)` becomes two
flat clauses). Such a definition is a tree automaton over the domain's
constructors, and the terms satisfying it form a regular tree language.

Each ground atom `p(t)` is decided by S23: the fields are strict subterms. The
**state** of a term is the set of regular predicates true of it. A goal
`∀x:D. φ(x)` or `∃x:D. φ(x)`, with `φ` a Boolean combination of regular
predicates on `x`, is decided over the finitely many states:

- **Yes** for `∀`: the states reachable from `D`'s constructors, closed under
  its rules, all satisfy `φ`. Sound by induction on membership, as
  `principle_valid` is: the domain's exact realization makes its members the
  least set built by its rules.
- **No** for `∀`: a counterexample term no deeper than the number of states,
  refuted by S23.
- `∃` dually; an open predicate gives Unknown, with S22's witnesses.

The search over states is a bounded backtracking search with a visited check.
Its bound is fixed at admission. The visited check is justified by the domain's
exact realization, not by the completion of KB predicates. The cost is
exponential in the number of predicates in the worst case.

Examples: `∀x:Nat. reachable(x)`, `∀x:Bool. defined(x)`, and
`∀x:List. allNat(x)` are Yes; `∀x:Nat. even(x)` is No, with the counterexample
`succ(zero)`; `∀x:Nat. even(x) ∨ odd(x)` is Yes. S12's induction path stays the
P2 route for predicates outside this class and for supplied proofs.

## Limits

- **Relations.** Multi-argument relations such as `less(x, y)` or
  `plus(x, y, z)` are outside the regular class. Presburger arithmetic for Nat
  and the H1 or shallow Horn classes are larger decidable classes, not
  planned; outside them the answer is Undecided until a proof is supplied.
- **Non-structural recursion.** Recursion on a measure other than a subterm,
  such as `gcd`, needs a supplied measure with a checked proof; not planned.
- **Cycles over infinite domains.** The loop check guarantees termination only
  over finite domains; a cycle through an infinite domain is a blocker.
