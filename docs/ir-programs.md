# The decision IR's programs (S27)

S27 implements the IR of the [decision IR](decision-ir.md): the Lean type of
the programs decisions run on, its checker, its evidence classes
P0 ⊂ P1 ⊂ P2, and its semantics, connected to the models the answers are
about. `Term` stays the representation of the KB, the queries, and the proofs;
the translator into the IR is S29's, its evaluator S28's. Traces are in
[Tests/Resolution/IR/Evidence.lean](../Tests/Resolution/IR/Evidence.lean).

| Module | Contents |
| --- | --- |
| [IR/Syntax](../AnthillModKbSpec/Resolution/IR/Syntax.lean) | `Kind`, `Predicate`, `Goal` (the literals), `Rule`, `Program`, `Query`; the rendering as `Term` (`Goal.toTerm`, `Program.clauses`, `Program.signature`, `Program.completion`) |
| [IR/Check](../AnthillModKbSpec/Resolution/IR/Check.lean) | The checker (`Program.check`): declarations, data, the left-to-right binding scan; what a passed check gives (`WellFormed`, `QueryOk`) |
| [IR/Evidence](../AnthillModKbSpec/Resolution/IR/Evidence.lean) | Call patterns and the vertex graph (the query's and the denials' calls), levels, data-term outputs and decrease, the notes of P2, S07's ground acyclic case, the split of rigid parameters, `Program.classify` |
| [IR/Semantics](../AnthillModKbSpec/Resolution/IR/Semantics.lean) | The models the answers are about (`Program.Models`, `Program.meaning`), the base of a key model (guards exact, primitives by evaluators, markers free), key fixpoints (`KeyFixpoint`), and that they are the completion's key models |
| [IR/Herbrand](../AnthillModKbSpec/Resolution/IR/Herbrand.lean) | The key fixpoint of a model (`herbrand_fixpoint`), the Herbrand reduction (`herbrand`) |
| [IR/Relevance](../AnthillModKbSpec/Resolution/IR/Relevance.lean) | Possible answers (`Ans`, `Passes`), relevant calls (the query's, the denials', and the relevant atoms'), atoms, and instances, possible answers complete (`ans_complete`), the splitting theorem (`relevant_of_fixpoint`, `fixpoint_of_relevant`), denials read on their passing instances (`denied_iff`) |
| [IR/Parameters](../AnthillModKbSpec/Resolution/IR/Parameters.lean) | What P1 gives a closed query (`p1_parts`), the finite split of rigid parameters (`meaning_split`) |
| [IR/Enumerate](../AnthillModKbSpec/Resolution/IR/Enumerate.lean) | Ground matching, the partial substitutions passing a body (`bodyEnvs`), complete for every passing instance (`bodyEnvs_complete`) |
| [IR/Finite](../AnthillModKbSpec/Resolution/IR/Finite.lean) | Finitely many possible answers per call (`ans_finite`); data-term outputs sound for possible answers (`ans_data`, `passes_flow`); calls at their caller's level keep to the data terms (`same_level_data`) |

## The IR

| Element | Lean | Rendering |
| --- | --- | --- |
| Predicate | `Predicate`: a symbol, its declared modes, its `Kind`: *defined*, *opened* (closed, with a marker case among its rules), *guard*, *primitive* | Defined and opened predicates are closed by the completion (`Program.signature`) |
| Literal | `Goal`: `call p args`, `naf p args`, `equal l r`, `differ l r`, `guard D t`, `primitive f inputs output`, `marker m args` | An atom; `naf` and `differ` as default negations; a primitive's output last |
| Rule | `Rule`: `head(args) :- body` | A definite clause |
| Derived rule | `Program.derived`, the same form | Never in the completion (`Program.derivedClauses`) |
| Denial | `Program.denials`, a body | A goal clause |
| Query | `Query`: conditions, goals, answer names; its other names are rigid parameters | The conditions as a context; the goals, the answer names existentially closed, as a formula |

A program also carries the declared free constructors, the members of the
finite guards (`members`), the decision of every other guard on ground data
(`holdsOf`), and the primitives' evaluators (`evaluate`), with the reserved
`ho_apply` symbol, which no IR predicate is. A finite guard holds exactly of
its listed members (`Program.guardHolds`), so the translator lists them
exactly and the checker verifies they are ground data. Data terms are names,
declared literals, and applications of declared constructors; `subst` and
`Query.instantiate` replace names by terms. The literal type is named `Goal`
(the design's `IR.Literal`): `Literal` is the type parameter of data
literals.

## The checker

`Program.check` returns every blocker (S22) of the program and the query, at
the sites of the rendering: rule `i` is clause `i`, denial `j` clause
`rules.length + j`, a query's condition `i` `.assumption i`, its goal `i`
`.goal` at path `[i]`.

| Check | Blocker |
| --- | --- |
| A call or NAF of a closed predicate at its arity; a guard of arity one; a primitive with its output last; a marker atom that is no declared predicate and not `ho_apply` | A mode for an undeclared predicate or another arity; a term kind for a predicate of another kind; `ho_apply` conversion for the reserved symbol |
| A rule's head a closed predicate at its arity | A guard definition for a guard; `ho_apply` conversion; a term kind or a mode |
| Every argument a data term over the declared constructors, at its argument's path | S23's kinds: a defined operation, a dictionary law, `ho_apply` conversion, a term kind |
| Each symbol declared once, by its name; no predicate named `ho_apply`; a finite guard's listed members ground data terms | A term kind; `ho_apply` conversion; a term kind |
| Read left to right (S23's scan on the IR): a call's inputs bound; NAF, a disequality, and a marker every name; an equation one side; a primitive its inputs; a guard its argument, unless its domain is finite (listed members), when it binds the argument over them. A rule starts from its head's inputs and binds its head's outputs by its end; a denial starts from no name; a query from its rigid parameters, its answer names bound by its end and in no condition | A mode |

What a passed check gives the semantics: `WellFormed` (every rule's head
closed at its arity, its body scanning, every symbol declared once, no
predicate `ho_apply`, finite guards' members ground) and `QueryOk`
(`wellFormed_of_check`, `queryOk_of_check`). An unguarded name passes the
check: it ranges over the carrier, and the query is P2 (decided with the
user, 2026-11-18).

## Evidence: P0, P1, P2

The evidence is read **per call pattern**, not per declared mode: a vertex is
a predicate with the arguments a call binds (`Vertex`, `patternOf`), and
reading a rule under a pattern gives its calls' patterns (`successors`). The
query `path(a, c)` reaches `path` with both arguments bound, `∃Y. path(a, Y)`
with the second free, so the same program is P1 for the first and P2 for the
second. The vertices the query and the denials reach are closed by
saturation (`Program.vertices`, checked closed: `Program.closed`); the
denials join every query's graph (decided with the user, 2026-11-18). A
vertex's **level** counts the vertices it reaches that do not reach it back
(`Program.levelTable`, by S23's `reach`); the graph, the levels, and the
data-term outputs are computed once per classification (`Program.notes`). In
a closed graph no call goes to a higher level (`levelIn_le`), and every vertex
of a checked query binds its predicate's declared inputs
(`covering_of_check`), so neither needs a note. What no note gives is
`Program.Evidence` (`evidence_of_notes`).

| Note (P2) | When |
| --- | --- |
| `growingCall` | A call at its caller's level whose bound arguments are not data terms of its caller's bound arguments (S23's `Frame.small`, with data-term outputs read per vertex: `dataOutputs`) |
| `freeOutput` | A call that leaves an output free, from a vertex that leaves one free, at a level no lower and not decreasing (its bound arguments subterms of the head's, one strictly): a self-supporting cycle may hold of unboundedly many values in the greatest fixpoint |
| `unguarded` | A name of a rule or a denial, or an answer name, that no guard literal guards: it ranges over the carrier, outside the Herbrand reduction |
| `parameter` | A rigid parameter that no finite guard among the conditions splits |
| `unclosed` | The vertex closure did not end within its bound |

Across components a body may construct a lower component's input
(`p(X) :- q(succ(X))`) and grow a term at each call (`dup` thirteen times in
a row): neither is a note; the bound composes along the levels, each rule
instance being finite. **P1** is a well-formed closed query with no note;
**P2** one with notes, run by the same evaluator with fuel (S28); **P0** S07's
ground acyclic case with no note: ground rules of calls and NAF, no denial,
no derived rule, no opened predicate, a ground query of calls and NAF, and no
atom depending on itself (`Program.ground`; S07 ranks atoms, so
`p(a) :- p(b). p(b).` is P0), so P0 ⊂ P1 by construction.
`Program.classifyClosed` reports Undecided with the checker's blockers first,
then P0, P1, or P2 with its notes (`classifyClosed_decides`,
`classifyClosed_p0`); a query with rigid parameters is classified through its
split (`classify_split`, below), and `p1_parts` gives what P1 gives the
theorems below. Derived rules are checked as rules, and stay outside the
completion, the vertex graph, and the relevant program: a decision that
derives with them (S28's certificates, S31) bounds them itself.

## Semantics

The answers are about the models of the rendering's completion with
complement NAF that realize the program's guards (exactly the ground data
terms they hold of, a finite guard its listed members) and primitives (exactly
their evaluations):
`Program.Models`, and `Program.meaning`, S22's `Meaning.ofModels` over them.
Over constructor keys, S24's consequence operator reads the closed atoms from
an interpretation and the rest from `Program.base`: guards exact, primitives
by their evaluators, markers free.

| Property | Theorem |
| --- | --- |
| The rendering is covered (S24) | `Program.covered` |
| Key fixpoints are exactly the completion's key models | `keyModel_models_iff` (S24's `fixpoint_iff_models`) |
| Every key fixpoint is a model the answers are about | `keyFixpoint_models` |
| A model's atoms over the keys of ground data terms are a key fixpoint, for a guarded program | `herbrand_fixpoint` |
| Every literal, and a closed query's conditions and formula, have the same truth in a model and in its key fixpoint | `goal_iff`, `body_iff`, `query_iff` |
| **The Herbrand reduction**: for a guarded program and a closed query, Yes, No, and Unknown mean the same over the models and over the key fixpoints | `herbrand` |

The reduction rests on the completion's equality theory, which makes the
declared constructors free in every model (S24's `free_of_equality`), and on
the guards, which hold only of ground data terms' values.

## Relevance

A closed query's relevant program is the set of ground rule instances its
calls and the denials' calls can use, for the answers they derive and for
those they may have in some model. A query with rigid parameters is read
through its split's instances, each closed.

| Notion | Lean |
| --- | --- |
| Possible answers of a vertex: heads of its rules' passing instances | `Ans` |
| An instance passes a body: fixed literals true, every call leaving an output free at a possible answer | `Passes` (with `Ans`, one mutual inductive) |
| Relevant calls: of the query's passing instances, its conditions, the denials' passing instances, and every relevant atom's passing instances | `Relevant` |
| A relevant atom at a vertex, a relevant instance | `Entry`, `RelevantAtom`, `Instance` |

| Property | Theorem |
| --- | --- |
| In every interpretation supported by its rules, every atom a free vertex may answer is a possible answer: by induction on the level, then the size of the bound arguments, a free call going lower or decreasing (`call_rank`) | `ans_complete` |
| A key fixpoint satisfies the relevant program's completion at every relevant atom | `relevant_of_fixpoint` |
| An interpretation satisfying the relevant program's completion at the relevant atoms, and the completion elsewhere, with denials false, is a key fixpoint | `fixpoint_of_relevant` |
| In an interpretation supported by its rules, the denials hold exactly when every passing denial instance has a false body | `denied_iff` |
| A rule's passing instances extend partial substitutions the enumeration computes | `bodyEnvs_complete` |
| With the evidence, a vertex leaving an output free has finitely many possible answers at each value of its bound arguments: by induction on the level, then the size, the lower calls' answers from the induction | `ans_finite` |
| A possible answer of a vertex with data-term outputs is a data term of its bound arguments and the program's ground terms (the closed data subterms of the rules and the finite guards' members); the flow's names hold data terms along a passing instance | `ans_data`, `passes_flow` |
| A call a passing instance makes at its vertex's level has bound values that are data terms of the instance's bound head values | `same_level_data` |

## Rigid parameters

Decided with the user, 2026-11-18. A rigid parameter ranges over the carrier
unless the conditions restrict it. A finite guard among the conditions splits
the query into one ground query per assignment of members
(`Program.splitValues`, `Query.instantiate`); the query is P1 when every
instance, classified as a closed query, is P0 or P1 (`classify_split`), and
its meaning is theirs (`meaning_split`): Yes exactly when every instance's
truth holds, No exactly when every instance's falsity holds, Unknown exactly
when one instance is not No and another is not Yes. An instance whose
conditions no model satisfies is both Yes and No, so the combination reads
meanings: "Unknown when neither all are Yes nor all are No" holds only when no
instance is vacuous (S26 settles vacuous contexts). A checked program's finite
guards list ground members and hold exactly of them
(`enumerates_of_wellFormed`). Every other parameter, unguarded or over an
infinite domain, is P2. Genericity over values outside the relevant data
terms is not taken.

## Traces

| Trace | Profile |
| --- | --- |
| `path` over the cycle `a ↔ b`, every name guarded: `path(a, c)` | P1; three vertices, `path` on a cycle |
| The same: `∃Y. path(a, Y)` | P2, a free output on the recursive call |
| The lowered program, guards over `D_all` | P1 |
| `append(+, +, −)`: `∃Z. append([a], [b], Z)` | P1: the component decreases |
| `count(+, −)` with its output free; with it bound | P2, a free output; P1 |
| `grow(X) :- grow(succ(X))` | P2, a growing call |
| `p(X) :- q(succ(X)). q(Y).`; thirteen `dup` calls in a row | P1; P1 |
| An unguarded name | P2 |
| `path(x, c)` with `x` a parameter; with `node(x)` a finite guard; with `D_all(x)` | P2; P1, its three instances each P1; P2 |
| `∃Y. path(x, Y)` with `node(x)` | P2: each of the three instances has a free output |
| `p(a) :- q(a), naf r(a). q(a).`; a ground cycle; `p(a) :- p(b). p(b).` | P0; P1; P0 (S07 ranks atoms) |
| `q(a). ⊥ :- q(a).`; `p(a) :- a = a.` | P1, not P0: S07's fragment has no denials and no equations |
| `p(a) :- naf q(a). q(a) :- naf p(a). ⊥ :- p(a).`, query `p(a)` | P1, the denial's call in the graph |
| `path(a, c)` with the denial `⊥ :- path(a, Y), node(Y)` | P2: the denial's free output on the cycle |
| An unbound input; a guard binding over an infinite domain; a finite one binding | Undecided; Undecided; checked |
| An undeclared predicate; a formula inside data; a symbol declared twice; a predicate named `ho_apply`; a finite guard's member not ground | Undecided |
| A duplicated symbol; an unbound input at goal 1; a defined operation in an argument | Blockers naming the symbol; at `.goal`, path `[1]`; at the body literal, path `[0]` |

## Boundaries and open points

- **Finiteness and computation of the relevant program.** Possible answers
  are finitely many per call, and calls at their caller's level keep to the
  data terms; that the relevant calls are finitely many (by the levels, entry
  calls coming from the query, the denials, and higher levels), and the
  relevant program computed with its sizes in the traces, are still open on
  S27.
- **S07's `P0.Ground` as the ground acyclic case.** `Program.ground` reads
  S07's class; the embedding of every `P0.Ground` is still open on S27.
- **Exactness** over the relevant program is S28's: a model of the relevant
  program's completion extends to a model of the whole only when the rest of
  the KB allows it (an unreached `r(a) :- p(a), naf r(a)` forces `p(a)`
  false), and S28 answers Unknown only when no rule outside the relevant
  program reads a relevant atom under NAF on a cycle (decided with the user,
  2026-11-18). The evaluator, cost classes, and certificates are S28's; the
  translation from `Term` S29's.
- **Cost of the classifier.** The graph, the levels, and the data-term outputs
  are computed once. The data-term check compares terms, so facts over long
  nested terms (`succ⁴⁰⁰(zero)`) cost more than the graph: a chain of 100
  such edges classifies in about a second, of 400 in about 50 s; S17 owns
  performance.
