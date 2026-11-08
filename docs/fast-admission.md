# The fast fragment's admission (S23)

S23 implements the admission side of [fast evaluation](fast-decision-routes.md).
Before anything runs, it classifies every predicate of a KB program, and every
query, into **P1**, **P2**, or **Undecided** with blockers, for S24's tabled
evaluation. It changes nothing in the machine. Traces are in
[Tests/Resolution/Tabled/Admission.lean](../Tests/Resolution/Tabled/Admission.lean).

| Module | Contents |
| --- | --- |
| [Tabled/Graph](../AnthillModKbSpec/Resolution/Tabled/Graph.lean) | Reachability by saturation (`reach`, `reach_iff`) and greatest post-fixpoints by deflation (`greatest`, `greatest_post`, `greatest_ge`) |
| [Tabled/Fragment](../AnthillModKbSpec/Resolution/Tabled/Fragment.lean) | Modes, the fragment's `Program`, the call view (`callOf?`, `io?`), the data-term analysis (`flow`, `sites`), the safety scan (`scan`), data and construct blockers |
| [Tabled/Admission](../AnthillModKbSpec/Resolution/Tabled/Admission.lean) | The dependency graph, data-term outputs, cost classes, notes and blockers, `Class`, `Profile`, queries (`admit`, `answer?`), `Program.ofInput` from S07's program input |
| [Tabled/Calls](../AnthillModKbSpec/Resolution/Tabled/Calls.lean) | The evaluation model (`Binds`, `CallIn`), data terms (`InData`, `dataTerms`), the soundness of the analysis, and the call bound (`calls_bounded`, `outputs_bounded`, `calls_decrease`) |
| [Tabled/Classes](../AnthillModKbSpec/Resolution/Tabled/Classes.lean) | What each check decides, locality, profiles, determinism |

## Inputs

`Program` holds what admission reads: the KB clauses with their indices (the
sites of blockers), the declared free constructors by symbol and arity, the
guard symbols, the unknown markers, the `ho_apply` symbol, and the **mode
declarations** (`Modes`): for each predicate symbol, the mode of each argument
position, input or output. The KB generator emits modes with the clauses, as it
emits explicit binder ranges; they are never inferred. A predicate without a
mode, or called at another arity, is a blocker. `Program.ofInput` builds the
program from S07's `ProgramInput`: the effective program's KB clauses as
lowering gave them, with their range guards, and the signature's guard symbols.

A `Query` has a context, a goal, and its **answer names**, which are flexible
and declared, never inferred. The query's other free names are rigid
parameters.

## Safety

`scan` reads a body left to right with the names bound so far and the rigid
names in scope. A violation is an Undecided blocker (S22) lacking a mode, at
its site and path.

| Goal | Rule |
| --- | --- |
| A predicate call | Its mode is declared at its arity; its inputs' names are bound or rigid; its outputs' names are bound after it. A concrete `ho_apply(p, args)` is the call `p(args)` (S11's `ho_goal`) |
| A range guard | Its arguments are data. It waits until its name is bound, as S06 delays it, and by the end of its scope (the clause body, the existential or universal that binds the name, or the NAF operand) its names must be bound, or constrained by a constructive NAF, which S21 decides with the guard by disunification with domain closure. Lowering puts guards first (`path(X, Y) :- D_all(X), D_all(Y), …`), so the rule reads "earlier positive goal" as "a goal of the same scope" for guards |
| A marker atom | Its names are bound or rigid |
| `s = t` | One side's names are bound or rigid; the other side's are bound after it |
| `naf A` | Ground in data (every name bound and flexible): finite failure. A flexible name or a rigid one needs constructive negation (S21): the operand is scanned with those names unbound, so an operand input on one of them is a blocker, and the operand's predicates must be complete, or the NAF lacks a termination argument: its answers may be infinite (`naf nat(X)`). Its unbound flexible names are constrained, not bound |
| `∃x. G` | `x` is unbound in `G` |
| `∀x. G` | `x` is rigid in `G`; P2, since a failure is Undecided |
| `D → G` | `D` is a Harrop clause with its names bound or rigid, or the goal is outside the fragment; its atoms' data and its rules' bodies are scanned for constructs outside the fragment, the rules' safety being S26's. A closed conjunction of atoms is decided, read materially; any other antecedent is P2 and budgeted (`hypothesis`) |
| A head output | Bound by the end of the body |

The query's goal is scanned with its rigid parameters and no bound name, and
every answer name must be bound by its end. A context assumption may be an
atom, a conjunction, a disjunction (split eagerly, S26), an existential, or a
Harrop rule, which is P2 and budgeted (`localRule`), its body scanned as an
antecedent's.

## Data terms and cost classes

The **data terms** of a call are the subterms of its input values and of the
program's ground terms; a query adds its context's and goal's
(`queryConstants`), since its context facts answer them. `flow` marks the names that hold data terms: subterms of
the head's inputs that no binder rebinds, ground terms, and the output names of
a call with data-term inputs to a predicate with **data-term outputs**. The
predicates with data-term outputs are the greatest post-fixpoint of the check
that every head output is a data term at the end of its body (`dataOutputs`).

A predicate is **complete** when, in every clause of its dependency closure,
every recursive call's inputs are data terms, its component **settles** (every
member has data-term outputs, or every recursive call in it decreases: each
input a subterm of the head input at its position, one strictly), and no
hypothesis is undecided. Otherwise it is **budgeted**, and growth notes name
the growing call or answer.

Decided with the user, 2026-11-07: bounding the calls alone does not bound the
answers. `count(X, zero). count(X, succ(Y)) :- count(X, Y).` with mode (+, −)
makes one call and has infinitely many answers, so it is budgeted, naming its
growing answer. `append(+, +, −)` constructs its output and decreases on every
recursive call: complete. `path(+, −)` over facts calls `path(Z, Y)` with `Z`
an output of `edge`, a predicate with data-term outputs: complete.

| Class | What is guaranteed (`Tabled/Calls`) |
| --- | --- |
| Complete | From a ground input, every call the component makes, transitively, has inputs among the data terms of the first call: at most `|component| · |dataTerms|ᵃ` calls of arity `a` (`calls_bounded`, `calls_dataTerms`). With data-term outputs, every answer is a data term of its call (`outputs_bounded`); in a decreasing component every recursive call is smaller (`calls_decrease`), so no call repeats |
| Budgeted | Bounded by S24's fuel; may answer Undecided |

The theorems are stated for any ground terms covering the program's and any
answer relation in which predicates with data-term outputs answer data terms
of them (`AnswersBounded`). Every derivable answer
does, by induction on derivations, and `outputs_bounded` is the step of that
induction. A call into a lower component is that component's entry, and the
theorems apply to it in turn.

The **degree** of a predicate is the most names a clause of its dependency
closure joins: its free names and those its quantifiers bind. Over n data terms, a clause has at most nᵏ
instances. Where outputs are constructed (`append`), the degree is no cost
claim: the recursion terminates, but its answers may be exponential
(`subset(+, −)`). A predicate is **deterministic** when, at some input position
of every two clauses, a literal or a declared constructor clash separates the
patterns (`Completion.mayMatch`). Then no input matches two clauses
(`deterministic_unique`).

## Profiles and blockers

| Profile | When |
| --- | --- |
| **P1** | No blocker and no note in the dependency closure; complete (`p1_complete`) |
| **P2** | No blocker, some note: a growing call or answer, an undecided hypothesis, a generic universal goal, NAF whose operand reaches a predicate on a cycle, a denial over a predicate on a cycle, a rule the query's context assumes |
| **Undecided** | A blocker in the dependency closure, before anything runs |

Blockers reuse S22's `Missing` and S07's capabilities. A predicate call with an
unbound input, a guard whose name no goal binds, an unbound head output, or a
predicate without a mode lacks a **mode**. A NAF whose operand may have
infinitely many answers lacks a **termination** argument. A construct outside
the fragment lacks its **construct**:

| Construct | Capability or construct |
| --- | --- |
| A compound head or a concrete `ho_apply` head: the completion leaves the predicates it may conclude open (`Completion.headOpens`) | `compoundHead`, `hoApplyConversion`, at each such predicate |
| A formula-variable head, or a head applying a predicate variable: it may conclude any predicate, and the completion closes none | `formulaVariable`, `hoApplyConversion`, at every predicate |
| A KB clause concluding a guard atom or an unknown marker | `guardDefinition`, `unknownMarkerDefinition`, at every predicate |
| A head that is no formula: a literal, a dictionary call | `termKind`, `dictionaryLaw`, at every predicate |
| A formula variable or a literal as a goal; `ho_apply` of a predicate variable, also in an antecedent; `ho_apply` inside data | `formulaVariable`, `termKind`, `hoApplyConversion` |
| A data symbol that is no declared constructor: a defined operation | `operation` |
| A dictionary call (S14 evaluates operations) | `dictionaryLaw` |
| A non-Harrop antecedent or context assumption | `scopedProof`, lacking a proof |

Equations conclude no predicate: they are statements (`statements`) and block
none; a defined operation is blocked where it occurs in data. A denial,
`⊥ :- body` or `false :- body`, is scanned from no bound name. Its notes reach
every predicate whose closure meets the predicates its body reaches. Its
blockers are shared by every predicate and query (`sharedBlockers`): a denial
the module cannot check leaves the KB's consistency open, and every answer
assumes it.

## Locality

A predicate's class follows from its own clauses, the denials over it, and the
classes of the predicates it calls. The classes carry what callers read: the
predicates they reach, data-term outputs, and completeness. A query's class
reads them over the predicates it uses: it is complete when they are and it
has no growth note of its own (a hypothesis, a context rule), and
deterministic when they are.

| Property | Theorem |
| --- | --- |
| Blockers: its own, the shared ones (global and every denial's), its callees' | `mem_blockers` |
| Notes: its own, the denials over it, its callees' | `mem_notes` |
| Complete exactly when locally complete with every callee complete | `complete_iff` |
| The degree: its own clauses' width and its callees' degrees | `degree_le` |
| A query's blockers: its own, the shared ones, those of the predicates it uses | `mem_queryBlockers` |

## Guarantees

| Property | Theorem |
| --- | --- |
| `reach` is the transitive closure of the dependency edges | `reach_iff`, `Tabled.reach_iff` |
| Data-term outputs are the greatest post-fixpoint of the local check | `dataOutputs_post`, `dataOutputs_greatest`, `flow_mono` |
| Budgeted exactly when a growth note in the closure names the growing call, the growing answer, or the hypothesis | `complete_iff_growth` |
| The profiles: P1 with no blocker and no note, P2 with notes, Undecided with blockers; P1 is complete | `profile_p1`, `profile_p2`, `profile_undecided`, `p1_complete`, `p1_notes` |
| Every name `flow` marks holds a data term after any evaluation against bounded answers; every call `sites` marks small has data-term inputs, every one it marks decreasing has smaller inputs | `flow_sound`, `site_of_call`, `Holds.decreasing` |
| A complete predicate has finitely many distinct calls from any ground input, within its component | `calls_bounded`, `calls_dataTerms` |
| Data-term outputs give data-term answers; a decreasing component's recursive calls are smaller | `outputs_bounded`, `calls_decrease` |
| No input matches two clauses of a deterministic predicate | `deterministic_unique`, `mayMatch_sound` |
| An Undecided admission is S22's Undecided answer, before anything runs | `answer?_undecided` |

## Traces

| Trace | Result |
| --- | --- |
| `reachable(+)`: `reachable(zero)`, `reachable(succ(X)) :- reachable(X)` | P1, complete, cyclic, degree 1, deterministic |
| `append(+, +, −)` | P1, complete, constructed outputs, degree 4, deterministic |
| `path(+, −)` over `edge` facts | P1, complete, data-term outputs, degree 3, not deterministic; the lowered form with prepended guards is P1 too |
| `grow(X) :- grow(succ(X))` | P2, budgeted, naming the growing call |
| `count(+, −)` | P2, budgeted, naming the growing answer |
| `q :- r`, `r :- q`, `p :- naf q` | `p` P2 (NAF over a predicate on a cycle), `q` P1; NAF over a predicate off any cycle is P1 |
| `p(X) :- naf nat(Y)` with `nat(−)` budgeted | Undecided: the operand may have infinitely many answers |
| `p(X) :- naf isZero(Y)` with `isZero(−)` | P1: constructive negation over a complete operand |
| `p(X) :- naf q(Y)` with `q(+)` | Undecided: an unsafe NAF, the operand's input unbound |
| `p(a) ∧ q(a)` as a head | `p` and `q` Undecided at the head; an unrelated predicate P1 |
| A call with an unbound input; a predicate without a mode; an unbound head output | Undecided, lacking a mode |
| A generic universal goal; a hypothesis with a data name; a closed atomic hypothesis | P2; P2 and budgeted; P1 |
| A non-Harrop antecedent | Undecided at the antecedent |
| A denial over a predicate on a cycle | P2 for the predicates it constrains, P1 for the others |
| A formula-variable head; a head applying a predicate variable | Every predicate Undecided |
| An equation | A statement: no predicate blocked |
| A defined operation in data | Undecided |
| `ho_apply(q, X)` concrete; `ho_apply(P, X)` flexible | The call `q(X)`, P1; Undecided |
| An open predicate `q(a) :- unknown` | P1 |
| A blocker in a predicate `p` does not call; in a callee | Not `p`'s; inherited, as budgeted is |
| Queries: `path(a, Y)` with answer `Y`; `path(X, b)` with answer `X`; an answer no goal binds; a parameter as an input | P1; Undecided; Undecided; P1 |
| `naf edge(a, x)` with `x` a parameter at an output; `naf edge(x, b)` with `x` at an input | P1; Undecided |
| A query using a budgeted predicate | P2 |
| Context facts and splits; a context rule; a negated assumption | P1; P2, budgeted; Undecided |
| `answer?` on an unsafe query; on a P1 query | Undecided with its blocker; none, the run answers |
| A lowered clause whose guard's name no goal binds | Undecided, two mode blockers |
| Lowered `p(X) :- naf isZero(Y)`: the guard `D_all(Y)` on a name the NAF constrains; `p(X) :- isNat(Y), naf isZero(Y)` | P1; P1 |
| A denial with a `false` head over a predicate on a cycle | P2 for the predicate |
| A denial with a dictionary call and no predicate | Every predicate Undecided |
| A literal or a dictionary call as a head | Every predicate Undecided |
| A formula variable in an antecedent rule's body; a dictionary call in a context rule's body | Undecided at the rule body |
| `ho_apply(P, a) → q(X)`; `ho_apply(q, f(a)) → q(X)` with `f` a defined operation | Undecided; Undecided at `f(a)` |
| `p(X) :- isNat(f(X))` with `f` a defined operation | Undecided at the guard's argument |
| `path(X, Y) :- ∃Z. edge(X, Z) ∧ path(Z, Y)` | Degree 3, as with an implicit `Z` |
| A query with its own hypothesis; a query over `path` | Budgeted; complete and not deterministic |

## Boundaries

- **Per component.** The call bound is stated within a predicate's component.
  Whole-run termination composes it along the component order, with finitely
  many answers per call (`outputs_bounded`, `calls_decrease`). S24's tables
  are keyed by these calls ([tabled evaluation](tabled-evaluation.md)); the
  composition into a fuel-free bound on its runs is not yet proved.
- **Cycles are predicate-level.** NAF or a denial over a predicate on a cycle
  is P2 even when the recursion decreases, as in `naf reachable(x)`.
- **Constructive negation reads rigid names unbound.** A NAF on a parameter at
  an operand input is a blocker, since the operand's answers are equations on
  that name. S21 runs constructive negation; S23 only admits it.
- **Decided antecedents** are closed conjunctions of atoms. A rule or an
  antecedent with data names is P2 and budgeted; contexts are S26's.
- **Constructors are declared.** Data symbols must be free constructors: a
  defined operation is a blocker, and determinism compares only declared
  constructors and literals.
- **Consistency.** P1 answers are Yes, No, or Unknown for a consistent KB. A
  denial whose body is Yes makes every answer Undecided; S24 checks it at run
  time (`Setup.denialCheck`).
- **Dictionary operations** are blockers until S14 evaluates them.
