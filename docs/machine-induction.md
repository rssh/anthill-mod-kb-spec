# Admitted induction

S12 admits structural induction for a guarded universal `∀x:D. p(x)` over any
declared inductive domain and proves the Nat example. It builds on S11's
[whole-formula head selection and conversion](machine-conversion.md), the
[S03 lowering](guarded-elaboration.md), the [S09 left strategy](machine-left.md),
and the [S08 checker](proof-checking.md). Each principle is an ordinary KB
clause with a proved validity theorem; no induction rule is added to `Derives`.
Traces are in [Tests/Resolution/P3/Induction.lean](../Tests/Resolution/P3/Induction.lean).

| Module | Contents |
| --- | --- |
| [P3/Principle](../AnthillModKbSpec/Resolution/P3/Principle.lean) | The structural principle of a domain from its rules (`source`, `ranges`, `rangeOf`, `principle`, `lower_principle`, `lower_rejects`), admissible names (`Admissible`, `admissible?`), its validity (`principle_valid`) |
| [P3/Induction](../AnthillModKbSpec/Resolution/P3/Induction.lean) | The target goal (`Target`, `target?`), admission (`CaseGap`, `dependencies`, `contextGaps`, `casesGaps`, `carried?`, `Need`, `check`, `Plan`, `check_input`), the plan's strategy (`guardSplits`, `Plan.selection`, `Plan.run`, `Plan.selection_focus`, `Plan.body_unfocused`, `Plan.lowered`), what a run establishes (`Plan.reconstructs`, `Plan.models`, `Plan.sound`, `Plan.not_p0`) |

## The principle

Every declared domain `D` has a structural principle, generated from its
listed constructor rules. For each rule `c : D₁ × … × Dₖ → D` it has one case:

```text
(G_D(x) → ho_apply(P, x)) :-
    …, ∀y₀:D₁ … ∀yₖ₋₁:Dₖ. (ho_apply(P, yᵢ) → … → ho_apply(P, c(y₀, …, yₖ₋₁))), …
```

- Each field is bound and guarded by its domain.
- Every field of `D` itself has an induction hypothesis.
- A field of another domain, a mutually recursive one included, is guarded and
  gets no hypothesis: the principle is for `D` alone.

`G_D` is the range guard of `D` (S03), so the head concludes exactly the focus
`G_D(a) → p(a)` that opening the lowered goal leaves. Some domains:

| Domain | Cases |
| --- | --- |
| Nat (`zero`, `succ`) | `ho_apply(P, zero)`; `∀y₀:Nat. (ho_apply(P, y₀) → ho_apply(P, succ(y₀)))` |
| Bool (`tt`, `ff`) | `ho_apply(P, tt)`; `ho_apply(P, ff)` |
| Lists of Nat (`nil`, `cons`) | `ho_apply(P, nil)`; `∀y₀:Nat. ∀y₁:List. (ho_apply(P, y₁) → ho_apply(P, cons(y₀, y₁)))` |

The source clause is lowered by `elaborateClause?` with `P` at `.predicate 1`
and the target at `.carrier`. The binder ranges of each case come from
`ranges`. Lowering adds the guard `P_1(P)` once (`clauseGuards` adds one guard
per free name) and each field's guard. `principle` builds the lowered clause
with the guards in place, and lowering the source gives exactly it for
admissible names (`lower_principle`): no field shadows `P`, and no constructor
is `ho_apply`. A range on `P` that admits no unary predicate, a data range
or `D_all`, is rejected (`lower_rejects`).

**Validity is a theorem.** `principle_valid` holds in every model realizing the
signature. The domain's exact realization (S02) makes its members the values
built by its rules, the least such set. A property satisfying every case
therefore holds of every member, for every value of `P`, by induction on
`Member`: the case of the rule that built a value applies to its children's
values, with hypotheses for the children of `D`. The proof uses only the data
realization. `P_1(P)` restricts which references the principle is applied to,
and registering a predicate proves nothing about induction.

## Admission

`check hoApplySymbol input` decides before anything runs:

1. **Declarations.** The program's signature clauses are the signature's own,
   and none is missing, as P0 checks them. Otherwise the result is `invalid`.
2. **Shape.** The goal is the lowered `∀x. G_D(x) → p(x)` over one declared
   domain (`target?`; otherwise `shape`).
3. **Registration.** `p` is registered at arity 1, so `P_1(p)` has its
   generated fact (otherwise `registration p`).
4. **The principle.** The program carries a clause whose names, read off it
   (`namesOf?`), generate it (`carried?`), whatever names the generator chose
   (otherwise `principle`). The names must be admissible: each case's fields
   distinct and none the predicate, the target not the predicate, and no
   constructor `ho_apply` (otherwise `names`). Lowering the source then gives
   the principle (`lower_principle`), so admission lowers nothing.
5. **What the cases search.** Neither the query's context nor a clause a case
   may select holds a formula the cases cannot run (`contextGaps`,
   `casesGaps`). Each such formula is a `CaseGap` at its site and path,
   reported as a `context` or a `clause` need:
   - NAF as a goal (`negation`): the plan's run is the left strategy alone,
     with no NAF route;
   - a range guard on a name no other goal of its clause mentions
     (`waitingGuard`): positive search delays a guard until a goal binds its
     name, and none can;
   - P0's other requests (`capability`), a formula variable as a goal, an
     assumption, or a head among them (`formulaVariable`), apart from ground
     instances of data, which P3 search does not need, and range guards: a
     guard goal is decided by its atoms, and a guard assumption is split at a
     guard goal on its term (below). Any other non-atomic assumption, NAF
     included, is a `scopedProof` request: it is a hypothesis, and the plan's
     selection chooses no left rule on it.

   The clauses in question are those concluding a symbol reachable through
   clause bodies from what the principle's premises ask, `p` and the guard
   `P_1` or a denial's body asks, plus every head applying a predicate by
   `ho_apply`, since such a head meets any call through its indirect view;
   every head that is a formula variable, which may meet any goal; and every
   denial `⊥ :- body`, which serves any `false` subgoal, such as ex falso asks
   (`dependencies`). A denial is run as a clause for `false`, so only its body
   is checked. A KB clause concluding `P_1` is reported (P0's
   `guardDefinition`), and so is an atomic induction clause
   `ho_apply(P, x) :- …`, which positive search would select again on every
   unary call. The base and the other cases search the same clauses, so the
   needs are not split by case.

Every shortfall is a `Need` listed together. Recursive definitions with
variables are not gaps: P3 search does not ground them. A clause outside the
dependencies is not reported. A Ready `Plan` records its input
(`check_input`) and what admission established. It says nothing about whether
the goal holds.

## The strategy

`Plan.run fuel` is one run of the left strategy committed to the plan's
selection (`leftCommitted`), on the program from the query: where the
selection chooses commands, they are the only ones offered. It chooses:

- `headMatch` of the principle exactly at a focus `G_D(e) → p(e)`
  (`Plan.selection_focus`). The implication's introduction is not offered
  there: depth-first, it would be tried first, and a valid looping clause such
  as `reachable(z) :- reachable(z)` would keep the principle from being tried.
- `disjCases` on a guard assumption `m(t) ∨ rest` at a guard goal on the same
  term `t`, when neither side is assumed yet (`guardSplits`). A case assumes
  each field's guard in this form; the split adds `m(n)`, which closes a guard
  atom on the field or its membership subgoals before the generated clauses
  (`isNat(v) :- isNat(v)` for `D_all = isNat` would loop), and its `false`
  case closes by ex falso. The split is invertible.

The run then:

- opens the universal at a rigid `a` (S06), and the selection matches the
  focus against the principle's whole head through its indirect view (S11):
  `x := a`, `P := p`;
- proves the body instance: the guards `P_1(p)` by the generated fact, and
  each case by opening its fields at fresh rigid names, assuming their guards
  and hypotheses, and proving `p(c(y⃗))` by `ho_goal` and `p`'s clauses, a
  hypothesis converted to `p(yᵢ)` where it is used. For Nat these are the
  base `p(zero)` and the step `p(succ(n))` under `G_Nat(n)` and the hypothesis
  for `n`;
- finishes the focus once, by the clause node converted under the
  implication.

**The principle is not selected again at its own premises.** No premise of
the principle, under any substitution, is a focus (`Plan.body_unfocused`): its
guards are atoms or truth, a case without fields an atom, any other case a
universal. The goals a case opens are its matrix under its assumptions,
concluding a call by `ho_apply`, and `positive` never selects a compound head
for an atomic goal. The theorem does not cover those opened goals: a clause a
case selects may ask a focus again, a nested induction, which the selection
answers by the principle. The run is bounded by its fuel: an
interrupted run is Undecided, never failure ([answers](answers.md)); S12's
needs are Undecided blockers before anything runs (`Induction.answer`). Induction search is P3. Failure of
a case for this predicate does not refute the universal, and a decision
request for the universal is not answered by this plan: P0 asks evidence for
it (`Plan.not_p0`).

## What a successful run establishes

- `Plan.reconstructs`: `Derives` for the guarded universal in the program's
  KB, for any NAF provider, since the run builds no NAF node.
- `Plan.lowered`: lowering the source gives the principle the plan applies.
- `Plan.models`: the program's KB is valid in a model realizing the signature
  once its other clauses are; the principle is valid by `principle_valid`.
- `Plan.sound`: the guarded universal is true in every such model, under
  every environment satisfying the query's context.

In the induction model, `universal_holds` combines these with
`InductiveSoundness.declarative_sound`. Any successful run of the admitted plan
makes `∀x:Nat. reachable(x)` true there.

## The exported proof

The run's tree exports as S08 nodes (`exportTree`, `exportProof`):

- the universal's introduction at `a`;
- the conversion under the implication: a cut, implication introduction and
  elimination, `hoApplyElim`;
- the principle's clause node with its explicit instantiation `P := p`,
  `x := a`;
- the guard nodes on the generated fact, and one subtree per case, each
  scoped by its fields' openings and assumptions.

The checker decides each node by its own procedure and repeats no matcher
search. Acceptance of an exported tree is decided per run, as the traces do;
that every successful run exports an accepted tree belongs to S15/S16. The
universal and the intermediate formulas have no P1 discovery plan, yet the
explicit-proof route accepts the tree (R29). A tree with the instantiation
forged to another predicate, or citing another domain's principle at the
focus, is rejected, and so is the genuine tree checked against a KB that does
not carry the principle.

## Guarantees

| Property | Theorem |
| --- | --- |
| A range on `P` that admits no unary predicate is rejected; lowering with `P` at `.predicate 1` gives the principle for admissible names | `lower_rejects`, `lower_principle`, `Plan.lowered` |
| The principle of every declared domain is valid in every model realizing the signature | `principle_valid` |
| Admissible names are decided | `admissible?_spec` |
| A Ready plan is for exactly the input checked, and applies a principle the program carries | `check_input`, `carried?_spec` |
| A Ready plan's context and the clauses its cases may select have no gaps | `Plan.context_clear`, `Plan.cases_clear` |
| The principle is chosen only at a focus, and never at one of its premises under any substitution | `Plan.selection_focus`, `Plan.body_unfocused` |
| A successful run reconstructs `Derives` for the guarded universal | `Plan.reconstructs` (with `leftCommitted_reconstructs`) |
| The universal is true in every realizing model satisfying the other clauses | `Plan.models`, `Plan.sound` |
| The universal has no P0 plan | `Plan.not_p0` |

## Traces

| Trace | Result |
| --- | --- |
| The principle for Nat, lowered with `P` at `.predicate 1`; with `D_all` or a data range on `P` | The lowered clause; rejected (`lower_rejects`) |
| The principles for Nat, Bool, and lists of Nat | Generated from the rules: Bool's two cases without fields; the list's `cons` case guards its Nat field, with a hypothesis for the tail only; each lowers to its principle |
| Admission of `∀x:Nat. reachable(x)` in the induction model | Ready; P0 asks scoped-proof evidence for the goal itself |
| `∀x:Nat. zero(x)`; `∀x. isNat(x) → reachable(x)` or an atom; no principle in the program | `registration`; `shape`; `principle` |
| A disjunctive body among the dependencies; the atomic induction clause added; NAF in a dependency; a clause concluding `P_1`; a formula variable as a goal | A `clause` need (scoped proof); a `clause` need at its `ho_apply` head; `negation`; `guardDefinition` at its head; `formulaVariable` |
| A guard on a name no other goal mentions; on a name another body goal binds; a disjunctive query assumption; an unrelated disjunctive clause | `waitingGuard`; Ready; a `context` need; Ready |
| A denial with NAF, and one without; a formula variable assumed, and as a head; NAF assumed; a guard assumption `isNat(zero) ∨ false` | `negation` at its body; Ready; `formulaVariable` each; `scopedProof`; Ready |
| The run | Success: the principle applied once at the focus, `P := reachable`, `x := a`; one guard `P_1(reachable)` by the generated fact; base by `ho_goal`; the step at a fresh `n` with `isNat(n)` and the hypothesis converted |
| A valid looping clause `reachable(z) :- reachable(z)` added; a step clause with an atomic guard `isNat(x)`; the principle generated with other names | Success: the principle is the one command at the focus; the field's guard split at the guard goal (`disjCases`); the principle found and the same run |
| Scope | Every node holding the hypothesis is in the step's subtree, by the tree's structure; the body's last conjunct, after the step, has the empty context |
| The exported tree | Accepted by S08; it begins with the universal's introduction and the conversion under the implication, and holds the principle's application |
| Forged trees | Rejected: `P := even`; the genuine tree against a KB without the principle |
| `∀x:Nat. reachable(x)`, `∀x:Bool. defined(x)`, `∀x:List. allNat(x)` over tagged symbols | Each exported Term accepted by `checkProof`, though P0 asks scoped-proof evidence for each universal itself; a tampered Term rejected |
| Another domain's principle: a program carrying only Bool's and the list's; a Nat tree citing Bool's principle at the focus | A `principle` need; rejected |
| Bool's and the list's runs | Bool: no field opened; list: two fields opened in the `cons` case, the tail's hypothesis converted |
| A step clause guarding its variable at the default range, `D_all(x)` | Success by the split, and the exported Term accepted |
| `∀x:List. defined(x)`; `∀x:Bool. reachable(x)` | Exhausted: a case has no proof |
| `universal_holds` | `∀x:Nat. reachable(x)` true in the induction model, by `InductiveSoundness` |

## Boundaries

- **Termination is by fuel.** The plan applies the principle once per focus,
  and its cases' clauses need no extension, but no structural decrease
  of the subgoal search is proved: the run is bounded by its fuel, and an
  interrupted run is Undecided. A checked termination argument for P3
  strategies is S15's.
- **One principle per domain.** Each declared domain gets its structural
  principle for a unary predicate, `∀x:D. p(x)`. Simultaneous induction over
  mutually recursive domains (one predicate per domain), invariants of other
  arities, and well-founded induction on other orders are not generated.
- **No decision.** Induction is P3: a failed case refutes nothing, and
  no complete decision contract for guarded universals is supplied.
- **Whole-run export.** Acceptance of an exported tree is decided per run, as
  the traces do. That every successful run exports an accepted tree belongs
  to S15/S16.
- **No NAF.** The plan's run is the left strategy alone, so NAF as a goal in
  a clause the cases may select is reported as a `negation` need. Running the
  plan's selection under S10's `nafByRefutation` or S07's `withNegation` would
  admit it; that is not done (S15). NAF assumed in the query's context is a
  hypothesis, reported as a `scopedProof` request.
- **Conservative gaps.** A formula P0 asks scoped-proof evidence for, such as a
  disjunctive body goal, is reported though S06's introductions may run it;
  the plan's selection chooses no left rule, so a non-atomic assumption is
  reported too. A guard is `waitingGuard` only when no other goal of its
  clause mentions its name; one that another goal leaves unbound still
  flounders at run time, and the run is abandoned: Undecided. Every denial is checked,
  since any `false` subgoal may select it.
