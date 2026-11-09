# Checked lemmas inside machine runs

S20 lets a run close a subgoal with a checked lemma instead of rediscovering
it: the P3 row "Assumption or supplied theorem: return its proof" of the
[admission contract](lean-admission-contract.md). Before S20, checked proofs
reached execution only as closed facts and rules in the P0 classes
(`admitImports`) or by answering a whole query (`admit`). A universal theorem,
one proved under assumptions, or one outside the P0 classes stayed in the proof
layer, and the machine had no node for a lemma.

S20 builds on the [S08 proof checker](proof-checking.md) (proof imports,
references re-checked at the use site) and on the
[S09 left strategy](machine-left.md). Traces are in
[Tests/Resolution/Lemmas.lean](../Tests/Resolution/Lemmas.lean).

| Module | Contents |
| --- | --- |
| [Machine/Lemma](../AnthillModKbSpec/Resolution/Machine/Lemma.lean) | The machine's view of lemmas (`Lemmas`, `Lemmas.Sound`); use sites that keep their reading (`Store.fixed`, `Store.lemmaSite`, `Lemmas.Sound.later`); the lemma commands and their contracts (`Expansion.lemmaUse`, `lemmaRule`, `lemmaCut`, `*_soundUnder`); backchaining and cuts (`compareLemma`, `lemmaMatch`, `lemmaAttempt`, `cutAttempt`, `LemmaSelection`); the strategy `withLemmas`, `withLemmas_sound_within`, `withLemmas_reconstructs` |
| [Machine/LeftStrategy](../AnthillModKbSpec/Resolution/Machine/LeftStrategy.lean), [Machine/Conversion](../AnthillModKbSpec/Resolution/Machine/Conversion.lean) | `leftWith`, the left strategy with any further candidates (`Offers`), of which `left` is the S09 case; S09's commands sound in every KB containing the program (`Choice.attempt_sound_within`); converted candidates sound with their contract read in scoped refinements (`conclusionAttempt_sound_scoped`) |
| [P1/Derived](../AnthillModKbSpec/Resolution/P1/Derived.lean) | The lemma constructions (`Unfold.reference`, `Unfold.lemmaUse`, `lemmaRule`, `lemmaCut`), valid when the reference resolves (`*_proves`), and their export (`exportDerived`) |
| [P1/Lemma](../AnthillModKbSpec/Resolution/P1/Lemma.lean) | Lemmas as input entries (`Lemma`), the lemmas a run sees (`offered`, `stated`, `lemmasFor`, over S08's `coversProgram`), what is offered and where it holds (`lemmasFor_offered`, `lemmasFor_checked`, `lemmasFor_holds`), soundness in the checker's KB (`lemmasFor_sound`, `withLemmas_sound`, `withLemmas_derives`), accepted exports (`Proves.accepted`, `lemmaUse_accepted`), diagnostics (`diagnose`, `diagnose_not_ready`, `lemmas_admitImports`) |
| [ProofLayer](../AnthillModKbSpec/Resolution/ProofLayer.lean) | Formulas a checked lemma may conclude, beside P0 (`atGoal`, `mayConcludeAs`, `lemmaReaches`, `lemmaCommand`, `diagnoseLemmas`, `diagnoseLemmas_not_ready`) |

## Lemmas as input entries

A lemma is declared as its own kind of input entry beside the clauses: S08's
`ProofImport`, a name, a statement with its context, its proof term, and the
binder ranges the statement was lowered with, as provenance. Statements stay
ordinary formulas. There is no citation marker in formulas, no new `Term`
constructor, and no surface syntax. Only exported trees mention a lemma, by
`Rule.reference`.

## The lemmas a run sees

`lemmasFor vocab checker hoApplySymbol program lemmas` is what a run of
`program` sees, for the run's checker:

- **Nothing unless the checker covers the program.** Its KB must contain the
  program's clauses, for the run's application symbol (`coversProgram`, the
  program's part of S08's `coversInput`). The lemmas form a proof layer over
  the executable program. Their KB may be larger than the program, as in S08's
  `even(4)` example.
- **Only checked lemmas.** A lemma is offered when it is the newest with its
  name and a checked proof of its statement, under its own context, against
  the lemmas older than it. That is its part of S08's `Imports.Checked`
  (`lemmasFor_offered`). The lemmas are checked against the run's checker, so
  an unchecked lemma is never offered, and neither is one checked against
  another snapshot or a stale one after the KB changed. A lemma that references
  itself never checks: its reference is checked against the older lemmas only.
  A checked table with distinct names offers all its lemmas
  (`lemmasFor_checked`). Each lemma is checked on its own, so one bad lemma does
  not hide the others.
- **A lemma holds where its reference resolves.** At a use site,
  `resolve` decides S08's `Resolves`: the lemma's context must be among the
  use site's assumptions, and its proof is checked again under the use site's
  context, context-indexed NAF evidence included (`lemmasFor_holds`). A lemma
  proved under assumptions is never a global fact, and no weakening is assumed.
- **A lemma applies where its own context is.** `stated` checks the
  reference's conditions without its proof. A lemma that applies but does not
  hold has a proof that, checked as written, fails under the use site's
  context: its NAF evidence is indexed by another context, or an eigenvariable
  of the proof is a name the use site's context mentions.

What `lemmasFor` offers is sound for the checker's KB and NAF provider
(`lemmasFor_sound`): a lemma that holds under a context is derivable under it.

## Commands

Three commands use a lemma, as `positive` and S09 use an assumption. Each is
`RuleApp.derived`, a composition of `Derives` rules, with the lemma's name and
statement and the witnesses for its leading binders:

| Command | Lemma `∀x̄. M` at witnesses | Premises | Reconstruction |
| --- | --- | --- | --- |
| `lemmaUse` | the instance concludes the goal, or the whole statement is the goal | — | universal eliminations from the lemma's derivation |
| `lemmaRule` | the instance is `B → H`, and `H` concludes the goal | `B` | eliminations to `B → H`, then `impElim` |
| `lemmaCut` | any instance, chosen by a `LemmaSelection` | the goal, under the instance | eliminations, then a cut on the instance |

Backchaining (`lemmaUse`, `lemmaRule`) uses a lemma at fresh flexible witnesses
for all its leading binders, as `positive` uses a local rule. Its conclusion
must be simple: an atom, falsity, an equation, or a NAF formula
(`simpleConclusion`). It is compared with the goal first (`compareLemma`), and
only a lemma that may apply gets witnesses. An equation or a NAF formula is
matched when the goal has its connective; an equation conclusion is the shape
of S14's dictionary laws. An atom is compared as a local rule's conclusion is
(S11): directly, or through an indirect view where the two differ by
`ho_apply`, the node then converted; a lambda-valued answer is a gap. A universal lemma is
instantiated with its premise `B` as an obligation of the run. A goal that
reads as the whole statement, a universal one for instance, is closed by the
lemma itself.

A compound conclusion is used through a cut. The instance becomes an
assumption of the continuation, where S09's left commands and `positive`'s
local rules use it, as for any assumption. The cut is chosen explicitly,
because a cut on the same lemma again would recurse.

### Use sites

The lemma is checked again once, at the focus, under the context as read, and
only for a conclusion that matches. Its node's contract is read in every later
store of the branch, so that reading must not change. The context and the
statement, as read, must name only rigid names (`Store.lemmaSite`). Rigid names
are never bound, so both read the same for the rest of the branch
(`Store.Scoped.read_fixed`, `Lemmas.Sound.later`). A closed statement always
qualifies, and so does a context under universal eigenvariables. Then:

| At the use site | Result |
| --- | --- |
| The context may still read otherwise: it names an unbound flexible name | A gap: the lemma may hold under one reading and not another |
| The lemma's own context is not among the assumptions | A miss: the lemma does not apply |
| Its context is there, but its proof does not check | A gap: the lemma applies, and the failed check says nothing about the goal |
| It holds | The candidate |

### The strategy

`withLemmas hoApplySymbol program lemmas select cuts` is `leftWith`, the left
strategy with further candidates. Where S09's chosen commands are offered, it
offers first the lemma candidates (`lemmaAttempts`): backchaining on every
lemma, then the cuts `cuts` chooses. Then come the commands `select` chooses.
That covers atomic and falsity goals, not concrete indirect calls, which are
normalized first (S11), and compound goals with no exact candidate. A goal that
waits on an unbound name is `positive`'s. `left` is `leftWith` with the chosen
commands only, unchanged.

Every lemma command's contract is the lemma's derivation read through the
answers, followed by eliminations and `impElim` or a cut
(`Expansion.lemma*_soundUnder`). So the strategy is sound for any KB and NAF
provider for which the lemmas are sound (`withLemmas_sound_within`). S09's
commands are sound in every KB containing the program's clauses
(`Choice.attempt_sound_within`). With `lemmasFor`, the strategy is sound for the
checker's KB and NAF provider when the checker covers the program
(`withLemmas_sound`), and a successful run reconstructs `Derives` there for its
answer instance (`withLemmas_derives`).

The selections are parameters, as in S09. The library defines no automatic
selection and claims no termination.

## Proof trees

A lemma node exports as a reference to the lemma followed by the eliminations
of its instance (`exportDerived`):

| Command | Exported tree |
| --- | --- |
| `lemmaUse` | `reference(L)` concluding the statement, then `forallElim` per witness |
| `lemmaRule` | `impElim H [the instance B → H, B]` |
| `lemmaCut` | `impElim C [impIntro (I → C) [C under I], the instance I]` |

The tree is checked with the lemma table as its import table. S08 checks the
referenced proof again under the use site's context. Each construction passes
checking when the reference resolves there, the steps are eliminations to the
instance (`Instances`), and its premise trees are valid
(`Unfold.reference_proves`, `lemmaUse_proves`, `lemmaRule_proves`,
`lemmaCut_proves`). A valid tree is accepted for its conclusion
(`Proves.accepted`, `lemmaUse_accepted`). Without the lemma table, the reference
is a missing capability: the checker answers `needsEvidence` with the lemma's
name.

## Static diagnostics

A formula a checked lemma may conclude is a proof-layer capability. P1's
`diagnose` lists, for each request P0 makes at a goal of the query or of a
clause body, the lemmas the input's program sees that may conclude the
requested formula, with the command that would use each (`lemmaCommand`). A
goal is reached through conjunctions only: a request inside a NAF operand,
where a lemma could only refute the goal, or inside an atom's arguments is not
one. `lemmaCommand` compares as the machine does, at the formula or at a goal
its introductions leave: the statement itself, the simple matrix or the
implication's simple conclusion by head (`mayConcludeAs`), and otherwise a
component of a compound conclusion through a cut. A component is an instance
over the universal binders a use may instantiate; one naming an existential's
binder concludes nothing, since the cut opens it at a fresh rigid name. P0 admission takes no
lemma, so a lemma never makes an input P0-Ready, and a lemma is reported only
for an input P0 does not admit (`diagnose_not_ready`). An input P0 admits
without the lemma, such as `p(a)` with no clause for `p`, is answered by P0's
run, which exhausts it, while the proof layer proves it with the lemma.

A lemma enters a P0 program only through `admitImports`, as a closed clause in
the P0 classes proved under no assumptions (`lemmas_admitImports`). A universal
lemma is not such a clause.

## Guarantees

| Property | Theorem |
| --- | --- |
| Each lemma command's completion contract, given the lemma's derivation, by `Derives` rules | `Expansion.lemmaUse_soundUnder`, `lemmaRule_soundUnder`, `lemmaCut_soundUnder` |
| A fixed use site reads the same in every later store, and the lemma holds there | `Store.Scoped.resolve_fixed`, `Store.Scoped.read_fixed`, `Lemmas.Sound.later` |
| The left strategy with lemmas is sound wherever its lemmas are | `withLemmas_sound_within`, `withLemmas_reconstructs` |
| A lemma is offered only when the checker covers the program and the lemma is the newest with its name, checked against the older ones | `lemmasFor_offered` |
| A checked table with distinct names offers all its lemmas | `lemmasFor_checked` |
| A lemma holds only where its reference resolves: its context among the use site's, its proof checked there | `lemmasFor_holds`, `Resolves.context` |
| What a run sees is sound for the checker's KB and NAF provider | `lemmasFor_sound` |
| The strategy is sound for the checker's KB, and a successful run reconstructs `Derives` there | `withLemmas_sound`, `withLemmas_derives` |
| Each construction is valid when its reference resolves and its premise trees are valid; a valid tree is accepted | `Unfold.reference_proves`, `lemmaUse_proves`, `lemmaRule_proves`, `lemmaCut_proves`, `Proves.accepted`, `lemmaUse_accepted` |
| A formula usable through a lemma is reported only for an input P0 does not admit | `diagnoseLemmas_not_ready`, `diagnose_not_ready` |
| A lemma enters a P0 program only as an imported clause proved under no assumptions | `lemmas_admitImports` |

## Traces

| Trace | Result |
| --- | --- |
| `univ : ∀1. (q(1) → p(1))`, proved with `p(X) :- q(X)` in a proof layer over the facts `q(a)`, `q(b)`; goal `p(a) ∧ p(b)` | Without lemmas exhausted; with `univ`, two `lemmaRule` nodes at witnesses read as `a` and `b`; exported with two references and two `forallElim`, accepted; without the lemma table, needs evidence (`lemma univ`) |
| Goal `∀1. (q(1) → p(1))` | Closed by the lemma itself; accepted |
| `ctx : t` under `[s]`, by `t :- s`; goal `t`; goal `s → t`; goal `t` under `s` | Exhausted (the context is absent); success with one `lemmaUse`, accepted; success. The reference is rejected by S08 in the empty context |
| `negated : w`, by `w :- naf v`, its NAF evidence accepted only in the empty context; goal `w`; goal `s → w` | Success, accepted; abandoned with one gap at `w`: the evidence is rejected at the use site under `s`, where the lemma applies |
| `∀2. (q(2) → p(2))` under `r(4)`; under `r(7)` | Abandoned with one gap at `p(5)`: the run opens the universal at 5, the eigenvariable of `univ`'s proof; success, opened at 8 |
| `indirect : ho_apply(p, a)`, by `hoApplyIntro`; goal `p(a)` | Compared through the goal's indirect view and converted; exported with `hoApplyElim`, accepted |
| A lemma referencing itself | Never checked, never offered; its goal exhausted; the reference needs evidence. Beside it, `univ` is still offered |
| An unchecked claim; the KB without `p(X) :- q(X)` (stale); a KB not containing the program; another application symbol | Never offered; `univ` not offered and `p(a) ∧ p(b)` exhausted; nothing offered; nothing offered |
| `q(X) → p(X)` with `X` an unbound flexible name | Abandoned, with one gap at `p(X)`: the use site may still change. With `q(X)` proved first, binding `X`, success |
| `cases : p ∨ s`, by the head `p ∨ s :- q`; goal `u` with `u :- p`, `u :- s` | Without the cut exhausted; with the cut, one `lemmaCut`, then `disjCases`; exported with one `disjElim`, accepted |
| `law : ∀1. (q(1) → f(1) = c)`; goal `f(b) = c`; goal `f(r) = c` | One `lemmaRule` at `b`, accepted; abandoned (no `q(r)`, and the equation goal has no introduction rule, a gap) |
| Diagnoses: goal `∀1. (q(1) → p(1))` with `univ`; with no lemma; goal `q(a) → p(a)`; goal `naf ∀1. (q(1) → p(1))`; goal `p(a)` | `scopedProof` with `univ` by `lemmaUse`; nothing; `univ` by `lemmaRule`, and the run proves it; nothing, inside a NAF operand; P0 admits `p(a)` and exhausts it, nothing diagnosed |
| `lemmaCommand` for `p(a) ∨ s(a)` against `∀1. (p(1) ∨ s(1))`; for `p(a)` against `∃1. p(1)` and `∃1. (q(1) ∧ p(a))` | `lemmaCut`; none; `lemmaCut` |
| `admitImports` with `univ`; with the closed lemma `p(a)` | Nothing added, P0 exhausted; added, P0 succeeds |

## Boundaries

- **Export of whole runs is not proved here.** As for S09, the constructions
  are checked given checked premise trees and their side conditions. The
  theorem that every successful run exports an accepted tree belongs to
  S15/S16.
- **Fixed use sites.** A lemma is used only where the context as read names no
  unbound flexible name. A context with one is a gap: the lemma is checked under
  one reading, and the contract is read at the end.
- **Proofs are checked as written.** S08 does not rename a referenced proof's
  eigenvariables. Where the use site's context names one, the proof does not
  check there and the use is a gap. The machine's fresh names do not avoid the
  lemmas' proofs.
- **References are checked again at each use.** Nothing is memoized (S08's
  boundary): each backchaining step that matches checks the lemma's proof
  under its context.
- **Conversion by introduction.** A goal applying a flexible predicate name is
  not matched against a lemma's view: that would choose a predicate among the
  lemmas, as among the clauses. It is a gap.
- **No termination or completeness.** Backchaining on a lemma whose premise
  needs the lemma again can loop, and such a run is interrupted. A failed
  lemma attempt establishes no negation and no non-derivability.
- **The fast fragment.** In P1 and P2, a lemma shaped as a Harrop clause is to
  be used by backchaining like a local clause, with its use tabled as any call
  is (S24). Admitting such lemmas into the tabled fragment is S15's
  composition. A lemma with a compound conclusion is used only by P3's left
  commands, as here.
