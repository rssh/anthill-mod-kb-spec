# Scope-safe matching and instantiation

S05 gives the [S04 machine](machine-state.md) its instantiation and matching
layer, over the existing `Term`, `Substitutes`, `Opening`, and
`ClauseInstantiation` code. It covers four things:

- capture-avoiding substitution that renames a binder instead of failing;
- freshening of clause uses that keeps captured parameters;
- how committed answers reach pending goals and local assumptions;
- a matcher whose outcomes separate a miss from an unadmitted capability.

The machine's commit still performs every binding. The matcher only computes
the bindings, and the commit replays them exactly.

| Module | Contents |
| --- | --- |
| [Substitution](../AnthillModKbSpec/Foundation/Substitution.lean) | Free names of instances, agreement on free names, cancellation through an intermediate instance |
| [ClauseInstantiation](../AnthillModKbSpec/Foundation/ClauseInstantiation.lean) | `Term.instantiate`: total substitution with alpha-renaming; agreement with `instantiate?`; composition |
| [Freshening](../AnthillModKbSpec/Foundation/Freshening.lean) | Clause template names, fresh names, renaming with captured names kept, local-rule binder instantiation |
| [Machine/Store](../AnthillModKbSpec/Resolution/Machine/Store.lean) | Total `Store.resolve`; triangular bindings as part of `Store.Scoped`; `Store.prepare` and `commit_prepared` |
| [Machine/Instantiation](../AnthillModKbSpec/Resolution/Machine/Instantiation.lean) | Reading through answers, store refinement, the scope of resolved answers, fresh names for a clause use |
| [Machine/Unification](../AnthillModKbSpec/Resolution/Machine/Unification.lean) | The matcher, its outcomes, termination, and correctness |
| [Machine/Commands](../AnthillModKbSpec/Resolution/Machine/Commands.lean) | Read-through completion contracts (`Expansion.SoundUnder`), clause and universal-elimination contracts |

## Instantiation with alpha-renaming

`Term.instantiate σ` is total. At a binder it keeps the binder's name unless
that name would capture a substituted free name of the body. In that case it
picks a name fresh for every such value (`Substitution.binder`). A capture
hazard is therefore never a logical failure. `instantiate?` keeps its partial
behaviour and its soundness theorem. Whenever it succeeds, the two functions
agree, so the existing Miller and core-matcher certificates are unchanged.

| Property | Theorem |
| --- | --- |
| The computed result is a capture-avoiding instance | `Term.instantiate_substitutes` |
| It agrees with `instantiate?` whenever that succeeds | `Term.instantiate?_eq` |
| Only the values at free names matter; fixing them leaves the term unchanged | `Term.instantiate_congr`, `Term.instantiate_fixed`, `Term.instantiate_identity` |
| Substituting into an instance gives the instance by the composed substitution | `Substitutes.instantiate` |
| An instance's free names are exactly the substituted values' free names | `Substitutes.mem_freeVars`, `Substitutes.freeVars_subset`, `Substitutes.freeVars_cover`, `Term.freeVars_instantiate_single` |
| The relation reads only the values at the template's free names | `Substitutes.congr`, `Substitutes.fixed` |
| A substitution that factors through an intermediate instance cancels against it, whatever binders each side chose | `Substitutes.cancel` |

Cancellation is what lets alpha-renaming coexist with reconstruction. Suppose a
goal is opened at one point and read through answers committed later. The read
premise is still an opening of the read quantifier, although the two sides may
have renamed different binders. The relation accepts every capture-free choice,
so no alpha-equivalence judgment is needed.

The opening contracts (`forallIntro`, `existsIntro`, `existsElim`) open the body
with `Term.instantiate` as well. An inner binder that would capture the opened
name is renamed, so the name needs to be fresh only for free names. This matters
when a command opens the goal as read through the answers. Reading can rename
binders or bring in binders from answer values, which no check on the
obligation as written can see. The commit checks only that a new name is new to
the store (S19). By the [name invariant](machine-state.md#declared-names) that
makes it fresh for the free names of every obligation the store reads, and
binder names impose nothing for soundness. The matcher, however, is syntactic. A
command should therefore also avoid the binder names it reads
(`Store.readBinders`), so that no opening or later reading renames a binder into
an alpha-variant that `Store.unify` reports as `unsupported`.

## Freshening a clause use

A clause use instantiates exactly the names its quantifiers own.

| Use | Instantiated names | Kept |
| --- | --- | --- |
| KB clause | Its free names, bound by the implicit universal closure (`HornClause.templates`) | Nothing else is free |
| Local rule `∀x₁…xₙ. R` | Its explicit leading binders (`Term.instantiateLeading`) | Every free name: captured parameters of the scope, rigid or flexible |
| Inner quantifiers | None: they own their bound names | Renamed only if a fresh name would be captured |

`Substitution.rename` maps template names to their fresh names and fixes every
other name. `Term.rename_freeVars` characterizes the result exactly: a free name
of the renamed term is the renaming of one of its free names. Bound names never
become free, and no fresh name is captured. `Store.freshen` picks the fresh names.
They are distinct, undeclared, and absent from the templates
(`Store.freshen_fresh`, `Store.freshen_nodup`), so they pass the commit's
freshness check. Every template name must be freshened. The commit refuses a
premise naming an undeclared or out-of-scope name as a contract gap, which
catches a clause body variable left as written in the usual case. A leftover
template name that happens to equal a declared name in scope cannot be detected. For local rules, `Derives.instantiateLeading`
gives the instance by universal elimination, `Term.instantiateLeading_captured`
keeps every captured name free, and `Term.instantiateLeading_freeVars` bounds the
new free names by the witnesses.

## Reading through committed answers

Goals, pending premises, and the local assumptions an obligation captured are
stored as written. They mean their reading through the answers, `Store.resolve`,
which applies the triangular bindings oldest first with `Term.instantiate`.
A later binding therefore reaches every pending goal and context without
rewriting the state.

| Property | Theorem |
| --- | --- |
| Reading is a chain of capture-avoiding substitutions | `Store.resolve_sound` |
| Reading through an extended store reads the earlier reading through the added bindings | `Store.resolve_extends` |
| Equal readings stay equal in every refinement: a matched pair stays matched | `Store.Refines.resolve_eq` |
| Reading an instance is an instance of the template by the read values; a freshened clause read through the answers is one clause instance | `Store.resolve_substitutes` |
| A read quantifier is a quantifier, and a read instance of its body is an instance of the read body with the read witness | `Store.resolve_forallVar`, `Store.resolve_existsVar` |
| Reading commutes with the other constructors | `Store.resolve_conj`, `_disj`, `_imp`, `_equal`, `_defaultNeg`, `_truth`, `_falsity`, `resolveWith_app` |
| A derived local rule read through the answers yields its read instances | `Derives.resolve_instantiateLeading` |

`Store.Scoped` now also requires the bindings to be `Triangular`. No name is
bound twice, and each value mentions neither its own name nor a name bound
before it. Commits preserve this (`Store.bind_scoped`). Resolution then leaves no
bound name (`Triangular.resolve_unbound`).

### Scope of resolved answers

S04 kept each committed binding within its name's dependencies. S05 proves the
property of fully resolved answers, through every alias and binding chain.

| Property | Theorem |
| --- | --- |
| A reading of names within a dependency set is within it and unbound | `Store.Scoped.resolve_within` |
| A resolved answer mentions only rigid names among its dependencies and flexible names depending only on them | `Store.Scoped.resolve_answer`, `Store.Scoped.not_mem_answer` |
| Commits refine the store: kinds kept, dependencies only narrowed, bindings only added | `Store.Refines`, `Store.commit_refines`, `Store.bindAll_refines` |
| A rigid name a commit opens never occurs in an older name's resolved answer, in any later scoped refinement | `Store.commit_no_escape_resolved` |
| A rigid name a commit opens is unbound and absent from the read goal and context of the obligation, and of every premise that does not open it (the existential `existsElim` opens), in every later scoped store refining the commit (`Obligation.FreshUnder`). The name invariant supplies the declared names, so there is no per-term hypothesis | `Store.commit_fresh_resolved`, `Store.commit_independent`, `Store.Scoped.fresh_resolve` |

## Matching

`Store.unify scope hoApplySymbol left right` reads both terms through the store
and processes a worklist of pairs (`unifyPairs`). Each step does one of three
things:

- drops an identical pair;
- binds an assignable name, an unbound flexible name, through `Store.bind`,
  then substitutes the binding into the remaining pairs;
- compares the two sides (`compareTerms`).

Because every binding goes through `Store.bind`, the occurs check, the
dependency check, and alias narrowing apply to all of them. Termination is
proved by a lexicographic measure: the number of assignable names, then the
size of the pending pairs. No fuel is involved.

| Outcome | Meaning | Machine use |
| --- | --- | --- |
| `unified store bindings` | The returned bindings, committed in order, give `store`, where both sides read the same | A candidate with these bindings |
| `mismatch` | A constructor or rigid-name clash, an arity clash, or a binding the store rejects (occurs check, dependency) | A candidate miss; never negative evidence about the goal |
| `unsupported` | A comparison the initial profile does not admit | A gap, recorded as unsupported |
| `violated` | A reading names something not usable here: an undeclared name, or a rigid name outside the scope | A command-contract breach, recorded as a gap |

| Pair, after reading | Outcome |
| --- | --- |
| Readings naming an unusable name, identical or not | `violated`, checked once before any comparison |
| Syntactically identical, including binders and calls | Dropped |
| An assignable name and anything | Bound, subject to the occurs and dependency checks |
| Two different binders of the same quantifier | `unsupported`: alpha-equivalence matching is not admitted |
| An operation call and anything else | `unsupported`: equality of calls needs evaluation (S14) |
| `ho_apply` against an ordinary application | `unsupported`: conversion is S11's |
| A rigid name and anything else; different constructors (a binder included); different symbols or arities; different literals | `mismatch` |
| The same structural constructor | Split into the corresponding parts |

| Property | Theorem |
| --- | --- |
| The bindings replay as commits; the result refines the store, is scoped, and both sides read the same there | `unifyPairs_bindAll`, `unifyPairs_sound`, `Store.unify_sound` |
| A match computed against the store a candidate's commit prepares is replayed exactly by that commit, when the candidate's names and premises pass its checks | `Store.commit_unify`, `Store.commit_prepared`, `Store.prepare_scoped` |
| On ordinary readings (no binders, calls, or `ho_apply`) matching never reports `unsupported` | `unifyPairs_supported`, `Store.unify_supported` |
| `violated` is reported exactly when a reading names an unusable name | `unifyPairs_wellScoped`, `Store.unify_wellScoped`, `Store.unify_violated` |
| Matching terminates | `unifyPairs` is defined by well-founded recursion; `Store.bind_openCount` and `matchParts_size` give the decrease |

So, for ordinary well-scoped inputs, the only failure is a mismatch. The matcher
is not claimed complete. A mismatch drops a candidate. It is never evidence that
no unifier exists, and never NAF evidence.

## Read-through completion contracts

`ReadDerives store obligation` is derivability of the obligation's context and
goal read through `store`. `Expansion.SoundUnder` is the completion contract
for read obligations: derivations of every read premise give a derivation of
the read obligation. S04's `Expansion.Sound` stated this only for binding-free
candidates. The goal need only *read* as the connective, so a command may
resolve the goal before choosing the rule.

| Contract | Lemma | Hypotheses |
| --- | --- | --- |
| `truth`, `conjIntro`, `disjLeft`, `disjRight`, `impIntro` | `*_soundUnder` | The goal reads as the connective |
| `assumption bindings` | `assumption_soundUnder` | The goal reads as an assumption of the scope: a match, kept by `Store.Refines.resolve_eq` |
| `disjElim`, `impElim`, `falsityElim` | `*_soundUnder` | None |
| `forallIntro`, `existsElim` | `forallIntro_soundUnder`, `existsElim_soundUnder` | The eigenvariable is fresh for the read obligation (`Obligation.FreshUnder`) and, for `existsElim`, absent from the read existential. `Store.commit_fresh_resolved` gives both from the commit |
| `existsIntro` | `existsIntro_soundUnder` | None; the witness's answer is read |
| `forallElim binder body witness` (new) | `forallElim_soundUnder` | The goal reads as the body's instance; this instantiates local rules with fresh witnesses |
| `clause head body fresh bindings` (new) | `clause_soundUnder` | The renamed head reads as the goal; the read renaming is the clause instance |

These are per-node lemmas. Composing them along a whole successful run belongs to
S06 and S16. That composition uses `Store.Refines` from each commit to the final
store, `Store.Refines.resolve_eq` for matched readings, and
`Store.commit_fresh_resolved` for opened names. That lemma needs the name
invariant at the commit, which `State.Valid` carries at that step. The final
tree does not record the store of each commit, so the composition applies the
lemma along the run.

## Traces

[Tests/Resolution/Matching.lean](../Tests/Resolution/Matching.lean) checks the
functions directly. It also runs the machine with a matcher-driven test driver:
identity against assumptions, universal assumptions with a fresh witness, and
freshened clauses, each matched against the prepared store.

| Trace | Result |
| --- | --- |
| `(∀1. p(1, 2))[2 := 1]` | `instantiate?` refuses; `instantiate` renames the binder |
| `p(3) :- ∀5. r(5, 3)` freshened with 3 ↦ 5 | Template `[3]`; the inner binder is renamed; 5 stays free; a captured name is kept |
| `∀1. (q(1) → p(1, 7))` | Only the binder is instantiated; the captured 7 is kept |
| Matches against a store | Two-sided bindings; clash, occurs, rigid, arity, and binder-versus-atom mismatches; dependency refusal |
| `2 := 0` or `0 := 2`, then either name against rigid 5 | Refused: the alias narrows the scope |
| Alpha-variants, a call, `ho_apply` against an atom | `unsupported`; identical binders and `ho_apply` against `ho_apply` are admitted |
| An undeclared name, a rigid name outside the scope, also on identical sides | `violated` |
| Opening `∀5. ∀6. r(5, 6, 1)` with 6 | `∀7. r(6, 7, 1)`: the inner binder is renamed |
| `p(0) ∧ ∀5. ∀1. r(5, 1, 0)` under `p(1)` with `r(X, X, Y)`, and its `∃5` and `∀9` variants | Exhausted: after `0 := 1` the conjunct reads as `∀5. ∀6. r(5, 6, 1)`. A driver that opens with the read inner binder uses 6, and the opening renames without capture |
| `∀5. ∀6. (p(5, 6) → p(5, 6))`, opened with the inner binder 6 | Success: a binder name of the obligation is a new name of the store (S05 refused it) |
| `∃2. (q(2) ∧ ∀1. p(1, 2))` under `q(a)`, `∀1. p(1, a)` | Success with the driver's witness 3, which avoids the read binder names. With store freshness alone the witness is 1, the inner binder is renamed, and the alpha-variant is unsupported (unknown) |
| `r(X) :- s(X, Z)` used by a command that freshens only the head | Contract gap on `r(Y)`: the body names the undeclared `Z`. Freshening every template answers `a` |
| `∀x. ∃y. y = x` / `∃y. ∀x. y = x` | Success / exhausted (a mismatch, not unknown) |
| `∃y. ∀x. ∃z. (y = z ∧ z = x)` | Exhausted: `y = z` narrows `z`, so `z = x` is refused |
| `(∀x. X = x) ∨ X = a` | The scope miss rolls back; answer `a`; a command proposing `X := x` directly is rejected by the commit, with no gap |
| `r(X) :- s(X)`, `r(X) :- t(X)` for `r(Y) ∧ u(Y)` | The first clause's bindings are discarded; answer `b`; only the second clause is in the proof; resuming is exhausted |
| `p(a, b)` from `∀1. p(1, C)` | Answer `C = b`: the captured answer name is kept and matched |
| `p(X) ∧ ∀5. (r(5, X) → r(5, X))` under `p(5)` | Success: reading the pending conjunct renames its binder (S04 reported this as unsupported) |
| Alpha-variant data / a plain clash | Unknown (gap) / exhausted |

## Boundaries

- The matcher is syntactic. It does not match up to alpha-equivalence, evaluate
  operation calls, or convert `ho_apply`: those report `unsupported`.
  Higher-order patterns remain with the Miller certificates.
- No completeness: `mismatch` and `exhausted` carry no negative evidence.
- The test driver is not S06's command set. Whole-run reconstruction is S06/S16.
- Delayed goals (S18) attach to names in the same store. The matcher reads and
  commits there and does not see deferred proofs.
- `#guard` checks evaluate compiled code: `Term.instantiate`, `Term.freeVars`,
  and `unifyPairs` are well-founded definitions that the kernel does not reduce.
