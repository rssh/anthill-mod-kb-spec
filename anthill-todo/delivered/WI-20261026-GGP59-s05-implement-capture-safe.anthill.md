## Attributes

- id: WI-20261026-GGP59-s05-implement-capture-safe
- created: 2026-10-26T08:32:22Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-28T08:16:22Z

- acceptance: lake build

- depends_on: WI-20261026-265RZ-s03-elaborate-scoped-data-and, WI-20261026-53V6D-s04-define-machine-states

- tags: resolution-machine

## Description

S05: Prove scope-safe matching and instantiation for machine transitions

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: reuse and extend the existing Lean substitution and head-matching operations for the initial profile, keeping clause-template variables separate from rigid query parameters and shared existential metavariables. Define how committed substitutions reach pending goals and captured local contexts.
Acceptance:
- Freshening preserves local captured parameters and explicit quantifier ownership.
- Instantiation handles alpha-renaming rather than treating capture hazards as logical failure.
- Scope constraints propagate through metavariable aliases; occurs/dependency checks prevent escaping witnesses.
- Tests distinguish forall x exists y y=x from exists y forall x y=x, and confirm rollback after a rejected candidate.
- Matching outcomes distinguish mismatch from a capability not admitted by the profile.
Reuse existing Substitution, Opening, ClauseInstantiation and certificate code; preserve its soundness contracts.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.

## Changes

### 2026-10-28T08:16:21Z — feedback — user

Implemented S05 (docs/machine-matching.md). Foundation: Substitutes.freeVars_subset/freeVars_cover/congr/cancel; Term.instantiate, total capture-avoiding substitution that renames a binder only on a hazard (Substitution.binder), with instantiate_substitutes, instantiate_congr, instantiate_fixed, and instantiate?_eq (agrees with instantiate? whenever it succeeds, so the Miller/core-matcher certificates are unchanged), and Substitutes.instantiate (composition). New Foundation/Freshening: HornClause.templates, freshNames/freshenNames, Substitution.rename with Term.rename_freeVars (captured names kept, bound names stay bound, no fresh name captured), Term.instantiateLeading for local rules with Derives.instantiateLeading, instantiateLeading_captured/freeVars. Machine/Store: total Store.resolve (resolveWith, oldest first) replacing resolve?; Triangular bindings as a Store.Scoped field; Store.prepare, prepare_scoped, commit_prepared; CompletedProof.answer is total. Machine/Instantiation: resolve_extends, Refines (commit_refines, Refines.resolve_eq), resolve_substitutes, resolve_forallVar/existsVar (reading an opened goal is an opening of the read quantifier, via cancel), Derives.resolve_instantiateLeading; Scoped.resolve_within/resolve_answer/not_mem_answer, commit_no_escape_resolved, commit_fresh_resolved, fresh_resolve; Store.freshen passes the commit check. Machine/Unification: Store.unify, a worklist matcher (well-founded on assignable names, then pair size) binding only through Store.bind (occurs, dependency, alias narrowing); outcomes unified/mismatch/unsupported/violated; unifyPairs_bindAll and Store.unify_sound (bindings replay as commits, result refines the store and is scoped, both sides read the same), Store.commit_unify, Store.unify_supported (Ordinary readings never unsupported), Store.unify_wellScoped (usable names never violated). Unsupported: different binders of one quantifier, operation calls, ho_apply against an ordinary application; everything else that is not unified is a mismatch. No completeness claimed. Machine/Commands: ReadDerives and Expansion.SoundUnder with lemmas for every S04 contract plus new forallElim and clause contracts (goals need only read as the connective). Tests/Resolution/Matching.lean: renaming vs instantiate?, freshening ownership and captured names, every matcher outcome, alias scope propagation, forall-exists vs exists-forall, dependency-miss rollback, store-rejected candidate with no gap, clause rollback keeping only the second clause, captured answer and rigid parameters, a pending goal read with alpha-renaming (unsupported in S04). S04 machine tests updated for Store.resolve/answer. Docs: machine-matching.md; machine-state, admission contract inventory, plan, README, implementation, design doc; S06/S11/S16 tickets point at the S05 interfaces. Validation: lake build (55 jobs, no warnings), lake build AnthillModKbSpec.Archive, all 31 Tests/**/*.lean files, axiom audit (propext, Quot.sound only), doc link check, git diff --check.

### 2026-10-28T08:41:57Z — feedback — user

Code review fix (part of S05). Soundness: the opening contracts used openFree, which needs the opened name absent from the body's binders, while the commit only checks the obligation as written. A command opening the goal as read through the answers could capture: p(0) ∧ ∀5. ∀1. r(5,1,0) under p(1) with r(X,X,Y) succeeded, while its ∀9 alpha-variant was exhausted. forallIntro, existsIntro, and existsElim now open with Term.instantiate, renaming an inner binder that would capture. The binder-freshness hypotheses are gone from forallIntro_sound/existsIntro_sound/existsElim_sound and their soundUnder versions; only free-name freshness remains, from Store.commit_fresh_resolved. Matcher: the usability check moved from compareTerms into Store.unify and runs once on both readings, so identical sides naming an unusable name are violated as documented. MatchStep.violated and the unused scope parameter of matchStep/compareTerms were removed. New Store.unify_violated: violated iff a reading names an unusable name. Cleanups: Substitution.keeps shared by instantiate?, Substitution.binder, and instantiate_identity; Store.prepare_refines used by commit_refines; the S04 test driver uses identical/Store.assignable; the S05 driver passes stored goals to Store.unify; alias tests check the narrowed dependency list directly. Regressions added: an opening that renames an inner binder, the nested ∀/∃ capture traces with their ∀9 variants, identical-but-unusable sides. Not changed: per-binding cost of resolveWith and done ++ [binding] in unifyPairs (spec-level, kept simple for the proofs). Validation: lake build (55 jobs, no warnings), archive build and tests, all 31 test files, axiom audit (propext, Quot.sound), doc links, git diff --check.

