## Attributes

- id: WI-20261026-DABJW-s11-add-ho-apply-conversion
- created: 2026-10-26T08:32:31Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-04T16:56:46Z

- acceptance: lake build

- depends_on: WI-20261026-3AAXX-s02-specify-data-ranges-and, WI-20261026-WHDHK-s09-implement-left-rule

- tags: resolution-machine

## Description

S11: Prove ho_apply conversion and whole-formula induction-head matching

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: implement ho_goal and ho_elim proof commands and checked selection of heads containing ho_apply. Include the user's intended whole-formula match: D_nat(a)->reachable(a) against D_nat(x)->ho_apply(P,x), not only an atomic reachable(a) matcher.
Acceptance:
- Match x:=a and P:=the registered unary reachable reference, without assigning rigids or enumerating arbitrary predicates.
- Discharge P's `Pred_1` guard from its generated fact (`Elaboration.rangeGuard_derives_predicate`), a lookup by symbol. A predicate range supplies no case analysis over the registry. Any per-predicate resolution procedure is selected by lookup on the matched reference symbol; a flexible P is bound only by matching or by resolving its guard against the generated facts.
- Preserve predicate-range guards and independently bound induction-step variables.
- Prove the conversion under implication using foundation rules; extend certificates beyond the current UnaryMatch/Expansion coverage without assuming their existing theorem handles compound heads.
- Direct and indirect calls share a canonical candidate view without rewrite loops.
- The S05 matcher reports `ho_apply` against an ordinary application as `unsupported` (docs/machine-matching.md). Admit the conversion here, as a matching step or a separate command, keeping `Store.unify_sound` and the commit-replay property.
- Emit Term proof-tree nodes for conversion and explicitly supplied whole-formula instantiations. Provide known terminating rule checks through S08 and prove export/check correctness without repeating matcher search.
- Selecting the principle exposes base and universally quantified step obligations and finishes the original formula exactly once.
- Unsupported lambda-valued answers are statically classified; distinguish structural reference matching from general higher-order unification.
Tests cover direct/indirect assumptions, compound heads, arity mismatch, and wrong-domain rejection.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.

## Changes

### 2026-11-04T16:56:45Z — feedback — user

Implemented S11 in AnthillModKbSpec/Resolution/Machine/Conversion.lean (new), with changes to Machine/Evidence (RuleApp.converted, RuleApp.base), Machine/Positive, Machine/LeftStrategy, P1/Derived, P1/Export, P1/Negation, P0/Strategy, ProofLayer. Indirect views (Indirect, Term.indirect?, Converts) with conversion under implications by Derives rules (Derives.ofIndirect/toIndirect, cuts, no weakening). ho_goal normalizes a concrete indirect goal once (Expansion.hoGoal, atomResponse_indirect: the direct premise is never normalized back). Candidates concluding a call by ho_apply (assumptions, local rules, flexible and concrete clause heads) are matched against the goal's indirect view with the unchanged S05 matcher (Store.unify_sound and commit replay kept) and wrapped as converted nodes (convertAttempt_sound); a direct assumption meets a goal applying a flexible name by introduction; a direct clause head against a flexible goal predicate stays a gap (predicate choice). Rigid predicates are never assigned. Static classification compareAtom/compare with lambda gaps (compareAtom_lambda: no instance is the goal or its view). Whole-formula selection Choice.headMatch: the induction principle (isNat(x) -> ho_apply(P,x)) :- isPred1(P), base, step matches isNat(a) -> reachable(a) with x := a, P := reachable, guard discharged by the generated fact (Program.predicateGuard_derives via rangeGuard_derives_predicate), the step binder kept, the focus finished once. Conversions export as S08 hoApplyElim/hoApplyIntro and cut nodes (Unfold.convert, convert_proves, exportNode_converted_proves); no RuleCheck registered. P0's hoApplyConversion requests get S11 proof-layer commands (Request.conversionLayer; none inside data). Tests: Tests/Resolution/Conversion.lean (direct/indirect assumptions, concrete and flexible heads, rigid predicates, compound heads, arity mismatch, wrong-domain and wrong-range rejection, hand-built conversions, diagnoses, theorem instances); updated Positive and LeftRules traces that recorded the old ho_apply gap. Docs: docs/machine-conversion.md (new), machine-matching, machine-positive, machine-left, machine-p0, lean-admission-contract, resolution-state-machine, roadmap, README. Validation: lake build; all non-archive and archive tests via lake env lean; git diff --check. Boundaries: no termination for flexible heads or repeated selection (S12), no general higher-order unification, no value conversion inside data, whole-run export theorem S15/S16.

### 2026-11-04T17:51:52Z — feedback — user

Review fixes: ho_goal keeps a strategy's chosen commands (atomResponse responds with ho_goal followed by extra). Introduction only for a goal applying an assignable name (flexiblePredicate); a rigid or compound predicate is a miss, not a gap. Lambda gaps only for call goals; falsity and other non-call goals are apart, so contradiction search stays exhaustive. Whole formulas of the same kind (binders, names, operation calls) go to the matcher in compare (sameKind). headProject compares its conjunct with conversion; headMatch and headProject admit introduction since the selection chose the clause. convertAttempt is now conclusionAttempt and also handles direct matches; clauseUse is shared by clause selection and headMatch and freshens names only for clauses that may apply. Store.resolve_app moved to Machine/Instantiation as @[simp]. Diagnoses: nothing inside a NAF operand; a compound head concluding a call by ho_apply also gets converted. Tests for each fix, plus a left-strategy trace that an alpha-variant matcher gap stays a gap. Delaying on an unbound goal predicate is recorded as a boundary in docs/machine-conversion.md, not implemented.

