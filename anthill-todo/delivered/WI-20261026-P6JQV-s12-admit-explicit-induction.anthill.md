## Attributes

- id: WI-20261026-P6JQV-s12-admit-explicit-induction
- created: 2026-10-26T08:32:32Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-05T17:36:03Z

- acceptance: lake build

- depends_on: WI-20261026-DABJW-s11-add-ho-apply-conversion, WI-20261026-ZPV53-s08-define-checked-proof, WI-20261026-NG07C-s07-build-the-initial-static

- tags: resolution-machine

## Description

S12: Formalize admitted induction and prove the Nat example

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: supply a model-valid Nat induction principle over registered predicate references and a checked strategy/proof application that produces the base and scoped-step obligations. Extend admission for this justified path, not unrestricted recursive induction selection.
Acceptance:
- Execute or check forall x:Nat reachable(x) by whole-formula induction-head selection.
- The step uses a fresh n, Nat membership, and local induction hypothesis; scope restoration is demonstrated.
- Registry membership does not substitute for proving the induction principle valid in the shared model.
- Lower the induction rule through `elaborateClause?` with P at `.predicate 1`; a D_all range on P is rejected.
- Repeated selection of induction on its own subgoals cannot evade the selected strategy's termination/admission contract.
- Base/step dependencies requiring extensions are reported before execution.
- Result reconstructs the original guarded universal, reusing InductionModel and InductiveSoundness.
- Export a successful induction proof as a Term tree containing the principle application, predicate instantiation, base proof, and scoped step proof. Prove P1 checks this tree via known rule procedures even when the universal and intermediate formulas have no P1 discovery plan; induction search remains P2 unless a separate complete decision contract applies.
Include rejected forged induction evidence and a domain mismatch; no automatic generic induction axiom for arbitrary domains.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.

## Changes

### 2026-11-05T17:36:01Z — feedback — user

Implemented S12 in AnthillModKbSpec/Resolution/P2/Principle.lean and P2/Induction.lean (new, with P2.lean aggregator). Principle: source clause (G_D(x) -> ho_apply(P, x)) :- ho_apply(P, zero), forall n:D. (ho_apply(P,n) -> ho_apply(P, succ n)), generated only for Nat-shaped domains (NatShape, natShape?, natShape?_spec), lowered by elaborateClause? with P at .predicate 1 (lower) and rejected with a data range on P (lower_data); principle_valid proves it true in every model realizing the signature from the domain's exact realization, not from the registry. Admission: check reports Needs before anything runs (shape, domain, registration, principle, names, base and step dependencies as P0 requests other than ground instances over the clauses reachable from p plus every ho_apply head, so the atomic induction clause is reported); invalid for forged or missing signature clauses; check_input. Strategy: one left-strategy run whose selection applies the principle by headMatch only at a focus G_D(e) -> p(e) (Plan.selection_focus), never at instances of its premises (Plan.body_unfocused); fuel-bounded, interrupted is Unknown. Results: Plan.reconstructs, Plan.models, Plan.sound, Plan.not_p0 (no P0 plan for the universal), Unfold.application_proves. Tests/Resolution/P2/Induction.lean: on the induction model, admission, the run (principle once with P := reachable, x := a; guards by the generated fact; base by ho_goal; step at a fresh n with isNat(n) and the hypothesis converted; scope restored), the export accepted by S08, forged trees rejected (P := even, an induction clause not in the KB), needs for registration/shape/principle/step/base, universal_holds via InductiveSoundness; over tagged symbols the exported Term accepted by checkProof, a tampered Term rejected, Bool rejected as not Nat-shaped. Docs: docs/machine-induction.md (new), roadmap, contract, state machine, conversion, README. Validation: lake build; all tests incl. archive via lake env lean; git diff --check. Boundaries: termination is by fuel (a checked P2 termination argument is S15's); only Nat-shaped domains and unary p; no decision; whole-run export theorem S15/S16.

### 2026-11-05T20:30:24Z — feedback — user

Generalized after review: no Nat-only principle. Every declared inductive domain has its structural principle, generated from its listed rules: one case per constructor rule, each field bound and guarded by its domain, an induction hypothesis for each field of the domain itself, fields of other domains (mutual ones included) guarded without hypothesis. principle_valid proves it in every realizing model by induction on Member, for arbitrary arities (assign, guardFields_satisfies, hypotheses_satisfies). Admission checks that elaborateClause? with P at .predicate 1 gives the principle (Plan.lowered), decides admissible names (admissible?_spec), and accepts domain-list guards m(t) ∨ false in dependencies; NatShape, natShape? and Need.domain are gone. Tests add Bool (two field-free cases) and lists of Nat (cons guards its Nat field, hypothesis for the tail only), each exported Term accepted by checkProof; failing cases are exhausted. Simultaneous induction over mutually recursive domains is out of scope.

### 2026-11-07T11:14:48Z — feedback — user

Code review (15 findings) fixed: admission now reports what the cases cannot run as CaseGap needs (context/clause): NAF (negation), formula-variable goals, range guards on names no other goal mentions (waitingGuard), and P0's other requests apart from ground instances and range guards; dependencies are seeded with p and the P_1 guard symbol, so guard-defining clauses are reported. lower_data generalized to lower_rejects (any range not admitting a unary predicate, D_all included). Unfold.application/application_proves removed; export acceptance is checked per run, whole-run theorem stays S15/S16. Gap renamed CaseGap (clash with Machine.Gap). New tests: NAF, guard definition, variable goal, waiting vs bound guard, another domain's principle (principle need; Bool principle cited at a Nat focus rejected), genuine tree against a KB without the principle, encoded P0 check requires the goal's own scoped-proof request. Open: NAF in the cases' search (would need the plan's selection under S10 nafByRefutation or S07 withNegation).

### 2026-11-07T13:03:22Z — feedback — user

Second review (14 findings) fixed: the run is leftCommitted (the principle is the one command at a focus, so a valid looping clause no longer diverges first); the selection splits guard assumptions m(t) ∨ rest at guard goals on the same term (guardSplits), so atomic and D_all guards on fields close; denials and formula-variable heads are dependencies, a denial's body checked; P0's groundInstance split into groundInstance (data) and formulaVariable; the principle and its names are found in the program (namesOf?, carried?), so any generator names work; lower_principle proves lowering gives the principle for admissible names, so admission lowers nothing (Plan.lowered is a theorem); the principle is cached in the Plan; bindable computed once per clause; S03 clauseGuards now gives one guard per free name (eraseDups); scope test checks the step's subtree structurally; docs corrected (context NAF is scopedProof).

