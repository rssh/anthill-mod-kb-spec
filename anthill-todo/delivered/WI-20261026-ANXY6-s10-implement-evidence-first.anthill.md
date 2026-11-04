## Attributes

- id: WI-20261026-ANXY6-s10-implement-evidence-first
- created: 2026-10-26T08:32:29Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-03T16:05:26Z

- acceptance: lake build

- depends_on: WI-20261026-WHDHK-s09-implement-left-rule, WI-20261026-NG07C-s07-build-the-initial-static

- tags: resolution-machine

## Description

S10: Formalize evidence-first NAF and guarded-universal refutation

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: implement NAF goal dispatch that first uses assumptions/clauses, then requests certified failure where admitted. Specify and prove any new scoped/domain certificate rule needed for forall x:D_i naf-not p(x).
The total ground P0 NAF evaluator and failure certificates are delivered by S07. Reuse that baseline here; S07 must not depend on this ticket.
Acceptance:
- An assumed naf-not p(a) can be used with rigid a without initiating failure search.
- For a guarded universal negative, a specialized positive-witness query exists x D_i(x) and p(x) precedes rigid opening when its certified strategy is selected.
- The positive fact p(1) defeats a universal negative over a domain containing 1; rigid matching failure cannot establish it.
- Exhaustive finite-domain absence includes coverage evidence; infinite-domain absence needs a justified symbolic certificate or static NeedsEvidence.
- Exact KB/context dependencies are checked, including after lemma imports.
- NAF and absence certificates are snapshot-indexed closed-world evidence. Registering a predicate, adding a domain, or adding a clause invalidates them; lowered formulas stay unchanged.
- Supply Term proof-tree nodes and known terminating rule-checking procedures through S08 for every enabled NAF route, including its negative-evidence certificate. Prove successful nodes pass checking; Unknown or incomplete absence searches cannot export a completed NAF proof.
- Logical-not and NAF remain distinct. If contradiction elimination for proved P plus naf-not P is added, prove its semantic soundness explicitly.
- NAF on a flexible operand delays until the operand is bound (`Response.delay`, S18, docs/machine-delay.md: retain a dependency and retry after instantiation). Still delayed at the end it flounders as a gap, never as NAF evidence. Waiting cannot help a rigid operand, which needs a scoped certificate. Constructive-negation answers kept as unresolved constraints (`Store.constraints`) come with their solver: a check at each binding, a discharge rule, and evidence for export.
Reuse CertifiedRefutation and CounterexampleSearch; do not claim existing ground-only Derives already admits scoped NAF.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.

## Changes

### 2026-11-03T14:58:25Z — feedback — claude

Design decided 2026-11-03 (discussion with the user):
- Core calculus: generalize `Derives.defaultNegIntro` — drop the closed-operand premise. `Model.FailureAdequate` then requires a provider's evidence to make `naf G` true in every environment satisfying the context, so evidence for an operand with rigid names must be uniform over their values. Existing providers stay adequate (S07's ground provider relates only closed operands; `Refutes` is already uniform).
- Rejected readings: failure search with a rigid name as a constant (lambda-Prolog's eigenvariable `not`; unsound: `p(1)` with `a` unmatched); enumerating a finite domain cover (impractical).
- NAF evidence from Clark completion: generate the only-if half of each predicate's definition, plus the free equality theory (distinct constructors, injectivity), as clauses beside the program; the completed KB. Evidence for `naf G` under a context is a `Derives` proof of `G -> false` in the completed KB, so S08's checker checks it unchanged and adequacy follows from `Model.sound` in every model of the completion and the equality theory, with complement NAF. Rigid names are handled by case analysis on the head equations, never by assuming a value.
- Dual rules for `not p` are the machine commands (search); each is a derived rule exporting to logical nodes over the completed KB, with a construction-validity proof per rule, as S09's commands.
- Open predicates are marked `P(X) :- UNKNOWN` with a reserved symbol: it has no clauses and no completion, is never refuted, and makes NAF of such predicates unknown, never evidence. A KB clause concluding UNKNOWN is Invalid.
- Evidence first: assumed or derivable `naf` closes a NAF goal before any refutation; flexible operands delay; a search that cannot be admitted as terminating answers NeedsEvidence.
- Caveats to handle: consistency of the completion with NAF in bodies (no NAF cycles, or strata); the occurs check as a schema or checked rule; the model hypothesis is completion plus free equality.

### 2026-11-03T16:05:25Z — feedback — user

Delivered 2026-11-03. Implemented as designed: Derives.defaultNegIntro without the closed-operand premise; Clark completion with the free equality theory (Foundation/Completion), open predicates by a reserved marker (complete?, complete?_reserved); refutation evidence checked by S08 (P1/Refutation, refutation_adequate, refutationChecker_sound); refutation search on the shared machine with inversion, equation joins (equalJoin) and only-if uses (onlyIfUse), exported as S08 logical nodes (Machine/Refutation, P1/Derived); evidence-first NAF (withRefutation: base first, flexible delay, rigid refutation; nafByRefutation_sound, withRefutation_checked); positive witnesses first for universal negatives (withWitness, witnessSearch_defeats); ProofLayer.refutation diagnostic. Snapshot/context/import exactness shown by traces. Boundaries (docs/machine-negation.md): injectivity, occurs check and induction are not searched (supplied trees may use injectivity); no termination; whole-run export theorem is S15/S16; completion consistency with NAF in bodies not checked; no constructive negation.

### 2026-11-03T17:07:20Z — feedback — user

Extended 2026-11-03 after delivery (user decision): the closing phase. A branch proved with goals still delayed closes before floundering (Store.close, step_close): residual suspensions run once more with Store.closing set; Store.bind refuses bindings while closing, and Store.Refines.closed keeps a closing store's bindings fixed, so a NAF node offered then is stable (Store.read_stableNegation). Evidence-first NAF no longer waits while closing and refutes generically: naf p(X) with no p clauses answers with X unbound; naf p(X) ∧ r(X) still delays first. step_valid/step_sound/step_success/step_gaps/run_exhausted extended (Branch.Valid.close); step_flounder now requires closing; step_proved_store allows the closed store. The general constraint mechanism is S21.

### 2026-11-03T18:41:23Z — feedback — user

Code-review fixes 2026-11-03: (1) Signature.of takes declared free constructors (literals always free), so defined operations such as plus in plus(zero)=zero get no clash clause; (2) predicates a non-atomic head (S09 compound head, ho_apply head) may conclude stay open, and a head applying a predicate variable closes nothing (headOpens); (3) ho_apply is never closed; marker check covers compound and ho_apply heads (complete?_heads); (4) a binding refused while closing is a floundered gap, not a miss (State.enter), so a NAF barrier is not opened by it; (5) withWitness defers to the base's evidence unless the base only opens the goal (Expansion.opens); (6) nafAlong marks only names inside atom data; withRefutation evaluates the base once (refuteOr); ofPairs moved to Foundation (Substitution.ofPairs), Term.variableName? reused; Miller Proves.defaultNeg drops its unused closed premise. Declined: halving clash clauses (search matches the stored orientation); context atoms stay hypotheses (guarded universals need it), documented against S07. Regression traces added.

### 2026-11-04T07:17:01Z — feedback — user

Second code-review fixes 2026-11-04: formula-variable heads (X, ∀x. x, X ∧ q) open every predicate (formulaVariable in headOpens); complete? rejects a head that may conclude a marker, including heads that may conclude any predicate when a marker is used (mayConcludeMarker, markerUsed); refuter commits conj/exists splits and joins, then offers closing candidates with clash clauses only for matching equations (clashRelevant, clashes parameter) and one progress step (first only-if use, else newest disjunction split); Bound/Commit.refused distinguishes the closing refusal from real misses (State.enter records only refused as floundered; the matcher reports refused as unsupported, unify_supported now assumes not closing); withWitness defers only to closing candidates (Expansion.closes); equalJoin?/onlyIfAttempt? via findSome?; P1.ofPairs alias removed; Completion.equality split into clashes and injections. Not done: caching nested refutation runs.

