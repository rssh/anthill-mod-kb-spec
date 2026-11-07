## Attributes

- id: WI-20261107-JA6WZ-s22-answers-yes-no-unknown-and
- created: 2026-11-07T12:22:11Z

- status: Claimed
- status_agent: claude
- status_at: 2026-11-07T15:42:15Z

- acceptance: lake build

- depends_on: WI-20261026-ANXY6-s10-implement-evidence-first, WI-20261026-NG07C-s07-build-the-initial-static, WI-20261026-P6JQV-s12-admit-explicit-induction

- tags: resolution-machine

## Description

S22: Answers Yes, No, Unknown, and Undecided(blockers)

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: give the module four answers and keep the two unknowns apart. The goal of the Anthill KB module is that computation either works or stops fast and says what it cannot compute.
- Logical Unknown: the KB leaves the goal open, because it depends on an open predicate (`p(x̄) :- UNKNOWN`, S10). It is a decided answer about the KB, the same for every correct engine, and fast: the open case is marked syntactically, so no search is needed.
- Undecided(blockers): the module did not decide the goal; the blockers say what is missing. It says nothing about the KB.
- Operational outcomes (fuel, an exhausted or interrupted search, floundering, an unsupported formula) are never reported as Unknown.

Decided form (2026-11-07, with the user):
- The answer type is `Yes | No | Unknown | Undecided(blockers)`. Yes carries a proof (`Derives`, exportable as an S08 tree); No a failure certificate or a refutation in the completion; Unknown two witnesses, assignments of the open atoms it reached, under which the KB holds and the goal is true and false respectively; Undecided its blockers, each with its site, path, and what is missing: a proof of a statement (a guarded universal over an infinite domain, a goal implication), a mode or termination argument, or an unsupported construct. Supplying checked evidence for a blocker (a proof Term, a lemma, a failure certificate) turns it into Yes or No.
- `Undecided` was chosen over NotProvable and NeedsEvidence: it states that the module did not decide, not that the goal has no proof.
- Combining results: a definite Yes or No wins; otherwise a remaining blocker gives Undecided, since evidence for it could still give Yes, No, or Unknown; Unknown only when no blocker remains and both witnesses are checked, so it is a statement about the KB alone.
- Unknown is sound, as Yes and No are (decided with the user, 2026-11-07): it means the goal is independent of the KB, true in some model of the completion and false in another. An evaluation that cannot exhibit both witnesses (open atoms that interact, such as `p(a) ∨ ¬p(a)`, or constraints on the open atoms) answers Undecided with a blocker naming them, never Unknown.

Acceptance:
- S10's open case is separated from the machine's gaps: NAF meeting an open predicate's `UNKNOWN` case reports the open atom, not `Outcome.unknown gaps`, and without running the refutation search first. Floundering, unsupported formulas, and lambda-valued answers stay gaps; fuel stays `interrupted`.
- Admission's requests (P0 `Request`, S12 `CaseGap`) are reported as Undecided blockers before anything runs; the combination rule above is stated and proved for the answer type.
- Soundness: Yes implies the goal holds in every model of the KB (with the tracked NAF provider); No implies it fails in every model of the completion.
- Soundness of Unknown: Unknown implies a model of the completion, realizing the signature, in which the goal holds and one in which it fails. Each witness is a finite assignment of the open atoms reached, extended canonically to the other open atoms, and checked: the KB's clauses and denials hold under it, and the goal evaluates true (respectively false). For a goal whose open atoms occur only positively, the all-true and all-false assignments are the candidate witnesses.
- P1's contract is kept: a completed P1 decision never returns an operational unknown; logical Unknown is a decided value. docs/lean-admission-contract.md's result table separates Unknown (logical), Undecided, and the operational outcomes, so no operational result is called Unknown.
- Traces: an open predicate answered Unknown without a refutation run, with its two witnesses; `p(a) ∨ ¬p(a)` with `p` open answered Undecided, not Unknown; a denial that forces an open atom answered by the forced value, not Unknown; `open(a) ∧ g` with `g` refuted answered No; a guarded universal over Nat with no proof answered Undecided with its blocker, and Yes once a checked proof is supplied; a fuel interruption not reported as Unknown.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs.
Design references: docs/machine-negation.md (Open predicates), docs/lean-admission-contract.md (results), docs/machine-p0.md, docs/machine-induction.md.

