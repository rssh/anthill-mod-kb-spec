## Attributes

- id: WI-20261117-A0H19-s29-admission-as-translation
- created: 2026-11-17T20:24:12Z

- status: Open
- status_agent: user
- status_at: 2026-11-17T20:24:12Z

- acceptance: lake build

- depends_on: WI-20261117-06YN9-s27-decision-ir-syntax-checker, WI-20261026-265RZ-s03-elaborate-scoped-data-and, WI-20261026-9C19E-s13-specify-checked-typeless, WI-20261026-5G8F5-s14-implement-dictionary-law, WI-20261026-DABJW-s11-add-ho-apply-conversion

- tags: resolution-machine

## Description

S29: Admission as translation: the decision IR from Term, patterns, statement normalization

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: the translator of docs/decision-ir.md: from the snapshot and the query to an IR program and query, or Undecided with blockers, before anything runs. Decided with the user, 2026-11-17: admission translates the program into the IR, or says which parts need a proof, and is extensible by formula patterns.

Acceptance:
- The pattern interface: a recognizer (a shape at a position: definition, derived, condition, goal or body, NAF operand, denial body), an emitter (IR rules, auxiliary predicates with fresh names, literals), and a correctness lemma; a pattern is a structure carrying its proof, and the translator is correct for any set of correct patterns. A pattern whose emitted IR S27's checker rejects does not apply.
- The translation theorem: every model of the KB's completion realizing the signature extends by the auxiliary predicates' definitions to a model of the IR program's completion, and back, and in it the query and its translation agree.
- Core patterns: clauses with atomic heads and bodies of S23's fragment (lowered, with guards); ground NAF; data equations; markers; denials; a concrete ho_apply as the direct call (S11's ho_goal); a dictionary call with a registered evaluator as a primitive literal (S13's access check, S14's contract); existential goals and bodies; conjunctions ordered so that names are bound from finite sources first.
- Statement normalization (the user's example, 2026-11-17: ∀x∈C. P(x) is P(x) :- x ∈ C when C is a collection): ∀x̄∈C̄. B → A, A an atom and every range a collection, is the rule A :- x̄ ∈ C̄, B, and Completion.headOpens no longer opens its predicates. The KB defines no collections yet. A universal over a declared data domain D_i is special and undecided (the user: "for D_i: need think"): settle with the user whether ∀x:D_i. P(x) defines P, constrains it, or states a theorem; until then its head keeps today's reading, its predicates opened and the statement a denial (⊥ :- D_i(x), naf P(x)). A conjunction of atomic heads as one rule each is proposed, to confirm with the user. Disjunctive and existential heads, formula variables, and predicate variables keep opening theirs, a marker case each, and the statement becomes a denial (A ∨ B :- body is ⊥ :- body, naf A, naf B). Derived statements (checked lemmas, S12's principles, dictionary laws) never enter the completion. Revisit the S09, S10, S22, and S23 traces that read compound heads as opening.
- Blockers: no pattern at a position, or emitted IR the checker rejects: Undecided naming a proof, a mode, a termination argument, or a construct, at the formula's site and path (S22's places).
- P0 and S23 as instances: a P0 input translates to S07's P0.Ground; S23's classes are read on the translation, with S27's point on free outputs.
- Traces: ∀x∈C. P(x) as a statement over a collection; ∀x:Nat. P(x) as a statement, by the reading settled for D_i; p(a) ∧ q(a) as a head, by the reading confirmed; A ∨ B as a head, opened with a denial; the lowered path program; a dictionary call with an evaluator and without one; a formula with no pattern, the blocker naming it.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs.
Design references: docs/decision-ir.md, docs/fast-admission.md, docs/guarded-elaboration.md, docs/machine-negation.md, docs/dictionary-evaluation.md.

## Changes

### 2026-11-17T22:00:22Z — feedback — user

From the user (2026-11-17), on statement normalization: "Our KB statement D_i - are special. I.e. if c is collection (but currently we have no collections defined), than transform is Ok. But for D_i: need think." The rule ∀x∈C. P(x) to P(x) :- x ∈ C is decided for collections only; a statement over a declared data domain D_i, and conjunction heads, keep today's reading (predicates opened, the statement a denial) until settled with the user.

