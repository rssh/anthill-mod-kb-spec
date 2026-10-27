## Attributes

- id: WI-20261026-265RZ-s03-elaborate-scoped-data-and
- created: 2026-10-26T08:32:19Z

- status: Delivered
- status_agent: codex
- status_at: 2026-10-26T22:23:46Z

- acceptance: lake build

- depends_on: WI-20261026-3AAXX-s02-specify-data-ranges-and

- tags: resolution-machine

## Description

S03: Formalize guarded quantifier elaboration over the existing Term syntax

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: formalize capture-safe guarded elaboration of already represented formulas, contexts, and rule templates using existing Term and domain structures. No concrete surface syntax or parser is required. Universal ranges become implication guards; existential ranges become conjunction guards. Preserve ho_apply and explicit dictionary calls. Guard implicitly quantified clause variables consistently with their declared ranges.
Acceptance:
- Reuse Universal.toTerm and forallAll_intro; add the missing general elaboration/exists support.
- Prove relevant satisfaction, substitution, and scope properties against the foundation model.
- Test shadowing, predicate ranges, empty/overlapping data domains, and semantic carrier values outside generated data.
- No assumption of whole-carrier coverage unless explicitly required.
- Clarify the default range of an unannotated binder in the executable profile; do not guard predicate variables with D_all.
Files: InductiveDomains, Opening, Substitution, UniversalIntroduction and new focused modules as appropriate.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.

## Changes

### 2026-10-26T22:23:45Z — feedback — codex

Implemented S03 in AnthillModKbSpec/Resolution/Elaboration.lean and imported it through the Resolution aggregate. Recursive lowering operates on existing Term, contexts, and definite/goal clause templates with lexical-path sidecar range annotations, preserving ho_apply, dictionary calls, argument order, and shadowing. Data guards reuse InductiveDomains.guard and Universal.toTerm; predicate guards use equalities to exactly registered arity-specific reference values; carrier guards are truth. The unannotated executable profile defaults to all declared data domains; predicate and carrier binders require explicit annotations. Proved exact guard and forall/exists range semantics under Realizes, general compositional value/truth preservation, exact free-name preservation, context satisfaction/freshness, alpha-renaming/opening and stable-image source substitution, arbitrary lowered-target substitution semantics, and implicit-clause guard semantics without carrier coverage or disjointness assumptions. Guarded introductions reconstruct existing Derives; forallAll_intro reuses the foundation theorem. Added Tests/Resolution/Elaboration.lean covering actual empty and overlapping data domains, non-data carrier values, predicate and arity ranges, same-name nested binders, alpha-renaming, dictionary traversal, distinct context-entry annotations, clause guard instantiation, and a false guarded rule template. Added docs/guarded-elaboration.md and updated inventories. Formula-valued replacements that need annotations are elaborated separately and substituted into the lowered target; source commutation explicitly requires Stable images. Validation passed: lake build AnthillModKbSpec AnthillModKbSpec.Archive; all 28 Tests/**/*.lean files; standard-axiom audit; documentation link check; git diff --check. Machine transitions, scope enforcement, operational admission, and quantifier search remain later tickets.
### 2026-10-27T13:50:44Z — feedback — claude

Post-delivery review revision (part of S03). (1) Predicate positions: predicateRanged and clausePredicateRanged, with checked lowering elaborate? and elaborateClause?, reject a binder applied by ho_apply unless its range is .predicate n of matching arity or .carrier. Formulas and their ranges are generated, so ranges are never inferred. (2) Derivable guards: Foundation/MembershipClauses generates constructor-membership clauses (valid under Realizes; Member.derives). Elaboration.signatureKb adds D_all clauses and one Pred_n fact per registered predicate; models_signatureKb and rangeGuard_derives_data/allData/predicate. E(KB) must include signatureKb. (3) Symbolic guards: lowering takes AdmissionSignature.Naming; .allData (the default) and .predicate n lower to membership atoms, so lowered terms never read the registry, domain catalog, or revision. Snapshots index closed-world evidence and plans only. Supporting changes: Model.satisfies_conjunction, SubstitutesList.conjunction, Derives.conjunctionIntro; Tree.toTerm moved to the foundation; InductionModel gains isPred n. Docs, plan, and affected open tickets (S04, S06-S08, S10-S12, S15-S17) updated. Validation: lake build AnthillModKbSpec AnthillModKbSpec.Archive; all 29 Tests/**/*.lean files; axiom audits; doc link check; git diff --check.

