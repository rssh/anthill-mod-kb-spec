## Attributes

- id: WI-20261026-53V6D-s04-define-machine-states
- created: 2026-10-26T08:32:20Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-27T16:03:25Z

- acceptance: lake build

- depends_on: WI-20261026-VJVCB-s01-define-the-first

- tags: resolution-machine

## Description

S04: Formalize machine states, continuations, proof evidence, and branch isolation

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: define the abstract executable machine state and certificate representation: focused obligation, per-obligation local context, rigid/flexible names, dependency levels, substitution, AND/OR continuations, candidate alternatives, and rollback state. Use named command contracts independent of Lean syntax.
Acceptance:
- Specify transition input/output and completion behavior; an AND parent completes exactly once after all children.
- AND branches maintain compatible shared answer substitutions; OR alternatives restore candidate-local changes.
- Local assumptions, existential witnesses, and rigids cannot escape their scopes.
- Represent success evidence and unsuccessful/incomplete outcomes separately.
- Define proof-tree construction interfaces for successful commands: rule identity, conclusion, premise trees, explicit instantiations/witnesses, discharged assumptions, and snapshot/context dependencies. S08 supplies the encoding as Term and checker; S04 does not depend on their implementation.
- Record which evidence is monotonic and which is snapshot-indexed. Derivations from clauses, including the generated signature clauses, stay valid when the KB or registry grows; NAF and finite absence or enumeration evidence is closed-world and snapshot-indexed. Lowered formulas carry no snapshot dependency: they read only the signature naming.
- Preserve successful choices and all required premise branches so a completed proof can be exported without replaying search. Unknown/exhaustion must not produce a completed proof tree.
- Include executable or formal traces for conjunction, disjunction, nested implication, and an incompatible shared-answer case.
This ticket defines the state/evidence foundation, not an unrestricted search scheduler.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/resolution-state-machine.md and docs/resolution-implementation-plan.md.

## Changes

### 2026-10-27T16:03:24Z — feedback — user

Implemented S04 in AnthillModKbSpec/Resolution/Machine/ (Store, Evidence, State, Commands; aggregated by Resolution/Machine.lean) with docs/machine-state.md. State: per-obligation Scope (level, rigid names, assumptions), Premise/Discharge scope extensions, a Store of declared rigid/flexible names with dependency levels and triangular newest-first answer bindings, AND Frames (parent, rule, proved premises with subproofs, current, pending), OR ChoicePoints saving store and frames, gaps that survive backtracking. Commands return candidates (Expansion: rule application with explicit parameters, fresh flexibles, bindings, premises) or unsupported; Store.commit checks freshness, binds only unbound flexibles to resolved in-scope values, applies occurs and level checks, and lowers aliased flexibles (rejected = candidate miss; violated = contract gap). step/run implement the transitions; Outcome separates success (CompletedProof with snapshot, root, tree, store, plus a resume state) from exhausted, unknown(gaps), and interrupted. Proved: Frame.feed_exact/feed_partial/feed_overfull and step_complete (AND parent completes exactly once after all premises); State.init_valid, step_valid, run_success (any command keeps frames/focus/choices linked; a success is a coherent tree for the root obligation, each subproof proving its premise under the parent scope plus only its discharge); step_proved_store, Store.commit_extends, Store.bind_bound (shared answers threaded, never rebound); step_backtrack, State.enter_store (rollback discards a failed alternative's bindings); Store.bind_respects_scope, Store.commit_rigid_level (opened rigids/witnesses cannot be bound into shallower answers); Outcome.proof?_eq_some, run_exhausted (only success carries a proof; exhaustion only without gaps); Store.resolve?_sound. Evidence: RuleId/RuleApp mirror Derives plus symbol-named extensions with parameters (eigenvariables, witnesses, clause template and instantiation, equalSubst template, closed-world refs); ProofTree nodes record obligation (context, conclusion), premises with discharges, and subproofs, with mutual Coherent/CoherentPremises. EvidenceClass, ProofTree.snapshots/Monotonic; new Foundation/Monotonicity (Derives.mono, positive_mono), Elaboration.signatureKb_mono, groundFailure_exact/stale. Named command contracts (truth, assumption, conjIntro, disjLeft/Right, disjElim, impIntro, impElim, falsityElim, forallIntro, existsIntro, existsElim) with Expansion.Sound lemmas for binding-free candidates. Tests/Resolution/Machine.lean: #guard traces for conjunction, disjunction with rollback (including binding rollback and answer enumeration), nested implication and sibling isolation, disjElim cases, incompatible vs compatible shared answers, store-refused rebinding, forall-exists vs exists-forall levels, root-answer escape, unsupported/gap persistence, interruption, contract violations; formal frame/coherence/run_success/monotonicity examples. Kernel decide cannot reduce the existing well-founded Term.freeVars/instantiate?, so traces use compiled #guard. Deferred: alias-level invariant and alpha-renaming (S05), concrete commands and reconstruction under bindings (S06), P0 termination/failure certificates (S07), Term encoding/checker (S08). Validation: lake build AnthillModKbSpec AnthillModKbSpec.Archive; all 27 current Tests/**/*.lean files; axiom audit (propext, Quot.sound, Classical.choice only); doc link check; git diff --check.

### 2026-10-27T16:36:50Z — feedback — user

Post-review revision (part of S04). (1) Scope dependencies replace numeric levels: NameInfo is rigid | flexible dependencies; a flexible name depends on the rigid names in scope where it was created, narrowed when aliased. Levels could not separate sibling scopes of the same depth, so a witness under one forall branch could be bound to the other branch's eigenvariable; the dependency check refuses it. Store.Scoped (answers mention only rigid names among their name's dependencies and flexible names depending on them) is preserved by commit (Store.commit_scoped) and is part of State.Valid; Store.commit_no_escape proves an opened rigid name is never a dependency of an existing flexible name. (2) Freshness: commit checks new names against Obligation.names (free and binder names of goal and context) and that the obligation's rigid names are declared; Store.commit_fresh and Obligation.fresh_of_not_mem_names give the Derives freshness premises, so forallIntro_sound/existsIntro_sound take fresh : name ∉ obligation.names. State.init now takes answer names, context, and goal and declares every other free name as a rigid parameter (no caller-supplied name table). (3) Binding a flexible name to itself is a no-op. (4) Proof trees carry no snapshot: RuleApp/ProofTree/Expansion/Frame/ChoicePoint/Focus/Command lost the Snapshot parameter; closed-world nodes are relative to CompletedProof.snapshot, so mixed snapshots are unrepresentable; ProofTree.closedWorld/Monotonic, and extensions declare their class (S08 proves declared-monotonic extensions survive growth). (5) Reused OperationDictionaries.lookup; enter computes the saved choice list once with enter_root/enter_gaps lemmas; added step_waiting tying step to Frame.receive. Tests: driver resolves the goal before identity matching and reports unresolvable assumptions as unsupported; new traces for existsElim witness isolation, sibling-branch escape refusal, query-name capture, self-binding. Docs updated (machine-state.md, design doc wording on what S04 does not provide). Validation: lake build AnthillModKbSpec AnthillModKbSpec.Archive; all 27 current Tests/**/*.lean files; axiom audit (standard only); doc link check; git diff --check.

### 2026-10-27T16:56:40Z — feedback — user

External review fix (part of S04): closed-world nodes now retain their evidence. The machine takes an abstract Certificate type parameter (RuleApp, ProofTree, Expansion, Response, Command, Frame, ChoicePoint, Focus, State, Outcome, CompletedProof). RuleApp.defaultNegIntro carries the operand's complete-failure certificate; extension carries Option (ClosedWorldEvidence Certificate) (kind and certificate). ProofTree.closedWorld lists the retained evidence, so an exporter reads certificates from CompletedProof instead of recomputing failure; certificates stay relative to CompletedProof.snapshot. S07/S10 define certificates, S08 checks them. New trace: p ∧ naf q under p with a toy certificate, read back from the completed proof. Validation: lake build AnthillModKbSpec AnthillModKbSpec.Archive; all 27 current tests; axiom audit; git diff --check.

