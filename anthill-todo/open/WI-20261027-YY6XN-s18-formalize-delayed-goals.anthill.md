## Attributes

- id: WI-20261027-YY6XN-s18-formalize-delayed-goals
- created: 2026-10-27T20:27:30Z

- status: Open
- status_agent: user
- status_at: 2026-10-27T20:27:30Z

- acceptance: lake build

- depends_on: WI-20261026-53V6D-s04-define-machine-states, WI-20261028-X6W1K-s19-make-declared-free-names-a

- tags: resolution-machine

## Description

S18: Formalize delayed goals: wakeups and constraints in the store

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: extend the S04 machine with delayed goals as designed in docs/machine-delay.md. Typed clause heads compile to generated goals that delay on unbound operands, wake when a later goal (possibly the caller's) binds them, and flounder loudly when still unbound at the end (Anthill proposal 060; the generated fill goal is appended after the body). Wakeups and residual constraints attach to names in the Store, so they are threaded through AND siblings and restored with the store on backtracking; the commit that binds a name returns its wakeups.
Acceptance:
- A delay response suspends the focused obligation on declared unbound flexible names; an invalid delay is a contract gap.
- Woken obligations run before the waking candidate's continuation, each under its own scope; their proofs are recorded under the suspension id and referenced from the tree.
- Wakeups are one store entry per suspension id, attached to every name it waits on. Prove exactly-once wakeup: a commit returns each woken suspension once, removes it from the store (no stale attachment on its other names), and keeps every suspension none of whose names it bound.
- A suspension outlives the frame that created it; the woken obligation keeps its own scope, and nothing from that scope reaches the caller.
- On success, references are filled at the end; prove the deferred proofs are coherent and prove their recorded obligations, and that a success has no pending wakeup and no unresolved constraint.
- Pending wakeups or unresolved constraints at the end flounder as gaps: never success, never exhaustion, never NAF evidence.
- Extend State.Valid, Store.Scoped, run_success, run_exhausted, and the rollback theorems; existing rule-frame guarantees are unchanged.
- Suspended and woken obligations satisfy S19's declared-names invariant: a suspension's free names are declared in the store that holds it.
- Distinguish persistent restrictions from unresolved constraints. Dependency sets are restrictions: checked at every commit, attached after binding, never residual, and never a cause of floundering. Add the slot for unresolved constraints without adding a constraint solver.
- Traces from docs/machine-delay.md: wake on binding; rollback restoring a suspension; rollback after a deferred proof was already recorded; two wakeups from one binding; a delay on two names woken once by binding one or both; alias-triggered re-delay; a callee's delayed goal woken by the caller's later goal; a resumed goal using its own discharged assumption while the caller cannot; flounder; a suspension discarded on failure; success with dependency sets attached; invalid delays.
- Update S06 (guards on unbound variables delay; the generated fill/member goal is appended after the body), S08 (encode and check references), and S10 (NAF on a flexible operand delays).

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/machine-delay.md, docs/machine-state.md, docs/resolution-state-machine.md.

