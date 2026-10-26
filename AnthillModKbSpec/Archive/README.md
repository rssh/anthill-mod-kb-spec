# Archived approaches

These experiments are preserved for reference and possible reuse. They are not
imported by `AnthillModKbSpec` and are not part of the current overview.

| Files | Previous approach |
| --- | --- |
| `InductionGoals.lean`, `InductiveResolution.lean`, `Soundness.lean` | A separate `Goal.formula / Goal.inductiveProof` language and a scheme registry. The current logic instead resolves ordinary induction clauses through `ho_apply`. |
| `UnaryMatcher.lean` | The earlier handwritten unary matcher. The active backend uses Lean core and checks its proposal independently. |
| `../../Tests/Archive/Induction.lean` | The early two-clause induction-certificate example with a coarse consistency witness. |

The archive uses `AnthillModKbSpec.Archive.*` namespaces. Its comparison theorems
are `Archive.ExplicitInduction.sound` and `Archive.ExplicitInduction.consistent`.
The original chronological notes are preserved in
[docs/archive/model-notes.md](../../docs/archive/model-notes.md).

To load or revisit the experiments:

```sh
lake build AnthillModKbSpec.Archive
while IFS= read -r -d '' test; do
  lake env lean "$test" || exit 1
done < <(find Tests/Archive -name '*.lean' -print0)
```

Import `AnthillModKbSpec.Archive` explicitly when using them. CI checks the
archive in a separate job so it stays buildable without becoming a dependency
of the current logic.
