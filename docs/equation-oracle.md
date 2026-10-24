# Soundness with an equation oracle

[`EquationOracle.lean`](../AnthillModKbSpec/EquationOracle.lean) extends the
soundness theorem with a positive oracle for conditional equations. The oracle
can certify equations involving ordinary operations or dictionary calls.

An `EquationOracle M Variable` contains an acceptance relation and its semantic
soundness obligation:

```text
certifies body left right →
  ∀ environment ρ,
    M,ρ satisfies conjunction(body) → eval(M,ρ,left) = eval(M,ρ,right)
```

Acceptance must be correct under every environment satisfying the condition.
This permits open equation schemas without treating a rigid parameter's current
value as a universal fact. Merely assuming that an oracle exists is insufficient;
the theorem requires this soundness obligation. Completeness and termination
of an oracle implementation are not assumptions of the theorem.

## The extended theorem

`oracle.extend KB` is the same kind of KB set as before:

```text
KB_O = KB ∪ { equation left right body | oracle.certifies body left right }
```

The syntax and `Derives` rules stay the same. Accepted equations become ordinary
conditional clauses, so using one still requires proving its body. They can
discharge equality goals in other rule bodies and support equality replacement.
`EquationOracle.models_extension` proves `M.Models KB_O` from the original KB's
validity and the oracle's soundness.

`Model.sound_with_equation_oracle` proves:

```text
M.Models KB
NAF evidence adequate for M and KB_O
KB_O; Γ ⊢_N G
─────────────────────────────────────
∀ρ, M,ρ satisfies Γ → M,ρ satisfies G
```

`Model.consistent_with_equation_oracle` excludes a proof of falsity from the
empty context under the same assumptions.

For inductive domains, `Interpretation.withEquationOracle` preserves the same
model, exact membership realization, and complement NAF. Its extended KB is
validated by `models_extension`. The packaged results are:

- `InductiveSoundness.declarative_sound_with_equation_oracle`;
- `InductiveSoundness.declarative_consistent_with_equation_oracle`;
- `InductiveSoundness.sound_with_equation_oracle` for resolution proofs.

Certified NAF uses the exact extended KB in its evidence index. A missing oracle
answer supplies neither disequality nor NAF evidence.

## A concrete oracle specification

`EquationOracle.closed` accepts unconditional equations between closed terms
when their evaluated values coincide at a fixed environment. The proof shows
that closedness makes this equality independent of the chosen environment.
This is a semantic specification; it does not assume decidable equality on the
entire carrier or provide an executable external solver.

[`Tests/EquationOracle.lean`](../Tests/EquationOracle.lean) checks a computed Nat
comparison used to prove an equation in a predicate rule's body, consistency,
and combination with certified NAF at the extended KB. A conditional-oracle
example accepts `0 = 1` under the premise `0 = 1` and proves that this cannot
create an unconditional proof of the false equality. An unanswered valid open
equality illustrates that acceptance is not assumed complete. The packaged
theorems are also checked with the nonempty inductive KB.

```sh
lake build
lake env lean Tests/EquationOracle.lean
```
