# Generating domains from Lean inductive data

Import the deriving handler and use the `InductiveDomain` class:

```lean
import AnthillModKbSpec.Deriving.InductiveDomain

open AnthillModKbSpec.InductiveDomains

inductive MessageTree where
  | leaf : Nat → MessageTree
  | branch : MessageTree → MessageTree → MessageTree
  deriving InductiveDomain
```

Existing declarations support `deriving instance InductiveDomain for Bool`.
Mutually recursive declarations can derive the class for every type in the
mutual block. Constructor fields may use other supported data types: the
generator includes their finite dependency closure in the generated family.

The [foundation interface](../AnthillModKbSpec/Foundation/InductiveDomain.lean)
packages an ordinary `InductiveDomains.FiniteFamily`, a root domain, and an
encoding from Lean values to constructor trees. It requires proofs of:

```text
encode_member:    every encoded value belongs to the root domain
member_complete: every tree in the root domain encodes a Lean value
```

`InductiveDomain.member_iff` states this exact-image correspondence.
`InductiveDomain.holds_iff` transports a universal property over the root domain
to the encodings of all values of the Lean type. No finite enumeration of those
values is assumed, and an empty type produces an empty root domain.

The [generator](../AnthillModKbSpec/Deriving/InductiveDomain.lean) reads elaborated
inductive declarations, generates constructor rules, encoders, and proof terms,
and elaborates them as ordinary kernel-checked declarations. It generates no
axioms or assumed proof-checker callbacks. The proofs use the existing
`Member.construct` rule and structural induction over membership.

For a public type `MessageTree`, inspect the generated declarations under
`MessageTree.inductiveDomain`:

- `Domain`, `Symbol`: finite enumerations, with one domain per field type and
  one symbol per constructor; their constructors are named `d0`, `d1`, etc.
  and `c0`, `c1`, etc.
- `rule0`, `rule1`, etc., `definitions`, and `family`: the constructor grammar.
- `encode0`, `member0`, etc.: per-type encoding and membership proofs.
- `Value`, `encode`, and `complete`: the family-wide exactness proof.
- `instance0`, etc.: class instances for the requested types.

Private types use a unique generated namespace; their class instances provide
the same interface. Constructor order and field order are preserved. Implicit
constructor fields are included as data fields. External field types are
included in the family without installing additional instances for those types.

The initial supported subset is safe, parameter-free inductive data in `Type`,
including structures, ordinary recursion, mutual recursion, and empty types.
Fields must reduce to other parameter-free inductive data types. Indexed
families, parameterized types and instantiated containers such as `List Nat`,
dependent fields, function-valued fields, nested recursion, and higher universes
are rejected. Unsupported dependencies are checked before generation begins.
Adding support for these forms requires explicit representation rules.

`Unit` fields are also unsupported: `Unit` reduces to the universe-polymorphic
`PUnit`, which the generator rejects. The diagnostic names the elaborated type
(`unsupported field type PUnit`), even when the field was written as `Unit`.

The encoder targets constructor trees. Its exactness theorem does not establish
`InductiveDomains.Realizes` for an arbitrary logical model: constructor
interpretations and membership predicates must still satisfy that separate
contract. It also adds no KB induction axiom or automatic P1 discovery strategy.

`AnthillModKbSpec.Foundation` imports the class and generic theorems without
importing the metaprogram. Import `AnthillModKbSpec.Deriving` to enable generation
alongside the foundation; the primary `AnthillModKbSpec` aggregate includes it.

The [regressions](../Tests/Deriving/InductiveDomain.lean) cover recursive and mutual
data, external and implicit fields, empty domains, wrong arities, wrong-domain
symbols, rejected declarations, and the standard-axiom audit.
