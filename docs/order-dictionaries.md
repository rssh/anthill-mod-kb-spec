# Ord for Nat and Bool

[`OrderDictionaries.lean`](../AnthillModKbSpec/OrderDictionaries.lean) constructs
two lawful order dictionaries in one untyped model. Nat uses its usual order;
Bool uses `false < true`.

Both implement the same interface schema `ordInterface domain`, with different
domain predicates. Each dictionary has this tree:

```text
Ord
├── member                    isNat / isBool
└── weakOrd
    ├── compare               natCompare / boolCompare
    └── eqModel
        └── equal             natEqual / boolEqual
```

This is a small representation inspired by Anthill's `Ord` conversion to
`WeakOrd` and its required equality model, as defined in
`stdlib/anthill/prelude/ordered.anthill`. It uses `Ordering` values (`lt`, `eq`,
`gt`) in place of Anthill's integer comparison signs, and includes the comparison
and equality operations. Derived operations and the full ordering hierarchy
are outside this example.

## One term, two dictionaries

The generic comparison term is:

```lean
compareTerm (.var "ord") (.var "a") (.var "b")
-- dictionaryCall (var "ord") [weakOrd] compare [var "a", var "b"]
```

Assign a dictionary and arguments through the environment:

| Dictionary | a | b | Result |
| --- | --- | --- | --- |
| `natOrd` | `2` | `3` | `lt` |
| `natOrd` | `9` | `2` | `gt` |
| `natOrd` | `4` | `4` | `eq` |
| `boolOrd` | `false` | `true` | `lt` |
| `boolOrd` | `true` | `false` | `gt` |
| `boolOrd` | `true` | `true` | `eq` |

`equalTerm` follows `[weakOrd, eqModel]` to the `equal` operation and returns a
Boolean value. Such a result can also appear in formula position, where
`model.holds` interprets it as truth. Passing Bool operands to the Nat comparison
returns the designated `invalid` value.

## What is proved

`nat_implements` and `bool_implements` prove interface satisfaction. Required
child dictionaries are checked recursively, and the Eq child has its own law
stating that its result is true exactly when the operands are equal.
The root interface additionally proves exact domain membership and `OrdLaws`:

- comparisons return ordering values on the domain;
- the induced non-strict order is reflexive, transitive, antisymmetric, and total;
- equality agrees with value equality;
- comparison returns `eq` exactly when the equality operation returns true.

The Nat proof works for all naturals. Both proofs use an injective rank into
Nat; Bool's ranks are `false ↦ 0` and `true ↦ 1`. All semantic laws are guarded
by the appropriate domain predicate on the shared carrier.

This concrete model contains tagged Nat and Bool literals, references,
dictionaries, and logical values. It is a separate example from `InductionModel`;
its interface proofs do not automatically insert ordering laws into the KB.

Run the examples with:

```sh
lake build
lake env lean Tests/OrderDictionaries.lean
```
