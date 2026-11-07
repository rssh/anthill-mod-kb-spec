# Ord for Nat and Bool

[`OrderDictionaries.lean`](../AnthillModKbSpec/Models/OrderDictionaries.lean) constructs
lawful order dictionaries in one untyped model: `natOrd` with the usual order on
Nat, `natDesc` with the reverse order on the same domain, and `boolOrd` with
`false < true`.

`natOrd` and `boolOrd` implement the same interface schema `ordInterface domain`,
with different domain predicates. Each dictionary has this tree:

```text
Ord
├── member                    isNat / isBool
├── less                      natLess / natLessDesc / boolLess
└── weakOrd
    ├── compare               natCompare / natCompareDesc / boolCompare
    └── eqModel
        └── equal             natEqual / boolEqual
```

This is a small representation inspired by Anthill's `Ord` conversion to
`WeakOrd` and its required equality model, as defined in
`stdlib/anthill/prelude/ordered.anthill`. It uses `Ordering` values (`lt`, `eq`,
`gt`) in place of Anthill's integer comparison signs, and includes `less`, the
comparison, and the equality operations. Other derived operations and the full
ordering hierarchy are outside this example.

## Data, names, and truth

Nat and Bool are declared constructor domains: `zero` and `succ` build the
Nat values, `boolTrue` and `boolFalse` the Bool values, and `isNat` and
`isBool` hold exactly on what they build (`realizes`). The constants `natOrd()`,
`natDesc()`, and `boolOrd()` denote the dictionaries; `aliasOrd()` is a second
name for `natOrd`'s value. The model also interprets the relations
`OrdDictionary(d)`, on the three dictionaries, and `DomainMember(d, x)`, read
off `d`'s member field (`domainMember_exact`). The
[dictionary registry](dictionary-registry.md) registers these dictionaries.

Predicates return logical values and operations return data. The unary
predicates (`isNat`, `isBool`, `isData`, `isPred`, `ordDictionary`) and what
each holds of are stated once (`predicateTruth`): the model's application and
the predicate role a dictionary entry may take (`roleOf`) both read it.
`DomainMember`, binary and read off a dictionary, is no dictionary entry. Only
logical values hold: a Bool result such as `less(natOrd, 2, 3)`, the value
`true`, is compared with `true`, never read as truth.

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
Boolean value, and `lessTerm` calls `less` at the root. Such a result in
formula position does not hold; its equation with `true` does. Passing Bool
operands to the Nat comparison returns the designated `invalid` value.

## What is proved

`nat_implements` and `bool_implements` prove interface satisfaction. Required
child dictionaries are checked recursively, and the Eq child has its own law
stating that its result is true exactly when the operands are equal.
The root interface additionally proves exact domain membership and `OrdLaws`:

- comparisons return ordering values on the domain;
- the induced non-strict order is reflexive, transitive, antisymmetric, and total;
- equality agrees with value equality;
- comparison returns `eq` exactly when the equality operation returns true;
- `less` returns a Bool, `true` exactly when comparison returns `lt`.

The Nat proof works for all naturals. Both proofs use an injective rank into
Nat; Bool's ranks are `false ↦ 0` and `true ↦ 1`. All semantic laws are guarded
by the appropriate domain predicate on the shared carrier.

This concrete model contains tagged Nat and Bool data, references,
dictionaries, and logical values. It is a separate example from `InductionModel`;
its interface proofs do not automatically insert ordering laws into the KB.
`natDesc` satisfies the registry's laws (`OrderRegistry.desc_checked`); its
`ordInterface` proof is not given (`laws_of_rank` covers ascending ranks only),
though `OrdLaws` fixes no direction.

Run the examples with:

```sh
lake build
lake env lean Tests/Models/OrderDictionaries.lean
```
