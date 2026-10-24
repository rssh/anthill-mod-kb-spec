# Callable references and operation dictionaries

The target is an untyped representation of Anthill sorts as dictionary trees of
predicates, operations, and required models. Their semantic contract is formalized in
[`OperationDictionaries.lean`](../AnthillModKbSpec/OperationDictionaries.lean).
`Term.dictionaryCall` provides syntax for calling an operation from such a tree.

An extension of a compositional model provides:

- `reference f`: an explicit value referring to a callable symbol;
- `call value args`: uniform value-level application;
- `dictionary entries` and `project value field`: dictionary values and lookup;
- `roleOf f`: whether a symbol represents a predicate or an operation.

The central law is

```
call (reference f) args = model.application f args
```

Thus ordinary application `f(args)` and indirect application through `reference f`
return the same value. `Extension.call_in_context` proves replacement inside any
semantic value context. Predicate goals can then inspect `model.holds` of the
returned value. This gives one application operation with roles recorded in the
interface.

A reference is distinct in its purpose from evaluating `f()` with zero arguments.
The contract does not require their values to be unequal in every model: an
operation may itself return a reference. The concrete test model demonstrates
that equality between them is not forced.

## Dictionary trees and interface laws

A `Dictionary` contains named `Node`s. Each node is either a `callable` leaf or
a `subdictionary` containing another dictionary. This is an inductive definition
of finite trees; required models can themselves contain required models.
A callable entry has a role, a symbol, and a list of captured values.
Invoking it prepends its captures to the supplied arguments:

```
invoke entry args = model.application entry.symbol (entry.captures ++ args)
```

For example, the intended shape of a Nat dictionary is:

| Field | Role | Callable |
| --- | --- | --- |
| `member` | predicate | `isNat` |
| `zero` | operation | `zero` |
| `succ` | operation | `succ` |

A parent requiring that Nat model can have this shape:

```text
parent
└── required                  subdictionary
    └── nat                   subdictionary
        ├── member            predicate isNat
        ├── zero              operation zero
        └── succ              operation succ
```

`subdictionary value field` projects the child as a semantic dictionary value.
`atPath value [required, nat]` follows the two model edges.
`lookupPathAs value [required, nat] succ operation` then checks the callable
leaf. `atPath_append` proves that concatenating paths agrees with following
them in sequence; `lookupPathAs_sound` proves that successful lookup reaches
the actual callable leaf with the requested role.

`lookupAs` checks both the stored role and the role declared for the symbol.
`lookupAs_sound` proves these checks hold for every accepted entry. Callable
lookup rejects subdictionary nodes; subdictionary lookup rejects callable leaves.
Missing fields and role errors return `none`; that result supplies no NAF
certificate. Duplicate fields use the first entry, with no fallback after a role
or node-kind error. Paths follow named children and do not search siblings.

`Interface.mk required requiredModels laws` specifies the callable fields,
required child interfaces, and semantic laws at a dictionary node. Interfaces
are finite trees too. `Implements` requires all callable fields to pass checked
lookup, every required subdictionary to implement its child interface
recursively, and the node's laws to hold. `Implements.required_model` extracts
the child value and its interface proof from a parent's interface proof.
For a Nat interface, laws could require membership of `zero`, closure under
`succ`, and chosen equations. The model author must prove those laws; field
names and role tags do not establish them. Captures allow dictionaries to
specialize operations with parameters without adding general lambda calculus.

## Syntax and evaluation

The term constructor is:

```text
dictionaryCall dictionary path operation args
```

For example, with a dictionary variable `D` and argument variable `x`:

```lean
.dictionaryCall (.var "D") [required, nat] succ [.var "x"]
```

An empty path selects an operation directly from `D`. Dictionary expressions and
arguments are terms and may themselves contain calls. Paths and operation names
use the existing symbol namespace; they are fixed selectors, not variables.
Free-variable collection, capture-avoiding substitution, binder opening,
executable instantiation, and Miller checking traverse the dictionary expression
and all arguments.

`Model.dictionaryCall` is the value-level interpretation used by `Model.eval`.
The generic model leaves it uninterpreted (defaulting to the model's inhabitant).
`extension.withDictionaryCalls invalid` supplies the intended interpretation:
evaluate the dictionary and arguments, follow the path, require an operation
leaf, and invoke it with its captures. Missing paths, wrong node kinds, and role
errors denote the explicitly supplied `invalid` value. This is a total semantic
interpretation; an invalid access is not a certificate of failed proof search.
An implementation can diagnose such accesses separately.

`Extension.eval_dictionaryCall` proves that a successful call returns
`model.application entry.symbol (entry.captures ++ evaluatedArgs)`. Therefore its
result can appear as data inside other expressions.

[Conditional equation rules](conditional-equations.md) can establish value
equalities between expressions containing these calls. Once their condition
body is derived, equality replacement also applies inside call arguments and
dictionary expressions.

## Relation to soundness

This record supplies additional semantic structure over an existing
`Semantics.Model`. The substitution and environment-congruence proofs include
dictionary calls, so `Model.sound` covers derivations containing the new terms
under its existing KB-validity and NAF-adequacy assumptions. The checked
dictionary interpretation is obtained with `withDictionaryCalls`. No interface
law is automatically a new KB clause or inference rule.

The current syntax-level `ho_apply` law guarantees truth equivalence only.
It cannot establish the value equality required here. Existing concrete models
therefore are not automatically implementations of this extension. Explicit
standalone reference and general indirect-call syntax remain separate future
extensions; dictionary calls use the stronger value-level contract already.

[`Tests/OperationDictionaries.lean`](../Tests/OperationDictionaries.lean) constructs
a model and an extension satisfying the contract. It checks distinct references,
captured arguments, role rejection (including forged tags), lookup behavior,
value replacement in a larger expression, and recursive interface satisfaction.
The nested example follows `required.nat.succ`; malformed child fields and false
child laws prevent a parent from satisfying its interface. The examples also
evaluate a syntax-level operation call, use its result inside another term,
check substitution and capture rejection, and apply `Model.positive_sound` to a
quantified formula containing a dictionary call. This free model witnesses the
contract's satisfiability; it does not interpret Nat operations arithmetically.

[The Nat and Bool Ord example](order-dictionaries.md) supplies interpreted
comparison and equality operations, nested required models, and proofs of
domain membership and ordering laws. The same syntax-level term can use either
dictionary through its environment.
