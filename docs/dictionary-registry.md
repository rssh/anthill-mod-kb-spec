# The dictionary registry

S13 specifies how dictionaries are registered and connected to the declared
inductive domains, without a type system. Dictionaries are values in the shared
carrier; names identify dictionaries and interfaces, and two ordinary
relations state their contracts: `I(d)` for an interface `I` (such as
`OrdDictionary(d)`) and `DomainMember(d, x)`. It builds on the
[S02 signature](admission-signature.md), the [dictionary contract](operation-dictionaries.md),
and the [Nat and Bool order dictionaries](order-dictionaries.md).
Traces are in [Tests/Resolution/DictionaryRegistry.lean](../Tests/Resolution/DictionaryRegistry.lean).

| Module | Contents |
| --- | --- |
| [DictionaryRegistry](../AnthillModKbSpec/Resolution/DictionaryRegistry.lean) | Declarations (`Operation`, `Law`, `Interface`, `Primitive`, `Registration`, `Naming`, `Registry`, `Snapshot`), consistency (`Registry.WellFormed`, `Snapshot.WellFormed`), the access check (`Registry.access?`, `Access`, `access?_declared`, `access?_consistent`, `access_eval`) and its verdict (`Verdict`, `Access.verdict`, `Access.blocker?`), the interpretation (`Interpretation`, `Interpretation.Member`, `Snapshot.InterfaceMember`, `Snapshot.Realizes`), the evidence (`Registration.Checked`, `Primitive.Holds`), generated clauses (`Snapshot.kb`, `models_kb`, `interface_derives`, `domainMember_derives`, `domainMember_iff`, `kb_mono`), laws (`Law.formula`, `law_valid`), unknown names (`not_interfaceMember`, `alias_interfaceMember`), invalidation (`Snapshot.ReusableAt`, `Registry.Unchanged`, `Snapshot.Unchanged`, `access_unchanged`, `Registration.Checked.transfer`, `register_unchanged`) |
| [OrderRegistry](../AnthillModKbSpec/Resolution/OrderRegistry.lean) | The Nat and Bool registry over the order model: the signature (`signature_realized`), the `Ord` interface with three laws tying its operations together, three registrations, realization (`realized`), the evidence of a dictionary in any snapshot over this signature (`checked_dictionary`) and of each registration (`checked`), and what it gives (`kb_models`, `asymmetry_valid`, `lessCompare_valid`, `equalCompare_valid`) |
| [Models/OrderDictionaries](../AnthillModKbSpec/Models/OrderDictionaries.lean) | The order model, extended: Nat and Bool constructors and their exact realization (`realizes`), `less`, a descending Nat dictionary, dictionary names, one table of the unary predicates (`predicateTruth`), `OrdDictionary` and `DomainMember` read off the dictionary value (`domainMember_exact`), Booleans that are not truth values |

## Declarations

A **registry** records, beside a signature snapshot:

- **interfaces**: a membership symbol (`ordDictionary`), the operations every
  dictionary of the interface provides, and generic laws. An operation has a
  path of required-model fields, a field, and the argument counts it supports:
  `less` at the root, `compare` under `weakOrd`, `equal` under
  `weakOrd.eqModel`, each at 2. A law is a formula about one dictionary, its
  binder free (`Law`);
- **registrations**: a dictionary's name, version, interface, domain `D_i` of
  the signature, and primitive contracts. The constant `n()` denotes the
  dictionary named `n` (`Interpretation.value`);
- the **naming**: the field holding every dictionary's own domain predicate
  (`member`), and the symbol of `DomainMember`.

A **snapshot** is the registry with the signature snapshot and a revision.
Consistency is decidable. `Registry.WellFormed`: names are unique; interface
symbols are unique and apart from `DomainMember`; an interface declares each
operation once, and no operation starts at the member field, where a
dictionary holds its domain predicate; every registration's interface is
declared, and every primitive contract is for an operation of it at a
supported argument count. `Snapshot.WellFormed` adds that the registry's
symbols are none of the signature's membership symbols or `D_all`, whose
clauses they would contradict. Separation from the `P_n` symbols, an infinite
family, stays a naming hypothesis, as S22's `Separated` states it. A snapshot
that fails the check is an invalid input, the admission contract's
"inconsistent registry declaration", never a missing capability.

Different dictionaries may have the same domain: the Nat example registers
`natOrd` (ascending) and `natDesc` (descending) for Nat, beside `boolOrd` for
Bool.

## What the relations mean

The interpretation is a model with checked dictionary calls: a base model, its
dictionary extension, and the value an invalid access denotes; its model is
`withDictionaryCalls` (`Interpretation.model`). `Snapshot.Realizes` requires,
beside the signature's realization:

| Relation | Holds exactly |
| --- | --- |
| `I(d)` | On the values of the names registered for `I` (`InterfaceMember`), as `P_n` holds on registered references (S02) |
| `DomainMember(d, x)` | When `d`'s own member field, a predicate entry by checked lookup, holds at `x` (`Interpretation.Member`), for every carrier value `d` |

`DomainMember` reads the dictionary value, not a table. A value that is no
dictionary, or has no predicate at `member`, has no members. In the order
model, `domainMember_exact` proves this reading for every value.

## Evidence, not table entries

A registration claims; `Registration.Checked` proves, at the value its name
denotes:

| Claim | Evidence |
| --- | --- |
| Its domain is `D_i` | Its member field holds exactly on `D_i`'s generated values |
| Its interface's operations | Each operation resolves by checked lookup along its path, to an operation entry |
| Its interface's laws | Each law's body holds with the binder at the dictionary's value, under every environment |
| Its primitive contracts | On arguments of the declared domains, the call returns a member of the result domain (`Primitive.Holds`) |

So the domain connection relates `DomainMember(n, x)` to `D_i.member(x)` by a
proof (`domainMember_iff`), and a law holds at a dictionary because it was
proved there, not because an operation is named `less`. A registration
claiming Nat for the Bool dictionary has no evidence, and a dictionary whose
`less` is equality cannot prove asymmetry (traces).

## Generated clauses and guards

`Snapshot.kb` is the signature's clauses (S03's `signatureKb`) and, per
registration of `n` at interface `I` and domain `D`:

```text
I(n).
DomainMember(n, X) :- D(X).
```

A realizing model with checked registrations satisfies them (`models_kb`), and
they make the guards derivable: `I(n)` from its fact (`interface_derives`), a
lookup on the name with no case analysis over the registry, and
`DomainMember(n, t)` for a generated member `t` of `D` from its clause and the
constructor clauses (`domainMember_derives`). An unmet guard, such as
`DomainMember(natOrd, true)`, is not derivable: the clauses are true in the
order model, where it fails. The converse `D(x)` from `DomainMember(n, x)` is
a theorem of the model (`domainMember_iff`), not a generated clause.

## Generic laws

A law of interface `I` closes into the guarded formula `∀d. I(d) → body`
(`Law.formula`). The Nat and Bool example has three, over two members `x`, `y`
of the dictionary (`∀d. OrdDictionary(d) → ∀x. DomainMember(d,x) →
∀y. DomainMember(d,y) → …`):

```text
less(d,x,y) = true → less(d,y,x) = false            asymmetry
less(d,x,y) = true  ↔  compare(d,x,y) = lt           less agrees with compare
equal(d,x,y) = true ↔  compare(d,x,y) = eq           equal agrees with compare
```

The last two tie the operations together: a dictionary whose `less` is
ascending and whose `compare` is descending is asymmetric, but the second law
rejects it.

`law_valid` proves every law valid in every realizing model with checked
registrations of a well-formed snapshot: the guard admits exactly the registered dictionaries of `I`,
and each proved the body at its value. This is ordinary guarded
quantification, though the domain guard depends on `d`. A law is a statement
with a validity theorem, like S12's induction principles; it is not among the
generated clauses and adds no inference rule. How a law is used, as a checked
lemma, is S14's (with S20).

## The access check

`Registry.access? position dictionary path field arity` classifies a call
`dictionaryCall(dictionary, path, field, args)` before anything runs, and
`Access.verdict` says what admission makes of it: it runs, it is blocked with
what it lacks, or the registry is inconsistent.

| Access | When | Verdict |
| --- | --- | --- |
| `declared registration operation` | A registered name, its interface declares the operation at this path, field, and argument count | Runs |
| `formula` | The call stands where a formula is needed | Blocked: no route (`dictionary formula`) |
| `unresolved` | The dictionary is a variable | Blocked: a binding (`mode`) |
| `unnamed` | The dictionary is neither a name nor a variable: a literal, an application, a nested call | Blocked: no route (`dictionary unnamed`) |
| `unknown name` | No registration has the name | Blocked: no route (`dictionary unknown`) |
| `invalid name error` | A registered name called outside its interface: no such operation (the member predicate included), or an unsupported argument count | Blocked: no route (`dictionary operation`, `dictionary arity`) |
| `inconsistent name` | The registration names an undeclared interface | Inconsistent: an invalid input |

Each blocked access carries its reason, so a blocker says which remedy
applies: register the name, call a declared operation, compare the value. A
well-formed registry has no inconsistent access (`access?_consistent`). A
declared access reaches a callable entry in every interpretation with checked
registrations, and the call evaluates as direct application of the entry's
symbol to its captures and the arguments (`access_eval`). A blocked access
becomes an S22 blocker (`Access.blocker?`), so it gives Undecided, never No.

**Booleans are values.** An operation's result is a value: `less(d, x, y)`
returns the Bool value `true` or `false`. A law compares it with the Bool
constant (`less(d,x,y) = true`), and `= false` is a true equation, not
falsity. A call standing as a formula is reported (`formula`): reading the
value as truth would conflate the two. The order model agrees: only logical
values hold, so `less(natOrd, 2, 3)` as a formula does not hold, the constant
`true` as a formula does not hold, and the equation does.

## Unknown dictionaries are not refuted

An unknown name is a missing registration, not a non-dictionary. `I(d)` is
about values: in a realizing model a name may denote a registered
dictionary's value without being registered. In the order model `aliasOrd()` denotes `natOrd`'s value; its access
is `unknown`, yet `OrdDictionary(aliasOrd)` and `DomainMember(aliasOrd, 2)` hold
(`alias_interfaceMember`). Excluding a value from an interface requires ruling
out every registered dictionary of it (`not_interfaceMember`). Likewise an
invalid access denotes the interpretation's `invalid` value; that is a value,
and the access check reports the call instead of deciding anything from it.

A closed-world reading is another matter. P0, or the completion route, reads
`I(n)` and `DomainMember(n, x)` as ordinary atoms against the generated
clauses: with no clause for `aliasOrd`, `OrdDictionary(aliasOrd)` fails, and
the completion's free-equality theory makes distinct names distinct values.
That answer is snapshot-indexed and holds in the models of the completion, not
in a realizing model with aliases. The order model is not a model of the
completion: `aliasOrd()` shares `natOrd`'s value, and the literal `2` shares
the value of `succ(succ(zero))`, which also makes `DomainMember(natOrd, 2)`
with the literal true there but underivable from the clauses, which reach
constructor terms only. S13's theorems are about realizing models; they do
not say a closed-world No is false.

## Snapshots and invalidation

| What | Across a change |
| --- | --- |
| Generated clauses | Grow with the registry (`kb_mono`); derivations from them stay valid (`Derives.mono`) |
| An access, and a plan built on it | Reused only while the names it reads (`reads`) keep their registrations, version included, or their absence, and their interfaces' declarations, laws included (`Registry.Unchanged`, `access_unchanged`) |
| A registration's evidence | Carries over while the signature, the naming, its name's registration, and its interface's declaration are unchanged (`Snapshot.Unchanged`, `Registration.Checked.transfer`); a new registration brings its own |
| Closed-world readings: an `unknown`, exactness of `I(d)`, NAF over the registry's relations | Snapshot-indexed: registering the name turns `unknown` into `declared` |
| A model's realization and the laws' validity | Per snapshot: the laws quantify over the registered dictionaries, so a registration adds a case that its evidence must cover |
| The whole snapshot | Reused only when equal (`Snapshot.ReusableAt`); a new revision is a new snapshot |

Registering a dictionary under a new name changes nothing the other names
read (`register_unchanged`), so their evidence transfers; a version change of
one registration affects the plans that read its name, and only those; a
changed signature or naming affects every registration's evidence. In the
traces, the registry grown by `aliasOrd` is realized by the same model, the
three old registrations' evidence transfers, and the new one is checked.

## What S13 does not do

- Evaluate operations. Primitive contracts state totality and result domains;
  the evaluators, their decision contract, and their termination, soundness,
  and completeness proofs are S14's.
- Use laws in runs: laws as checked lemmas and the conditional-rule view are
  S14's (with S20).
- Compose admission: S15 runs `Snapshot.WellFormed` (Invalid) and the access
  check (blockers) at every call site, with each site's position.
- Add a type system, a runtime evaluator, or new `Term` syntax.
