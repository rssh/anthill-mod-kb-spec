# Conditional equation rules

An operation equation

```text
left <=> right :- C1, ..., Cn
```

states that the two expressions return the same value whenever the condition
body holds. Both expressions can contain ordinary applications, dictionary
calls, and variables. The syntax remains untyped.

`HornClause.equation left right body` represents this as an ordinary definite
clause with head `Term.equal left right`. Equation rules therefore belong to the
same KB set as predicate definitions and induction rules. They share the usual
implicit universal closure of their free variables.

The model condition is

```text
for every environment ρ:
  M,ρ satisfies conjunction(body) → eval(M,ρ,left) = eval(M,ρ,right)
```

`Model.satisfies_equation` states this equivalence. `Model.equality` interprets
the equality constructor, and `holds_equality` relates its truth exactly to
equality of the returned values. Logical equivalence alone does not supply this
equality: distinct values may have the same truth status.

## Using an equation

`Derives.equation` uses the existing clause rule. It requires:

- membership of the equation clause in the KB;
- one capture-avoiding substitution applied to both sides and the body;
- a derivation of the instantiated condition body in the current context.

An empty body is an unconditional equation. A nonempty body uses the ordinary
goal logic, including scoped goals and NAF when its required certificates are
available.

## Equations in rule bodies

`Term.equal` is also a goal in the right-hand side of any rule:

```text
p(x) :- f(x) <=> g(x), q(x)
h(x) <=> k(x) :- f(x) <=> g(x), r(x)
```

To apply either rule, prove the equation and the remaining body goals under the
same clause substitution and current assumptions. A body equation can be proved
using another conditional equation rule or the equality inference rules.
Its model meaning is equality of the operand values, just as for an equality
head. The existing body syntax and clause rule already support this position.

Equality has reflexivity, symmetry, transitivity, and replacement rules.
`Derives.equalSubst` uses a formula template and checked substitutions for its
two instances. It permits replacing equal values inside operation arguments,
dictionary expressions, and scoped formulas while preserving binding.
`Model.sound` proves these rules preserve truth. Its KB-validity assumption now
also requires every equation clause to satisfy its model condition.

The equation is symmetric. Choosing a reduction direction, automating matching,
or establishing termination of a conditional rewriter are separate operational
questions; the declarative rule does not require termination.

[The equation-oracle theorem](equation-oracle.md) permits a sound oracle to
certify additional conditional equations. Their clauses extend the same KB;
the soundness and consistency results require the oracle's semantic contract
and adequate NAF evidence for that extended KB.

## Checked example

[`Tests/Foundation/EquationRules.lean`](../Tests/Foundation/EquationRules.lean) contains a nonempty KB:

```text
natEqual(x,x) <=> true :- isNat(x)
isNat(3)
isBool(natEqual(x,x)) :- natEqual(x,x) <=> true
```

Here `true` denotes the Boolean literal `.lit (.bool true)`. The test proves KB
validity in `OrderDictionaries.model`, derives the equation at `3`, and uses it
as the body goal that enables the `isBool` conclusion. A check at a non-Nat
argument proves that a false body equation cannot enable that conclusion.
The test also uses the equation inside an expression of the form

```text
D.weakOrd.compare(natEqual(3,3), false)
  <=> D.weakOrd.compare(true, false)
```

The soundness theorem establishes equality of these returned values for every
dictionary assignment. The same model supplies a consistency proof for the KB.
A counterexample shows that removing `isNat(x)` invalidates the equation on
non-Nat values. Further checks cover symmetry, transitivity, capture rejection,
and the distinction between value equality and truth equivalence.

```sh
lake build
lake env lean Tests/Foundation/EquationRules.lean
```
