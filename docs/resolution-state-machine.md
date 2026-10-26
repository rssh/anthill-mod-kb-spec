# Decidable core and proof extensions: state-machine design

Status: design discussion, not an implemented resolver or a completeness theorem.

The [S01 Lean admission contract](lean-admission-contract.md) defines P0, P1, and P2
admission rules for this same syntax and state machine. P1 extends P0 with certified
decision procedures; P2 admits broader proof strategies with Unknown permitted.

Current implementation scope: Lean formalization in this repository, reusing
the existing Term representation and semantic infrastructure. Rust-model/component
work in `/Users/rssh/work/oss/anthill-mod-kb-rust` has its own separate scope.
Parsing, runtime term-representation design, production APIs, and integration are
not part of these tickets. Anthill docs/proposals remain design references. See the
[implementation roadmap](resolution-implementation-plan.md).

Revised direction: provide a decidable executable core and a broader proof
language, both interpreted in the general model. The broader language may have
undecidable proof discovery. Its formulas are handled by explicit proof constructs
and extensions, rather than promising complete automatic search for every term.
The earlier general-search transition catalogue below remains useful for proof
construction, but does not define the decidable core.

Starting points: Qi, *An Implementation of the Language Lambda Prolog Organized
around Higher-Order Pattern Unification*, §§2.2, 4.2–4.3
([paper](https://arxiv.org/abs/0911.5203)); `Derivation.lean` supplies the current
proof rules. The reference PDF is in the neighboring Anthill checkout at
`docs/local/references/lambda-prolog/implementation-ho-0911.5203v1-QI.pdf`.

## Architectural boundary

```text
Decidable core: program + query
    -> terminating decision procedure
    -> answer with the core's specified meaning

Proof language: statement + explicit proof
    -> terminating certificate checker
    -> checked theorem
    -> core-admission check
    -> usable core fact/rule, when admissible
```

An explicit proof is a finite tree in the same logic used by P0/P1/P2, passed as
a `Term`. P1 checks each rule application via a known terminating procedure;
the conclusion and intermediate formulas need no automatic P1 discovery plan.
The tree may be built manually, produced externally, or exported from successful
P2 search. User-provided contexts retain their local assumption scopes. S08
defines the internal tree encoding and checker; this does not require a parser
or public proof syntax. The roadmap assigns the P0 baseline and proof-export
obligations and identifies deferred P1 decision procedures explicitly.

Both paths use the same semantic interpretation. There must be no change of
meaning when an admitted theorem becomes available to the core engine.

### Shared foundation: elaboration into the declarative calculus

Terminology: call the existing `Term`/`Derives` system the **declarative calculus**
(or foundation logic), and `Semantics.Model` its semantic model. The executable
core and the broader proof language both elaborate into this calculus. They are
different admission/execution layers, not different interpretations of truth.

Let `E` be elaboration and `D_all(x)` the disjunction of membership in the declared
data domains. If surface quantifiers range over generated data, define:

```text
E(forall x. P) = forall x. D_all(x) -> E(P)
E(exists x. P) = exists x. D_all(x) and E(P)
E(forall x:D_i. P) = forall x. D_i.member(x) -> E(P)
E(exists x:D_i. P) = exists x. D_i.member(x) and E(P)
```

Elaboration is recursive and capture-avoiding. It applies to goals, assumptions,
proof statements, and clauses, including their implicit quantifiers. If free
variables of a surface clause range only over generated data, the target clause
must carry the corresponding guards; raw KB variables otherwise range over the
whole semantic carrier. Quantifiers over other categories, such as predicate
values, need their declared range rather than an indiscriminate data guard.

The universal translation already exists as `InductiveDomains.Universal.toTerm`
and `FiniteFamily.forallAll`. `FiniteFamily.forallAll_satisfies_iff` proves that it
quantifies over exactly the generated data, assuming exact domain realization.
`Derives.forallAll_intro` reconstructs the guarded universal using existing
implication and universal introduction. The existential translation above is a
design requirement here, not a claim of an existing general elaboration theorem.

The intended soundness composition is:

```text
accepted execution/proof of KB; Gamma |- P
    -- new reconstruction theorem -->
Derives E(KB); E(Gamma) |- E(P)
    -- existing soundness theorem -->
for every rho, M satisfies E(Gamma) implies M satisfies E(P)
```

Use `Model.sound` with KB validity and adequate NAF evidence, or the packaged
`InductiveSoundness.declarative_sound` with its interpretation assumptions. No
new model proof is required for each search strategy if it reconstructs existing
derivations. Scope, substitution, and answer instances are part of reconstruction.

This does not make arbitrary semantic certificates existing `Derives` proofs.
For example, scoped NAF introduction is still a gap unless evidence reconstructs
current rules or a new rule receives its own soundness proof. A model-relative
extension can instead establish its semantic contract directly, but must be
identified separately from reuse through the unmodified calculus.

No assumption that all model values belong to `D_all` is needed for guarded
quantification. Equivalence to raw unrestricted model `forall` needs the separate
carrier-coverage hypothesis, as in `FiniteFamily.forallAll_iff_forall`. A finite
catalog of domains also does not mean those domains have finitely many members.

### Data and predicate quantifier ranges

Proposed surface distinction: quantify over a data domain D_i or over the
registered predicate references of arity n, P_n. P_n is not the set of all
mathematical relations of arity n. Lambda-defined predicate values would require
an explicit enlargement of this range and its interpretation.

```text
forall x:D_i. A   -> forall x. D_i.member(x) -> E(A)
forall P:P_n. A   -> forall P. Pred_n.member(P) -> E(A)
exists P:P_n. A   -> exists P. Pred_n.member(P) and E(A)
```

These are two surface binder categories but the same foundation quantifier with
different guards. Keep the untyped carrier and existing soundness proof rules.

The executable signature needs a registry of predicate symbols and supported
arities. The semantic extension needs a membership interpretation for their
reference values and a contract connecting application of those references to
the corresponding predicates. This extends the existing concrete-symbol
`holds_hoApply` contract; it does not require a disjoint semantic carrier per arity.
If symbols can support multiple arities, P_n ranges may overlap. Any stronger
disjointness or unique-arity requirement must be explicit.

For example, selecting an induction principle quantified over P_1 and instantiating
P := reachable requires evidence that reachable is a registered unary predicate.
The Nat induction principle must still be valid in the model for every admitted
P_1 value. Merely declaring a registry or arity does not prove induction validity.

Formula-level selection for induction uses the entire guarded head:

```text
focus: D_nat(a) -> reachable(a)
head:  D_nat(x) -> ho_apply(P,x)
bind:  x := a, P := reference to reachable
body:  reachable(zero) and
       forall n. D_nat(n) -> (reachable(n) -> reachable(succ(n)))
```

The induction step binder n is independent of the target x. The registration
obligation for P is discharged from checked signature evidence. The exact
encoded clause body must retain that guard if P's implicit universal closure
has been restricted to P_1. Matching the indirect and direct conclusion requires
the existing ho_apply interpretation, not plain syntactic identity. This is an
additional formula-head selection path; the atomic commands in section 9 do not
alone implement it. Any new expansion certificate must justify this whole-formula
application, including the ho_apply conversion under implication.

Neither a finite list of data domains nor predicate arity guarantees decidable
execution. Registry changes must trigger admission rechecking where needed.

### What must be decidable

The immediate requirement is a fast rules interpreter with a decidable static
admission analysis. Before evaluating KB rules, the analysis must either produce
an executable plan or identify obligations requiring supplied proofs/extensions.
It does not first attempt proof search and infer missing capabilities from failure.

```text
check(program, query, input modes, extension contracts)
    -> Ready(compiledPlan)
     | NeedsEvidence(obligations, sourceLocations, reasons)
     | Invalid(diagnostic)

check supplied evidence and operational contracts
    -> recheck admission

run(compiledPlan, inputs satisfying checked contracts)
    -> core execution
```

`Ready` means the interpreter supports the computation, not that the query is
true or will succeed. `NeedsEvidence` means the configured static rules cannot
admit the computation; it is not a theorem that the formula has no automatic
proof. A conservative checker may request evidence for cases that some stronger
analysis could admit. No perfect recognizer for all terminating programs is needed.

The analysis reads declarations, rule bodies, dependency graphs, and available
proofs. "Before evaluating the KB" does not mean "without inspecting the KB".
It must account for dependencies transitively, including possible local clauses.
Data-dependent calls need statically checked interfaces/modes; changing the KB
or an extension contract invalidates affected admission results.

The key invariant is: a Ready plan, run with inputs satisfying its contracts,
does not encounter a missing logical capability or request a new proof at runtime.
Termination, logical completeness, and speed are additional stated guarantees of
the selected core profile. Static capability checking alone establishes none of
them. A terminating core still needs a practical cost model, indexing, and limits
on expensive admitted operations to support the requirement to run fast.

Each formula handler therefore needs two specifications: its static admission
rule and its runtime transition. For example, a finite-domain universal can be
admitted with a checked finite cover and admissible body; an unbounded universal
with no applicable certified strategy requests a theorem or a strategy contract.
A negative assumption used by identity needs no failure-search capability;
establishing that same formula through NAF requires the NAF admission conditions.
Classification depends on position and context, not just the constructor name.

Decidability is a contract for a class of programs, queries, domains, and primitive
operations, not merely a list of allowed connectives. Unrestricted Horn programs
already allow nonterminating computation. Conversely, logical negation is decidable
in propositional logic; its presence alone is not the boundary.

The core specification must identify:

- the admitted programs and queries, with an effective admission check;
- the precise decision problem (for example, truth in a specified finite completed
  interpretation, or derivability in a specified calculus);
- a terminating algorithm sound and complete for that decision problem;
- the relationship between its answers and the shared general model.

Deciding that a formula is not derivable does not generally prove its logical
negation in an arbitrary model. If a core returns Boolean truth using NAF, its
closure/completion interpretation and adequacy theorem are part of the contract.

S01 defines finite ground acyclic resolution as P0, certified decidable extensions
as P1, and scoped proof strategies permitting Unknown as P2; see the
[admission contract](lean-admission-contract.md)
for their requirements and shared execution semantics. A possible additional
strategy is finite-domain, function-free,
range-restricted Datalog with stratified NAF and total terminating primitives.
Finite saturation and stratum evaluation would require their own formalization.
Admitting scoped implication, richer quantifiers, higher-order calls, operation
equations, or infinite domains requires an additional decision procedure and proof;
the earlier transition catalogue does not automatically supply one.

### Abstract interpretation

The motivation is predictable automatic analysis. Specify an abstract domain,
sound transfer functions, and a terminating fixed-point computation. A finite-height
domain is one possible route; a suitable widening is another. Abstract interpretation
can analyze undecidable concrete languages soundly, but generally loses precision.
Thus a terminating analysis can still answer "unknown" about a property. Deciding
the core's queries and making an abstraction exact are separate requirements.

### Conservative proof extensions

Proof discovery may be undecidable; checking an explicit finite proof must be a
terminating operation. Primitive computations invoked by the checker must also
terminate, or arrive with independently checkable certificates.

An imported theorem has two distinct checks:

1. Logical validity: its proof is accepted, with all dependencies and assumptions
   recorded. A proof under a local context does not create a global theorem.
2. Operational admissibility: its use as a core fact or rule preserves the core's
   restrictions and termination argument.

For example, a theorem establishing `p(3)` may be installed as an admissible fact.
A theorem `forall n. p(n)` over an infinite domain cannot simply generate infinitely
many core facts. It can remain in the proof layer, yield checked instances on demand
outside core execution, or enter via a separately verified decidable interface.
A proved recursive rule also needs admission checking: truth alone does not ensure
that executing the rule terminates. Admission considers the resulting program,
including stratification and primitive dependencies, not just the isolated formula.

Never install the procedure that searched for the proof as an unrestricted callback
inside the decidable engine. Install checked evidence or an admitted total operation.

Strict logical conservativity means that the extension proves no new old-language
statements beyond those already entailed by the base theory. Proved lemmas can expose
existing consequences without adding axioms. Soundness in a chosen general model is
not, by itself, a proof of conservativity. A stronger axiom or an external claim true
only in selected models is a theory extension and must be identified as such.

If a theorem lies outside the core language, keep it in the proof environment until
an admissible consequence is proved. This boundary is explicit at program admission;
it must not emerge as an unexpected unsupported-form error during core evaluation.

### Next concrete design step

Implement S01's shared machine and P0/P1/P2 admission definitions with their specified
decision, strategy, and model contracts. Implement theorem admission and the P1/P2
requirements for the broader transitions below. No decision procedure for all
formulas in the common syntax is claimed.

## First worked boundary: `forall x:D_i. naf-not p(x)`

The syntax expands to:

```text
forall x. D_i(x) -> defaultNeg(p(x))
```

Under the project's complement-NAF interpretation, its meaning is: every member
of `D_i` makes `p` false. It does not mean that there is no uniform proof of `p`
for an arbitrary domain member.

Ordinary goal introduction produces:

```text
KB; Gamma |- forall x. D_i(x) -> defaultNeg(p(x))
KB; Gamma, D_i(a) |- defaultNeg(p(a))     -- fresh rigid a
```

The current `Derives.defaultNegIntro` cannot close this obligation: its operand
must have no free variables, and `p(a)` has the free rigid parameter `a`.
Making an eigenparameter rigid does not make it a closed constructor value.

Why ordinary matching failure is insufficient:

```text
D_i contains 1 and 2
KB contains p(1)
p(a) cannot match p(1) with rigid a
but the universal negative is false: 1 is a counterexample
```

The proposed engine should retain a domain-wide refutation obligation and offer
the following strategies, rather than report success from that failed match.

### A. Exhaustive finite-domain proof

Obtain a certified cover `D_i = {d1, ..., dn}` and require certified refutation
of every `p(dj)` under the original context and exact KB. All instances are
required (AND), not alternative witnesses (OR). A proof of any `p(dj)` refutes
the universal negative, provided domain membership is also proved. An unknown
instance keeps the overall result unknown. An empty certified domain satisfies
the universal vacuously.

The cover is a logical premise, not just the list returned by a generator so far.
Unresolved outer parameters also need uniform treatment; instantiating `x` alone
does not necessarily make `p(dj)` closed.

### B. Certified absence of a positive witness

Search for:

```text
exists x. D_i(x) and p(x)
```

Here `x` becomes a flexible metavariable, so `p(1)` can produce the witness `1`.
A sound, exhaustive refutation of this existential establishes absence of every
positive witness. Under complement NAF, this is semantically equivalent to the
universal negative. It is not ordinary failure of a bounded search, nor an
unconditional rewrite between the current derivation rules.

For example, if `D_i` is Nat and `p(1)` is available, the positive witness search
succeeds and rejects the universal negative. If no clause defines `p`, absence
can justify a negative result only with the required completion/closure evidence;
an empty set of rules alone does not force `p` false in every model of the KB.

### C. Symbolic domain-wide proof

For infinite domains, try an induction argument, invariant, or complete symbolic
constraint analysis proving:

```text
for every environment rho satisfying Gamma,
for every d in D_i, p(d) is false in the intended model
```

This is a certificate obligation, not a promise that such a certificate is always
discoverable. Enumeration over an infinite domain cannot establish exhaustion
merely by continuing to find no positive witness.

### Required proof-system decision

The existing ground NAF introduction rule does not automatically reconstruct
these domain-wide results as `Derives` proofs. Options to investigate:

1. Add a scoped NAF introduction rule whose certificate is uniformly adequate
   under every environment satisfying the local assumptions. Prove its soundness.
2. Add a guarded-universal certificate rule, with a domain-wide semantic contract.
3. Where the KB contains enough coverage and negative facts, reconstruct an
   ordinary derivation using those facts and existing rules.

`CertifiedScopedSearch.guarded` and `CounterexampleSearch` already illustrate
semantic domain certificates. They do not establish a general translation of
such certificates into KB-only `Derives`. The counterexample construction there
for a positive universal uses a negative witness; the present negative universal
uses a positive witness under complement NAF. Do not conflate the two searches.

## Machine state and proof obligations

An obligation is `KB; Gamma; Scope |- Goal`, together with a proof continuation.
The machine holds an AND/OR proof tree, metavariables, scope dependencies,
substitutions, residual constraints, solver jobs, and backtracking alternatives.

- AND children must all be proved; OR children are alternative proof attempts.
- Shared answer metavariables must have compatible substitutions across AND
  children. Alternatives have rollback. Branch-local witnesses cannot escape.
- Each obligation owns its local context and scope. Hypotheses introduced in one
  child do not become available in siblings.
- Rigid parameters cannot be assigned. Metavariable bindings obey dependency
  restrictions, propagated through other metavariables as in universe labeling.
- Local assumptions retain captured free parameters. Only explicit binders and
  the global KB's implicitly quantified clause variables are freshened.
- Success carries checked evidence. Running, suspended, or budget-exhausted search
  is not refutation. A failed candidate is not a negative answer about its goal.

General formula support does not imply termination. Fair scheduling and an
effective enumeration of clauses, term instances, and proof alternatives are
prerequisites for a possible completeness argument. `LogicalKb` is currently a
set predicate, not an executable clause enumerator. Equality and NAF extensions
need separate adequacy/completeness hypotheses. No completeness claim is made yet.

## Transition catalogue

These are logical transitions to implement, not yet a fully specified focusing
discipline. Introduction is not always the only search alternative: with arbitrary
formula heads, a goal can also be established directly by a clause or assumption.

### 1. Disjunctive assumptions

```text
Gamma, A or B |- C
    AND: Gamma, A |- C
         Gamma, B |- C
```

Record a `disjElim` continuation. Unlike a disjunctive goal, both cases are needed.
For `(p or q) -> (q or p)`, the two cases prove the goal using different disjuncts.
Answer variables shared outside the case split cannot receive incompatible values.

### 2. Existential assumptions

```text
Gamma, exists x. A(x) |- C
    Gamma, A(a) |- C                    -- fresh rigid a
```

Record `existsElim`; `a` must not occur in the original context or conclusion,
and must not escape through answers or constraints. This is not the flexible
witness used for an existential goal. Example: `(exists x. p(x)) -> exists y. p(y)`
uses `a` internally as the existential witness and discharges its scope.

### 3. Arbitrary implication assumptions

To use `A -> B` when proving `C`, focus on that assumption and create:

```text
Gamma |- A
Gamma, B |- C
```

These are AND obligations with an implication-elimination/proof-substitution
continuation. Contexts remain intuitionistic (assumptions are reusable). Retaining
the implication for other uses is allowed; blindly refocusing forever is not a
search strategy. The eventual scheduler needs fair alternatives and loop control.

`B` need not be atomic: decompose it by the appropriate assumption transitions.
For `((p or q) -> (r or s)) -> t`, the inner implication is a local assumption;
using it requires `p or q`, after which `r or s` requires case analysis to prove `t`.
The formula is processable without being automatically provable.

Correction to an earlier discussion example: `((p -> q) -> r) -> s` is already
Harrop-shaped when `p,q,r,s` are atoms. Nested implication alone is not the boundary.

### 4. Arbitrary clause heads

For `H :- B`, freshen the universally quantified clause variables together,
prove the instantiated `B`, and obtain the instantiated formula `H` with evidence.
It can close a matching goal or be used as an available derived formula.

| Head H | Subsequent action |
| --- | --- |
| `A and C` | Project either component; splitting into two clauses is possible |
| `A or C` | Use case analysis; never choose a disjunct as if it were known |
| `exists x. A(x)` | Introduce a local rigid witness when using the result |
| `forall x. A(x)` | Instantiate as needed; repeated uses may differ |
| `A -> C` | Retain as an implication and use the preceding transition |
| `false` | Close a falsity goal or apply falsity elimination |

Derived facts retain their context and substitution dependencies. Arbitrary
forward generation can diverge; relevance heuristics must coexist with whatever
fair exploration is required by the eventual completeness target.

### 5. Logical negation and falsity

Logical negation is `.imp A .falsity`, or `false :- A`, not `A :- false`.

```text
Gamma |- not-logical A       -> Gamma, A |- false
Gamma, false |- C            -> close by falsity elimination
```

A falsity goal must search for contradictions, denial-clause applications, or
other proofs of falsity. It is not immediate operational failure. A denial clause
`HornClause.goal body` derives falsity after all its body goals are established.

### 6. NAF, including open operands

For `defaultNeg G`, first try assumptions and applicable rules, as for other
goals. An existing proof does not require a new failure search or a groundness
check. When establishing a closed operand through failure, launch the certified
refutation provider with the exact KB and context. A certificate closes the goal;
a proof of `G` defeats this NAF attempt under complement NAF; unfinished search
provides no negative evidence.

For flexible metavariables, retain a dependency and retry after instantiation;
a constructive-negation extension may instead return certified constraints.
Waiting alone is not a complete strategy for existential negative queries: fair
witness search or a constructive solver is needed. Such a solver must specify
which answers its constraints represent and how a final proof is reconstructed.

For rigid parameters, waiting for assignment cannot help. Use a uniform scoped
certificate or a domain strategy as in the first worked case. This requires the
explicit proof-system extension discussed there. In the broader proof layer, an
unresolved certificate obligation remains pending. Admission into the decidable
core requires a terminating complete procedure for the admitted instances.

NAF assumptions are available by identity; they are not automatically implication
assumptions. Current `Derives` does not identify NAF with logical negation.

### 7. Equality goals and equality assumptions

Concrete case: the focused goal is `equal(s,t)`.

1. Try an equal assumption or an equation clause, using ordinary rule selection.
2. If both sides are identical after permitted metavariable assignments, close
   by reflexivity. Do not assign rigid parameters.
3. When an equation clause is selected, push its condition as the next goal and
   save a continuation that closes the original equality after the condition succeeds.

```text
Goal: equal(f(a), g(a))
Rule: equal(f(x), g(x)) :- H(x)
    instantiate x := a
    next goal: H(a)
    on success: finish equal(f(a), g(a))
```

An equality assumption supplies a replacement action:

```text
Context: equal(s,t), P(s)
Goal: P(t)
    select the equality and the occurrence to replace
    obtain P(t) with an equalSubst proof
```

This specifies individual actions, not a complete equality solver. Choosing
replacement occurrences and intermediate equalities remains to be designed.
Failure of syntactic matching only rejects that candidate; it does not prove
value inequality. See [conditional equations](conditional-equations.md).

### 8. Dictionary calls and other operation terms

#### Typeless registry and proved laws

Dictionaries are values in the shared carrier. Names identify dictionaries and
interfaces; membership predicates express their contracts without introducing a
polymorphic type system. Use ordinary relations such as:

```text
OrdDictionary(d)
DomainMember(d, x)
```

The registry connects a dictionary to its inductive domain definition, operation
entries (including nested paths), proved laws, and admitted evaluation contracts.
A domain connection must have checked meaning, for example evidence relating
`DomainMember(d,x)` to `D_i.member(x)`; a table entry alone is not a logical axiom.
Different dictionaries may operate on the same domain.

A law can quantify over dictionary values and their associated domains:

```text
forall d. OrdDictionary(d) ->
    forall x. DomainMember(d,x) ->
    forall y. DomainMember(d,y) ->
        (operation_call(d, less, [x,y]) = True_Boolean ->
         operation_call(d, less, [y,x]) = False_Boolean)
```

This is ordinary guarded quantification, even though the guard depends on d.
`True_Boolean` and `False_Boolean` are values, distinct in notation and role from
logical truth and falsity. The law is supplied with a checked proof in the broader
calculus and enters execution only after the static admission check. It is not
assumed valid for every operation merely named `less`.

Its compiled conditional-rule view is:

```text
operation_call(d, less, [y,x]) = False_Boolean :-
    OrdDictionary(d),
    DomainMember(d,x),
    DomainMember(d,y),
    operation_call(d, less, [x,y]) = True_Boolean
```

Compilation retains the proof of the original law and reconstructs each use by
instantiation and implication elimination. Installing a derived clause into an
extended KB additionally requires preserving model validity and updating any NAF
evidence tied to the exact KB. Neither compilation path creates an unchecked axiom.

#### Command: select a dictionary law

```text
focus: operation_call(myOrd, less, [b,a]) = False_Boolean

select_dictionary_law(focus)
    retrieve candidate laws by dictionary/interface, operation path/name,
        argument count, and conclusion shape
    freshen the selected law's quantified variables
    match the entire conclusion against the focus
    d := myOrd, y := b, x := a
    push FinishDictionaryLaw(originalGoal, lawProof, substitution)
    push_and:
        OrdDictionary(myOrd)
        DomainMember(myOrd,a)
        DomainMember(myOrd,b)
        operation_call(myOrd, less, [a,b]) = True_Boolean
```

Registration evidence or local assumptions may close the guard obligations. The
remaining equation needs its own proof or admitted evaluation. On success of all
obligations, the continuation applies the proved law and closes the original goal
once. A failed candidate restores its choice point; it does not prove the opposite
Boolean result. Generic interface-law candidates still require their guards, even
if the index suggests applicability. Unknown dictionaries require a statically
admitted lookup/matching strategy; indexing never binds rigid parameters.

This particular matching problem is structural: it assigns dictionary and argument
variables, not lambda abstractions. Rules parameterized by dictionaries are not by
themselves a demonstration that general higher-order unification is needed.

#### Command: evaluate a dictionary operation

When a value is required, use the registered, statically admitted evaluator. It must
supply checked value-equality evidence, or use a previously justified total primitive
contract. Evaluation is distinct from selecting a theorem about the result.

For a known dictionary and arguments occurring in an equality goal:

```text
Goal: equal(dictionaryCall(d, path, op, args), result)
    request a checked equation dictionaryCall(d, path, op, args) = v
    if supplied, next goal: equal(v, result)
    continuation: compose the two equalities
```

If the equation has conditions, prove them before using it. If no checked
equation is supplied, this candidate cannot advance; retain the original goal
for other rule/equality candidates. Missing evaluation is not falsity.

This action uses the existing equation-oracle contract; it does not define an
evaluator for arbitrary dictionaries. Dictionary resolution, callable lookup,
and invalid-access behavior need a separate concrete design. A dictionary call
used directly as a proposition additionally needs a proof connecting its value
to truth. Those transitions are not settled here.

Do not trigger all dictionary laws merely because an operation term occurs as
data. Law selection is driven by the focused proof goal; value evaluation is
driven by a demand for the operation's result. Static admission must check the
resulting call/rule dependencies: even a finite registry of true laws can support
cyclic proof search. An admissible execution strategy, not theorem validity alone,
is required for a Ready plan.

### 9. Flexible predicate calls and flexible clause heads

`ho_apply` is an explicit operation of the search language, not merely a matcher
implementation detail. Elaboration preserves it:

```text
E(ho_apply(P, args)) = Term.hoApply hoApplySymbol E(P) (map E args)
```

In the foundation model this evaluates through `application hoApplySymbol`.
`Model.holds_hoApply` relates its truth to direct application when the predicate
is a symbol value. It does not supply a general evaluator for every carrier value.

Machine dispatch for a focused `ho_apply(P, args)`:

1. Apply the current substitution to P and the arguments.
2. If P is a known symbol p, continue with the direct goal p(args), saving a
   `hoApplyIntro` continuation. The direct call still needs core admission.
3. Otherwise try assumptions and clauses for the whole ho_apply goal, respecting
   rigid names and shared substitutions. Matching an assumption can bind a
   flexible predicate variable but cannot assign a rigid predicate parameter.
4. If P is flexible, an admitted finite predicate-candidate set permits a choice
   of P := symbol(p) followed by step 2. A dependency on an earlier binding may
   instead permit a statically checked scheduling action. Neither capability is
   implicit in the syntax. General predicate synthesis is a proof-layer problem.
5. If P is rigid, retain the application as an opaque proposition. Use evidence
   about that application; never enumerate assignments to P. An extension may
   provide further checked rules, but an arbitrary carrier value is not executable
   just because it occupies the predicate position.

For example, the assumption ho_apply(q,[a]) proves the identical goal even when
q is rigid. Against goal ho_apply(?P,[a]), that assumption can instead supply
?P := q if the scope dependency permits it. No evaluation of q is needed.

Before runtime, admission must justify the applicable evidence/call strategy and
its dependencies. An unknown predicate does not automatically require rejection
if the goal follows directly from a local assumption. Conversely, symbol binding
alone does not establish termination or completeness of the resulting predicate
call. Missing higher-order capabilities must be reported during admission, not
discovered as a runtime request for a proof.

#### Commands: clause selection and ho_apply conversion

These are proposed abstract-machine commands, not existing Anthill kernel opcodes.
They operate on a focused goal, scoped context, substitution, choice points, and
proof continuations. `symbol(p)` below is the term `.app p []`.

**`select_clause(G)`** builds alternatives for the focused atomic goal.

For an ordinary goal `p(args)`, candidates include:

- ordinary heads indexed by p and argument count;
- compatible concrete heads `ho_apply(symbol(p), args')`;
- flexible heads `ho_apply(P, args')`, including induction clauses.

The last group requires a separate index by application shape/argument count;
indexing only by p would miss induction. Candidate sources include KB clauses
and local rules, with their provenance and scope retained. Existing local facts
are also tried by assumption lookup. Goal-side concrete ho_apply calls are
normalized by `ho_goal` below before this lookup.

For each selected candidate, save the remaining alternatives and a rollback point,
then execute `enter_clause`. Selection does not prove the clause body or assert
its head as a fact. General compound heads still use the actions in section 4.

**`enter_clause(candidate, G)`** checks and applies one candidate.

```text
1. Freshen its quantified template variables, preserving captured parameters.
2. Match/unify its head against G using the admitted matching procedure.
3. Check the substitution, rigid dependencies, and capture-safe instantiation.
4. Apply the same substitution to head and entire body.
5. Save FinishClause(candidate, substitution, headEvidence, originalGoal).
6. Replace the focus with the instantiated body (AND of its obligations).
```

For a flexible head and an ordinary target, the matching view is:

```text
head: ho_apply(?P, args')
goal: p(args)
    bind ?P := symbol(p)
    match args' against args
```

This assigns fresh clause variables, never a rigid predicate parameter. For the
existing unary certificate path, the target argument must be a rigid variable.
More general argument matching needs a separately justified implementation.

When the body succeeds, `FinishClause` constructs the clause application proof.
If its proved head is `ho_apply(symbol(p), args)` but the original goal was
`p(args)`, execute `ho_elim` on that proof before returning. The original goal is
completed once. No head is made available before the body is proved.

A rejected candidate or an unsuccessful body restores its rollback point and
tries the next candidate. A matcher capability gap is not evidence of failure:
core admission must have excluded that gap or supplied the required extension.

Global clauses reconstruct with `Derives.clause`; a local rule reconstructs from
its assumption/derived proof with explicit universal elimination and implication
elimination. Local captured parameters are not implicitly universally quantified.

**`ho_goal`** reduces a concrete indirect goal to a direct goal.

```text
focus: ho_apply(symbol(p), args)
    push FinishHoGoal(originalGoal)
    focus := p(args)

on direct-goal success with proof d:
    return Derives.hoApplyIntro(d)
```

Although this command removes ho_apply from the runtime goal, its proof
continuation uses **introduction**, because it must prove the original indirect
goal. It does not evaluate or instantiate an unknown P.

**`ho_elim(d)`** converts already available evidence.

```text
input proof d: ho_apply(symbol(p), args)
output proof: p(args) = Derives.hoApplyElim(d)
```

Use this command after a clause with an indirect head succeeds, or when a local
indirect assumption is used for a direct goal. Index such assumptions under the
direct predicate as well, retaining their original proof and conversion.

Do not implement the two proof directions as an unguarded loop of goal rewrites
`p(args) -> ho_apply(symbol(p), args) -> p(args)`. Normalize concrete calls to
the direct form; consider indirect heads through candidate selection. Convert
evidence only when required by the original goal or selected clause.

#### Induction trace

Let the KB contain the following model-validated induction clause:

```text
ho_apply(P, n) :-
    Nat(n),
    ho_apply(P, zero),
    forall k. Nat(k) ->
        (ho_apply(P, k) -> ho_apply(P, succ(k))).
```

For a focused goal `reachable(a)` with rigid a and local evidence `Nat(a)`:

```text
select_clause(reachable(a))
    choose the induction clause from the flexible-head index

enter_clause(induction, reachable(a))
    P := symbol(reachable), n := a
    push FinishClause(..., originalGoal = reachable(a))
    push_and:
        Nat(a)
        ho_apply(symbol(reachable), zero)
        forall k. Nat(k) ->
            (ho_apply(symbol(reachable), k) ->
             ho_apply(symbol(reachable), succ(k)))
```

The first obligation uses the local membership evidence. `ho_goal` turns the
second into `reachable(zero)`. For the third, introduce fresh rigid b and local
assumptions `Nat(b)` and `ho_apply(symbol(reachable), b)`; `ho_goal` makes the step
goal `reachable(succ(b))`. The induction hypothesis is available as `reachable(b)`
through `ho_elim`. The base and step still need proofs from available rules.

When all three obligations succeed, `FinishClause` obtains
`ho_apply(symbol(reachable), a)` by clause application and uses `ho_elim` to
finish `reachable(a)`. No predicate enumeration or lambda-valued substitution is
needed: the target symbol determines P.

This trace specifies a proof attempt, not a termination argument. Repeatedly
selecting induction on its own subgoals can diverge. Core admission therefore
needs an admitted induction strategy with its subgoal contracts, or an explicit
proof-layer application; admitting the head match alone is insufficient.

#### Existing proof support

`MillerCertificates.UnaryMatch` checks the symbol-valued unary head match against
a rigid argument. `Expansion.toDerives` already composes clause application with
`hoApplyElim`. `MillerResolution.Proves.certifiedClause` exposes that checked step.
`Derives.hoApplyIntro` and `Derives.hoApplyElim` justify the two evidence conversions.
The commands, indexes, scheduler, and continuations specified here remain to be
implemented; the existing certificate path is not a general unification engine.

A rejected proposal rejects that candidate, not the goal. If the predicate is
an unresolved metavariable, or matching needs an unrepresentable lambda-valued
answer, the general transition still needs design. Saying "use a higher-order
solver" does not settle it. `Term` has no general lambda-abstraction constructor.
This remains an explicit design gap in the broader proof layer. Admission into
the core requires a separately established decidable matching/call discipline.

### 10. Raw variables, literals, and formula-valued arguments

For an opaque term in goal position, the concrete actions currently identified
are assumption lookup and clause selection. If a permitted metavariable binding
reveals a logical constructor, dispatch on that constructor again. A bare rigid
parameter cannot be assigned to reveal structure.

There is no generic transition "evaluate any term as a Boolean" in the current
model. Literal truth and callable-value interpretation require explicit contracts;
their general execution is still a design question. Logical constructors inside
data arguments are not automatically goals.

## Baseline goal transitions retained from the Harrop machine

| Goal | Action |
| --- | --- |
| `true` | Close with truth introduction |
| `A and B` | AND obligations with compatible answers |
| `A or B` | OR alternatives |
| `A -> B` | Prove B under local A, then discharge A |
| `forall x. A(x)` | Introduce a fresh rigid parameter |
| `exists x. A(x)` | Introduce a fresh flexible witness with scope restrictions |
| Atomic/opaque goal | Identity, clause use, applicable left rules, or solver evidence |

Universal assumptions can be instantiated repeatedly. Conjunctive assumptions
provide both components. These operations must remain available even when the
current goal is compound; otherwise arbitrary formula assumptions can be missed.

## Extension interface and next design questions

Sections 7–10 record concrete candidate actions and remaining gaps. They are not
a completed general solver design. Continue by tracing one focused expression at
a time: state before the action, subgoals, saved continuation, success, and failure.

Each extension declares its trigger, generated obligations, scope effects,
residual constraints, and proof reconstruction contract. A proposed answer must
either reconstruct current `Derives`, use a separately proved extension of that
calculus, or be explicitly classified as model-relative semantic evidence.

The next decisions are:

1. Which scoped/domain NAF certificate rule supports the first worked case?
2. What focusing and fair scheduling discipline covers all positive `Derives`
   rules while preserving efficient Harrop execution?
3. How are shared substitutions and witness scopes represented across AND cases?
4. What effective KB and extension interfaces replace semantic set membership?
5. Which equality/callability contracts are part of the executable environment?

Acceptance examples should include every catalogue row, both quantifier orders
`forall x. exists y. y=x` and `exists y. forall x. y=x`, and the domain-wide NAF
example with a positive fact at one domain member. These should become meaningful
implementation tests when an executable transition relation exists.
