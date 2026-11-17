## Attributes

- id: WI-20261026-5G8F5-s14-implement-dictionary-law
- created: 2026-10-26T08:32:35Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-17T22:19:29Z

- acceptance: lake build

- depends_on: WI-20261026-9C19E-s13-specify-checked-typeless, WI-20261026-WHDHK-s09-implement-left-rule, WI-20261103-2QMVP-s20-use-checked-lemmas-inside, WI-20261107-JA6WZ-s22-answers-yes-no-unknown-and

- tags: resolution-machine

## Description

S14: Dictionary operations by total evaluators; laws as checked lemmas

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: dictionary operations inside the fast fragment, and dictionary laws as statements (docs/fast-decision-routes.md). Reorganized 2026-11-07: law selection by search is P3, a proof producer outside the KB module, and is not part of this item.

Acceptance:
- Own the initial P1 dictionary operation/equality route: a registered total concrete evaluator (using the Nat ordering example), its declared decision problem, and termination, soundness, and completeness proofs. A bare operation term is evaluated on value demand, not by firing laws.
- Evaluation equations reconstruct with the existing equation/implication rules or the explicit equation-oracle contract, preserving exact-KB NAF dependencies. They export as Term proof trees with known terminating rule and certificate checks through S08, and the exported trees are proved to pass checking. Trusting an evaluator callback or an oracle assertion is insufficient.
- Dictionary laws are statements, used only as checked lemmas (S20). For the goal less(myOrd,b,a)=False_Boolean, the proved asymmetry law used as a checked lemma generates OrdDictionary(myOrd), both DomainMember obligations, and less(myOrd,a,b)=True_Boolean; all conditions succeed before the goal closes, and rollback restores rejected candidates. A goal that needs a law with no checked lemma is Undecided, naming the law.
- Tests: the Nat ordering example, unmet domain guards, nested dictionary paths, and missing evaluator evidence (Undecided).
- Structural dictionary matching is not mislabeled general higher-order unification; symmetric laws do not silently become unrestricted rewriting.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs. Documentation-only work is checked against its stated deliverables; a build alone does not establish them.
Design references: docs/fast-decision-routes.md, docs/resolution-state-machine.md, docs/resolution-implementation-plan.md.

## Changes

### 2026-11-07T18:44:37Z — feedback — user

From S13 (dictionary registry, docs/dictionary-registry.md): the evaluator computes with S13's primitive contracts (Primitive.Holds: total on the declared argument domains, results in the declared result domain), registered per dictionary. In the Nat/Bool registry (Resolution/OrderRegistry.lean) less and equal carry contracts; compare has none, since its Ordering results lie in no declared domain. Laws are statements with a validity theorem (law_valid), not KB clauses: making them checked lemmas (S20) and the conditional-rule view are S14's. Generated clauses give I(n) and DomainMember(n, X) :- D(X) only; the converse D(x) from DomainMember(n, x) is a model theorem (domainMember_iff). A declared access evaluates by access_eval; an unknown name (aliasOrd in the example) is a blocker, never No.

### 2026-11-09T17:52:26Z — feedback — user

From S20 (2026-11-09): the machine side of laws as checked lemmas is in place. An equation conclusion is backchained by lemmaRule, the law's premises becoming obligations of the run in order, and exported as a reference re-checked at the use site (trace law : ∀1. (q(1) → f(1) = c) in Tests/Resolution/Lemmas.lean). The run's lemmas are sound when they give Derives (Machine.Lemmas.Sound): a law used this way is a P1.Lemma entry with a proof term checked by the run's checker; a law known only by its validity theorem (law_valid) needs its own route to Derives.

### 2026-11-17T22:11:37Z — feedback — user

Review before delivery (2026-11-18): acceptance met. The Nat ordering route decides call = result as a DecisionContract (decide_sound, decide_refutes, evaluate_total), run with its own value check (check?_true, check?_false, check?_complete); evaluation on value demand (Strategy.withEvaluation); laws only as checked lemmas through structurally matched views, the asymmetry trace generating OrdDictionary, both DomainMember guards, and less(natOrd, a, b) = true in order, with rollback across dictionaries and Undecided naming a missing law; unmet guards, nested paths, and missing evaluators traced. Exported trees: the decision's evaluation node is proved accepted (Route.answer_accepted); a run's export is checked before Yes, and the whole-run export theorem is S15/S16's, as for S09 and S20. Scope moved: dictionary operations inside the fast fragment become IR primitives under the decision IR (S29), composed at every call site in S15.

