## Attributes

- id: WI-20261117-06YN9-s27-decision-ir-syntax-checker
- created: 2026-11-17T20:23:45Z

- status: Claimed
- status_agent: claude
- status_at: 2026-11-18T07:09:21Z

- acceptance: lake build

- depends_on: WI-20261107-7PQMQ-s23-moded-structural-recursion, WI-20261107-R9YMZ-s24-tabled-backtracking-on-the, WI-20261107-JA6WZ-s22-answers-yes-no-unknown-and, WI-20261026-NG07C-s07-build-the-initial-static

- tags: resolution-machine

## Description

S27: Decision IR: syntax, checker, finiteness evidence, and semantics

Current scope: Lean formalization in /Users/rssh/work/oss/anthill-mod-kb-spec only. Rust-model/component development has its own separate scope. Use the existing Term representation and semantic infrastructure; do not add parser/frontend work, redesign runtime term representation, bootstrap Rust crates, or implement production APIs here. Anthill docs/proposals are optional requirements references. No Rust or Anthill source changes/builds are prerequisites. Executable definitions in this ticket mean Lean functions or abstract-machine relations supporting the proofs.

Scope: the IR of docs/decision-ir.md (decided with the user, 2026-11-17): the Lean type of the programs decisions run on, its checker and evidence classes (P0 ⊂ P1 ⊂ P2), and its semantics, connected to the models the answers are about. The IR is a type for admitted programs; Term stays the representation of the KB, the queries, and the proofs.

Acceptance:
- Types: predicates with arities, declared modes, and kinds (defined, open by a marker case, guard, primitive); rules (definitions); derived rules (from checked lemmas, never in the completion); denials; literals (a call with inputs and outputs, NAF of an atom with every name bound, data equality and disequality, a guard, a primitive, a marker atom); queries (the context's conditions, the atoms to decide, the answer names).
- The checker, decidable: every literal's inputs bound, read left to right (S23's scan on the IR); every data name guarded; a guard binds its name only over a finite domain. Finiteness evidence for P1: data-term inputs on every call of the dependency closure (calls_bounded), finitely many derivable answers (outputs_bounded, calls_decrease), and no free output on a recursive call of a component that does not decrease. P2 without the evidence. S07's P0.Ground embeds as the ground acyclic case.
- Semantics: key interpretations and the consequence operator (S24's Tabled/Fixpoint) extended to guards (exact), primitives (by their evaluators), and markers (free); the completion's models over keys are its fixpoints.
- Herbrand reduction: for a program and a closed query whose data names are all guarded, truth in every model of the completion realizing the admission signature is truth in every key fixpoint.
- Relevance: the relevant program of a query (the ground rule instances its calls can use, for derived and for possible answers), finite under the P1 evidence; the completion's models restricted to it are the models of its completion, given a model of the rest of the KB.
- Rigid parameters: settle which queries with parameters are P1 (genericity over values outside the relevant data terms, or a split by domain closure) and prove it; the others are P2.
- Traces: path over a cycle, a ground query P1 and ∃Y. path(a, Y) P2; append(+, +, −) P1, decreasing; a self-supporting cycle with a free output P2; a lowered program with its guards P1; a P0 input as P0; the size of each relevant program.

Validation: lake build and focused Lean tests/examples appropriate to the changed definitions and proofs.
Design references: docs/decision-ir.md, docs/fast-admission.md, docs/tabled-evaluation.md, docs/answers.md.

## Changes

### 2026-11-18T05:47:01Z — feedback — user

From S24's review (2026-11-18), for the finiteness evidence: (1) compose S23's per-component bounds along the component order, since a body may construct a lower component's input: p(X) :- q(succ(X)). q(Y). is S23-P1 and S24 answers it Yes, but calls_bounded read per component would make it P2 (this composition was S15's in the 2026-11-08 S24 notes). (2) Bound term growth by the bodies, not the symbols: thirteen calls dup(X, Y) :- Y = pair(X, X) in a row reach 8191 nodes, past S24's (s+1)^(p+1) limit of 4096. (3) Contexts are sets: an assumption repeated along a recursion (p(succ(X)) :- (r → p(X))) makes no new call; S24's repeat-free contexts cut it. (4) S23-P1 queries that leave an output free on a recursive call of a component that does not decrease (path(a, Y) over a cycle) are P2 here; say so where the profiles move.

### 2026-11-18T07:13:29Z — feedback — user

Decided with the user (2026-11-18), rigid parameters: a parameter the query's conditions guard by a finite domain (a declared enumeration of its members) splits into one ground query per member, and the query is P1 when every instance is (Yes when all are Yes, No when all are No, Unknown otherwise). Unguarded parameters and parameters over infinite domains are P2. Genericity over values outside the relevant data terms is not taken.

### 2026-11-18T08:01:10Z — feedback — user

Progress (claude, 2026-11-18): Resolution/IR/ added. Syntax (Kind, Predicate, Goal, Rule, Program, Query; rendering to Term: Goal.toTerm, Program.clauses, signature, completion). Check (declarations, data, the left-to-right binding scan, Program.check with S22 blockers; WellFormed, QueryOk). Evidence (call patterns: vertices are predicates with the arguments a call binds; the vertex graph from the query, closed; levels certified by the checks; notes: growingCall, freeOutput, unguarded, parameter, unclosed; classify: P0, P1, P2 notes, Undecided). Semantics (Program.base: guards exact, primitives by evaluators, markers free; Realizes, Models, meaning; KeyFixpoint; keyModel_models_iff via S24's fixpoint_iff_models; keyFixpoint_models). Herbrand (herbrand_fixpoint: a model's atoms over ground keys are a key fixpoint; herbrand: for guarded programs and closed queries Yes, No, Unknown mean the same over the models and over the key fixpoints). Relevance (Ans and Passes: possible answers of calls leaving outputs free; Relevant, Entry, Instance; ans_complete by induction on level then size; the splitting theorem relevant_of_fixpoint and fixpoint_of_relevant). Traces in Tests/Resolution/IR/Evidence.lean. Open: finiteness of the relevant program under the evidence, its computation and sizes in traces, the rigid-parameter split theorem, the P0.Ground embedding, docs.

### 2026-11-18T08:06:07Z — feedback — user

Progress (claude, 2026-11-18, later): Parameters (p1_parts: P1 gives WellFormed, Guarded, QueryOk, notes = [], guarded answers; closed_of_parts; Query.instantiate, Enumerates, Splits; meaning_split: with exact finite enumerations a query's Yes, No, Unknown are its ground instances'). Remaining, planned: (1) finiteness of the relevant atoms under the evidence: data-term outputs sound for possible answers (induction on Ans with flow soundness along Passes; constants include guard members), a computable instance enumerator for a rule body under a pattern given answer lists (complete for passing instances), finitely many possible answers per call (induction on level then size), relevant calls finite by induction on levels with same-level calls within the data terms of the level's entry calls (growing = []); (2) the relevant program computed by saturation with fuel, equal to the relevant set when stable, and sizes in traces; (3) S07's P0.Ground into the IR, classified P0 (compound NAF operands by auxiliary predicates or excluded); (4) docs: an implementation note beside decision-ir.md, README, plan row.

### 2026-11-18T08:30:14Z — feedback — user

Progress (claude, 2026-11-18, enumerator): IR/Enumerate: matchTerm/matchAll with completeness (matchTerm_complete), Faithful and Gives partial substitutions, stepEnvs and bodyEnvs (the partial substitutions passing a body, answers supplied per free call), Scans.mono, stepEnvs_complete and bodyEnvs_complete (every passing instance extends a computed partial substitution, coverage required only at the body's free calls, which lets the finiteness proof supply lower-rank answers from its induction). Next: (1) finitely many possible answers per call (induction on level then size; answers from the induction, bodyEnvs_complete, then the heads instantiated); (2) data-term outputs sound for Ans and the flow invariant along Passes; relevant calls finite by levels; (3) saturation with fuel and sizes in traces; (4) P0.Ground embedding; (5) docs.

### 2026-11-18T08:48:17Z — feedback — user

Progress (claude, 2026-11-18, finite answers): Evidence checks every vertex binds its predicate's declared inputs (covering, uncovered notes as unclosed). IR/Finite: start_covers, answerList (lower-rank answers chosen from the induction), ans_finite: with the evidence and exact finite enumerations, a vertex leaving an output free has finitely many possible answers at each value of its bound arguments (induction on level then size; bodyEnvs_complete; heads instantiated). Program.level and vertices are made locally irreducible in the proofs (unfolding them timed out). Docs: docs/ir-programs.md written for the parts done; README row, plan link, decision-ir.md status and the settled parameter rule. Next: relevant calls finite (restate growing over a recursive flowCalls per rule; data-term outputs sound for Ans by mutual induction with the flow invariant along Passes; constants = closed data terms of the rules and guard members; invariant: every relevant call's values are data terms of an entry call at its level; downward induction on levels, entry calls from the query's or higher levels' finitely many instances); then the computed relevant program and sizes; the P0.Ground embedding.

### 2026-11-18T08:59:14Z — feedback — user

Progress (claude, 2026-11-18, data terms): Evidence's growing check now walks flowCalls (a recursive per-rule list carrying the names bound and the flow's data-term names before each call). IR/Finite: groundTerms (closed data subterms of the rules, finite guards' members), subterm and closedness lemmas under subst, Holds (names hold data terms of the head's bound values and groundTerms), small_sound, FlowSound and AnsSound, flow_free and flow_fixed (one literal), ans_data (data-term outputs sound for possible answers, by Ans.rec) and passes_flow (by Passes.rec); the mutual recursion is written with the generated recursors (structural recursion over the mutual proofs was not inferred). Next, relevant calls finite: (a) for a passing instance, every call in bodyCalls has a flowCalls entry whose data-term names hold (one step = flow_free/flow_fixed with an empty rest); (b) growing = [] makes same-level calls' bound values data terms of the head's bound values (small_sound); (c) invariant by induction on Relevant: every relevant call's values are data terms of an entry call at the same level (query and condition calls, or calls made from a strictly higher level); (d) downward induction on levels (levels at most the vertex count): entry calls at a level come from the query's enumerated instances (bodyEnvs from the parameters) and from higher levels' finitely many calls, their entries (full atoms or answerList), and their enumerated instances; calls at the level are tuples over dataTerms of the entry calls' values (S24's tuples). Then entries finite, the computed relevant program with sizes in traces, the P0.Ground embedding, docs for Enumerate/Finite.

### 2026-11-18T10:49:02Z — feedback — user

From the /code-review of the uncommitted S27 work (2026-11-18), decided with the user: (1) denials join the relevant program: denial instances that the relevant atoms meet are decided with the query, their call patterns join the evidence graph, and a denial without finiteness evidence makes the query P2 (as S23's denial notes did); (2) an unguarded name stays a P2 note (carrier-ranged, outside the Herbrand reduction), not a checker blocker; decision-ir.md's well-formedness paragraph to say so. Also fixing from the review: relevance read on closed queries, parameterized queries classified through their enumerated split instances; finite guards mean their listed members (checked ground), so the split needs no unchecked Enumerates; P0 only with no notes, and as S07's class (atom-level acyclic, no denials, call and NAF bodies); the split's combination stated as meaning_split proves it (an instance whose conditions no model satisfies is both Yes and No); stepEnvs checks answer predicates and ground evaluator outputs; blocker sites, paths, and kinds; the classifier's graph computed once.

### 2026-11-18T12:08:54Z — feedback — user

Progress (claude, 2026-11-18, review cleanup): the items the /code-review cut by its cap. The uncovered and unranked notes never fire, now proved and removed: levelIn_le (in a closed graph no call goes to a higher level, by S23's reach) and covering_of_check (every vertex of a checked query binds its declared inputs); ans_finite takes QueryOk. What no note gives is the structure Program.Evidence (evidence_of_notes, Evidence.ranked) instead of a 7-tuple. The rank step shared by ans_complete and ans_finite is call_rank. Reuse: closeVertices is S24's untilStable, Machine.nodup_map_inj replaces unique_of_nodup, sat_exists replaces satisfies_exists_iff, den_injectives under dens_injective_of and dataKeys_injective_of; Query.instanceSubst shared by instantiate and the split proofs; mem_of_mem_boundArgs for four inline copies; the classify proofs by split. The IR modules build with no warnings (unused section variables omitted, dif_pos replaced, unused hypotheses of atom_iff and small_sound dropped). Not taken: decreases_size and small_sound through S23's Holds (they would need data hypotheses and Enumerate's lemmas before Relevance).

