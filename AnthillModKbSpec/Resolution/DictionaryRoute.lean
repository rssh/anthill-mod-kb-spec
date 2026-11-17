import AnthillModKbSpec.Resolution.DictionaryEvaluation
import AnthillModKbSpec.Resolution.DictionaryLaws
import AnthillModKbSpec.Resolution.P1.Evaluation

/-! # The dictionary route and its answers (S14)

A setup (`Route`) fixes a registry snapshot with its registered evaluations,
the KB's own clauses, the lemmas, and the S08 vocabulary. It builds:

- the **program**: the KB's clauses, then the generated clauses of the
  signature and the registry (`Route.generated`): `I(n)` and
  `DomainMember(n, X) :- D(X)` per registration;
- the **checker**: an S08 snapshot whose KB is the program, the laws' facts,
  and the evaluated equations (`Snapshot.checkSnapshot`), with the evaluation
  rule registered (`P1.evaluationRule`) and no NAF;
- the **strategy**: evaluation first (`Strategy.withEvaluation`), then the
  laws' views matched structurally (`Strategy.withLaws`), then the left
  strategy with the lemmas the program sees (`withLemmas`).

`Route.answer` answers a query under a context:

| Query | Answer |
| --- | --- |
| `call = result` or `result = call`, admitted (`Snapshot.admits?`: the call's arguments and `result` member trees of the contract's domains), the evaluator's value a member tree of the result domain (`Snapshot.check?`) | The decision: Yes, the evaluation node (turned around by `equalSymm` for a call on the right), with no run; No once a run under the context does not prove it |
| Anything else, a run that succeeds and whose export the checker accepts | Yes, the checked proof term |
| A run interrupted by its fuel | Undecided: termination |
| A run with gaps | Undecided, a blocker per gap: at an equation on a dictionary operation, the access S13 blocks, alone; for a declared access, an operation with no evaluator (`dictionary evaluator`) or a call outside its contract (`dictionary domain`), then each law with a view that may conclude it and is not offered (`lemma law`); otherwise the gap's own. What a call lacks is named once |
| An exhausted run | Undecided: a proof. Law search is not a decision: a failed candidate refutes nothing |

The route never answers Unknown. Its answers are about the interpretations
of `Snapshot.Models` that satisfy the KB's own clauses (`Route.meaning`): a
Yes holds in each, a No fails in each (`Route.answer_sound`), and every Yes is
a term the route's checker accepts (`Route.answer_accepted`). The decision is
checked as it runs, so its answers need no evidence that the evaluators are
total: an evaluator that does not answer, or answers outside the result
domain, leaves the equation to a run. With that evidence (`Snapshot.Complete`)
and every rule of the signature listed, every equation the decision contract
decides is answered Yes or No (`Route.answer_definite`), as the contract
decides it (`Snapshot.check?_complete`). A Yes by a run is a derivation in the
checker's KB, reconstructed from the accepted proof term; that KB holds in
these interpretations, the laws' facts by `law_valid` and the evaluated
equations by the evaluations' soundness. -/

namespace AnthillModKbSpec.DictionaryRegistry

open Semantics InductiveDomains AdmissionSignature Machine P1 Answers

variable {Domain Variable Literal Symbol Value : Type}

/-! ## Member trees -/

section Members

variable [DecidableEq Domain] [DecidableEq Symbol]

mutual
/-- A ground constructor term read as a member tree of the domain, by the
listed rules: by the first rule of the domain with the term's symbol whose
fields read the arguments. -/
def memberOf? (rules : List (Rule Domain Symbol)) (domain : Domain) :
    Term Variable Literal Symbol → Option (Tree Symbol)
  | .app symbol args =>
      rules.findSome? fun rule =>
        if rule.result = domain ∧ rule.symbol = symbol then (membersOf? rules rule.fields args).map (Tree.node symbol)
        else none
  | _ => none

/-- Terms read as member trees of their domains, one each. -/
def membersOf? (rules : List (Rule Domain Symbol)) :
    List Domain → List (Term Variable Literal Symbol) → Option (List (Tree Symbol))
  | [], [] => some []
  | domain :: domains, arg :: args =>
      match memberOf? rules domain arg, membersOf? rules domains args with
      | some tree, some trees => some (tree :: trees)
      | _, _ => none
  | _, _ => none
end

variable {sigma : Definitions Domain Symbol} {rules : List (Rule Domain Symbol)}

omit [DecidableEq Domain] [DecidableEq Symbol] in
/-- A node whose children are members of the rule's fields is a member of its
result. -/
theorem member_node {rule : Rule Domain Symbol} (declared : sigma rule) {trees : List (Tree Symbol)}
    (length : trees.length = rule.fields.length)
    (members : ∀ pair ∈ rule.fields.zip trees, InductiveDomains.Member sigma pair.1 pair.2) :
    InductiveDomains.Member sigma rule.result (.node rule.symbol trees) := by
  have built := InductiveDomains.Member.construct (sigma := sigma) declared
    (fun index => trees[index.1]'(by have := index.2; omega)) fun index =>
      members (rule.fields[index], trees[index.1]'(by have := index.2; omega)) (by
        rw [List.mem_iff_getElem]
        exact ⟨index.1, by simp [length], by simp⟩)
  have same : List.ofFn (fun index : Fin rule.fields.length => trees[index.1]'(by have := index.2; omega)) = trees :=
    List.ext_getElem (by simp [length]) fun _ _ _ => by simp
  rwa [same] at built

mutual
theorem memberOf?_sound (listed : ∀ rule ∈ rules, sigma rule) :
    ∀ {domain : Domain} {term : Term Variable Literal Symbol} {tree : Tree Symbol},
      memberOf? rules domain term = some tree → InductiveDomains.Member sigma domain tree ∧ term = tree.toTerm
  | domain, .app symbol args, tree, found => by
      rw [memberOf?] at found
      obtain ⟨rule, inside, read⟩ := List.exists_of_findSome?_eq_some found
      split at read
      · rename_i matching
        obtain ⟨sameResult, sameSymbol⟩ := matching
        obtain ⟨trees, inner, rfl⟩ := Option.map_eq_some_iff.mp read
        obtain ⟨length, members, rfl⟩ := membersOf?_sound listed inner
        subst sameResult sameSymbol
        exact ⟨member_node (listed rule inside) length members, by simp [Tree.toTerm]⟩
      · cases read
  | _, .var _, _, found | _, .lit _, _, found | _, .truth, _, found | _, .falsity, _, found
  | _, .conj _ _, _, found | _, .disj _ _, _, found | _, .imp _ _, _, found | _, .defaultNeg _, _, found
  | _, .forallVar _ _, _, found | _, .existsVar _ _, _, found | _, .dictionaryCall _ _ _ _, _, found
  | _, .equal _ _, _, found => by simp [memberOf?] at found

theorem membersOf?_sound (listed : ∀ rule ∈ rules, sigma rule) :
    ∀ {domains : List Domain} {args : List (Term Variable Literal Symbol)} {trees : List (Tree Symbol)},
      membersOf? rules domains args = some trees →
        trees.length = domains.length ∧ (∀ pair ∈ domains.zip trees, InductiveDomains.Member sigma pair.1 pair.2) ∧
          args = trees.map Tree.toTerm
  | [], [], trees, found => by
      simp only [membersOf?, Option.some.injEq] at found
      subst found
      simp
  | domain :: domains, arg :: args, trees, found => by
      rw [membersOf?] at found
      split at found
      · rename_i tree rest first others
        cases found
        obtain ⟨member, rfl⟩ := memberOf?_sound listed first
        obtain ⟨length, members, rfl⟩ := membersOf?_sound listed others
        refine ⟨by simp [length], ?_, rfl⟩
        simp only [List.zip_cons_cons, List.mem_cons, forall_eq_or_imp]
        exact ⟨member, members⟩
      · cases found
  | [], _ :: _, _, found | _ :: _, [], _, found => by simp [membersOf?] at found
end

theorem membersOf?_isSome :
    ∀ {domains : List Domain} {trees : List (Tree Symbol)}, trees.length = domains.length →
      (∀ pair ∈ domains.zip trees, (memberOf? rules pair.1 (pair.2.toTerm : Term Variable Literal Symbol)).isSome) →
      (membersOf? rules domains (trees.map Tree.toTerm : List (Term Variable Literal Symbol))).isSome
  | [], [], _, _ => by simp [membersOf?]
  | domain :: domains, tree :: trees, length, each => by
      obtain ⟨first, firstFound⟩ := Option.isSome_iff_exists.mp (each (domain, tree) (by simp))
      obtain ⟨rest, restFound⟩ := Option.isSome_iff_exists.mp
        (membersOf?_isSome (by simpa using length) fun pair inside => each pair (by simp [inside]))
      simp [membersOf?, firstFound, restFound]
  | [], _ :: _, length, _ | _ :: _, [], length, _ => by simp at length

/-- The listed rules read every member tree, when every rule of the definitions
is listed. Two rules of one domain with one symbol are both tried. -/
theorem memberOf?_complete (covering : ∀ rule, sigma rule → rule ∈ rules) {domain : Domain} {tree : Tree Symbol}
    (member : InductiveDomains.Member sigma domain tree) :
    (memberOf? rules domain (tree.toTerm : Term Variable Literal Symbol)).isSome := by
  induction member with
  | @construct rule declared children _ inner =>
      simp only [Tree.toTerm, memberOf?, List.findSome?_isSome_iff]
      refine ⟨rule, covering rule declared, ?_⟩
      simp only [and_self, ↓reduceIte, Option.isSome_map]
      apply membersOf?_isSome (by simp)
      intro pair inside
      obtain ⟨index, bound, rfl⟩ := List.mem_iff_getElem.mp inside
      simp only [List.length_zip, List.length_ofFn, Nat.min_self] at bound
      simpa [List.getElem_zip, List.getElem_ofFn] using inner ⟨index, bound⟩

end Members

/-! ## Admission and the decision as run -/

section Admission

variable [DecidableEq Domain] [DecidableEq Symbol]

/-- The target admits the result: the call's arguments read as member trees of
the contract's argument domains, and the result as a member tree of its result
domain. -/
def Target.admits (rules : List (Rule Domain Symbol)) (target : Target Domain Variable Literal Symbol)
    (result : Term Variable Literal Symbol) : Bool :=
  (membersOf? rules target.primitive.arguments target.arguments).isSome &&
    (memberOf? rules target.primitive.result result).isSome

/-- The equation is admitted for the decision: the call has a target that
admits the result. -/
def Snapshot.admits? (snapshot : Snapshot Domain Variable Literal Symbol)
    (evaluations : List (Evaluation Variable Literal Symbol)) (rules : List (Rule Domain Symbol))
    (equation : Equation Variable Literal Symbol) : Bool :=
  match snapshot.target? evaluations equation.call with
  | some target => target.admits rules equation.result
  | none => false

variable {snapshot : Snapshot Domain Variable Literal Symbol} {evaluations : List (Evaluation Variable Literal Symbol)}
  {rules : List (Rule Domain Symbol)}

/-- What an admitting target establishes, with the listed rules declared. -/
theorem Target.admits_decides (listed : ∀ rule ∈ rules, snapshot.signature.signature.data.definitions rule)
    {equation : Equation Variable Literal Symbol} {target : Target Domain Variable Literal Symbol}
    (targeted : snapshot.target? evaluations equation.call = some target)
    (admitted : target.admits rules equation.result = true) : snapshot.Decides evaluations equation := by
  simp only [Target.admits, Bool.and_eq_true, Option.isSome_iff_exists] at admitted
  obtain ⟨⟨trees, arguments⟩, ⟨result, resultFound⟩⟩ := admitted
  obtain ⟨_, members, argumentsEq⟩ := membersOf?_sound listed arguments
  obtain ⟨resultMember, resultEq⟩ := memberOf?_sound listed resultFound
  exact ⟨target, trees, result, targeted, argumentsEq, members, resultMember, resultEq⟩

/-- The admission check is sound: an admitted equation is one the decision
contract decides. -/
theorem Snapshot.admits?_decides (listed : ∀ rule ∈ rules, snapshot.signature.signature.data.definitions rule)
    {equation : Equation Variable Literal Symbol} (admitted : snapshot.admits? evaluations rules equation = true) :
    snapshot.Decides evaluations equation := by
  unfold Snapshot.admits? at admitted
  split at admitted
  · rename_i target targeted
    exact Target.admits_decides listed targeted admitted
  · cases admitted

/-- The admission check is complete when every rule of the signature is listed:
each equation the decision contract decides is admitted. -/
theorem Snapshot.admits?_complete
    (covering : ∀ rule, snapshot.signature.signature.data.definitions rule → rule ∈ rules)
    {equation : Equation Variable Literal Symbol} (decides : snapshot.Decides evaluations equation) :
    snapshot.admits? evaluations rules equation = true := by
  obtain ⟨target, trees, result, targeted, arguments, members, inside, resultEq⟩ := decides
  have length := (Snapshot.target?_spec targeted).2.2.2.2.2.2.2.1
  simp only [Snapshot.admits?, targeted, Target.admits, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [arguments]
    refine membersOf?_isSome ?_ fun pair inside => memberOf?_complete covering (members pair inside)
    rw [length, arguments, List.length_map]
  · rw [resultEq]
    exact memberOf?_complete covering inside

variable [DecidableEq Variable] [DecidableEq Literal]

/-- The decision as run: an equation its call's target admits, decided by the
evaluator's value, itself read as a member tree of the contract's result
domain. None where any of it is missing: no target, no admission, no value, or
a value that is no member tree. Every check is made here, so its answer needs
no evidence beyond the evaluations' soundness and separation. -/
def Snapshot.check? (snapshot : Snapshot Domain Variable Literal Symbol)
    (evaluations : List (Evaluation Variable Literal Symbol)) (rules : List (Rule Domain Symbol))
    (equation : Equation Variable Literal Symbol) : Option Bool :=
  match snapshot.target? evaluations equation.call with
  | some target =>
      if target.admits rules equation.result then
        (target.evaluation.run target.arguments).bind fun value =>
          if (memberOf? rules target.primitive.result value).isSome then some (Machine.identical value equation.result)
          else none
      else none
  | none => none

/-- What a decision as run reads: the call's target admitting the result, the
evaluator's value, a member tree of the result domain. -/
theorem Snapshot.check?_some {equation : Equation Variable Literal Symbol} {decided : Bool}
    (found : snapshot.check? evaluations rules equation = some decided) :
    ∃ target value tree, snapshot.target? evaluations equation.call = some target ∧
      target.admits rules equation.result = true ∧ snapshot.evaluate evaluations equation.call = some value ∧
      memberOf? rules target.primitive.result value = some tree ∧ decided = Machine.identical value equation.result := by
  unfold Snapshot.check? at found
  split at found
  · rename_i target targeted
    split at found
    · rename_i admitted
      obtain ⟨value, ran, read⟩ := Option.bind_eq_some_iff.mp found
      split at read
      · rename_i member
        obtain ⟨tree, treeFound⟩ := Option.isSome_iff_exists.mp member
        cases read
        refine ⟨target, value, tree, targeted, admitted, ?_, treeFound, rfl⟩
        simp only [Snapshot.evaluate, targeted, Option.bind_some, ran]
      · cases read
    · cases found
  · cases found

/-- The decision as run is the decision contract's, and admits what it decides. -/
theorem Snapshot.check?_decide {equation : Equation Variable Literal Symbol} {decided : Bool}
    (found : snapshot.check? evaluations rules equation = some decided) :
    snapshot.admits? evaluations rules equation = true ∧ decided = snapshot.decide evaluations equation := by
  obtain ⟨_, _, _, targeted, admitted, evaluated, _, rfl⟩ := Snapshot.check?_some found
  exact ⟨by simp only [Snapshot.admits?, targeted, admitted], by simp only [Snapshot.decide, evaluated]⟩

theorem Snapshot.check?_true {equation : Equation Variable Literal Symbol}
    (found : snapshot.check? evaluations rules equation = some true) :
    snapshot.evaluate evaluations equation.call = some equation.result := by
  obtain ⟨_, _, _, _, _, evaluated, _, same⟩ := Snapshot.check?_some found
  rw [evaluated, Machine.identical_iff.mp same.symm]

/-- A No as run fails in every interpretation with sound evaluations that
separates the result domains. -/
theorem Snapshot.check?_false (listed : ∀ rule ∈ rules, snapshot.signature.signature.data.definitions rule)
    {equation : Equation Variable Literal Symbol} (found : snapshot.check? evaluations rules equation = some false)
    {interp : Interpretation Literal Symbol Value hoApplySymbol} (evaluated : snapshot.Evaluated evaluations interp)
    (separated : snapshot.Separated interp) (environment : Environment Variable Value) :
    interp.model.eval environment equation.call ≠ interp.model.eval environment equation.result := by
  obtain ⟨target, value, valueTree, targeted, admitted, valued, valueFound, different⟩ := Snapshot.check?_some found
  simp only [Target.admits, Bool.and_eq_true, Option.isSome_iff_exists] at admitted
  obtain ⟨_, resultTree, resultFound⟩ := admitted
  obtain ⟨valueMember, rfl⟩ := memberOf?_sound listed valueFound
  obtain ⟨resultMember, resultEq⟩ := memberOf?_sound listed resultFound
  have apart : valueTree ≠ resultTree := fun same => by
    rw [same, resultEq, Machine.identical_self] at different
    cases different
  rw [Snapshot.evaluate_sound evaluated valued environment, resultEq, Tree.eval_toTerm, Tree.eval_toTerm]
  exact Snapshot.separates targeted separated valueMember resultMember apart

/-- Completeness: with totality evidence and every rule of the signature listed,
the decision as run decides every equation the decision contract decides, as
the contract does. -/
theorem Snapshot.check?_complete (complete : snapshot.Complete evaluations)
    (covering : ∀ rule, snapshot.signature.signature.data.definitions rule → rule ∈ rules)
    {equation : Equation Variable Literal Symbol} (decides : snapshot.Decides evaluations equation) :
    snapshot.check? evaluations rules equation = some (snapshot.decide evaluations equation) := by
  have admitted := Snapshot.admits?_complete covering decides
  obtain ⟨target, trees, _, targeted, arguments, members, _, _⟩ := decides
  obtain ⟨value, valueMember, evaluated⟩ := Snapshot.evaluate_total complete targeted arguments members
  have ran : target.evaluation.run target.arguments = some value.toTerm := by
    simpa only [Snapshot.evaluate, targeted, Option.bind_some] using evaluated
  have read := memberOf?_complete (rules := rules) (Variable := Variable) (Literal := Literal) covering valueMember
  simp only [Snapshot.admits?, targeted] at admitted
  simp only [Snapshot.check?, targeted, admitted, ↓reduceIte, ran, Option.bind_some, read, Snapshot.decide, evaluated]

end Admission

/-! ## The setup -/

/-- What the route runs on: a registry snapshot with its evaluations, the
signature's listed rules and generated names, the KB's own clauses, the
lemmas, the S08 vocabulary, the evaluation rule's name, the selections of the
left strategy, and the fuel. -/
structure Route (Domain Variable Literal Symbol : Type) where
  snapshot : Snapshot Domain Variable Literal Symbol
  evaluations : List (Evaluation Variable Literal Symbol)
  hoApplySymbol : Symbol
  vocab : Vocabulary Symbol
  rule : Symbol
  names : Nat → Variable
  rules : List (Rule Domain Symbol)
  clauses : List (HornClause Variable Literal Symbol)
  lemmas : List (Lemma Domain Variable Literal Symbol)
  select : Selection Variable Literal Symbol
  cuts : LemmaSelection Variable Literal Symbol
  fuel : Nat

namespace Route

variable [DecidableEq Domain] [DecidableEq Variable] [DecidableEq Literal] [DecidableEq Symbol] [FreshNames Variable]
  (route : Route Domain Variable Literal Symbol)

/-- The generated clauses: the signature's, then one fact and one membership
clause per registration. -/
def generated : List (HornClause Variable Literal Symbol) :=
  signatureClauses route.snapshot.signature route.names route.rules ++
    route.snapshot.registry.dictionaries.flatMap fun registration =>
      [interfaceFact registration,
        domainClause route.snapshot.registry.naming route.snapshot.signature.naming (route.names 0) registration]

/-- The executable program: the KB's clauses, then the generated ones. -/
def program : Program Variable Literal Symbol :=
  ⟨route.clauses.mapIdx (fun index clause => ⟨.lowered index, clause⟩) ++ route.generated.map (⟨.signature, ·⟩),
    guardSymbol route.snapshot.signature⟩

/-- The program's clauses, the laws' facts, and the evaluated equations. -/
def checkSnapshot : P1.Snapshot Variable Literal Symbol :=
  route.snapshot.checkSnapshot route.evaluations route.hoApplySymbol
    (route.program.clauses.map ProgramClause.clause ++ route.snapshot.registry.lawClauses)

/-- The checker: the evaluation rule registered, no NAF. -/
def checker : Checker Variable Literal Symbol :=
  ⟨route.checkSnapshot, NafFailure.disabled, none, [evaluationRule route.rule route.checkSnapshot NafFailure.disabled]⟩

/-- The lemmas the program sees under the checker. -/
def offered : Machine.Lemmas Variable Literal Symbol :=
  lemmasFor route.vocab route.checker route.hoApplySymbol route.program route.lemmas

/-- Evaluation first, then the laws' views, then the left strategy with lemmas. -/
def strategy : Strategy Variable Literal Symbol Unit :=
  Strategy.withEvaluation route.hoApplySymbol route.rule (route.snapshot.evaluate route.evaluations)
    (Strategy.withLaws route.offered (withLemmas route.hoApplySymbol route.program route.offered route.select route.cuts))

omit [DecidableEq Domain] [FreshNames Variable] in
/-- The checker's KB contains the program's clauses. -/
theorem covers : coversProgram route.checker route.hoApplySymbol route.program = true := by
  simp only [coversProgram, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨rfl, fun entry member => List.mem_append_left _ (List.mem_map_of_mem member)⟩

omit [DecidableEq Domain] in
/-- The route's strategy is sound for the checker's KB. -/
theorem strategy_sound : Strategy.Sound route.hoApplySymbol route.checkSnapshot.kb NafFailure.disabled route.strategy :=
  Strategy.withEvaluation_sound (fun _ _ found => Or.inr ⟨_, _, ⟨_, List.mem_singleton_self _, found⟩, rfl⟩)
    (Strategy.withLaws_sound (lemmasFor_sound route.vocab route.checker route.hoApplySymbol route.program route.lemmas)
      (withLemmas_sound route.vocab route.checker route.covers route.lemmas route.select route.cuts))

/-- A run from the query, its names rigid. -/
def run (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    Outcome Variable Literal Symbol Unit Unit :=
  Machine.run route.strategy route.fuel (State.init () [] context goal)

/-- The lemma table of the export. -/
def table : List (Import Variable Literal Symbol) := route.lemmas.map ProofImport.entry

/-- A successful run's export, accepted by the checker for the answer instance. -/
def proved (proof : CompletedProof Variable Literal Symbol Unit Unit) (context : ProofContext Variable Literal Symbol)
    (goal : Formula Variable Literal Symbol) : Option (Term Variable Literal Symbol) :=
  (exportProof route.vocab (fun _ => .truth) proof).filter fun term =>
    decide (checkProof route.vocab route.checker route.table context goal term = .accept)

/-! ## Blockers -/

/-- A call outside its contract: an argument is a member tree of some listed
domain but not of the contract's argument domain at its position. An argument
that reads as no member tree, a name or another call, may still be a member,
and is not outside. -/
def outside (target : Target Domain Variable Literal Symbol) : Bool :=
  (target.primitive.arguments.zip target.arguments).any fun (domain, argument) =>
    (memberOf? route.rules domain argument).isNone &&
      route.rules.any fun rule => (memberOf? route.rules rule.result argument).isSome

/-- What a gap lacks at an equation on a dictionary operation. Where S13 blocks
the access, that alone: every view of a law has the interface guard first,
which no unregistered dictionary meets. Where the access is declared, a
missing evaluator or a call outside its contract (`outside`), then each law
with a view that may conclude it and is not among the `offered` lemmas.
Elsewhere, the gap's own. A gap keeps its goal as written: a dictionary written
as a name the run may have bound by then is classified by its laws only, never
as a missing binding. A goal with the call on the right only is turned around
before it can be a gap. -/
def blockers (offered : List (Symbol × Formula Variable Literal Symbol)) (gap : Gap Variable Literal Symbol) :
    List (Blocker Variable Literal Symbol) :=
  let place : Place Variable Literal Symbol := .reached gap.obligation.context gap.trail
  let path := gap.trail.map Origin.premise
  let goal := gap.obligation.goal
  let needed : Unit → List (Blocker Variable Literal Symbol) := fun _ =>
    (route.snapshot.registry.lawsFor goal fun statement =>
      offered.any fun entry => Machine.identical entry.2 statement).map fun law => ⟨place, path, goal, .lemma law⟩
  let found : List (Blocker Variable Literal Symbol) :=
    match gap.reason, goal with
    | .unsupported, .equal (.dictionaryCall (.var _) _ _ _) _ => needed ()
    | .unsupported, .equal (.dictionaryCall dictionary path' field args) _ =>
        match route.snapshot.registry.access? .value dictionary path' field args.length with
        | .declared _ _ =>
            let contract : List (Blocker Variable Literal Symbol) :=
              match route.snapshot.target? route.evaluations (.dictionaryCall dictionary path' field args) with
              | some target => if route.outside target then [⟨place, path, goal, .construct (.dictionary .domain)⟩] else []
              | none => [⟨place, path, goal, .construct (.dictionary .evaluator)⟩]
            contract ++ needed ()
        | access => (access.blocker? place path goal).toList
    | _, _ => []
  match found with
  | [] => [Blocker.ofGap (fun _ => []) gap]
  | found => found

/-- Two blockers a call lacks alike: the same formula, missing the same law or
the same dictionary evidence. What they lack does not depend on where the run
reached them. -/
def Blocker.repeats (first second : Blocker Variable Literal Symbol) : Bool :=
  Machine.identical first.formula second.formula &&
    match first.missing, second.missing with
    | .lemma law, .lemma other => law == other
    | .construct (.dictionary miss), .construct (.dictionary other) => miss == other
    | _, _ => false

/-- The blockers, each a call lacks kept once, at the first place it was
reached. -/
def Blocker.once (blockers : List (Blocker Variable Literal Symbol)) : List (Blocker Variable Literal Symbol) :=
  blockers.foldl (fun kept blocker => if kept.any (Blocker.repeats · blocker) then kept else kept ++ [blocker]) []

/-! ## Answers -/

/-- What the route's answers carry: a Yes the accepted proof term, a No the
decision, never Unknown. -/
abbrev DictionaryAnswer (Variable Literal Symbol : Type) :=
  Answer (Term Variable Literal Symbol) Unit Empty (Blocker Variable Literal Symbol)

/-- A run's answer: Yes once its export is accepted; its gaps as blockers,
classified against the lemmas the run was offered, what a call lacks named
once. -/
def runAnswer (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    DictionaryAnswer Variable Literal Symbol :=
  match route.run context goal with
  | .success proof _ =>
      match route.proved proof context goal with
      | some term => .yes term
      | none => .undecided [Blocker.unproved goal]
  | .interrupted _ => .undecided [Blocker.interrupted context goal]
  | .opened gaps | .abandoned gaps =>
      let offered := route.offered.statements
      .undecided (Blocker.once (gaps.flatMap (route.blockers offered)))
  | .exhausted => .undecided [Blocker.unproved goal]

/-- The decision of an equation, the call on the left first, then on the
right: the decision and whether the call is on the right. -/
def decision? (left right : Term Variable Literal Symbol) : Option (Bool × Bool) :=
  match route.snapshot.check? route.evaluations route.rules ⟨left, right⟩ with
  | some decided => some (decided, false)
  | none => (route.snapshot.check? route.evaluations route.rules ⟨right, left⟩).map fun decided => (decided, true)

/-- The decision's Yes: the evaluation node, turned around by `equalSymm` when
the call is on the right. -/
def evaluationProof (left right : Term Variable Literal Symbol) (turned : Bool) : Proof Variable Literal Symbol :=
  if turned then .node .equalSymm (.equal left right) [Unfold.evaluation route.rule right left]
  else Unfold.evaluation route.rule left right

/-- The route's answer: the P1 decision of an equation it admits, its Yes with
no run; otherwise a run's. The decision's No is answered once a run under the
context does not prove the goal: a context no interpretation satisfies, one
assuming the goal itself, makes both true, and the route then answers Yes, a
term its checker accepts. -/
def answer (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    DictionaryAnswer Variable Literal Symbol :=
  match goal with
  | .equal left right =>
      match route.decision? left right with
      | some (true, turned) => .yes (encode route.vocab (route.evaluationProof left right turned))
      | some (false, _) =>
          match route.runAnswer context (.equal left right) with
          | .yes term => .yes term
          | _ => .no ()
      | none => route.runAnswer context (.equal left right)
  | goal => route.runAnswer context goal

/-! ## Soundness -/

/-- The interpretations the route's answers are about: those of
`Snapshot.Models` satisfying the KB's own clauses. -/
def Holds (Value : Type) (model : Model Literal Symbol Value route.hoApplySymbol) : Prop :=
  ∃ interp : Interpretation Literal Symbol Value route.hoApplySymbol, interp.model = model ∧
    route.snapshot.Models route.evaluations interp ∧ model.Models fun clause => clause ∈ route.clauses

/-- What the route's answers claim about a query. -/
def meaning (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) : Meaning :=
  Meaning.ofModels route.Holds context goal

omit [DecidableEq Domain] [DecidableEq Literal] [FreshNames Variable] in
/-- The generated clauses are true in a realizing interpretation with checked
registrations. -/
theorem models_generated (wellFormed : route.snapshot.WellFormed)
    (listed : ∀ rule ∈ route.rules, route.snapshot.signature.signature.data.definitions rule)
    {interp : Interpretation Literal Symbol Value route.hoApplySymbol} (models : route.snapshot.Models route.evaluations interp) :
    interp.model.Models fun clause => clause ∈ route.generated := by
  intro clause member environment
  rcases List.mem_append.mp member with signature | registry
  · exact Elaboration.models_signatureKb route.snapshot.signature interp.model models.realizes.signature route.names clause
      (mem_signatureClauses listed signature) environment
  · obtain ⟨registration, registered, inside⟩ := List.mem_flatMap.mp registry
    have kb := models_kb models.realizes models.checked wellFormed (Literal := Literal) route.names
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl
    · exact kb _ (Or.inr ⟨registration, registered, Or.inl rfl⟩) environment
    · exact kb _ (Or.inr ⟨registration, registered, Or.inr rfl⟩) environment

omit [DecidableEq Domain] [DecidableEq Literal] [FreshNames Variable] in
/-- The checker's KB is true in the interpretations the answers are about. -/
theorem models_checkSnapshot (wellFormed : route.snapshot.WellFormed)
    (listed : ∀ rule ∈ route.rules, route.snapshot.signature.signature.data.definitions rule)
    {Value : Type} {model : Model Literal Symbol Value route.hoApplySymbol} (holds : route.Holds Value model) :
    model.Models route.checkSnapshot.kb := by
  obtain ⟨interp, rfl, models, own⟩ := holds
  apply route.snapshot.models_evaluated route.evaluations models.evaluated
  intro clause member environment
  rcases List.mem_append.mp member with programClause | law
  · obtain ⟨entry, inside, rfl⟩ := List.mem_map.mp programClause
    rcases List.mem_append.mp inside with lowered | generatedEntry
    · obtain ⟨index, bound, same⟩ := List.mem_mapIdx.mp lowered
      rw [← same]
      exact own _ (List.getElem_mem bound) environment
    · obtain ⟨clause, generatedMember, rfl⟩ := List.mem_map.mp generatedEntry
      exact route.models_generated wellFormed listed models clause generatedMember environment
  · exact models_lawClauses models.realizes models.checked wellFormed _ law environment

/-- A run's Yes is its accepted export, derived in the checker's KB, which
holds in the interpretations the answers are about. -/
theorem runAnswer_sound (wellFormed : route.snapshot.WellFormed)
    (listed : ∀ rule ∈ route.rules, route.snapshot.signature.signature.data.definitions rule)
    (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    (route.runAnswer context goal).Sound (route.meaning context goal) := by
  unfold runAnswer
  split
  · split
    · rename_i term found
      intro Value model holds environment satisfied
      have checked := (Option.filter_eq_some_iff.mp found).2
      have derived := checked_toDerives route.vocab route.checker
        ((checkProof_accept_iff route.vocab route.checker).mp (of_decide_eq_true checked))
      exact model.sound (route.models_checkSnapshot wellFormed listed holds) (model.disabled_adequate _) derived
        environment satisfied
    · trivial
  all_goals trivial

omit [FreshNames Variable] in
/-- What a decision establishes: the evaluator's value is the other side
(`some true`), or the two differ in every interpretation the answers are about
(`some false`), the call on the side `turned` says. -/
theorem decision?_spec {left right : Term Variable Literal Symbol} {decided turned : Bool}
    (found : route.decision? left right = some (decided, turned)) :
    if turned then route.snapshot.check? route.evaluations route.rules ⟨right, left⟩ = some decided
    else route.snapshot.check? route.evaluations route.rules ⟨left, right⟩ = some decided := by
  unfold decision? at found
  split at found
  · cases found; simpa
  · obtain ⟨value, inside, same⟩ := Option.map_eq_some_iff.mp found
    cases same
    simpa using inside

/-- `answer_sound`: every answer of the route means what it says. -/
theorem answer_sound (wellFormed : route.snapshot.WellFormed)
    (listed : ∀ rule ∈ route.rules, route.snapshot.signature.signature.data.definitions rule)
    (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    (route.answer context goal).Sound (route.meaning context goal) := by
  cases goal with
  | equal left right =>
      simp only [answer]
      split
      · rename_i turned found
        have spec := route.decision?_spec found
        intro Value model holds environment _
        obtain ⟨interp, rfl, models, _⟩ := holds
        rw [Model.satisfies_equal]
        cases turned
        · exact Snapshot.evaluate_sound models.evaluated (Snapshot.check?_true (by simpa using spec)) environment
        · exact (Snapshot.evaluate_sound models.evaluated (Snapshot.check?_true (by simpa using spec)) environment).symm
      · rename_i turned found
        split
        · rename_i term ran
          have sound := route.runAnswer_sound wellFormed listed context (.equal left right)
          rwa [ran] at sound
        · have spec := route.decision?_spec found
          intro Value model holds environment _
          obtain ⟨interp, rfl, models, _⟩ := holds
          rw [Model.satisfies_equal]
          cases turned
          · exact Snapshot.check?_false listed (by simpa using spec) models.evaluated models.separated environment
          · exact fun same => Snapshot.check?_false listed (by simpa using spec) models.evaluated models.separated
              environment same.symm
      · exact route.runAnswer_sound wellFormed listed context _
  | _ => exact route.runAnswer_sound wellFormed listed context _

/-- `answer_definite`, completeness: with totality evidence and every rule of the
signature listed, an equation the decision contract decides, the call on
either side, is answered Yes or No. -/
theorem answer_definite (complete : route.snapshot.Complete route.evaluations)
    (covering : ∀ rule, route.snapshot.signature.signature.data.definitions rule → rule ∈ route.rules)
    (context : ProofContext Variable Literal Symbol) {left right : Term Variable Literal Symbol}
    (decides : route.snapshot.Decides route.evaluations ⟨left, right⟩ ∨
      route.snapshot.Decides route.evaluations ⟨right, left⟩) :
    (route.answer context (.equal left right)).definite = true := by
  have decided : ∃ found, route.decision? left right = some found := by
    unfold decision?
    rcases decides with decides | decides
    · rw [Snapshot.check?_complete complete covering decides]
      exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · rw [Snapshot.check?_complete complete covering decides]
        exact ⟨_, rfl⟩
  obtain ⟨⟨decision, turned⟩, found⟩ := decided
  simp only [answer]
  rw [found]
  cases decision
  · dsimp only
    split <;> rfl
  · rfl

omit [DecidableEq Domain] [FreshNames Variable] in
/-- The checker finds the evaluation rule under its name. -/
theorem rule?_evaluation :
    route.checker.rule? route.rule = some (evaluationRule route.rule route.checker.snapshot route.checker.provider) := by
  simp [Checker.rule?, checker, evaluationRule]

/-- Every Yes of the route is a term its checker accepts for the query: the
decision's evaluation node, turned around when the call is on the right, or a
run's export, checked before it is answered. -/
theorem answer_accepted {context : ProofContext Variable Literal Symbol} {goal : Formula Variable Literal Symbol}
    {term : Term Variable Literal Symbol} (answered : route.answer context goal = .yes term) :
    checkProof route.vocab route.checker route.table context goal term = .accept := by
  have ofRun : ∀ {goal : Formula Variable Literal Symbol}, route.runAnswer context goal = .yes term →
      checkProof route.vocab route.checker route.table context goal term = .accept := by
    intro goal ran
    unfold runAnswer at ran
    split at ran
    · split at ran
      · rename_i found _ _
        cases ran
        rename_i found
        exact of_decide_eq_true (Option.filter_eq_some_iff.mp found).2
      · cases ran
    all_goals cases ran
  cases goal with
  | equal left right =>
      simp only [answer] at answered
      split at answered
      · rename_i turned found
        cases answered
        have spec := route.decision?_spec found
        apply Proves.accepted route.vocab route.checker
        cases turned
        · have evaluated : route.snapshot.evaluate route.evaluations left = some right :=
            Snapshot.check?_true (by simpa using spec)
          exact Unfold.evaluation_proves route.rule?_evaluation ⟨_, List.mem_singleton_self _, evaluated⟩
        · have evaluated : route.snapshot.evaluate route.evaluations right = some left :=
            Snapshot.check?_true (by simpa using spec)
          exact Unfold.node₁_proves .equalSymm (by
            simpa using Unfold.evaluation_proves (refs := Resolves route.vocab route.checker route.table)
              (context := context) route.rule?_evaluation ⟨_, List.mem_singleton_self _, evaluated⟩)
      · split at answered
        · rename_i ran
          cases answered
          exact ofRun ran
        · cases answered
      · exact ofRun answered
  | _ => exact ofRun answered

end Route

end AnthillModKbSpec.DictionaryRegistry
