import AnthillModKbSpec.Resolution.P1.Substitutes

/-! # Supplied proof trees and their checker (S08)

A supplied proof is a finite tree in the shared logic. Each node names a rule
application with the parameters its conclusion and premises do not determine
(eigenvariables, witnesses, the clause and its instantiation, the opened
assumption of an existential, replacement templates, NAF evidence), its
conclusion, and one subtree per premise. The context of each premise is
fixed by the rule: `impIntro`, `disjElim`, and `existsElim` add the assumption
they discharge, as `Derives` does.

`Valid` is the tree validity judgment: one constructor per rule, each the
side conditions of the matching `Derives` rule read off the node. `check`
decides it by recursion on the tree, with a known terminating procedure for
each rule (`check_iff`), and a valid tree reconstructs `Derives` for exactly
the checker's application symbol, KB, context, and NAF provider
(`Valid.derives`). No rule checks its premises by proof search: every premise
is a subtree.

Three things come from outside the logic's rules, each through an interface
with its own soundness proof: NAF evidence (`NafCheck`), derived rules of later
commands (`RuleCheck`, S09–S14), and references to previously checked proofs
(the `refs` parameter, resolved over an import table in `P1/Encoding`). Every
capability a valid tree uses is one the checker has (`Valid.uses`); a tree
that needs one the checker lacks is reported (`P1.missing`) instead of being
decided. -/

namespace AnthillModKbSpec.P1

open Machine

variable {Variable Literal Symbol : Type}

/-- A rule application of a supplied tree, with its parameters. -/
inductive Rule (Variable Literal Symbol : Type) where
  | assumption
  | truth
  | conjIntro
  | conjLeft
  | conjRight
  | disjLeft
  | disjRight
  | disjElim
  | impIntro
  | impElim
  | falsityElim
  /-- The eigenvariable opening the universal. -/
  | forallIntro (eigen : Variable)
  | forallElim (witness : Term Variable Literal Symbol)
  | existsIntro (witness : Term Variable Literal Symbol)
  /-- The eigenvariable and the opened body, assumed in the second premise. -/
  | existsElim (eigen : Variable) (opened : Formula Variable Literal Symbol)
  /-- A KB clause, as a template, and its instantiation. -/
  | clause (clause : HornClause Variable Literal Symbol) (instantiation : List (Variable × Term Variable Literal Symbol))
  | goalClause (clause : HornClause Variable Literal Symbol)
      (instantiation : List (Variable × Term Variable Literal Symbol))
  /-- NAF, with the evidence of the operand's complete failure. -/
  | defaultNegIntro (evidence : Term Variable Literal Symbol)
  | hoApplyIntro
  | hoApplyElim
  | equalRefl
  | equalSymm
  | equalTrans
  | equalSubst (name : Variable) (template : Term Variable Literal Symbol)
  /-- A derived rule of a later command, checked by its registered procedure. -/
  | extension (name : Symbol) (parameters : List (Term Variable Literal Symbol))
  /-- A previously checked proof, by name. -/
  | reference (name : Symbol)

/-- A supplied proof tree: a rule application, its conclusion, and one subtree
per premise, in order. -/
inductive Proof (Variable Literal Symbol : Type) where
  | node (rule : Rule Variable Literal Symbol) (conclusion : Formula Variable Literal Symbol)
      (premises : List (Proof Variable Literal Symbol))

def Proof.conclusion : Proof Variable Literal Symbol → Formula Variable Literal Symbol
  | .node _ conclusion _ => conclusion

/-- What a tree is checked against: the application symbol and the KB, as a
finite clause list. -/
structure Snapshot (Variable Literal Symbol : Type) where
  hoApplySymbol : Symbol
  clauses : List (HornClause Variable Literal Symbol)

def Snapshot.kb (snapshot : Snapshot Variable Literal Symbol) : LogicalKb Variable Literal Symbol :=
  fun clause => clause ∈ snapshot.clauses

/-- A known procedure for NAF evidence: it decides evidence for an operand
under a context, and what it accepts is evidence of the provider. -/
structure NafCheck (snapshot : Snapshot Variable Literal Symbol) (provider : NafFailure Variable Literal Symbol) where
  check : ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Term Variable Literal Symbol → Bool
  sound : ∀ context operand evidence, check context operand evidence = true →
    provider snapshot.hoApplySymbol snapshot.kb context operand

section Checking

variable [DecidableEq Variable]

/-- A derived rule of a later command (S09–S14): its name, the assumptions each
premise adds, and a known terminating procedure checking one application from
its conclusion, parameters, and premise conclusions. It checks the
application, not the premises: the tree supplies their proofs. Its soundness
is proved in the shared logic. -/
structure RuleCheck (snapshot : Snapshot Variable Literal Symbol) (provider : NafFailure Variable Literal Symbol) where
  name : Symbol
  discharges : Formula Variable Literal Symbol → List (Term Variable Literal Symbol) →
    List (Formula Variable Literal Symbol) → List (ProofContext Variable Literal Symbol)
  check : ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → List (Term Variable Literal Symbol) →
    List (Formula Variable Literal Symbol) → Bool
  sound : ∀ context conclusion parameters premises, check context conclusion parameters premises = true →
    (∀ entry ∈ premises.zip (discharges conclusion parameters premises),
      Derives snapshot.hoApplySymbol snapshot.kb (entry.2 ++ context) entry.1 provider) →
    Derives snapshot.hoApplySymbol snapshot.kb context conclusion provider

/-- The checking procedures a tree is checked with: the snapshot, the NAF
provider reconstruction preserves, the NAF evidence check if any, and the
registered derived rules. -/
structure Checker (Variable Literal Symbol : Type) [DecidableEq Variable] where
  snapshot : Snapshot Variable Literal Symbol
  provider : NafFailure Variable Literal Symbol
  negation : Option (NafCheck snapshot provider)
  rules : List (RuleCheck snapshot provider)

/-- An instantiation as a substitution; the first pair for a name wins. -/
def ofPairs : List (Variable × Term Variable Literal Symbol) → Substitution Variable Literal Symbol
  | [] => Term.var
  | (name, value) :: rest => Substitution.bind (ofPairs rest) name value

variable [DecidableEq Symbol]

/-- The registered procedure of a derived rule: the first with its name. -/
def Checker.rule? (checker : Checker Variable Literal Symbol) (name : Symbol) :
    Option (RuleCheck checker.snapshot checker.provider) :=
  checker.rules.find? fun rule => decide (rule.name = name)

/-- One rule application, without its premises' proofs: the side conditions
of the matching `Derives` rule, from the node's context, rule with its
parameters, conclusion, and premise conclusions, and the assumptions each
premise adds. -/
inductive Local (checker : Checker Variable Literal Symbol)
    (refs : Symbol → ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Prop)
    (context : ProofContext Variable Literal Symbol) :
    Rule Variable Literal Symbol → Formula Variable Literal Symbol → List (Formula Variable Literal Symbol) →
      List (ProofContext Variable Literal Symbol) → Prop where
  | assumption (member : goal ∈ context) : Local checker refs context .assumption goal [] []
  | truth : Local checker refs context .truth .truth [] []
  | conjIntro : Local checker refs context .conjIntro (.conj a b) [a, b] [[], []]
  | conjLeft : Local checker refs context .conjLeft goal [.conj goal other] [[]]
  | conjRight : Local checker refs context .conjRight goal [.conj other goal] [[]]
  | disjLeft : Local checker refs context .disjLeft (.disj a b) [a] [[]]
  | disjRight : Local checker refs context .disjRight (.disj a b) [b] [[]]
  | disjElim : Local checker refs context .disjElim goal [.disj a b, goal, goal] [[], [a], [b]]
  | impIntro : Local checker refs context .impIntro (.imp premise conclusion) [conclusion] [[premise]]
  | impElim : Local checker refs context .impElim goal [.imp premise goal, premise] [[], []]
  | falsityElim : Local checker refs context .falsityElim goal [.falsity] [[]]
  | forallIntro (freshContext : FreshForContext eigen context)
      (freshGoal : eigen ∉ (Term.forallVar binder body).freeVars)
      (opening : Substitutes (Substitution.single binder (.var eigen)) body opened) :
      Local checker refs context (.forallIntro eigen) (.forallVar binder body) [opened] [[]]
  | forallElim (instantiation : Substitutes (Substitution.single binder witness) body goal) :
      Local checker refs context (.forallElim witness) goal [.forallVar binder body] [[]]
  | existsIntro (instantiation : Substitutes (Substitution.single binder witness) body instantiated) :
      Local checker refs context (.existsIntro witness) (.existsVar binder body) [instantiated] [[]]
  | existsElim (freshContext : FreshForContext eigen context)
      (freshBody : eigen ∉ (Term.existsVar binder body).freeVars) (freshGoal : eigen ∉ goal.freeVars)
      (opening : Substitutes (Substitution.single binder (.var eigen)) body opened) :
      Local checker refs context (.existsElim eigen opened) goal [.existsVar binder body, goal] [[], [opened]]
  | clause (member : HornClause.definite head body ∈ checker.snapshot.clauses)
      (headInstance : Substitutes (ofPairs instantiation) head goal)
      (bodyInstance : Substitutes (ofPairs instantiation) (.conjunction body) instantiated) :
      Local checker refs context (.clause (.definite head body) instantiation) goal [instantiated] [[]]
  | goalClause (member : HornClause.goal body ∈ checker.snapshot.clauses)
      (bodyInstance : Substitutes (ofPairs instantiation) (.conjunction body) instantiated) :
      Local checker refs context (.goalClause (.goal body) instantiation) .falsity [instantiated] [[]]
  | defaultNegIntro (ground : operand.freeVars = []) (negation : checker.negation = some naf)
      (accepted : naf.check context operand evidence = true) :
      Local checker refs context (.defaultNegIntro evidence) (.defaultNeg operand) [] []
  | hoApplyIntro :
      Local checker refs context .hoApplyIntro (.app checker.snapshot.hoApplySymbol (.app predicate [] :: args))
        [.app predicate args] [[]]
  | hoApplyElim :
      Local checker refs context .hoApplyElim (.app predicate args)
        [.app checker.snapshot.hoApplySymbol (.app predicate [] :: args)] [[]]
  | equalRefl : Local checker refs context .equalRefl (.equal term term) [] []
  | equalSymm : Local checker refs context .equalSymm (.equal b a) [.equal a b] [[]]
  | equalTrans : Local checker refs context .equalTrans (.equal a c) [.equal a b, .equal b c] [[], []]
  | equalSubst (leftInstance : Substitutes (Substitution.single name a) template before)
      (rightInstance : Substitutes (Substitution.single name b) template goal) :
      Local checker refs context (.equalSubst name template) goal [.equal a b, before] [[], []]
  | extension (found : checker.rule? name = some rule) (accepted : rule.check context goal parameters premises = true)
      (lengths : (rule.discharges goal parameters premises).length = premises.length) :
      Local checker refs context (.extension name parameters) goal premises (rule.discharges goal parameters premises)
  | reference (resolved : refs name context goal) : Local checker refs context (.reference name) goal [] []

/-- Tree validity, for references resolved by `refs`: every node is a valid
rule application, and every premise subtree is valid under the context its
rule gives it. -/
inductive Valid (checker : Checker Variable Literal Symbol)
    (refs : Symbol → ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Prop) :
    ProofContext Variable Literal Symbol → Proof Variable Literal Symbol → Prop where
  | node (step : Local checker refs context rule conclusion (premises.map Proof.conclusion) contexts)
      (children : ∀ entry ∈ premises.zip contexts, Valid checker refs (entry.2 ++ context) entry.1) :
      Valid checker refs context (.node rule conclusion premises)

/-! ## The checker -/

/-- Decide `FreshForContext`. -/
def freshIn (eigen : Variable) (context : ProofContext Variable Literal Symbol) : Bool :=
  context.all fun assumption => !decide (eigen ∈ assumption.freeVars)

omit [DecidableEq Symbol] in
theorem freshIn_iff {eigen : Variable} {context : ProofContext Variable Literal Symbol} :
    freshIn eigen context = true ↔ FreshForContext eigen context := by
  simp [freshIn, FreshForContext]

variable [DecidableEq Literal]

attribute [local instance] termEq clauseEq

/-- The known procedure for each rule: whether one application is valid, and
then the contexts of its premises. It reads the node and never searches. -/
def nodeCheck (checker : Checker Variable Literal Symbol)
    (refs : Symbol → ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Bool)
    (context : ProofContext Variable Literal Symbol) (rule : Rule Variable Literal Symbol)
    (conclusion : Formula Variable Literal Symbol) (premises : List (Formula Variable Literal Symbol)) :
    Option (List (ProofContext Variable Literal Symbol)) :=
  match rule with
  | .assumption =>
      match premises with
      | [] => if conclusion ∈ context then some [] else none
      | _ => none
  | .truth =>
      match conclusion, premises with
      | .truth, [] => some []
      | _, _ => none
  | .conjIntro =>
      match conclusion, premises with
      | .conj a b, [first, second] => if first = a ∧ second = b then some [[], []] else none
      | _, _ => none
  | .conjLeft =>
      match premises with
      | [.conj a _] => if a = conclusion then some [[]] else none
      | _ => none
  | .conjRight =>
      match premises with
      | [.conj _ b] => if b = conclusion then some [[]] else none
      | _ => none
  | .disjLeft =>
      match conclusion, premises with
      | .disj a _, [premise] => if premise = a then some [[]] else none
      | _, _ => none
  | .disjRight =>
      match conclusion, premises with
      | .disj _ b, [premise] => if premise = b then some [[]] else none
      | _, _ => none
  | .disjElim =>
      match premises with
      | [.disj a b, first, second] => if first = conclusion ∧ second = conclusion then some [[], [a], [b]] else none
      | _ => none
  | .impIntro =>
      match conclusion, premises with
      | .imp premise goal, [body] => if body = goal then some [[premise]] else none
      | _, _ => none
  | .impElim =>
      match premises with
      | [.imp premise goal, argument] => if argument = premise ∧ goal = conclusion then some [[], []] else none
      | _ => none
  | .falsityElim =>
      match premises with
      | [.falsity] => some [[]]
      | _ => none
  | .forallIntro eigen =>
      match conclusion, premises with
      | .forallVar binder body, [opened] =>
          if freshIn eigen context = true ∧ eigen ∉ (Term.forallVar binder body).freeVars ∧
              substitutes (Substitution.single binder (.var eigen)) body opened = true then some [[]] else none
      | _, _ => none
  | .forallElim witness =>
      match premises with
      | [.forallVar binder body] =>
          if substitutes (Substitution.single binder witness) body conclusion = true then some [[]] else none
      | _ => none
  | .existsIntro witness =>
      match conclusion, premises with
      | .existsVar binder body, [instantiated] =>
          if substitutes (Substitution.single binder witness) body instantiated = true then some [[]] else none
      | _, _ => none
  | .existsElim eigen opened =>
      match premises with
      | [.existsVar binder body, goal] =>
          if freshIn eigen context = true ∧ eigen ∉ (Term.existsVar binder body).freeVars ∧
              eigen ∉ conclusion.freeVars ∧ substitutes (Substitution.single binder (.var eigen)) body opened = true ∧
              goal = conclusion then some [[], [opened]] else none
      | _ => none
  | .clause clause instantiation =>
      match clause, premises with
      | .definite head body, [instantiated] =>
          if HornClause.definite head body ∈ checker.snapshot.clauses ∧
              substitutes (ofPairs instantiation) head conclusion = true ∧
              substitutes (ofPairs instantiation) (.conjunction body) instantiated = true then some [[]] else none
      | _, _ => none
  | .goalClause clause instantiation =>
      match clause, conclusion, premises with
      | .goal body, .falsity, [instantiated] =>
          if HornClause.goal body ∈ checker.snapshot.clauses ∧
              substitutes (ofPairs instantiation) (.conjunction body) instantiated = true then some [[]] else none
      | _, _, _ => none
  | .defaultNegIntro evidence =>
      match conclusion, premises, checker.negation with
      | .defaultNeg operand, [], some naf =>
          if operand.freeVars = [] ∧ naf.check context operand evidence = true then some [] else none
      | _, _, _ => none
  | .hoApplyIntro =>
      match conclusion, premises with
      | .app symbol (.app predicate [] :: args), [premise] =>
          if symbol = checker.snapshot.hoApplySymbol ∧ premise = .app predicate args then some [[]] else none
      | _, _ => none
  | .hoApplyElim =>
      match conclusion, premises with
      | .app predicate args, [premise] =>
          if premise = .app checker.snapshot.hoApplySymbol (.app predicate [] :: args) then some [[]] else none
      | _, _ => none
  | .equalRefl =>
      match conclusion, premises with
      | .equal a b, [] => if a = b then some [] else none
      | _, _ => none
  | .equalSymm =>
      match conclusion, premises with
      | .equal b a, [premise] => if premise = .equal a b then some [[]] else none
      | _, _ => none
  | .equalTrans =>
      match conclusion, premises with
      | .equal a c, [.equal a' b, second] => if a' = a ∧ second = .equal b c then some [[], []] else none
      | _, _ => none
  | .equalSubst name template =>
      match premises with
      | [.equal a b, before] =>
          if substitutes (Substitution.single name a) template before = true ∧
              substitutes (Substitution.single name b) template conclusion = true then some [[], []] else none
      | _ => none
  | .extension name parameters =>
      match checker.rule? name with
      | some rule =>
          if rule.check context conclusion parameters premises = true ∧
              (rule.discharges conclusion parameters premises).length = premises.length then
            some (rule.discharges conclusion parameters premises)
          else none
      | none => none
  | .reference name =>
      match premises with
      | [] => if refs name context conclusion = true then some [] else none
      | _ => none

/-- Check a tree under a context, with references decided by `refs`: each node
by its rule's procedure, then each premise subtree under the context the rule
gives it. Recursion is on the tree, so checking terminates. -/
def check (checker : Checker Variable Literal Symbol)
    (refs : Symbol → ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Bool)
    (context : ProofContext Variable Literal Symbol) : Proof Variable Literal Symbol → Bool
  | .node rule conclusion premises =>
      match nodeCheck checker refs context rule conclusion (premises.map Proof.conclusion) with
      | some contexts => (premises.attach.zip contexts).all fun entry => check checker refs (entry.2 ++ context) entry.1.1
      | none => false
termination_by proof => sizeOf proof
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem entry.1.2
  omega

/-! ## The checker decides validity -/

section Decides

variable {checker : Checker Variable Literal Symbol}
  {refsB : Symbol → ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Bool}
  {refsP : Symbol → ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Prop}

omit [DecidableEq Literal] in
/-- A rule application gives one context per premise. -/
theorem Local.length {context : ProofContext Variable Literal Symbol} {rule : Rule Variable Literal Symbol}
    {conclusion : Formula Variable Literal Symbol} {premises : List (Formula Variable Literal Symbol)}
    {contexts : List (ProofContext Variable Literal Symbol)}
    (step : Local checker refsP context rule conclusion premises contexts) : contexts.length = premises.length := by
  cases step <;> first | rfl | assumption

/-- Each rule's procedure accepts every valid application. -/
theorem nodeCheck_complete (agree : ∀ name context goal, refsB name context goal = true ↔ refsP name context goal)
    {context : ProofContext Variable Literal Symbol} {rule : Rule Variable Literal Symbol}
    {conclusion : Formula Variable Literal Symbol} {premises : List (Formula Variable Literal Symbol)}
    {contexts : List (ProofContext Variable Literal Symbol)}
    (step : Local checker refsP context rule conclusion premises contexts) :
    nodeCheck checker refsB context rule conclusion premises = some contexts := by
  cases step with
  | assumption member => simp [nodeCheck, member]
  | truth | conjIntro | conjLeft | conjRight | disjLeft | disjRight | disjElim | impIntro | impElim | falsityElim
  | hoApplyIntro | hoApplyElim | equalRefl | equalSymm | equalTrans => simp [nodeCheck]
  | forallIntro freshContext freshGoal opening =>
      simp only [nodeCheck, freshIn_iff.mpr freshContext, substitutes_iff.mpr opening]
      simp [freshGoal]
  | forallElim instantiation => simp [nodeCheck, substitutes_iff.mpr instantiation]
  | existsIntro instantiation => simp [nodeCheck, substitutes_iff.mpr instantiation]
  | existsElim freshContext freshBody freshGoal opening =>
      simp only [nodeCheck, freshIn_iff.mpr freshContext, substitutes_iff.mpr opening]
      simp [freshBody, freshGoal]
  | clause member headInstance bodyInstance =>
      simp [nodeCheck, member, substitutes_iff.mpr headInstance, substitutes_iff.mpr bodyInstance]
  | goalClause member bodyInstance => simp [nodeCheck, member, substitutes_iff.mpr bodyInstance]
  | defaultNegIntro ground negation accepted => simp [nodeCheck, negation, ground, accepted]
  | equalSubst leftInstance rightInstance =>
      simp [nodeCheck, substitutes_iff.mpr leftInstance, substitutes_iff.mpr rightInstance]
  | extension found accepted lengths => simp [nodeCheck, found, accepted, lengths]
  | reference resolved => simp [nodeCheck, (agree _ _ _).mpr resolved]

/-- Each rule's procedure accepts only valid applications. -/
theorem nodeCheck_sound (agree : ∀ name context goal, refsB name context goal = true ↔ refsP name context goal)
    {context : ProofContext Variable Literal Symbol} {rule : Rule Variable Literal Symbol}
    {conclusion : Formula Variable Literal Symbol} {premises : List (Formula Variable Literal Symbol)}
    {contexts : List (ProofContext Variable Literal Symbol)}
    (checked : nodeCheck checker refsB context rule conclusion premises = some contexts) :
    Local checker refsP context rule conclusion premises contexts := by
  cases rule with
  | assumption =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · cases checked; exact .assumption ‹_›
        · cases checked
      · cases checked
  | truth =>
      simp only [nodeCheck] at checked
      split at checked
      · cases checked; exact .truth
      · cases checked
  | conjIntro =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · rename_i same; obtain ⟨rfl, rfl⟩ := same; cases checked; exact .conjIntro
        · cases checked
      · cases checked
  | conjLeft =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · rename_i same; subst same; cases checked; exact .conjLeft
        · cases checked
      · cases checked
  | conjRight =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · rename_i same; subst same; cases checked; exact .conjRight
        · cases checked
      · cases checked
  | disjLeft =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · rename_i same; subst same; cases checked; exact .disjLeft
        · cases checked
      · cases checked
  | disjRight =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · rename_i same; subst same; cases checked; exact .disjRight
        · cases checked
      · cases checked
  | disjElim =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · rename_i same; obtain ⟨rfl, rfl⟩ := same; cases checked; exact .disjElim
        · cases checked
      · cases checked
  | impIntro =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · rename_i same; subst same; cases checked; exact .impIntro
        · cases checked
      · cases checked
  | impElim =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · rename_i same; obtain ⟨rfl, rfl⟩ := same; cases checked; exact .impElim
        · cases checked
      · cases checked
  | falsityElim =>
      simp only [nodeCheck] at checked
      split at checked
      · cases checked; exact .falsityElim
      · cases checked
  | forallIntro eigen =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · rename_i holds
          obtain ⟨fresh, freshGoal, opening⟩ := holds
          cases checked
          exact .forallIntro (freshIn_iff.mp fresh) freshGoal (substitutes_iff.mp opening)
        · cases checked
      · cases checked
  | forallElim witness =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · rename_i holds; cases checked; exact .forallElim (substitutes_iff.mp holds)
        · cases checked
      · cases checked
  | existsIntro witness =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · rename_i holds; cases checked; exact .existsIntro (substitutes_iff.mp holds)
        · cases checked
      · cases checked
  | existsElim eigen opened =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · rename_i holds
          obtain ⟨fresh, freshBody, freshGoal, opening, rfl⟩ := holds
          cases checked
          exact .existsElim (freshIn_iff.mp fresh) freshBody freshGoal (substitutes_iff.mp opening)
        · cases checked
      · cases checked
  | clause clause instantiation =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · rename_i holds
          obtain ⟨member, headInstance, bodyInstance⟩ := holds
          cases checked
          exact .clause member (substitutes_iff.mp headInstance) (substitutes_iff.mp bodyInstance)
        · cases checked
      · cases checked
  | goalClause clause instantiation =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · rename_i holds
          obtain ⟨member, bodyInstance⟩ := holds
          cases checked
          exact .goalClause member (substitutes_iff.mp bodyInstance)
        · cases checked
      · cases checked
  | defaultNegIntro evidence =>
      simp only [nodeCheck] at checked
      split at checked
      · rename_i naf negation
        split at checked
        · rename_i holds; cases checked; exact .defaultNegIntro holds.1 negation holds.2
        · cases checked
      · cases checked
  | hoApplyIntro =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · rename_i same; obtain ⟨rfl, rfl⟩ := same; cases checked; exact .hoApplyIntro
        · cases checked
      · cases checked
  | hoApplyElim =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · rename_i same; subst same; cases checked; exact .hoApplyElim
        · cases checked
      · cases checked
  | equalRefl =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · rename_i same; subst same; cases checked; exact .equalRefl
        · cases checked
      · cases checked
  | equalSymm =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · rename_i same; subst same; cases checked; exact .equalSymm
        · cases checked
      · cases checked
  | equalTrans =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · rename_i same; obtain ⟨rfl, rfl⟩ := same; cases checked; exact .equalTrans
        · cases checked
      · cases checked
  | equalSubst name template =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · rename_i holds; cases checked
          exact .equalSubst (substitutes_iff.mp holds.1) (substitutes_iff.mp holds.2)
        · cases checked
      · cases checked
  | extension name parameters =>
      simp only [nodeCheck] at checked
      split at checked
      · rename_i rule found
        split at checked
        · rename_i holds; cases checked; exact .extension found holds.1 holds.2
        · cases checked
      · cases checked
  | reference name =>
      simp only [nodeCheck] at checked
      split at checked
      · split at checked
        · rename_i resolved; cases checked; exact .reference ((agree _ _ _).mp resolved)
        · cases checked
      · cases checked

omit [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal] in
theorem mem_zip_attach {α β : Type} {items : List α} {others : List β} {entry : α × β} :
    entry ∈ items.zip others ↔ ∃ other ∈ items.attach.zip others, other.1.1 = entry.1 ∧ other.2 = entry.2 := by
  have mapped : (items.attach.zip others).map (Prod.map Subtype.val id) = items.zip others := by
    rw [← List.zip_map_left, List.attach_map_subtype_val]
  rw [← mapped, List.mem_map]
  constructor
  · rintro ⟨other, member, rfl⟩; exact ⟨other, member, rfl, rfl⟩
  · rintro ⟨other, member, first, second⟩
    exact ⟨other, member, Prod.ext first second⟩

/-- `check` accepts every valid tree. -/
theorem check_complete (agree : ∀ name context goal, refsB name context goal = true ↔ refsP name context goal)
    {context : ProofContext Variable Literal Symbol} {proof : Proof Variable Literal Symbol}
    (valid : Valid checker refsP context proof) : check checker refsB context proof = true := by
  induction valid with
  | node step children ih =>
      rw [check, nodeCheck_complete agree step]
      simp only [List.all_eq_true]
      exact fun other member => ih (other.1.1, other.2) (mem_zip_attach.mpr ⟨other, member, rfl, rfl⟩)

/-- `check` accepts only valid trees. -/
theorem check_sound (agree : ∀ name context goal, refsB name context goal = true ↔ refsP name context goal) :
    ∀ (context : ProofContext Variable Literal Symbol) (proof : Proof Variable Literal Symbol),
      check checker refsB context proof = true → Valid checker refsP context proof := by
  intro context proof
  induction context, proof using check.induct checker refsB with
  | case1 context rule conclusion premises contexts checkedNode ih =>
      intro checked
      replace checkedNode :
          nodeCheck checker refsB context rule conclusion (premises.map Proof.conclusion) = some contexts := by
        simpa using checkedNode
      rw [check, checkedNode] at checked
      simp only [List.all_eq_true] at checked
      refine .node (nodeCheck_sound agree checkedNode) fun entry member => ?_
      obtain ⟨other, inside, first, second⟩ := mem_zip_attach.mp member
      rw [← first, ← second]
      exact ih other (checked other inside)
  | case2 context rule conclusion premises checkedNode =>
      intro checked
      replace checkedNode :
          nodeCheck checker refsB context rule conclusion (premises.map Proof.conclusion) = none := by
        simpa using checkedNode
      rw [check, checkedNode] at checked
      cases checked

/-- `check_iff`: the checker decides tree validity. -/
theorem check_iff (agree : ∀ name context goal, refsB name context goal = true ↔ refsP name context goal)
    {context : ProofContext Variable Literal Symbol} {proof : Proof Variable Literal Symbol} :
    check checker refsB context proof = true ↔ Valid checker refsP context proof :=
  ⟨check_sound agree context proof, check_complete agree⟩

end Decides

/-! ## Valid trees are derivations -/

section Derives

variable {checker : Checker Variable Literal Symbol}
  {refs : Symbol → ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Prop}

omit [DecidableEq Literal] in
/-- A valid rule application derives its conclusion from derivations of its
premises, each under the context the rule gives it. -/
theorem Local.derives {context : ProofContext Variable Literal Symbol} {rule : Rule Variable Literal Symbol}
    {conclusion : Formula Variable Literal Symbol} {premises : List (Formula Variable Literal Symbol)}
    {contexts : List (ProofContext Variable Literal Symbol)}
    (step : Local checker refs context rule conclusion premises contexts)
    (resolved : ∀ name context goal, refs name context goal →
      Derives checker.snapshot.hoApplySymbol checker.snapshot.kb context goal checker.provider)
    (proved : ∀ entry ∈ premises.zip contexts,
      Derives checker.snapshot.hoApplySymbol checker.snapshot.kb (entry.2 ++ context) entry.1 checker.provider) :
    Derives checker.snapshot.hoApplySymbol checker.snapshot.kb context conclusion checker.provider := by
  cases step
  all_goals try simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.nil_append, List.singleton_append] at proved
  case assumption => exact .assumption ‹_›
  case truth => exact .truth
  case conjIntro => exact .conjIntro proved.1 proved.2
  case conjLeft => exact .conjLeft proved
  case conjRight => exact .conjRight proved
  case disjLeft => exact .disjLeft proved
  case disjRight => exact .disjRight proved
  case disjElim => exact .disjElim proved.1 proved.2.1 proved.2.2
  case impIntro => exact .impIntro proved
  case impElim => exact .impElim proved.1 proved.2
  case falsityElim => exact .falsityElim proved
  case forallIntro => exact .forallIntro ‹_› ‹_› ‹_› proved
  case forallElim => exact .forallElim proved ‹_›
  case existsIntro => exact .existsIntro ‹_› proved
  case existsElim => exact .existsElim proved.1 ‹_› ‹_› ‹_› ‹_› proved.2
  case clause => exact .clause ‹_› ‹_› ‹_› proved
  case goalClause => exact .goalClause ‹_› ‹_› proved
  case defaultNegIntro => exact .defaultNegIntro ‹_› (‹NafCheck _ _›.sound _ _ _ ‹_›)
  case hoApplyIntro => exact .hoApplyIntro proved
  case hoApplyElim => exact .hoApplyElim proved
  case equalRefl => exact .equalRefl
  case equalSymm => exact .equalSymm proved
  case equalTrans => exact .equalTrans proved.1 proved.2
  case equalSubst => exact .equalSubst proved.1 ‹_› ‹_› proved.2
  case extension => exact ‹RuleCheck _ _›.sound _ _ _ _ ‹_› proved
  case reference => exact resolved _ _ _ ‹_›

omit [DecidableEq Literal] in
/-- `Valid.derives`: a valid tree reconstructs `Derives` for its conclusion,
with the checker's application symbol, KB, and NAF provider, and the context it
was checked under. -/
theorem Valid.derives
    (resolved : ∀ name context goal, refs name context goal →
      Derives checker.snapshot.hoApplySymbol checker.snapshot.kb context goal checker.provider)
    {context : ProofContext Variable Literal Symbol} {proof : Proof Variable Literal Symbol}
    (valid : Valid checker refs context proof) :
    Derives checker.snapshot.hoApplySymbol checker.snapshot.kb context proof.conclusion checker.provider := by
  induction valid with
  | node step children ih =>
      refine step.derives resolved fun entry member => ?_
      rw [List.zip_map_left, List.mem_map] at member
      obtain ⟨other, inside, rfl⟩ := member
      exact ih other inside

end Derives

/-! ## Capabilities a tree needs -/

/-- What a tree may need beyond the shared rules: an evidence check for NAF, a
registered derived rule, or a previously checked proof. -/
inductive Capability (Symbol : Type) where
  | negation
  | rule (name : Symbol)
  | lemma (name : Symbol)
  deriving DecidableEq, Repr

def Rule.requires : Rule Variable Literal Symbol → Option (Capability Symbol)
  | .defaultNegIntro _ => some .negation
  | .extension name _ => some (.rule name)
  | .reference name => some (.lemma name)
  | _ => none

mutual
/-- The capabilities a tree's nodes use, in preorder. -/
def Proof.requires : Proof Variable Literal Symbol → List (Capability Symbol)
  | .node rule _ premises => rule.requires.toList ++ Proof.requiresOf premises

def Proof.requiresOf : List (Proof Variable Literal Symbol) → List (Capability Symbol)
  | [] => []
  | proof :: rest => proof.requires ++ Proof.requiresOf rest
end

omit [DecidableEq Variable] [DecidableEq Symbol] [DecidableEq Literal] in
theorem Proof.requiresOf_eq : ∀ proofs : List (Proof Variable Literal Symbol),
    Proof.requiresOf proofs = proofs.flatMap Proof.requires
  | [] => rfl
  | proof :: rest => by simp [Proof.requiresOf, Proof.requiresOf_eq rest]

omit [DecidableEq Variable] [DecidableEq Symbol] in
theorem exists_zip_of_mem {α β : Type} {item : α} :
    ∀ {items : List α} {others : List β}, item ∈ items → items.length ≤ others.length →
      ∃ other, (item, other) ∈ items.zip others
  | [], _, member, _ => by cases member
  | _ :: _, [], _, bound => by simp at bound
  | first :: rest, other :: more, member, bound => by
      rcases List.mem_cons.mp member with rfl | inside
      · exact ⟨other, by simp⟩
      · obtain ⟨found, found_mem⟩ := exists_zip_of_mem inside (by simpa using bound)
        exact ⟨found, List.mem_cons_of_mem _ found_mem⟩

omit [DecidableEq Literal] in
/-- Every capability a valid tree uses is one the checker has: its NAF evidence
check, a registered derived rule, or a reference that resolves. -/
theorem Valid.uses {checker : Checker Variable Literal Symbol}
    {refs : Symbol → ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Prop}
    {context : ProofContext Variable Literal Symbol} {proof : Proof Variable Literal Symbol}
    (valid : Valid checker refs context proof) :
    ∀ capability ∈ proof.requires,
      (capability = .negation ∧ checker.negation.isSome = true) ∨
        (∃ name, capability = .rule name ∧ (checker.rule? name).isSome = true) ∨
        ∃ name inner goal, capability = .lemma name ∧ refs name inner goal := by
  induction valid with
  | @node context rule conclusion contexts premises step children ih =>
      intro capability member
      simp only [Proof.requires, Proof.requiresOf_eq, List.mem_append, List.mem_flatMap] at member
      rcases member with own | ⟨premise, inside, used⟩
      · generalize premises.map Proof.conclusion = conclusions at step
        cases step <;> simp only [Rule.requires, Option.toList_none, List.not_mem_nil, Option.toList_some,
          List.mem_singleton] at own
        · subst own; exact .inl ⟨rfl, by simp [‹checker.negation = some _›]⟩
        · subst own; exact .inr (.inl ⟨_, rfl, by simp [‹checker.rule? _ = some _›]⟩)
        · subst own; exact .inr (.inr ⟨_, _, _, rfl, ‹_›⟩)
      · have long : premises.length ≤ contexts.length := by rw [step.length, List.length_map]; exact Nat.le_refl _
        obtain ⟨premiseContext, entry⟩ := exists_zip_of_mem inside long
        exact ih (premise, premiseContext) entry capability used

end Checking

end AnthillModKbSpec.P1
