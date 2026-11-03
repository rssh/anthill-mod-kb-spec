import AnthillModKbSpec.Resolution.P1.Tree
import AnthillModKbSpec.Resolution.Machine.LeftRules

/-! # S09 commands as checked logical nodes

An S09 command (`Machine.Derived`) is one machine step that composes `Derives`
rules. A supplied proof spells it out in S08's logical nodes, so checking it
needs no new rule and no `RuleCheck`: each node is decided by its own rule's
procedure (`nodeCheck`), and the tree reconstructs `Derives` by `Valid.derives`.

| Command | Logical nodes |
| --- | --- |
| cut on a lemma `L` for the goal `C` | `impElim C [impIntro (L → C) [C under L], L]` |
| `A ∧ B` assumed | a cut on `B` by `conjRight`, then a cut on `A` by `conjLeft` |
| `A ∨ B` assumed | `disjElim C [A ∨ B, C under A, C under B]` |
| `∃x. A` assumed | `existsElim e A[e/x] C [∃x. A, C under A[e/x]]` |
| `∀x̄. A` assumed | universal eliminations from the assumption, then a cut on the instance |
| `∀x̄. (A → B)` assumed | the instance `A' → B'` by eliminations, `B'` by `impElim` on `A'`, then a cut on `B'` |
| a clause `H :- body` | the clause node for `H'`, then a cut on `H'` |
| a conjunctive head, split | the clause node for `H'`, then `conjLeft`/`conjRight` down to the conjunct |
| a head `A → false` | `impElim false [clause node for A' → false, A']` |

The implication command derives `B'` by `impElim`, discharges `B'` from the
continuation by `impIntro`, and applies `impElim` to obtain the goal, all in
the original context: no weakening or transport of context-indexed NAF
evidence is needed. Each construction is valid whenever the premise trees are
valid under the contexts the command gives them and its side conditions hold
(`Unfold.*_proves`). `exportDerived` builds the construction of a machine node
from its parameters read through the final store and its exported subproofs. -/

namespace AnthillModKbSpec.P1

open Machine

variable {Variable Literal Symbol : Type}

namespace Unfold

/-- Close an assumption. -/
def hypothesis (formula : Formula Variable Literal Symbol) : Proof Variable Literal Symbol :=
  .node .assumption formula []

/-- A cut: prove `lemma`, then the goal under `lemma`, discharged by
implication introduction and eliminated against the lemma's proof. -/
def cut (lemma goal : Formula Variable Literal Symbol) (lemmaProof continuation : Proof Variable Literal Symbol) :
    Proof Variable Literal Symbol :=
  .node .impElim goal [.node .impIntro (.imp lemma goal) [continuation], lemmaProof]

/-- `A ∧ B` assumed: the goal under `A` and `B`, by a cut on each component. -/
def conjUse (left right goal : Formula Variable Literal Symbol) (continuation : Proof Variable Literal Symbol) :
    Proof Variable Literal Symbol :=
  cut right goal (.node .conjRight right [hypothesis (.conj left right)])
    (cut left goal (.node .conjLeft left [hypothesis (.conj left right)]) continuation)

/-- `A ∨ B` assumed: case analysis on the assumption. -/
def disjCases (left right goal : Formula Variable Literal Symbol) (first second : Proof Variable Literal Symbol) :
    Proof Variable Literal Symbol :=
  .node .disjElim goal [hypothesis (.disj left right), first, second]

/-- `∃x. A` assumed: opened at `eigen`, as `opened`, for the continuation. -/
def existsOpen (existential : Formula Variable Literal Symbol) (eigen : Variable)
    (opened goal : Formula Variable Literal Symbol) (continuation : Proof Variable Literal Symbol) :
    Proof Variable Literal Symbol :=
  .node (.existsElim eigen opened) goal [hypothesis existential, continuation]

/-- Universal eliminations from an assumption: each step a witness and the
instance it gives. -/
def eliminations (assumption : Formula Variable Literal Symbol) (steps : List (Term Variable Literal Symbol × Formula Variable Literal Symbol)) :
    Proof Variable Literal Symbol :=
  steps.foldl (fun proof step => .node (.forallElim step.1) step.2 [proof]) (hypothesis assumption)

/-- `∀x̄. A` assumed: the instance by eliminations, then the goal under it. -/
def forallUse (assumption : Formula Variable Literal Symbol) (steps : List (Term Variable Literal Symbol × Formula Variable Literal Symbol))
    (instantiated goal : Formula Variable Literal Symbol) (continuation : Proof Variable Literal Symbol) :
    Proof Variable Literal Symbol :=
  cut instantiated goal (eliminations assumption steps) continuation

/-- `∀x̄. (A → B)` assumed: the instance `A' → B'` by eliminations, `B'` by
implication elimination on the proof of `A'`, then the goal under `B'`. -/
def impUse (assumption : Formula Variable Literal Symbol) (steps : List (Term Variable Literal Symbol × Formula Variable Literal Symbol))
    (conclusion goal : Formula Variable Literal Symbol) (argument continuation : Proof Variable Literal Symbol) :
    Proof Variable Literal Symbol :=
  cut conclusion goal (.node .impElim conclusion [eliminations assumption steps, argument]) continuation

/-- The clause node proving a head instance from the body's proof. -/
def clauseNode (clause : HornClause Variable Literal Symbol) (instantiation : List (Variable × Term Variable Literal Symbol))
    (head : Formula Variable Literal Symbol) (bodyProof : Proof Variable Literal Symbol) : Proof Variable Literal Symbol :=
  .node (.clause clause instantiation) head [bodyProof]

/-- A clause `H :- body`: the head instance from the body, then the goal under it. -/
def headUse (clause : HornClause Variable Literal Symbol) (instantiation : List (Variable × Term Variable Literal Symbol))
    (head goal : Formula Variable Literal Symbol) (bodyProof continuation : Proof Variable Literal Symbol) :
    Proof Variable Literal Symbol :=
  cut head goal (clauseNode clause instantiation head bodyProof) continuation

/-- Project the conjunct at `path` out of a proof of a nested conjunction, as
`Term.component?` reads it; `none` for a path the formula does not have. -/
def project : List Bool → Formula Variable Literal Symbol → Proof Variable Literal Symbol →
    Option (Proof Variable Literal Symbol)
  | [], _, proof => some proof
  | false :: path, .conj left _, proof => project path left (.node .conjLeft left [proof])
  | true :: path, .conj _ right, proof => project path right (.node .conjRight right [proof])
  | _ :: _, _, _ => none

/-- A conjunctive head, split: the conjunct at `path` of the head instance. -/
def headProject (clause : HornClause Variable Literal Symbol) (instantiation : List (Variable × Term Variable Literal Symbol))
    (head : Formula Variable Literal Symbol) (path : List Bool) (bodyProof : Proof Variable Literal Symbol) :
    Option (Proof Variable Literal Symbol) :=
  project path head (clauseNode clause instantiation head bodyProof)

/-- A head `A → false`, as the denial `false :- body, A`. -/
def headDenial (clause : HornClause Variable Literal Symbol) (instantiation : List (Variable × Term Variable Literal Symbol))
    (premise : Formula Variable Literal Symbol) (bodyProof argument : Proof Variable Literal Symbol) :
    Proof Variable Literal Symbol :=
  .node .impElim .falsity [clauseNode clause instantiation (.imp premise .falsity) bodyProof, argument]

end Unfold

/-- Universal eliminations, one per step, lead from a formula to an instance:
each step's formula is the previous one's body at the step's witness. -/
inductive Instances [DecidableEq Variable] :
    Formula Variable Literal Symbol → List (Term Variable Literal Symbol × Formula Variable Literal Symbol) →
      Formula Variable Literal Symbol → Prop where
  | nil {formula : Formula Variable Literal Symbol} : Instances formula [] formula
  | cons {binder : Variable} {body next last : Formula Variable Literal Symbol} {witness : Term Variable Literal Symbol}
      {steps : List (Term Variable Literal Symbol × Formula Variable Literal Symbol)}
      (instantiation : Substitutes (Substitution.single binder witness) body next) (rest : Instances next steps last) :
      Instances (.forallVar binder body) ((witness, next) :: steps) last

section Proves

variable [DecidableEq Variable] [DecidableEq Symbol] {checker : Checker Variable Literal Symbol}
  {refs : Symbol → ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Prop}
  {context : ProofContext Variable Literal Symbol}

/-- A valid tree under `context` concluding `goal`. -/
def Proves (checker : Checker Variable Literal Symbol)
    (refs : Symbol → ProofContext Variable Literal Symbol → Formula Variable Literal Symbol → Prop)
    (context : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol)
    (proof : Proof Variable Literal Symbol) : Prop :=
  Valid checker refs context proof ∧ proof.conclusion = goal

namespace Unfold

/-- A node with one premise, given its rule application and the premise's tree
under the context it adds. -/
theorem node₁_proves {rule : Rule Variable Literal Symbol} {goal premise : Formula Variable Literal Symbol}
    {added : ProofContext Variable Literal Symbol} {child : Proof Variable Literal Symbol}
    (step : Local checker refs context rule goal [premise] [added])
    (proves : Proves checker refs (added ++ context) premise child) :
    Proves checker refs context goal (.node rule goal [child]) :=
  ⟨.node (by simpa only [List.map_cons, List.map_nil, proves.2] using step) (by simpa using proves.1), rfl⟩

theorem node₂_proves {rule : Rule Variable Literal Symbol} {goal first second : Formula Variable Literal Symbol}
    {firstAdded secondAdded : ProofContext Variable Literal Symbol} {firstChild secondChild : Proof Variable Literal Symbol}
    (step : Local checker refs context rule goal [first, second] [firstAdded, secondAdded])
    (firstProves : Proves checker refs (firstAdded ++ context) first firstChild)
    (secondProves : Proves checker refs (secondAdded ++ context) second secondChild) :
    Proves checker refs context goal (.node rule goal [firstChild, secondChild]) :=
  ⟨.node (by simpa only [List.map_cons, List.map_nil, firstProves.2, secondProves.2] using step)
    (by simpa using ⟨firstProves.1, secondProves.1⟩), rfl⟩

theorem node₃_proves {rule : Rule Variable Literal Symbol} {goal first second third : Formula Variable Literal Symbol}
    {firstAdded secondAdded thirdAdded : ProofContext Variable Literal Symbol}
    {firstChild secondChild thirdChild : Proof Variable Literal Symbol}
    (step : Local checker refs context rule goal [first, second, third] [firstAdded, secondAdded, thirdAdded])
    (firstProves : Proves checker refs (firstAdded ++ context) first firstChild)
    (secondProves : Proves checker refs (secondAdded ++ context) second secondChild)
    (thirdProves : Proves checker refs (thirdAdded ++ context) third thirdChild) :
    Proves checker refs context goal (.node rule goal [firstChild, secondChild, thirdChild]) :=
  ⟨.node (by simpa only [List.map_cons, List.map_nil, firstProves.2, secondProves.2, thirdProves.2] using step)
    (by simpa using ⟨firstProves.1, secondProves.1, thirdProves.1⟩), rfl⟩

theorem hypothesis_proves {formula : Formula Variable Literal Symbol} (member : formula ∈ context) :
    Proves checker refs context formula (hypothesis formula) :=
  ⟨.node (contexts := []) (.assumption member) (by simp), rfl⟩

theorem cut_proves {lemma goal : Formula Variable Literal Symbol} {lemmaProof continuation : Proof Variable Literal Symbol}
    (lemmaProves : Proves checker refs context lemma lemmaProof)
    (continues : Proves checker refs (lemma :: context) goal continuation) :
    Proves checker refs context goal (cut lemma goal lemmaProof continuation) :=
  node₂_proves .impElim (node₁_proves .impIntro continues) lemmaProves

theorem conjUse_proves {left right goal : Formula Variable Literal Symbol} {continuation : Proof Variable Literal Symbol}
    (member : .conj left right ∈ context) (continues : Proves checker refs (left :: right :: context) goal continuation) :
    Proves checker refs context goal (conjUse left right goal continuation) :=
  cut_proves (node₁_proves .conjRight (hypothesis_proves member))
    (cut_proves (node₁_proves .conjLeft (hypothesis_proves (List.mem_cons_of_mem _ member))) continues)

theorem disjCases_proves {left right goal : Formula Variable Literal Symbol} {first second : Proof Variable Literal Symbol}
    (member : .disj left right ∈ context) (firstCase : Proves checker refs (left :: context) goal first)
    (secondCase : Proves checker refs (right :: context) goal second) :
    Proves checker refs context goal (disjCases left right goal first second) :=
  node₃_proves .disjElim (hypothesis_proves member) firstCase secondCase

/-- The eigenvariable is fresh for the context, the existential, and the
goal, and `opened` is the existential's body opened at it: the side conditions
of `existsElim`. -/
theorem existsOpen_proves {binder eigen : Variable} {body opened goal : Formula Variable Literal Symbol}
    {continuation : Proof Variable Literal Symbol} (member : .existsVar binder body ∈ context)
    (freshContext : FreshForContext eigen context) (freshBody : eigen ∉ (Term.existsVar binder body).freeVars)
    (freshGoal : eigen ∉ goal.freeVars) (opening : Substitutes (Substitution.single binder (.var eigen)) body opened)
    (continues : Proves checker refs (opened :: context) goal continuation) :
    Proves checker refs context goal (existsOpen (.existsVar binder body) eigen opened goal continuation) :=
  node₂_proves (.existsElim freshContext freshBody freshGoal opening) (hypothesis_proves member) continues

theorem eliminations_step {formula last : Formula Variable Literal Symbol} {proof : Proof Variable Literal Symbol}
    {steps : List (Term Variable Literal Symbol × Formula Variable Literal Symbol)}
    (proves : Proves checker refs context formula proof) (instances : Instances formula steps last) :
    Proves checker refs context last
      (steps.foldl (fun proof step => .node (.forallElim step.1) step.2 [proof]) proof) := by
  induction instances generalizing proof with
  | nil => exact proves
  | cons instantiation _ ih => exact ih (node₁_proves (.forallElim instantiation) proves)

theorem eliminations_proves {assumption last : Formula Variable Literal Symbol}
    {steps : List (Term Variable Literal Symbol × Formula Variable Literal Symbol)} (member : assumption ∈ context)
    (instances : Instances assumption steps last) :
    Proves checker refs context last (eliminations assumption steps) :=
  eliminations_step (hypothesis_proves member) instances

theorem forallUse_proves {assumption instantiated goal : Formula Variable Literal Symbol}
    {steps : List (Term Variable Literal Symbol × Formula Variable Literal Symbol)} {continuation : Proof Variable Literal Symbol}
    (member : assumption ∈ context) (instances : Instances assumption steps instantiated)
    (continues : Proves checker refs (instantiated :: context) goal continuation) :
    Proves checker refs context goal (forallUse assumption steps instantiated goal continuation) :=
  cut_proves (eliminations_proves member instances) continues

/-- The implication command: the premise is proved in the original context,
and the goal under the conclusion. -/
theorem impUse_proves {assumption premise conclusion goal : Formula Variable Literal Symbol}
    {steps : List (Term Variable Literal Symbol × Formula Variable Literal Symbol)}
    {argument continuation : Proof Variable Literal Symbol}
    (member : assumption ∈ context) (instances : Instances assumption steps (.imp premise conclusion))
    (argues : Proves checker refs context premise argument)
    (continues : Proves checker refs (conclusion :: context) goal continuation) :
    Proves checker refs context goal (impUse assumption steps conclusion goal argument continuation) :=
  cut_proves (node₂_proves .impElim (eliminations_proves member instances) argues) continues

theorem clauseNode_proves {head : Term Variable Literal Symbol} {instantiated goal : Formula Variable Literal Symbol}
    {bodyGoals : List (Term Variable Literal Symbol)} {instantiation : List (Variable × Term Variable Literal Symbol)}
    {bodyProof : Proof Variable Literal Symbol}
    (member : HornClause.definite head bodyGoals ∈ checker.snapshot.clauses)
    (headInstance : Substitutes (ofPairs instantiation) head goal)
    (bodyInstance : Substitutes (ofPairs instantiation) (.conjunction bodyGoals) instantiated)
    (bodyProves : Proves checker refs context instantiated bodyProof) :
    Proves checker refs context goal (clauseNode (.definite head bodyGoals) instantiation goal bodyProof) :=
  node₁_proves (.clause member headInstance bodyInstance) bodyProves

theorem headUse_proves {head instantiatedHead instantiated goal : Formula Variable Literal Symbol}
    {bodyGoals : List (Term Variable Literal Symbol)} {instantiation : List (Variable × Term Variable Literal Symbol)}
    {bodyProof continuation : Proof Variable Literal Symbol}
    (member : HornClause.definite head bodyGoals ∈ checker.snapshot.clauses)
    (headInstance : Substitutes (ofPairs instantiation) head instantiatedHead)
    (bodyInstance : Substitutes (ofPairs instantiation) (.conjunction bodyGoals) instantiated)
    (bodyProves : Proves checker refs context instantiated bodyProof)
    (continues : Proves checker refs (instantiatedHead :: context) goal continuation) :
    Proves checker refs context goal
      (headUse (.definite head bodyGoals) instantiation instantiatedHead goal bodyProof continuation) :=
  cut_proves (clauseNode_proves member headInstance bodyInstance bodyProves) continues

/-- A path the formula has projects a proof of it to a proof of the conjunct. -/
theorem project_proves : ∀ {path : List Bool} {formula component : Formula Variable Literal Symbol}
    {proof : Proof Variable Literal Symbol}, formula.component? path = some component →
    Proves checker refs context formula proof →
      ∃ projected, project path formula proof = some projected ∧ Proves checker refs context component projected
  | [], _, _, proof, found, proves => by cases found; exact ⟨proof, rfl, proves⟩
  | direction :: _, _, _, proof, found, proves => by
      obtain ⟨left, right, rfl, rest⟩ := Term.component?_conj found
      cases direction
      · exact project_proves (proof := .node .conjLeft left [proof]) rest (node₁_proves .conjLeft proves)
      · exact project_proves (proof := .node .conjRight right [proof]) rest (node₁_proves .conjRight proves)

/-- A split conjunctive head: the conjunct of the head instance at `path`. -/
theorem headProject_proves {head instantiatedHead instantiated component : Formula Variable Literal Symbol}
    {bodyGoals : List (Term Variable Literal Symbol)} {instantiation : List (Variable × Term Variable Literal Symbol)}
    {path : List Bool} {bodyProof : Proof Variable Literal Symbol}
    (member : HornClause.definite head bodyGoals ∈ checker.snapshot.clauses)
    (headInstance : Substitutes (ofPairs instantiation) head instantiatedHead)
    (bodyInstance : Substitutes (ofPairs instantiation) (.conjunction bodyGoals) instantiated)
    (bodyProves : Proves checker refs context instantiated bodyProof)
    (found : instantiatedHead.component? path = some component) :
    ∃ projected, headProject (.definite head bodyGoals) instantiation instantiatedHead path bodyProof = some projected ∧
      Proves checker refs context component projected :=
  project_proves found (clauseNode_proves member headInstance bodyInstance bodyProves)

/-- A head `A → false` as a denial: falsity from the body and the instance of `A`. -/
theorem headDenial_proves {head instantiated premise : Formula Variable Literal Symbol}
    {bodyGoals : List (Term Variable Literal Symbol)} {instantiation : List (Variable × Term Variable Literal Symbol)}
    {bodyProof argument : Proof Variable Literal Symbol}
    (member : HornClause.definite head bodyGoals ∈ checker.snapshot.clauses)
    (headInstance : Substitutes (ofPairs instantiation) head (.imp premise .falsity))
    (bodyInstance : Substitutes (ofPairs instantiation) (.conjunction bodyGoals) instantiated)
    (bodyProves : Proves checker refs context instantiated bodyProof)
    (argues : Proves checker refs context premise argument) :
    Proves checker refs context .falsity (headDenial (.definite head bodyGoals) instantiation premise bodyProof argument) :=
  node₂_proves .impElim (clauseNode_proves member headInstance bodyInstance bodyProves) argues

end Unfold

end Proves

/-! ## Exporting a command node -/

section Export

variable [DecidableEq Variable] [FreshNames Variable]

/-- The universal eliminations of `witnesses` from a formula: each witness with
the instance it gives, or `none` past the formula's leading binders. Their
last instance is `Term.instantiateLeading`'s. -/
def leadingSteps : Term Variable Literal Symbol → List (Term Variable Literal Symbol) →
    Option (List (Term Variable Literal Symbol × Term Variable Literal Symbol))
  | _, [] => some []
  | .forallVar binder body, witness :: rest =>
      let next := body.instantiate (Substitution.single binder witness)
      (leadingSteps next rest).map ((witness, next) :: ·)
  | _, _ :: _ => none

/-- The steps' last instance is `Term.instantiateLeading`'s. -/
theorem leadingSteps_last {rule : Term Variable Literal Symbol} {witnesses : List (Term Variable Literal Symbol)}
    {steps : List (Term Variable Literal Symbol × Term Variable Literal Symbol)}
    (found : leadingSteps rule witnesses = some steps) :
    rule.instantiateLeading witnesses = some ((steps.getLast?.map Prod.snd).getD rule) := by
  induction witnesses generalizing rule steps with
  | nil => cases found; rfl
  | cons witness rest ih =>
      cases rule with
      | forallVar binder body =>
          simp only [leadingSteps, Option.map_eq_some_iff] at found
          obtain ⟨tail, tailEq, rfl⟩ := found
          rw [Term.instantiateLeading, ih tailEq, List.getLast?_cons]
          cases tail.getLast? <;> rfl
      | _ => cases found

/-- Read through any store, the steps are universal eliminations from the read
rule to the read instance: the chain an exported `forallUse` or `impUse` node
spells out is checked whatever the final answers are. -/
theorem leadingSteps_instances (store : Store Variable Literal Symbol) {rule : Term Variable Literal Symbol}
    {witnesses : List (Term Variable Literal Symbol)}
    {steps : List (Term Variable Literal Symbol × Term Variable Literal Symbol)}
    (found : leadingSteps rule witnesses = some steps) :
    Instances (store.resolve rule) (steps.map fun step => (store.resolve step.1, store.resolve step.2))
      (store.resolve ((steps.getLast?.map Prod.snd).getD rule)) := by
  induction witnesses generalizing rule steps with
  | nil => cases found; exact .nil
  | cons witness rest ih =>
      cases rule with
      | forallVar binder body =>
          simp only [leadingSteps, Option.map_eq_some_iff] at found
          obtain ⟨tail, tailEq, rfl⟩ := found
          obtain ⟨renamed, result, read, opening⟩ := store.resolve_forallVar binder body
          have last : ((((witness, body.instantiate (Substitution.single binder witness)) :: tail).getLast?.map
              Prod.snd).getD (Term.forallVar binder body)) =
              (tail.getLast?.map Prod.snd).getD (body.instantiate (Substitution.single binder witness)) := by
            rw [List.getLast?_cons]; cases tail.getLast? <;> rfl
          rw [read, last, List.map_cons]
          exact .cons (opening (body.instantiate_substitutes _)) (ih tailEq)
      | _ => cases found

/-- A clause renaming as an instantiation read through the store. -/
def readInstantiation (store : Store Variable Literal Symbol) (fresh : List (Variable × Variable)) :
    List (Variable × Term Variable Literal Symbol) :=
  fresh.map fun pair => (pair.1, store.resolve (.var pair.2))

/-- The logical nodes of an S09 machine node: its parameters read through the
store, its goal as read, and its exported subproofs, in premise order. A node
whose parameters do not have the command's shape exports nothing. -/
def exportDerived (store : Store Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    Derived Variable Literal Symbol → List (Proof Variable Literal Symbol) → Option (Proof Variable Literal Symbol)
  | .conjUse (.conj left right), [continuation] =>
      some (Unfold.conjUse (store.resolve left) (store.resolve right) goal continuation)
  | .disjCases (.disj left right), [first, second] =>
      some (Unfold.disjCases (store.resolve left) (store.resolve right) goal first second)
  | .existsOpen assumption@(.existsVar binder body) eigen, [continuation] =>
      some (Unfold.existsOpen (store.resolve assumption) eigen
        (store.resolve (body.instantiate (Substitution.single binder (.var eigen)))) goal continuation)
  | .forallUse assumption witnesses, [continuation] =>
      (leadingSteps assumption witnesses).map fun steps =>
        let read := steps.map fun step => (store.resolve step.1, store.resolve step.2)
        Unfold.forallUse (store.resolve assumption) read ((read.getLast?.map Prod.snd).getD (store.resolve assumption))
          goal continuation
  | .impUse assumption witnesses, [argument, continuation] =>
      match leadingSteps assumption witnesses with
      | some steps =>
          match (steps.getLast?.map Prod.snd).getD assumption with
          | .imp _ conclusion =>
              some (Unfold.impUse (store.resolve assumption)
                (steps.map fun step => (store.resolve step.1, store.resolve step.2))
                (store.resolve conclusion) goal argument continuation)
          | _ => none
      | none => none
  | .headUse clause@(.definite head _) fresh, [bodyProof, continuation] =>
      some (Unfold.headUse clause (readInstantiation store fresh)
        (store.resolve (head.instantiate (Substitution.rename fresh))) goal bodyProof continuation)
  | .headProject clause@(.definite head _) fresh path, [bodyProof] =>
      Unfold.headProject clause (readInstantiation store fresh)
        (store.resolve (head.instantiate (Substitution.rename fresh))) path bodyProof
  | .headDenial clause@(.definite (.imp premise .falsity) _) fresh, [bodyProof, argument] =>
      some (Unfold.headDenial clause (readInstantiation store fresh)
        (store.resolve (premise.instantiate (Substitution.rename fresh))) bodyProof argument)
  | _, _ => none

end Export

end AnthillModKbSpec.P1
