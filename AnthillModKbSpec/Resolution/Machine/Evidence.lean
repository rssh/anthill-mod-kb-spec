import AnthillModKbSpec.Resolution.Machine.Store
import AnthillModKbSpec.Resolution.P0.GroundSearch

namespace AnthillModKbSpec.Machine

/-- Kinds of closed-world evidence: valid only for the exact snapshot (KB,
registry, and context) it was computed against. -/
inductive ClosedWorld where
  /-- Complete failure of a NAF operand. -/
  | completeFailure
  /-- No witness in a certified finite cover. -/
  | finiteAbsence
  /-- A finite cover of a range is complete. -/
  | enumeration
  deriving DecidableEq, Repr

/-- Rule identity, independent of parameters. Each name is a `Derives` rule,
except `extension`, a derived or certificate rule added by S08-S14. -/
inductive RuleId where
  | assumption | truth | conjIntro | conjLeft | conjRight | disjLeft | disjRight | disjElim
  | impIntro | impElim | falsityElim | forallIntro | forallElim | existsIntro | existsElim
  | clause | goalClause | defaultNegIntro | hoApplyIntro | hoApplyElim
  | equalRefl | equalSymm | equalTrans | equalSubst | extension
  deriving DecidableEq, Repr

/-- Closed-world evidence retained in a proof node: its kind and the certificate
the command produced. `Certificate` is abstract here: S07 and S10 define the
certificates, and S08 checks them, so an exported proof never recomputes a
failure or a cover. A proof tree carries no snapshot of its own; every
certificate is relative to the snapshot of the run that built the tree. -/
structure ClosedWorldEvidence (Certificate : Type) where
  kind : ClosedWorld
  certificate : Certificate
  deriving Repr

variable {Variable Literal Symbol Certificate Snapshot : Type}

/-- A rule application with the parameters its conclusion and premises do not
determine: eigenvariables, witnesses, the clause and its finite instantiation,
replacement templates, and closed-world certificates. With the node's obligation
and premises, this is what S08's checker needs; no search is replayed. -/
inductive RuleApp (Variable Literal Symbol Certificate : Type) where
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
  | forallIntro (eigen : Variable)
  | forallElim (witness : Term Variable Literal Symbol)
  | existsIntro (witness : Term Variable Literal Symbol)
  | existsElim (eigen : Variable)
  /-- A KB clause, recorded as a template, with its explicit instantiation. -/
  | clause (clause : HornClause Variable Literal Symbol)
      (instantiation : List (Variable × Term Variable Literal Symbol))
  | goalClause (clause : HornClause Variable Literal Symbol)
      (instantiation : List (Variable × Term Variable Literal Symbol))
  /-- NAF, with the certificate of the operand's complete failure. -/
  | defaultNegIntro (certificate : Certificate)
  | hoApplyIntro
  | hoApplyElim
  | equalRefl
  | equalSymm
  | equalTrans
  | equalSubst (name : Variable) (template : Term Variable Literal Symbol)
  /-- A rule named in the symbol namespace, so S08 can encode it as `Term`. It
  carries the closed-world evidence it uses, if any. -/
  | extension (name : Symbol) (parameters : List (Term Variable Literal Symbol))
      (closedWorld : Option (ClosedWorldEvidence Certificate))
  deriving Repr

def RuleApp.id : RuleApp Variable Literal Symbol Certificate → RuleId
  | .assumption => .assumption | .truth => .truth | .conjIntro => .conjIntro
  | .conjLeft => .conjLeft | .conjRight => .conjRight | .disjLeft => .disjLeft
  | .disjRight => .disjRight | .disjElim => .disjElim | .impIntro => .impIntro
  | .impElim => .impElim | .falsityElim => .falsityElim | .forallIntro _ => .forallIntro
  | .forallElim _ => .forallElim | .existsIntro _ => .existsIntro | .existsElim _ => .existsElim
  | .clause _ _ => .clause | .goalClause _ _ => .goalClause | .defaultNegIntro _ => .defaultNegIntro
  | .hoApplyIntro => .hoApplyIntro | .hoApplyElim => .hoApplyElim | .equalRefl => .equalRefl
  | .equalSymm => .equalSymm | .equalTrans => .equalTrans | .equalSubst _ _ => .equalSubst
  | .extension _ _ _ => .extension

def RuleApp.closedWorld? : RuleApp Variable Literal Symbol Certificate → Option (ClosedWorldEvidence Certificate)
  | .defaultNegIntro certificate => some ⟨.completeFailure, certificate⟩
  | .extension _ _ evidence => evidence
  | _ => none

/-- Monotonic evidence stays valid when the KB or the predicate registry grows:
clause applications (including the generated signature clauses) and every
logical rule. Snapshot-indexed evidence is closed-world: NAF, finite absence,
and enumeration. An extension's class is what it declares; S08 must prove that
an extension declared monotonic survives growth, since `Derives.mono` covers
only `Derives` rules. Lowered formulas carry no snapshot dependency, since
lowering reads only the signature naming. -/
inductive EvidenceClass where
  | monotonic
  | snapshotIndexed
  deriving DecidableEq, Repr

def RuleApp.evidenceClass (rule : RuleApp Variable Literal Symbol Certificate) : EvidenceClass :=
  match rule.closedWorld? with
  | some _ => .snapshotIndexed
  | none => .monotonic

/-- A finished proof tree. Each node records its rule application, the
obligation it proves (scope, context, and conclusion), the premises it
required, and one subproof per premise in order. There is no hole constructor:
a tree is built only from completed premises. Formulas may mention flexible
names, read through the final answer bindings. -/
inductive ProofTree (Variable Literal Symbol Certificate : Type) where
  | node (rule : RuleApp Variable Literal Symbol Certificate) (obligation : Obligation Variable Literal Symbol)
      (premises : List (Premise Variable Literal Symbol)) (subproofs : List (ProofTree Variable Literal Symbol Certificate))

namespace ProofTree

def rule : ProofTree Variable Literal Symbol Certificate → RuleApp Variable Literal Symbol Certificate
  | .node rule _ _ _ => rule

def obligation : ProofTree Variable Literal Symbol Certificate → Obligation Variable Literal Symbol
  | .node _ obligation _ _ => obligation

def premises : ProofTree Variable Literal Symbol Certificate → List (Premise Variable Literal Symbol)
  | .node _ _ premises _ => premises

def subproofs : ProofTree Variable Literal Symbol Certificate → List (ProofTree Variable Literal Symbol Certificate)
  | .node _ _ _ subproofs => subproofs

mutual
/-- Rule identities in preorder. -/
def rules : ProofTree Variable Literal Symbol Certificate → List RuleId
  | .node rule _ _ subproofs => rule.id :: rulesOf subproofs

def rulesOf : List (ProofTree Variable Literal Symbol Certificate) → List RuleId
  | [] => []
  | tree :: trees => tree.rules ++ rulesOf trees
end

mutual
/-- The closed-world evidence the tree's nodes retain, in preorder. -/
def closedWorld : ProofTree Variable Literal Symbol Certificate → List (ClosedWorldEvidence Certificate)
  | .node rule _ _ subproofs => rule.closedWorld?.toList ++ closedWorldOf subproofs

def closedWorldOf : List (ProofTree Variable Literal Symbol Certificate) → List (ClosedWorldEvidence Certificate)
  | [] => []
  | tree :: trees => tree.closedWorld ++ closedWorldOf trees
end

/-- A tree with no closed-world node does not depend on its run's snapshot. For
`Derives` rules its validity survives KB and registry growth (`Derives.mono`
with the disabled provider); an extension declared monotonic needs that from its
own soundness proof. -/
def Monotonic (tree : ProofTree Variable Literal Symbol Certificate) : Prop := tree.closedWorld = []

mutual
/-- Scope coherence: each subproof proves exactly the premise obligation built
from its parent's scope. Assumptions and rigid names a premise opens therefore
appear only inside that premise's subtree, and every premise has a subproof. -/
inductive Coherent : ProofTree Variable Literal Symbol Certificate → Prop where
  | node {rule : RuleApp Variable Literal Symbol Certificate} {obligation : Obligation Variable Literal Symbol}
      {premises : List (Premise Variable Literal Symbol)} {subproofs : List (ProofTree Variable Literal Symbol Certificate)}
      (children : CoherentPremises obligation premises subproofs) :
      Coherent (.node rule obligation premises subproofs)

inductive CoherentPremises : Obligation Variable Literal Symbol → List (Premise Variable Literal Symbol) →
    List (ProofTree Variable Literal Symbol Certificate) → Prop where
  | nil {parent : Obligation Variable Literal Symbol} : CoherentPremises parent [] []
  | cons {parent : Obligation Variable Literal Symbol} {premise : Premise Variable Literal Symbol}
      {premises : List (Premise Variable Literal Symbol)} {tree : ProofTree Variable Literal Symbol Certificate}
      {trees : List (ProofTree Variable Literal Symbol Certificate)}
      (opened : tree.obligation = parent.premise premise) (coherent : Coherent tree)
      (rest : CoherentPremises parent premises trees) :
      CoherentPremises parent (premise :: premises) (tree :: trees)
end

theorem CoherentPremises.length_eq {parent : Obligation Variable Literal Symbol}
    {premises : List (Premise Variable Literal Symbol)} {trees : List (ProofTree Variable Literal Symbol Certificate)}
    (coherent : CoherentPremises parent premises trees) : trees.length = premises.length := by
  induction premises generalizing trees with
  | nil => cases coherent; rfl
  | cons premise rest ih =>
      cases coherent with
      | cons _ _ tail => simp [ih tail]

theorem CoherentPremises.snoc {parent : Obligation Variable Literal Symbol}
    {premises : List (Premise Variable Literal Symbol)} {trees : List (ProofTree Variable Literal Symbol Certificate)}
    {premise : Premise Variable Literal Symbol} {tree : ProofTree Variable Literal Symbol Certificate}
    (coherent : CoherentPremises parent premises trees) (opened : tree.obligation = parent.premise premise)
    (valid : tree.Coherent) : CoherentPremises parent (premises ++ [premise]) (trees ++ [tree]) := by
  induction premises generalizing trees with
  | nil => cases coherent; exact .cons opened valid .nil
  | cons first rest ih =>
      cases coherent with
      | cons head headValid tail => exact .cons head headValid (ih tail)

/-- Each subproof of a coherent tree proves its own premise, under the parent
context extended only by that premise's discharged assumptions. -/
theorem CoherentPremises.subproof_context {parent : Obligation Variable Literal Symbol}
    {premises : List (Premise Variable Literal Symbol)} {trees : List (ProofTree Variable Literal Symbol Certificate)}
    (coherent : CoherentPremises parent premises trees) :
    ∀ pair ∈ premises.zip trees, pair.2.obligation.context =
      pair.1.discharge.assumptions ++ parent.context ∧ pair.2.obligation.goal = pair.1.goal := by
  induction premises generalizing trees with
  | nil => cases coherent; simp
  | cons premise rest ih =>
      cases coherent with
      | cons opened _ tail =>
          intro pair member
          simp only [List.zip_cons_cons, List.mem_cons] at member
          rcases member with rfl | member
          · exact ⟨by rw [opened]; rfl, by rw [opened]; rfl⟩
          · exact ih tail pair member

end ProofTree

/-- A successful run: the tree for the root obligation, the final store, and
the snapshot the tree's closed-world certificates are relative to (irrelevant
for a `Monotonic` tree). Answers are the root's flexible names read through the
store. -/
structure CompletedProof (Variable Literal Symbol Certificate Snapshot : Type) where
  snapshot : Snapshot
  root : Obligation Variable Literal Symbol
  tree : ProofTree Variable Literal Symbol Certificate
  store : Store Variable Literal Symbol

def CompletedProof.answer [DecidableEq Variable] [FreshNames Variable]
    (proof : CompletedProof Variable Literal Symbol Certificate Snapshot) (name : Variable) :
    Term Variable Literal Symbol :=
  proof.store.resolve (.var name)

/-! ## Monotonic and snapshot-indexed evidence

Clause and logical evidence transfers along KB growth by `Derives.mono`, and the
generated signature clauses only grow with the registry
(`Elaboration.signatureKb_mono`). The ground NAF provider below is the
contrasting closed-world case: it names its exact KB and context. -/

variable {hoApplySymbol : Symbol}

/-- Ground complete-failure evidence holds only for its own program, context,
and application symbol, so it is never reused under a grown KB. -/
theorem groundFailure_exact {program : GroundSearch.Program Variable Literal Symbol hoApplySymbol}
    {context : GroundSearch.Context Variable Literal Symbol hoApplySymbol}
    {actualSymbol : Symbol} {kb : LogicalKb Variable Literal Symbol}
    {actualContext : ProofContext Variable Literal Symbol} {goal : Formula Variable Literal Symbol}
    (evidence : GroundSearch.failureEvidence program context actualSymbol kb actualContext goal) :
    actualSymbol = hoApplySymbol ∧ kb = program.toKb ∧ actualContext = context.assumptions :=
  ⟨evidence.1, evidence.2.1, evidence.2.2.1⟩

theorem groundFailure_stale {program : GroundSearch.Program Variable Literal Symbol hoApplySymbol}
    {context : GroundSearch.Context Variable Literal Symbol hoApplySymbol}
    {kb : LogicalKb Variable Literal Symbol} (grown : kb ≠ program.toKb)
    (actualContext : ProofContext Variable Literal Symbol) (goal : Formula Variable Literal Symbol) :
    ¬ GroundSearch.failureEvidence program context hoApplySymbol kb actualContext goal :=
  fun evidence => grown (groundFailure_exact evidence).2.1

end AnthillModKbSpec.Machine
