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
required, and one subproof per premise in order. A tree is built only from
completed premises. The one leaf that is not a rule application is a reference
to a delayed obligation (S18): its proof is built after its place in the tree
has been passed, so it is recorded separately under the suspension id and
substituted at the end (`fill`). Formulas may mention flexible names, read
through the final answer bindings. -/
inductive ProofTree (Variable Literal Symbol Certificate : Type) where
  | node (rule : RuleApp Variable Literal Symbol Certificate) (obligation : Obligation Variable Literal Symbol)
      (premises : List (Premise Variable Literal Symbol)) (subproofs : List (ProofTree Variable Literal Symbol Certificate))
  /-- The separately recorded proof of the delayed obligation with this id. -/
  | deferred (id : Nat) (obligation : Obligation Variable Literal Symbol)

/-- A suspension id with the obligation it stands for: what a reference names
and what a pending wakeup, a woken continuation, or a deferred proof holds. -/
abbrev Hole (Variable Literal Symbol : Type) := Nat × Obligation Variable Literal Symbol

namespace ProofTree

def rule? : ProofTree Variable Literal Symbol Certificate → Option (RuleApp Variable Literal Symbol Certificate)
  | .node rule _ _ _ => some rule
  | .deferred _ _ => none

def obligation : ProofTree Variable Literal Symbol Certificate → Obligation Variable Literal Symbol
  | .node _ obligation _ _ => obligation
  | .deferred _ obligation => obligation

def premises : ProofTree Variable Literal Symbol Certificate → List (Premise Variable Literal Symbol)
  | .node _ _ premises _ => premises
  | .deferred _ _ => []

def subproofs : ProofTree Variable Literal Symbol Certificate → List (ProofTree Variable Literal Symbol Certificate)
  | .node _ _ _ subproofs => subproofs
  | .deferred _ _ => []

mutual
/-- Rule identities in preorder. A reference is not a rule application; `refs`
lists the references. A successful run's tree has none. -/
def rules : ProofTree Variable Literal Symbol Certificate → List RuleId
  | .node rule _ _ subproofs => rule.id :: rulesOf subproofs
  | .deferred _ _ => []

def rulesOf : List (ProofTree Variable Literal Symbol Certificate) → List RuleId
  | [] => []
  | tree :: trees => tree.rules ++ rulesOf trees
end

mutual
/-- The closed-world evidence the tree's nodes retain, in preorder. -/
def closedWorld : ProofTree Variable Literal Symbol Certificate → List (ClosedWorldEvidence Certificate)
  | .node rule _ _ subproofs => rule.closedWorld?.toList ++ closedWorldOf subproofs
  | .deferred _ _ => []

def closedWorldOf : List (ProofTree Variable Literal Symbol Certificate) → List (ClosedWorldEvidence Certificate)
  | [] => []
  | tree :: trees => tree.closedWorld ++ closedWorldOf trees
end

mutual
/-- The obligations the tree's nodes prove and require, in preorder: each
node's obligation followed by its premise obligations. A reference contributes
the obligation it stands for. -/
def obligations : ProofTree Variable Literal Symbol Certificate → List (Obligation Variable Literal Symbol)
  | .node _ obligation premises subproofs =>
      obligation :: premises.map obligation.premise ++ obligationsOf subproofs
  | .deferred _ obligation => [obligation]

def obligationsOf : List (ProofTree Variable Literal Symbol Certificate) → List (Obligation Variable Literal Symbol)
  | [] => []
  | tree :: trees => tree.obligations ++ obligationsOf trees
end

mutual
/-- The references to delayed obligations in the tree, in preorder. -/
def refs : ProofTree Variable Literal Symbol Certificate → List (Hole Variable Literal Symbol)
  | .node _ _ _ subproofs => refsOf subproofs
  | .deferred id obligation => [(id, obligation)]

def refsOf : List (ProofTree Variable Literal Symbol Certificate) → List (Hole Variable Literal Symbol)
  | [] => []
  | tree :: trees => tree.refs ++ refsOf trees
end

theorem mem_refsOf {trees : List (ProofTree Variable Literal Symbol Certificate)} {ref : Hole Variable Literal Symbol} :
    ref ∈ refsOf trees ↔ ∃ tree ∈ trees, ref ∈ tree.refs := by
  induction trees with
  | nil => simp [refsOf]
  | cons tree trees ih => simp [refsOf, ih]

theorem refsOf_append (first second : List (ProofTree Variable Literal Symbol Certificate)) :
    refsOf (first ++ second) = refsOf first ++ refsOf second := by
  induction first with
  | nil => rfl
  | cons tree trees ih => simp [refsOf, ih, List.append_assoc]

theorem mem_obligationsOf {trees : List (ProofTree Variable Literal Symbol Certificate)}
    {obligation : Obligation Variable Literal Symbol} :
    obligation ∈ obligationsOf trees ↔ ∃ tree ∈ trees, obligation ∈ tree.obligations := by
  induction trees with
  | nil => simp [obligationsOf]
  | cons tree trees ih => simp [obligationsOf, ih]

/-- Every obligation the tree proves or requires names only names declared in
`store`. -/
def Declared [DecidableEq Variable] (store : Store Variable Literal Symbol)
    (tree : ProofTree Variable Literal Symbol Certificate) : Prop :=
  ∀ obligation ∈ tree.obligations, obligation.Declared store

theorem Declared.node [DecidableEq Variable] {store : Store Variable Literal Symbol}
    {rule : RuleApp Variable Literal Symbol Certificate} {obligation : Obligation Variable Literal Symbol}
    {premises : List (Premise Variable Literal Symbol)} {subproofs : List (ProofTree Variable Literal Symbol Certificate)}
    (declared : obligation.Declared store)
    (required : ∀ premise ∈ premises, (obligation.premise premise).Declared store)
    (children : ∀ tree ∈ subproofs, tree.Declared store) :
    (ProofTree.node rule obligation premises subproofs).Declared store := by
  intro other member
  simp only [obligations, List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
    mem_obligationsOf] at member
  rcases member with rfl | ⟨premise, inside, rfl⟩ | ⟨tree, inside, found⟩
  · exact declared
  · exact required premise inside
  · exact children tree inside other found

theorem Declared.deferred [DecidableEq Variable] {store : Store Variable Literal Symbol} {id : Nat}
    {obligation : Obligation Variable Literal Symbol} (declared : obligation.Declared store) :
    (ProofTree.deferred (Certificate := Certificate) id obligation).Declared store := by
  intro other member
  simp only [obligations, List.mem_singleton] at member
  subst member
  exact declared

theorem Declared.mono [DecidableEq Variable] {store later : Store Variable Literal Symbol}
    {tree : ProofTree Variable Literal Symbol Certificate} (declared : tree.Declared store)
    (grows : ∀ name, store.info? name ≠ none → later.info? name ≠ none) : tree.Declared later :=
  fun obligation member => (declared obligation member).mono grows

/-- A complete tree with no closed-world node does not depend on its run's
snapshot. For `Derives` rules its validity survives KB and registry growth
(`Derives.mono` with the disabled provider); an extension declared monotonic
needs that from its own soundness proof. A reference retains no evidence itself
and may stand for a proof that does, so a tree with references is never
monotonic. A successful run's tree has none (`CompletedProof.Valid`). -/
def Monotonic (tree : ProofTree Variable Literal Symbol Certificate) : Prop := tree.refs = [] ∧ tree.closedWorld = []

mutual
/-- Scope coherence: each subproof proves exactly the premise obligation built
from its parent's scope. Assumptions and rigid names a premise opens therefore
appear only inside that premise's subtree, and every premise has a subproof. A
reference stands for the obligation it names; its record proves it
(`DeferredProof.Valid`). -/
inductive Coherent : ProofTree Variable Literal Symbol Certificate → Prop where
  | node {rule : RuleApp Variable Literal Symbol Certificate} {obligation : Obligation Variable Literal Symbol}
      {premises : List (Premise Variable Literal Symbol)} {subproofs : List (ProofTree Variable Literal Symbol Certificate)}
      (children : CoherentPremises obligation premises subproofs) :
      Coherent (.node rule obligation premises subproofs)
  | deferred {id : Nat} {obligation : Obligation Variable Literal Symbol} : Coherent (.deferred id obligation)

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

/-- Every premise has a coherent subproof that proves it. -/
theorem CoherentPremises.exists_tree {parent : Obligation Variable Literal Symbol}
    {premises : List (Premise Variable Literal Symbol)} {trees : List (ProofTree Variable Literal Symbol Certificate)}
    (coherent : CoherentPremises parent premises trees) :
    ∀ premise ∈ premises, ∃ tree ∈ trees, tree.obligation = parent.premise premise ∧ tree.Coherent := by
  induction premises generalizing trees with
  | nil => intro _ member; cases member
  | cons first rest ih =>
      cases coherent with
      | cons opened valid tail =>
          intro premise member
          rcases List.mem_cons.mp member with rfl | later
          · exact ⟨_, List.mem_cons_self, opened, valid⟩
          · obtain ⟨tree, inside, proves, treeValid⟩ := ih tail premise later
            exact ⟨tree, List.mem_cons_of_mem _ inside, proves, treeValid⟩

end ProofTree

/-! ## Deferred proofs -/

/-- The proof of a woken suspension: its id, the obligation it delayed, and the
tree that proved it after waking. Its tree may reference later records. Deferred
proofs stay out of the store, which is the logical state the matcher reads and
commits to; the success step fills them into the completed tree. -/
structure DeferredProof (Variable Literal Symbol Certificate : Type) where
  id : Nat
  obligation : Obligation Variable Literal Symbol
  tree : ProofTree Variable Literal Symbol Certificate

def DeferredProof.hole (record : DeferredProof Variable Literal Symbol Certificate) : Hole Variable Literal Symbol :=
  (record.id, record.obligation)

/-- A record proves exactly the obligation it was recorded for, coherently, and
names only names declared in `store`. -/
structure DeferredProof.Valid [DecidableEq Variable] (store : Store Variable Literal Symbol)
    (record : DeferredProof Variable Literal Symbol Certificate) : Prop where
  obligation : record.tree.obligation = record.obligation
  coherent : record.tree.Coherent
  declared : record.tree.Declared store

theorem nodup_map_inj {α β : Type} {f : α → β} {items : List α} (distinct : (items.map f).Nodup)
    {first second : α} (firstMember : first ∈ items) (secondMember : second ∈ items) (same : f first = f second) :
    first = second := by
  have pairwise := List.pairwise_map.mp distinct
  exact List.Pairwise.forall_of_forall_of_flip (R := fun a b => f a = f b → a = b) (fun _ _ _ => rfl)
    (pairwise.imp fun differ equal => absurd equal differ) (pairwise.imp fun differ equal => absurd equal.symm differ)
    firstMember secondMember same

/-- With distinct ids, the record found for a hole's id is the record of that hole. -/
theorem DeferredProof.find_hole {records : List (DeferredProof Variable Literal Symbol Certificate)}
    (distinct : (records.map DeferredProof.id).Nodup) {id : Nat} {obligation : Obligation Variable Literal Symbol}
    (member : (id, obligation) ∈ records.map DeferredProof.hole) :
    ∃ record ∈ records, records.find? (·.id == id) = some record ∧ record.id = id ∧ record.obligation = obligation := by
  obtain ⟨found, foundMember, foundHole⟩ := List.mem_map.mp member
  simp only [DeferredProof.hole, Prod.mk.injEq] at foundHole
  cases findEq : records.find? (·.id == id) with
  | none => exact absurd foundHole.1 (by simpa using List.find?_eq_none.mp findEq found foundMember)
  | some record =>
      have recordMember := List.mem_of_find?_eq_some findEq
      have sameId : record.id = id := by simpa using List.find?_some findEq
      have same := nodup_map_inj distinct recordMember foundMember (sameId.trans foundHole.1.symm)
      exact ⟨record, recordMember, rfl, sameId, same ▸ foundHole.2⟩

namespace ProofTree

mutual
/-- Substitute the recorded proofs for the references, once. A substituted proof
may itself reference later records; `fillAll` repeats the pass. -/
def fill (records : List (DeferredProof Variable Literal Symbol Certificate)) :
    ProofTree Variable Literal Symbol Certificate → ProofTree Variable Literal Symbol Certificate
  | .node rule obligation premises subproofs => .node rule obligation premises (fillOf records subproofs)
  | .deferred id obligation =>
      match records.find? (·.id == id) with
      | some record => record.tree
      | none => .deferred id obligation

def fillOf (records : List (DeferredProof Variable Literal Symbol Certificate)) :
    List (ProofTree Variable Literal Symbol Certificate) → List (ProofTree Variable Literal Symbol Certificate)
  | [] => []
  | tree :: trees => tree.fill records :: fillOf records trees
end

def fillAll (records : List (DeferredProof Variable Literal Symbol Certificate)) :
    Nat → ProofTree Variable Literal Symbol Certificate → ProofTree Variable Literal Symbol Certificate
  | 0, tree => tree
  | count + 1, tree => fillAll records count (tree.fill records)

variable {records : List (DeferredProof Variable Literal Symbol Certificate)}

/-- Each record stands for exactly the obligation it was recorded for. -/
abbrev Resolved (records : List (DeferredProof Variable Literal Symbol Certificate))
    (refs : List (Hole Variable Literal Symbol)) : Prop :=
  ∀ ref ∈ refs, ref ∈ records.map DeferredProof.hole

theorem obligation_fill (distinct : (records.map DeferredProof.id).Nodup)
    (proves : ∀ record ∈ records, record.tree.obligation = record.obligation)
    {tree : ProofTree Variable Literal Symbol Certificate} (resolved : Resolved records tree.refs) :
    (tree.fill records).obligation = tree.obligation := by
  cases tree with
  | node => simp [fill, obligation]
  | deferred id obligation =>
      obtain ⟨record, member, found, _, sameObligation⟩ :=
        DeferredProof.find_hole distinct (resolved (id, obligation) (List.mem_singleton_self _))
      simp only [fill, found]
      exact (proves record member).trans sameObligation

mutual
theorem fill_coherent (distinct : (records.map DeferredProof.id).Nodup)
    (valid : ∀ record ∈ records, record.tree.obligation = record.obligation ∧ record.tree.Coherent) :
    ∀ tree : ProofTree Variable Literal Symbol Certificate, tree.Coherent → Resolved records tree.refs →
      (tree.fill records).Coherent
  | .node _ _ _ subproofs, coherent, resolved => by
      cases coherent with
      | node children => exact .node (fillOf_coherent distinct valid subproofs children resolved)
  | .deferred id obligation, _, resolved => by
      obtain ⟨record, member, found, _, _⟩ := DeferredProof.find_hole distinct (resolved (id, obligation) (List.mem_singleton_self _))
      simp only [fill, found]
      exact (valid record member).2

theorem fillOf_coherent (distinct : (records.map DeferredProof.id).Nodup)
    (valid : ∀ record ∈ records, record.tree.obligation = record.obligation ∧ record.tree.Coherent) :
    ∀ (trees : List (ProofTree Variable Literal Symbol Certificate)) {parent : Obligation Variable Literal Symbol}
      {premises : List (Premise Variable Literal Symbol)}, CoherentPremises parent premises trees →
      Resolved records (refsOf trees) → CoherentPremises parent premises (fillOf records trees)
  | [], _, _, children, _ => by cases children; exact .nil
  | tree :: trees, _, _, children, resolved => by
      cases children with
      | cons opened coherent rest =>
          have here : Resolved records tree.refs := fun ref inside => resolved ref (List.mem_append_left _ inside)
          exact .cons ((obligation_fill distinct (fun record member => (valid record member).1) here).trans opened)
            (fill_coherent distinct valid tree coherent here)
            (fillOf_coherent distinct valid trees rest fun ref inside => resolved ref (List.mem_append_right _ inside))
end

mutual
/-- A reference left after one pass comes from the substituted record of a
reference of the tree. -/
theorem refs_fill (distinct : (records.map DeferredProof.id).Nodup) : ∀ tree : ProofTree Variable Literal Symbol Certificate,
    Resolved records tree.refs →
    ∀ ref ∈ (tree.fill records).refs, ∃ record ∈ records, record.id ∈ tree.refs.map Prod.fst ∧ ref ∈ record.tree.refs
  | .node _ _ _ subproofs, resolved, ref, member => by
      simp only [fill, refs] at member resolved ⊢
      exact refsOf_fill distinct subproofs resolved ref member
  | .deferred id obligation, resolved, ref, member => by
      obtain ⟨record, recordMember, found, sameId, _⟩ :=
        DeferredProof.find_hole distinct (resolved (id, obligation) (List.mem_singleton_self _))
      simp only [fill, found] at member
      exact ⟨record, recordMember, by simp [refs, sameId], member⟩

theorem refsOf_fill (distinct : (records.map DeferredProof.id).Nodup) : ∀ trees : List (ProofTree Variable Literal Symbol Certificate),
    Resolved records (refsOf trees) →
    ∀ ref ∈ refsOf (fillOf records trees), ∃ record ∈ records,
      record.id ∈ (refsOf trees).map Prod.fst ∧ ref ∈ record.tree.refs
  | [], _, ref, member => by simp [fillOf, refsOf] at member
  | tree :: trees, resolved, ref, member => by
      simp only [fillOf, refsOf, List.mem_append] at member
      rcases member with here | there
      · obtain ⟨record, member, idMember, inside⟩ :=
          refs_fill distinct tree (fun ref inside => resolved ref (by simp [refsOf, inside])) ref here
        exact ⟨record, member, by simp only [refsOf, List.map_append, List.mem_append]; exact .inl idMember, inside⟩
      · obtain ⟨record, member, idMember, inside⟩ :=
          refsOf_fill distinct trees (fun ref inside => resolved ref (by simp [refsOf, inside])) ref there
        exact ⟨record, member, by simp only [refsOf, List.map_append, List.mem_append]; exact .inr idMember, inside⟩
end

mutual
theorem obligations_fill : ∀ tree : ProofTree Variable Literal Symbol Certificate,
    ∀ obligation ∈ (tree.fill records).obligations,
      obligation ∈ tree.obligations ∨ ∃ record ∈ records, obligation ∈ record.tree.obligations
  | .node _ _ premises subproofs, obligation, member => by
      simp only [fill, obligations, List.cons_append, List.mem_cons, List.mem_append] at member ⊢
      rcases member with here | inside | inside
      · exact .inl (.inl here)
      · exact .inl (.inr (.inl inside))
      · rcases obligationsOf_fill subproofs obligation inside with old | recorded
        · exact .inl (.inr (.inr old))
        · exact .inr recorded
  | .deferred id other, obligation, member => by
      simp only [fill] at member
      split at member
      · rename_i record findEq
        exact .inr ⟨record, List.mem_of_find?_eq_some findEq, member⟩
      · exact .inl member

theorem obligationsOf_fill : ∀ trees : List (ProofTree Variable Literal Symbol Certificate),
    ∀ obligation ∈ obligationsOf (fillOf records trees),
      obligation ∈ obligationsOf trees ∨ ∃ record ∈ records, obligation ∈ record.tree.obligations
  | [], _, member => by simp [fillOf, obligationsOf] at member
  | tree :: trees, obligation, member => by
      simp only [fillOf, obligationsOf, List.mem_append] at member ⊢
      rcases member with here | there
      · rcases obligations_fill tree obligation here with old | recorded
        · exact .inl (.inl old)
        · exact .inr recorded
      · rcases obligationsOf_fill trees obligation there with old | recorded
        · exact .inl (.inr old)
        · exact .inr recorded
end

/-- The number of records below an id. Every reference in a record points to a
later record, so this count grows along every chain of references. -/
def countBelow (records : List (DeferredProof Variable Literal Symbol Certificate)) (id : Nat) : Nat :=
  (records.filter (·.id < id)).length

theorem countBelow_lt {record : DeferredProof Variable Literal Symbol Certificate} (member : record ∈ records)
    {id : Nat} (lower : record.id < id) : countBelow records record.id < countBelow records id :=
  filter_length_lt (fun _ _ smaller => by simpa using Nat.lt_trans (by simpa using smaller) lower)
    ⟨record, member, by simpa using lower, by simp⟩

theorem countBelow_lt_length {record : DeferredProof Variable Literal Symbol Certificate} (member : record ∈ records) :
    countBelow records record.id < records.length :=
  List.length_filter_lt_length_iff_exists.mpr ⟨record, member, by simp⟩

/-- Filling preserves what the tree proves, its coherence, and its declared
names; after one pass per record no reference remains, since references in
records point only to later records. -/
theorem fillAll_valid [DecidableEq Variable] {store : Store Variable Literal Symbol}
    (distinct : (records.map DeferredProof.id).Nodup) (valid : ∀ record ∈ records, record.Valid store)
    (inner : ∀ record ∈ records, ∀ ref ∈ record.tree.refs, ref ∈ records.map DeferredProof.hole ∧ record.id < ref.1) :
    ∀ (count : Nat) (tree : ProofTree Variable Literal Symbol Certificate) (least : Nat), tree.Coherent →
      tree.Declared store → Resolved records tree.refs → (∀ ref ∈ tree.refs, least ≤ countBelow records ref.1) →
      (tree.fillAll records count).obligation = tree.obligation ∧ (tree.fillAll records count).Coherent ∧
        (tree.fillAll records count).Declared store ∧ Resolved records (tree.fillAll records count).refs ∧
        ∀ ref ∈ (tree.fillAll records count).refs, least + count ≤ countBelow records ref.1
  | 0, tree, least, coherent, declared, resolved, ranked => ⟨rfl, coherent, declared, resolved, ranked⟩
  | count + 1, tree, least, coherent, declared, resolved, ranked => by
      have origin := refs_fill distinct tree resolved
      have filledResolved : Resolved records (tree.fill records).refs := fun ref inside => by
        obtain ⟨record, member, _, there⟩ := origin ref inside
        exact (inner record member ref there).1
      have filledRanked : ∀ ref ∈ (tree.fill records).refs, least + 1 ≤ countBelow records ref.1 := by
        intro ref inside
        obtain ⟨record, member, idMember, there⟩ := origin ref inside
        obtain ⟨parent, parentMember, parentId⟩ := List.mem_map.mp idMember
        have parentRank := ranked parent parentMember
        rw [parentId] at parentRank
        exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt parentRank (countBelow_lt member (inner record member ref there).2))
      have filledDeclared : (tree.fill records).Declared store := fun obligation inside => by
        rcases obligations_fill tree obligation inside with old | ⟨record, member, recorded⟩
        · exact declared obligation old
        · exact (valid record member).declared obligation recorded
      obtain ⟨sameObligation, filledCoherent, rest⟩ := fillAll_valid distinct valid inner count (tree.fill records)
        (least + 1) (fill_coherent distinct (fun record member => ⟨(valid record member).obligation,
          (valid record member).coherent⟩) tree coherent resolved) filledDeclared filledResolved filledRanked
      refine ⟨sameObligation.trans (obligation_fill distinct (fun record member => (valid record member).obligation)
        resolved), filledCoherent, rest.1, rest.2.1, fun ref inside => ?_⟩
      have := rest.2.2 ref inside
      simp only [Nat.add_assoc, Nat.add_comm 1 count] at this
      exact this

/-- Fill at the end: with distinct record ids, valid records, and references that
resolve and point to later records, one pass per record leaves a tree that
proves the same obligation, coherently, names only declared names, and holds no
reference. -/
theorem fillAll_complete [DecidableEq Variable] {store : Store Variable Literal Symbol}
    (distinct : (records.map DeferredProof.id).Nodup) (valid : ∀ record ∈ records, record.Valid store)
    (inner : ∀ record ∈ records, ∀ ref ∈ record.tree.refs, ref ∈ records.map DeferredProof.hole ∧ record.id < ref.1)
    {tree : ProofTree Variable Literal Symbol Certificate} (coherent : tree.Coherent) (declared : tree.Declared store)
    (resolved : Resolved records tree.refs) :
    (tree.fillAll records records.length).obligation = tree.obligation ∧ (tree.fillAll records records.length).Coherent ∧
      (tree.fillAll records records.length).Declared store ∧ (tree.fillAll records records.length).refs = [] := by
  obtain ⟨sameObligation, filledCoherent, filledDeclared, filledResolved, ranked⟩ :=
    fillAll_valid distinct valid inner records.length tree 0 coherent declared resolved (fun _ _ => Nat.zero_le _)
  refine ⟨sameObligation, filledCoherent, filledDeclared, ?_⟩
  cases refsEq : (tree.fillAll records records.length).refs with
  | nil => rfl
  | cons ref _ =>
      have inside : ref ∈ (tree.fillAll records records.length).refs := by rw [refsEq]; exact List.mem_cons_self
      obtain ⟨record, member, sameHole⟩ := List.mem_map.mp (filledResolved ref inside)
      have rank := ranked ref inside
      rw [← sameHole, Nat.zero_add] at rank
      exact (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt rank (countBelow_lt_length member))).elim

end ProofTree

/-- A successful run: the complete tree for the root obligation, the deferred
proofs, the final store, and the snapshot the tree's closed-world certificates
are relative to. The success step has already substituted every deferred proof
for its reference, so the tree holds no reference. `deferred` is provenance:
each delayed obligation's proof under its id, as recorded when it woke, so a
record may still reference later records. The tree carries no ids, so it does
not say where each delayed proof sits. Answers are the root's flexible names
read through the store. -/
structure CompletedProof (Variable Literal Symbol Certificate Snapshot : Type) where
  snapshot : Snapshot
  root : Obligation Variable Literal Symbol
  tree : ProofTree Variable Literal Symbol Certificate
  deferred : List (DeferredProof Variable Literal Symbol Certificate)
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
