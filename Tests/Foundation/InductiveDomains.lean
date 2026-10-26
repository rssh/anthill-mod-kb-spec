import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.InductiveDomains AnthillModKbSpec.Semantics

private inductive D where | nat | boolean | empty deriving DecidableEq
private abbrev V := Tree String
private def zero : V := .node "zero" []
private def succ (value : V) : V := .node "succ" [value]
private def yes : V := .node "yes" []
private def no : V := .node "no" []
private def rZero : Rule D String := ⟨.nat, "zero", []⟩
private def rSucc : Rule D String := ⟨.nat, "succ", [.nat]⟩
private def rYes : Rule D String := ⟨.boolean, "yes", []⟩
private def rNo : Rule D String := ⟨.boolean, "no", []⟩
private def sigma : Definitions D String := fun rule =>
  rule = rZero ∨ rule = rSucc ∨ rule = rYes ∨ rule = rNo

private theorem zeroMember : Member sigma .nat zero := by
  simpa [rZero, zero] using Member.construct (rule := rZero) (by simp [sigma])
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
private theorem succMember {value : V} (member : Member sigma .nat value) : Member sigma .nat (succ value) := by
  simpa [rSucc, succ] using Member.construct (rule := rSucc) (by simp [sigma])
    (fun _ => value) (fun i => by
      have same : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) i 0
      subst i
      exact member)
private theorem yesMember : Member sigma .boolean yes := by
  simpa [rYes, yes] using Member.construct (rule := rYes) (by simp [sigma])
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
private theorem noMember : Member sigma .boolean no := by
  simpa [rNo, no] using Member.construct (rule := rNo) (by simp [sigma])
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

private theorem nonemptyDomain {domain : D} {tree : V} (member : Member sigma domain tree) : domain ≠ .empty := by
  induction member with
  | construct declared children members ih =>
      rcases declared with rfl | rfl | rfl | rfl <;> decide

-- A property proved structurally, rather than by enumeration of Nat.
private inductive NatShape : V → Prop where
  | zero : NatShape zero
  | succ (ih : NatShape value) : NatShape (succ value)
private def invariant (domain : D) (tree : V) : Prop :=
  match domain with
  | .nat => NatShape tree
  | .boolean => tree = yes ∨ tree = no
  | .empty => False
private theorem shapeInduction : Induction sigma invariant := by
  constructor
  intro rule declared children members ih
  rcases declared with rfl | rfl | rfl | rfl
  all_goals dsimp only [rZero, rSucc, rYes, rNo] at children members ih ⊢
  · simpa [invariant, rZero, zero] using NatShape.zero
  · simpa [invariant, rSucc, succ] using NatShape.succ (ih 0)
  · simp [invariant, yes]
  · simp [invariant, no]

example : Holds sigma [.nat, .boolean] (fun tree => NatShape tree ∨ tree = yes ∨ tree = no) := by
  refine holds_by_induction (domains := [.nat, .boolean])
    (property := fun tree => NatShape tree ∨ tree = yes ∨ tree = no) shapeInduction ?_
  intro domain selected tree property
  simp at selected
  rcases selected with rfl | rfl
  · exact Or.inl property
  · exact Or.inr property

private def boolCover : Cover sigma .boolean := ⟨[yes, no], by
  intro tree selected; simp at selected
  rcases selected with rfl | rfl
  · exact yesMember
  · exact noMember, by
  intro tree member
  have property := member.induct shapeInduction
  simpa [invariant] using property⟩

-- The finite domain has an exhaustive cover. An incomplete sample does not.
example : Holds sigma [.boolean] (fun tree => tree = yes ∨ tree = no) := by
  let covers : ∀ domain ∈ [D.boolean], Cover sigma domain := fun domain selected => by
    simp only [List.mem_singleton] at selected; subst domain; exact boolCover
  refine holds_by_covers (domains := [D.boolean]) (property := fun tree => tree = yes ∨ tree = no) covers ?_
  intro domain selected tree member
  simp only [List.mem_singleton] at selected
  subst domain
  simpa [covers, boolCover] using member

example : ¬ (∀ tree, Member sigma .boolean tree → tree ∈ [yes]) := by
  intro complete
  have impossible := complete no noMember
  simp [yes, no] at impossible

-- Repeating a domain in a union is harmless; no disjointness is assumed.
example (property : V → Prop) : Holds sigma [.nat, .nat] property ↔ Holds sigma [.nat] property := by
  simp [Holds, InUnion]

example : Holds sigma [.empty] (fun _ => False) := by
  intro tree ⟨domain, selected, member⟩
  simp at selected; subst domain
  exact False.elim (nonemptyDomain member rfl)

example : Refutes sigma [.nat, .boolean] (fun tree => tree ≠ zero) :=
  .witness (by simp) zeroMember (fun property => property rfl)

example : ¬ Holds sigma [.nat, .boolean] (fun tree => tree ≠ zero) :=
  refutes_not_holds (.witness (by simp) zeroMember (fun property => property rfl))

-- A concrete compositional model. It identifies constructor denotations, while
-- the canonical domain trees above remain distinct. False is outside both
-- inhabited domains; thus a guarded universal is weaker than unrestricted forall.
private def symbolValue (symbol : String) : Bool := symbol != "isEmpty"
private def model : Model Nat String Bool "ho_apply" :=
  { Model.trueAtoms Nat String "ho_apply" with
    application := fun symbol args => symbolValue symbol && args.all id
    holds_hoApply := by
      intro predicate args
      simp [symbolValue, List.all_cons, Model.trueAtoms] }
private def membershipSymbol : D → String
  | .nat => "isNat"
  | .boolean => "isBool"
  | .empty => "isEmpty"

private theorem memberDenotesTrue {domain : D} {tree : V} (member : Member sigma domain tree) :
    denote model tree = true := by
  induction member with
  | construct declared children members ih =>
      rcases declared with rfl | rfl | rfl | rfl
      all_goals dsimp only [rZero, rSucc, rYes, rNo] at children members ih ⊢
      · simp [denote, model, symbolValue]
      · simpa [denote, rSucc, model, symbolValue] using ih 0
      · simp [denote, model, symbolValue]
      · simp [denote, model, symbolValue]

private theorem realizes : Realizes model sigma membershipSymbol := by
  intro domain value
  constructor
  · intro trueGuard
    cases domain with
    | nat =>
        have same : value = true := by simpa [model, Model.trueAtoms, membershipSymbol, symbolValue] using trueGuard
        exact ⟨zero, zeroMember, (memberDenotesTrue zeroMember).trans same.symm⟩
    | boolean =>
        have same : value = true := by simpa [model, Model.trueAtoms, membershipSymbol, symbolValue] using trueGuard
        exact ⟨yes, yesMember, (memberDenotesTrue yesMember).trans same.symm⟩
    | empty => simp [model, Model.trueAtoms, membershipSymbol, symbolValue] at trueGuard
  · intro ⟨tree, member, same⟩
    have trueValue : value = true := same.symm.trans (memberDenotesTrue member)
    have inhabited := nonemptyDomain member
    cases domain <;> simp_all [model, Model.trueAtoms, membershipSymbol, symbolValue]

private def universal : Universal D String Nat String := ⟨[.nat, .boolean], "x", .var "x"⟩

example : universal.toTerm membershipSymbol =
    .forallVar "x" (.imp
      (.disj (.app "isNat" [.var "x"]) (.disj (.app "isBool" [.var "x"]) .falsity)) (.var "x")) := rfl

example (environment : Environment String Bool) : model.Satisfies environment (universal.toTerm membershipSymbol) := by
  apply (universal.satisfies_iff model realizes environment).mpr
  intro tree ⟨domain, selected, member⟩
  change model.holds (model.eval (update environment "x" (denote model tree)) (.var "x"))
  simp only [Model.eval, update, ite_true]
  exact memberDenotesTrue member

private def falseUniversal : Universal D String Nat String := ⟨[.nat, .boolean], "x", .falsity⟩
private theorem falseCounterexample (environment : Environment String Bool) :
    Refutes sigma falseUniversal.domains (fun tree => model.Satisfies
      (update environment falseUniversal.binder (denote model tree)) falseUniversal.body) :=
  .witness (by simp [falseUniversal]) zeroMember (by
    simp only [falseUniversal, Model.Satisfies, Model.eval]
    exact model.holds_bottom)

private theorem complement : model.ComplementNAF := by
  intro value
  change (!value = true ↔ ¬value = true)
  cases value <;> decide

-- Sound NAF of a guarded forall comes from a member with a false property.
example (environment : Environment String Bool) :
    model.Satisfies environment (.defaultNeg (falseUniversal.toTerm membershipSymbol)) :=
  falseUniversal.naf_of_refutation model realizes complement environment (falseCounterexample environment)

private abbrev K := LogicalKb String Nat String
private def provider := InductiveDomains.failureEvidence sigma model membershipSymbol (∅ : K)
example : model.FailureAdequate (∅ : K) provider := failureAdequate model realizes complement _

example : Derives "ho_apply" (∅ : K) [] (.defaultNeg (falseUniversal.toTerm membershipSymbol)) provider := by
  apply Derives.defaultNegIntro
  · simp [Universal.toTerm, InductiveDomains.guard, falseUniversal, membershipSymbol, Term.freeVars]
  · exact ⟨rfl, rfl, falseUniversal, rfl, fun environment _ => falseCounterexample environment⟩

-- An empty domain cannot supply a counterexample, regardless of its property.
example (property : V → Prop) : ¬ Refutes sigma [.empty] property := by
  intro refuted
  cases refuted with
  | witness selected member _ =>
      simp only [List.mem_singleton] at selected
      subst_vars
      exact nonemptyDomain member rfl

example : ¬ Derives "ho_apply" (∅ : K) [] .falsity provider :=
  model.consistent (by intro clause member; cases member) (failureAdequate model realizes complement _)

-- The unified refutation provider accepts the existing guarded counterexample.
private theorem certifiedUniversalRefutation :
    CertifiedRefutation.Refutes model (∅ : K) [] (falseUniversal.toTerm membershipSymbol) :=
  .guarded realizes (fun environment _ => falseCounterexample environment)

example : Derives "ho_apply" (∅ : K) [] (.defaultNeg (falseUniversal.toTerm membershipSymbol))
    (CertifiedRefutation.failureEvidence model (∅ : K)) :=
  certifiedUniversalRefutation.toDerives (by
    simp [Universal.toTerm, InductiveDomains.guard, falseUniversal, membershipSymbol, Term.freeVars])

-- Guarded quantifiers can occur inside a recursively refuted implication.
example : CertifiedRefutation.Refutes model (∅ : K) []
    (.imp .truth (falseUniversal.toTerm membershipSymbol)) :=
  .imp (fun environment _ => by simpa only [Model.Satisfies, Model.eval] using model.holds_top)
    certifiedUniversalRefutation

-- The certified success judgment also consumes positive guarded-domain proofs.
private def certifiedProgram : ScopedSearch.Program String Nat String "ho_apply" := ⟨[], by simp⟩
private def certifiedScope : ScopedSearch.Context String Nat String "ho_apply" := ⟨[], [], by simp⟩
private theorem certifiedProgramModels : model.Models certifiedProgram.toKb := by
  intro clause member; change clause ∈ certifiedProgram.clauses at member
  simp [certifiedProgram] at member

private theorem guardedSuccess : CertifiedScopedSearch.Succeeds model certifiedProgram certifiedScope
    (universal.toTerm membershipSymbol) := by
  apply CertifiedScopedSearch.Succeeds.guarded realizes
  intro environment valid tree ⟨domain, selected, member⟩
  change model.holds (model.eval (update environment "x" (denote model tree)) (.var "x"))
  simp only [Model.eval, update, ite_true]
  exact memberDenotesTrue member

example (environment : Semantics.Environment String Bool) :
    model.Satisfies environment (universal.toTerm membershipSymbol) :=
  guardedSuccess.sound certifiedProgramModels complement environment (by intro assumption member; cases member)

example : CertifiedScopedSearch.Succeeds model certifiedProgram certifiedScope
    (.defaultNeg (falseUniversal.toTerm membershipSymbol)) := by
  apply CertifiedScopedSearch.Succeeds.defaultNeg
  · simp [Universal.toTerm, InductiveDomains.guard, falseUniversal, membershipSymbol, Term.freeVars]
  · have same : certifiedProgram.toKb = (∅ : K) := by
      apply LogicalKb.ext
      intro clause
      change clause ∈ ([] : List (HornClause String Nat String)) ↔ False
      simp
    rw [same]
    exact certifiedUniversalRefutation

-- Finite-domain success can enter the same judgment through an exhaustive cover.
private def finiteUniversal : Universal D String Nat String := ⟨[.boolean], "x", .truth⟩
example : CertifiedScopedSearch.Succeeds model certifiedProgram certifiedScope
    (finiteUniversal.toTerm membershipSymbol) := by
  apply CertifiedScopedSearch.Succeeds.guarded realizes
  intro environment valid
  let covers : ∀ domain ∈ [D.boolean], Cover sigma domain := fun domain selected => by
    simp only [List.mem_singleton] at selected; subst domain; exact boolCover
  apply holds_by_covers (domains := [D.boolean])
    (property := fun tree => model.Satisfies (update environment "x" (denote model tree)) .truth) covers
  intro domain selected tree member
  simpa only [Model.Satisfies, Model.eval] using model.holds_top

-- All-domain forall uses the complete finite catalog, including the empty
-- domain. Nat still has infinitely many canonical inhabitants.
private def family : FiniteFamily D String :=
  ⟨sigma, [.nat, .boolean, .empty], by intro domain; cases domain <;> simp⟩

private def allUniversal : Universal D String Nat String := family.forallAll "x" (.var "x")

example : allUniversal.toTerm membershipSymbol =
    .forallVar "x" (.imp
      (.disj (.app "isNat" [.var "x"])
        (.disj (.app "isBool" [.var "x"]) (.disj (.app "isEmpty" [.var "x"]) .falsity)))
      (.var "x")) := rfl

example : Holds family.definitions family.domains
    (fun tree => NatShape tree ∨ tree = yes ∨ tree = no) := by
  refine (family.holds_iff (fun tree => NatShape tree ∨ tree = yes ∨ tree = no)).mpr ?_
  intro ⟨tree, domain, member⟩
  have property := member.induct shapeInduction
  cases domain with
  | nat => exact Or.inl property
  | boolean => exact Or.inr property
  | empty => exact False.elim property

private theorem allSuccess : CertifiedScopedSearch.Succeeds model certifiedProgram certifiedScope
    (allUniversal.toTerm membershipSymbol) := by
  apply CertifiedScopedSearch.Succeeds.guarded realizes
  intro environment valid tree ⟨domain, selected, member⟩
  change model.holds (model.eval (update environment "x" (denote model tree)) (.var "x"))
  simp only [Model.eval, update, ite_true]
  exact memberDenotesTrue member

-- Extra carrier values cannot silently be included in data quantification.
example : ¬ family.Covers model := by
  intro covers
  obtain ⟨tree, same⟩ := covers false
  obtain ⟨domain, member⟩ := tree.property
  have impossible := (memberDenotesTrue member).symm.trans same
  cases impossible

example (environment : Environment String Bool) :
    ¬ model.Satisfies environment (.forallVar "x" (.var "x")) := by
  simp only [Model.Satisfies, Model.eval, model.holds_universal]
  intro proof
  have impossible := proof false
  simp [update, model, Model.trueAtoms] at impossible

-- Equivalence to raw forall explicitly requires coverage of the carrier.
example (other : Model Nat String Bool "ho_apply")
    (realization : Realizes other family.definitions membershipSymbol)
    (coverage : family.Covers other) (environment : Environment String Bool) :
    other.Satisfies environment (allUniversal.toTerm membershipSymbol) ↔
      other.Satisfies environment (.forallVar "x" (.var "x")) :=
  family.forallAll_iff_forall other realization coverage environment "x" (.var "x")

-- An explicit model-existence witness, not just conditional soundness: this
-- family and KB have a realized model in which every certified success is true
-- and falsity cannot be certified. This does not assert existence for every KB.
example : ∃ witness : Model Nat String Bool "ho_apply",
    Realizes witness family.definitions membershipSymbol ∧
    witness.Models certifiedProgram.toKb ∧ witness.ComplementNAF ∧
    CertifiedScopedSearch.Succeeds witness certifiedProgram certifiedScope (allUniversal.toTerm membershipSymbol) ∧
    (∀ goal, CertifiedScopedSearch.Succeeds witness certifiedProgram certifiedScope goal →
      ∀ environment, witness.Satisfies environment goal) ∧
    ¬ CertifiedScopedSearch.Succeeds witness certifiedProgram certifiedScope .falsity := by
  refine ⟨model, realizes, certifiedProgramModels, complement, allSuccess, ?_, ?_⟩
  · intro goal proof environment
    exact proof.sound certifiedProgramModels complement environment (by intro assumption member; cases member)
  · exact CertifiedScopedSearch.no_falsity certifiedProgramModels complement
