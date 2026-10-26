import AnthillModKbSpec.Archive

open AnthillModKbSpec AnthillModKbSpec.Semantics AnthillModKbSpec.InductiveDomains
open AnthillModKbSpec.Archive.InductionGoals AnthillModKbSpec.Archive.InductiveResolution
open AnthillModKbSpec.InductionModel

private def scheme : Scheme family := ⟨[zeroRule, succRule], by intro rule; simp [family, sigma]⟩
private def predicates : Domain → T := fun _ => .app .reachable []
private def nafBase : HornClause String Unit Symbol := .definite (reachable zero) [.defaultNeg .falsity]
private def program : Archive.InductiveResolution.Program family String Unit := ⟨{nafBase, reachableSucc, natZero, natSucc}, some scheme⟩
private abbrev Proof (context : ProofContext String Unit Symbol) (goal : Goal Domain String Unit Symbol) :=
  Proves model program membershipSymbol context goal

private theorem programModels : model.Models program.clauses := by
  intro clause member environment
  simp only [program, LogicalKb.mem_insert, LogicalKb.mem_singleton] at member
  rcases member with rfl | rfl | rfl | rfl
  · simp only [nafBase, HornClause.toFormula, reachable, zero, Model.Satisfies, Model.eval, List.map_cons, List.map_nil, model.holds_implication]
    intro _
    exact (application_reachable _).mpr ⟨0, application_zero⟩
  · exact reachableSucc_valid environment
  · exact natZero_valid environment
  · exact natSucc_valid environment

private def interpretation : InductiveSoundness.Interpretation family program.clauses Value .hoApply :=
  ⟨model, membershipSymbol, realizes, programModels, complement⟩

example : Nonempty (InductiveSoundness.Interpretation family program.clauses Value .hoApply) := ⟨interpretation⟩

-- Goal expansion is executable and returns two obligations, not a success bit.
example : (program.inductionGoals (hoApplySymbol := Symbol.hoApply) membershipSymbol predicates).map List.length = some 2 := rfl

example : (⟨program.clauses, none⟩ : Archive.InductiveResolution.Program family String Unit).inductionGoals
    (hoApplySymbol := Symbol.hoApply) membershipSymbol predicates = none := rfl

-- The end-to-end proof below does not rely on the old generic ho_apply clause.
example : inductionRule ∉ program.clauses := by
  simp [program, inductionRule, nafBase, reachableSucc, natZero, natSucc, applyP,
    Term.hoApply, reachable, isNat]

-- Constructor obligations are generated as syntax, with fresh field binders.
example : constructorGoal (hoApplySymbol := Symbol.hoApply) family membershipSymbol predicates zeroRule =
    .imp .truth (applyP (.app .reachable []) zero) := rfl

private theorem succGoal : constructorGoal (hoApplySymbol := Symbol.hoApply) family membershipSymbol predicates succRule =
    .forallVar "_" (.imp (.conj (.conj (isNat (.var "_")) (applyP (.app .reachable []) (.var "_"))) .truth)
      (applyP (.app .reachable []) (succ (.var "_")))) := by
  have freshString : FreshNames.fresh ([] : List String) = "_" := rfl
  simp [constructorGoal, arguments, premises, conclusion, predicates, family, succRule,
    freshList, membershipSymbol, isNat, applyP, succ, Term.freeVars, Term.conjunction, freshString]

-- The zero case invokes a KB clause whose body is discharged by a NAF
-- certificate. This is inside induction, not an externally assumed invariant.
private theorem baseCase (context : ProofContext String Unit Symbol) :
    Proof context (.formula (constructorGoal (hoApplySymbol := Symbol.hoApply) family membershipSymbol predicates zeroRule)) := by
  apply Proves.impIntro
  apply Proves.hoApplyIntro
  apply Proves.clause (head := reachable zero) (body := [.defaultNeg .falsity]) (substitution := Term.var)
    (instantiatedBody := .conj (.defaultNeg .falsity) .truth)
  · simp [program, nafBase]
  · exact Substitutes.identity _
  · exact Substitutes.identity _
  · exact .conj (.defaultNeg (by simp [Term.freeVars]) .falsity) .truth

-- The successor case opens a rigid field parameter. The recursive call is
-- answered by its scoped IH; clause substitution never binds the rigid field.
private theorem stepCase (context : ProofContext String Unit Symbol) (fresh : FreshForContext "_" context) :
    Proof context (.formula (constructorGoal (hoApplySymbol := Symbol.hoApply) family membershipSymbol predicates succRule)) := by
  rw [succGoal]
  apply Proves.generalize (binder := "_") (fresh := fresh)
  apply Proves.impIntro
  apply Proves.hoApplyIntro
  apply Proves.clause (head := reachable (succ (.var "x"))) (body := [reachable (.var "x")])
    (substitution := fun _ => .var "_") (instantiatedBody := .conj (reachable (.var "_")) .truth)
  · simp [program, reachableSucc]
  · exact .app (.cons (.app (.cons .var .nil)) .nil)
  · exact .conj (.app (.cons .var .nil)) .truth
  · exact .conj (.hoApplyElim (.conjRight (a := isNat (.var "_")) (.conjLeft (b := .truth) (.assumption (by simp [applyP]))))) .truth

private theorem certificate (context : ProofContext String Unit Symbol) (fresh : FreshForContext "_" context) :
    Proof context (.inductiveProof predicates) := by
  apply Proves.induction (scheme := scheme) rfl predicates
  intro rule member
  simp only [scheme, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact baseCase context
  · exact stepCase context fresh

-- End-to-end proof: open rigid x, assume Nat(x), generate constructor goals,
-- prove them using search and NAF, then apply the certificate at rigid x.
private theorem allNaturals : Proof [] (.formula
    (.forallVar "x" (.imp (isNat (.var "x")) (reachable (.var "x"))))) := by
  apply Proves.generalize (binder := "x") (fresh := by intro assumption member; cases member)
  apply Proves.impIntro
  apply Proves.hoApplyElim
  apply Proves.inductionApply (domain := Domain.nat) (predicates := predicates)
  · exact certificate _ (by simp [FreshForContext, isNat, Term.freeVars])
  · exact .assumption (by simp [membershipSymbol, isNat])

example (environment : Environment String Value) : model.Satisfies environment
    (.forallVar "x" (.imp (isNat (.var "x")) (reachable (.var "x")))) :=
  Archive.ExplicitInduction.sound interpretation rfl allNaturals environment (by intro assumption member; cases member)

-- The D_all guard is a disjunction. Its singleton-domain case is discharged
-- logically; it is not treated as an atomic assumption in a fact table.
private theorem allData : Proof [] (.formula
    ((family.forallAll "x" (reachable (.var "x"))).toTerm membershipSymbol)) := by
  apply Proves.generalize (binder := "x") (fresh := by intro assumption member; cases member)
  apply Proves.impIntro
  apply Proves.hoApplyElim
  apply Proves.inductionApply (domain := Domain.nat) (predicates := predicates)
  · exact certificate _ (by simp [FreshForContext, InductiveDomains.guard, FiniteFamily.forallAll, family, membershipSymbol, Term.freeVars])
  · apply Proves.declarative
    apply Derives.disjElim (a := isNat (.var "x")) (b := .falsity)
      (.assumption (by simp [InductiveDomains.guard, FiniteFamily.forallAll, family, membershipSymbol, isNat]))
    · exact .assumption (by simp [isNat, membershipSymbol])
    · exact .falsityElim (.assumption (by simp))

example (environment : Environment String Value) : model.Satisfies environment
    ((family.forallAll "x" (reachable (.var "x"))).toTerm membershipSymbol) :=
  Archive.ExplicitInduction.sound interpretation rfl allData environment (by intro assumption member; cases member)

example : ¬ Proof [] (.formula .falsity) := Archive.ExplicitInduction.consistent interpretation rfl

-- A search proof that used induction can participate in a later NAF certificate.
example : Proof [] (.formula (.defaultNeg (.imp
    (.forallVar "x" (.imp (isNat (.var "x")) (reachable (.var "x")))) .falsity))) :=
  .defaultNeg (by simp [isNat, reachable, Term.freeVars])
    (.imp (allNaturals.established programModels realizes complement) .falsity)

-- Induction is an explicit KB declaration, rather than an always-enabled
-- fallback. Dropping it makes the special certificate goal unavailable.
example (context : ProofContext String Unit Symbol) : ¬ Proves model (⟨program.clauses, none⟩ : Archive.InductiveResolution.Program family String Unit)
    membershipSymbol context (.inductiveProof predicates) := by
  intro proof
  cases proof with
  | induction declared predicates cases => cases declared

-- An incomplete constructor catalog cannot authorize an induction scheme.
example : ¬ (∀ rule, sigma rule ↔ rule ∈ [zeroRule]) := by
  intro exactness
  have missing := (exactness succRule).mp (Or.inr rfl)
  simp [succRule, zeroRule] at missing

-- The extended soundness theorem also excludes false induction certificates.
example : ¬ Proof [] (.inductiveProof (fun _ => .app .even [])) := by
  intro proof
  have correct := Archive.ExplicitInduction.sound interpretation rfl proof (fun _ => model.inhabitant)
    (by intro assumption member; cases member)
  have one := correct .nat (natTree 1) (natTree_member 1)
  simp only [interpretation, Model.eval, List.map_nil] at one
  have truth : model.holds (model.application .even [natValue 1]) := by
    apply (model.holds_hoApply .even [natValue 1]).mp
    simpa only [Model.eval, List.map_nil, natTree_denote] using one
  exact (by decide : ¬ 1 % 2 = 0) ((even_at_nat 1).mp truth)

-- Fresh argument generation avoids every free predicate parameter, and is
-- injective even for constructors with several fields in the same domain.
example (predicate : T) (rule : Rule Domain Symbol) :
    Function.Injective (arguments family (fun _ => predicate) rule).names :=
  (arguments family (fun _ => predicate) rule).distinct

example (rule : Rule Domain Symbol) (i : Fin rule.fields.length) :
    (arguments family (fun _ => (.var "P" : T)) rule).names i ≠ "P" := by
  intro same
  exact (arguments family (fun _ => (.var "P" : T)) rule).fresh .nat i (by simp [same, Term.freeVars])
