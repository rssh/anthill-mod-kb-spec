import AnthillModKbSpec.Resolution.Miller
import AnthillModKbSpec.Foundation.LogicalKb

open AnthillModKbSpec

private abbrev TestTerm := Term String Nat String
private abbrev TestFormula := Formula String Nat String

example : TestTerm := .lit 0
example : TestTerm := .app "zero" []
example : HornClause String Nat String :=
  .definite (.app "p" [.app "succ" [.var "x"]]) []

private def p (args : List TestTerm) : TestFormula :=
  .hoApply "ho_apply" (.var "P") args

-- The same P is passed as data and applied; n scopes the IH and consequent.
def inductionRule : HornClause String Nat String :=
  .definite (.app "Nat.induction" [.var "P"])
    [p [.app "zero" []],
     .forallImpl ["n"] [p [.var "n"]] [p [.app "succ" [.var "n"]]]]

-- forall_impl is syntax for scoped implication, not a Lean execution function.
example : (Term.forallImpl ["x", "y"]
    [.app "a" [.var "x", .var "y"]] [.app "b" [.var "x"]] : TestTerm) =
    .forallVar "x" (.forallVar "y"
      (.imp (.conj (.app "a" [.var "x", .var "y"]) .truth)
        (.conj (.app "b" [.var "x"]) .truth))) := rfl

example : (Term.forallImpl [] [] [] : TestTerm) = .imp .truth .truth := rfl

-- Nested implications and scopes can occur inside an ordinary term argument.
def scopedArgument : TestTerm :=
  .app "store"
    [.forallVar "x"
      (.imp (.app "a" [.var "x"])
        (.forallVar "y"
          (.imp (.app "b" [.var "x", .var "y"])
            (.app "c" [.var "x", .var "y"]))))]

-- A scope on the left of an implication stays local to that premise.
example : TestFormula :=
  .imp (.forallVar "x" (.app "a" [.var "x"])) (.app "b" [.var "x"])

-- Free predicate unknowns must receive distinct bound variables.
example : (Term.forallVar "x" (.forallVar "y" (p [.var "y", .var "x"]))).IsMiller
    "ho_apply" := by
  simp [Term.IsMiller, Term.MillerHead, p, Term.hoApply,
    IsMillerArguments, Term.variableName?]

example : ¬ (Term.forallVar "x" (p [.var "x", .var "x"])).IsMiller "ho_apply" := by
  simp [Term.IsMiller, Term.MillerHead, p, Term.hoApply,
    IsMillerArguments, Term.variableName?]

example : ¬ (Term.forallVar "x" (p [.app "succ" [.var "x"]])).IsMiller "ho_apply" := by
  simp [Term.IsMiller, Term.MillerHead, p, Term.hoApply,
    IsMillerArguments, List.filterMap, Term.variableName?]

example : ¬ (p [.var "x"]).IsMiller "ho_apply" := by
  simp [Term.IsMiller, Term.MillerHead, p, Term.hoApply,
    IsMillerArguments, Term.variableName?]

example : (p []).IsMiller "ho_apply" := by
  simp [Term.IsMiller, Term.MillerHead, p, Term.hoApply, IsMillerArguments]

-- A shared binder binds P in predicate positions, including nested terms.
example : (Term.forallVar "P" (p [.lit 0])).IsMiller "ho_apply" := by
  simp [Term.IsMiller, Term.MillerHead, p, Term.hoApply]

example : (Term.existsVar "P" (p [.lit 0])).IsMiller "ho_apply" := by
  simp [Term.IsMiller, Term.MillerHead, p, Term.hoApply]

example : (Term.app "store" [.forallVar "P" (p [.lit 0])]).IsMiller "ho_apply" := by
  simp [Term.IsMiller, Term.MillerHead, p, Term.hoApply]

-- The check reaches inside arguments and respects lexical scope boundaries.
example : ¬ (Term.app "store" [p [.lit 0]]).IsMiller "ho_apply" := by
  simp [Term.IsMiller, Term.MillerHead, p, Term.hoApply,
    IsMillerArguments, List.filterMap, Term.variableName?]

example : ¬ (Term.imp (.forallVar "P" .truth) (p [.lit 0])).IsMiller "ho_apply" := by
  simp [Term.IsMiller, Term.MillerHead, p, Term.hoApply,
    IsMillerArguments, List.filterMap, Term.variableName?]

example : (Term.forallVar "P" (.imp (p [.lit 0])
    (.forallVar "n" (p [.app "succ" [.var "n"]])))).IsMiller "ho_apply" := by
  simp [Term.IsMiller, Term.MillerHead, p, Term.hoApply]

-- ∀P. (P(zero) ∧ ∀n. (P(n) → P(succ(n)))) → ∀n. P(n).
-- Representation of induction, not a proof of its validity.
def inductionFormula : TestFormula :=
  .forallVar "P"
    (.imp
      (.conj
        (p [.app "zero" []])
        (.forallVar "n" (.imp (p [.var "n"]) (p [.app "succ" [.var "n"]]))))
      (.forallVar "n" (p [.var "n"])))

example : inductionFormula.IsMiller "ho_apply" := by
  simp [inductionFormula, Term.IsMiller, Term.MillerHead, p, Term.hoApply]

example : (HornClause.definite (Variable := String) (Literal := Nat)
    (.app "induction" [.var "P"]) [p [.lit 0]]).toFormula =
    .imp (.conj (p [.lit 0]) .truth) (.app "induction" [.var "P"]) := rfl

example : (HornClause.goal (Variable := String) (Literal := Nat) (Symbol := String) []).toFormula =
    .imp .truth .falsity := rfl

-- Knowledge bases are sets: order and duplicate clauses do not matter.
private def zeroFact : HornClause String Nat String :=
  .definite (.app "Nat" [.app "zero" []]) []

private def natKb : LogicalKb String Nat String := {zeroFact, inductionRule}

example : zeroFact ∈ natKb := by simp [natKb]
example : inductionRule ∈ natKb := by simp [natKb]

example : (insert zeroFact natKb) = natKb := by
  apply LogicalKb.ext
  intro clause
  simp [natKb]

example : natKb = ({inductionRule, zeroFact} : LogicalKb String Nat String) := by
  apply LogicalKb.ext
  intro clause
  simp [natKb, or_comm]

example : ¬ zeroFact ∈ (∅ : LogicalKb String Nat String) := by simp

-- Negation as failure has its own syntax and may occur in a clause body.
example : HornClause String Nat String :=
  .definite (.app "available" [.var "x"])
    [.defaultNeg (.app "blocked" [.var "x"])]

-- Clause translation preserves default negation, without turning it into P → ⊥.
example : (HornClause.definite (Variable := String) (Literal := Nat)
    (.app "available" [.var "x"]) [.defaultNeg (.app "blocked" [.var "x"])]).toFormula =
    .imp (.conj (.defaultNeg (.app "blocked" [.var "x"])) .truth)
      (.app "available" [.var "x"]) := rfl

-- The optional argument check traverses default negation with the same scope.
example : (Term.forallVar "x" (.defaultNeg (p [.var "x"]))).IsMiller "ho_apply" := by
  simp [Term.IsMiller, Term.MillerHead, p, Term.hoApply,
    IsMillerArguments, Term.variableName?]

example : ¬ (Term.forallVar "x" (.defaultNeg (p [.var "x", .var "x"]))).IsMiller
    "ho_apply" := by
  simp [Term.IsMiller, Term.MillerHead, p, Term.hoApply,
    IsMillerArguments, Term.variableName?]
