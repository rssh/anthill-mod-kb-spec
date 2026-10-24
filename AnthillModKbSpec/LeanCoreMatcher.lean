import Lean.Meta.Sym.Pattern
import AnthillModKbSpec.CoreMatcherCertificate

namespace AnthillModKbSpec.LeanCoreMatcher

open Lean Meta Sym
open CoreMatcherCertificate

/-- Run the native Miller-pattern solver on abstractions over fresh arguments.
P is created before the argument telescope, so it cannot capture those rigids.
Only new metavariables may be assigned, and all search state is restored.
This is a proposer, not a theorem about the model's syntax. -/
def solveAbstracted? (carrier : Expr) (arity : Nat)
    (target : Array Expr → MetaM Expr) : MetaM (Option Expr) := withoutModifyingState <| withNewMCtxDepth do
  let mut functionType := carrier
  for _ in [:arity] do
    functionType ← mkArrow carrier functionType
  let predicate ← mkFreshExprMVar (some functionType)
  forallTelescope functionType fun args _ => do
    let lhs ← mkLambdaFVars args (mkAppN predicate args)
    let rhs ← mkLambdaFVars args (← target args)
    let unified ← SymM.run do
      let lhs ← shareCommon lhs
      let rhs ← shareCommon rhs
      isDefEqS lhs rhs (mvarsToCheckType := #[predicate.mvarId!])
    unless unified do return none
    let answer ← instantiateMVars predicate
    if answer.hasExprMVar || answer.hasLevelMVar || answer.hasLooseBVars then return none
    return some answer

variable {Variable Literal Symbol : Type} [DecidableEq Variable] [DecidableEq Symbol]

/-- Adapt the supported unary head shape to actual Lean function application,
not quoted Term constructors. An opaque carrier and local symbol function keep
the model independent of typed domain definitions. Lambda answers are accepted
only when eta-reducible to the original symbol. Errors mean unsupported or
undecided, never certified failure of the logical query. -/
def proposeUnary? (ha : Symbol) (head query : Term Variable Literal Symbol) :
    MetaM (Except String (UnaryCandidate Variable Symbol)) :=
  match head, query with
  | .app h [.var _, .var _], .app f [.var a] => do
      unless h = ha && f != ha do return .error "unsupported head or target symbol"
      withLocalDeclD `Carrier (mkSort (.succ .zero)) fun carrier => do
        let functionType ← mkArrow carrier carrier
        withLocalDeclD `symbol functionType fun symbol => do
          let some answer ← solveAbstracted? carrier 1 (fun args => pure (mkApp symbol args[0]!))
            | return .error "native pattern solver did not produce a closed substitution"
          unless etaReduce answer == symbol do
            return .error "native predicate answer is not representable as a symbol value"
          withLocalDeclD `rigid carrier fun rigid => withoutModifyingState <| withNewMCtxDepth do
            let argument ← mkFreshExprMVar (some carrier)
            let unified ← SymM.run do
              let argument ← shareCommon argument
              let rigid ← shareCommon rigid
              isDefEqS argument rigid (mvarsToCheckType := #[argument.mvarId!])
            unless unified do return .error "native argument matching was undecided"
            unless (← instantiateMVars argument) == rigid do
              return .error "native argument answer is not the original rigid"
            return .ok ⟨f, a⟩
  | _, _ => pure (.error "unsupported shape: expected ho_apply(P,x) against f(a)")

/-- Native proposal followed by independent pure checking and body
instantiation. No native unification-success flag is accepted as a proof. -/
def expandUnary? (ha : Symbol) (rigids : List Variable) (head : Term Variable Literal Symbol)
    (body : List (Term Variable Literal Symbol)) (query : Term Variable Literal Symbol) :
    MetaM (Except String (MillerCertificates.Expansion ha rigids head body query)) := do
  match ← proposeUnary? ha head query with
  | .error reason => return .error reason
  | .ok candidate =>
      match CoreMatcherCertificate.expandUnary? ha rigids head body query candidate with
      | none => return .error "proposal rejected by the scope/capture certificate checker"
      | some certificate => return .ok certificate

end AnthillModKbSpec.LeanCoreMatcher
