import AnthillModKbSpec.Foundation.InductiveDomain
import Lean

/-! Opt-in generation of exact constructor-domain presentations. The generated
definitions and proofs are ordinary Lean declarations checked by the kernel. -/
namespace AnthillModKbSpec.Deriving

open Lean Meta Elab Command
open InductiveDomains

private structure Constructor where
  name : Name
  result : Nat
  fields : Array Nat
  deriving Inhabited

private def qualified (name : Name) : String := "_root_." ++ (privateToUserName name).toString
private def join (items : List String) : String := String.intercalate ", " items
private def list (items : List String) : String := "[" ++ join items ++ "]"

/-- Inspect the finite closure of first-order, parameter-free constructor field
types. Unsupported declarations are rejected before emitting anything. -/
private def inspect (requested : Array Name) : CommandElabM (Array Name × Array Constructor) := do
  let mut types := requested
  let mut constructors := #[]
  let mut cursor := 0
  while cursor < types.size do
    let name := types[cursor]!
    let info ← getConstInfoInduct name
    unless info.numParams == 0 && info.numIndices == 0 && info.levelParams.isEmpty &&
        info.numNested == 0 && !info.isUnsafe && !info.isReflexive &&
        info.type == mkSort (.succ .zero) do
      throwError "InductiveDomain: {name} must be safe, parameter-free, non-indexed first-order data in Type; nested and function-valued recursion are unsupported"
    for other in info.all do
      unless types.contains other do types := types.push other
    for constructor in info.ctors do
      let ctor ← getConstInfoCtor constructor
      let fields ← liftTermElabM <| forallTelescopeReducing ctor.type fun args result => do
        unless result.isConstOf name do
          throwError "InductiveDomain: dependent constructor result in {constructor}"
        args.mapM fun arg => do
          let type ← whnf (← inferType arg)
          match type with
          | .const field [] => return field
          | _ => throwError "InductiveDomain: constructor {constructor} has an unsupported field type {type}; expected a parameter-free inductive data type"
      let mut indices := #[]
      for field in fields do
        unless types.contains field do types := types.push field
        indices := indices.push (types.idxOf field)
      constructors := constructors.push ⟨constructor, cursor, indices⟩
    cursor := cursor + 1
  return (types, constructors)

private def emit (source : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command source with
  | .error error => throwError "InductiveDomain generator syntax error: {error}\n{source}"
  | .ok command =>
    -- Parsed generated text has its own offsets, not offsets in the user's file.
    elabCommand (command.rewriteBottomUp (fun stx => stx.setInfo .none))

private def arguments (ctor : Constructor) : List String :=
  (List.range ctor.fields.size).map (fun i => s!"v{i}")

private def application (name : String) (args : List String) : String :=
  "(" ++ String.intercalate " " (name :: args) ++ ")"

private def encodedArguments (ctor : Constructor) : List String :=
  (List.range ctor.fields.size).map fun i => s!"(encode{ctor.fields[i]!} v{i})"

private def finFunction (values : List String) : String :=
  values.foldr (fun value rest => s!"(Fin.cases {value} {rest})") "(fun i => Fin.elim0 i)"

private def generate (requested : Array Name) : CommandElabM Unit := do
  let (types, constructors) ← inspect requested
  let root := requested[0]!
  let package := if isPrivateName root then
      (Name.str `AnthillModKbSpec.Generated root.toString).str "inductiveDomain"
    else root.str "inductiveDomain"
  if (← getEnv).contains (package.str "Domain") then
    throwError "InductiveDomain: presentation already exists for {requested[0]!}"
  emit s!"namespace {package}"
  emit "open AnthillModKbSpec.InductiveDomains"
  emit ("inductive Domain where\n" ++ String.join
    ((List.range types.size).map (fun i => s!"  | d{i}\n")) ++ "deriving DecidableEq, Repr")
  emit ("inductive Symbol where\n" ++ String.join
    ((List.range constructors.size).map (fun i => s!"  | c{i}\n")) ++ "deriving DecidableEq, Repr")
  for i in [:constructors.size] do
    let ctor := constructors[i]!
    emit s!"def rule{i} : Rule Domain Symbol := ⟨.d{ctor.result}, .c{i}, {list (ctor.fields.toList.map (fun d => s!".d{d}"))}⟩"
  let choices := (List.range constructors.size).map (fun i => s!"rule = rule{i}")
  emit ("def definitions : Definitions Domain Symbol := fun rule => " ++
    String.intercalate " ∨ " (choices ++ ["False"]))
  emit s!"def family : FiniteFamily Domain Symbol := ⟨definitions, {list ((List.range types.size).map (fun i => s!".d{i}"))}, by intro domain; cases domain <;> simp⟩"
  let mut encoders := #[]
  let mut proofs := #[]
  for d in [:types.size] do
    let ctors := (List.range constructors.size).filter (fun i => constructors[i]!.result == d)
    let mut equations := ""
    let mut memberEquations := ""
    for i in ctors do
      let ctor := constructors[i]!
      let pattern := application ("@" ++ qualified ctor.name) (arguments ctor)
      let children := list (encodedArguments ctor)
      equations := equations ++ s!"  | {pattern} => .node .c{i} {children}\n"
      let members := (List.range ctor.fields.size).map (fun f => s!"(member{ctor.fields[f]!} v{f})")
      memberEquations := memberEquations ++ s!"  | {pattern} => by\n    change Member definitions .d{d} (.node .c{i} {children})\n    simpa [rule{i}, List.ofFn_succ] using (Member.construct (rule := rule{i}) (by simp [definitions]) {finFunction (encodedArguments ctor)} {finFunction members})\n"
    let type := qualified types[d]!
    if ctors.isEmpty then
      encoders := encoders.push s!"def encode{d} (value : {type}) : Tree Symbol := nomatch value\n"
      proofs := proofs.push s!"theorem member{d} (value : {type}) : Member definitions .d{d} (encode{d} value) := nomatch value\n"
    else
      encoders := encoders.push s!"def encode{d} : {type} → Tree Symbol\n{equations}"
      proofs := proofs.push s!"theorem member{d} : ∀ value : {type}, Member definitions .d{d} (encode{d} value)\n{memberEquations}"
  emit ("mutual\n" ++ String.join encoders.toList ++ "end")
  emit ("mutual\n" ++ String.join proofs.toList ++ "end")
  emit ("def Value : Domain → Type\n" ++ String.join
    ((List.range types.size).map (fun i => s!"  | .d{i} => {qualified types[i]!}\n")))
  emit ("def encode : (domain : Domain) → Value domain → Tree Symbol\n" ++ String.join
    ((List.range types.size).map (fun i => s!"  | .d{i} => encode{i}\n")))
  let mut complete := "theorem complete {domain : Domain} {tree : Tree Symbol} (member : Member definitions domain tree) : ∃ value : Value domain, encode domain value = tree := by\n  induction member with\n  | construct declared children members ih =>\n    rcases declared with "
  complete := complete ++ String.intercalate " | "
    ((List.range constructors.size).map (fun _ => "rfl") ++ ["impossible"]) ++ "\n"
  for i in [:constructors.size] do
    let ctor := constructors[i]!
    complete := complete ++ s!"    · dsimp only [rule{i}] at children members ih ⊢\n"
    for f in [:ctor.fields.size] do
      complete := complete ++ s!"      obtain ⟨v{f}, h{f}⟩ := ih ⟨{f}, by decide⟩\n      change encode{ctor.fields[f]!} v{f} = children ⟨{f}, by decide⟩ at h{f}\n"
    complete := complete ++ s!"      refine ⟨{application ("@" ++ qualified ctor.name) (arguments ctor)}, ?_⟩\n      change Tree.node .c{i} {list (encodedArguments ctor)} = Tree.node .c{i} (List.ofFn children)\n      simp only [List.ofFn_succ, List.ofFn_zero{if ctor.fields.isEmpty then "" else ", " ++ join ((List.range ctor.fields.size).map (fun f => s!"h{f}"))}] <;> rfl\n"
  complete := complete ++ "    · exact False.elim impossible"
  if constructors.isEmpty then
    emit "theorem complete {domain : Domain} {tree : Tree Symbol} (member : Member definitions domain tree) : ∃ value : Value domain, encode domain value = tree := by\n  cases member with\n  | construct declared _ _ => exact False.elim declared"
  else
    emit complete
  for name in requested do
    let d := types.idxOf name
    emit s!"instance instance{d} : InductiveDomain {qualified name} where\n  Domain := Domain\n  Symbol := Symbol\n  family := family\n  root := .d{d}\n  encode := encode{d}\n  encode_member := member{d}\n  member_complete := fun _ member => complete member"
  emit s!"end {package}"

private def handler (names : Array Name) : CommandElabM Bool := do
  if names.isEmpty then return false
  withScope (fun scope => { scope with currNamespace := .anonymous }) (generate names)
  return true

initialize registerDerivingHandler ``InductiveDomain handler

end AnthillModKbSpec.Deriving
