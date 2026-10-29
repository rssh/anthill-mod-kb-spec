import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Machine

namespace MatchingTests

/-! Executable checks of S05: instantiation with alpha-renaming, freshening of
clause uses, the outcomes of matching against the store, and machine traces
with a matcher-driven test driver. `#guard` evaluates compiled code; the
theorems they illustrate hold for every input. -/

inductive Sym where
  | p | q | r | s | t | u | f | a | b | ha
  deriving DecidableEq, Repr

abbrev T := Term Nat Nat Sym

def k (symbol : Sym) : T := .app symbol []
def atom (symbol : Sym) (args : List T) : T := .app symbol args
def same (left right : T) : Bool := identical left right

/-! ### Instantiation renames instead of failing -/

-- ∀1. p(1, 2) with 2 := 1: `instantiate?` refuses the capture hazard;
-- `instantiate` renames the binder and keeps the substituted name free.
def capturing : T := .forallVar 1 (atom .p [.var 1, .var 2])
def renamedInstance : T := capturing.instantiate (Substitution.single 2 (.var 1))
#guard (capturing.instantiate? (Substitution.single 2 (.var 1))).isNone
#guard match renamedInstance with
  | .forallVar binder (.app .p [.var bound, .var free]) => binder != 1 && bound == binder && free == 1
  | _ => false

example : Substitutes (Substitution.single 2 (.var 1)) capturing renamedInstance :=
  capturing.instantiate_substitutes _

-- Without a hazard the binder is kept and both instantiations agree.
#guard match capturing.instantiate? (Substitution.single 2 (k .a)) with
  | some result => same result (capturing.instantiate (Substitution.single 2 (k .a)))
  | none => false

-- The nearest binder owns its occurrences.
#guard same ((Term.forallVar 2 (atom .p [.var 2]) : T).instantiate (Substitution.single 2 (k .a)))
  (.forallVar 2 (atom .p [.var 2]))

/-! ### Freshening a clause use -/

-- p(3) :- ∀5. r(5, 3). The clause instantiates 3; the binder 5 belongs to its
-- quantifier and is not a template name.
def ruleHead : T := atom .p [.var 3]
def ruleBody : List T := [.forallVar 5 (atom .r [.var 5, .var 3])]
#guard (HornClause.definite ruleHead ruleBody).templates == [3]

-- Avoiding 0, 1, 2, and 4, the fresh name for 3 is 5, the binder's own name:
-- the binder is renamed, and the fresh name stays free.
def freshened : List (Nat × Nat) := freshenNames [0, 1, 2, 4] [3]
#guard freshened == [(3, 5)]
#guard match (Term.conjunction ruleBody).instantiate (Substitution.rename freshened) with
  | .conj (.forallVar binder (.app .r [.var bound, .var free])) .truth =>
      binder != 5 && bound == binder && free == 5
  | _ => false

-- A captured name is kept.
#guard same ((atom .q [.var 3, .var 8] : T).instantiate (Substitution.rename freshened)) (atom .q [.var 5, .var 8])

-- The local rule ∀1. (q(1) → p(1, 7)) captures 7: only its explicit binder is
-- instantiated.
def localRule : T := .forallVar 1 (.imp (atom .q [.var 1]) (atom .p [.var 1, .var 7]))
#guard match localRule.instantiateLeading [.var 9] with
  | some (.imp (.app .q [.var 9]) (.app .p [.var 9, .var 7])) => true
  | _ => false
#guard (localRule.instantiateLeading [.var 9, .var 10]).isNone

example {kb : LogicalKb Nat Nat Sym} {opened : T} (computed : localRule.instantiateLeading [.var 9] = some opened)
    (proof : Derives Sym.ha kb [localRule] localRule) : Derives Sym.ha kb [localRule] opened :=
  Derives.instantiateLeading _ computed proof

/-! ### Matching outcomes -/

/-- Flexible 0 and 1 may take the rigid 5; flexible 2 depends on nothing. -/
def store₀ : Store Nat Nat Sym :=
  { names := [(0, .flexible [5]), (1, .flexible [5]), (2, .flexible []), (5, .rigid), (6, .rigid)], bindings := []
    wakeups := [], constraints := [] }
def scope₀ : Scope Nat Nat Sym := ⟨[5, 6], []⟩

def outcome : Unification Nat Nat Sym → String
  | .unified _ _ => "unified"
  | .mismatch => "mismatch"
  | .unsupported => "unsupported"
  | .violated => "violated"

def unify (left right : T) (store : Store Nat Nat Sym := store₀) (scope : Scope Nat Nat Sym := scope₀) :
    Unification Nat Nat Sym :=
  store.unify scope .ha left right

def reads (result : Unification Nat Nat Sym) (name : Nat) (expected : T) : Bool :=
  match result with
  | .unified final _ => same (final.resolve (.var name)) expected
  | _ => false

def after : Unification Nat Nat Sym → Option (Store Nat Nat Sym)
  | .unified final _ => some final
  | _ => none

-- Matching is two-sided, and answers propagate through earlier bindings.
#guard reads (unify (atom .p [.var 0, k .b]) (atom .p [k .a, .var 1])) 0 (k .a)
#guard reads (unify (atom .p [.var 0, k .b]) (atom .p [k .a, .var 1])) 1 (k .b)
#guard reads (unify (atom .p [.var 0, .var 0]) (atom .p [.var 1, atom .f [k .a]])) 0 (atom .f [k .a])

-- Mismatches: a clash, a clash after a binding, the occurs check, distinct
-- rigid names, arity. A binder against another constructor is a clash too.
#guard outcome (unify (atom .p [k .a]) (atom .p [k .b])) == "mismatch"
#guard outcome (unify (atom .p [.var 0, .var 0]) (atom .p [k .a, k .b])) == "mismatch"
#guard outcome (unify (.var 0) (atom .f [.var 0])) == "mismatch"
#guard outcome (unify (.var 5) (.var 6)) == "mismatch"
#guard outcome (unify (atom .p [k .a]) (atom .p [k .a, k .b])) == "mismatch"
#guard outcome (unify (.forallVar 7 (k .p)) (k .p)) == "mismatch"

-- Dependencies: 2 may not take the rigid 5; 0 may.
#guard outcome (unify (.var 2) (.var 5)) == "mismatch"
#guard outcome (unify (.var 0) (.var 5)) == "unified"

-- Aliases carry the scope. Binding 2 := 0 narrows 0 to 2's dependencies, so 0,
-- which could take 5 before, no longer can.
#guard match after (unify (.var 2) (.var 0)) with
  | some aliased =>
      aliased.info? 0 == some (.flexible []) && outcome (unify (.var 0) (.var 5) aliased) == "mismatch"
  | none => false
-- Binding 0 := 2 instead makes 0 read as 2, whose scope excludes 5.
#guard match after (unify (.var 0) (.var 2)) with
  | some aliased => reads (unify (.var 0) (.var 0) aliased) 0 (.var 2) &&
      outcome (unify (.var 0) (.var 5) aliased) == "mismatch"
  | none => false

-- Unsupported: alpha-variants, an operation call, ho_apply against an ordinary atom.
#guard outcome (unify (.forallVar 7 (atom .p [.var 7])) (.forallVar 8 (atom .p [.var 8]))) == "unsupported"
#guard outcome (unify (.dictionaryCall (k .a) [] .f [k .b]) (.lit 3)) == "unsupported"
#guard outcome (unify (atom .ha [.var 0, k .a]) (atom .p [k .a])) == "unsupported"

-- Admitted: identical binders, ho_apply against ho_apply, binding a name to a call.
#guard outcome (unify (.forallVar 7 (atom .p [.var 7])) (.forallVar 7 (atom .p [.var 7]))) == "unified"
#guard reads (unify (atom .ha [.var 0, k .a]) (atom .ha [k .q, k .a])) 0 (k .q)
#guard outcome (unify (.var 0) (.dictionaryCall (k .a) [] .f [k .b])) == "unified"

-- Violated: an undeclared name; a rigid name outside the scope; even when both
-- sides are identical.
#guard outcome (unify (atom .p [.var 9]) (atom .p [k .a])) == "violated"
#guard outcome (unify (.var 6) (k .a) store₀ ⟨[5], []⟩) == "violated"
#guard outcome (unify (atom .p [.var 9]) (atom .p [.var 9])) == "violated"

-- The bindings a match returns replay as a commit to the same answers.
#guard match unify (atom .p [.var 0, k .b]) (atom .p [k .a, .var 1]) with
  | .unified final bindings =>
      match store₀.bindAll scope₀ bindings with
      | .bound replayed =>
          same (replayed.resolve (atom .p [.var 0, .var 1])) (final.resolve (atom .p [.var 0, .var 1]))
      | _ => false
  | _ => false

/-! ### A matcher-driven test driver -/

abbrev E := Expansion Nat Nat Sym Unit
abbrev Program := List (T × List T)

/-- A match as a candidate: `some none` is a miss, `none` a gap. -/
def candidate (result : Unification Nat Nat Sym) (make : List (Nat × T) → E) : Option (Option E) :=
  match result with
  | .unified _ bindings => some (some (make bindings))
  | .mismatch => some none
  | .unsupported | .violated => none

def respond (found : List (Option (Option E))) (more : List E) : Response Nat Nat Sym Unit :=
  if found.any Option.isNone then .unsupported else .candidates ((found.filterMap id).filterMap id ++ more)

/-- Identity against the assumptions first. An atom also tries every universal
assumption with a fresh witness, and every clause freshened for this use; each
is matched against the store its commit prepares. New names avoid the read
binder names (`Store.readBinders`): the commit would accept them, but the
renamed binder would be an alpha-variant the matcher does not admit. This is a
test driver, not the S06 command set. -/
def driver (program : Program) : Command Nat Nat Sym Unit := fun obligation store =>
  let goal := store.resolve obligation.goal
  let scope := obligation.scope
  let identity := scope.assumptions.map fun assumption =>
    candidate (store.unify scope .ha obligation.goal assumption) fun bindings => Expansion.assumption bindings
  let instances := scope.assumptions.filterMap fun
    | .forallVar binder body =>
        let witness := store.freshFor (binder :: store.readBinders obligation)
        some (candidate ((store.prepare obligation [witness] []).unify scope .ha
            (body.instantiate (Substitution.single binder (.var witness))) obligation.goal)
          fun bindings => { Expansion.forallElim binder body (.var witness) with
            flexibles := [witness], bindings := bindings })
    | _ => none
  let clauses := program.map fun (head, body) =>
    let fresh := store.freshen (HornClause.definite head body).templates (store.readBinders obligation)
    candidate ((store.prepare obligation (fresh.map Prod.snd) []).unify scope .ha
        (head.instantiate (Substitution.rename fresh)) obligation.goal)
      fun bindings => Expansion.clause head body fresh bindings
  match goal with
  | .app _ _ => respond (identity ++ instances ++ clauses) []
  | .truth => respond identity [.truth]
  | .conj a b => respond identity [.conjIntro a b]
  | .disj a b => respond identity [.disjLeft a, .disjRight b]
  | .imp a b => respond identity [.impIntro a b]
  | .forallVar x body => respond identity [.forallIntro x body (store.freshFor (store.readBinders obligation))]
  | .existsVar x body => respond identity [.existsIntro x body (store.freshFor (store.readBinders obligation))]
  | .equal l r =>
      respond (identity ++ [candidate (store.unify scope .ha l r) fun bindings => { rule := .equalRefl, bindings }]) []
  | _ => .unsupported

def query (flexibles : List Nat) (context : List T) (goal : T) : State Nat Nat Sym Unit Nat :=
  State.init 0 flexibles context goal

def solve (program : Program) (state : State Nat Nat Sym Unit Nat) (fuel : Nat := 300) :
    Outcome Nat Nat Sym Unit Nat :=
  run (driver program) fuel state

def resume (program : Program) : Outcome Nat Nat Sym Unit Nat → Outcome Nat Nat Sym Unit Nat
  | .success _ state => solve program state
  | other => other

def rulesOf (outcome : Outcome Nat Nat Sym Unit Nat) : Option (List RuleId) :=
  outcome.proof?.map (·.tree.rules)

def answerIs (outcome : Outcome Nat Nat Sym Unit Nat) (name : Nat) (expected : T) : Bool :=
  match outcome.proof? with
  | some proof => same (proof.answer name) expected
  | none => false

mutual
/-- Clause applications in preorder, with their recorded renaming. -/
def clauseUses : ProofTree Nat Nat Sym Unit → List (HornClause Nat Nat Sym × List (Nat × T))
  | .node (.clause clause instantiation) _ _ subproofs => (clause, instantiation) :: clauseUsesOf subproofs
  | .node _ _ _ subproofs => clauseUsesOf subproofs
  | .deferred _ _ => []

def clauseUsesOf : List (ProofTree Nat Nat Sym Unit) → List (HornClause Nat Nat Sym × List (Nat × T))
  | [] => []
  | tree :: trees => clauseUses tree ++ clauseUsesOf trees
end

/-! ### Quantifier order -/

-- ∀x. ∃y. y = x: y is created under x, so it may take x.
def forallExists := solve [] (query [] [] (.forallVar 10 (.existsVar 11 (.equal (.var 11) (.var 10)))))
#guard forallExists.kind = .success
#guard rulesOf forallExists = some [.forallIntro, .existsIntro, .equalRefl]

-- ∃y. ∀x. y = x: y exists before x is opened; the match is a mismatch, so the
-- run is exhausted, not unknown.
def existsForall := solve [] (query [] [] (.existsVar 11 (.forallVar 10 (.equal (.var 11) (.var 10)))))
#guard existsForall.kind = .exhausted

-- ∃y. ∀x. ∃z. (y = z ∧ z = x): z may take x, but y = z makes z an alias of y,
-- which narrows z to y's scope; then z = x is refused.
def aliasEscape := solve [] (query [] []
  (.existsVar 11 (.forallVar 10 (.existsVar 12 (.conj (.equal (.var 11) (.var 12)) (.equal (.var 12) (.var 10)))))))
#guard aliasEscape.kind = .exhausted

-- Without the alias z takes x; with y inside x's scope the alias is harmless.
#guard (solve [] (query [] [] (.existsVar 11 (.forallVar 10 (.existsVar 12 (.equal (.var 12) (.var 10))))))).kind
  = .success
#guard (solve [] (query [] []
  (.forallVar 10 (.existsVar 11 (.existsVar 12 (.conj (.equal (.var 11) (.var 12)) (.equal (.var 12) (.var 10)))))))).kind
  = .success

/-! ### Rollback after a rejected candidate -/

-- (∀x. X = x) ∨ X = a: the first alternative needs X := x for an x opened after
-- X, which the dependency check rejects; the second alternative starts from the
-- restored store and answers a.
def scopeMiss := solve [] (query [0] [] (.disj (.forallVar 10 (.equal (.var 0) (.var 10))) (.equal (.var 0) (k .a))))
#guard scopeMiss.kind = .success
#guard answerIs scopeMiss 0 (k .a)
#guard rulesOf scopeMiss = some [.disjRight, .equalRefl]
#guard (resume [] scopeMiss).kind = .exhausted

-- A command that skips matching and proposes X := x directly: the store rejects
-- the commit, an ordinary miss with no gap, and the next alternative succeeds.
def naive : Command Nat Nat Sym Unit := fun obligation store =>
  match store.resolve obligation.goal with
  | .equal (.var name) value => .candidates [{ rule := .equalRefl, bindings := [(name, value)] }]
  | _ => driver [] obligation store

def rejected := run naive 100 (query [0] [] (.disj (.forallVar 10 (.equal (.var 0) (.var 10))) (.equal (.var 0) (k .a))))
#guard rejected.kind = .success
#guard match rejected.proof? with
  | some proof => same (proof.answer 0) (k .a)
  | none => false
#guard (match rejected with | .success _ state => run naive 100 state | other => other).kind = .exhausted

-- r(X) :- s(X) and r(X) :- t(X), under s(a), t(b), u(b), for r(Y) ∧ u(Y): the
-- first clause binds Y to a and fails at u(a); rollback restores the store
-- before that clause's fresh name and bindings, and the second clause answers b.
def rProgram : Program := [(atom .r [.var 50], [atom .s [.var 50]]), (atom .r [.var 50], [atom .t [.var 50]])]
def clauseRollback := solve rProgram
  (query [0] [atom .s [k .a], atom .t [k .b], atom .u [k .b]] (.conj (atom .r [.var 0]) (atom .u [.var 0])))
#guard clauseRollback.kind = .success
#guard answerIs clauseRollback 0 (k .b)
-- The clause's premise is its body conjunction t(X') ∧ true.
#guard rulesOf clauseRollback = some [.conjIntro, .clause, .conjIntro, .assumption, .truth, .assumption]
-- The proof keeps only the second clause; its renaming reads as b.
#guard match clauseRollback.proof? with
  | some proof =>
      match clauseUses proof.tree with
      | [(.definite _ [.app .t _], [(50, fresh)])] => same (proof.store.resolve fresh) (k .b)
      | _ => false
  | none => false
#guard (resume rProgram clauseRollback).kind = .exhausted

/-! ### Captured parameters -/

-- ∀1. p(1, C) captures the answer name C: instantiating the binder keeps C, so
-- matching p(a, b) answers C = b.
def capturedAnswer := solve [] (query [0] [.forallVar 1 (atom .p [.var 1, .var 0])] (atom .p [k .a, k .b]))
#guard capturedAnswer.kind = .success
#guard answerIs capturedAnswer 0 (k .b)
#guard rulesOf capturedAnswer = some [.forallElim, .assumption]

-- A captured rigid parameter is kept as itself and never renamed or bound.
#guard (solve [] (query [] [.forallVar 1 (atom .p [.var 1, .var 7])] (atom .p [k .a, .var 7]))).kind = .success
#guard (solve [] (query [] [.forallVar 1 (atom .p [.var 1, .var 7])] (atom .p [k .a, .var 8]))).kind = .exhausted

/-! ### Alpha-renaming while reading pending goals -/

-- p(X) ∧ ∀5. (r(5, X) → r(5, X)) under p(5), where 5 is also a parameter of the
-- query: after X := 5, reading the pending conjunct is a capture hazard. S04's
-- partial resolution refused it; reading now renames the binder.
def pendingGoal : T := .forallVar 5 (.imp (atom .r [.var 5, .var 0]) (atom .r [.var 5, .var 0]))
#guard (pendingGoal.instantiate? (Substitution.single 0 (.var 5))).isNone
def renamedReading := solve [] (query [0] [atom .p [.var 5]] (.conj (atom .p [.var 0]) pendingGoal))
#guard renamedReading.kind = .success
#guard answerIs renamedReading 0 (.var 5)
#guard rulesOf renamedReading = some [.conjIntro, .assumption, .forallIntro, .impIntro, .assumption]

-- Opening renames an inner binder that would capture the opened name: opening
-- ∀5. ∀6. r(5, 6, 1) with 6 gives ∀7. r(6, 7, 1), not ∀6. r(6, 6, 1).
#guard match (Expansion.forallIntro (Certificate := Unit) 5 (.forallVar 6 (atom .r [.var 5, .var 6, .var 1])) 6).premises with
  | [{ goal := .forallVar binder (.app .r [.var 6, .var bound, .var 1]), .. }] => binder != 6 && bound == binder
  | _ => false

-- p(0) ∧ ∀5. ∀1. r(5, 1, 0) under p(1) with r(X, X, Y): after 0 := 1 the pending
-- conjunct reads as ∀5. ∀6. r(5, 6, 1). No instance r(X, X, Y) applies, so the
-- run is exhausted, as for the alpha-variant with ∀9 and for an existential.
def rrProgram : Program := [(atom .r [.var 50, .var 50, .var 51], [])]
def nested (inner : Nat) (quantifier : Nat → T → T) : T :=
  .conj (atom .p [.var 0]) (quantifier 5 (.forallVar inner (atom .r [.var 5, .var inner, .var 0])))
#guard (solve rrProgram (query [0] [atom .p [.var 1]] (nested 1 .forallVar))).kind = .exhausted
#guard (solve rrProgram (query [0] [atom .p [.var 1]] (nested 9 .forallVar))).kind = .exhausted
#guard (solve rrProgram (query [0] [atom .p [.var 1]] (nested 1 .existsVar))).kind = .exhausted
#guard (solve rrProgram (query [0] [atom .p [.var 1]] (nested 9 .existsVar))).kind = .exhausted

/-! ### New names equal to binder names -/

/-- The inner binder of a quantifier's body, or the quantifier's own binder. -/
def binderOf (binder : Nat) : T → Nat
  | .forallVar inner _ | .existsVar inner _ => inner
  | _ => binder

/-- The driver, except that it opens every quantified goal with a binder name of
the goal as read (`binderOf`). The commit checks only store freshness, so these
names are accepted; the opening renames the inner binder that would capture. If
the name is already declared the focus is unsupported, so a trace that cannot
reuse a binder name is never mistaken for one that did. -/
def reuseBinders (program : Program) : Command Nat Nat Sym Unit := fun obligation store =>
  match store.resolve obligation.goal with
  | .forallVar x body =>
      if store.info? (binderOf x body) = none then .candidates [.forallIntro x body (binderOf x body)]
      else .unsupported
  | .existsVar x body =>
      if store.info? (binderOf x body) = none then .candidates [.existsIntro x body (binderOf x body)]
      else .unsupported
  | _ => driver program obligation store

-- ∀5. ∀6. (p(5, 6) → p(5, 6)) opened with 6, the inner binder, gives
-- ∀7. (p(6, 7) → p(6, 7)), then opened with 7, its own binder. S05 refused 6 as
-- a binder name of the obligation; it is a new name of the store.
def binderNames := run (reuseBinders []) 100
  (query [] [] (.forallVar 5 (.forallVar 6 (.imp (atom .p [.var 5, .var 6]) (atom .p [.var 5, .var 6])))))
#guard binderNames.kind = .success
#guard rulesOf binderNames = some [.forallIntro, .forallIntro, .impIntro, .assumption]

-- Store freshness alone may pick a binder name. For ∃2. (q(2) ∧ ∀1. p(1, 2))
-- under q(a) and ∀1. p(1, a), the empty store gives witness 1: the opening
-- renames the inner binder, ∀3. p(3, a) is an alpha-variant of the assumption,
-- and the matcher reports it unsupported. The driver avoids the read binder
-- names, picks 3, and the conjunct reads as the assumption itself.
def keepBindersQuery : State Nat Nat Sym Unit Nat :=
  query [] [atom .q [k .a], .forallVar 1 (atom .p [.var 1, k .a])]
    (.existsVar 2 (.conj (atom .q [.var 2]) (.forallVar 1 (atom .p [.var 1, .var 2]))))
def storeFreshOnly : Command Nat Nat Sym Unit := fun obligation store =>
  match store.resolve obligation.goal with
  | .existsVar x body => .candidates [.existsIntro x body store.freshFor]
  | _ => driver [] obligation store
#guard (run storeFreshOnly 100 keepBindersQuery).kind = .unknown
#guard (solve [] keepBindersQuery).kind = .success

-- The nested traces again, with the read inner binder chosen on purpose: the
-- conjunct ∀5. ∀6. r(5, 6, 1) is opened with 6 as ∀7. r(6, 7, 1), and the
-- existential's witness 6 likewise. Capture would give r(6, 6, 1), an instance.
#guard (run (reuseBinders rrProgram) 300 (query [0] [atom .p [.var 1]] (nested 1 .forallVar))).kind = .exhausted
#guard (run (reuseBinders rrProgram) 300 (query [0] [atom .p [.var 1]] (nested 9 .forallVar))).kind = .exhausted
#guard (run (reuseBinders rrProgram) 300 (query [0] [atom .p [.var 1]] (nested 1 .existsVar))).kind = .exhausted
#guard (run (reuseBinders rrProgram) 300 (query [0] [atom .p [.var 1]] (nested 9 .existsVar))).kind = .exhausted

/-! ### Undeclared names in premises -/

-- r(X) :- s(X, Z) used by a command that freshens only the head's names: the
-- body still names the template Z, which the store has not declared. The commit
-- refuses the candidate, a contract gap on r(Y) itself, before the body is
-- focused. Freshening every template name answers a.
def headOnly : Command Nat Nat Sym Unit := fun obligation store =>
  let head := atom .r [.var 50]
  let fresh := store.freshen head.freeVars
  match store.resolve obligation.goal,
      (store.prepare obligation (fresh.map Prod.snd) []).unify obligation.scope .ha
        (head.instantiate (Substitution.rename fresh)) obligation.goal with
  | .app .r _, .unified _ bindings => .candidates [Expansion.clause head [atom .s [.var 50, .var 60]] fresh bindings]
  | _, _ => driver [] obligation store

def unfreshened := run headOnly 50 (query [0] [atom .s [k .a, k .b]] (atom .r [.var 0]))
#guard match unfreshened with
  | .unknown [⟨.contract, obligation⟩] => same obligation.goal (atom .r [.var 0])
  | _ => false
def freshenedAll := solve [(atom .r [.var 50], [atom .s [.var 50, .var 60]])]
  (query [0] [atom .s [k .a, k .b]] (atom .r [.var 0]))
#guard freshenedAll.kind = .success
#guard answerIs freshenedAll 0 (k .a)

/-! ### Gaps and misses -/

-- Alpha-variant data needs a capability the profile lacks: a gap, not failure.
#guard (solve [] (query [] [atom .p [.forallVar 1 (atom .q [.var 1])]]
  (atom .p [.forallVar 2 (atom .q [.var 2])]))).kind = .unknown
-- A plain clash is a miss.
#guard (solve [] (query [] [atom .p [k .b]] (atom .p [k .a]))).kind = .exhausted

/-! ### Formal properties used by the traces -/

-- A matched assumption stays matched in every later store, so its node reads
-- as derivable there.
example {store final later : Store Nat Nat Sym} (valid : store.Scoped) {scope : Scope Nat Nat Sym}
    {goal assumption : T} {bindings : List (Nat × T)}
    (computed : store.unify scope .ha goal assumption = .unified final bindings)
    (refines : final.Refines later) (member : assumption ∈ scope.assumptions) {kb : LogicalKb Nat Nat Sym} :
    (Expansion.assumption (Certificate := Unit) bindings).SoundUnder Sym.ha kb NafFailure.disabled later
      ⟨scope, goal⟩ :=
  let ⟨_, _, _, matched⟩ := Store.unify_sound valid computed
  Expansion.assumption_soundUnder member (refines.resolve_eq matched)

-- A clause use read through any store is one clause instance.
example {kb : LogicalKb Nat Nat Sym} (member : HornClause.definite ruleHead ruleBody ∈ kb)
    {store : Store Nat Nat Sym} {scope : Scope Nat Nat Sym} {goal : T}
    (matched : store.resolve (ruleHead.instantiate (Substitution.rename freshened)) = store.resolve goal) :
    (Expansion.clause (Certificate := Unit) ruleHead ruleBody freshened).SoundUnder Sym.ha kb NafFailure.disabled
      store ⟨scope, goal⟩ :=
  Expansion.clause_soundUnder member matched

-- A rigid name a commit opens never occurs in the answer of an older name, in
-- any later scoped store.
example {store next later : Store Nat Nat Sym} (valid : store.Scoped) {obligation : Obligation Nat Nat Sym}
    {flexibles rigids : List Nat} {premises : List (Premise Nat Nat Sym)} {bindings : List (Nat × T)}
    {woken : List (Suspension Nat Nat Sym)}
    (committed : store.commit obligation flexibles rigids premises bindings = .committed next woken)
    (refines : next.Refines later) (laterScoped : later.Scoped) {opened : Nat} (member : opened ∈ rigids)
    {name : Nat} {dependencies : List Nat} (existing : store.info? name = some (.flexible dependencies)) :
    opened ∉ (later.resolve (.var name)).freeVars :=
  Store.commit_no_escape_resolved valid committed refines laterScoped member existing

-- The opening contracts' freshness comes from the commit, once: an eigenvariable
-- committed for forallIntro or existsElim is fresh for the read obligation and
-- for the read existential in every later scoped store.
example {store next later : Store Nat Nat Sym} (valid : store.Scoped) {scope : Scope Nat Nat Sym}
    {goal body : T} {binder eigen : Nat} (declared : (⟨scope, goal⟩ : Obligation Nat Nat Sym).Declared store)
    {woken : List (Suspension Nat Nat Sym)}
    (committed : store.commit ⟨scope, goal⟩ [] [eigen]
      (Expansion.forallIntro (Certificate := Unit) binder body eigen).premises [] = .committed next woken)
    (refines : next.Refines later) (laterScoped : later.Scoped)
    (read : later.resolve goal = later.resolve (.forallVar binder body)) {kb : LogicalKb Nat Nat Sym} :
    (Expansion.forallIntro (Certificate := Unit) binder body eigen).SoundUnder Sym.ha kb NafFailure.disabled
      later ⟨scope, goal⟩ :=
  Expansion.forallIntro_soundUnder read
    (Store.commit_fresh_resolved valid declared committed refines laterScoped (List.mem_singleton_self _)).1

example {store next later : Store Nat Nat Sym} (valid : store.Scoped) {scope : Scope Nat Nat Sym}
    {goal body : T} {binder eigen : Nat} (declared : (⟨scope, goal⟩ : Obligation Nat Nat Sym).Declared store)
    {woken : List (Suspension Nat Nat Sym)}
    (committed : store.commit ⟨scope, goal⟩ [] [eigen]
      (Expansion.existsElim (Certificate := Unit) binder body eigen goal).premises [] = .committed next woken)
    (refines : next.Refines later) (laterScoped : later.Scoped) {kb : LogicalKb Nat Nat Sym} :
    (Expansion.existsElim (Certificate := Unit) binder body eigen goal).SoundUnder Sym.ha kb NafFailure.disabled
      later ⟨scope, goal⟩ :=
  let fresh := Store.commit_fresh_resolved valid declared committed refines laterScoped (List.mem_singleton_self _)
  Expansion.existsElim_soundUnder fresh.1
    (fresh.2 { goal := .existsVar binder body } (by simp [Expansion.existsElim]) (by simp)).goal

-- On ordinary, well-scoped readings the only failure is a mismatch.
example (store : Store Nat Nat Sym) (scope : Scope Nat Nat Sym) {left right : T}
    (leftOrdinary : Ordinary Sym.ha (store.resolve left)) (rightOrdinary : Ordinary Sym.ha (store.resolve right))
    (usable : ∀ name ∈ (store.resolve left).freeVars ++ (store.resolve right).freeVars,
      store.usable scope name = true) :
    store.unify scope .ha left right ≠ .unsupported ∧ store.unify scope .ha left right ≠ .violated :=
  ⟨store.unify_supported leftOrdinary rightOrdinary, store.unify_wellScoped usable⟩

end MatchingTests
