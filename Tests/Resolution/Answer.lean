import AnthillModKbSpec

open AnthillModKbSpec AnthillModKbSpec.Machine AnthillModKbSpec.P1 AnthillModKbSpec.Completion
  AnthillModKbSpec.Answers AnthillModKbSpec.AdmissionSignature AnthillModKbSpec.InductiveDomains

namespace AnswerTests

/-! Executable traces of S22: the module's answers Yes, No, Unknown, and
Undecided(blockers) over the completion, the logical Unknown with its two
checked witnesses, and the combination rule. Each `#guard` evaluates compiled
code. -/

attribute [local instance] termEq clauseEq

inductive Sym where
  | p | q | r | o | a | b | unknown | ha
  | isUnit | allData | isPred (arity : Nat)
  | tag (tag : Tag)
  deriving DecidableEq, Repr

def vocab : Vocabulary Sym := ⟨Sym.tag, fun _ _ same => by cases same; rfl⟩

abbrev T := Term Nat Nat Sym
abbrev Clause := HornClause Nat Nat Sym

def k (symbol : Sym) : T := .app symbol []
def atom (symbol : Sym) (args : List T) : T := .app symbol args
def fact (head : T) : Clause := .definite head []
def naf (goal : T) : T := .defaultNeg goal

/-- The data constants are free constructors; `unknown` is the unknown marker. -/
def free (symbol : Sym) : Bool := [Sym.a, .b].contains symbol
def unknownMarker (symbol : Sym) : Bool := symbol == .unknown

/-- The admission signature: one domain without constructors, no registered
predicate. Its guard symbols `isUnit`, `allData`, and `isPred n` have one role
each, so the witnesses' models realize it. -/
def family : FiniteFamily Unit Sym := ⟨fun _ => False, [()], fun domain => by cases domain; simp⟩
def admission : SignatureSnapshot Unit Sym := ⟨0, ⟨family, fun _ => .isUnit, .allData, .isPred, []⟩⟩

def isGuard : Sym → Bool
  | .isUnit | .allData | .isPred _ => true
  | _ => false

theorem isGuard_iff (symbol : Sym) : isGuard symbol = true ↔ Open.IsGuard admission.naming symbol := by
  cases symbol <;> simp [isGuard, Open.IsGuard, admission, SignatureSnapshot.naming, Signature.naming]

theorem separated : Open.Separated admission.naming Sym.ha where
  membership _ _ _ := rfl
  predicate _ _ same := by cases same; rfl
  dataMembership _ same := by cases same
  predicateMembership _ _ same := by cases same
  predicateData _ same := by cases same
  hoApply := by simp [Open.IsGuard, admission, SignatureSnapshot.naming, Signature.naming]

/-- The module over the completion of `clauses`, closing the query's predicates. -/
def setupOf (clauses : List Clause) (formulas : List T) (fuel : Nat := 2000) : Option (Setup Unit Nat Nat Sym) :=
  match Setup.ofComplete? vocab .ha unknownMarker free admission isGuard isGuard_iff separated clauses formulas fuel 200 with
  | .ok setup => some setup
  | .error _ => none

def answerOf (clauses : List Clause) (goal : T) (fuel : Nat := 2000) : Option (ModuleAnswer Nat Nat Sym) :=
  (setupOf clauses [goal] fuel).map (·.answer [] goal)

def fastOf (clauses : List Clause) (goal : T) : Option OutcomeKind :=
  (setupOf clauses [goal]).map fun setup => (setup.run true [] goal).kind

def kindOf : Option (ModuleAnswer Nat Nat Sym) → String
  | some (.yes _) => "yes"
  | some (.no _) => "no"
  | some (.unknown _ _) => "unknown"
  | some (.undecided _) => "undecided"
  | none => "invalid"

/-- The open atoms an Undecided answer names as missing witnesses. -/
def missingWitnesses : Option (ModuleAnswer Nat Nat Sym) → List T
  | some (.undecided blockers) => blockers.flatMap fun
      | ⟨_, _, _, .witnesses atoms⟩ => atoms
      | _ => []
  | _ => []

def missingKinds : Option (ModuleAnswer Nat Nat Sym) → List String
  | some (.undecided blockers) => blockers.map fun blocker => match blocker.missing with
      | .proof => "proof" | .mode => "mode" | .termination => "termination"
      | .construct _ => "construct" | .witnesses _ => "witnesses"
  | _ => []

/-! ### Unknown: an open predicate, two witnesses, no refutation -/

-- q(a) :- unknown keeps q(a) open: the marker atom `unknown` is the open atom.
def openQ : List Clause := [.definite (atom .q [k .a]) [k .unknown]]

-- The fast run reports the NAF as opened: the marked case is syntax, and no
-- refutation is searched for it.
#guard fastOf openQ (naf (atom .q [k .a])) = some .opened
-- Unknown, with the two witnesses: unknown false makes naf q(a) true, and
-- unknown true makes it false.
#guard match answerOf openQ (naf (atom .q [k .a])) with
  | some (.unknown holds fails) => holds.isEmpty && identicalArgs fails [k .unknown]
  | _ => false
-- The positive goal: q(a) holds when unknown does.
#guard match answerOf openQ (atom .q [k .a]) with
  | some (.unknown holds fails) => identicalArgs holds [k .unknown] && fails.isEmpty
  | _ => false
-- The witnesses check: each is a model of the completion with the expected value.
#guard Open.check .ha isGuard unknownMarker openQ (naf (atom .q [k .a])) [] true
#guard Open.check .ha isGuard unknownMarker openQ (naf (atom .q [k .a])) [k .unknown] false
#guard !Open.check .ha isGuard unknownMarker openQ (naf (atom .q [k .a])) [k .unknown] true
-- An atom of another predicate is no open atom: a candidate must be a marker atom.
#guard !Open.check .ha isGuard unknownMarker openQ (naf (atom .q [k .a])) [atom .q [k .a]] false
-- The witnesses' models realize the admission signature: they interpret the
-- guards exactly, and the program and goal mention none. A goal that mentions
-- a guard symbol is outside the check: Undecided, not Unknown.
#guard !Open.check .ha isGuard unknownMarker openQ (.conj (naf (atom .q [k .a])) (naf (atom .isUnit [k .a]))) [] true
#guard kindOf (answerOf openQ (.conj (naf (atom .q [k .a])) (naf (atom .isUnit [k .a])))) = "undecided"

-- A marker with arguments keeps atoms apart: q(a) open, q(b) refuted by its
-- completion's clash of b with a.
def openQa : List Clause := [.definite (atom .q [k .a]) [atom .unknown [k .a]]]
#guard kindOf (answerOf openQa (naf (atom .q [k .b]))) = "yes"
#guard kindOf (answerOf openQa (naf (atom .q [k .a]))) = "unknown"

-- Every open atom the goal reaches is assigned, also those the run did not
-- visit after the first open conjunct: both all true, then all false.
def twoOpen : List Clause := [.definite (k .q) [atom .unknown [k .a], atom .unknown [k .b]]]
#guard match answerOf twoOpen (k .q) with
  | some (.unknown holds fails) => holds.length == 2 && fails.isEmpty
  | _ => false
#guard kindOf (answerOf [] (.conj (atom .unknown [k .a]) (atom .unknown [k .b]))) = "unknown"
-- A marker atom as a NAF operand, or nested in a body, is open too.
#guard fastOf [] (naf (k .unknown)) = some .opened
#guard kindOf (answerOf [] (naf (k .unknown))) = "unknown"
#guard kindOf (answerOf [.definite (atom .q [k .a]) [naf (k .unknown)]] (atom .q [k .a])) = "unknown"
#guard fastOf [.definite (atom .q [k .a]) [.disj (k .unknown) (atom .r [k .a])]] (naf (atom .q [k .a])) = some .opened
-- An open atom reached through another predicate: q :- r, r :- unknown.
def throughR : List Clause := [.definite (k .q) [k .r], .definite (k .r) [k .unknown]]
#guard fastOf throughR (naf (k .q)) = some .opened
#guard kindOf (answerOf throughR (naf (k .q))) = "unknown"
-- A defined operation may equal any value: o is no declared constructor, so
-- p(b) :- unknown may cover p(o(a)).
#guard fastOf [.definite (atom .p [k .b]) [k .unknown]] (naf (atom .p [atom .o [k .a]])) = some .opened

/-! ### The full run recovers refutations the fast run deferred -/

-- The fast run defers naf q(a), whose case reaches unknown, and leaves an
-- unsupported gap beside it; the full run refutes q(a) through r(a), which
-- has no clauses.
def deferred : List Clause := [.definite (atom .q [k .a]) [k .unknown, atom .r [k .a]], fact (atom .p [k .a])]
def deferredGoal : T := .disj (.forallVar 1 (naf (atom .p [.var 1]))) (naf (atom .q [k .a]))
#guard fastOf deferred deferredGoal = some .abandoned
#guard kindOf (answerOf deferred deferredGoal) = "yes"
-- A non-linear head is matched argument by argument: q(X, X) :- unknown may
-- seem to cover q(a, b); the full run refutes it by the clash of a and b.
#guard fastOf [.definite (atom .q [.var 0, .var 0]) [k .unknown]] (naf (atom .q [k .a, k .b])) = some .opened
#guard kindOf (answerOf [.definite (atom .q [.var 0, .var 0]) [k .unknown]] (naf (atom .q [k .a, k .b]))) = "yes"

/-! ### Undecided, not Unknown -/

-- p(a) ∨ ¬p(a) with p open: true under both assignments, so no witness makes
-- it false. Undecided, naming the open atom, never Unknown.
def openP : List Clause := [.definite (atom .p [k .a]) [k .unknown]]
def excluded : T := .disj (atom .p [k .a]) (naf (atom .p [k .a]))
#guard fastOf openP excluded = some .opened
#guard kindOf (answerOf openP excluded) = "undecided"
#guard (missingWitnesses (answerOf openP excluded)).any (identical · (k .unknown))

-- A non-ground open predicate is outside the witness check: Undecided, naming
-- the open atom (S24 extends the witnesses).
def openQx : List Clause := [.definite (atom .q [.var 0]) [k .unknown]]
#guard fastOf openQx (naf (atom .q [k .a])) = some .opened
#guard kindOf (answerOf openQx (naf (atom .q [k .a]))) = "undecided"
#guard (missingWitnesses (answerOf openQx (naf (atom .q [k .a])))).any (identical · (k .unknown))

/-! ### A denial forces an open atom: the forced value, not Unknown -/

-- With the denial false :- q(a), unknown is false in every model of the
-- completion. The witness making q(a) true violates the denial, so there is no
-- Unknown; the full run refutes q(a) by the denial.
def forced : List Clause := openQ ++ [.goal [atom .q [k .a]]]
#guard !Open.check .ha isGuard unknownMarker forced (naf (atom .q [k .a])) [k .unknown] false
#guard kindOf (answerOf forced (naf (atom .q [k .a]))) = "yes"
#guard kindOf (answerOf forced (atom .q [k .a])) = "no"

/-! ### No: a refuted conjunct decides an open conjunction -/

-- o(a) is open, r(b) has no clauses: the conjunction is false in every model.
def openO : List Clause := [.definite (atom .o [k .a]) [k .unknown]]
def openAndRefuted : T := .conj (atom .o [k .a]) (atom .r [k .b])
#guard fastOf openO openAndRefuted = some .opened
#guard kindOf (answerOf openO openAndRefuted) = "no"

/-! ### Yes, No, and operational outcomes -/

#guard kindOf (answerOf [fact (atom .p [k .a])] (atom .p [k .a])) = "yes"
#guard kindOf (answerOf [fact (atom .p [k .a])] (atom .p [k .b])) = "no"
#guard kindOf (answerOf [fact (atom .p [k .a])] (naf (atom .p [k .b]))) = "yes"
-- Fuel runs out: Undecided, lacking a termination argument, never Unknown.
#guard kindOf (answerOf [fact (atom .p [k .a])] (atom .p [k .a]) 1) = "undecided"
#guard missingKinds (answerOf [fact (atom .p [k .a])] (atom .p [k .a]) 1) = ["termination"]
-- A guarded universal over an unbounded recursion: the search finds no proof
-- or refutation, so the goal lacks a proof.
def recursive : List Clause := [.definite (atom .p [atom .q [.var 0]]) [atom .p [.var 0]]]
#guard kindOf (answerOf recursive (.forallVar 1 (atom .p [.var 1]))) = "undecided"
-- A clause concluding the marker is invalid: no answer.
#guard kindOf (answerOf (openQ ++ [fact (k .unknown)]) (atom .q [k .a])) = "invalid"

/-! ### Blockers keep their scope and provenance -/

/-- The blockers at obligations a run reached, with their contexts and trails. -/
def reached : Option (ModuleAnswer Nat Nat Sym) → List (List T × List (Origin Nat Nat Sym) × T)
  | some (.undecided blockers) => blockers.filterMap fun
      | ⟨.reached context trail, _, formula, _⟩ => some (context, trail, formula)
      | _ => none
  | _ => []

-- naf p(x) at a rigid x, with the fact p(a), is a gap inside the body of
-- q :- r, ∀x. naf p(x): the blocker names the clause and the premise position
-- along its trail.
def nested : Clause := .definite (k .q) [k .r, .forallVar 1 (naf (atom .p [.var 1]))]
def nestedKb : List Clause := [nested, fact (atom .p [k .a]), fact (k .r)]
#guard kindOf (answerOf nestedKb (k .q)) = "undecided"
#guard (reached (answerOf nestedKb (k .q))).any fun (_, trail, formula) =>
  trail.any (fun origin => origin.rule == .clause && decide (origin.clause = some nested)) &&
    match formula with
    | .defaultNeg (.app .p [_]) => true
    | _ => false
-- Two gaps with the same formula are told apart by their trails and contexts:
-- under the hypothesis r, the gap's context holds r. (Without the fact r, the
-- completion refutes r, and the implication is Yes.)
def hypothetical : T := .imp (k .r) (.forallVar 1 (naf (atom .p [.var 1])))
#guard kindOf (answerOf [fact (atom .p [k .a])] hypothetical) = "yes"
#guard (reached (answerOf [fact (atom .p [k .a]), fact (k .r)] hypothetical)).any fun (context, trail, _) =>
  context.any (identical · (k .r)) && trail.any (·.rule == .impIntro)
-- A fuel interruption keeps the query's context.
#guard match answerOf [fact (atom .p [k .a])] (atom .p [k .a]) 1 with
  | some (.undecided [⟨.reached [] [], [], _, .termination⟩]) => true
  | _ => false

/-! ### The combination rule -/

abbrev A := Answer Nat Nat Nat Nat

def shape : A → String
  | .yes proof => s!"yes {proof}"
  | .no refutation => s!"no {refutation}"
  | .unknown holds fails => s!"unknown {holds} {fails}"
  | .undecided blockers => s!"undecided {blockers}"

-- A definite Yes or No wins, the first when both are definite.
#guard shape (((.yes 1 : A)).combine (.no 2)) = "yes 1"
#guard shape (((.undecided [3] : A)).combine (.no 2)) = "no 2"
#guard shape (((.unknown 4 5 : A)).combine (.yes 1)) = "yes 1"
-- Otherwise a remaining blocker gives Undecided, also beside an Unknown.
#guard shape (((.unknown 4 5 : A)).combine (.undecided [3])) = "undecided [3]"
#guard shape (((.undecided [3] : A)).combine (.unknown 4 5)) = "undecided [3]"
#guard shape (((.undecided [3] : A)).combine (.undecided [6])) = "undecided [3, 6]"
-- Unknown only when no blocker remains; Undecided with no blocker is no result.
#guard shape (((.unknown 4 5 : A)).combine (.unknown 6 7)) = "unknown 4 5"
#guard shape (((.unknown 4 5 : A)).combine (.undecided [])) = "unknown 4 5"
#guard shape (((.undecided [] : A)).combine (.unknown 4 5)) = "unknown 4 5"
#guard shape (Answer.combineAll ([] : List A)) = "undecided []"
#guard shape (Answer.combineAll [(.undecided [] : A), .unknown 4 5, .undecided []]) = "unknown 4 5"
-- Supplying a checked proof or refutation turns Undecided into Yes or No.
#guard shape (((.undecided [3] : A)).supplyProof (· == 8) 8) = "yes 8"
#guard shape (((.undecided [3] : A)).supplyProof (· == 8) 9) = "undecided [3]"
#guard shape (((.undecided [3] : A)).supplyRefutation (· == 8) 8) = "no 8"

end AnswerTests
