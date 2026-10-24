import AnthillModKbSpec.Substitution
import Init.Data.String.Length

namespace AnthillModKbSpec

/-- A lawful supply of fresh variable names. This is independent of search. -/
class FreshNames (Variable : Type) where
  fresh : List Variable → Variable
  fresh_not_mem : ∀ names, fresh names ∉ names

private def natBound : List Nat → Nat
  | [] => 0
  | n :: ns => max n (natBound ns)

private theorem le_natBound (member : n ∈ ns) : n ≤ natBound ns := by
  induction ns with
  | nil => simp at member
  | cons a ns ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

instance : FreshNames Nat where
  fresh names := natBound names + 1
  fresh_not_mem names member :=
    Nat.not_lt_of_ge (le_natBound member) (Nat.lt_succ_self (natBound names))

instance : FreshNames String where
  fresh names := String.ofList (List.replicate (natBound (names.map String.length) + 1) '_')
  fresh_not_mem names member := by
    have bound := le_natBound (ns := names.map String.length) (List.mem_map.mpr ⟨_, member, rfl⟩)
    simp only [String.length_ofList, List.length_replicate] at bound
    exact Nat.not_lt_of_ge bound (Nat.lt_succ_self _)

/-- Names introduced by binders, including binders nested in term arguments. -/
def Term.binderNames : Term Variable Literal Symbol → List Variable
  | .var _ | .lit _ | .truth | .falsity => []
  | .app _ args => args.flatMap Term.binderNames
  | .dictionaryCall dictionary _ _ args => dictionary.binderNames ++ args.flatMap Term.binderNames
  | .conj a b | .disj a b | .imp a b | .equal a b => a.binderNames ++ b.binderNames
  | .defaultNeg body => body.binderNames
  | .forallVar name body | .existsVar name body => name :: body.binderNames

/-- Open a binder by replacing its free occurrences. The caller must choose an
`eigen` absent from `binderNames`; `openFree_substitutes` establishes capture
avoidance under that condition. Inner binders of the same name shadow it. -/
def Term.openFree [DecidableEq Variable] (binder eigen : Variable) :
    Term Variable Literal Symbol → Term Variable Literal Symbol
  | .var name => if name = binder then .var eigen else .var name
  | .lit value => .lit value
  | .app symbol args => .app symbol (args.map (Term.openFree binder eigen))
  | .dictionaryCall dictionary path operation args =>
      .dictionaryCall (dictionary.openFree binder eigen) path operation
        (args.map (Term.openFree binder eigen))
  | .equal a b => .equal (a.openFree binder eigen) (b.openFree binder eigen)
  | .truth => .truth
  | .falsity => .falsity
  | .conj a b => .conj (a.openFree binder eigen) (b.openFree binder eigen)
  | .disj a b => .disj (a.openFree binder eigen) (b.openFree binder eigen)
  | .imp a b => .imp (a.openFree binder eigen) (b.openFree binder eigen)
  | .defaultNeg body => .defaultNeg (body.openFree binder eigen)
  | .forallVar name body =>
      .forallVar name (if name = binder then body else body.openFree binder eigen)
  | .existsVar name body =>
      .existsVar name (if name = binder then body else body.openFree binder eigen)

variable {Variable Literal Symbol : Type} [DecidableEq Variable]

private theorem bind_identity (name : Variable) :
    Substitution.bind (Term.var : Substitution Variable Literal Symbol) name (.var name) = Term.var := by
  funext candidate
  by_cases same : candidate = name <;> simp [Substitution.bind, same]

/-- Identity substitution, including scoped terms and application arguments. -/
theorem Substitutes.identity (term : Term Variable Literal Symbol) : Substitutes Term.var term term := by
  refine Term.rec
    (motive_1 := fun term => Substitutes Term.var term term)
    (motive_2 := fun args => SubstitutesList Term.var args args)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ term
  · intro name; exact .var
  · intro value; exact .lit
  · intro symbol args ih; exact .app ih
  · exact .truth
  · exact .falsity
  · intro a b left right; exact .conj left right
  · intro a b left right; exact .disj left right
  · intro a b left right; exact .imp left right
  · intro body ih; exact .defaultNeg ih
  · intro name body ih
    apply Substitutes.forallVar (renamed := name)
    · intro candidate member different; simpa [Term.freeVars] using Ne.symm different
    · simpa [bind_identity] using ih
  · intro name body ih
    apply Substitutes.existsVar (renamed := name)
    · intro candidate member different; simpa [Term.freeVars] using Ne.symm different
    · simpa [bind_identity] using ih
  · intro dictionary path operation args ihDictionary ihArgs
    exact .dictionaryCall ihDictionary ihArgs
  · intro a b left right; exact .equal left right
  · exact .nil
  · intro head tail first rest; exact .cons first rest

private theorem reset_single (binder : Variable) (eigen : Variable) :
    Substitution.bind (Substitution.single binder (.var eigen) : Substitution Variable Literal Symbol)
      binder (.var binder) = Term.var := by
  funext candidate
  by_cases same : candidate = binder <;>
    simp [Substitution.bind, Substitution.single, same]

private theorem preserve_single (binder eigen name : Variable) (different : name ≠ binder) :
    Substitution.bind (Substitution.single binder (.var eigen) : Substitution Variable Literal Symbol)
      name (.var name) = Substitution.single binder (.var eigen) := by
  funext candidate
  by_cases same : candidate = name
  · subst candidate; simp [Substitution.bind, Substitution.single, different]
  · simp [Substitution.bind, same]

private theorem binder_safe (binder eigen name : Variable) (fresh : eigen ≠ name)
    (candidate : Variable) (different : candidate ≠ name) :
    name ∉ ((Substitution.single binder (.var eigen) : Substitution Variable Literal Symbol) candidate).freeVars := by
  by_cases same : candidate = binder
  · subst candidate; simp [Substitution.single, Substitution.bind, Term.freeVars, fresh.symm]
  · simp [Substitution.single, Substitution.bind, Term.freeVars, same, different.symm]

/-- Opening is the existing capture-avoiding substitution relation. Choosing a
name absent from every nested binder permits a deterministic opening without
alpha-renaming; freshness for the surrounding sequent is checked by search. -/
theorem Term.openFree_substitutes (term : Term Variable Literal Symbol) :
    ∀ binder eigen, eigen ∉ term.binderNames →
      Substitutes (Substitution.single binder (.var eigen)) term (term.openFree binder eigen) := by
  refine Term.rec
    (motive_1 := fun term => ∀ binder eigen, eigen ∉ term.binderNames →
      Substitutes (Substitution.single binder (.var eigen)) term (term.openFree binder eigen))
    (motive_2 := fun args => ∀ binder eigen, eigen ∉ args.flatMap Term.binderNames →
      SubstitutesList (Substitution.single binder (.var eigen)) args (args.map (Term.openFree binder eigen)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ term
  · intro name binder eigen fresh
    simpa [Term.openFree, Substitution.single, Substitution.bind] using
      (Substitutes.var (σ := Substitution.single binder (.var eigen)) (name := name))
  · intro value binder eigen fresh; simpa [Term.openFree] using
      (Substitutes.lit (σ := Substitution.single binder (.var eigen)) (value := value))
  · intro symbol args ih binder eigen fresh
    simpa only [Term.openFree] using Substitutes.app (ih binder eigen (by simpa [Term.binderNames] using fresh))
  · intros; simpa [Term.openFree] using (Substitutes.truth (σ := Substitution.single _ (.var _)))
  · intros; simpa [Term.openFree] using (Substitutes.falsity (σ := Substitution.single _ (.var _)))
  · intro a b left right binder eigen fresh
    simp only [Term.binderNames, List.mem_append, not_or] at fresh
    simpa only [Term.openFree] using Substitutes.conj (left binder eigen fresh.1) (right binder eigen fresh.2)
  · intro a b left right binder eigen fresh
    simp only [Term.binderNames, List.mem_append, not_or] at fresh
    simpa only [Term.openFree] using Substitutes.disj (left binder eigen fresh.1) (right binder eigen fresh.2)
  · intro a b left right binder eigen fresh
    simp only [Term.binderNames, List.mem_append, not_or] at fresh
    simpa only [Term.openFree] using Substitutes.imp (left binder eigen fresh.1) (right binder eigen fresh.2)
  · intro body ih binder eigen fresh
    simpa only [Term.openFree] using Substitutes.defaultNeg (ih binder eigen (by simpa [Term.binderNames] using fresh))
  · intro name body ih binder eigen fresh
    simp only [Term.binderNames, List.mem_cons, not_or] at fresh
    by_cases shadow : name = binder
    · subst name
      simp only [Term.openFree]
      apply Substitutes.forallVar (renamed := binder)
      · intro candidate member different
        simp [Substitution.single, Substitution.bind, Term.freeVars, different, different.symm]
      · simpa [reset_single] using Substitutes.identity body
    · simp only [Term.openFree, ite_eq_right shadow]
      apply Substitutes.forallVar (renamed := name)
      · intro candidate member different; exact binder_safe binder eigen name fresh.1 candidate different
      · simpa [preserve_single binder eigen name shadow] using ih binder eigen fresh.2
  · intro name body ih binder eigen fresh
    simp only [Term.binderNames, List.mem_cons, not_or] at fresh
    by_cases shadow : name = binder
    · subst name
      simp only [Term.openFree]
      apply Substitutes.existsVar (renamed := binder)
      · intro candidate member different
        simp [Substitution.single, Substitution.bind, Term.freeVars, different, different.symm]
      · simpa [reset_single] using Substitutes.identity body
    · simp only [Term.openFree, ite_eq_right shadow]
      apply Substitutes.existsVar (renamed := name)
      · intro candidate member different; exact binder_safe binder eigen name fresh.1 candidate different
      · simpa [preserve_single binder eigen name shadow] using ih binder eigen fresh.2
  · intro dictionary path operation args ihDictionary ihArgs binder eigen fresh
    simp only [Term.binderNames, List.mem_append, not_or] at fresh
    simpa only [Term.openFree] using
      Substitutes.dictionaryCall (ihDictionary binder eigen fresh.1) (ihArgs binder eigen fresh.2)
  · intro a b left right binder eigen fresh
    simp only [Term.binderNames, List.mem_append, not_or] at fresh
    simpa only [Term.openFree] using
      Substitutes.equal (left binder eigen fresh.1) (right binder eigen fresh.2)
  · intro binder eigen fresh; exact .nil
  · intro head tail first rest binder eigen fresh
    simp only [List.flatMap_cons, List.mem_append, not_or] at fresh
    exact .cons (first binder eigen fresh.1) (rest binder eigen fresh.2)

end AnthillModKbSpec
