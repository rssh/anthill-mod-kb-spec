/-! # The multiset order (S24)

The measure a tabled run decreases holds one weight per branch of the search,
and a step replaces one branch by any number of smaller ones: consuming a
table's answers makes one alternative per answer, however many there are. The
multiset order of Dershowitz and Manna compares such collections. Multisets
are lists up to permutation here:

- `Replace r smaller larger`: one element of `larger` replaced by any number
  of elements `r`-below it.
- `Lower r`: one or more replacements. For a well-founded `r` it is
  well-founded (`Lower.wellFounded`).

The construction lemmas (`Lower.replace`, `Lower.erase`, `Lower.append_left`,
`Lower.append_right`, `Lower.sublist`) build the steps the machine and the
run take. -/

namespace AnthillModKbSpec.Tabled

variable {α : Type} {r : α → α → Prop}

/-- One element of `larger` replaced by the elements `added`, each `r`-below
it, up to permutation. -/
def Replace (r : α → α → Prop) (smaller larger : List α) : Prop :=
  ∃ a rest added, larger.Perm (a :: rest) ∧ smaller.Perm (added ++ rest) ∧ ∀ b ∈ added, r b a

/-- The multiset order: one or more replacements. -/
def Lower (r : α → α → Prop) : List α → List α → Prop := Relation.TransGen (Replace r)

theorem Replace.perm_left {smaller other larger : List α} (replace : Replace r smaller larger) (same : smaller.Perm other) :
    Replace r other larger := by
  obtain ⟨a, rest, added, larger', smaller', below⟩ := replace
  exact ⟨a, rest, added, larger', same.symm.trans smaller', below⟩

theorem Replace.perm_right {smaller larger other : List α} (replace : Replace r smaller larger) (same : larger.Perm other) :
    Replace r smaller other := by
  obtain ⟨a, rest, added, larger', smaller', below⟩ := replace
  exact ⟨a, rest, added, same.symm.trans larger', smaller', below⟩

/-! ## Well-foundedness -/

section WellFounded

/-- Accessibility is invariant under permutation. -/
theorem acc_perm {M M' : List α} (acc : Acc (Replace r) M) (same : M.Perm M') : Acc (Replace r) M' :=
  Acc.intro M' fun _ replace => acc.inv (replace.perm_right same.symm)

/-- Adding elements below `a` one at a time, when each keeps accessibility. -/
theorem acc_append {a : α} (adds : ∀ b, r b a → ∀ M, Acc (Replace r) M → Acc (Replace r) (b :: M)) :
    ∀ (added : List α), (∀ b ∈ added, r b a) → ∀ M, Acc (Replace r) M → Acc (Replace r) (added ++ M)
  | [], _, _, acc => acc
  | b :: rest, below, M, acc =>
      adds b (below b List.mem_cons_self) _
        (acc_append adds rest (fun c member => below c (List.mem_cons_of_mem _ member)) M acc)

/-- An element whose smaller elements keep accessibility when added keeps it
when added itself. -/
theorem acc_cons_of {a : α} (adds : ∀ b, r b a → ∀ M, Acc (Replace r) M → Acc (Replace r) (b :: M)) :
    ∀ M, Acc (Replace r) M → Acc (Replace r) (a :: M) := by
  classical
  intro M acc
  induction acc with
  | intro M accM ih =>
      refine Acc.intro _ fun N replace => ?_
      obtain ⟨c, rest, added, larger, smaller, below⟩ := replace
      by_cases same : c = a
      · subst same
        have restPerm : M.Perm rest := larger.cons_inv
        exact acc_perm (acc_append adds added below M (Acc.intro M accM))
          ((List.Perm.append_left added restPerm).trans smaller.symm)
      · have inM : c ∈ M := by
          rcases List.mem_cons.mp (larger.mem_iff.mpr List.mem_cons_self) with eq | inside
          · exact absurd eq same
          · exact inside
        have mPerm : M.Perm (c :: M.erase c) := List.perm_cons_erase inM
        have restPerm : rest.Perm (a :: M.erase c) :=
          (larger.symm.trans ((mPerm.cons a).trans (List.Perm.swap c a (M.erase c)))).cons_inv
        have replaced : Replace r (added ++ M.erase c) M := ⟨c, M.erase c, added, mPerm, List.Perm.refl _, below⟩
        exact acc_perm (ih _ replaced)
          ((List.perm_middle.symm.trans (List.Perm.append_left added restPerm.symm)).trans smaller.symm)

theorem acc_cons (wf : WellFounded r) : ∀ (a : α) (M : List α), Acc (Replace r) M → Acc (Replace r) (a :: M) :=
  fun a => wf.induction (C := fun a => ∀ M, Acc (Replace r) M → Acc (Replace r) (a :: M)) a
    fun _ ih => acc_cons_of fun b below => ih b below

theorem acc_all (wf : WellFounded r) : ∀ M : List α, Acc (Replace r) M
  | [] => Acc.intro [] fun _ replace => by
      obtain ⟨_, _, _, larger, _, _⟩ := replace
      exact absurd larger.length_eq (by simp)
  | a :: M => acc_cons wf a M (acc_all wf M)

/-- **The multiset order of a well-founded order is well-founded.** -/
theorem Lower.wellFounded (wf : WellFounded r) : WellFounded (Lower r) :=
  WellFounded.transGen ⟨acc_all wf⟩

end WellFounded

/-! ## Building steps -/

theorem Lower.trans {first second third : List α} (one : Lower r first second) (two : Lower r second third) :
    Lower r first third :=
  Relation.TransGen.trans one two

/-- One element replaced by smaller ones. -/
theorem Lower.replace {a : α} {rest added : List α} (below : ∀ b ∈ added, r b a) : Lower r (added ++ rest) (a :: rest) :=
  .single ⟨a, rest, added, .refl _, .refl _, below⟩

/-- One element removed. -/
theorem Lower.erase (a : α) (rest : List α) : Lower r rest (a :: rest) := by
  simpa using Lower.replace (r := r) (a := a) (rest := rest) (added := []) (by simp)

theorem Lower.perm_left {smaller other larger : List α} (lower : Lower r smaller larger) (same : smaller.Perm other) :
    Lower r other larger := by
  induction lower with
  | single replace => exact .single (replace.perm_left same)
  | tail _ replace ih => exact .tail ih replace

theorem Lower.perm_right {smaller larger other : List α} (lower : Lower r smaller larger) (same : larger.Perm other) :
    Lower r smaller other := by
  cases lower with
  | single replace => exact .single (replace.perm_right same)
  | tail first replace => exact .tail first (replace.perm_right same)

theorem Replace.append_left {smaller larger : List α} (replace : Replace r smaller larger) (front : List α) :
    Replace r (front ++ smaller) (front ++ larger) := by
  obtain ⟨a, rest, added, larger', smaller', below⟩ := replace
  refine ⟨a, front ++ rest, added, (larger'.append_left front).trans List.perm_middle, ?_, below⟩
  refine (smaller'.append_left front).trans ?_
  rw [← List.append_assoc, ← List.append_assoc]
  exact List.perm_append_comm.append_right rest

theorem Replace.append_right {smaller larger : List α} (replace : Replace r smaller larger) (back : List α) :
    Replace r (smaller ++ back) (larger ++ back) := by
  obtain ⟨a, rest, added, larger', smaller', below⟩ := replace
  refine ⟨a, rest ++ back, added, larger'.append_right back, ?_, below⟩
  rw [← List.append_assoc]
  exact smaller'.append_right back

theorem Lower.append_left {smaller larger : List α} (lower : Lower r smaller larger) (front : List α) :
    Lower r (front ++ smaller) (front ++ larger) := by
  induction lower with
  | single replace => exact .single (replace.append_left front)
  | tail _ replace ih => exact .tail ih (replace.append_left front)

theorem Lower.append_right {smaller larger : List α} (lower : Lower r smaller larger) (back : List α) :
    Lower r (smaller ++ back) (larger ++ back) := by
  induction lower with
  | single replace => exact .single (replace.append_right back)
  | tail _ replace ih => exact .tail ih (replace.append_right back)

/-- Removing an element and any of the others. -/
theorem Lower.sublist {smaller larger : List α} (sub : smaller.Sublist larger) (a : α) : Lower r smaller (a :: larger) := by
  induction sub with
  | slnil => exact Lower.erase a []
  | cons x _ ih =>
      exact ih.trans ((Lower.erase x (a :: _)).perm_right (List.Perm.swap a x _))
  | cons_cons x _ ih =>
      exact (ih.append_left [x]).perm_right (List.Perm.swap a x _)

/-- Replacing one element of a sublist-context: the element in the middle. -/
theorem Lower.middle {a : α} {front back added : List α} (below : ∀ b ∈ added, r b a) :
    Lower r (front ++ added ++ back) (front ++ a :: back) := by
  have := (Lower.replace (r := r) (rest := back) below).append_left front
  simpa [List.append_assoc] using this

end AnthillModKbSpec.Tabled
