import FS2.DuplexTrace

/-! Structural transport facts for extending an oracle trace by a suffix. -/
set_option autoImplicit false
namespace AspisR1.TraceAppend

open FS FS2 FS2.Duplex
open AspisV8R19.MemoizedProgramLaw
open AspisV8PairedCommitment

variable {I A : Type} [DecidableEq I]

theorem tableBefore_append (t : Table I A) (tr tail : List (I × A)) (a : I)
    (ha : a ∈ tr.map Prod.fst) :
    tableBefore t (tr ++ tail) a = tableBefore t tr a := by
  induction tr generalizing t with
  | nil => simp at ha
  | cons q rest ih =>
      obtain ⟨i, v⟩ := q
      by_cases hia : i = a
      · subst i
        simp [List.cons_append, tableBefore]
      · have hrest : a ∈ rest.map Prod.fst := by
          simp only [List.map_cons, List.mem_cons] at ha
          rcases ha with h | h
          · exact (hia h.symm).elim
          · exact h
        simp only [List.cons_append, tableBefore, hia, if_false]
        rw [ih (put t i v) hrest]

theorem traceFrom_append (tr tail : List (I × A)) (a : I)
    (ha : a ∈ tr.map Prod.fst) :
    traceFrom (tr ++ tail) a = traceFrom tr a ++ tail := by
  induction tr with
  | nil => simp at ha
  | cons q rest ih =>
      obtain ⟨i, v⟩ := q
      by_cases hia : i = a
      · subst i
        simp [List.cons_append, traceFrom]
      · have hrest : a ∈ rest.map Prod.fst := by
          simp only [List.map_cons, List.mem_cons] at ha
          rcases ha with h | h
          · exact (hia h.symm).elim
          · exact h
        simp only [List.cons_append, traceFrom, hia, if_false]
        exact ih hrest

theorem firstReads_le_append (t : Table I A) (tr tail : List (I × A)) :
    firstReads t tr ≤ firstReads t (tr ++ tail) := by
  induction tr generalizing t with
  | nil => simp [firstReads]
  | cons q rest ih =>
      obtain ⟨i, v⟩ := q
      simp only [List.cons_append, firstReads]
      have h := ih (put t i v)
      omega

theorem hitsBad_of_prefix (bad : I → Table I A → A → Prop)
    (t : Table I A) (tr tail : List (I × A)) :
    hitsBad bad t tr → hitsBad bad t (tr ++ tail) := by
  induction tr generalizing t with
  | nil => simp [hitsBad]
  | cons q rest ih =>
      obtain ⟨i, v⟩ := q
      simp only [List.cons_append, hitsBad]
      intro h
      rcases h with hfirst | hrest
      · exact Or.inl hfirst
      · exact Or.inr (ih (put t i v) hrest)

#print axioms tableBefore_append
#print axioms traceFrom_append
#print axioms firstReads_le_append
#print axioms hitsBad_of_prefix

end AspisR1.TraceAppend
