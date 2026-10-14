import R1TraceTable

/-! Structural list decomposition at the first occurrence of a read address. -/
set_option autoImplicit false
namespace AspisR1.FirstReadCut

open FS FS2.Duplex
open AspisV8PairedCommitment

variable {I A : Type} [DecidableEq I]

theorem first_read_cut (tr : List (I × A)) (a : I)
    (ha : a ∈ tr.map Prod.fst) :
    ∃ pre value post, tr = pre ++ (a, value) :: post ∧
      a ∉ pre.map Prod.fst := by
  induction tr with
  | nil => simp at ha
  | cons q rest ih =>
      rcases q with ⟨i, v⟩
      simp only [List.map_cons, List.mem_cons] at ha
      by_cases hia : i = a
      · subst i
        exact ⟨[], v, rest, by simp, by simp⟩
      · have hrest : a ∈ rest.map Prod.fst := ha.resolve_left hia
        obtain ⟨pre, value, post, hrep, hnot⟩ := ih hrest
        refine ⟨(i, v) :: pre, value, post, ?_, ?_⟩
        · simp [hrep, List.cons_append]
        · simp only [List.map_cons, List.mem_cons]
          exact ⟨Ne.symm hia, hnot⟩

theorem tableBefore_representation (t : Table I A) (tr : List (I × A))
    (a : I) (ha : a ∈ tr.map Prod.fst) :
    ∃ pre value post, tr = pre ++ (a, value) :: post ∧
      a ∉ pre.map Prod.fst ∧
      tableBefore t tr a = TraceTable.replay t pre := by
  obtain ⟨pre, value, post, hrep, hnot⟩ := first_read_cut tr a ha
  refine ⟨pre, value, post, hrep, hnot, ?_⟩
  rw [hrep]
  exact TraceTable.tableBefore_cut t pre a value post hnot

#print axioms first_read_cut
#print axioms tableBefore_representation

end AspisR1.FirstReadCut
