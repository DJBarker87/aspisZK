import FS2.DuplexTrace

/-! Deterministic replay facts for oracle tables. -/
set_option autoImplicit false
namespace AspisR1.TraceTable

open FS FS2.Duplex
open AspisV8PairedCommitment

variable {I A : Type} [DecidableEq I]

/-- Replay a trace by applying its oracle writes in order. -/
def replay (t : Table I A) (tr : List (I × A)) : Table I A :=
  tr.foldl (fun T q => put T q.1 q.2) t

theorem replay_append (t : Table I A) (tr₁ tr₂ : List (I × A)) :
    replay t (tr₁ ++ tr₂) = replay (replay t tr₁) tr₂ := by
  simp [replay, List.foldl_append]

private theorem replay_apply (t : Table I A) (tr : List (I × A))
    (H : I → A) (hcons : ∀ q ∈ tr, q.2 = H q.1) (a : I) :
    replay t tr a = if a ∈ tr.map Prod.fst then some (H a) else t a := by
  induction tr generalizing t with
  | nil => simp [replay]
  | cons q rest ih =>
      obtain ⟨i, v⟩ := q
      have hv : v = H i := hcons (i, v) (List.mem_cons_self ..)
      have hrest : ∀ q ∈ rest, q.2 = H q.1 := fun q hq =>
        hcons q (List.mem_cons_of_mem _ hq)
      by_cases hia : i = a
      · subst a
        simp [replay, hv]
      · have htail := ih (put t i v) H hrest a
        simp only [replay, List.foldl_cons, List.map_cons, List.mem_cons]
        rw [htail]
        by_cases hmem : a ∈ rest.map Prod.fst
        · simp [hmem, put, Ne.symm hia]
        · simp [hmem, put, Ne.symm hia]

theorem replay_empty_apply (H : I → A) (tr : List (I × A))
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (a : I) :
    replay (emptyTable : Table I A) tr a =
      if a ∈ tr.map Prod.fst then some (H a) else none := by
  rw [replay_apply emptyTable tr H hcons a]
  simp [emptyTable]

theorem tableBefore_cut (t : Table I A) (pre : List (I × A))
    (a : I) (value : A) (post : List (I × A))
    (hnot : a ∉ pre.map Prod.fst) :
    tableBefore t (pre ++ (a, value) :: post) a = replay t pre := by
  induction pre generalizing t with
  | nil => rfl
  | cons q rest ih =>
      obtain ⟨i, v⟩ := q
      have hia : i ≠ a := by
        intro h
        apply hnot
        simp [h]
      have hrest : a ∉ rest.map Prod.fst := by
        intro h
        apply hnot
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr h
      simp only [List.cons_append, tableBefore, if_neg hia]
      rw [ih (put t i v) hrest]
      rfl

#print axioms replay_append
#print axioms replay_empty_apply
#print axioms tableBefore_cut

end AspisR1.TraceTable
