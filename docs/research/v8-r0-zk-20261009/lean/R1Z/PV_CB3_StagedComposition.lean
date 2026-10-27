import R1Z.PV_CB3_StagedWord
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_StagedComposition
open Aeneas Aeneas.Std Result
/-- Compose successful source steps without assuming their outputs. -/
theorem bind_total {A B : Type} (r : Result A) (k : A → Result B)
    (hr : ∃ a, r = ok a) (hk : ∀ a, ∃ b, k a = ok b) :
    ∃ b, (do let a ← r; k a) = ok b := by
  obtain ⟨a,ha⟩ := hr
  rw [ha]
  exact hk a

theorem read_total {T : Type} {n : Usize} (xs : Array T n) (i : Usize)
    (h : i.val < n.val) : ∃ v, Array.index_usize xs i = ok v :=
  ⟨_,PV_CB3_StagedTotal.read_eq xs i h⟩

/-- Every byte read in the staged source is within the 32-byte carrier. -/
theorem words_total (block : Array U8 32#usize) :
    ∃ words, PV_CB3_StagedSource.staged_reference.words block = ok words := by
  unfold PV_CB3_StagedSource.staged_reference.words
  simp only [lift,bind_tc_ok]
  repeat' first
    | exact ⟨_,rfl⟩
    | exact read_total _ _ (by decide)
    | apply bind_total
    | intro x

/-- All eight division stages terminate for every word array. -/
theorem pass_total (rank : Array U32 8#usize) :
    ∃ q r, PV_CB3_StagedSource.staged_reference.pass rank = ok (q,r) := by
  have h : ∃ qr, PV_CB3_StagedSource.staged_reference.pass rank = ok qr := by
    unfold PV_CB3_StagedSource.staged_reference.pass
    simp only [lift,bind_tc_ok]
    repeat' first
      | exact ⟨_,rfl⟩
      | exact read_total _ _ (by decide)
      | exact PV_CB3_StagedWord.word_total _ _
      | apply bind_total
      | rintro ⟨x,y⟩
      | intro x
  obtain ⟨⟨q,r⟩,h⟩ := h
  exact ⟨q,r,h⟩
#print axioms bind_total
#print axioms read_total
#print axioms words_total
#print axioms pass_total
end R1Z.PV_CB3_StagedComposition
