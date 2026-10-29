import R0Z.WriterRefineValueModel

/-! The extracted aux-block writer (value aux + both occupancy rows) computes
block 63 of the model (rows 1008..1023), cell by cell (DESIGN-BUILDER-MODEL §9). -/
set_option autoImplicit false

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result R0WriterCopies

variable {K : Type} [Field K]

theorem aux_block_model [CharP K 0x7fffffff] (values : Array U32 3#usize) (input output : OccRecord)
    (C : R0Z.BuilderModel.Cells K) (hv : ValueLifts values C) (hi : OccLifts input C.inOcc)
    (ho : OccLifts output C.outOcc) :
    ∃ b, write_aux_block values input output = ok b ∧
      ∀ (r c : Fin 16), liftU (K := K) (b.val[r.val * 16 + c.val]!) =
        R0Z.BuilderModel.auxCell C (1008 + r.val) c := by
  obtain ⟨b0, hb0, hs0⟩ := value_block values hv.small
  have n9 : (9#usize : Usize).val = 9 := by simp
  have n10 : (10#usize : Usize).val = 10 := by simp
  obtain ⟨b1, hb1, hr1, hu1⟩ := occ_row_model b0 9#usize (by rw [n9]; omega) input C.inOcc hi
    (fun c hc => by rw [n9]; exact value_rows_zero values b0 hs0 9 (Or.inl rfl) c hc)
  obtain ⟨b2, hb2, hr2, hu2⟩ := occ_row_model b1 10#usize (by rw [n10]; omega) output C.outOcc ho
    (fun c hc => by
      rw [n10, hu1 _ (by rw [n9]; omega)]
      exact value_rows_zero values b0 hs0 10 (Or.inr rfl) c hc)
  refine ⟨b2, ?_, fun r c => ?_⟩
  · rw [write_aux_block, hb0]
    simp only [bind_tc_ok]
    rw [hb1]
    simp only [bind_tc_ok]
    exact hb2
  · have hc := c.isLt
    by_cases e10 : r.val = 10
    · have := hr2 c
      rw [n10] at this
      rw [e10, this, show (1008 + 10 : Nat) = 1018 by norm_num, R0Z.BuilderModel.aux_1018]
    rw [hu2 _ (by rw [n10]; omega)]
    by_cases e9 : r.val = 9
    · have := hr1 c
      rw [n9] at this
      rw [e9, this, show (1008 + 9 : Nat) = 1017 by norm_num, R0Z.BuilderModel.aux_1017]
    rw [hu1 _ (by rw [n9]; omega)]
    have hr := r.isLt
    obtain ⟨rv, hrv⟩ : ∃ rv, r.val = rv := ⟨_, rfl⟩
    rw [hrv]
    rw [hrv] at e9 e10 hr
    interval_cases rv
    · exact value_row_0 values C hv b0 hs0 c
    · exact value_row_1 values C hv b0 hs0 c
    · exact value_row_2 values C hv b0 hs0 c
    · exact value_row_3 values C hv b0 hs0 c
    · exact value_row_4 values C hv b0 hs0 c
    · exact value_row_5 values C hv b0 hs0 c
    · exact value_row_6 values C hv b0 hs0 c
    · exact value_row_7 values C hv b0 hs0 c
    · exact value_row_8 values C hv b0 hs0 c
    · exact absurd rfl e9
    · exact absurd rfl e10
    · exact value_row_11 values C hv b0 hs0 c
    · exact value_row_12 values C hv b0 hs0 c
    · exact value_row_13 values C hv b0 hs0 c
    · exact value_row_14 values C hv b0 hs0 c
    · exact value_row_15 values C hv b0 hs0 c

#print axioms aux_block_model
end R0Z.WriterRefine
