import R1Z.BuilderTransportExtracted
import R0Z.WriterRefineOcc
import D18Transport

/-! P6's Kani certificate connects shipped S2 to this extracted arithmetic
reference. The theorems below are kernel proofs about the extracted reference;
Kani soundness is not introduced as a Lean axiom. -/
set_option autoImplicit false
namespace R1Z.BuilderTransport
open Aeneas Aeneas.Std Result R0Z.WriterRefine

/-- The extracted machine-word reference returns D18 without wrapping. -/
theorem reference_row (j : Usize) :
    ∃ out, AspisBuilderReference.row_arithmetic j = ok out ∧
      out.val = AspisR1.rowNat j.val := by
  obtain ⟨d0, hd0, vd0⟩ := WP.spec_imp_exists (UScalar.rem_spec j (y := 4#usize) (by simp))
  obtain ⟨q1, hq1, vq1⟩ := UScalar.div_spec j (y := 4#usize) (by simp)
  obtain ⟨d1, hd1, vd1⟩ := WP.spec_imp_exists (UScalar.rem_spec q1 (y := 4#usize) (by simp))
  obtain ⟨q2, hq2, vq2⟩ := UScalar.div_spec j (y := 16#usize) (by simp)
  obtain ⟨d2, hd2, vd2⟩ := WP.spec_imp_exists (UScalar.rem_spec q2 (y := 4#usize) (by simp))
  obtain ⟨q3, hq3, vq3⟩ := UScalar.div_spec j (y := 64#usize) (by simp)
  obtain ⟨d3, hd3, vd3⟩ := WP.spec_imp_exists (UScalar.rem_spec q3 (y := 4#usize) (by simp))
  obtain ⟨q4, hq4, vq4⟩ := UScalar.div_spec j (y := 256#usize) (by simp)
  obtain ⟨d4, hd4, vd4⟩ := WP.spec_imp_exists (UScalar.rem_spec q4 (y := 4#usize) (by simp))
  have v0 : d0.val = j.val % 4 := by simpa using vd0
  have v1 : d1.val = (j.val / 4) % 4 := by simpa using vd1.trans (by simp [vq1])
  have v2 : d2.val = (j.val / 16) % 4 := by simpa using vd2.trans (by simp [vq2])
  have v3 : d3.val = (j.val / 64) % 4 := by simpa using vd3.trans (by simp [vq3])
  have v4 : d4.val = (j.val / 256) % 4 := by simpa using vd4.trans (by simp [vq4])
  rw [AspisBuilderReference.row_arithmetic, hd0]
  simp only [bind_tc_ok, lift]
  rw [hq1]
  simp only [bind_tc_ok, lift]
  rw [hd1]
  simp only [bind_tc_ok, lift]
  rw [hq2]
  simp only [bind_tc_ok, lift]
  rw [hd2]
  simp only [bind_tc_ok, lift]
  rw [hq3]
  simp only [bind_tc_ok, lift]
  rw [hd3]
  simp only [bind_tc_ok, lift]
  rw [hq4]
  simp only [bind_tc_ok, lift]
  rw [hd4]
  simp only [bind_tc_ok, lift]
  refine ⟨_, rfl, ?_⟩
  let m0 := Usize.wrapping_mul 64#usize d0
  have vm0 : m0.val = 64 * d0.val := by
    dsimp [m0]
    rw [umul _ _ (by simp; omega)]
    simp
  let m1 := Usize.wrapping_mul 256#usize d1
  have vm1 : m1.val = 256 * d1.val := by
    dsimp [m1]
    rw [umul _ _ (by simp; omega)]
    simp
  let m2 := Usize.wrapping_mul 16#usize d2
  have vm2 : m2.val = 16 * d2.val := by
    dsimp [m2]
    rw [umul _ _ (by simp; omega)]
    simp
  let m4 := Usize.wrapping_mul 4#usize d4
  have vm4 : m4.val = 4 * d4.val := by
    dsimp [m4]
    rw [umul _ _ (by simp; omega)]
    simp
  let a1 := Usize.wrapping_add m0 m1
  have va1 : a1.val = 64 * d0.val + 256 * d1.val := by
    dsimp [a1]
    rw [uadd _ _ (by rw [vm0, vm1]; omega), vm0, vm1]
  let a2 := Usize.wrapping_add a1 m2
  have va2 : a2.val = 64 * d0.val + 256 * d1.val + 16 * d2.val := by
    dsimp [a2]
    rw [uadd _ _ (by rw [va1, vm2]; omega), va1, vm2]
  let a3 := Usize.wrapping_add a2 d3
  have va3 : a3.val = 64 * d0.val + 256 * d1.val + 16 * d2.val + d3.val := by
    dsimp [a3]
    rw [uadd _ _ (by rw [va2]; omega), va2]
  change (Usize.wrapping_add a3 m4).val = AspisR1.rowNat j.val
  rw [uadd _ _ (by rw [va3, vm4]; omega), va3, vm4]
  simp only [v0, v1, v2, v3, v4, AspisR1.rowNat]

/-- Its coefficient index is precisely the existing D18 transport. -/
theorem reference_row_fin (j : Usize) (hj : j.val < 1024) :
    ∃ out, AspisBuilderReference.row_arithmetic j = ok out ∧
      out.val = (AspisR1.row ⟨j.val, hj⟩).val := by
  obtain ⟨out, ho, hv⟩ := reference_row j
  exact ⟨out, ho, hv⟩

#print axioms reference_row
#print axioms reference_row_fin
end R1Z.BuilderTransport
