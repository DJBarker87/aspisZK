import AspisR1SelectedMaskProbe.Funs

/-! Canonical-input addition/subtraction for the freshly extracted current field
functions, using the full Aeneas runtime. Proof routes reuse UnsignedCoreSlice,
UnsignedReducerOps, GeneratedM31Add and GeneratedM31Sub. The selected extraction
disables r0-r91-audit and r0-op-count; verifier caller canonicality remains separate. -/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskM31AddSub

open Aeneas.Std Result Error

abbrev P : Nat := 2147483647

private theorem currentP_value : AspisR1SelectedMaskProbe.field.P.val = P := by
  rw [AspisR1SelectedMaskProbe.field.P]
  rfl

private theorem tryMk_success {ty : UScalarTy} (n : Nat)
    (h : n < 2 ^ ty.numBits) :
    ∃ z : UScalar ty, UScalar.tryMk ty n = .ok z ∧ z.val = n := by
  refine ⟨UScalar.ofNatCore n h, ?_, rfl⟩
  simp [UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds, h, Result.ofOption]

private theorem sub_success {ty : UScalarTy} (x y : UScalar ty)
    (h : y.val ≤ x.val) :
    ∃ z : UScalar ty, UScalar.sub x y = .ok z ∧ z.val = x.val - y.val := by
  refine ⟨⟨BitVec.ofNat _ (x.val - y.val)⟩, ?_, ?_⟩
  · simp only [UScalar.sub, Nat.not_lt.mpr h, if_false]
  · change (x.val - y.val) % 2 ^ ty.numBits = x.val - y.val
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.bv.isLt

private def finishSub (n : UScalar .U32) : Result (UScalar .U32) :=
  if n ≥ AspisR1SelectedMaskProbe.field.P then do
    let r ← UScalar.sub n AspisR1SelectedMaskProbe.field.P
    .ok r
  else .ok n

private theorem finishSub_mod (n : UScalar .U32) (hn : n.val < 2 * P) :
    ∃ r : UScalar .U32, finishSub n = .ok r ∧
      r.val = n.val % P ∧ r.val < P := by
  have branch : (n ≥ AspisR1SelectedMaskProbe.field.P) ↔ P ≤ n.val := by
    change AspisR1SelectedMaskProbe.field.P.val ≤ n.val ↔ P ≤ n.val
    rw [currentP_value]
  by_cases h : P ≤ n.val
  · obtain ⟨r, hr, hv⟩ := sub_success n AspisR1SelectedMaskProbe.field.P
      (by rw [currentP_value]; exact h)
    rw [currentP_value] at hv
    have small : n.val - P < P := by omega
    refine ⟨r, ?_, ?_, by rw [hv]; exact small⟩
    · simp only [finishSub, branch, h, if_pos, hr, bind_tc_ok]
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt small]
      exact hv
  · have small : n.val < P := Nat.lt_of_not_ge h
    exact ⟨n, by simp only [finishSub, branch, h, if_false],
      (Nat.mod_eq_of_lt small).symm, small⟩

theorem current_add_mod
    (x y : AspisR1SelectedMaskProbe.field.M31)
    (hx : x.val < P) (hy : y.val < P) :
    ∃ z : AspisR1SelectedMaskProbe.field.M31,
      AspisR1SelectedMaskProbe.field.M31.add x y = .ok z ∧
      z.val = (x.val + y.val) % P ∧ z.val < P := by
  have hP : P = 2147483647 := rfl
  have hbound : x.val + y.val < 2 ^ 32 := by omega
  have hadd : ∃ s : UScalar .U32, UScalar.add x y = .ok s ∧
      s.val = x.val + y.val := tryMk_success _ hbound
  obtain ⟨s, hs, hvs⟩ := hadd
  obtain ⟨z, hz, hvz, hcz⟩ := finishSub_mod s (by rw [hvs]; omega)
  refine ⟨z, ?_, ?_, hcz⟩
  · change (do let s ← UScalar.add x y; finishSub s) = Result.ok z
    simp only [AspisR1SelectedMaskProbe.field.M31.add, hs, bind_tc_ok, hz]
  · simpa only [hvs] using hvz

theorem current_sub_mod
    (x y : AspisR1SelectedMaskProbe.field.M31)
    (hx : x.val < P) (hy : y.val < P) :
    ∃ z : AspisR1SelectedMaskProbe.field.M31,
      AspisR1SelectedMaskProbe.field.M31.sub x y = .ok z ∧
      z.val = (x.val + P - y.val) % P ∧ z.val < P := by
  have hP : P = 2147483647 := rfl
  have hbound : x.val + AspisR1SelectedMaskProbe.field.P.val < 2 ^ 32 := by
    rw [currentP_value]
    omega
  have hadd : ∃ i : UScalar .U32,
      UScalar.add x AspisR1SelectedMaskProbe.field.P = .ok i ∧
      i.val = x.val + AspisR1SelectedMaskProbe.field.P.val :=
    tryMk_success _ hbound
  obtain ⟨i, hi, hiv⟩ := hadd
  rw [currentP_value] at hiv
  obtain ⟨n, hn, hnv⟩ := sub_success i y (by rw [hiv]; omega)
  rw [hiv] at hnv
  obtain ⟨z, hz, hvz, hcz⟩ := finishSub_mod n (by rw [hnv]; omega)
  refine ⟨z, ?_, ?_, hcz⟩
  · change (do
      let i ← UScalar.add x AspisR1SelectedMaskProbe.field.P
      let n ← UScalar.sub i y
      finishSub n) = Result.ok z
    simp only [AspisR1SelectedMaskProbe.field.M31.sub, hi, hn,
      bind_tc_ok, hz]
  · simpa only [hnv] using hvz

#print axioms current_add_mod
#print axioms current_sub_mod

end AspisR1.ExtractedMaskM31AddSub
