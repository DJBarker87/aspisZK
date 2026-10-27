import RPu_FJe_RawReference
import ExtractedMaskReducerOps
set_option autoImplicit false
namespace AspisR1.FJe_Component0
open Aeneas Aeneas.Std Result
open ExtractedMaskReducerOps
abbrev Words := Fin 4 → Fin 4 → U64
def component0Ops (bound : U64) (w : Words) : Result U64 := do
  let i1 ← 5#u64 * bound
  let i2 ← w 0 0 + i1
  let i4 ← i2 - w 1 1
  let i6 ← 2#u64 * (w 2 2)
  let i7 ← i4 + i6
  let i9 ← i7 - w 2 3
  let i11 ← i9 - w 3 2
  let i13 ← 2#u64 * (w 3 3)
  let i14 ← i11 - i13
  ok i14

theorem component0Ops_success (bound : U64) (w : Words)
    (hbound : ∀ r j, (w r j).val < bound.val)
    (hwide : 8 * bound.val < 2^64) :
    ∃ out : U64,
      component0Ops bound w = .ok out ∧
      out.val = AspisR1.PoseidonExternalPackedAlgebra.packedNat
        bound.val (fun r j => (w r j).val) 0 := by
  have h5 : (5#u64).val = 5 := by decide
  have h2c : (2#u64).val = 2 := by decide
  have h1 : (5#u64).val * bound.val < 2^64 := by
    have h5 : (5#u64).val = 5 := by decide
    rw [h5]
    omega
  obtain ⟨i1, hi1, hv1⟩ := mul_success (5#u64) bound h1
  rw [h5] at hv1
  have h2 : (w 0 0).val + i1.val < 2^64 := by
    rw [hv1]
    have hw := hbound 0 0
    have h5 : (5#u64).val = 5 := by decide
    omega
  obtain ⟨i2, hi2, hv2⟩ := add_success (w 0 0) i1 h2
  have h4 : (w 1 1).val ≤ i2.val := by
    rw [hv2, hv1]
    have hw0 := hbound 0 0
    have hw1 := hbound 1 1
    have h5 : (5#u64).val = 5 := by decide
    omega
  obtain ⟨i4, hi4, hv4⟩ := sub_success i2 (w 1 1) h4
  have h6 : (2#u64).val * (w 2 2).val < 2^64 := by
    have h2c : (2#u64).val = 2 := by decide
    rw [h2c]
    have hw := hbound 2 2
    omega
  obtain ⟨i6, hi6, hv6⟩ := mul_success (2#u64) (w 2 2) h6
  rw [h2c] at hv6
  have h7 : i4.val + i6.val < 2^64 := by
    rw [hv4, hv6]
    have hw0 := hbound 0 0
    have hw1 := hbound 1 1
    have hw2 := hbound 2 2
    have h5 : (5#u64).val = 5 := by decide
    have h2c : (2#u64).val = 2 := by decide
    omega
  obtain ⟨i7, hi7, hv7⟩ := add_success i4 i6 h7
  have h9 : (w 2 3).val ≤ i7.val := by
    rw [hv7, hv4, hv2, hv1]
    have hw00 := hbound 0 0
    have hw11 := hbound 1 1
    have hw22 := hbound 2 2
    have hw23 := hbound 2 3
    have h5 : (5#u64).val = 5 := by decide
    have h2c : (2#u64).val = 2 := by decide
    omega
  obtain ⟨i9, hi9, hv9⟩ := sub_success i7 (w 2 3) h9
  have h11 : (w 3 2).val ≤ i9.val := by
    rw [hv9, hv7, hv4, hv2, hv1]
    have hw00 := hbound 0 0
    have hw11 := hbound 1 1
    have hw22 := hbound 2 2
    have hw23 := hbound 2 3
    have hw32 := hbound 3 2
    have h5 : (5#u64).val = 5 := by decide
    have h2c : (2#u64).val = 2 := by decide
    omega
  obtain ⟨i11, hi11, hv11⟩ := sub_success i9 (w 3 2) h11
  have h13 : (2#u64).val * (w 3 3).val < 2^64 := by
    have h2c : (2#u64).val = 2 := by decide
    rw [h2c]
    have hw := hbound 3 3
    omega
  obtain ⟨i13, hi13, hv13⟩ := mul_success (2#u64) (w 3 3) h13
  rw [h2c] at hv13
  have h14 : i13.val ≤ i11.val := by
    rw [hv13, hv11, hv9, hv7, hv4, hv2, hv1]
    have hw00 := hbound 0 0
    have hw11 := hbound 1 1
    have hw22 := hbound 2 2
    have hw23 := hbound 2 3
    have hw32 := hbound 3 2
    have hw33 := hbound 3 3
    have h5 : (5#u64).val = 5 := by decide
    have h2c : (2#u64).val = 2 := by decide
    omega
  obtain ⟨i14, hi14, hv14⟩ := sub_success i11 i13 h14
  change UScalar.mul (5#u64) bound = Result.ok i1 at hi1
  change UScalar.add (w 0 0) i1 = Result.ok i2 at hi2
  change UScalar.sub i2 (w 1 1) = Result.ok i4 at hi4
  change UScalar.mul (2#u64) (w 2 2) = Result.ok i6 at hi6
  change UScalar.add i4 i6 = Result.ok i7 at hi7
  change UScalar.sub i7 (w 2 3) = Result.ok i9 at hi9
  change UScalar.sub i9 (w 3 2) = Result.ok i11 at hi11
  change UScalar.mul (2#u64) (w 3 3) = Result.ok i13 at hi13
  change UScalar.sub i11 i13 = Result.ok i14 at hi14
  refine ⟨i14, ?_, ?_⟩
  · change (do
      let i1 ← UScalar.mul (5#u64) bound
      let i2 ← UScalar.add (w 0 0) i1
      let i4 ← UScalar.sub i2 (w 1 1)
      let i6 ← UScalar.mul (2#u64) (w 2 2)
      let i7 ← UScalar.add i4 i6
      let i9 ← UScalar.sub i7 (w 2 3)
      let i11 ← UScalar.sub i9 (w 3 2)
      let i13 ← UScalar.mul (2#u64) (w 3 3)
      let i14 ← UScalar.sub i11 i13
      Result.ok i14) = Result.ok i14
    simp only [bind_tc_ok, hi1, hi2, hi4, hi6, hi7, hi9, hi11, hi13, hi14]
  · rw [hv14, hv13, hv11, hv9, hv7, hv6, hv4, hv2, hv1]
    simp [AspisR1.PoseidonExternalPackedAlgebra.packedNat]
#print axioms component0Ops_success
end AspisR1.FJe_Component0
