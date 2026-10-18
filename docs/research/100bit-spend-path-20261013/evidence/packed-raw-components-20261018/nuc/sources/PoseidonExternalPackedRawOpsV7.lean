import Aeneas
import PoseidonLeadingSourceDeclarationsV5
import PoseidonExternalPackedAlgebra
import ExtractedMaskReducerOps

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result
namespace AspisR1.PoseidonExternalPackedRawOps
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskReducerOps

abbrev Words := Fin 4 → Fin 4 → U64

/-- The exact source-order operations which produce raw packed component 0,
after its Array.index_usize reads have been resolved. -/
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

/-- Source-order checked arithmetic for raw packed component 1. -/
def component1Ops (bound : U64) (w : Words) : Result U64 := do
  let i17 ← w 0 1 + w 1 0
  let i19 ← i17 + w 2 2
  let i21 ← 2#u64 * (w 2 3)
  let i22 ← i19 + i21
  let i24 ← 2#u64 * (w 3 2)
  let i25 ← i22 + i24
  let i26 ← i25 + bound
  let i28 ← i26 - w 3 3
  ok i28

/-- Source-order checked arithmetic for raw packed component 2. -/
def component2Ops (bound : U64) (w : Words) : Result U64 := do
  let i30 ← 2#u64 * bound
  let i31 ← w 0 2 + i30
  let i33 ← i31 - w 1 3
  let i35 ← i33 + w 2 0
  let i37 ← i35 - w 3 1
  ok i37

/-- Source-order checked arithmetic for raw packed component 3. -/
def component3Ops (w : Words) : Result U64 := do
  let i40 ← w 0 3 + w 1 2
  let i42 ← i40 + w 2 1
  let i44 ← i42 + w 3 0
  ok i44

def packedComponentsOps (bound : U64) (w : Words) : Result (Array U64 4#usize) := do
  let x0 ← component0Ops bound w
  let x1 ← component1Ops bound w
  let x2 ← component2Ops bound w
  let x3 ← component3Ops w
  ok (Array.make 4#usize [x0, x1, x2, x3])

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

theorem component1Ops_success (bound : U64) (w : Words)
    (hbound : ∀ r j, (w r j).val < bound.val)
    (hwide : 8 * bound.val < 2^64) :
    ∃ out : U64,
      component1Ops bound w = .ok out ∧
      out.val = AspisR1.PoseidonExternalPackedAlgebra.packedNat
        bound.val (fun r j => (w r j).val) 1 := by
  have h2c : (2#u64).val = 2 := by decide
  have h17 : (w 0 1).val + (w 1 0).val < 2^64 := by
    have h01 := hbound 0 1; have h10 := hbound 1 0
    omega
  obtain ⟨i17, hi17, hv17⟩ := add_success (w 0 1) (w 1 0) h17
  have h19 : i17.val + (w 2 2).val < 2^64 := by
    rw [hv17]
    have h01 := hbound 0 1; have h10 := hbound 1 0
    have h22 := hbound 2 2
    omega
  obtain ⟨i19, hi19, hv19⟩ := add_success i17 (w 2 2) h19
  have h21 : (2#u64).val * (w 2 3).val < 2^64 := by
    rw [h2c]
    have h23 := hbound 2 3
    omega
  obtain ⟨i21, hi21, hv21⟩ := mul_success (2#u64) (w 2 3) h21
  rw [h2c] at hv21
  have h22' : i19.val + i21.val < 2^64 := by
    rw [hv19, hv21, hv17]
    have h01 := hbound 0 1; have h10 := hbound 1 0
    have h22 := hbound 2 2; have h23 := hbound 2 3
    omega
  obtain ⟨i22, hi22, hv22⟩ := add_success i19 i21 h22'
  have h24 : (2#u64).val * (w 3 2).val < 2^64 := by
    rw [h2c]
    have h32 := hbound 3 2
    omega
  obtain ⟨i24, hi24, hv24⟩ := mul_success (2#u64) (w 3 2) h24
  rw [h2c] at hv24
  have h25 : i22.val + i24.val < 2^64 := by
    rw [hv22, hv24, hv21, hv19, hv17]
    have h01 := hbound 0 1; have h10 := hbound 1 0
    have h22 := hbound 2 2; have h23 := hbound 2 3
    have h32 := hbound 3 2
    omega
  obtain ⟨i25, hi25, hv25⟩ := add_success i22 i24 h25
  have h26 : i25.val + bound.val < 2^64 := by
    rw [hv25, hv22, hv24, hv21, hv19, hv17]
    have h01 := hbound 0 1; have h10 := hbound 1 0
    have h22 := hbound 2 2; have h23 := hbound 2 3
    have h32 := hbound 3 2
    omega
  obtain ⟨i26, hi26, hv26⟩ := add_success i25 bound h26
  have h28 : (w 3 3).val ≤ i26.val := by
    rw [hv26, hv25, hv22, hv24, hv21, hv19, hv17]
    have h01 := hbound 0 1; have h10 := hbound 1 0
    have h22 := hbound 2 2; have h23 := hbound 2 3
    have h32 := hbound 3 2; have h33 := hbound 3 3
    omega
  obtain ⟨i28, hi28, hv28⟩ := sub_success i26 (w 3 3) h28
  change UScalar.add (w 0 1) (w 1 0) = Result.ok i17 at hi17
  change UScalar.add i17 (w 2 2) = Result.ok i19 at hi19
  change UScalar.mul (2#u64) (w 2 3) = Result.ok i21 at hi21
  change UScalar.add i19 i21 = Result.ok i22 at hi22
  change UScalar.mul (2#u64) (w 3 2) = Result.ok i24 at hi24
  change UScalar.add i22 i24 = Result.ok i25 at hi25
  change UScalar.add i25 bound = Result.ok i26 at hi26
  change UScalar.sub i26 (w 3 3) = Result.ok i28 at hi28
  refine ⟨i28, ?_, ?_⟩
  · change (do
      let i17 ← UScalar.add (w 0 1) (w 1 0)
      let i19 ← UScalar.add i17 (w 2 2)
      let i21 ← UScalar.mul (2#u64) (w 2 3)
      let i22 ← UScalar.add i19 i21
      let i24 ← UScalar.mul (2#u64) (w 3 2)
      let i25 ← UScalar.add i22 i24
      let i26 ← UScalar.add i25 bound
      let i28 ← UScalar.sub i26 (w 3 3)
      Result.ok i28) = Result.ok i28
    simp only [bind_tc_ok, hi17, hi19, hi21, hi22, hi24, hi25, hi26, hi28]
  · rw [hv28, hv26, hv25, hv24, hv22, hv21, hv19, hv17]
    simp [AspisR1.PoseidonExternalPackedAlgebra.packedNat]

theorem component2Ops_success (bound : U64) (w : Words)
    (hbound : ∀ r j, (w r j).val < bound.val)
    (hwide : 8 * bound.val < 2^64) :
    ∃ out : U64,
      component2Ops bound w = .ok out ∧
      out.val = AspisR1.PoseidonExternalPackedAlgebra.packedNat
        bound.val (fun r j => (w r j).val) 2 := by
  have h2c : (2#u64).val = 2 := by decide
  have h30 : (2#u64).val * bound.val < 2^64 := by
    rw [h2c]
    omega
  obtain ⟨i30, hi30, hv30⟩ := mul_success (2#u64) bound h30
  rw [h2c] at hv30
  have h31 : (w 0 2).val + i30.val < 2^64 := by
    rw [hv30]
    have h02 := hbound 0 2
    omega
  obtain ⟨i31, hi31, hv31⟩ := add_success (w 0 2) i30 h31
  have h33 : (w 1 3).val ≤ i31.val := by
    rw [hv31, hv30]
    have h02 := hbound 0 2; have h13 := hbound 1 3
    omega
  obtain ⟨i33, hi33, hv33⟩ := sub_success i31 (w 1 3) h33
  have h35 : i33.val + (w 2 0).val < 2^64 := by
    rw [hv33, hv31, hv30]
    have h02 := hbound 0 2; have h13 := hbound 1 3
    have h20 := hbound 2 0
    omega
  obtain ⟨i35, hi35, hv35⟩ := add_success i33 (w 2 0) h35
  have h37 : (w 3 1).val ≤ i35.val := by
    rw [hv35, hv33, hv31, hv30]
    have h02 := hbound 0 2; have h13 := hbound 1 3
    have h20 := hbound 2 0; have h31 := hbound 3 1
    omega
  obtain ⟨i37, hi37, hv37⟩ := sub_success i35 (w 3 1) h37
  change UScalar.mul (2#u64) bound = Result.ok i30 at hi30
  change UScalar.add (w 0 2) i30 = Result.ok i31 at hi31
  change UScalar.sub i31 (w 1 3) = Result.ok i33 at hi33
  change UScalar.add i33 (w 2 0) = Result.ok i35 at hi35
  change UScalar.sub i35 (w 3 1) = Result.ok i37 at hi37
  refine ⟨i37, ?_, ?_⟩
  · change (do
      let i30 ← UScalar.mul (2#u64) bound
      let i31 ← UScalar.add (w 0 2) i30
      let i33 ← UScalar.sub i31 (w 1 3)
      let i35 ← UScalar.add i33 (w 2 0)
      let i37 ← UScalar.sub i35 (w 3 1)
      Result.ok i37) = Result.ok i37
    simp only [bind_tc_ok, hi30, hi31, hi33, hi35, hi37]
  · rw [hv37, hv35, hv33, hv31, hv30]
    simp [AspisR1.PoseidonExternalPackedAlgebra.packedNat]

theorem component3Ops_success (bound : U64) (w : Words)
    (hbound : ∀ r j, (w r j).val < bound.val)
    (hwide : 8 * bound.val < 2^64) :
    ∃ out : U64,
      component3Ops w = .ok out ∧
      out.val = AspisR1.PoseidonExternalPackedAlgebra.packedNat
        bound.val (fun r j => (w r j).val) 3 := by
  have h40 : (w 0 3).val + (w 1 2).val < 2^64 := by
    have h03 := hbound 0 3; have h12 := hbound 1 2
    omega
  obtain ⟨i40, hi40, hv40⟩ := add_success (w 0 3) (w 1 2) h40
  have h42 : i40.val + (w 2 1).val < 2^64 := by
    rw [hv40]
    have h03 := hbound 0 3; have h12 := hbound 1 2
    have h21 := hbound 2 1
    omega
  obtain ⟨i42, hi42, hv42⟩ := add_success i40 (w 2 1) h42
  have h44 : i42.val + (w 3 0).val < 2^64 := by
    rw [hv42, hv40]
    have h03 := hbound 0 3; have h12 := hbound 1 2
    have h21 := hbound 2 1; have h30 := hbound 3 0
    omega
  obtain ⟨i44, hi44, hv44⟩ := add_success i42 (w 3 0) h44
  change UScalar.add (w 0 3) (w 1 2) = Result.ok i40 at hi40
  change UScalar.add i40 (w 2 1) = Result.ok i42 at hi42
  change UScalar.add i42 (w 3 0) = Result.ok i44 at hi44
  refine ⟨i44, ?_, ?_⟩
  · change (do
      let i40 ← UScalar.add (w 0 3) (w 1 2)
      let i42 ← UScalar.add i40 (w 2 1)
      let i44 ← UScalar.add i42 (w 3 0)
      Result.ok i44) = Result.ok i44
    simp only [bind_tc_ok, hi40, hi42, hi44]
  · rw [hv44, hv42, hv40]
    simp [AspisR1.PoseidonExternalPackedAlgebra.packedNat]

theorem packedComponentsOps_success (bound : U64) (w : Words)
    (hbound : ∀ r j, (w r j).val < bound.val)
    (hwide : 8 * bound.val < 2^64) :
    ∃ out : Array U64 4#usize,
      packedComponentsOps bound w = .ok out ∧
      ∀ j : Fin 4,
        out.val[j.val]'(by simpa using j.isLt) =
          AspisR1.PoseidonExternalPackedAlgebra.packedNat
            bound.val (fun r k => (w r k).val) j := by
  obtain ⟨x0, hx0, hv0⟩ := component0Ops_success bound w hbound hwide
  obtain ⟨x1, hx1, hv1⟩ := component1Ops_success bound w hbound hwide
  obtain ⟨x2, hx2, hv2⟩ := component2Ops_success bound w hbound hwide
  obtain ⟨x3, hx3, hv3⟩ := component3Ops_success bound w hbound hwide
  refine ⟨Array.make 4#usize [x0, x1, x2, x3], ?_, ?_⟩
  · simp [packedComponentsOps, hx0, hx1, hx2, hx3]
  · intro j
    fin_cases j <;> simp [Array.make, hv0, hv1, hv2, hv3]

#print axioms component0Ops_success
end AspisR1.PoseidonExternalPackedRawOps
