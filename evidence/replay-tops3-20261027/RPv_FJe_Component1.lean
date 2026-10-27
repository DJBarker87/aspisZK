import RPv_FJe_RawReference
import ExtractedMaskReducerOps
set_option autoImplicit false
namespace AspisR1.FJe_Component1
open Aeneas Aeneas.Std Result
open ExtractedMaskReducerOps
abbrev Words := Fin 4 → Fin 4 → U64
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
#print axioms component1Ops_success
end AspisR1.FJe_Component1
