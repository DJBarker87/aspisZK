import RPv_FJe_RawReference
import ExtractedMaskReducerOps
set_option autoImplicit false
namespace AspisR1.FJe_Component2
open Aeneas Aeneas.Std Result
open ExtractedMaskReducerOps
abbrev Words := Fin 4 → Fin 4 → U64
def component2Ops (bound : U64) (w : Words) : Result U64 := do
  let i30 ← 2#u64 * bound
  let i31 ← w 0 2 + i30
  let i33 ← i31 - w 1 3
  let i35 ← i33 + w 2 0
  let i37 ← i35 - w 3 1
  ok i37

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
#print axioms component2Ops_success
end AspisR1.FJe_Component2
