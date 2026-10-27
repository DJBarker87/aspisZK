import RPu_FJe_RawReference
import ExtractedMaskReducerOps
set_option autoImplicit false
namespace AspisR1.FJe_Component3
open Aeneas Aeneas.Std Result
open ExtractedMaskReducerOps
abbrev Words := Fin 4 → Fin 4 → U64
def component3Ops (w : Words) : Result U64 := do
  let i40 ← w 0 3 + w 1 2
  let i42 ← i40 + w 2 1
  let i44 ← i42 + w 3 0
  ok i44

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
#print axioms component3Ops_success
end AspisR1.FJe_Component3
