import AspisV8R19.R788OrdinaryPointDecomposition
import AspisV8R17.WeightedScatter
import AspisV8R19.R775GatherUnitChordBridge

/-! Exact transpose of the selected transport marker. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace AspisV8R19.R793MarkerTranspose

open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R788OrdinaryPointDecomposition
noncomputable section

variable {F : Type*} [CommRing F]

theorem order_1023 : order (1023 : Fin 1024) = 1023 := by decide

theorem marker_eq_unit : marker (F := F) = unitVector 1023 := by
  funext r
  by_cases hr : r < 1024
  · have hiff : order (⟨r, hr⟩ : Fin 1024) = 1023 ↔ r = 1023 := by
      constructor
      · intro h
        have hj : (⟨r, hr⟩ : Fin 1024) = 1023 := order.injective (by simpa [order_1023] using h)
        exact congrArg Fin.val hj
      · intro h
        subst r
        simpa using order_1023
    simp [marker, extendFin1024, unitVector, hr, hiff]
  · simp [marker, extendFin1024, unitVector, hr]

theorem even_marker_zero :
    (fun i : Nat => unitVector (F := F) 1023 (2*i)) = fun _ => 0 := by
  simpa using (unitVector_odd_even (F := F) 511)

theorem odd_marker :
    (fun i : Nat => unitVector (F := F) 1023 (2*i+1)) = unitVector 511 := by
  simpa using (unitVector_odd_odd (F := F) 511)

theorem marker_transpose (half a b c : F) (r : Nat) :
    sourceChordTranspose half (marker (F := F)) a b c r =
      if r % 2 = 0 then c * unitVector 511 (r / 2)
      else a * unitVector 511 (r / 2) + b * sourceGather half (unitVector 511) (r / 2) := by
  rw [marker_eq_unit]
  unfold sourceChordTranspose
  rw [even_marker_zero, odd_marker]
  simp only [zeroExtend, unitVector, Function.comp_apply]
  -- The bounded lanes are respectively zero and the unit vector at index 63.
  have hzero : (zeroExtend 512 (fun _ : Nat => (0 : F))) = fun _ => 0 := by
    funext i
    simp [zeroExtend]
  have hunit : zeroExtend 512 (unitVector (F := F) 63) = unitVector 511 :=
    zeroExtend_unit 512 63 (by omega)
  rw [hzero, hunit]
  unfold interleave chordDualEven chordDualOdd
  simp only [sourceGather, List.map_const, List.sum_const_zero, mul_zero,
    add_zero, sub_zero, zero_sub, neg_zero, zero_add]
  split <;> simp

theorem target_no_511 (j : Fin 511) : 511 ∉ indexTargets j.val := by decide

theorem marker_transpose_zero_below (half a b c : F) {r : Nat} (hr : r < 1021) :
    sourceChordTranspose half (marker (F := F)) a b c r = 0 := by
  rw [marker_transpose]
  have hdiv : r / 2 < 511 := by omega
  have hgather : sourceGather half (unitVector (F := F) 511) (r / 2) = 0 := by
    rw [AspisV8R19.R775GatherUnitChordBridge.sourceGather_unitVector_eq_sparseX]
    apply sparseX_zero
    exact target_no_511 ⟨r / 2, hdiv⟩
  by_cases he : r % 2 = 0
  · simp [he, unitVector, hr]
  · have hne : r / 2 ≠ 511 := by omega
    simp [he, unitVector, hne, hgather]

#print axioms order_1023
#print axioms marker_eq_unit
#print axioms marker_transpose
#print axioms target_no_511
#print axioms marker_transpose_zero_below

end
end AspisV8R19.R793MarkerTranspose
