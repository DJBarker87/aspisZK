import AspisV8R19.R788OrdinaryPointDecomposition
import AspisV8R17.WeightedScatter

/-! Exact transpose of the selected transport marker. -/
set_option autoImplicit false
namespace AspisV8R19.R793MarkerTranspose

open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R788OrdinaryPointDecomposition
noncomputable section

variable {F : Type*} [CommRing F]

theorem order_127 : order (127 : Fin 1024) = 1023 := by decide

theorem marker_eq_unit : marker (F := F) = unitVector 127 := by
  funext r
  by_cases hr : r < 1024
  · have hiff : order (⟨r, hr⟩ : Fin 1024) = 1023 ↔ r = 127 := by
      constructor
      · intro h
        have hj : (⟨r, hr⟩ : Fin 1024) = 127 := order.injective (by simpa [order_127] using h)
        exact congrArg Fin.val hj
      · intro h
        subst r
        simpa using order_127
    simp [marker, extendFin1024, unitVector, hr, hiff]
  · simp [marker, extendFin1024, unitVector, hr]

theorem even_marker_zero :
    (fun i : Nat => unitVector (F := F) 127 (2*i)) = fun _ => 0 := by
  simpa using (unitVector_odd_even (F := F) 63)

theorem odd_marker :
    (fun i : Nat => unitVector (F := F) 127 (2*i+1)) = unitVector 63 := by
  simpa using (unitVector_odd_odd (F := F) 63)

theorem marker_transpose (half a b c : F) (r : Nat) :
    sourceChordTranspose half (marker (F := F)) a b c r =
      if r % 2 = 0 then c * unitVector 63 (r / 2)
      else a * unitVector 63 (r / 2) + b * sourceGather half (unitVector 63) (r / 2) := by
  rw [marker_eq_unit]
  unfold sourceChordTranspose
  rw [even_marker_zero, odd_marker]
  simp only [zeroExtend, unitVector, Function.comp_apply]
  -- The bounded lanes are respectively zero and the unit vector at index 63.
  have hzero : (zeroExtend 512 (fun _ : Nat => (0 : F))) = fun _ => 0 := by
    funext i
    simp [zeroExtend]
  have hunit : zeroExtend 512 (unitVector (F := F) 63) = unitVector 63 :=
    zeroExtend_unit 512 63 (by omega)
  rw [hzero, hunit]
  unfold interleave chordDualEven chordDualOdd
  simp [hzero]

#print axioms order_127
#print axioms marker_eq_unit
#print axioms marker_transpose

end
end AspisV8R19.R793MarkerTranspose
