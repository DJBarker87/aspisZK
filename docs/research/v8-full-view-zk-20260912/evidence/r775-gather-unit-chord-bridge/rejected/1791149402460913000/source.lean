import AspisV8R17.ScatterDual
import AspisV8R17.WeightedScatter

set_option autoImplicit false
namespace AspisV8R19.R775GatherUnitChordBridge
open AspisV8R17
open scoped BigOperators
noncomputable section
variable {F : Type*} [CommRing F]

theorem sourceGather_unitVector_eq_sparseX (half : F) (r j : Nat) :
    sourceGather half (unitVector r) j = sparseX half j r := by
  unfold sourceGather sparseX sparseVector unitVector
  apply congrArg (fun xs : List F => xs.sum)
  apply List.map_congr_left
  intro e he
  by_cases h : e.1 = r
  · simp [unitVector, h]
  · have hr : r ≠ e.1 := fun h' => h h'.symm
    simp [unitVector, h, hr]

theorem sourceGather_sourceGather_unitVector_eq_sparseXX (half : F) (r j : Nat) :
    sourceGather half (fun i => sourceGather half (unitVector r) i) j = sparseXX half j r := by
  change (((weightedIndexLoop half 10 j 0 1).getD []).map
      (fun e => e.2 * sourceGather half (unitVector r) e.1)).sum = _
  unfold sparseXX
  apply List.sum_congr rfl
  intro e he
  rw [sourceGather_unitVector_eq_sparseX half r e.1]

theorem sourceChord_unit_even_sourceGather (half : F) (j r : Nat) (hj : j<512) (a b c : F) :
    sourceChord half (unitVector (2*j)) a b c r =
      if r%2=0 then a*unitVector j (r/2)+b*sourceGather half (unitVector (r/2)) j
      else c*unitVector j (r/2) := by
  rw [sourceChord_unit_even half j r hj a b c]
  rw [← sourceGather_unitVector_eq_sparseX half (r/2) j]

theorem sourceChord_unit_odd_sourceGather (half : F) (j r : Nat) (hj : j<512) (a b c : F) :
    sourceChord half (unitVector (2*j+1)) a b c r =
      if r%2=0 then c*(unitVector j (r/2)-
          sourceGather half (fun i => sourceGather half (unitVector (r/2)) i) j)
      else a*unitVector j (r/2)+b*sourceGather half (unitVector (r/2)) j := by
  rw [sourceChord_unit_odd half j r hj a b c]
  rw [← sourceGather_sourceGather_unitVector_eq_sparseXX half (r/2) j,
      ← sourceGather_unitVector_eq_sparseX half (r/2) j]

#print axioms sourceGather_unitVector_eq_sparseX
#print axioms sourceGather_sourceGather_unitVector_eq_sparseXX
#print axioms sourceChord_unit_even_sourceGather
#print axioms sourceChord_unit_odd_sourceGather
end
end AspisV8R19.R775GatherUnitChordBridge
