import AspisV8R19.R812BlockSixP2LowerZeros
import AspisV8R19.R812BlockSixP0LowerZeros
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R807SourceBlock01Binding

set_option autoImplicit false
namespace AspisV8R19.R820SupplementaryLowerZero
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R812BlockSixP2LowerZeros
open AspisV8R19.R812BlockSixP0LowerZeros

 theorem block_label_lt_six_implies_lt35 (j : Fin 222) (h : blockLabel j < (6 : Fin 41)) : j.val < 35 := by
  decide

theorem p2_lower_zero (j : Fin 222) (h : blockLabel j < (6 : Fin 41)) :
    fixedSourceMatrix (AspisV8R19.R803LiteralSupplementaryEntries.pointPosition 2) (colOrder j) = 0 := by
  let j35 : Fin 35 := ⟨j.val, block_label_lt_six_implies_lt35 j h⟩
  have hj : (⟨j.val, by omega⟩ : Fin 222) = j := Fin.ext rfl
  have hc := congrFun AspisV8R19.R812BlockSixP2LowerZeros.lower_columns_exact j35
  calc
    fixedSourceMatrix (AspisV8R19.R803LiteralSupplementaryEntries.pointPosition 2) (colOrder j) =
      fixedSourceMatrix (AspisV8R19.R803LiteralSupplementaryEntries.pointPosition 2) (colOrder (⟨j.val, by omega⟩ : Fin 222)) := by rw [hj]
    _ = fixedSourceMatrix (AspisV8R19.R803LiteralSupplementaryEntries.pointPosition 2)
      (AspisV8R19.R812BlockSixP2LowerZeros.lowerColumns j35) := by rw [hc]
    _ = 0 := AspisV8R19.R812BlockSixP2LowerZeros.source_p2_lower_zero j35

theorem p0_lower_zero (j : Fin 222) (h : blockLabel j < (6 : Fin 41)) :
    fixedSourceMatrix (AspisV8R19.R803LiteralSupplementaryEntries.pointPosition 0) (colOrder j) = 0 := by
  let j35 : Fin 35 := ⟨j.val, block_label_lt_six_implies_lt35 j h⟩
  have hj : (⟨j.val, by omega⟩ : Fin 222) = j := Fin.ext rfl
  have hc := congrFun AspisV8R19.R812BlockSixP0LowerZeros.lower_columns_exact j35
  calc
    fixedSourceMatrix (AspisV8R19.R803LiteralSupplementaryEntries.pointPosition 0) (colOrder j) =
      fixedSourceMatrix (AspisV8R19.R803LiteralSupplementaryEntries.pointPosition 0) (colOrder (⟨j.val, by omega⟩ : Fin 222)) := by rw [hj]
    _ = fixedSourceMatrix (AspisV8R19.R803LiteralSupplementaryEntries.pointPosition 0)
      (AspisV8R19.R812BlockSixP0LowerZeros.lowerColumns j35) := by rw [hc]
    _ = 0 := AspisV8R19.R812BlockSixP0LowerZeros.source_p0_lower_zero j35

#print axioms block_label_lt_six_implies_lt35
#print axioms p2_lower_zero
#print axioms p0_lower_zero
end AspisV8R19.R820SupplementaryLowerZero
