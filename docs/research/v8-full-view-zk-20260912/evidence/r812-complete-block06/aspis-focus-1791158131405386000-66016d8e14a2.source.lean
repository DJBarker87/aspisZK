import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R812P2StaticLowChunk00
import AspisV8R19.R812P2StaticLowChunk01
import AspisV8R19.R812P2StaticLowChunk02
import AspisV8R19.R812P2StaticLowChunk03
import AspisV8R19.R812P2StaticLowChunk04
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812BlockSixP2LowerZeros
open AspisV8R19.R807SourceBlock01Binding AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R812SourceBlock06P2StaticLowChunk00
open AspisV8R19.R812SourceBlock06P2StaticLowChunk01
open AspisV8R19.R812SourceBlock06P2StaticLowChunk02
open AspisV8R19.R812SourceBlock06P2StaticLowChunk03
open AspisV8R19.R812SourceBlock06P2StaticLowChunk04
noncomputable section
def lowerColumns : Fin 35 → Fin 222 := ![214,215,216,217,218,219,34,31,32,33,23,24,25,26,27,28,29,30,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,35]
theorem lower_columns_exact : (fun j : Fin 35 => colOrder (⟨j.val, by omega⟩ : Fin 222)) = lowerColumns := by funext j; fin_cases j <;> rfl
theorem source_p2_lower_zero (j : Fin 35) : fixedSourceMatrix (AspisV8R19.R803LiteralSupplementaryEntries.pointPosition 2) (lowerColumns j) = 0 := by
  fin_cases j
  · simpa [lowerColumns] using static_p2_d023_s0_flat00
  · simpa [lowerColumns] using static_p2_d023_s1_flat01
  · simpa [lowerColumns] using static_p2_d023_s2_flat02
  · simpa [lowerColumns] using static_p2_d024_s0_flat03
  · simpa [lowerColumns] using static_p2_d024_s1_flat04
  · simpa [lowerColumns] using static_p2_d024_s2_flat05
  · simpa [lowerColumns] using static_p2_d046_s0_flat06
  · simpa [lowerColumns] using static_p2_d044_s0_flat07
  · simpa [lowerColumns] using static_p2_d044_s1_flat08
  · simpa [lowerColumns] using static_p2_d045_s0_flat09
  · simpa [lowerColumns] using static_p2_d040_s0_flat10
  · simpa [lowerColumns] using static_p2_d040_s1_flat11
  · simpa [lowerColumns] using static_p2_d041_s0_flat12
  · simpa [lowerColumns] using static_p2_d041_s1_flat13
  · simpa [lowerColumns] using static_p2_d042_s0_flat14
  · simpa [lowerColumns] using static_p2_d042_s1_flat15
  · simpa [lowerColumns] using static_p2_d043_s0_flat16
  · simpa [lowerColumns] using static_p2_d043_s1_flat17
  · simpa [lowerColumns] using static_p2_d032_s0_flat18
  · simpa [lowerColumns] using static_p2_d032_s1_flat19
  · simpa [lowerColumns] using static_p2_d033_s0_flat20
  · simpa [lowerColumns] using static_p2_d033_s1_flat21
  · simpa [lowerColumns] using static_p2_d034_s0_flat22
  · simpa [lowerColumns] using static_p2_d034_s1_flat23
  · simpa [lowerColumns] using static_p2_d035_s0_flat24
  · simpa [lowerColumns] using static_p2_d035_s1_flat25
  · simpa [lowerColumns] using static_p2_d036_s0_flat26
  · simpa [lowerColumns] using static_p2_d036_s1_flat27
  · simpa [lowerColumns] using static_p2_d037_s0_flat28
  · simpa [lowerColumns] using static_p2_d037_s1_flat29
  · simpa [lowerColumns] using static_p2_d038_s0_flat30
  · simpa [lowerColumns] using static_p2_d038_s1_flat31
  · simpa [lowerColumns] using static_p2_d039_s0_flat32
  · simpa [lowerColumns] using static_p2_d039_s1_flat33
  · simpa [lowerColumns] using static_p2_d047_s1_flat34
#print axioms source_p2_lower_zero
end
end AspisV8R19.R812BlockSixP2LowerZeros
