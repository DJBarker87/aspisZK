import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R754Point1GuardedTransport
import AspisV8R19.Point1GuardedChunk06
import AspisV8R19.T163SourceTable
import AspisV8R19.TwoSwapSourceTable

set_option autoImplicit false
namespace AspisV8R19.R865PointWeightBlock
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
abbrev M := ZMod 2147483647

def w1 (n : Nat) : M := AspisV8R19.R748JointWitnessPointEntry.w n

theorem w1_387 : w1 387 = (576:M) := by
  let j : Fin 1024 := ⟨387, by omega⟩
  have ho : order j = (25 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (25 : Fin 1024) ∈ inactive.erase (1023 : Fin 1024) := by
    change (25 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (25 : Fin 1024) ∈ T163SourceTable.inactive
      rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := AspisR19.R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [w1, j] using hw

theorem w1_388 : w1 388 = (576:M) := by
  let j : Fin 1024 := ⟨388, by omega⟩
  have ho : order j = (40 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (40 : Fin 1024) ∈ inactive.erase (1023 : Fin 1024) := by
    change (40 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (40 : Fin 1024) ∈ T163SourceTable.inactive
      rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := AspisR19.R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [w1, j] using hw

#print axioms w1_387
#print axioms w1_388
end AspisV8R19.R865PointWeightBlock
