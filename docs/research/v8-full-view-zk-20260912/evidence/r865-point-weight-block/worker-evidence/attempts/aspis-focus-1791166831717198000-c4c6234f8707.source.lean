import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R754Point1GuardedTransport
import AspisV8R19.Point1GuardedChunk06

set_option autoImplicit false
namespace AspisV8R19.R865PointWeightBlock
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
abbrev M := ZMod 2147483647

def w1 (n : Nat) : M := AspisV8R19.R748JointWitnessPointEntry.w n

private theorem w1_value (n m : Nat) (hn : n < 1024) (hm : m < 1024)
    (ho : order (⟨n, hn⟩ : Fin 1024) = ⟨m, hm⟩)
    (hmem : (⟨m, hm⟩ : Fin 1024) ∈ inactive.erase (1023 : Fin 1024)) :
    w1 n = (576 : M) := by
  let j : Fin 1024 := ⟨n, hn⟩
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hw := AspisR19.R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [w1, j] using hw

theorem w1_387 : w1 387 = (576:M) := by
  apply w1_value 387 25 (by decide) (by decide)
  · decide
  · decide

theorem w1_388 : w1 388 = (576:M) := by
  apply w1_value 388 40 (by decide) (by decide)
  · decide
  · decide

#print axioms w1_387
#print axioms w1_388
end AspisV8R19.R865PointWeightBlock
