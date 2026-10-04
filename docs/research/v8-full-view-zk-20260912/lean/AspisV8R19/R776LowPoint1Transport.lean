import AspisV8R19.R755Point1BasisTransport
import AspisV8R19.R752SharedWitnessPointSupport
namespace AspisV8R19.R776LowPoint1Transport
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R748JointWitnessPointEntry
noncomputable section
set_option maxRecDepth 4096

def lowIndex (j : Fin 96) : Fin 1024 := ⟨j.val,by omega⟩

theorem low_guard : ∀ j : Fin 96,
    ((((order (lowIndex j)).val >>> 9) &&& 1) = 0) ∨
      ((((order (lowIndex j)).val >>> 8) &&& 1) = 0) := by decide

theorem low_member : ∀ j : Fin 96,
    order (lowIndex j) ∈ inactive.erase (1023 : Fin 1024) := by decide

theorem low_w_constant (j : Fin 96) : w j.val = (576 : M) := by
  have hb : sourcePointBasis point (order (lowIndex j)).val = (0:M) :=
    R752SharedWitnessPointSupport.point1_source_basis_zero _ (low_guard j)
  have h := R755Point1BasisTransport.w_from_basis (lowIndex j) 0 hb
  rw [if_pos (low_member j), zero_add] at h
  exact h

#print axioms low_guard
#print axioms low_member
#print axioms low_w_constant
end
end AspisV8R19.R776LowPoint1Transport
