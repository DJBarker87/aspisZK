import AspisV8R19.R750WitnessPointSupport
import AspisV8R19.R752SharedWitnessPointSupport
import AspisV8R19.TwoSwapSourceTable
import AspisV8R16.TransportDual

namespace AspisV8R19.R771Point02Transport
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.SourceStatementPoints
open AspisR19.R750WitnessPointSupport
open AspisR19.TwoSwapSourceTable
noncomputable section
set_option autoImplicit false
variable {F : Type*} [CommRing F]

def point0 : Fin 10 → F := points (zFin10 (F := F)) 0
def point2 : Fin 10 → F := points (zFin10 (F := F)) 2

theorem point0_pivot_basis_zero : sourcePointBasis point0 1023 = 0 := by
  exact R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 1023
    (Or.inr (Or.inr (by decide)))

theorem point2_pivot_basis_zero : sourcePointBasis point2 1023 = 0 := by
  exact R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 1023
    (Or.inr (Or.inr (by decide)))

/-- A zero basis value at the erased pivot removes the correction branch of
`transportDual` for every index. -/
theorem transportDual_eq_basis_of_pivot_zero (point : Fin 10 → F)
    (hpivot : sourcePointBasis point 1023 = 0) (j : Fin 1024) :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis point k.val) j =
      sourcePointBasis point (order j).val := by
  unfold AspisV8R16.transportDual
  by_cases h : order j ∈ inactive.erase (1023 : Fin 1024)
  · simp [h, hpivot]
  · simp [h]

theorem point0_transport_exact (j : Fin 1024) :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis point0 k.val) j =
      sourcePointBasis point0 (order j).val :=
  transportDual_eq_basis_of_pivot_zero point0 point0_pivot_basis_zero j

theorem point2_transport_exact (j : Fin 1024) :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis point2 k.val) j =
      sourcePointBasis point2 (order j).val :=
  transportDual_eq_basis_of_pivot_zero point2 point2_pivot_basis_zero j

#print axioms point0_pivot_basis_zero
#print axioms point2_pivot_basis_zero
#print axioms transportDual_eq_basis_of_pivot_zero
#print axioms point0_transport_exact
#print axioms point2_transport_exact
end
end AspisV8R19.R771Point02Transport
