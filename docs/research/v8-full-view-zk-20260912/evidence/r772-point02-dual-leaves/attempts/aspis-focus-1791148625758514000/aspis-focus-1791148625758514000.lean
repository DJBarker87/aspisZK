import AspisV8R19.R771Point02Transport
import AspisV8R19.R768Point02BasisLeaves
import AspisV8R19.R768Point02LeavesChunk00
import AspisV8R19.R750WitnessPointSupport
import AspisV8R19.R752SharedWitnessPointSupport

namespace AspisV8R19.R772Point02DualLeaves
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.SourceStatementPoints
open AspisR19.R750WitnessPointSupport
open AspisR19.TwoSwapSourceTable
noncomputable section
set_option autoImplicit false
variable {F : Type*} [CommRing F]

/-- Reindex the all-index transport theorem from input coordinates to original
source coordinates. -/
theorem point0_transport_original (i : Fin 1024) :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm i) =
      sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) i.val := by
  rw [AspisV8R19.R771Point02Transport.point0_transport_exact]
  simp

theorem point2_transport_original (i : Fin 1024) :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm i) =
      sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) i.val := by
  rw [AspisV8R19.R771Point02Transport.point2_transport_exact]
  simp

theorem point0_guard14_transport_zero :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (14 : Fin 1024)) = 0 := by
  rw [point0_transport_original]
  apply R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 14
  exact Or.inr (Or.inr (by decide))

theorem point2_guard14_transport_zero :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (14 : Fin 1024)) = 0 := by
  rw [point2_transport_original]
  apply R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 14
  exact Or.inr (Or.inr (by decide))

theorem point0_candidate780_transport_exact :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (780 : Fin 1024)) =
      ([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List F).prod := by
  rw [point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using
    AspisV8R19.R768Point02LeavesChunk00.p0_basis_780_exact (F := F)

theorem point2_candidate780_transport_exact :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (780 : Fin 1024)) =
      ([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List F).prod := by
  rw [point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using
    AspisV8R19.R768Point02LeavesChunk00.p2_basis_780_exact (F := F)

#print axioms point0_transport_original
#print axioms point2_transport_original
#print axioms point0_guard14_transport_zero
#print axioms point2_guard14_transport_zero
#print axioms point0_candidate780_transport_exact
#print axioms point2_candidate780_transport_exact
end
end AspisV8R19.R772Point02DualLeaves
