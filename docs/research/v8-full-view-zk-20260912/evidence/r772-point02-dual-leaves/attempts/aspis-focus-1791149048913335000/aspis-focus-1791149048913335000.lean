import AspisV8R19.R772Point02DualLeaves
import AspisV8R19.R750WitnessPointSupport
import AspisV8R19.R752SharedWitnessPointSupport
import AspisV8R19.R768Point02LeavesChunk00
import AspisV8R19.R768Point02LeavesChunk01
import AspisV8R19.R768Point02LeavesChunk02
import AspisV8R19.R768Point02LeavesChunk03
import AspisV8R19.R768Point02LeavesChunk04
import AspisV8R19.R768Point02LeavesChunk05
import AspisV8R19.R768Point02LeavesChunk06
import AspisV8R19.R768Point02BasisLeaves

namespace AspisV8R19.R772Point02DualLeavesChunk32
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.R750WitnessPointSupport
open AspisR19.TwoSwapSourceTable
noncomputable section
set_option autoImplicit false
variable {F : Type*} [CommRing F]

/-- Transport at original index 928, point p0. -/
theorem p0_transport_exact_original_928 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (928 : Fin 1024)) =
      ([1, 1, 2, -2, 4, -1, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk05.p0_basis_928_exact (F := F)
#print axioms p0_transport_exact_original_928

/-- Transport at original index 928, point p2. -/
theorem p2_transport_exact_original_928 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (928 : Fin 1024)) =
      ([1, 1, 2, -2, 4, -1, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk05.p2_basis_928_exact (F := F)
#print axioms p2_transport_exact_original_928

/-- Transport at original index 944, point p0. -/
theorem p0_transport_exact_original_944 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (944 : Fin 1024)) =
      ([1, 1, 2, -2, 4, 2, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk05.p0_basis_944_exact (F := F)
#print axioms p0_transport_exact_original_944

/-- Transport at original index 944, point p2. -/
theorem p2_transport_exact_original_944 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (944 : Fin 1024)) =
      ([1, 1, 2, -2, 4, 2, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk05.p2_basis_944_exact (F := F)
#print axioms p2_transport_exact_original_944

/-- Transport at original index 960, point p0. -/
theorem p0_transport_exact_original_960 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (960 : Fin 1024)) =
      ([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk06.p0_basis_960_exact (F := F)
#print axioms p0_transport_exact_original_960

/-- Transport at original index 960, point p2. -/
theorem p2_transport_exact_original_960 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (960 : Fin 1024)) =
      ([1, 1, 2, 3, -3, -1, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk06.p2_basis_960_exact (F := F)
#print axioms p2_transport_exact_original_960

/-- Transport at original index 976, point p0. -/
theorem p0_transport_exact_original_976 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (976 : Fin 1024)) =
      ([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk06.p0_basis_976_exact (F := F)
#print axioms p0_transport_exact_original_976

/-- Transport at original index 976, point p2. -/
theorem p2_transport_exact_original_976 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (976 : Fin 1024)) =
      ([1, 1, 2, 3, -3, 2, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk06.p2_basis_976_exact (F := F)
#print axioms p2_transport_exact_original_976

/-- Transport at original index 992, point p0. -/
theorem p0_transport_exact_original_992 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (992 : Fin 1024)) =
      ([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk06.p0_basis_992_exact (F := F)
#print axioms p0_transport_exact_original_992

/-- Transport at original index 992, point p2. -/
theorem p2_transport_exact_original_992 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (992 : Fin 1024)) =
      ([1, 1, 2, 3, 4, -1, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk06.p2_basis_992_exact (F := F)
#print axioms p2_transport_exact_original_992

end
end AspisV8R19.R772Point02DualLeavesChunk32
