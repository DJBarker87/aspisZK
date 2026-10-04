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

namespace AspisV8R19.R772Point02DualLeavesChunk16
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.R750WitnessPointSupport
open AspisR19.TwoSwapSourceTable
noncomputable section
set_option autoImplicit false
variable {F : Type*} [CommRing F]

/-- Transport at original index 28, point p0. -/
theorem p0_transport_zero_original_28 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (28 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 28 (by decide)
#print axioms p0_transport_zero_original_28

/-- Transport at original index 28, point p2. -/
theorem p2_transport_zero_original_28 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (28 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 28 (by decide)
#print axioms p2_transport_zero_original_28

/-- Transport at original index 44, point p0. -/
theorem p0_transport_zero_original_44 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (44 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 44 (by decide)
#print axioms p0_transport_zero_original_44

/-- Transport at original index 44, point p2. -/
theorem p2_transport_zero_original_44 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (44 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 44 (by decide)
#print axioms p2_transport_zero_original_44

/-- Transport at original index 60, point p0. -/
theorem p0_transport_zero_original_60 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (60 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 60 (by decide)
#print axioms p0_transport_zero_original_60

/-- Transport at original index 60, point p2. -/
theorem p2_transport_zero_original_60 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (60 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 60 (by decide)
#print axioms p2_transport_zero_original_60

/-- Transport at original index 76, point p0. -/
theorem p0_transport_zero_original_76 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (76 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 76 (by decide)
#print axioms p0_transport_zero_original_76

/-- Transport at original index 76, point p2. -/
theorem p2_transport_zero_original_76 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (76 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 76 (by decide)
#print axioms p2_transport_zero_original_76

/-- Transport at original index 92, point p0. -/
theorem p0_transport_zero_original_92 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (92 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 92 (by decide)
#print axioms p0_transport_zero_original_92

/-- Transport at original index 92, point p2. -/
theorem p2_transport_zero_original_92 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (92 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 92 (by decide)
#print axioms p2_transport_zero_original_92

/-- Transport at original index 108, point p0. -/
theorem p0_transport_zero_original_108 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (108 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 108 (by decide)
#print axioms p0_transport_zero_original_108

/-- Transport at original index 108, point p2. -/
theorem p2_transport_zero_original_108 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (108 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 108 (by decide)
#print axioms p2_transport_zero_original_108

/-- Transport at original index 124, point p0. -/
theorem p0_transport_zero_original_124 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (124 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 124 (by decide)
#print axioms p0_transport_zero_original_124

/-- Transport at original index 124, point p2. -/
theorem p2_transport_zero_original_124 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (124 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 124 (by decide)
#print axioms p2_transport_zero_original_124

/-- Transport at original index 140, point p0. -/
theorem p0_transport_zero_original_140 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (140 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 140 (by decide)
#print axioms p0_transport_zero_original_140

/-- Transport at original index 140, point p2. -/
theorem p2_transport_zero_original_140 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (140 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 140 (by decide)
#print axioms p2_transport_zero_original_140

/-- Transport at original index 156, point p0. -/
theorem p0_transport_zero_original_156 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (156 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 156 (by decide)
#print axioms p0_transport_zero_original_156

/-- Transport at original index 156, point p2. -/
theorem p2_transport_zero_original_156 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (156 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 156 (by decide)
#print axioms p2_transport_zero_original_156

/-- Transport at original index 172, point p0. -/
theorem p0_transport_zero_original_172 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (172 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 172 (by decide)
#print axioms p0_transport_zero_original_172

/-- Transport at original index 172, point p2. -/
theorem p2_transport_zero_original_172 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (172 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 172 (by decide)
#print axioms p2_transport_zero_original_172

/-- Transport at original index 188, point p0. -/
theorem p0_transport_zero_original_188 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (188 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 188 (by decide)
#print axioms p0_transport_zero_original_188

/-- Transport at original index 188, point p2. -/
theorem p2_transport_zero_original_188 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (188 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 188 (by decide)
#print axioms p2_transport_zero_original_188

/-- Transport at original index 204, point p0. -/
theorem p0_transport_zero_original_204 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (204 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 204 (by decide)
#print axioms p0_transport_zero_original_204

/-- Transport at original index 204, point p2. -/
theorem p2_transport_zero_original_204 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (204 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 204 (by decide)
#print axioms p2_transport_zero_original_204

/-- Transport at original index 220, point p0. -/
theorem p0_transport_zero_original_220 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (220 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 220 (by decide)
#print axioms p0_transport_zero_original_220

/-- Transport at original index 220, point p2. -/
theorem p2_transport_zero_original_220 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (220 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 220 (by decide)
#print axioms p2_transport_zero_original_220

/-- Transport at original index 236, point p0. -/
theorem p0_transport_zero_original_236 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (236 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 236 (by decide)
#print axioms p0_transport_zero_original_236

/-- Transport at original index 236, point p2. -/
theorem p2_transport_zero_original_236 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (236 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 236 (by decide)
#print axioms p2_transport_zero_original_236

/-- Transport at original index 252, point p0. -/
theorem p0_transport_zero_original_252 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (252 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 252 (by decide)
#print axioms p0_transport_zero_original_252

/-- Transport at original index 252, point p2. -/
theorem p2_transport_zero_original_252 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (252 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 252 (by decide)
#print axioms p2_transport_zero_original_252

/-- Transport at original index 268, point p0. -/
theorem p0_transport_zero_original_268 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (268 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 268 (by decide)
#print axioms p0_transport_zero_original_268

/-- Transport at original index 268, point p2. -/
theorem p2_transport_zero_original_268 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (268 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 268 (by decide)
#print axioms p2_transport_zero_original_268

end
end AspisV8R19.R772Point02DualLeavesChunk16
