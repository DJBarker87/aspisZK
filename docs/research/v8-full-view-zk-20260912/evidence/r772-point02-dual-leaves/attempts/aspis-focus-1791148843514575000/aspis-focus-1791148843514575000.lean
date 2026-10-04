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

namespace AspisV8R19.R772Point02DualLeavesChunk12
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.R750WitnessPointSupport
open AspisR19.TwoSwapSourceTable
noncomputable section
set_option autoImplicit false
variable {F : Type*} [CommRing F]

/-- Transport at original index 931, point p0. -/
theorem p0_transport_zero_original_931 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (931 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 931 (by decide)
#print axioms p0_transport_zero_original_931

/-- Transport at original index 931, point p2. -/
theorem p2_transport_zero_original_931 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (931 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 931 (by decide)
#print axioms p2_transport_zero_original_931

/-- Transport at original index 947, point p0. -/
theorem p0_transport_zero_original_947 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (947 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 947 (by decide)
#print axioms p0_transport_zero_original_947

/-- Transport at original index 947, point p2. -/
theorem p2_transport_zero_original_947 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (947 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 947 (by decide)
#print axioms p2_transport_zero_original_947

/-- Transport at original index 963, point p0. -/
theorem p0_transport_zero_original_963 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (963 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 963 (by decide)
#print axioms p0_transport_zero_original_963

/-- Transport at original index 963, point p2. -/
theorem p2_transport_zero_original_963 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (963 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 963 (by decide)
#print axioms p2_transport_zero_original_963

/-- Transport at original index 979, point p0. -/
theorem p0_transport_zero_original_979 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (979 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 979 (by decide)
#print axioms p0_transport_zero_original_979

/-- Transport at original index 979, point p2. -/
theorem p2_transport_zero_original_979 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (979 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 979 (by decide)
#print axioms p2_transport_zero_original_979

/-- Transport at original index 995, point p0. -/
theorem p0_transport_zero_original_995 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (995 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 995 (by decide)
#print axioms p0_transport_zero_original_995

/-- Transport at original index 995, point p2. -/
theorem p2_transport_zero_original_995 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (995 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 995 (by decide)
#print axioms p2_transport_zero_original_995

/-- Transport at original index 1011, point p0. -/
theorem p0_transport_zero_original_1011 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (1011 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 1011 (by decide)
#print axioms p0_transport_zero_original_1011

/-- Transport at original index 1011, point p2. -/
theorem p2_transport_zero_original_1011 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (1011 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 1011 (by decide)
#print axioms p2_transport_zero_original_1011

/-- Transport at original index 0, point p0. -/
theorem p0_transport_zero_original_0 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (0 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 0 (by decide)
#print axioms p0_transport_zero_original_0

/-- Transport at original index 0, point p2. -/
theorem p2_transport_zero_original_0 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (0 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 0 (by decide)
#print axioms p2_transport_zero_original_0

/-- Transport at original index 33, point p0. -/
theorem p0_transport_zero_original_33 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (33 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 33 (by decide)
#print axioms p0_transport_zero_original_33

/-- Transport at original index 33, point p2. -/
theorem p2_transport_zero_original_33 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (33 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 33 (by decide)
#print axioms p2_transport_zero_original_33

/-- Transport at original index 49, point p0. -/
theorem p0_transport_zero_original_49 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (49 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 49 (by decide)
#print axioms p0_transport_zero_original_49

/-- Transport at original index 49, point p2. -/
theorem p2_transport_zero_original_49 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (49 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 49 (by decide)
#print axioms p2_transport_zero_original_49

/-- Transport at original index 65, point p0. -/
theorem p0_transport_zero_original_65 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (65 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 65 (by decide)
#print axioms p0_transport_zero_original_65

/-- Transport at original index 65, point p2. -/
theorem p2_transport_zero_original_65 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (65 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 65 (by decide)
#print axioms p2_transport_zero_original_65

/-- Transport at original index 81, point p0. -/
theorem p0_transport_zero_original_81 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (81 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 81 (by decide)
#print axioms p0_transport_zero_original_81

/-- Transport at original index 81, point p2. -/
theorem p2_transport_zero_original_81 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (81 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 81 (by decide)
#print axioms p2_transport_zero_original_81

/-- Transport at original index 97, point p0. -/
theorem p0_transport_zero_original_97 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (97 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 97 (by decide)
#print axioms p0_transport_zero_original_97

/-- Transport at original index 97, point p2. -/
theorem p2_transport_zero_original_97 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (97 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 97 (by decide)
#print axioms p2_transport_zero_original_97

/-- Transport at original index 113, point p0. -/
theorem p0_transport_zero_original_113 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (113 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 113 (by decide)
#print axioms p0_transport_zero_original_113

/-- Transport at original index 113, point p2. -/
theorem p2_transport_zero_original_113 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (113 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 113 (by decide)
#print axioms p2_transport_zero_original_113

/-- Transport at original index 129, point p0. -/
theorem p0_transport_zero_original_129 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (129 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 129 (by decide)
#print axioms p0_transport_zero_original_129

/-- Transport at original index 129, point p2. -/
theorem p2_transport_zero_original_129 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (129 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 129 (by decide)
#print axioms p2_transport_zero_original_129

/-- Transport at original index 145, point p0. -/
theorem p0_transport_zero_original_145 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (145 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 145 (by decide)
#print axioms p0_transport_zero_original_145

/-- Transport at original index 145, point p2. -/
theorem p2_transport_zero_original_145 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (145 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 145 (by decide)
#print axioms p2_transport_zero_original_145

/-- Transport at original index 161, point p0. -/
theorem p0_transport_zero_original_161 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (161 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 161 (by decide)
#print axioms p0_transport_zero_original_161

/-- Transport at original index 161, point p2. -/
theorem p2_transport_zero_original_161 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (161 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 161 (by decide)
#print axioms p2_transport_zero_original_161

end
end AspisV8R19.R772Point02DualLeavesChunk12
