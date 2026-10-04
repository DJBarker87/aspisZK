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

namespace AspisV8R19.R772Point02DualLeavesChunk15
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.R750WitnessPointSupport
open AspisR19.TwoSwapSourceTable
noncomputable section
set_option autoImplicit false
variable {F : Type*} [CommRing F]

/-- Transport at original index 641, point p0. -/
theorem p0_transport_zero_original_641 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (641 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 641 (by decide)
#print axioms p0_transport_zero_original_641

/-- Transport at original index 641, point p2. -/
theorem p2_transport_zero_original_641 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (641 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 641 (by decide)
#print axioms p2_transport_zero_original_641

/-- Transport at original index 657, point p0. -/
theorem p0_transport_zero_original_657 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (657 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 657 (by decide)
#print axioms p0_transport_zero_original_657

/-- Transport at original index 657, point p2. -/
theorem p2_transport_zero_original_657 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (657 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 657 (by decide)
#print axioms p2_transport_zero_original_657

/-- Transport at original index 673, point p0. -/
theorem p0_transport_zero_original_673 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (673 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 673 (by decide)
#print axioms p0_transport_zero_original_673

/-- Transport at original index 673, point p2. -/
theorem p2_transport_zero_original_673 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (673 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 673 (by decide)
#print axioms p2_transport_zero_original_673

/-- Transport at original index 689, point p0. -/
theorem p0_transport_zero_original_689 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (689 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 689 (by decide)
#print axioms p0_transport_zero_original_689

/-- Transport at original index 689, point p2. -/
theorem p2_transport_zero_original_689 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (689 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 689 (by decide)
#print axioms p2_transport_zero_original_689

/-- Transport at original index 705, point p0. -/
theorem p0_transport_zero_original_705 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (705 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 705 (by decide)
#print axioms p0_transport_zero_original_705

/-- Transport at original index 705, point p2. -/
theorem p2_transport_zero_original_705 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (705 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 705 (by decide)
#print axioms p2_transport_zero_original_705

/-- Transport at original index 721, point p0. -/
theorem p0_transport_zero_original_721 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (721 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 721 (by decide)
#print axioms p0_transport_zero_original_721

/-- Transport at original index 721, point p2. -/
theorem p2_transport_zero_original_721 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (721 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 721 (by decide)
#print axioms p2_transport_zero_original_721

/-- Transport at original index 737, point p0. -/
theorem p0_transport_zero_original_737 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (737 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 737 (by decide)
#print axioms p0_transport_zero_original_737

/-- Transport at original index 737, point p2. -/
theorem p2_transport_zero_original_737 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (737 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 737 (by decide)
#print axioms p2_transport_zero_original_737

/-- Transport at original index 753, point p0. -/
theorem p0_transport_zero_original_753 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (753 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 753 (by decide)
#print axioms p0_transport_zero_original_753

/-- Transport at original index 753, point p2. -/
theorem p2_transport_zero_original_753 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (753 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 753 (by decide)
#print axioms p2_transport_zero_original_753

/-- Transport at original index 1022, point p0. -/
theorem p0_transport_zero_original_1022 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (1022 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 1022 (by decide)
#print axioms p0_transport_zero_original_1022

/-- Transport at original index 1022, point p2. -/
theorem p2_transport_zero_original_1022 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (1022 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 1022 (by decide)
#print axioms p2_transport_zero_original_1022

/-- Transport at original index 926, point p0. -/
theorem p0_transport_zero_original_926 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (926 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 926 (by decide)
#print axioms p0_transport_zero_original_926

/-- Transport at original index 926, point p2. -/
theorem p2_transport_zero_original_926 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (926 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 926 (by decide)
#print axioms p2_transport_zero_original_926

/-- Transport at original index 942, point p0. -/
theorem p0_transport_zero_original_942 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (942 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 942 (by decide)
#print axioms p0_transport_zero_original_942

/-- Transport at original index 942, point p2. -/
theorem p2_transport_zero_original_942 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (942 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 942 (by decide)
#print axioms p2_transport_zero_original_942

/-- Transport at original index 958, point p0. -/
theorem p0_transport_zero_original_958 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (958 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 958 (by decide)
#print axioms p0_transport_zero_original_958

/-- Transport at original index 958, point p2. -/
theorem p2_transport_zero_original_958 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (958 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 958 (by decide)
#print axioms p2_transport_zero_original_958

/-- Transport at original index 974, point p0. -/
theorem p0_transport_zero_original_974 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (974 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 974 (by decide)
#print axioms p0_transport_zero_original_974

/-- Transport at original index 974, point p2. -/
theorem p2_transport_zero_original_974 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (974 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 974 (by decide)
#print axioms p2_transport_zero_original_974

/-- Transport at original index 990, point p0. -/
theorem p0_transport_zero_original_990 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (990 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 990 (by decide)
#print axioms p0_transport_zero_original_990

/-- Transport at original index 990, point p2. -/
theorem p2_transport_zero_original_990 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (990 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 990 (by decide)
#print axioms p2_transport_zero_original_990

/-- Transport at original index 1006, point p0. -/
theorem p0_transport_zero_original_1006 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (1006 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 1006 (by decide)
#print axioms p0_transport_zero_original_1006

/-- Transport at original index 1006, point p2. -/
theorem p2_transport_zero_original_1006 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (1006 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 1006 (by decide)
#print axioms p2_transport_zero_original_1006

/-- Transport at original index 12, point p0. -/
theorem p0_transport_zero_original_12 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (12 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 12 (by decide)
#print axioms p0_transport_zero_original_12

/-- Transport at original index 12, point p2. -/
theorem p2_transport_zero_original_12 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (12 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 12 (by decide)
#print axioms p2_transport_zero_original_12

end
end AspisV8R19.R772Point02DualLeavesChunk15
