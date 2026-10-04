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

namespace AspisV8R19.R772Point02DualLeavesChunk22
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.R750WitnessPointSupport
open AspisR19.TwoSwapSourceTable
noncomputable section
set_option autoImplicit false
variable {F : Type*} [CommRing F]

/-- Transport at original index 891, point p0. -/
theorem p0_transport_zero_original_891 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (891 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 891 (by decide)
#print axioms p0_transport_zero_original_891

/-- Transport at original index 891, point p2. -/
theorem p2_transport_zero_original_891 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (891 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 891 (by decide)
#print axioms p2_transport_zero_original_891

/-- Transport at original index 922, point p0. -/
theorem p0_transport_zero_original_922 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (922 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 922 (by decide)
#print axioms p0_transport_zero_original_922

/-- Transport at original index 922, point p2. -/
theorem p2_transport_zero_original_922 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (922 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 922 (by decide)
#print axioms p2_transport_zero_original_922

/-- Transport at original index 938, point p0. -/
theorem p0_transport_zero_original_938 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (938 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 938 (by decide)
#print axioms p0_transport_zero_original_938

/-- Transport at original index 938, point p2. -/
theorem p2_transport_zero_original_938 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (938 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 938 (by decide)
#print axioms p2_transport_zero_original_938

/-- Transport at original index 954, point p0. -/
theorem p0_transport_zero_original_954 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (954 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 954 (by decide)
#print axioms p0_transport_zero_original_954

/-- Transport at original index 954, point p2. -/
theorem p2_transport_zero_original_954 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (954 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 954 (by decide)
#print axioms p2_transport_zero_original_954

/-- Transport at original index 970, point p0. -/
theorem p0_transport_zero_original_970 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (970 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 970 (by decide)
#print axioms p0_transport_zero_original_970

/-- Transport at original index 970, point p2. -/
theorem p2_transport_zero_original_970 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (970 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 970 (by decide)
#print axioms p2_transport_zero_original_970

/-- Transport at original index 986, point p0. -/
theorem p0_transport_zero_original_986 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (986 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 986 (by decide)
#print axioms p0_transport_zero_original_986

/-- Transport at original index 986, point p2. -/
theorem p2_transport_zero_original_986 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (986 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 986 (by decide)
#print axioms p2_transport_zero_original_986

/-- Transport at original index 1002, point p0. -/
theorem p0_transport_zero_original_1002 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (1002 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 1002 (by decide)
#print axioms p0_transport_zero_original_1002

/-- Transport at original index 1002, point p2. -/
theorem p2_transport_zero_original_1002 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (1002 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 1002 (by decide)
#print axioms p2_transport_zero_original_1002

/-- Transport at original index 1018, point p0. -/
theorem p0_transport_zero_original_1018 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (1018 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 1018 (by decide)
#print axioms p0_transport_zero_original_1018

/-- Transport at original index 1018, point p2. -/
theorem p2_transport_zero_original_1018 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (1018 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 1018 (by decide)
#print axioms p2_transport_zero_original_1018

/-- Transport at original index 918, point p0. -/
theorem p0_transport_zero_original_918 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (918 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 918 (by decide)
#print axioms p0_transport_zero_original_918

/-- Transport at original index 918, point p2. -/
theorem p2_transport_zero_original_918 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (918 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 918 (by decide)
#print axioms p2_transport_zero_original_918

/-- Transport at original index 934, point p0. -/
theorem p0_transport_zero_original_934 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (934 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 934 (by decide)
#print axioms p0_transport_zero_original_934

/-- Transport at original index 934, point p2. -/
theorem p2_transport_zero_original_934 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (934 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 934 (by decide)
#print axioms p2_transport_zero_original_934

/-- Transport at original index 950, point p0. -/
theorem p0_transport_zero_original_950 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (950 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 950 (by decide)
#print axioms p0_transport_zero_original_950

/-- Transport at original index 950, point p2. -/
theorem p2_transport_zero_original_950 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (950 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 950 (by decide)
#print axioms p2_transport_zero_original_950

/-- Transport at original index 966, point p0. -/
theorem p0_transport_zero_original_966 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (966 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 966 (by decide)
#print axioms p0_transport_zero_original_966

/-- Transport at original index 966, point p2. -/
theorem p2_transport_zero_original_966 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (966 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 966 (by decide)
#print axioms p2_transport_zero_original_966

/-- Transport at original index 982, point p0. -/
theorem p0_transport_zero_original_982 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (982 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 982 (by decide)
#print axioms p0_transport_zero_original_982

/-- Transport at original index 982, point p2. -/
theorem p2_transport_zero_original_982 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (982 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 982 (by decide)
#print axioms p2_transport_zero_original_982

/-- Transport at original index 998, point p0. -/
theorem p0_transport_zero_original_998 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (998 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 998 (by decide)
#print axioms p0_transport_zero_original_998

/-- Transport at original index 998, point p2. -/
theorem p2_transport_zero_original_998 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (998 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 998 (by decide)
#print axioms p2_transport_zero_original_998

/-- Transport at original index 1014, point p0. -/
theorem p0_transport_zero_original_1014 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (1014 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 1014 (by decide)
#print axioms p0_transport_zero_original_1014

/-- Transport at original index 1014, point p2. -/
theorem p2_transport_zero_original_1014 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (1014 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 1014 (by decide)
#print axioms p2_transport_zero_original_1014

/-- Transport at original index 1015, point p0. -/
theorem p0_transport_zero_original_1015 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (1015 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 1015 (by decide)
#print axioms p0_transport_zero_original_1015

/-- Transport at original index 1015, point p2. -/
theorem p2_transport_zero_original_1015 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (1015 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 1015 (by decide)
#print axioms p2_transport_zero_original_1015

end
end AspisV8R19.R772Point02DualLeavesChunk22
