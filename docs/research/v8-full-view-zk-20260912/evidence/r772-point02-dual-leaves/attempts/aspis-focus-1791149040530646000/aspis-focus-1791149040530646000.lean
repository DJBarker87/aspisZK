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

namespace AspisV8R19.R772Point02DualLeavesChunk30
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.R750WitnessPointSupport
open AspisR19.TwoSwapSourceTable
noncomputable section
set_option autoImplicit false
variable {F : Type*} [CommRing F]

/-- Transport at original index 776, point p0. -/
theorem p0_transport_exact_original_776 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (776 : Fin 1024)) =
      ([1, 1, -1, -2, -3, -1, 2, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk03.p0_basis_776_exact (F := F)
#print axioms p0_transport_exact_original_776

/-- Transport at original index 776, point p2. -/
theorem p2_transport_exact_original_776 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (776 : Fin 1024)) =
      ([1, 1, -1, -2, -3, -1, -1, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk03.p2_basis_776_exact (F := F)
#print axioms p2_transport_exact_original_776

/-- Transport at original index 777, point p0. -/
theorem p0_transport_exact_original_777 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (777 : Fin 1024)) =
      ([1, 1, -1, -2, -3, -1, 2, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk03.p0_basis_777_exact (F := F)
#print axioms p0_transport_exact_original_777

/-- Transport at original index 777, point p2. -/
theorem p2_transport_exact_original_777 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (777 : Fin 1024)) =
      ([1, 1, -1, -2, -3, -1, -1, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk03.p2_basis_777_exact (F := F)
#print axioms p2_transport_exact_original_777

/-- Transport at original index 792, point p0. -/
theorem p0_transport_exact_original_792 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (792 : Fin 1024)) =
      ([1, 1, -1, -2, -3, 2, 2, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk04.p0_basis_792_exact (F := F)
#print axioms p0_transport_exact_original_792

/-- Transport at original index 792, point p2. -/
theorem p2_transport_exact_original_792 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (792 : Fin 1024)) =
      ([1, 1, -1, -2, -3, 2, -1, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk04.p2_basis_792_exact (F := F)
#print axioms p2_transport_exact_original_792

/-- Transport at original index 904, point p0. -/
theorem p0_transport_exact_original_904 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (904 : Fin 1024)) =
      ([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk04.p0_basis_904_exact (F := F)
#print axioms p0_transport_exact_original_904

/-- Transport at original index 904, point p2. -/
theorem p2_transport_exact_original_904 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (904 : Fin 1024)) =
      ([1, 1, 2, -2, -3, -1, -1, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk04.p2_basis_904_exact (F := F)
#print axioms p2_transport_exact_original_904

/-- Transport at original index 905, point p0. -/
theorem p0_transport_exact_original_905 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (905 : Fin 1024)) =
      ([1, 1, 2, -2, -3, -1, 2, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk04.p0_basis_905_exact (F := F)
#print axioms p0_transport_exact_original_905

/-- Transport at original index 905, point p2. -/
theorem p2_transport_exact_original_905 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (905 : Fin 1024)) =
      ([1, 1, 2, -2, -3, -1, -1, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk04.p2_basis_905_exact (F := F)
#print axioms p2_transport_exact_original_905

/-- Transport at original index 920, point p0. -/
theorem p0_transport_exact_original_920 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (920 : Fin 1024)) =
      ([1, 1, 2, -2, -3, 2, 2, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk04.p0_basis_920_exact (F := F)
#print axioms p0_transport_exact_original_920

/-- Transport at original index 920, point p2. -/
theorem p2_transport_exact_original_920 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (920 : Fin 1024)) =
      ([1, 1, 2, -2, -3, 2, -1, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk04.p2_basis_920_exact (F := F)
#print axioms p2_transport_exact_original_920

/-- Transport at original index 936, point p0. -/
theorem p0_transport_exact_original_936 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (936 : Fin 1024)) =
      ([1, 1, 2, -2, 4, -1, 2, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk04.p0_basis_936_exact (F := F)
#print axioms p0_transport_exact_original_936

/-- Transport at original index 936, point p2. -/
theorem p2_transport_exact_original_936 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (936 : Fin 1024)) =
      ([1, 1, 2, -2, 4, -1, -1, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk04.p2_basis_936_exact (F := F)
#print axioms p2_transport_exact_original_936

/-- Transport at original index 952, point p0. -/
theorem p0_transport_exact_original_952 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (952 : Fin 1024)) =
      ([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk04.p0_basis_952_exact (F := F)
#print axioms p0_transport_exact_original_952

/-- Transport at original index 952, point p2. -/
theorem p2_transport_exact_original_952 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (952 : Fin 1024)) =
      ([1, 1, 2, -2, 4, 2, -1, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk04.p2_basis_952_exact (F := F)
#print axioms p2_transport_exact_original_952

/-- Transport at original index 968, point p0. -/
theorem p0_transport_exact_original_968 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (968 : Fin 1024)) =
      ([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk04.p0_basis_968_exact (F := F)
#print axioms p0_transport_exact_original_968

/-- Transport at original index 968, point p2. -/
theorem p2_transport_exact_original_968 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (968 : Fin 1024)) =
      ([1, 1, 2, 3, -3, -1, -1, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk04.p2_basis_968_exact (F := F)
#print axioms p2_transport_exact_original_968

/-- Transport at original index 984, point p0. -/
theorem p0_transport_exact_original_984 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (984 : Fin 1024)) =
      ([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk04.p0_basis_984_exact (F := F)
#print axioms p0_transport_exact_original_984

/-- Transport at original index 984, point p2. -/
theorem p2_transport_exact_original_984 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (984 : Fin 1024)) =
      ([1, 1, 2, 3, -3, 2, -1, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk04.p2_basis_984_exact (F := F)
#print axioms p2_transport_exact_original_984

/-- Transport at original index 1000, point p0. -/
theorem p0_transport_exact_original_1000 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (1000 : Fin 1024)) =
      ([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk04.p0_basis_1000_exact (F := F)
#print axioms p0_transport_exact_original_1000

/-- Transport at original index 1000, point p2. -/
theorem p2_transport_exact_original_1000 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (1000 : Fin 1024)) =
      ([1, 1, 2, 3, 4, -1, -1, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk04.p2_basis_1000_exact (F := F)
#print axioms p2_transport_exact_original_1000

/-- Transport at original index 1016, point p0. -/
theorem p0_transport_exact_original_1016 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (1016 : Fin 1024)) =
      ([1, 1, 2, 3, 4, 2, 2, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk04.p0_basis_1016_exact (F := F)
#print axioms p0_transport_exact_original_1016

/-- Transport at original index 1016, point p2. -/
theorem p2_transport_exact_original_1016 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (1016 : Fin 1024)) =
      ([1, 1, 2, 3, 4, 2, -1, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk04.p2_basis_1016_exact (F := F)
#print axioms p2_transport_exact_original_1016

/-- Transport at original index 772, point p0. -/
theorem p0_transport_exact_original_772 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (772 : Fin 1024)) =
      ([1, 1, -1, -2, -3, -1, -1, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk04.p0_basis_772_exact (F := F)
#print axioms p0_transport_exact_original_772

/-- Transport at original index 772, point p2. -/
theorem p2_transport_exact_original_772 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (772 : Fin 1024)) =
      ([1, 1, -1, -2, -3, -1, 2, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk04.p2_basis_772_exact (F := F)
#print axioms p2_transport_exact_original_772

/-- Transport at original index 900, point p0. -/
theorem p0_transport_exact_original_900 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (900 : Fin 1024)) =
      ([1, 1, 2, -2, -3, -1, -1, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk04.p0_basis_900_exact (F := F)
#print axioms p0_transport_exact_original_900

/-- Transport at original index 900, point p2. -/
theorem p2_transport_exact_original_900 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (900 : Fin 1024)) =
      ([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk04.p2_basis_900_exact (F := F)
#print axioms p2_transport_exact_original_900

/-- Transport at original index 901, point p0. -/
theorem p0_transport_exact_original_901 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (901 : Fin 1024)) =
      ([1, 1, 2, -2, -3, -1, -1, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk04.p0_basis_901_exact (F := F)
#print axioms p0_transport_exact_original_901

/-- Transport at original index 901, point p2. -/
theorem p2_transport_exact_original_901 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (901 : Fin 1024)) =
      ([1, 1, 2, -2, -3, -1, 2, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk04.p2_basis_901_exact (F := F)
#print axioms p2_transport_exact_original_901

/-- Transport at original index 916, point p0. -/
theorem p0_transport_exact_original_916 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (916 : Fin 1024)) =
      ([1, 1, 2, -2, -3, 2, -1, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk04.p0_basis_916_exact (F := F)
#print axioms p0_transport_exact_original_916

/-- Transport at original index 916, point p2. -/
theorem p2_transport_exact_original_916 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (916 : Fin 1024)) =
      ([1, 1, 2, -2, -3, 2, 2, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk04.p2_basis_916_exact (F := F)
#print axioms p2_transport_exact_original_916

end
end AspisV8R19.R772Point02DualLeavesChunk30
