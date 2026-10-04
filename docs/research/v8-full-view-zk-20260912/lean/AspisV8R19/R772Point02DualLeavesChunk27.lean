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

namespace AspisV8R19.R772Point02DualLeavesChunk27
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.R750WitnessPointSupport
open AspisR19.TwoSwapSourceTable
noncomputable section
set_option autoImplicit false
variable {F : Type*} [CommRing F]

/-- Transport at original index 1005, point p0. -/
theorem p0_transport_exact_original_1005 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (1005 : Fin 1024)) =
      ([1, 1, 2, 3, 4, -1, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk00.p0_basis_1005_exact (F := F)
#print axioms p0_transport_exact_original_1005

/-- Transport at original index 1005, point p2. -/
theorem p2_transport_exact_original_1005 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (1005 : Fin 1024)) =
      ([1, 1, 2, 3, 4, -1, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk00.p2_basis_1005_exact (F := F)
#print axioms p2_transport_exact_original_1005

/-- Transport at original index 921, point p0. -/
theorem p0_transport_exact_original_921 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (921 : Fin 1024)) =
      ([1, 1, 2, -2, -3, 2, 2, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk00.p0_basis_921_exact (F := F)
#print axioms p0_transport_exact_original_921

/-- Transport at original index 921, point p2. -/
theorem p2_transport_exact_original_921 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (921 : Fin 1024)) =
      ([1, 1, 2, -2, -3, 2, -1, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk00.p2_basis_921_exact (F := F)
#print axioms p2_transport_exact_original_921

/-- Transport at original index 937, point p0. -/
theorem p0_transport_exact_original_937 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (937 : Fin 1024)) =
      ([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk01.p0_basis_937_exact (F := F)
#print axioms p0_transport_exact_original_937

/-- Transport at original index 937, point p2. -/
theorem p2_transport_exact_original_937 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (937 : Fin 1024)) =
      ([1, 1, 2, -2, 4, -1, -1, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk01.p2_basis_937_exact (F := F)
#print axioms p2_transport_exact_original_937

/-- Transport at original index 953, point p0. -/
theorem p0_transport_exact_original_953 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (953 : Fin 1024)) =
      ([1, 1, 2, -2, 4, 2, 2, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk01.p0_basis_953_exact (F := F)
#print axioms p0_transport_exact_original_953

/-- Transport at original index 953, point p2. -/
theorem p2_transport_exact_original_953 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (953 : Fin 1024)) =
      ([1, 1, 2, -2, 4, 2, -1, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk01.p2_basis_953_exact (F := F)
#print axioms p2_transport_exact_original_953

/-- Transport at original index 969, point p0. -/
theorem p0_transport_exact_original_969 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (969 : Fin 1024)) =
      ([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk01.p0_basis_969_exact (F := F)
#print axioms p0_transport_exact_original_969

/-- Transport at original index 969, point p2. -/
theorem p2_transport_exact_original_969 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (969 : Fin 1024)) =
      ([1, 1, 2, 3, -3, -1, -1, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk01.p2_basis_969_exact (F := F)
#print axioms p2_transport_exact_original_969

/-- Transport at original index 985, point p0. -/
theorem p0_transport_exact_original_985 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (985 : Fin 1024)) =
      ([1, 1, 2, 3, -3, 2, 2, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk01.p0_basis_985_exact (F := F)
#print axioms p0_transport_exact_original_985

/-- Transport at original index 985, point p2. -/
theorem p2_transport_exact_original_985 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (985 : Fin 1024)) =
      ([1, 1, 2, 3, -3, 2, -1, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk01.p2_basis_985_exact (F := F)
#print axioms p2_transport_exact_original_985

/-- Transport at original index 1001, point p0. -/
theorem p0_transport_exact_original_1001 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (1001 : Fin 1024)) =
      ([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk01.p0_basis_1001_exact (F := F)
#print axioms p0_transport_exact_original_1001

/-- Transport at original index 1001, point p2. -/
theorem p2_transport_exact_original_1001 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (1001 : Fin 1024)) =
      ([1, 1, 2, 3, 4, -1, -1, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk01.p2_basis_1001_exact (F := F)
#print axioms p2_transport_exact_original_1001

/-- Transport at original index 1017, point p0. -/
theorem p0_transport_exact_original_1017 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (1017 : Fin 1024)) =
      ([1, 1, 2, 3, 4, 2, 2, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk01.p0_basis_1017_exact (F := F)
#print axioms p0_transport_exact_original_1017

/-- Transport at original index 1017, point p2. -/
theorem p2_transport_exact_original_1017 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (1017 : Fin 1024)) =
      ([1, 1, 2, 3, 4, 2, -1, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk01.p2_basis_1017_exact (F := F)
#print axioms p2_transport_exact_original_1017

/-- Transport at original index 917, point p0. -/
theorem p0_transport_exact_original_917 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (917 : Fin 1024)) =
      ([1, 1, 2, -2, -3, 2, -1, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk01.p0_basis_917_exact (F := F)
#print axioms p0_transport_exact_original_917

/-- Transport at original index 917, point p2. -/
theorem p2_transport_exact_original_917 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (917 : Fin 1024)) =
      ([1, 1, 2, -2, -3, 2, 2, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk01.p2_basis_917_exact (F := F)
#print axioms p2_transport_exact_original_917

/-- Transport at original index 933, point p0. -/
theorem p0_transport_exact_original_933 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (933 : Fin 1024)) =
      ([1, 1, 2, -2, 4, -1, -1, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk01.p0_basis_933_exact (F := F)
#print axioms p0_transport_exact_original_933

/-- Transport at original index 933, point p2. -/
theorem p2_transport_exact_original_933 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (933 : Fin 1024)) =
      ([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk01.p2_basis_933_exact (F := F)
#print axioms p2_transport_exact_original_933

/-- Transport at original index 949, point p0. -/
theorem p0_transport_exact_original_949 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (949 : Fin 1024)) =
      ([1, 1, 2, -2, 4, 2, -1, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk01.p0_basis_949_exact (F := F)
#print axioms p0_transport_exact_original_949

/-- Transport at original index 949, point p2. -/
theorem p2_transport_exact_original_949 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (949 : Fin 1024)) =
      ([1, 1, 2, -2, 4, 2, 2, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk01.p2_basis_949_exact (F := F)
#print axioms p2_transport_exact_original_949

/-- Transport at original index 965, point p0. -/
theorem p0_transport_exact_original_965 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (965 : Fin 1024)) =
      ([1, 1, 2, 3, -3, -1, -1, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk01.p0_basis_965_exact (F := F)
#print axioms p0_transport_exact_original_965

/-- Transport at original index 965, point p2. -/
theorem p2_transport_exact_original_965 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (965 : Fin 1024)) =
      ([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk01.p2_basis_965_exact (F := F)
#print axioms p2_transport_exact_original_965

/-- Transport at original index 981, point p0. -/
theorem p0_transport_exact_original_981 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (981 : Fin 1024)) =
      ([1, 1, 2, 3, -3, 2, -1, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk01.p0_basis_981_exact (F := F)
#print axioms p0_transport_exact_original_981

/-- Transport at original index 981, point p2. -/
theorem p2_transport_exact_original_981 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (981 : Fin 1024)) =
      ([1, 1, 2, 3, -3, 2, 2, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk01.p2_basis_981_exact (F := F)
#print axioms p2_transport_exact_original_981

/-- Transport at original index 997, point p0. -/
theorem p0_transport_exact_original_997 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (997 : Fin 1024)) =
      ([1, 1, 2, 3, 4, -1, -1, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk01.p0_basis_997_exact (F := F)
#print axioms p0_transport_exact_original_997

/-- Transport at original index 997, point p2. -/
theorem p2_transport_exact_original_997 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (997 : Fin 1024)) =
      ([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk01.p2_basis_997_exact (F := F)
#print axioms p2_transport_exact_original_997

/-- Transport at original index 1012, point p0. -/
theorem p0_transport_exact_original_1012 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (1012 : Fin 1024)) =
      ([1, 1, 2, 3, 4, 2, -1, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk01.p0_basis_1012_exact (F := F)
#print axioms p0_transport_exact_original_1012

/-- Transport at original index 1012, point p2. -/
theorem p2_transport_exact_original_1012 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (1012 : Fin 1024)) =
      ([1, 1, 2, 3, 4, 2, 2, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk01.p2_basis_1012_exact (F := F)
#print axioms p2_transport_exact_original_1012

/-- Transport at original index 768, point p0. -/
theorem p0_transport_exact_original_768 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (768 : Fin 1024)) =
      ([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk01.p0_basis_768_exact (F := F)
#print axioms p0_transport_exact_original_768

/-- Transport at original index 768, point p2. -/
theorem p2_transport_exact_original_768 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (768 : Fin 1024)) =
      ([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk01.p2_basis_768_exact (F := F)
#print axioms p2_transport_exact_original_768

end
end AspisV8R19.R772Point02DualLeavesChunk27
