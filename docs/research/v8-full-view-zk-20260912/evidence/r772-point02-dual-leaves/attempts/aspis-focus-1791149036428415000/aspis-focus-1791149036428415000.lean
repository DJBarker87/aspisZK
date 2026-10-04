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

namespace AspisV8R19.R772Point02DualLeavesChunk29
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.R750WitnessPointSupport
open AspisR19.TwoSwapSourceTable
noncomputable section
set_option autoImplicit false
variable {F : Type*} [CommRing F]

/-- Transport at original index 797, point p0. -/
theorem p0_transport_exact_original_797 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (797 : Fin 1024)) =
      ([1, 1, -1, -2, -3, 2, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk02.p0_basis_797_exact (F := F)
#print axioms p0_transport_exact_original_797

/-- Transport at original index 797, point p2. -/
theorem p2_transport_exact_original_797 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (797 : Fin 1024)) =
      ([1, 1, -1, -2, -3, 2, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk02.p2_basis_797_exact (F := F)
#print axioms p2_transport_exact_original_797

/-- Transport at original index 813, point p0. -/
theorem p0_transport_exact_original_813 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (813 : Fin 1024)) =
      ([1, 1, -1, -2, 4, -1, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk02.p0_basis_813_exact (F := F)
#print axioms p0_transport_exact_original_813

/-- Transport at original index 813, point p2. -/
theorem p2_transport_exact_original_813 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (813 : Fin 1024)) =
      ([1, 1, -1, -2, 4, -1, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk02.p2_basis_813_exact (F := F)
#print axioms p2_transport_exact_original_813

/-- Transport at original index 829, point p0. -/
theorem p0_transport_exact_original_829 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (829 : Fin 1024)) =
      ([1, 1, -1, -2, 4, 2, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk03.p0_basis_829_exact (F := F)
#print axioms p0_transport_exact_original_829

/-- Transport at original index 829, point p2. -/
theorem p2_transport_exact_original_829 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (829 : Fin 1024)) =
      ([1, 1, -1, -2, 4, 2, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk03.p2_basis_829_exact (F := F)
#print axioms p2_transport_exact_original_829

/-- Transport at original index 845, point p0. -/
theorem p0_transport_exact_original_845 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (845 : Fin 1024)) =
      ([1, 1, -1, 3, -3, -1, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk03.p0_basis_845_exact (F := F)
#print axioms p0_transport_exact_original_845

/-- Transport at original index 845, point p2. -/
theorem p2_transport_exact_original_845 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (845 : Fin 1024)) =
      ([1, 1, -1, 3, -3, -1, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk03.p2_basis_845_exact (F := F)
#print axioms p2_transport_exact_original_845

/-- Transport at original index 861, point p0. -/
theorem p0_transport_exact_original_861 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (861 : Fin 1024)) =
      ([1, 1, -1, 3, -3, 2, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk03.p0_basis_861_exact (F := F)
#print axioms p0_transport_exact_original_861

/-- Transport at original index 861, point p2. -/
theorem p2_transport_exact_original_861 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (861 : Fin 1024)) =
      ([1, 1, -1, 3, -3, 2, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk03.p2_basis_861_exact (F := F)
#print axioms p2_transport_exact_original_861

/-- Transport at original index 877, point p0. -/
theorem p0_transport_exact_original_877 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (877 : Fin 1024)) =
      ([1, 1, -1, 3, 4, -1, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk03.p0_basis_877_exact (F := F)
#print axioms p0_transport_exact_original_877

/-- Transport at original index 877, point p2. -/
theorem p2_transport_exact_original_877 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (877 : Fin 1024)) =
      ([1, 1, -1, 3, 4, -1, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk03.p2_basis_877_exact (F := F)
#print axioms p2_transport_exact_original_877

/-- Transport at original index 893, point p0. -/
theorem p0_transport_exact_original_893 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (893 : Fin 1024)) =
      ([1, 1, -1, 3, 4, 2, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk03.p0_basis_893_exact (F := F)
#print axioms p0_transport_exact_original_893

/-- Transport at original index 893, point p2. -/
theorem p2_transport_exact_original_893 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (893 : Fin 1024)) =
      ([1, 1, -1, 3, 4, 2, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk03.p2_basis_893_exact (F := F)
#print axioms p2_transport_exact_original_893

/-- Transport at original index 909, point p0. -/
theorem p0_transport_exact_original_909 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (909 : Fin 1024)) =
      ([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk03.p0_basis_909_exact (F := F)
#print axioms p0_transport_exact_original_909

/-- Transport at original index 909, point p2. -/
theorem p2_transport_exact_original_909 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (909 : Fin 1024)) =
      ([1, 1, 2, -2, -3, -1, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk03.p2_basis_909_exact (F := F)
#print axioms p2_transport_exact_original_909

/-- Transport at original index 924, point p0. -/
theorem p0_transport_exact_original_924 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (924 : Fin 1024)) =
      ([1, 1, 2, -2, -3, 2, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk03.p0_basis_924_exact (F := F)
#print axioms p0_transport_exact_original_924

/-- Transport at original index 924, point p2. -/
theorem p2_transport_exact_original_924 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (924 : Fin 1024)) =
      ([1, 1, 2, -2, -3, 2, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk03.p2_basis_924_exact (F := F)
#print axioms p2_transport_exact_original_924

/-- Transport at original index 940, point p0. -/
theorem p0_transport_exact_original_940 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (940 : Fin 1024)) =
      ([1, 1, 2, -2, 4, -1, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk03.p0_basis_940_exact (F := F)
#print axioms p0_transport_exact_original_940

/-- Transport at original index 940, point p2. -/
theorem p2_transport_exact_original_940 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (940 : Fin 1024)) =
      ([1, 1, 2, -2, 4, -1, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk03.p2_basis_940_exact (F := F)
#print axioms p2_transport_exact_original_940

/-- Transport at original index 956, point p0. -/
theorem p0_transport_exact_original_956 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (956 : Fin 1024)) =
      ([1, 1, 2, -2, 4, 2, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk03.p0_basis_956_exact (F := F)
#print axioms p0_transport_exact_original_956

/-- Transport at original index 956, point p2. -/
theorem p2_transport_exact_original_956 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (956 : Fin 1024)) =
      ([1, 1, 2, -2, 4, 2, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk03.p2_basis_956_exact (F := F)
#print axioms p2_transport_exact_original_956

/-- Transport at original index 972, point p0. -/
theorem p0_transport_exact_original_972 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (972 : Fin 1024)) =
      ([1, 1, 2, 3, -3, -1, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk03.p0_basis_972_exact (F := F)
#print axioms p0_transport_exact_original_972

/-- Transport at original index 972, point p2. -/
theorem p2_transport_exact_original_972 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (972 : Fin 1024)) =
      ([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk03.p2_basis_972_exact (F := F)
#print axioms p2_transport_exact_original_972

/-- Transport at original index 988, point p0. -/
theorem p0_transport_exact_original_988 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (988 : Fin 1024)) =
      ([1, 1, 2, 3, -3, 2, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk03.p0_basis_988_exact (F := F)
#print axioms p0_transport_exact_original_988

/-- Transport at original index 988, point p2. -/
theorem p2_transport_exact_original_988 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (988 : Fin 1024)) =
      ([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk03.p2_basis_988_exact (F := F)
#print axioms p2_transport_exact_original_988

/-- Transport at original index 1004, point p0. -/
theorem p0_transport_exact_original_1004 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (1004 : Fin 1024)) =
      ([1, 1, 2, 3, 4, -1, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk03.p0_basis_1004_exact (F := F)
#print axioms p0_transport_exact_original_1004

/-- Transport at original index 1004, point p2. -/
theorem p2_transport_exact_original_1004 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (1004 : Fin 1024)) =
      ([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk03.p2_basis_1004_exact (F := F)
#print axioms p2_transport_exact_original_1004

/-- Transport at original index 1020, point p0. -/
theorem p0_transport_exact_original_1020 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (1020 : Fin 1024)) =
      ([1, 1, 2, 3, 4, 2, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk03.p0_basis_1020_exact (F := F)
#print axioms p0_transport_exact_original_1020

/-- Transport at original index 1020, point p2. -/
theorem p2_transport_exact_original_1020 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (1020 : Fin 1024)) =
      ([1, 1, 2, 3, 4, 2, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk03.p2_basis_1020_exact (F := F)
#print axioms p2_transport_exact_original_1020

/-- Transport at original index 1021, point p0. -/
theorem p0_transport_exact_original_1021 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (1021 : Fin 1024)) =
      ([1, 1, 2, 3, 4, 2, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk03.p0_basis_1021_exact (F := F)
#print axioms p0_transport_exact_original_1021

/-- Transport at original index 1021, point p2. -/
theorem p2_transport_exact_original_1021 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (1021 : Fin 1024)) =
      ([1, 1, 2, 3, 4, 2, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk03.p2_basis_1021_exact (F := F)
#print axioms p2_transport_exact_original_1021

end
end AspisV8R19.R772Point02DualLeavesChunk29
