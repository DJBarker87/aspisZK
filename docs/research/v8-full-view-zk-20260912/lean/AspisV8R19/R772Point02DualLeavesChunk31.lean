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

namespace AspisV8R19.R772Point02DualLeavesChunk31
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.R750WitnessPointSupport
open AspisR19.TwoSwapSourceTable
noncomputable section
set_option autoImplicit false
variable {F : Type*} [CommRing F]

/-- Transport at original index 932, point p0. -/
theorem p0_transport_exact_original_932 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (932 : Fin 1024)) =
      ([1, 1, 2, -2, 4, -1, -1, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk04.p0_basis_932_exact (F := F)
#print axioms p0_transport_exact_original_932

/-- Transport at original index 932, point p2. -/
theorem p2_transport_exact_original_932 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (932 : Fin 1024)) =
      ([1, 1, 2, -2, 4, -1, 2, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk04.p2_basis_932_exact (F := F)
#print axioms p2_transport_exact_original_932

/-- Transport at original index 948, point p0. -/
theorem p0_transport_exact_original_948 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (948 : Fin 1024)) =
      ([1, 1, 2, -2, 4, 2, -1, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk04.p0_basis_948_exact (F := F)
#print axioms p0_transport_exact_original_948

/-- Transport at original index 948, point p2. -/
theorem p2_transport_exact_original_948 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (948 : Fin 1024)) =
      ([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk04.p2_basis_948_exact (F := F)
#print axioms p2_transport_exact_original_948

/-- Transport at original index 964, point p0. -/
theorem p0_transport_exact_original_964 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (964 : Fin 1024)) =
      ([1, 1, 2, 3, -3, -1, -1, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk05.p0_basis_964_exact (F := F)
#print axioms p0_transport_exact_original_964

/-- Transport at original index 964, point p2. -/
theorem p2_transport_exact_original_964 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (964 : Fin 1024)) =
      ([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk05.p2_basis_964_exact (F := F)
#print axioms p2_transport_exact_original_964

/-- Transport at original index 980, point p0. -/
theorem p0_transport_exact_original_980 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (980 : Fin 1024)) =
      ([1, 1, 2, 3, -3, 2, -1, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk05.p0_basis_980_exact (F := F)
#print axioms p0_transport_exact_original_980

/-- Transport at original index 980, point p2. -/
theorem p2_transport_exact_original_980 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (980 : Fin 1024)) =
      ([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk05.p2_basis_980_exact (F := F)
#print axioms p2_transport_exact_original_980

/-- Transport at original index 996, point p0. -/
theorem p0_transport_exact_original_996 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (996 : Fin 1024)) =
      ([1, 1, 2, 3, 4, -1, -1, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk05.p0_basis_996_exact (F := F)
#print axioms p0_transport_exact_original_996

/-- Transport at original index 996, point p2. -/
theorem p2_transport_exact_original_996 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (996 : Fin 1024)) =
      ([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk05.p2_basis_996_exact (F := F)
#print axioms p2_transport_exact_original_996

/-- Transport at original index 1013, point p0. -/
theorem p0_transport_exact_original_1013 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (1013 : Fin 1024)) =
      ([1, 1, 2, 3, 4, 2, -1, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk05.p0_basis_1013_exact (F := F)
#print axioms p0_transport_exact_original_1013

/-- Transport at original index 1013, point p2. -/
theorem p2_transport_exact_original_1013 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (1013 : Fin 1024)) =
      ([1, 1, 2, 3, 4, 2, 2, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk05.p2_basis_1013_exact (F := F)
#print axioms p2_transport_exact_original_1013

/-- Transport at original index 769, point p0. -/
theorem p0_transport_exact_original_769 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (769 : Fin 1024)) =
      ([1, 1, -1, -2, -3, -1, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk05.p0_basis_769_exact (F := F)
#print axioms p0_transport_exact_original_769

/-- Transport at original index 769, point p2. -/
theorem p2_transport_exact_original_769 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (769 : Fin 1024)) =
      ([1, 1, -1, -2, -3, -1, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk05.p2_basis_769_exact (F := F)
#print axioms p2_transport_exact_original_769

/-- Transport at original index 785, point p0. -/
theorem p0_transport_exact_original_785 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (785 : Fin 1024)) =
      ([1, 1, -1, -2, -3, 2, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk05.p0_basis_785_exact (F := F)
#print axioms p0_transport_exact_original_785

/-- Transport at original index 785, point p2. -/
theorem p2_transport_exact_original_785 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (785 : Fin 1024)) =
      ([1, 1, -1, -2, -3, 2, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk05.p2_basis_785_exact (F := F)
#print axioms p2_transport_exact_original_785

/-- Transport at original index 801, point p0. -/
theorem p0_transport_exact_original_801 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (801 : Fin 1024)) =
      ([1, 1, -1, -2, 4, -1, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk05.p0_basis_801_exact (F := F)
#print axioms p0_transport_exact_original_801

/-- Transport at original index 801, point p2. -/
theorem p2_transport_exact_original_801 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (801 : Fin 1024)) =
      ([1, 1, -1, -2, 4, -1, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk05.p2_basis_801_exact (F := F)
#print axioms p2_transport_exact_original_801

/-- Transport at original index 817, point p0. -/
theorem p0_transport_exact_original_817 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (817 : Fin 1024)) =
      ([1, 1, -1, -2, 4, 2, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk05.p0_basis_817_exact (F := F)
#print axioms p0_transport_exact_original_817

/-- Transport at original index 817, point p2. -/
theorem p2_transport_exact_original_817 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (817 : Fin 1024)) =
      ([1, 1, -1, -2, 4, 2, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk05.p2_basis_817_exact (F := F)
#print axioms p2_transport_exact_original_817

/-- Transport at original index 833, point p0. -/
theorem p0_transport_exact_original_833 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (833 : Fin 1024)) =
      ([1, 1, -1, 3, -3, -1, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk05.p0_basis_833_exact (F := F)
#print axioms p0_transport_exact_original_833

/-- Transport at original index 833, point p2. -/
theorem p2_transport_exact_original_833 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (833 : Fin 1024)) =
      ([1, 1, -1, 3, -3, -1, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk05.p2_basis_833_exact (F := F)
#print axioms p2_transport_exact_original_833

/-- Transport at original index 849, point p0. -/
theorem p0_transport_exact_original_849 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (849 : Fin 1024)) =
      ([1, 1, -1, 3, -3, 2, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk05.p0_basis_849_exact (F := F)
#print axioms p0_transport_exact_original_849

/-- Transport at original index 849, point p2. -/
theorem p2_transport_exact_original_849 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (849 : Fin 1024)) =
      ([1, 1, -1, 3, -3, 2, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk05.p2_basis_849_exact (F := F)
#print axioms p2_transport_exact_original_849

/-- Transport at original index 865, point p0. -/
theorem p0_transport_exact_original_865 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (865 : Fin 1024)) =
      ([1, 1, -1, 3, 4, -1, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk05.p0_basis_865_exact (F := F)
#print axioms p0_transport_exact_original_865

/-- Transport at original index 865, point p2. -/
theorem p2_transport_exact_original_865 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (865 : Fin 1024)) =
      ([1, 1, -1, 3, 4, -1, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk05.p2_basis_865_exact (F := F)
#print axioms p2_transport_exact_original_865

/-- Transport at original index 881, point p0. -/
theorem p0_transport_exact_original_881 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (881 : Fin 1024)) =
      ([1, 1, -1, 3, 4, 2, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk05.p0_basis_881_exact (F := F)
#print axioms p0_transport_exact_original_881

/-- Transport at original index 881, point p2. -/
theorem p2_transport_exact_original_881 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (881 : Fin 1024)) =
      ([1, 1, -1, 3, 4, 2, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk05.p2_basis_881_exact (F := F)
#print axioms p2_transport_exact_original_881

/-- Transport at original index 897, point p0. -/
theorem p0_transport_exact_original_897 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (897 : Fin 1024)) =
      ([1, 1, 2, -2, -3, -1, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk05.p0_basis_897_exact (F := F)
#print axioms p0_transport_exact_original_897

/-- Transport at original index 897, point p2. -/
theorem p2_transport_exact_original_897 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (897 : Fin 1024)) =
      ([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk05.p2_basis_897_exact (F := F)
#print axioms p2_transport_exact_original_897

/-- Transport at original index 912, point p0. -/
theorem p0_transport_exact_original_912 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (912 : Fin 1024)) =
      ([1, 1, 2, -2, -3, 2, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk05.p0_basis_912_exact (F := F)
#print axioms p0_transport_exact_original_912

/-- Transport at original index 912, point p2. -/
theorem p2_transport_exact_original_912 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (912 : Fin 1024)) =
      ([1, 1, 2, -2, -3, 2, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk05.p2_basis_912_exact (F := F)
#print axioms p2_transport_exact_original_912

end
end AspisV8R19.R772Point02DualLeavesChunk31
