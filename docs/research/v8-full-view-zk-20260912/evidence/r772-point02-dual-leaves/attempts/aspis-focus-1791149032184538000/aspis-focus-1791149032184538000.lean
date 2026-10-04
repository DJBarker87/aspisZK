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

namespace AspisV8R19.R772Point02DualLeavesChunk28
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.R750WitnessPointSupport
open AspisR19.TwoSwapSourceTable
noncomputable section
set_option autoImplicit false
variable {F : Type*} [CommRing F]

/-- Transport at original index 784, point p0. -/
theorem p0_transport_exact_original_784 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (784 : Fin 1024)) =
      ([1, 1, -1, -2, -3, 2, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk01.p0_basis_784_exact (F := F)
#print axioms p0_transport_exact_original_784

/-- Transport at original index 784, point p2. -/
theorem p2_transport_exact_original_784 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (784 : Fin 1024)) =
      ([1, 1, -1, -2, -3, 2, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk01.p2_basis_784_exact (F := F)
#print axioms p2_transport_exact_original_784

/-- Transport at original index 800, point p0. -/
theorem p0_transport_exact_original_800 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (800 : Fin 1024)) =
      ([1, 1, -1, -2, 4, -1, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk01.p0_basis_800_exact (F := F)
#print axioms p0_transport_exact_original_800

/-- Transport at original index 800, point p2. -/
theorem p2_transport_exact_original_800 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (800 : Fin 1024)) =
      ([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk01.p2_basis_800_exact (F := F)
#print axioms p2_transport_exact_original_800

/-- Transport at original index 816, point p0. -/
theorem p0_transport_exact_original_816 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (816 : Fin 1024)) =
      ([1, 1, -1, -2, 4, 2, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk02.p0_basis_816_exact (F := F)
#print axioms p0_transport_exact_original_816

/-- Transport at original index 816, point p2. -/
theorem p2_transport_exact_original_816 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (816 : Fin 1024)) =
      ([1, 1, -1, -2, 4, 2, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk02.p2_basis_816_exact (F := F)
#print axioms p2_transport_exact_original_816

/-- Transport at original index 832, point p0. -/
theorem p0_transport_exact_original_832 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (832 : Fin 1024)) =
      ([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk02.p0_basis_832_exact (F := F)
#print axioms p0_transport_exact_original_832

/-- Transport at original index 832, point p2. -/
theorem p2_transport_exact_original_832 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (832 : Fin 1024)) =
      ([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk02.p2_basis_832_exact (F := F)
#print axioms p2_transport_exact_original_832

/-- Transport at original index 848, point p0. -/
theorem p0_transport_exact_original_848 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (848 : Fin 1024)) =
      ([1, 1, -1, 3, -3, 2, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk02.p0_basis_848_exact (F := F)
#print axioms p0_transport_exact_original_848

/-- Transport at original index 848, point p2. -/
theorem p2_transport_exact_original_848 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (848 : Fin 1024)) =
      ([1, 1, -1, 3, -3, 2, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk02.p2_basis_848_exact (F := F)
#print axioms p2_transport_exact_original_848

/-- Transport at original index 864, point p0. -/
theorem p0_transport_exact_original_864 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (864 : Fin 1024)) =
      ([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk02.p0_basis_864_exact (F := F)
#print axioms p0_transport_exact_original_864

/-- Transport at original index 864, point p2. -/
theorem p2_transport_exact_original_864 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (864 : Fin 1024)) =
      ([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk02.p2_basis_864_exact (F := F)
#print axioms p2_transport_exact_original_864

/-- Transport at original index 880, point p0. -/
theorem p0_transport_exact_original_880 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (880 : Fin 1024)) =
      ([1, 1, -1, 3, 4, 2, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk02.p0_basis_880_exact (F := F)
#print axioms p0_transport_exact_original_880

/-- Transport at original index 880, point p2. -/
theorem p2_transport_exact_original_880 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (880 : Fin 1024)) =
      ([1, 1, -1, 3, 4, 2, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk02.p2_basis_880_exact (F := F)
#print axioms p2_transport_exact_original_880

/-- Transport at original index 896, point p0. -/
theorem p0_transport_exact_original_896 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (896 : Fin 1024)) =
      ([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk02.p0_basis_896_exact (F := F)
#print axioms p0_transport_exact_original_896

/-- Transport at original index 896, point p2. -/
theorem p2_transport_exact_original_896 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (896 : Fin 1024)) =
      ([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk02.p2_basis_896_exact (F := F)
#print axioms p2_transport_exact_original_896

/-- Transport at original index 913, point p0. -/
theorem p0_transport_exact_original_913 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (913 : Fin 1024)) =
      ([1, 1, 2, -2, -3, 2, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk02.p0_basis_913_exact (F := F)
#print axioms p0_transport_exact_original_913

/-- Transport at original index 913, point p2. -/
theorem p2_transport_exact_original_913 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (913 : Fin 1024)) =
      ([1, 1, 2, -2, -3, 2, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk02.p2_basis_913_exact (F := F)
#print axioms p2_transport_exact_original_913

/-- Transport at original index 929, point p0. -/
theorem p0_transport_exact_original_929 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (929 : Fin 1024)) =
      ([1, 1, 2, -2, 4, -1, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk02.p0_basis_929_exact (F := F)
#print axioms p0_transport_exact_original_929

/-- Transport at original index 929, point p2. -/
theorem p2_transport_exact_original_929 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (929 : Fin 1024)) =
      ([1, 1, 2, -2, 4, -1, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk02.p2_basis_929_exact (F := F)
#print axioms p2_transport_exact_original_929

/-- Transport at original index 945, point p0. -/
theorem p0_transport_exact_original_945 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (945 : Fin 1024)) =
      ([1, 1, 2, -2, 4, 2, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk02.p0_basis_945_exact (F := F)
#print axioms p0_transport_exact_original_945

/-- Transport at original index 945, point p2. -/
theorem p2_transport_exact_original_945 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (945 : Fin 1024)) =
      ([1, 1, 2, -2, 4, 2, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk02.p2_basis_945_exact (F := F)
#print axioms p2_transport_exact_original_945

/-- Transport at original index 961, point p0. -/
theorem p0_transport_exact_original_961 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (961 : Fin 1024)) =
      ([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk02.p0_basis_961_exact (F := F)
#print axioms p0_transport_exact_original_961

/-- Transport at original index 961, point p2. -/
theorem p2_transport_exact_original_961 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (961 : Fin 1024)) =
      ([1, 1, 2, 3, -3, -1, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk02.p2_basis_961_exact (F := F)
#print axioms p2_transport_exact_original_961

/-- Transport at original index 977, point p0. -/
theorem p0_transport_exact_original_977 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (977 : Fin 1024)) =
      ([1, 1, 2, 3, -3, 2, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk02.p0_basis_977_exact (F := F)
#print axioms p0_transport_exact_original_977

/-- Transport at original index 977, point p2. -/
theorem p2_transport_exact_original_977 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (977 : Fin 1024)) =
      ([1, 1, 2, 3, -3, 2, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk02.p2_basis_977_exact (F := F)
#print axioms p2_transport_exact_original_977

/-- Transport at original index 1008, point p0. -/
theorem p0_transport_exact_original_1008 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (1008 : Fin 1024)) =
      ([1, 1, 2, 3, 4, 2, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk02.p0_basis_1008_exact (F := F)
#print axioms p0_transport_exact_original_1008

/-- Transport at original index 1008, point p2. -/
theorem p2_transport_exact_original_1008 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (1008 : Fin 1024)) =
      ([1, 1, 2, 3, 4, 2, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk02.p2_basis_1008_exact (F := F)
#print axioms p2_transport_exact_original_1008

/-- Transport at original index 1009, point p0. -/
theorem p0_transport_exact_original_1009 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (1009 : Fin 1024)) =
      ([1, 1, 2, 3, 4, 2, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk02.p0_basis_1009_exact (F := F)
#print axioms p0_transport_exact_original_1009

/-- Transport at original index 1009, point p2. -/
theorem p2_transport_exact_original_1009 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (1009 : Fin 1024)) =
      ([1, 1, 2, 3, 4, 2, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk02.p2_basis_1009_exact (F := F)
#print axioms p2_transport_exact_original_1009

/-- Transport at original index 781, point p0. -/
theorem p0_transport_exact_original_781 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (781 : Fin 1024)) =
      ([1, 1, -1, -2, -3, -1, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk02.p0_basis_781_exact (F := F)
#print axioms p0_transport_exact_original_781

/-- Transport at original index 781, point p2. -/
theorem p2_transport_exact_original_781 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (781 : Fin 1024)) =
      ([1, 1, -1, -2, -3, -1, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk02.p2_basis_781_exact (F := F)
#print axioms p2_transport_exact_original_781

end
end AspisV8R19.R772Point02DualLeavesChunk28
