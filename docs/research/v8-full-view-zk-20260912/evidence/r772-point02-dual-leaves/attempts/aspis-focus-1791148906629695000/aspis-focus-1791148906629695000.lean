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

namespace AspisV8R19.R772Point02DualLeavesChunk26
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.R750WitnessPointSupport
open AspisR19.TwoSwapSourceTable
noncomputable section
set_option autoImplicit false
variable {F : Type*} [CommRing F]

/-- Transport at original index 736, point p0. -/
theorem p0_transport_zero_original_736 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (736 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 736 (by decide)
#print axioms p0_transport_zero_original_736

/-- Transport at original index 736, point p2. -/
theorem p2_transport_zero_original_736 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (736 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 736 (by decide)
#print axioms p2_transport_zero_original_736

/-- Transport at original index 752, point p0. -/
theorem p0_transport_zero_original_752 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (752 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := F) 752 (by decide)
#print axioms p0_transport_zero_original_752

/-- Transport at original index 752, point p2. -/
theorem p2_transport_zero_original_752 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (752 : Fin 1024)) =
      0 := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := F) 752 (by decide)
#print axioms p2_transport_zero_original_752

/-- Transport at original index 993, point p0. -/
theorem p0_transport_exact_original_993 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (993 : Fin 1024)) =
      ([1, 1, 2, 3, 4, -1, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02BasisLeaves.p0_basis_993_exact (F := F)
#print axioms p0_transport_exact_original_993

/-- Transport at original index 993, point p2. -/
theorem p2_transport_exact_original_993 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (993 : Fin 1024)) =
      ([1, 1, 2, 3, 4, -1, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02BasisLeaves.p2_basis_993_exact (F := F)
#print axioms p2_transport_exact_original_993

/-- Transport at original index 796, point p0. -/
theorem p0_transport_exact_original_796 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (796 : Fin 1024)) =
      ([1, 1, -1, -2, -3, 2, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk00.p0_basis_796_exact (F := F)
#print axioms p0_transport_exact_original_796

/-- Transport at original index 796, point p2. -/
theorem p2_transport_exact_original_796 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (796 : Fin 1024)) =
      ([1, 1, -1, -2, -3, 2, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk00.p2_basis_796_exact (F := F)
#print axioms p2_transport_exact_original_796

/-- Transport at original index 812, point p0. -/
theorem p0_transport_exact_original_812 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (812 : Fin 1024)) =
      ([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk00.p0_basis_812_exact (F := F)
#print axioms p0_transport_exact_original_812

/-- Transport at original index 812, point p2. -/
theorem p2_transport_exact_original_812 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (812 : Fin 1024)) =
      ([1, 1, -1, -2, 4, -1, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk00.p2_basis_812_exact (F := F)
#print axioms p2_transport_exact_original_812

/-- Transport at original index 828, point p0. -/
theorem p0_transport_exact_original_828 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (828 : Fin 1024)) =
      ([1, 1, -1, -2, 4, 2, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk00.p0_basis_828_exact (F := F)
#print axioms p0_transport_exact_original_828

/-- Transport at original index 828, point p2. -/
theorem p2_transport_exact_original_828 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (828 : Fin 1024)) =
      ([1, 1, -1, -2, 4, 2, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk00.p2_basis_828_exact (F := F)
#print axioms p2_transport_exact_original_828

/-- Transport at original index 844, point p0. -/
theorem p0_transport_exact_original_844 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (844 : Fin 1024)) =
      ([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk00.p0_basis_844_exact (F := F)
#print axioms p0_transport_exact_original_844

/-- Transport at original index 844, point p2. -/
theorem p2_transport_exact_original_844 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (844 : Fin 1024)) =
      ([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk00.p2_basis_844_exact (F := F)
#print axioms p2_transport_exact_original_844

/-- Transport at original index 860, point p0. -/
theorem p0_transport_exact_original_860 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (860 : Fin 1024)) =
      ([1, 1, -1, 3, -3, 2, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk00.p0_basis_860_exact (F := F)
#print axioms p0_transport_exact_original_860

/-- Transport at original index 860, point p2. -/
theorem p2_transport_exact_original_860 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (860 : Fin 1024)) =
      ([1, 1, -1, 3, -3, 2, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk00.p2_basis_860_exact (F := F)
#print axioms p2_transport_exact_original_860

/-- Transport at original index 876, point p0. -/
theorem p0_transport_exact_original_876 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (876 : Fin 1024)) =
      ([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk00.p0_basis_876_exact (F := F)
#print axioms p0_transport_exact_original_876

/-- Transport at original index 876, point p2. -/
theorem p2_transport_exact_original_876 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (876 : Fin 1024)) =
      ([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk00.p2_basis_876_exact (F := F)
#print axioms p2_transport_exact_original_876

/-- Transport at original index 892, point p0. -/
theorem p0_transport_exact_original_892 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (892 : Fin 1024)) =
      ([1, 1, -1, 3, 4, 2, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk00.p0_basis_892_exact (F := F)
#print axioms p0_transport_exact_original_892

/-- Transport at original index 892, point p2. -/
theorem p2_transport_exact_original_892 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (892 : Fin 1024)) =
      ([1, 1, -1, 3, 4, 2, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk00.p2_basis_892_exact (F := F)
#print axioms p2_transport_exact_original_892

/-- Transport at original index 908, point p0. -/
theorem p0_transport_exact_original_908 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (908 : Fin 1024)) =
      ([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk00.p0_basis_908_exact (F := F)
#print axioms p0_transport_exact_original_908

/-- Transport at original index 908, point p2. -/
theorem p2_transport_exact_original_908 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (908 : Fin 1024)) =
      ([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk00.p2_basis_908_exact (F := F)
#print axioms p2_transport_exact_original_908

/-- Transport at original index 925, point p0. -/
theorem p0_transport_exact_original_925 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (925 : Fin 1024)) =
      ([1, 1, 2, -2, -3, 2, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk00.p0_basis_925_exact (F := F)
#print axioms p0_transport_exact_original_925

/-- Transport at original index 925, point p2. -/
theorem p2_transport_exact_original_925 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (925 : Fin 1024)) =
      ([1, 1, 2, -2, -3, 2, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk00.p2_basis_925_exact (F := F)
#print axioms p2_transport_exact_original_925

/-- Transport at original index 941, point p0. -/
theorem p0_transport_exact_original_941 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (941 : Fin 1024)) =
      ([1, 1, 2, -2, 4, -1, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk00.p0_basis_941_exact (F := F)
#print axioms p0_transport_exact_original_941

/-- Transport at original index 941, point p2. -/
theorem p2_transport_exact_original_941 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (941 : Fin 1024)) =
      ([1, 1, 2, -2, 4, -1, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk00.p2_basis_941_exact (F := F)
#print axioms p2_transport_exact_original_941

/-- Transport at original index 957, point p0. -/
theorem p0_transport_exact_original_957 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (957 : Fin 1024)) =
      ([1, 1, 2, -2, 4, 2, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk00.p0_basis_957_exact (F := F)
#print axioms p0_transport_exact_original_957

/-- Transport at original index 957, point p2. -/
theorem p2_transport_exact_original_957 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (957 : Fin 1024)) =
      ([1, 1, 2, -2, 4, 2, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk00.p2_basis_957_exact (F := F)
#print axioms p2_transport_exact_original_957

/-- Transport at original index 973, point p0. -/
theorem p0_transport_exact_original_973 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (973 : Fin 1024)) =
      ([1, 1, 2, 3, -3, -1, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk00.p0_basis_973_exact (F := F)
#print axioms p0_transport_exact_original_973

/-- Transport at original index 973, point p2. -/
theorem p2_transport_exact_original_973 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (973 : Fin 1024)) =
      ([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk00.p2_basis_973_exact (F := F)
#print axioms p2_transport_exact_original_973

/-- Transport at original index 989, point p0. -/
theorem p0_transport_exact_original_989 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point0 (F := F)) k.val)
      (order.symm (989 : Fin 1024)) =
      ([1, 1, 2, 3, -3, 2, 2, 3, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point0_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point0] using AspisV8R19.R768Point02LeavesChunk00.p0_basis_989_exact (F := F)
#print axioms p0_transport_exact_original_989

/-- Transport at original index 989, point p2. -/
theorem p2_transport_exact_original_989 :
    AspisV8R16.transportDual inactive (1023 : Fin 1024) order
      (fun k : Fin 1024 => sourcePointBasis (AspisV8R19.R771Point02Transport.point2 (F := F)) k.val)
      (order.symm (989 : Fin 1024)) =
      ([1, 1, 2, 3, -3, 2, -1, -2, 1, 2] : List F).prod := by
  rw [AspisV8R19.R772Point02DualLeaves.point2_transport_original]
  simpa [AspisV8R19.R771Point02Transport.point2] using AspisV8R19.R768Point02LeavesChunk00.p2_basis_989_exact (F := F)
#print axioms p2_transport_exact_original_989

end
end AspisV8R19.R772Point02DualLeavesChunk26
