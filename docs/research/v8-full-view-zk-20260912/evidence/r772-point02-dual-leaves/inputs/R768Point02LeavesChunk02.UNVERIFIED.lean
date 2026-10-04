import AspisV8R19.R750WitnessPointSupport

namespace AspisV8R19.R768Point02LeavesChunk02
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.SourceStatementPoints
open AspisR19.R750WitnessPointSupport
noncomputable section
set_option autoImplicit false
variable {F : Type*} [CommRing F]

/-- Exact source-selected ten-factor product at original index 816, point p0. -/
theorem p0_basis_816_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 816 =
      ([1, 1, -1, -2, 4, 2, -1, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_816_exact

/-- Exact source-selected ten-factor product at original index 816, point p2. -/
theorem p2_basis_816_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 816 =
      ([1, 1, -1, -2, 4, 2, 2, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_816_exact

/-- Exact source-selected ten-factor product at original index 832, point p0. -/
theorem p0_basis_832_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 832 =
      ([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_832_exact

/-- Exact source-selected ten-factor product at original index 832, point p2. -/
theorem p2_basis_832_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 832 =
      ([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_832_exact

/-- Exact source-selected ten-factor product at original index 848, point p0. -/
theorem p0_basis_848_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 848 =
      ([1, 1, -1, 3, -3, 2, -1, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_848_exact

/-- Exact source-selected ten-factor product at original index 848, point p2. -/
theorem p2_basis_848_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 848 =
      ([1, 1, -1, 3, -3, 2, 2, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_848_exact

/-- Exact source-selected ten-factor product at original index 864, point p0. -/
theorem p0_basis_864_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 864 =
      ([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_864_exact

/-- Exact source-selected ten-factor product at original index 864, point p2. -/
theorem p2_basis_864_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 864 =
      ([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_864_exact

/-- Exact source-selected ten-factor product at original index 880, point p0. -/
theorem p0_basis_880_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 880 =
      ([1, 1, -1, 3, 4, 2, -1, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_880_exact

/-- Exact source-selected ten-factor product at original index 880, point p2. -/
theorem p2_basis_880_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 880 =
      ([1, 1, -1, 3, 4, 2, 2, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_880_exact

/-- Exact source-selected ten-factor product at original index 896, point p0. -/
theorem p0_basis_896_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 896 =
      ([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_896_exact

/-- Exact source-selected ten-factor product at original index 896, point p2. -/
theorem p2_basis_896_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 896 =
      ([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_896_exact

/-- Exact source-selected ten-factor product at original index 913, point p0. -/
theorem p0_basis_913_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 913 =
      ([1, 1, 2, -2, -3, 2, -1, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_913_exact

/-- Exact source-selected ten-factor product at original index 913, point p2. -/
theorem p2_basis_913_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 913 =
      ([1, 1, 2, -2, -3, 2, 2, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_913_exact

/-- Exact source-selected ten-factor product at original index 929, point p0. -/
theorem p0_basis_929_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 929 =
      ([1, 1, 2, -2, 4, -1, -1, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_929_exact

/-- Exact source-selected ten-factor product at original index 929, point p2. -/
theorem p2_basis_929_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 929 =
      ([1, 1, 2, -2, 4, -1, 2, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_929_exact

/-- Exact source-selected ten-factor product at original index 945, point p0. -/
theorem p0_basis_945_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 945 =
      ([1, 1, 2, -2, 4, 2, -1, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_945_exact

/-- Exact source-selected ten-factor product at original index 945, point p2. -/
theorem p2_basis_945_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 945 =
      ([1, 1, 2, -2, 4, 2, 2, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_945_exact

/-- Exact source-selected ten-factor product at original index 961, point p0. -/
theorem p0_basis_961_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 961 =
      ([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_961_exact

/-- Exact source-selected ten-factor product at original index 961, point p2. -/
theorem p2_basis_961_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 961 =
      ([1, 1, 2, 3, -3, -1, 2, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_961_exact

/-- Exact source-selected ten-factor product at original index 977, point p0. -/
theorem p0_basis_977_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 977 =
      ([1, 1, 2, 3, -3, 2, -1, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_977_exact

/-- Exact source-selected ten-factor product at original index 977, point p2. -/
theorem p2_basis_977_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 977 =
      ([1, 1, 2, 3, -3, 2, 2, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_977_exact

/-- Exact source-selected ten-factor product at original index 1008, point p0. -/
theorem p0_basis_1008_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 1008 =
      ([1, 1, 2, 3, 4, 2, -1, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_1008_exact

/-- Exact source-selected ten-factor product at original index 1008, point p2. -/
theorem p2_basis_1008_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 1008 =
      ([1, 1, 2, 3, 4, 2, 2, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_1008_exact

/-- Exact source-selected ten-factor product at original index 1009, point p0. -/
theorem p0_basis_1009_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 1009 =
      ([1, 1, 2, 3, 4, 2, -1, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_1009_exact

/-- Exact source-selected ten-factor product at original index 1009, point p2. -/
theorem p2_basis_1009_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 1009 =
      ([1, 1, 2, 3, 4, 2, 2, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_1009_exact

/-- Exact source-selected ten-factor product at original index 781, point p0. -/
theorem p0_basis_781_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 781 =
      ([1, 1, -1, -2, -3, -1, 2, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_781_exact

/-- Exact source-selected ten-factor product at original index 781, point p2. -/
theorem p2_basis_781_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 781 =
      ([1, 1, -1, -2, -3, -1, -1, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_781_exact

/-- Exact source-selected ten-factor product at original index 797, point p0. -/
theorem p0_basis_797_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 797 =
      ([1, 1, -1, -2, -3, 2, 2, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_797_exact

/-- Exact source-selected ten-factor product at original index 797, point p2. -/
theorem p2_basis_797_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 797 =
      ([1, 1, -1, -2, -3, 2, -1, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_797_exact

/-- Exact source-selected ten-factor product at original index 813, point p0. -/
theorem p0_basis_813_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 813 =
      ([1, 1, -1, -2, 4, -1, 2, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_813_exact

/-- Exact source-selected ten-factor product at original index 813, point p2. -/
theorem p2_basis_813_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 813 =
      ([1, 1, -1, -2, 4, -1, -1, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_813_exact

end
end AspisV8R19.R768Point02LeavesChunk02
