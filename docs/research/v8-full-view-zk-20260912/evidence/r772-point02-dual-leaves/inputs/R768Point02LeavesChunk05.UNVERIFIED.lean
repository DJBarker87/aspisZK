import AspisV8R19.R750WitnessPointSupport

namespace AspisV8R19.R768Point02LeavesChunk05
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.SourceStatementPoints
open AspisR19.R750WitnessPointSupport
noncomputable section
set_option autoImplicit false
variable {F : Type*} [CommRing F]

/-- Exact source-selected ten-factor product at original index 964, point p0. -/
theorem p0_basis_964_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 964 =
      ([1, 1, 2, 3, -3, -1, -1, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_964_exact

/-- Exact source-selected ten-factor product at original index 964, point p2. -/
theorem p2_basis_964_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 964 =
      ([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_964_exact

/-- Exact source-selected ten-factor product at original index 980, point p0. -/
theorem p0_basis_980_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 980 =
      ([1, 1, 2, 3, -3, 2, -1, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_980_exact

/-- Exact source-selected ten-factor product at original index 980, point p2. -/
theorem p2_basis_980_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 980 =
      ([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_980_exact

/-- Exact source-selected ten-factor product at original index 996, point p0. -/
theorem p0_basis_996_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 996 =
      ([1, 1, 2, 3, 4, -1, -1, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_996_exact

/-- Exact source-selected ten-factor product at original index 996, point p2. -/
theorem p2_basis_996_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 996 =
      ([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_996_exact

/-- Exact source-selected ten-factor product at original index 1013, point p0. -/
theorem p0_basis_1013_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 1013 =
      ([1, 1, 2, 3, 4, 2, -1, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_1013_exact

/-- Exact source-selected ten-factor product at original index 1013, point p2. -/
theorem p2_basis_1013_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 1013 =
      ([1, 1, 2, 3, 4, 2, 2, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_1013_exact

/-- Exact source-selected ten-factor product at original index 769, point p0. -/
theorem p0_basis_769_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 769 =
      ([1, 1, -1, -2, -3, -1, -1, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_769_exact

/-- Exact source-selected ten-factor product at original index 769, point p2. -/
theorem p2_basis_769_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 769 =
      ([1, 1, -1, -2, -3, -1, 2, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_769_exact

/-- Exact source-selected ten-factor product at original index 785, point p0. -/
theorem p0_basis_785_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 785 =
      ([1, 1, -1, -2, -3, 2, -1, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_785_exact

/-- Exact source-selected ten-factor product at original index 785, point p2. -/
theorem p2_basis_785_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 785 =
      ([1, 1, -1, -2, -3, 2, 2, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_785_exact

/-- Exact source-selected ten-factor product at original index 801, point p0. -/
theorem p0_basis_801_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 801 =
      ([1, 1, -1, -2, 4, -1, -1, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_801_exact

/-- Exact source-selected ten-factor product at original index 801, point p2. -/
theorem p2_basis_801_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 801 =
      ([1, 1, -1, -2, 4, -1, 2, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_801_exact

/-- Exact source-selected ten-factor product at original index 817, point p0. -/
theorem p0_basis_817_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 817 =
      ([1, 1, -1, -2, 4, 2, -1, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_817_exact

/-- Exact source-selected ten-factor product at original index 817, point p2. -/
theorem p2_basis_817_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 817 =
      ([1, 1, -1, -2, 4, 2, 2, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_817_exact

/-- Exact source-selected ten-factor product at original index 833, point p0. -/
theorem p0_basis_833_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 833 =
      ([1, 1, -1, 3, -3, -1, -1, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_833_exact

/-- Exact source-selected ten-factor product at original index 833, point p2. -/
theorem p2_basis_833_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 833 =
      ([1, 1, -1, 3, -3, -1, 2, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_833_exact

/-- Exact source-selected ten-factor product at original index 849, point p0. -/
theorem p0_basis_849_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 849 =
      ([1, 1, -1, 3, -3, 2, -1, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_849_exact

/-- Exact source-selected ten-factor product at original index 849, point p2. -/
theorem p2_basis_849_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 849 =
      ([1, 1, -1, 3, -3, 2, 2, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_849_exact

/-- Exact source-selected ten-factor product at original index 865, point p0. -/
theorem p0_basis_865_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 865 =
      ([1, 1, -1, 3, 4, -1, -1, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_865_exact

/-- Exact source-selected ten-factor product at original index 865, point p2. -/
theorem p2_basis_865_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 865 =
      ([1, 1, -1, 3, 4, -1, 2, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_865_exact

/-- Exact source-selected ten-factor product at original index 881, point p0. -/
theorem p0_basis_881_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 881 =
      ([1, 1, -1, 3, 4, 2, -1, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_881_exact

/-- Exact source-selected ten-factor product at original index 881, point p2. -/
theorem p2_basis_881_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 881 =
      ([1, 1, -1, 3, 4, 2, 2, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_881_exact

/-- Exact source-selected ten-factor product at original index 897, point p0. -/
theorem p0_basis_897_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 897 =
      ([1, 1, 2, -2, -3, -1, -1, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_897_exact

/-- Exact source-selected ten-factor product at original index 897, point p2. -/
theorem p2_basis_897_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 897 =
      ([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_897_exact

/-- Exact source-selected ten-factor product at original index 912, point p0. -/
theorem p0_basis_912_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 912 =
      ([1, 1, 2, -2, -3, 2, -1, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_912_exact

/-- Exact source-selected ten-factor product at original index 912, point p2. -/
theorem p2_basis_912_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 912 =
      ([1, 1, 2, -2, -3, 2, 2, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_912_exact

/-- Exact source-selected ten-factor product at original index 928, point p0. -/
theorem p0_basis_928_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 928 =
      ([1, 1, 2, -2, 4, -1, -1, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_928_exact

/-- Exact source-selected ten-factor product at original index 928, point p2. -/
theorem p2_basis_928_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 928 =
      ([1, 1, 2, -2, 4, -1, 2, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_928_exact

/-- Exact source-selected ten-factor product at original index 944, point p0. -/
theorem p0_basis_944_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 944 =
      ([1, 1, 2, -2, 4, 2, -1, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_944_exact

/-- Exact source-selected ten-factor product at original index 944, point p2. -/
theorem p2_basis_944_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 944 =
      ([1, 1, 2, -2, 4, 2, 2, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_944_exact

end
end AspisV8R19.R768Point02LeavesChunk05
