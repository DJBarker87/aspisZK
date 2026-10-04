import AspisV8R19.R750WitnessPointSupport

namespace AspisV8R19.R768Point02LeavesChunk00
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.SourceStatementPoints
open AspisR19.R750WitnessPointSupport
noncomputable section
set_option autoImplicit false
variable {F : Type*} [CommRing F]

/-- Exact source-selected ten-factor product at original index 780, point p0. -/
theorem p0_basis_780_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 780 =
      ([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_780_exact

/-- Exact source-selected ten-factor product at original index 780, point p2. -/
theorem p2_basis_780_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 780 =
      ([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_780_exact

/-- Exact source-selected ten-factor product at original index 796, point p0. -/
theorem p0_basis_796_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 796 =
      ([1, 1, -1, -2, -3, 2, 2, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_796_exact

/-- Exact source-selected ten-factor product at original index 796, point p2. -/
theorem p2_basis_796_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 796 =
      ([1, 1, -1, -2, -3, 2, -1, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_796_exact

/-- Exact source-selected ten-factor product at original index 812, point p0. -/
theorem p0_basis_812_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 812 =
      ([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_812_exact

/-- Exact source-selected ten-factor product at original index 812, point p2. -/
theorem p2_basis_812_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 812 =
      ([1, 1, -1, -2, 4, -1, -1, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_812_exact

/-- Exact source-selected ten-factor product at original index 828, point p0. -/
theorem p0_basis_828_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 828 =
      ([1, 1, -1, -2, 4, 2, 2, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_828_exact

/-- Exact source-selected ten-factor product at original index 828, point p2. -/
theorem p2_basis_828_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 828 =
      ([1, 1, -1, -2, 4, 2, -1, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_828_exact

/-- Exact source-selected ten-factor product at original index 844, point p0. -/
theorem p0_basis_844_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 844 =
      ([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_844_exact

/-- Exact source-selected ten-factor product at original index 844, point p2. -/
theorem p2_basis_844_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 844 =
      ([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_844_exact

/-- Exact source-selected ten-factor product at original index 860, point p0. -/
theorem p0_basis_860_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 860 =
      ([1, 1, -1, 3, -3, 2, 2, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_860_exact

/-- Exact source-selected ten-factor product at original index 860, point p2. -/
theorem p2_basis_860_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 860 =
      ([1, 1, -1, 3, -3, 2, -1, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_860_exact

/-- Exact source-selected ten-factor product at original index 876, point p0. -/
theorem p0_basis_876_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 876 =
      ([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_876_exact

/-- Exact source-selected ten-factor product at original index 876, point p2. -/
theorem p2_basis_876_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 876 =
      ([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_876_exact

/-- Exact source-selected ten-factor product at original index 892, point p0. -/
theorem p0_basis_892_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 892 =
      ([1, 1, -1, 3, 4, 2, 2, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_892_exact

/-- Exact source-selected ten-factor product at original index 892, point p2. -/
theorem p2_basis_892_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 892 =
      ([1, 1, -1, 3, 4, 2, -1, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_892_exact

/-- Exact source-selected ten-factor product at original index 908, point p0. -/
theorem p0_basis_908_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 908 =
      ([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_908_exact

/-- Exact source-selected ten-factor product at original index 908, point p2. -/
theorem p2_basis_908_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 908 =
      ([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_908_exact

/-- Exact source-selected ten-factor product at original index 925, point p0. -/
theorem p0_basis_925_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 925 =
      ([1, 1, 2, -2, -3, 2, 2, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_925_exact

/-- Exact source-selected ten-factor product at original index 925, point p2. -/
theorem p2_basis_925_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 925 =
      ([1, 1, 2, -2, -3, 2, -1, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_925_exact

/-- Exact source-selected ten-factor product at original index 941, point p0. -/
theorem p0_basis_941_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 941 =
      ([1, 1, 2, -2, 4, -1, 2, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_941_exact

/-- Exact source-selected ten-factor product at original index 941, point p2. -/
theorem p2_basis_941_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 941 =
      ([1, 1, 2, -2, 4, -1, -1, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_941_exact

/-- Exact source-selected ten-factor product at original index 957, point p0. -/
theorem p0_basis_957_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 957 =
      ([1, 1, 2, -2, 4, 2, 2, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_957_exact

/-- Exact source-selected ten-factor product at original index 957, point p2. -/
theorem p2_basis_957_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 957 =
      ([1, 1, 2, -2, 4, 2, -1, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_957_exact

/-- Exact source-selected ten-factor product at original index 973, point p0. -/
theorem p0_basis_973_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 973 =
      ([1, 1, 2, 3, -3, -1, 2, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_973_exact

/-- Exact source-selected ten-factor product at original index 973, point p2. -/
theorem p2_basis_973_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 973 =
      ([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_973_exact

/-- Exact source-selected ten-factor product at original index 989, point p0. -/
theorem p0_basis_989_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 989 =
      ([1, 1, 2, 3, -3, 2, 2, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_989_exact

/-- Exact source-selected ten-factor product at original index 989, point p2. -/
theorem p2_basis_989_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 989 =
      ([1, 1, 2, 3, -3, 2, -1, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_989_exact

/-- Exact source-selected ten-factor product at original index 1005, point p0. -/
theorem p0_basis_1005_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 1005 =
      ([1, 1, 2, 3, 4, -1, 2, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_1005_exact

/-- Exact source-selected ten-factor product at original index 1005, point p2. -/
theorem p2_basis_1005_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 1005 =
      ([1, 1, 2, 3, 4, -1, -1, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_1005_exact

/-- Exact source-selected ten-factor product at original index 921, point p0. -/
theorem p0_basis_921_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 921 =
      ([1, 1, 2, -2, -3, 2, 2, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_921_exact

/-- Exact source-selected ten-factor product at original index 921, point p2. -/
theorem p2_basis_921_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 921 =
      ([1, 1, 2, -2, -3, 2, -1, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_921_exact

end
end AspisV8R19.R768Point02LeavesChunk00
