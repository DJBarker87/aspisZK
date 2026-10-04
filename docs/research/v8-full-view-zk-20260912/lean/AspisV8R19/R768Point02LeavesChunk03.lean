import AspisV8R19.R750WitnessPointSupport

namespace AspisV8R19.R768Point02LeavesChunk03
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.SourceStatementPoints
open AspisR19.R750WitnessPointSupport
noncomputable section
set_option autoImplicit false
variable {F : Type*} [CommRing F]

/-- Exact source-selected ten-factor product at original index 829, point p0. -/
theorem p0_basis_829_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 829 =
      ([1, 1, -1, -2, 4, 2, 2, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_829_exact

/-- Exact source-selected ten-factor product at original index 829, point p2. -/
theorem p2_basis_829_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 829 =
      ([1, 1, -1, -2, 4, 2, -1, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_829_exact

/-- Exact source-selected ten-factor product at original index 845, point p0. -/
theorem p0_basis_845_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 845 =
      ([1, 1, -1, 3, -3, -1, 2, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_845_exact

/-- Exact source-selected ten-factor product at original index 845, point p2. -/
theorem p2_basis_845_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 845 =
      ([1, 1, -1, 3, -3, -1, -1, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_845_exact

/-- Exact source-selected ten-factor product at original index 861, point p0. -/
theorem p0_basis_861_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 861 =
      ([1, 1, -1, 3, -3, 2, 2, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_861_exact

/-- Exact source-selected ten-factor product at original index 861, point p2. -/
theorem p2_basis_861_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 861 =
      ([1, 1, -1, 3, -3, 2, -1, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_861_exact

/-- Exact source-selected ten-factor product at original index 877, point p0. -/
theorem p0_basis_877_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 877 =
      ([1, 1, -1, 3, 4, -1, 2, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_877_exact

/-- Exact source-selected ten-factor product at original index 877, point p2. -/
theorem p2_basis_877_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 877 =
      ([1, 1, -1, 3, 4, -1, -1, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_877_exact

/-- Exact source-selected ten-factor product at original index 893, point p0. -/
theorem p0_basis_893_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 893 =
      ([1, 1, -1, 3, 4, 2, 2, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_893_exact

/-- Exact source-selected ten-factor product at original index 893, point p2. -/
theorem p2_basis_893_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 893 =
      ([1, 1, -1, 3, 4, 2, -1, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_893_exact

/-- Exact source-selected ten-factor product at original index 909, point p0. -/
theorem p0_basis_909_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 909 =
      ([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_909_exact

/-- Exact source-selected ten-factor product at original index 909, point p2. -/
theorem p2_basis_909_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 909 =
      ([1, 1, 2, -2, -3, -1, -1, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_909_exact

/-- Exact source-selected ten-factor product at original index 924, point p0. -/
theorem p0_basis_924_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 924 =
      ([1, 1, 2, -2, -3, 2, 2, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_924_exact

/-- Exact source-selected ten-factor product at original index 924, point p2. -/
theorem p2_basis_924_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 924 =
      ([1, 1, 2, -2, -3, 2, -1, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_924_exact

/-- Exact source-selected ten-factor product at original index 940, point p0. -/
theorem p0_basis_940_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 940 =
      ([1, 1, 2, -2, 4, -1, 2, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_940_exact

/-- Exact source-selected ten-factor product at original index 940, point p2. -/
theorem p2_basis_940_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 940 =
      ([1, 1, 2, -2, 4, -1, -1, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_940_exact

/-- Exact source-selected ten-factor product at original index 956, point p0. -/
theorem p0_basis_956_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 956 =
      ([1, 1, 2, -2, 4, 2, 2, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_956_exact

/-- Exact source-selected ten-factor product at original index 956, point p2. -/
theorem p2_basis_956_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 956 =
      ([1, 1, 2, -2, 4, 2, -1, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_956_exact

/-- Exact source-selected ten-factor product at original index 972, point p0. -/
theorem p0_basis_972_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 972 =
      ([1, 1, 2, 3, -3, -1, 2, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_972_exact

/-- Exact source-selected ten-factor product at original index 972, point p2. -/
theorem p2_basis_972_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 972 =
      ([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_972_exact

/-- Exact source-selected ten-factor product at original index 988, point p0. -/
theorem p0_basis_988_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 988 =
      ([1, 1, 2, 3, -3, 2, 2, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_988_exact

/-- Exact source-selected ten-factor product at original index 988, point p2. -/
theorem p2_basis_988_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 988 =
      ([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_988_exact

/-- Exact source-selected ten-factor product at original index 1004, point p0. -/
theorem p0_basis_1004_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 1004 =
      ([1, 1, 2, 3, 4, -1, 2, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_1004_exact

/-- Exact source-selected ten-factor product at original index 1004, point p2. -/
theorem p2_basis_1004_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 1004 =
      ([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_1004_exact

/-- Exact source-selected ten-factor product at original index 1020, point p0. -/
theorem p0_basis_1020_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 1020 =
      ([1, 1, 2, 3, 4, 2, 2, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_1020_exact

/-- Exact source-selected ten-factor product at original index 1020, point p2. -/
theorem p2_basis_1020_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 1020 =
      ([1, 1, 2, 3, 4, 2, -1, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_1020_exact

/-- Exact source-selected ten-factor product at original index 1021, point p0. -/
theorem p0_basis_1021_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 1021 =
      ([1, 1, 2, 3, 4, 2, 2, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_1021_exact

/-- Exact source-selected ten-factor product at original index 1021, point p2. -/
theorem p2_basis_1021_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 1021 =
      ([1, 1, 2, 3, 4, 2, -1, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_1021_exact

/-- Exact source-selected ten-factor product at original index 776, point p0. -/
theorem p0_basis_776_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 776 =
      ([1, 1, -1, -2, -3, -1, 2, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_776_exact

/-- Exact source-selected ten-factor product at original index 776, point p2. -/
theorem p2_basis_776_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 776 =
      ([1, 1, -1, -2, -3, -1, -1, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_776_exact

/-- Exact source-selected ten-factor product at original index 777, point p0. -/
theorem p0_basis_777_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 777 =
      ([1, 1, -1, -2, -3, -1, 2, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_777_exact

/-- Exact source-selected ten-factor product at original index 777, point p2. -/
theorem p2_basis_777_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 777 =
      ([1, 1, -1, -2, -3, -1, -1, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_777_exact

end
end AspisV8R19.R768Point02LeavesChunk03
