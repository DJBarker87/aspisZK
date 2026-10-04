import AspisV8R19.R750WitnessPointSupport

namespace AspisV8R19.R768Point02LeavesChunk01
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.SourceStatementPoints
open AspisR19.R750WitnessPointSupport
noncomputable section
set_option autoImplicit false
variable {F : Type*} [CommRing F]

/-- Exact source-selected ten-factor product at original index 937, point p0. -/
theorem p0_basis_937_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 937 =
      ([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_937_exact

/-- Exact source-selected ten-factor product at original index 937, point p2. -/
theorem p2_basis_937_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 937 =
      ([1, 1, 2, -2, 4, -1, -1, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_937_exact

/-- Exact source-selected ten-factor product at original index 953, point p0. -/
theorem p0_basis_953_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 953 =
      ([1, 1, 2, -2, 4, 2, 2, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_953_exact

/-- Exact source-selected ten-factor product at original index 953, point p2. -/
theorem p2_basis_953_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 953 =
      ([1, 1, 2, -2, 4, 2, -1, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_953_exact

/-- Exact source-selected ten-factor product at original index 969, point p0. -/
theorem p0_basis_969_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 969 =
      ([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_969_exact

/-- Exact source-selected ten-factor product at original index 969, point p2. -/
theorem p2_basis_969_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 969 =
      ([1, 1, 2, 3, -3, -1, -1, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_969_exact

/-- Exact source-selected ten-factor product at original index 985, point p0. -/
theorem p0_basis_985_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 985 =
      ([1, 1, 2, 3, -3, 2, 2, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_985_exact

/-- Exact source-selected ten-factor product at original index 985, point p2. -/
theorem p2_basis_985_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 985 =
      ([1, 1, 2, 3, -3, 2, -1, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_985_exact

/-- Exact source-selected ten-factor product at original index 1001, point p0. -/
theorem p0_basis_1001_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 1001 =
      ([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_1001_exact

/-- Exact source-selected ten-factor product at original index 1001, point p2. -/
theorem p2_basis_1001_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 1001 =
      ([1, 1, 2, 3, 4, -1, -1, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_1001_exact

/-- Exact source-selected ten-factor product at original index 1017, point p0. -/
theorem p0_basis_1017_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 1017 =
      ([1, 1, 2, 3, 4, 2, 2, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_1017_exact

/-- Exact source-selected ten-factor product at original index 1017, point p2. -/
theorem p2_basis_1017_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 1017 =
      ([1, 1, 2, 3, 4, 2, -1, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_1017_exact

/-- Exact source-selected ten-factor product at original index 917, point p0. -/
theorem p0_basis_917_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 917 =
      ([1, 1, 2, -2, -3, 2, -1, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_917_exact

/-- Exact source-selected ten-factor product at original index 917, point p2. -/
theorem p2_basis_917_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 917 =
      ([1, 1, 2, -2, -3, 2, 2, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_917_exact

/-- Exact source-selected ten-factor product at original index 933, point p0. -/
theorem p0_basis_933_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 933 =
      ([1, 1, 2, -2, 4, -1, -1, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_933_exact

/-- Exact source-selected ten-factor product at original index 933, point p2. -/
theorem p2_basis_933_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 933 =
      ([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_933_exact

/-- Exact source-selected ten-factor product at original index 949, point p0. -/
theorem p0_basis_949_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 949 =
      ([1, 1, 2, -2, 4, 2, -1, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_949_exact

/-- Exact source-selected ten-factor product at original index 949, point p2. -/
theorem p2_basis_949_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 949 =
      ([1, 1, 2, -2, 4, 2, 2, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_949_exact

/-- Exact source-selected ten-factor product at original index 965, point p0. -/
theorem p0_basis_965_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 965 =
      ([1, 1, 2, 3, -3, -1, -1, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_965_exact

/-- Exact source-selected ten-factor product at original index 965, point p2. -/
theorem p2_basis_965_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 965 =
      ([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_965_exact

/-- Exact source-selected ten-factor product at original index 981, point p0. -/
theorem p0_basis_981_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 981 =
      ([1, 1, 2, 3, -3, 2, -1, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_981_exact

/-- Exact source-selected ten-factor product at original index 981, point p2. -/
theorem p2_basis_981_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 981 =
      ([1, 1, 2, 3, -3, 2, 2, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_981_exact

/-- Exact source-selected ten-factor product at original index 997, point p0. -/
theorem p0_basis_997_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 997 =
      ([1, 1, 2, 3, 4, -1, -1, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_997_exact

/-- Exact source-selected ten-factor product at original index 997, point p2. -/
theorem p2_basis_997_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 997 =
      ([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_997_exact

/-- Exact source-selected ten-factor product at original index 1012, point p0. -/
theorem p0_basis_1012_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 1012 =
      ([1, 1, 2, 3, 4, 2, -1, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_1012_exact

/-- Exact source-selected ten-factor product at original index 1012, point p2. -/
theorem p2_basis_1012_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 1012 =
      ([1, 1, 2, 3, 4, 2, 2, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_1012_exact

/-- Exact source-selected ten-factor product at original index 768, point p0. -/
theorem p0_basis_768_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 768 =
      ([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_768_exact

/-- Exact source-selected ten-factor product at original index 768, point p2. -/
theorem p2_basis_768_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 768 =
      ([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_768_exact

/-- Exact source-selected ten-factor product at original index 784, point p0. -/
theorem p0_basis_784_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 784 =
      ([1, 1, -1, -2, -3, 2, -1, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_784_exact

/-- Exact source-selected ten-factor product at original index 784, point p2. -/
theorem p2_basis_784_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 784 =
      ([1, 1, -1, -2, -3, 2, 2, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_784_exact

/-- Exact source-selected ten-factor product at original index 800, point p0. -/
theorem p0_basis_800_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 800 =
      ([1, 1, -1, -2, 4, -1, -1, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_800_exact

/-- Exact source-selected ten-factor product at original index 800, point p2. -/
theorem p2_basis_800_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 800 =
      ([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_800_exact

end
end AspisV8R19.R768Point02LeavesChunk01
