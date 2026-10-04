import AspisV8R19.R750WitnessPointSupport

namespace AspisV8R19.R768Point02LeavesChunk04
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.SourceStatementPoints
open AspisR19.R750WitnessPointSupport
noncomputable section
set_option autoImplicit false
variable {F : Type*} [CommRing F]

/-- Exact source-selected ten-factor product at original index 792, point p0. -/
theorem p0_basis_792_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 792 =
      ([1, 1, -1, -2, -3, 2, 2, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_792_exact

/-- Exact source-selected ten-factor product at original index 792, point p2. -/
theorem p2_basis_792_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 792 =
      ([1, 1, -1, -2, -3, 2, -1, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_792_exact

/-- Exact source-selected ten-factor product at original index 904, point p0. -/
theorem p0_basis_904_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 904 =
      ([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_904_exact

/-- Exact source-selected ten-factor product at original index 904, point p2. -/
theorem p2_basis_904_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 904 =
      ([1, 1, 2, -2, -3, -1, -1, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_904_exact

/-- Exact source-selected ten-factor product at original index 905, point p0. -/
theorem p0_basis_905_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 905 =
      ([1, 1, 2, -2, -3, -1, 2, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_905_exact

/-- Exact source-selected ten-factor product at original index 905, point p2. -/
theorem p2_basis_905_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 905 =
      ([1, 1, 2, -2, -3, -1, -1, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_905_exact

/-- Exact source-selected ten-factor product at original index 920, point p0. -/
theorem p0_basis_920_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 920 =
      ([1, 1, 2, -2, -3, 2, 2, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_920_exact

/-- Exact source-selected ten-factor product at original index 920, point p2. -/
theorem p2_basis_920_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 920 =
      ([1, 1, 2, -2, -3, 2, -1, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_920_exact

/-- Exact source-selected ten-factor product at original index 936, point p0. -/
theorem p0_basis_936_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 936 =
      ([1, 1, 2, -2, 4, -1, 2, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_936_exact

/-- Exact source-selected ten-factor product at original index 936, point p2. -/
theorem p2_basis_936_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 936 =
      ([1, 1, 2, -2, 4, -1, -1, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_936_exact

/-- Exact source-selected ten-factor product at original index 952, point p0. -/
theorem p0_basis_952_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 952 =
      ([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_952_exact

/-- Exact source-selected ten-factor product at original index 952, point p2. -/
theorem p2_basis_952_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 952 =
      ([1, 1, 2, -2, 4, 2, -1, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_952_exact

/-- Exact source-selected ten-factor product at original index 968, point p0. -/
theorem p0_basis_968_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 968 =
      ([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_968_exact

/-- Exact source-selected ten-factor product at original index 968, point p2. -/
theorem p2_basis_968_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 968 =
      ([1, 1, 2, 3, -3, -1, -1, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_968_exact

/-- Exact source-selected ten-factor product at original index 984, point p0. -/
theorem p0_basis_984_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 984 =
      ([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_984_exact

/-- Exact source-selected ten-factor product at original index 984, point p2. -/
theorem p2_basis_984_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 984 =
      ([1, 1, 2, 3, -3, 2, -1, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_984_exact

/-- Exact source-selected ten-factor product at original index 1000, point p0. -/
theorem p0_basis_1000_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 1000 =
      ([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_1000_exact

/-- Exact source-selected ten-factor product at original index 1000, point p2. -/
theorem p2_basis_1000_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 1000 =
      ([1, 1, 2, 3, 4, -1, -1, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_1000_exact

/-- Exact source-selected ten-factor product at original index 1016, point p0. -/
theorem p0_basis_1016_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 1016 =
      ([1, 1, 2, 3, 4, 2, 2, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_1016_exact

/-- Exact source-selected ten-factor product at original index 1016, point p2. -/
theorem p2_basis_1016_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 1016 =
      ([1, 1, 2, 3, 4, 2, -1, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_1016_exact

/-- Exact source-selected ten-factor product at original index 772, point p0. -/
theorem p0_basis_772_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 772 =
      ([1, 1, -1, -2, -3, -1, -1, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_772_exact

/-- Exact source-selected ten-factor product at original index 772, point p2. -/
theorem p2_basis_772_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 772 =
      ([1, 1, -1, -2, -3, -1, 2, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_772_exact

/-- Exact source-selected ten-factor product at original index 900, point p0. -/
theorem p0_basis_900_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 900 =
      ([1, 1, 2, -2, -3, -1, -1, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_900_exact

/-- Exact source-selected ten-factor product at original index 900, point p2. -/
theorem p2_basis_900_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 900 =
      ([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_900_exact

/-- Exact source-selected ten-factor product at original index 901, point p0. -/
theorem p0_basis_901_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 901 =
      ([1, 1, 2, -2, -3, -1, -1, 3, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_901_exact

/-- Exact source-selected ten-factor product at original index 901, point p2. -/
theorem p2_basis_901_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 901 =
      ([1, 1, 2, -2, -3, -1, 2, -2, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_901_exact

/-- Exact source-selected ten-factor product at original index 916, point p0. -/
theorem p0_basis_916_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 916 =
      ([1, 1, 2, -2, -3, 2, -1, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_916_exact

/-- Exact source-selected ten-factor product at original index 916, point p2. -/
theorem p2_basis_916_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 916 =
      ([1, 1, 2, -2, -3, 2, 2, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_916_exact

/-- Exact source-selected ten-factor product at original index 932, point p0. -/
theorem p0_basis_932_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 932 =
      ([1, 1, 2, -2, 4, -1, -1, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_932_exact

/-- Exact source-selected ten-factor product at original index 932, point p2. -/
theorem p2_basis_932_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 932 =
      ([1, 1, 2, -2, 4, -1, 2, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_932_exact

/-- Exact source-selected ten-factor product at original index 948, point p0. -/
theorem p0_basis_948_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 948 =
      ([1, 1, 2, -2, 4, 2, -1, 3, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_948_exact

/-- Exact source-selected ten-factor product at original index 948, point p2. -/
theorem p2_basis_948_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 948 =
      ([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_948_exact

end
end AspisV8R19.R768Point02LeavesChunk04
