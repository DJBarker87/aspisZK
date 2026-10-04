import AspisV8R19.R750WitnessPointSupport

namespace AspisV8R19.R768Point02LeavesChunk06
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.SourceStatementPoints
open AspisR19.R750WitnessPointSupport
noncomputable section
set_option autoImplicit false
variable {F : Type*} [CommRing F]

/-- Exact source-selected ten-factor product at original index 960, point p0. -/
theorem p0_basis_960_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 960 =
      ([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_960_exact

/-- Exact source-selected ten-factor product at original index 960, point p2. -/
theorem p2_basis_960_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 960 =
      ([1, 1, 2, 3, -3, -1, 2, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_960_exact

/-- Exact source-selected ten-factor product at original index 976, point p0. -/
theorem p0_basis_976_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 976 =
      ([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_976_exact

/-- Exact source-selected ten-factor product at original index 976, point p2. -/
theorem p2_basis_976_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 976 =
      ([1, 1, 2, 3, -3, 2, 2, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_976_exact

/-- Exact source-selected ten-factor product at original index 992, point p0. -/
theorem p0_basis_992_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 992 =
      ([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p0_basis_992_exact

/-- Exact source-selected ten-factor product at original index 992, point p2. -/
theorem p2_basis_992_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 992 =
      ([1, 1, 2, 3, 4, -1, 2, 3, 1, -1] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10] <;> ring
#print axioms p2_basis_992_exact

end
end AspisV8R19.R768Point02LeavesChunk06
