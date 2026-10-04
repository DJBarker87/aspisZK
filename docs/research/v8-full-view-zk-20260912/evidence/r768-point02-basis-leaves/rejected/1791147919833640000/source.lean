import AspisV8R19.R750WitnessPointSupport

namespace AspisV8R19.R768Point02BasisLeaves
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.SourceStatementPoints
open AspisR19.R750WitnessPointSupport
noncomputable section
set_option autoImplicit false

variable {F : Type*} [CommRing F]

/-- The p0 source-shaped basis at original index 993, retained as its exact
ordered ten-factor product rather than evaluated in the field. -/
theorem p0_basis_993_exact :
    sourcePointBasis (points (zFin10 (F := F)) 0) 993 =
      ([1, 1, 2, 3, 4, -1, -1, -2, 1, 2] : List F).prod := by
  rw [points0_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10]

/-- The p2 source-shaped basis at original index 993, retained as its exact
ordered ten-factor product rather than evaluated in the field. -/
theorem p2_basis_993_exact :
    sourcePointBasis (points (zFin10 (F := F)) 2) 993 =
      ([1, 1, 2, 3, 4, -1, 2, 3, 1, 2] : List F).prod := by
  rw [points2_exact]
  simp [sourcePointBasis, sourceMultilinearFactors, zFin10]

#print axioms p0_basis_993_exact
#print axioms p2_basis_993_exact

end
end AspisV8R19.R768Point02BasisLeaves
