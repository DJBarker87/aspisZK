import AspisV8R19.R748JointWitnessPointEntry

/-! Generated finite point-1 basis values. Each lemma reduces exactly ten source factors; R754 separately supplies the shared pivot 1023. -/
namespace AspisV8R19.R753Point1BasisValues
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R748JointWitnessPointEntry
noncomputable section

/-- index 1019; ten factors: 1 * 1 * 2 * 3 * 4 * 2 * 2 * -2 * 2 * -1 -/
lemma point1_basis_1019 : sourcePointBasis point 1019 = (384:M) := by
  rw [point_eq_p]
  norm_num [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p] <;> decide
#print axioms point1_basis_1019

/-- index 1020; ten factors: 1 * 1 * 2 * 3 * 4 * 2 * 2 * 3 * -1 * 2 -/
lemma point1_basis_1020 : sourcePointBasis point 1020 = (2147483071:M) := by
  rw [point_eq_p]
  norm_num [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p] <;> decide
#print axioms point1_basis_1020

/-- index 1021; ten factors: 1 * 1 * 2 * 3 * 4 * 2 * 2 * 3 * -1 * -1 -/
lemma point1_basis_1021 : sourcePointBasis point 1021 = (288:M) := by
  rw [point_eq_p]
  norm_num [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p] <;> decide
#print axioms point1_basis_1021

/-- index 1022; ten factors: 1 * 1 * 2 * 3 * 4 * 2 * 2 * 3 * 2 * 2 -/
lemma point1_basis_1022 : sourcePointBasis point 1022 = (1152:M) := by
  rw [point_eq_p]
  norm_num [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p] <;> decide
#print axioms point1_basis_1022

end
end AspisV8R19.R753Point1BasisValues
