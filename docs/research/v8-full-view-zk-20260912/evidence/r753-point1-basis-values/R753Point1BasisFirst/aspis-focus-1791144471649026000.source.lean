import AspisV8R19.R748JointWitnessPointEntry

/-! Generated finite point-1 basis values. Each lemma reduces exactly ten source factors; R754 separately supplies the shared pivot 1023. -/
namespace AspisV8R19.R753Point1BasisValues
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R748JointWitnessPointEntry
noncomputable section

/-- index 768; ten factors: 1 * 1 * -1 * -2 * -3 * -1 * -1 * -2 * -1 * 2 -/
lemma point1_basis_768 : sourcePointBasis point 768 = (2147483623:M) := by
  rw [point_eq_p]
  norm_num [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p] <;> decide
#print axioms point1_basis_768

end
end AspisV8R19.R753Point1BasisValues
