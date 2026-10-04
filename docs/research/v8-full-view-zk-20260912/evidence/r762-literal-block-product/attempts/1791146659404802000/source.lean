import AspisV8R19.R752SCC00Inverse
import AspisV8R19.R752SCC01Inverse

namespace AspisV8R19.R763TwoFactorProbe

theorem unit_pair : IsUnit (Matrix.det R752SCC00Matrix.A_scc * Matrix.det R752SCC01Matrix.A_scc) := by
  exact IsUnit.mul R752SCC00Inverse.determinant_isUnit R752SCC01Inverse.determinant_isUnit

#print axioms unit_pair

end AspisV8R19.R763TwoFactorProbe
