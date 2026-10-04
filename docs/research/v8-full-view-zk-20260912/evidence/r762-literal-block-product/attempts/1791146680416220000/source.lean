import AspisV8R19.R752SCC00Inverse
import AspisV8R19.R752SCC01Inverse
import AspisV8R19.R752SCC02Inverse
import AspisV8R19.R752SCC03Inverse

namespace AspisV8R19.R763FourFactorProbe

theorem unit_chunk : IsUnit ((Matrix.det R752SCC00Matrix.A_scc * Matrix.det R752SCC01Matrix.A_scc) * (Matrix.det R752SCC02Matrix.A_scc * Matrix.det R752SCC03Matrix.A_scc)) := by
  have h01 : IsUnit (Matrix.det R752SCC00Matrix.A_scc * Matrix.det R752SCC01Matrix.A_scc) :=
    IsUnit.mul R752SCC00Inverse.determinant_isUnit R752SCC01Inverse.determinant_isUnit
  have h23 : IsUnit (Matrix.det R752SCC02Matrix.A_scc * Matrix.det R752SCC03Matrix.A_scc) :=
    IsUnit.mul R752SCC02Inverse.determinant_isUnit R752SCC03Inverse.determinant_isUnit
  exact IsUnit.mul h01 h23

#print axioms unit_chunk

end AspisV8R19.R763FourFactorProbe
