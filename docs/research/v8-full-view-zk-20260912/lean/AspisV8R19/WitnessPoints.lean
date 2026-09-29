/- Generated staged point-weight certificate. Do not inline earlier stages. -/
import AspisV8R19.WitnessPointData
namespace AspisR19.WitnessPointData
open RootCertificate ResidualModel
noncomputable section
theorem point0 : point z 0 = coords0 := by
  funext j
  fin_cases j <;> decide
#print axioms point0
theorem point1 : point z 1 = coords1 := by
  funext j
  fin_cases j <;> decide
#print axioms point1
theorem point2 : point z 2 = coords2 := by
  funext j
  fin_cases j <;> decide
#print axioms point2
end
end AspisR19.WitnessPointData
