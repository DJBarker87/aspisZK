/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem shiftStep2 : shift half 1 s1=s2 := by
  funext j
  fin_cases j <;> decide
#print axioms shiftStep2
end AspisR19.WitnessRootData
