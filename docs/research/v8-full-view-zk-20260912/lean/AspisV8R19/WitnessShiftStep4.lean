/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem shiftStep4 : shift half 1 s3=s4 := by
  funext j
  fin_cases j <;> decide
#print axioms shiftStep4
end AspisR19.WitnessRootData
