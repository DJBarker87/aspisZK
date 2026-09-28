/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem shiftStep1 : shift half 1 s0=s1 := by
  funext j
  fin_cases j <;> decide
#print axioms shiftStep1
end AspisR19.WitnessRootData
