/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep14 : (fun j => shift half 1 p13 j-(14:M)*p13 j)=p14 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep14
end AspisR19.WitnessRootData
