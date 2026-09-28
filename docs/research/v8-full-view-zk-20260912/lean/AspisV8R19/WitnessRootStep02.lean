/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep02 : (fun j => shift half 1 p1 j-(2:M)*p1 j)=p2 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep02
end AspisR19.WitnessRootData
