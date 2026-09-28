/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep03 : (fun j => shift half 1 p2 j-(3:M)*p2 j)=p3 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep03
end AspisR19.WitnessRootData
