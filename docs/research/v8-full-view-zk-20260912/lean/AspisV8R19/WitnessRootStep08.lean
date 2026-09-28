/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep08 : (fun j => shift half 1 p7 j-(8:M)*p7 j)=p8 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep08
end AspisR19.WitnessRootData
