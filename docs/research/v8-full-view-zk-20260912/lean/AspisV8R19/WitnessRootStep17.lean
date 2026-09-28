/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep17 : (fun j => shift half 1 p16 j-(17:M)*p16 j)=p17 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep17
end AspisR19.WitnessRootData
