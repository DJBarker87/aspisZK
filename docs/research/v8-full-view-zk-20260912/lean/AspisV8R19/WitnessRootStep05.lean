/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep05 : (fun j => shift half 1 p4 j-(5:M)*p4 j)=p5 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep05
end AspisR19.WitnessRootData
