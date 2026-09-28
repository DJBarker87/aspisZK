/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep06 : (fun j => shift half 1 p5 j-(6:M)*p5 j)=p6 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep06
end AspisR19.WitnessRootData
