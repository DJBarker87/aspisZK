/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep15 : (fun j => shift half 1 p14 j-(15:M)*p14 j)=p15 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep15
end AspisR19.WitnessRootData
