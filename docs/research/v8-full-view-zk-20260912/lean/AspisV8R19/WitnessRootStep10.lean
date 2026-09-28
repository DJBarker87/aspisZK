/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep10 : (fun j => shift half 1 p9 j-(10:M)*p9 j)=p10 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep10
end AspisR19.WitnessRootData
