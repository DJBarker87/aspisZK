/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep09 : (fun j => shift half 1 p8 j-(9:M)*p8 j)=p9 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep09
end AspisR19.WitnessRootData
