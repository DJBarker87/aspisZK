/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep13 : (fun j => shift half 1 p12 j-(13:M)*p12 j)=p13 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep13
end AspisR19.WitnessRootData
