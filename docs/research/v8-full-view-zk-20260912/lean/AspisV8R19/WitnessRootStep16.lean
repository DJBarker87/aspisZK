/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep16 : (fun j => shift half 1 p15 j-(16:M)*p15 j)=p16 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep16
end AspisR19.WitnessRootData
