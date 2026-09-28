/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep11 : (fun j => shift half 1 p10 j-(11:M)*p10 j)=p11 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep11
end AspisR19.WitnessRootData
