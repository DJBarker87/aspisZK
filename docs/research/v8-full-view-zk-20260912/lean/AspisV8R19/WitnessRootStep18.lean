/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep18 : (fun j => shift half 1 p17 j-(18:M)*p17 j)=p18 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep18
end AspisR19.WitnessRootData
