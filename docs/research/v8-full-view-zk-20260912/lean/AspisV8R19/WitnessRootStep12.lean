/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep12 : (fun j => shift half 1 p11 j-(12:M)*p11 j)=p12 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep12
end AspisR19.WitnessRootData
