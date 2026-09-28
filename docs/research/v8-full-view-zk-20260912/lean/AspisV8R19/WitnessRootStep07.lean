/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep07 : (fun j => shift half 1 p6 j-(7:M)*p6 j)=p7 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep07
end AspisR19.WitnessRootData
