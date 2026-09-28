/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep04 : (fun j => shift half 1 p3 j-(4:M)*p3 j)=p4 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep04
end AspisR19.WitnessRootData
