/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep01 : (fun j => shift half 1 p0 j-(1:M)*p0 j)=p1 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep01
end AspisR19.WitnessRootData
