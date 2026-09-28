/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep22 : (fun j => shift half 1 p21 j-(22:M)*p21 j)=p22 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep22
end AspisR19.WitnessRootData
