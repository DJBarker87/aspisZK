/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep21 : (fun j => shift half 1 p20 j-(21:M)*p20 j)=p21 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep21
end AspisR19.WitnessRootData
