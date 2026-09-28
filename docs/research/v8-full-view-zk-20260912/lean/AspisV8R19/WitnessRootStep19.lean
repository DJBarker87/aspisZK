/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep19 : (fun j => shift half 1 p18 j-(19:M)*p18 j)=p19 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep19
end AspisR19.WitnessRootData
