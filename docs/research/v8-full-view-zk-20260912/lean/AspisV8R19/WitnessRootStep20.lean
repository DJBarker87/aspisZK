/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootData
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel
theorem rootStep20 : (fun j => shift half 1 p19 j-(20:M)*p19 j)=p20 := by
  funext j
  fin_cases j <;> decide
#print axioms rootStep20
end AspisR19.WitnessRootData
