/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessEntryData
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem padding : (fun j : Fin 27 => if h : j.val<23 then SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots ⟨j.val,h⟩ else 0) = WitnessRootData.p22 := by
  simp only [WitnessRootData.root_coefficients]
  funext j
  fin_cases j <;> decide
theorem wr_stage : (fun r => (5:M)*WitnessPointData.weights0 r+5^2*WitnessPointData.weights1 r+5^3*WitnessPointData.weights2 r) = wr := by
  funext r
  fin_cases r <;> decide
#print axioms wr_stage
theorem wg_stage : (fun r => (5:M)^2*WitnessPointData.weights1 r+5^3*WitnessPointData.weights2 r) = wg := by
  funext r
  fin_cases r <;> decide
#print axioms wg_stage
#print axioms padding
end
end AspisR19.WitnessEntryData
