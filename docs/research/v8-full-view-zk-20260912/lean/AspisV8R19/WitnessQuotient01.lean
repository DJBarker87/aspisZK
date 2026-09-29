/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessEntryInputs
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem quotient1 : quotient half (7:M) (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) (1:Fin 13) = q1 := by
  unfold quotient
  rw [padding]
  have hs : shift half ((1:Fin 13).val/3) WitnessRootData.p22 = WitnessRootData.s0 := WitnessRootData.shift0
  simp only [hs]
  funext r
  fin_cases r <;> decide
#print axioms quotient1
end
end AspisR19.WitnessEntryData
