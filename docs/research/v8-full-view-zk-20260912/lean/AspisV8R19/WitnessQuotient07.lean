/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessEntryInputs
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem quotient7 : quotient half (7:M) (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) (7:Fin 13) = q7 := by
  unfold quotient
  rw [padding]
  have hs : shift half ((7:Fin 13).val/3) WitnessRootData.p22 = WitnessRootData.s2 := WitnessRootData.shift2
  simp only [hs]
  funext r
  fin_cases r <;> decide
#print axioms quotient7
end
end AspisR19.WitnessEntryData
