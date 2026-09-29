/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessEntryInputs
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem quotient9 : quotient half (7:M) (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) (9:Fin 13) = q9 := by
  unfold quotient
  rw [padding]
  have hs : shift half ((9:Fin 13).val/3) WitnessRootData.p22 = WitnessRootData.s3 := WitnessRootData.shift3
  simp only [hs]
  funext r
  fin_cases r <;> decide
#print axioms quotient9
end
end AspisR19.WitnessEntryData
