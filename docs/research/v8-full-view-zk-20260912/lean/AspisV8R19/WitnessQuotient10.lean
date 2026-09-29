/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessEntryInputs
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem quotient10 : quotient half (7:M) (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) (10:Fin 13) = q10 := by
  unfold quotient
  rw [padding]
  have hs : shift half ((10:Fin 13).val/3) WitnessRootData.p22 = WitnessRootData.s3 := WitnessRootData.shift3
  simp only [hs]
  funext r
  fin_cases r <;> decide
#print axioms quotient10
end
end AspisR19.WitnessEntryData
