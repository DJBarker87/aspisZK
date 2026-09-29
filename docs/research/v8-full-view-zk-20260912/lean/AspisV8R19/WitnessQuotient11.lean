/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessEntryInputs
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem quotient11 : quotient half (7:M) (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) (11:Fin 13) = q11 := by
  unfold quotient
  rw [padding]
  have hs : shift half ((11:Fin 13).val/3) WitnessRootData.p22 = WitnessRootData.s3 := WitnessRootData.shift3
  simp only [hs]
  funext r
  fin_cases r <;> decide
#print axioms quotient11
end
end AspisR19.WitnessEntryData
