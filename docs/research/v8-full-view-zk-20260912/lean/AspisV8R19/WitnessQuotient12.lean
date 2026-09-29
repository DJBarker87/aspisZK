/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessEntryInputs
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem quotient12 : quotient half (7:M) (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) (12:Fin 13) = q12 := by
  unfold quotient
  rw [padding]
  have hs : shift half ((12:Fin 13).val/3) WitnessRootData.p22 = WitnessRootData.s4 := WitnessRootData.shift4
  simp only [hs]
  funext r
  fin_cases r <;> decide
#print axioms quotient12
end
end AspisR19.WitnessEntryData
