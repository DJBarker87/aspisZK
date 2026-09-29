/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessEntryInputs
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem quotient8 : quotient half (7:M) (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) (8:Fin 13) = q8 := by
  unfold quotient
  rw [padding]
  have hs : shift half ((8:Fin 13).val/3) WitnessRootData.p22 = WitnessRootData.s2 := WitnessRootData.shift2
  simp only [hs]
  funext r
  fin_cases r <;> decide
#print axioms quotient8
end
end AspisR19.WitnessEntryData
