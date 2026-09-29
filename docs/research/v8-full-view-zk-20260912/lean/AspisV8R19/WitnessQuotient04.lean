/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessEntryInputs
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem quotient4 : quotient half (7:M) (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) (4:Fin 13) = q4 := by
  unfold quotient
  rw [padding]
  have hs : shift half ((4:Fin 13).val/3) WitnessRootData.p22 = WitnessRootData.s1 := WitnessRootData.shift1
  simp only [hs]
  funext r
  fin_cases r <;> decide
#print axioms quotient4
end
end AspisR19.WitnessEntryData
