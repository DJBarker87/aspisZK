/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessEntryInputs
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem quotient0 : quotient half (7:M) (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) (0:Fin 13) = q0 := by
  unfold quotient
  rw [padding, WitnessRootData.shift0]
  funext r
  fin_cases r <;> decide
#print axioms quotient0
end
end AspisR19.WitnessEntryData
