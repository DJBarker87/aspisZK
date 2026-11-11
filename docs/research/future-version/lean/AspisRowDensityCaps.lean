import AspisRowDensityQM31
import R1PerAttemptEnvelope
import R1LiteralClassifier

/-! Aspis per-step accounting, row densities: the new caps against R1's
row-32 budget and R1's common envelope.

Kind of result: scalar inequalities between exact rationals (no protocol, no
probability). `LiteralClassifier.budget 32` is R1's row-32 budget;
`PerAttemptEnvelope.B = 15/2^109` is R1's common envelope. No figure for Aspis
is derived here. -/

set_option autoImplicit false

namespace AspisRowDensity.Caps

open AspisR1 AspisRowDensity.QM31

theorem budget32_eq_capPair : LiteralClassifier.budget 32 = capPair := by
  rw [capPair_eq_rhoCap]
  rfl

theorem capLambda_le_budget32 : capLambda ≤ LiteralClassifier.budget 32 := by
  rw [budget32_eq_capPair]
  exact capLambda_le_capRound.trans capRound_le_capPair

theorem capRound_le_budget32 : capRound ≤ LiteralClassifier.budget 32 := by
  rw [budget32_eq_capPair]
  exact capRound_le_capPair

theorem capPair_le_B : capPair ≤ PerAttemptEnvelope.B := by
  rw [capPair_eq_rhoCap]
  exact PerAttemptEnvelope.rho_cap_le

theorem capRound_le_B : capRound ≤ PerAttemptEnvelope.B :=
  capRound_le_capPair.trans capPair_le_B

theorem capLambda_le_B : capLambda ≤ PerAttemptEnvelope.B :=
  capLambda_le_capRound.trans capRound_le_B

#print axioms budget32_eq_capPair
#print axioms capLambda_le_budget32
#print axioms capRound_le_budget32
#print axioms capPair_le_B
#print axioms capRound_le_B
#print axioms capLambda_le_B

end AspisRowDensity.Caps
