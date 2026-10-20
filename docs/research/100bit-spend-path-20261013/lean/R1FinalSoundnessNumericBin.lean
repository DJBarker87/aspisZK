import R1FinalSoundnessNumeric

/-! Binary extraction changes no charged probability term. Reuse the exact
rational endpoint proof; numeric-endpoint.json independently recomputes it. -/
set_option autoImplicit false
namespace AspisR1.R1FinalSoundnessNumericBin
abbrev totalBound := R1FinalSoundnessNumeric.totalBound
abbrev maxAdversaryQueries := R1FinalSoundnessNumeric.maxAdversaryQueries

theorem numeric_iff (Q : Nat) :
    totalBound Q < 1 / (2 : ℚ)^100 ↔ Q ≤ maxAdversaryQueries :=
  R1FinalSoundnessNumeric.numeric_iff Q

theorem successor_not_lt : 1 / (2 : ℚ)^100 ≤
    totalBound (maxAdversaryQueries + 1) :=
  R1FinalSoundnessNumeric.successor_not_lt

#print axioms numeric_iff
#print axioms successor_not_lt
end AspisR1.R1FinalSoundnessNumericBin
