import SCE_CompleteSubmission
import F3T_Charged
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_Numeric
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- Charging both account wrappers as prover preprocessing is sound accounting,
but this envelope does not meet the unchanged zero-query target. This compares
upper bounds; it is NOT a lower bound on any attack's actual success. -/
theorem complete_start_envelope_exceeds :
    (1 : Rat)/(2:Rat)^100 < ((1921+34 : Nat) : Rat)*PerAttemptEnvelope.B := by
  norm_num [PerAttemptEnvelope.B]

/-- Merely moving all account execution into P is not a zero-cost repair. -/
theorem complete_start_not_headline :
    ¬ (((1921+34 : Nat) : Rat)*PerAttemptEnvelope.B ≤ (1 : Rat)/(2:Rat)^100) :=
  not_le_of_gt complete_start_envelope_exceeds

#print axioms complete_start_envelope_exceeds
#print axioms complete_start_not_headline
end AspisR1.SCE_Numeric
end
