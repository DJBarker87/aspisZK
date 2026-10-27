import Uni_CanonicalPerAttempt
import RPz7_AuS1_Bound
set_option autoImplicit false
noncomputable section
namespace AspisR1.EndP_Numeric

/-- Whole source 22585 calls plus ALL1040 replay calls, charged once. -/
def authLoss (Q : Nat) : Rat := 6*((Q+23625 : Nat) : Rat)^2/(2:Rat)^256

def collision (Q : Nat) : Rat :=
  6*((Q+1161 : Nat) : Rat)^2/(2:Rat)^256 + authLoss Q

def total (Q : Nat) : Rat :=
  ((Q+34 : Nat) : Rat)*PerAttemptEnvelope.B + collision Q +
    1/(2:Rat)^126 + 1/(2:Rat)^454

theorem replay_loss (Q : Nat) : AuS1_Bound.loss (Q+22585) = authLoss Q := by
  rw [AuS1_Bound.loss_binary]
  simp only [authLoss,show Q+22585+1040 = Q+23625 by omega]

theorem total_eq (Q : Nat) :
    total Q = StartChargeNumeric.totalBound Q + authLoss Q := by
  have power : (256^32 : Rat) = 2^256 := by
    calc
      (256^32 : Rat) = ((2^8)^32 : Rat) := rfl
      _ = (2^(8*32) : Rat) := (pow_mul 2 8 32).symm
      _ = (2^256 : Rat) := rfl
  unfold total collision StartChargeNumeric.totalBound OracleDecisionPrereqNumeric.envelope
    BinCombinedMerkleCollision.kappa
  rw [power]
  ring

theorem auth_nonnegative (Q : Nat) : 0 ≤ authLoss Q := by
  unfold authLoss
  positivity

/-- Exact spare margin. This includes both collision terms and both aborts. -/
theorem zero_margin :
    1/(2:Rat)^100 - total 0 = 1/(2:Rat)^108 -
      6*((1161:Rat)^2+23625^2)/(2:Rat)^256 - 1/(2:Rat)^126 - 1/(2:Rat)^454 := by
  norm_num [total,collision,authLoss,PerAttemptEnvelope.B,BinPerQueryNumeric.power454]

/-- Contract (A), including the new source-authentication collision loss. -/
theorem zero_queries : total 0 ≤ 1/(2:Rat)^100 := by
  norm_num [total,collision,authLoss,PerAttemptEnvelope.B,BinPerQueryNumeric.power454]

/-- The challenge mass itself is below the required per-attempt error. -/
theorem challenge_mass : PerAttemptEnvelope.B ≤ 1/(2:Rat)^100 := by
  norm_num [PerAttemptEnvelope.B]

#print axioms replay_loss
#print axioms total_eq
#print axioms auth_nonnegative
#print axioms zero_margin
#print axioms zero_queries
#print axioms challenge_mass
end AspisR1.EndP_Numeric
end
