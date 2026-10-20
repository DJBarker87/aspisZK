import R1PerAttemptEnvelope
import QvStage2Count

/-! Exact rational arithmetic for C3. Q is the adversary allowance; the
collision budget includes the 1,161 verifier-core first reads. External
runtime/Pool reads, if designated, must be included in Q as well. -/
set_option autoImplicit false
namespace AspisR1.R1FinalSoundnessNumeric

/-- Largest adversary allowance for the stated conservative binary ledger. -/
def maxAdversaryQueries : Nat := 22482956455467539568187

/-- Largest total first-read allowance, including the verifier core. -/
def maxTotalQueries : Nat := 22482956455467539569348

def totalBound (Q : Nat) : ℚ :=
  6 * ((Q + 1161 : Nat) : ℚ)^2 / 256^32 +
    33 * PerAttemptEnvelope.B + 1 / 2^126 + 1 / 2^454

theorem verifier_reads : QvStage1.stage1Budget 10 + QvStage2.stage2Budget 12 = 1161 :=
  QvStage2.verifierBudget_value

theorem allowance_identity : maxAdversaryQueries + 1161 = maxTotalQueries := by
  norm_num [maxAdversaryQueries, maxTotalQueries]

theorem totalBound_mono {Q R : Nat} (h : Q ≤ R) : totalBound Q ≤ totalBound R := by
  unfold totalBound
  have hc : ((Q + 1161 : Nat) : ℚ) ≤ ((R + 1161 : Nat) : ℚ) := by exact_mod_cast Nat.add_le_add_right h 1161
  have hn : (0 : ℚ) ≤ ((Q + 1161 : Nat) : ℚ) := by positivity
  gcongr

theorem endpoint_lt : totalBound maxAdversaryQueries < 1 / (2 : ℚ)^100 := by
  have hp : (2 : ℚ)^454 = ((2 : ℚ)^227)^2 := by rw [← pow_mul]
  rw [totalBound, hp]
  norm_num [maxAdversaryQueries, PerAttemptEnvelope.B]

theorem successor_not_lt : 1 / (2 : ℚ)^100 ≤ totalBound (maxAdversaryQueries + 1) := by
  have hp : (2 : ℚ)^454 = ((2 : ℚ)^227)^2 := by rw [← pow_mul]
  rw [totalBound, hp]
  norm_num [maxAdversaryQueries, PerAttemptEnvelope.B]

/-- Bank and query-scan aborts together fit the Decision 3 allowance. -/
theorem extractor_abort_allowance :
    1 / (2 : ℚ)^126 + 1 / (2 : ℚ)^454 ≤ 1 / (2 : ℚ)^120 := by
  have hp : (2 : ℚ)^454 = ((2 : ℚ)^227)^2 := by rw [← pow_mul]
  rw [hp]
  norm_num

/-- Exact maximality, not a rounded bit-security estimate. -/
theorem numeric_iff (Q : Nat) :
    totalBound Q < 1 / (2 : ℚ)^100 ↔ Q ≤ maxAdversaryQueries := by
  constructor
  · intro h
    by_contra hn
    have hm : maxAdversaryQueries + 1 ≤ Q := by omega
    exact (not_lt_of_ge (successor_not_lt.trans (totalBound_mono hm))) h
  · intro h
    exact (totalBound_mono h).trans_lt endpoint_lt

#print axioms verifier_reads
#print axioms allowance_identity
#print axioms totalBound_mono
#print axioms endpoint_lt
#print axioms successor_not_lt
#print axioms extractor_abort_allowance
#print axioms numeric_iff
end AspisR1.R1FinalSoundnessNumeric
