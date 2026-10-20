import OracleDecisionPrereqPaths
import BinPerQueryNumeric

/-! Numeric effects only: no soundness endpoint or premise is ported here.
The quadratic is handled symbolically, then by two endpoint checks. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionPrereqNumeric

def envelope (Q c B : Nat) : ℚ :=
  ((Q+c : Nat) : ℚ) * PerAttemptEnvelope.B +
    BinCombinedMerkleCollision.kappa (Q+B) + 1/(2:ℚ)^126 + 1/(2:ℚ)^454

def gap (x : ℚ) (c B : Nat) : ℚ :=
  6*(x+B)^2/(2:ℚ)^256 + (x+c)*15/(2:ℚ)^109 +
    1/(2:ℚ)^126 + 1/(2:ℚ)^454 - (x+1)/(2:ℚ)^100

def retainedMax : Nat := 14777960484892959601791002642008314224629686252
def safeMax : Nat := 14777960484892959601791002642008314224629686214

theorem budget_delta (x : ℚ) (c : Nat) :
    gap x c 1375 = gap x c 1161 + 6*214*(2*x+2536)/(2:ℚ)^256 := by
  unfold gap
  push_cast
  ring

theorem start_delta (x : ℚ) :
    gap x 1294 1375 = gap x 34 1375 + 1260*15/(2:ℚ)^109 := by
  unfold gap
  push_cast
  ring

theorem envelope_gap (Q c B : Nat) :
    envelope Q c B - (Q+1 : ℚ)*(1/(2:ℚ)^100) = gap Q c B := by
  have hb : PerAttemptEnvelope.B = 15/(2:ℚ)^109 := by norm_num [PerAttemptEnvelope.B]
  unfold envelope gap BinCombinedMerkleCollision.kappa
  rw [hb]
  push_cast
  norm_num
  <;> ring

/-- A translated convex-quadratic chord, with no concrete oracle reduction. -/
theorem gap_interval (lo hi Q c B : Nat) (hlt : lo < hi)
    (hlo : lo ≤ Q) (hhi : Q ≤ hi)
    (hleft : gap lo c B ≤ 0) (hright : gap hi c B ≤ 0) : gap Q c B ≤ 0 := by
  let a : ℚ := 6/(2:ℚ)^256
  let b : ℚ := 12*((lo:ℚ)+B)/(2:ℚ)^256 - 497/(2:ℚ)^109
  let z : ℚ := gap lo c B
  have hid (x : ℚ) : gap ((lo:ℚ)+x) c B = a*x^2+b*x+z := by
    dsimp [gap, a, b, z]
    norm_num
    <;> ring
  have he : a*((hi:ℚ)-lo)^2+b*((hi:ℚ)-lo)+z ≤ 0 := by
    rw [← hid]
    simpa only [add_sub_cancel_left] using hright
  have hn : 0 ≤ (Q:ℚ)-lo := sub_nonneg.mpr (by exact_mod_cast hlo)
  have hm : 0 < (hi:ℚ)-lo := sub_pos.mpr (by exact_mod_cast hlt)
  have hqm : (Q:ℚ)-lo ≤ (hi:ℚ)-lo := sub_le_sub_right (by exact_mod_cast hhi) _
  have hg := BinPerQueryNumeric.quadratic_interval a b z ((hi:ℚ)-lo) ((Q:ℚ)-lo)
    (by dsimp [a]; positivity) hm hn hqm hleft he
  rw [← hid] at hg
  simpa only [add_sub_cancel_left] using hg

theorem retained_edges : gap 0 34 1375 ≤ 0 ∧ gap retainedMax 34 1375 ≤ 0 ∧
    0 < gap (retainedMax+1) 34 1375 := by
  norm_num [gap, retainedMax, BinPerQueryNumeric.power454]

theorem safe_edges : 0 < gap 38 1294 1375 ∧ gap 39 1294 1375 ≤ 0 ∧
    gap safeMax 1294 1375 ≤ 0 ∧ 0 < gap (safeMax+1) 1294 1375 := by
  norm_num [gap, safeMax, BinPerQueryNumeric.power454]

theorem retained_range (Q : Nat) (hq : Q ≤ retainedMax) :
    envelope Q 34 1375 ≤ (Q+1 : ℚ)*(1/(2:ℚ)^100) := by
  have hg := gap_interval 0 retainedMax Q 34 1375 (by norm_num [retainedMax])
    (Nat.zero_le Q) hq retained_edges.1 retained_edges.2.1
  rw [← envelope_gap] at hg
  linarith

theorem safe_range (Q : Nat) (hlo : 39 ≤ Q) (hhi : Q ≤ safeMax) :
    envelope Q 1294 1375 ≤ (Q+1 : ℚ)*(1/(2:ℚ)^100) := by
  have hg := gap_interval 39 safeMax Q 1294 1375 (by norm_num [safeMax])
    hlo hhi safe_edges.2.1 safe_edges.2.2.1
  rw [← envelope_gap] at hg
  linarith

/-- The increased start constant cannot retain the old range beginning at 0. -/
theorem safe_zero_fails : (1:ℚ)/(2:ℚ)^100 < envelope 0 1294 1375 := by
  have hg : 0 < gap 0 1294 1375 := by
    norm_num [gap, BinPerQueryNumeric.power454]
  rw [← envelope_gap] at hg
  norm_num at hg ⊢
  linarith

theorem max_shifts : retainedMax + 428 = BinPerQueryNumeric.Qmax ∧
    safeMax + 466 = BinPerQueryNumeric.Qmax := by
  norm_num [retainedMax, safeMax, BinPerQueryNumeric.Qmax]

#print axioms budget_delta
#print axioms start_delta
#print axioms envelope_gap
#print axioms gap_interval
#print axioms retained_edges
#print axioms safe_edges
#print axioms retained_range
#print axioms safe_range
#print axioms safe_zero_fails
#print axioms max_shifts
end AspisR1.OracleDecisionPrereqNumeric
end
