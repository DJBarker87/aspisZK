import R1Z.SimCostWriter

/-! Rejection-sampling caveat for implementing uniform field primitives from
binary random words. This module proves a bounded truncation and geometric
work model; it does not silently replace the headline's uniform tape law. -/
set_option autoImplicit false
namespace R1Z.SimCostSampling
open R1Z.SimCostWriter

def truncate {A : Type} : List (Option A) → Costed (Option A)
  | [] => (none, 0)
  | some a :: _ => (some a, 1)
  | none :: t => let r := truncate t; (r.1, r.2+1)

def reference {A : Type} : List (Option A) → Option A
  | [] => none
  | some a :: _ => some a
  | none :: t => reference t

theorem truncate_erase {A : Type} (xs : List (Option A)) :
    (truncate xs).1 = reference xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp only [truncate, reference, ih]

theorem truncate_bound {A : Type} (xs : List (Option A)) :
    (truncate xs).2 ≤ xs.length := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih => cases x <;> simp only [truncate, List.length_cons] <;> omega

/-- For every finite budget there is a stream with no accepted sample.
An exact sampler implemented by retry-until-success has no worst-case cap. -/
theorem all_reject {A : Type} (B : Nat) :
    truncate (List.replicate B (none : Option A)) = (none,B) := by
  induction B with
  | zero => rfl
  | succ B ih => simp only [List.replicate_succ, truncate, ih]

/-- Expected charged draws for at most B independent trials, each rejecting
with probability rho. Independence/geometric law is an external sampler
refinement obligation, not inferred from returned-value equality. -/
def expectedDraws (rho : ℚ) : Nat → ℚ
  | 0 => 0
  | n+1 => 1+rho*expectedDraws rho n

theorem expected_nonneg (rho : ℚ) (h : 0 ≤ rho) (B : Nat) :
    0 ≤ expectedDraws rho B := by
  induction B with
  | zero => exact le_refl 0
  | succ B ih => unfold expectedDraws; positivity

theorem expected_le_two (rho : ℚ) (h0 : 0 ≤ rho) (h1 : rho ≤ 1/2) (B : Nat) :
    expectedDraws rho B ≤ 2 := by
  induction B with
  | zero => norm_num [expectedDraws]
  | succ B ih =>
    have hn := expected_nonneg rho h0 B
    unfold expectedDraws
    nlinarith

/-- A 31-bit word has exactly one rejected value for M31 (all ones).
This rational rate describes uniform independent words; the source coupling
and the byte-sampler implementation still need their own certificate. -/
def m31Reject : ℚ := 1/(2:ℚ)^31

theorem m31_rate : 0 ≤ m31Reject ∧ m31Reject ≤ 1/2 := by norm_num [m31Reject]

theorem m31_expected (B : Nat) : expectedDraws m31Reject B ≤ 2 :=
  expected_le_two m31Reject m31_rate.1 m31_rate.2 B

/-- Truncation failure rate under independent binary-word trials. -/
theorem m31_tail (B : Nat) : m31Reject^B = 1/(2:ℚ)^(31*B) := by
  simp only [m31Reject, one_div_pow, ← pow_mul]

#print axioms truncate_erase
#print axioms truncate_bound
#print axioms all_reject
#print axioms expected_nonneg
#print axioms expected_le_two
#print axioms m31_rate
#print axioms m31_expected
#print axioms m31_tail
end R1Z.SimCostSampling
