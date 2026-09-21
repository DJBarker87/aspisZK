import AspisV8R17.BoundedRejection
import Mathlib.Tactic.NormNum

/-! Single-sentinel ideal limb law. This does not identify shared-oracle
outputs with independent uniform tapes, or refine Rust byte decoding. -/
set_option autoImplicit false
namespace AspisV8R17.SingleSentinelSampler
open AspisV8Privacy AspisV8R17.BoundedRejection

def accept (q : ℕ) (x : Fin (q+1)) : Bool := decide (x ≠ Fin.last q)

def rejectedEquiv (q : ℕ) : {x : Fin (q+1) // accept q x = false} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨Fin.last q, by simp [accept]⟩
  left_inv x := by
    apply Subtype.ext
    have h : x.val = Fin.last q := by simpa [accept] using x.property
    exact h.symm
  right_inv x := by cases x; rfl

theorem rejected_card (q : ℕ) :
    Fintype.card {x : Fin (q+1) // accept q x = false} = 1 := by
  exact (Fintype.card_congr (rejectedEquiv q)).trans (by simp)

theorem failure_law (q n : ℕ) :
    uniformProbability (@sample (Fin (q+1)) (accept q) n) none =
      1 / ((q+1 : ℕ) : ℚ)^n := by
  rw [failure_probability, rejected_card]
  simp

theorem m31_eight_attempt_failure :
    uniformProbability (@sample (Fin (2147483647+1)) (accept 2147483647) 8) none =
      1 / (2 : ℚ)^248 := by
  rw [failure_law]
  have base : ((2147483647+1 : ℕ) : ℚ) = (2 : ℚ)^31 := by norm_num
  rw [base, ← pow_mul]

#print axioms rejected_card
#print axioms failure_law
#print axioms m31_eight_attempt_failure
end AspisV8R17.SingleSentinelSampler
