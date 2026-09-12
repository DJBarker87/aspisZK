/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import Mathlib
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.RejectionKernel
noncomputable section

/-- Raw one-attempt abort mass r; success at any particular output has mass a.
The successful-value probability remains UNCONDITIONAL on not aborting. -/
def retryAtom (r a : ℚ) : Nat → ℚ
  | 0 => 0
  | n+1 => a + r * retryAtom r a n

def retryAbort (r : ℚ) (n : Nat) : ℚ := r^n

theorem retryAtom_nonneg (r a : ℚ) (hr : 0 ≤ r) (ha : 0 ≤ a) :
    ∀ n, 0 ≤ retryAtom r a n := by
  intro n
  induction n with
  | zero => simp [retryAtom]
  | succ n ih => exact add_nonneg ha (mul_nonneg hr ih)

/-- If every valid value has a ≤(1-r)/N, bounded retries give ≤1/N.
A real decoder's exact preimage count must produce this inequality. -/
theorem retryAtom_bound (r a b : ℚ) (hr : 0 ≤ r) (hb : 0 ≤ b)
    (atom : a ≤ (1-r)*b) : ∀ n, retryAtom r a n ≤ b := by
  intro n
  induction n with
  | zero => simpa [retryAtom] using hb
  | succ n ih =>
    calc
      retryAtom r a (n+1) = a+r*retryAtom r a n := rfl
      _ ≤ (1-r)*b+r*b := add_le_add atom (mul_le_mul_of_nonneg_left ih hr)
      _ = b := by ring

/-- Equal one-step atoms stay equal after the same bounded retry controller. -/
theorem retryAtom_equal (r a b : ℚ) (same : a=b) (n : Nat) :
    retryAtom r a n = retryAtom r b n := by rw [same]

/-- Successful-total mass plus abort is exactly one: no omitted failure mass. -/
theorem retry_total (r : ℚ) : ∀ n,
    retryAtom r (1-r) n + retryAbort r n = 1 := by
  intro n
  induction n with
  | zero => simp [retryAtom, retryAbort]
  | succ n ih =>
    simp only [retryAtom, retryAbort, pow_succ] at *
    nlinarith

#print axioms retryAtom_bound
#print axioms retry_total
end
end AspisV8Completion.RejectionKernel
