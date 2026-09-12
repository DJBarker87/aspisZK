import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat

/-! IMPORTED FIRST ATTEMPT; COMPILED IN THIS WORKSTREAM. Equality of CONDITIONAL public kernels
composes adaptively. Merely proving fixed-schedule ranks does not provide
these kernels. Abort must be a response symbol, not silently conditioned away.
-/
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Privacy
variable {O : Type*} [Fintype O]

structure PublicKernel (O : Type*) [Fintype O] where
  probability : List O → O → ℚ
  nonnegative : ∀ h o, 0 ≤ probability h o
  total : ∀ h, ∑ o, probability h o = 1

/-- Probability of this exact bounded response sequence, starting with a
fixed common public history. A finished source must use inert padding. -/
def traceWeight (k : PublicKernel O) : List O → List O → ℚ
  | _, [] => 1
  | history, x :: rest => k.probability history x * traceWeight k (history ++ [x]) rest

theorem traceWeight_nonnegative (k : PublicKernel O) (past future : List O) :
    0 ≤ traceWeight k past future := by
  induction future generalizing past with
  | nil => simp [traceWeight]
  | cons x rest ih =>
      exact mul_nonneg (k.nonnegative past x) (ih (past ++ [x]))

/-- Conditional identities must hold at the SAME public history, with the
remaining hidden-state distribution induced by that history. -/
theorem adaptive_weights_equal (real sim : PublicKernel O)
    (stepEquality : ∀ history answer, real.probability history answer = sim.probability history answer)
    (past future : List O) : traceWeight real past future = traceWeight sim past future := by
  induction future generalizing past with
  | nil => rfl
  | cons x rest ih =>
      simp only [traceWeight, stepEquality, ih]

#print axioms traceWeight_nonnegative
#print axioms adaptive_weights_equal
end AspisV8Privacy
