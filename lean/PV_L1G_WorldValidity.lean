import PV_L1G_WorldRetry
set_option autoImplicit false
namespace PV_L1G_WorldRetry
open R1Z.PV_W_Threading
variable {W S P : Type}
/-- The world transition relation remains an independent native input. All
calls, including those on failed leaves, satisfy it when the leaves do. -/
theorem valid_run (a : Attempt W S P) (step : W → Event → W → Prop)
 (leaves : ∀ k s, Valid step (a k s)) (n k : Nat) (s : S) :
 Valid step (run a n k s) := by
 induction n generalizing k s with
 | zero => exact valid_lift step _
 | succ n ih =>
   apply valid_bind step (a k s) _ (leaves k s)
   rintro ⟨out,after⟩
   cases out with
   | done p => exact valid_lift step _
   | stop e => exact valid_lift step _
   | retry => exact ih (k+1) after
#print axioms valid_run
end PV_L1G_WorldRetry
