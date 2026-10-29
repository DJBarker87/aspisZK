import PV_L1G_WorldRetry
set_option autoImplicit false
namespace PV_L1G_WorldRetry
open R1Z.PV_W_Threading
variable {W S P : Type}
/-- A retry preserves the exact pre-world-labelled prefix, even when the
remaining run subsequently fails or diverges. -/
theorem retry_calls (a : Attempt W S P) (n k : Nat) (s after : S) (w : W)
 (h : (a k s w).outcome = .ok (.retry,after)) :
 (run a (n+1) k s w).calls =
 (a k s w).calls ++ (run a n (k+1) after (a k s w).world).calls := by
 rw [run,bind_ok _ _ w (.retry,after) h]
#print axioms retry_calls
theorem retry_world (a : Attempt W S P) (n k : Nat) (s after : S) (w : W)
 (h : (a k s w).outcome = .ok (.retry,after)) :
 (run a (n+1) k s w).world = (run a n (k+1) after (a k s w).world).world := by
 rw [run,bind_ok _ _ w (.retry,after) h]
#print axioms retry_world
end PV_L1G_WorldRetry
