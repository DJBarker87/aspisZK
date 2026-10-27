import XRn_Join_ABI
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace XRs_LoopBind
/-- No arithmetic is reduced while commuting the loop continuation. -/
theorem step {S T X Y : Type} (body : S → Result (ControlFlow S T))
 (s : S) (r : Result X) (next : X → S) (k : T → Result Y)
 (h : body s = (r >>= fun x => ok (.cont (next x)))) :
 (loop body s >>= k) = (r >>= fun x => loop body (next x) >>= k) := by
 rw [loop.eq_def,h]
 cases r <;> rfl

theorem done {S T Y : Type} (body : S → Result (ControlFlow S T))
 (s : S) (v : T) (k : T → Result Y) (h : body s = ok (.done v)) :
 (loop body s >>= k) = k v := by rw [loop.eq_def,h]; rfl
#print axioms step
#print axioms done
end XRs_LoopBind
