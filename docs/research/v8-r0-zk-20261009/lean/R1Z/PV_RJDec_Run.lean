import R1Z.PV_W_Threading
set_option autoImplicit false
namespace R1Z.PV_RJDec_Run
open PV_W_Threading
variable {W C E A : Type}
theorem ext (l r : Run W C E A) (outcome : l.outcome=r.outcome)
    (world : l.world=r.world) (calls : l.calls=r.calls) : l=r := by
  cases l
  cases r
  cases outcome
  cases world
  cases calls
  rfl
#print axioms ext
end R1Z.PV_RJDec_Run
