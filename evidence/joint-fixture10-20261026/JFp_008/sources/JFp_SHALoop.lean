import JFp_SHA256
set_option autoImplicit false
namespace AspisR1.JFp_SHA256
/-- Definitional loop equation, isolated from concrete SHA certificates. -/
theorem loop_step (k : Nat) (ks w : List Nat) (s : Reg) :
    loop (k::ks) w s=loop ks (advance w) (round s k (w.getD 0 0)) := by rfl
#print axioms loop_step
end AspisR1.JFp_SHA256
