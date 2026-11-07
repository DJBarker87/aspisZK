import NMT_R2_345Frames
set_option autoImplicit false
namespace NMT_R2_345
open RSL NMT_345Observation NMT_R2_Observation

def stepReturn (length : Nat) (bytes : Bytes) : Obs (Except ProgramError Bytes) :=
 silent (if bytes.length != length then .error .invalidAccountData else .ok bytes)

theorem stepReturn_valid (length : Nat) (bytes : Bytes) (env : Env) :
 RS.seq (RS.check (bytes.length != length) .invalidAccountData) (RS.pure bytes)
  env (stepReturn length bytes) := by
 unfold stepReturn
 cases h : bytes.length != length <;>
  simp only [h,RS.check,Bool.false_eq_true,if_false,if_true,RS.seq_pure,RS.seq_throw] <;> rfl
#print axioms stepReturn_valid
end NMT_R2_345
