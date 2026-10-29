import R1Z.PV_RDB2E_FallbackScalar

section
-- Unchanged source component R1Z.PV_CBL_FallbackRoundShape
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackRoundShape
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar
set_option autoImplicit false
theorem shape (s : State) (w0 w1 u v : U32) :
    PV_CBL_FallbackRound.sha_fallback_reference.sha256_digest_round_x2
      (pack s.c s.d s.g s.h) (pack s.a s.b s.e s.f) (pack u v w1 w0) =
      let r := step (step s w0) w1
      ok (pack r.a r.b r.e r.f) := by
  simp only [PV_CBL_FallbackRound.sha_fallback_reference.sha256_digest_round_x2,
    index0,index1,index2,index3,lift,bind_tc_ok]
  rfl
#print axioms shape
end R1Z.PV_CBL_FallbackRoundShape

end
