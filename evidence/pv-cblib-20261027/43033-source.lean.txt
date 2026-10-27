import R1Z.PV_CBL_FallbackRoundShape
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackRoundUnused
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar
set_option autoImplicit false
/-- The x2 helper consumes only the lower two message words. -/
theorem unused (s : State) (w0 w1 u v u' v' : U32) :
    PV_CBL_FallbackRound.sha_fallback_reference.sha256_digest_round_x2
      (pack s.c s.d s.g s.h) (pack s.a s.b s.e s.f) (pack u v w1 w0) =
    PV_CBL_FallbackRound.sha_fallback_reference.sha256_digest_round_x2
      (pack s.c s.d s.g s.h) (pack s.a s.b s.e s.f) (pack u' v' w1 w0) := by
  rw [PV_CBL_FallbackRoundShape.shape,PV_CBL_FallbackRoundShape.shape]
#print axioms unused
end R1Z.PV_CBL_FallbackRoundUnused
