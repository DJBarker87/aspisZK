import R1Z.PV_CBL_FallbackCanonicalStep
import R1Z.PV_CBL_FallbackRoundShape
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackRoundCanonical
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar
set_option autoImplicit false
theorem source (s : State) (w0 w1 u v : U32) :
    PV_CBL_FallbackRound.sha_fallback_reference.sha256_digest_round_x2
      (pack s.c s.d s.g s.h) (pack s.a s.b s.e s.f) (pack u v w1 w0) =
      let r := PV_CBL_FallbackCanonicalStep.step (PV_CBL_FallbackCanonicalStep.step s w0) w1
      ok (pack r.a r.b r.e r.f) := by
  simpa only [PV_CBL_FallbackCanonicalStep.source] using
    PV_CBL_FallbackRoundShape.shape s w0 w1 u v
#print axioms source
end R1Z.PV_CBL_FallbackRoundCanonical
