import R1Z.PV_RDB2E_FallbackBlockSwap
import R1Z.PV_RDB2E_FallbackRoundShape
import R1Z.PV_RDB2E_FallbackLanes
import R1Z.PV_RDB2E_FallbackStateShift

section
-- Unchanged source component R1Z.PV_CBL_FallbackFourModel
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackFourModel
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar PV_CBL_FallbackRoundsModel
set_option autoImplicit false
/-- Factoring of the exact straight-line rounds4 macro; no replaced compressor. -/
def source (abef cdgh w k : A4) : Result (A4×A4) := do
  let t ← PV_CBL_FallbackBlock.sha_fallback_reference.add w k
  let c ← PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 cdgh abef t
  let u ← PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap t
  let a ← PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 abef c u
  ok (a,c)
def run4 (s : State) (w0 w1 w2 w3 k0 k1 k2 k3 : U32) : State :=
  run s [U32.wrapping_add w0 k0,U32.wrapping_add w1 k1,
         U32.wrapping_add w2 k2,U32.wrapping_add w3 k3]
#print axioms source
#print axioms run4
end R1Z.PV_CBL_FallbackFourModel

end
