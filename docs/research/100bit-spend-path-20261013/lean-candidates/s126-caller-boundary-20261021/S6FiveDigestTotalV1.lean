import S6FiveCodecNativeV1
import S6RetainedDigestTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6FiveUnrolledCodec.DigestTotal
open AspisS6FiveUnrolledCodec

theorem equals_checked_reference (digest : Array U32 8#usize) :
    aspis_statement.atomic_statement.encode_digest_canonical digest =
      AspisS6DigestReference.encode_digest_canonical digest := by
  rfl

/-- TOTAL actual extracted digest body in the complete codec reference.
No successful-child or canonicality premise. -/
theorem encode_total (digest : Array U32 8#usize) :
    ∃ out, aspis_statement.atomic_statement.encode_digest_canonical digest=ok out := by
  rw [equals_checked_reference]
  exact AspisS6RetainedDigest.encode_total digest

#print axioms equals_checked_reference
#print axioms encode_total
end AspisS6FiveUnrolledCodec.DigestTotal
