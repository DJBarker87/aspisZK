import S6DigestReferenceV1
import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6RetainedDigest
open AspisS6DigestReference

/-- TOTAL exact unrolled reference. Native loop equivalence is separately
checked on the complete native carrier, not assumed by this kernel theorem. -/
theorem encode_total (digest : Array M31 8#usize) :
    ∃ out,encode_digest_canonical digest=ok out := by
  have ht : encode_digest_canonical digest ⦃ _ => True ⦄ := by
    unfold encode_digest_canonical
    simp only [M31.to_le_bytes,bind_tc_ok]
    step*
  obtain ⟨out,ho,_⟩ := spec_imp_exists ht
  exact ⟨out,ho⟩

#print axioms encode_digest_canonical
#print axioms encode_total
end AspisS6RetainedDigest
