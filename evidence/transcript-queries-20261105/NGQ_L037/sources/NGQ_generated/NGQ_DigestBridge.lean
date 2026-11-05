import NGQ_DigestRef
set_option autoImplicit false
namespace AspisR1.NGQ_DigestBridge
open Aeneas Aeneas.Std Result
/-- The NGC-emitted reference returns the SAME complete reply at the SAME
ordered descriptor input. Digest value=H remains runtime/P1 trust. -/
theorem observed (parts : SdkC_Source.Parts) (reply : SdkC_Source.Digest) :
 NGQ_DigestRef.digest_ref parts reply=ok reply := rfl
#print axioms observed
end AspisR1.NGQ_DigestBridge
