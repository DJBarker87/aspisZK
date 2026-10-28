import NDO_JGz_PublicDigest
import NDO_JFn_HashBoundary
set_option autoImplicit false
namespace AspisR1.JHi_SHAPublic
open AspisV8R19.SqueezeOracleBridge
/-- Standalone SHA field, kept out of the verifier import union. -/
theorem source : JFp_SHADigest.digest (flatten JFn_HashBoundary.publicParts)=
    decodeState JFo_AuthBytes.publicHash := JGz_PublicDigest.source
#print axioms source
end AspisR1.JHi_SHAPublic
