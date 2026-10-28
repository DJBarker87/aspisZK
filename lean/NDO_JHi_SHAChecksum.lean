import NDO_JGz_ChecksumDigest
import NDO_JFn_HashBoundary
set_option autoImplicit false
namespace AspisR1.JHi_SHAChecksum
open AspisV8R19.SqueezeOracleBridge
/-- Standalone SHA field, kept out of the verifier import union. -/
theorem source : JFp_SHADigest.digest (flatten JFn_HashBoundary.checksumParts)=
    decodeState JFo_AuthBytes.checksum := JGz_ChecksumDigest.source
#print axioms source
end AspisR1.JHi_SHAChecksum
