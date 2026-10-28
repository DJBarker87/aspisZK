import NDO_JHe_SHARealization
import NDO_JFn_HashBoundary
set_option autoImplicit false
namespace AspisR1
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
/-- The inherited 453 tree equations, plus three concrete retained-byte
requests. No success, output identity, or execution is a field. The immutable
JHe interface is extended here rather than edited. -/
class JHh_SHARealization : Prop extends JHe_SHARealization where
  proof : JFp_SHADigest.digest (flatten JFn_HashBoundary.proofParts)=decodeState JFo_AuthBytes.proofHash
  publicInput : JFp_SHADigest.digest (flatten JFn_HashBoundary.publicParts)=decodeState JFo_AuthBytes.publicHash
  checksum : JFp_SHADigest.digest (flatten JFn_HashBoundary.checksumParts)=decodeState JFo_AuthBytes.checksum
end AspisR1
