import NDO_JGz_ChecksumDigest
set_option autoImplicit false
namespace AspisR1.JHn_ChecksumEquation
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
/-- The exact checksum field of JHh_SHARealization, independently of the
large tree environment. Reuses the SAME retained checkpoint digest proof. -/
theorem source : JFp_SHADigest.digest (flatten JFn_HashBoundary.checksumParts)=decodeState JFo_AuthBytes.checksum :=
  JGz_ChecksumDigest.source
#print axioms source
end AspisR1.JHn_ChecksumEquation
