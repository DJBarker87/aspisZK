import NDO_JFn_HashBoundary
import NDO_JFp_SHADigest
set_option autoImplicit false
namespace AspisR1.JHi_SHARealization
open AspisV8R19.SqueezeOracleBridge
/-- Concrete mathematical digest equations only. No source or syscall law,
acceptance observation, or validator result is hidden in this boundary. -/
structure SHARealization : Prop where
  proof : JFp_SHADigest.digest (flatten JFn_HashBoundary.proofParts)=decodeState JFo_AuthBytes.proofHash
  publicInput : JFp_SHADigest.digest (flatten JFn_HashBoundary.publicParts)=decodeState JFo_AuthBytes.publicHash
  checksum : JFp_SHADigest.digest (flatten JFn_HashBoundary.checksumParts)=decodeState JFo_AuthBytes.checksum

theorem realizes (h : SHARealization) : JFn_HashBoundary.Realizes JFp_SHADigest.digest :=
  ⟨h.proof,h.publicInput,h.checksum⟩
#print axioms realizes
end AspisR1.JHi_SHARealization
