import JHn_ProofEquation
import JHn_PublicEquation
import JHn_ChecksumEquation
import JHh_SHARealization
set_option autoImplicit false
namespace AspisR1.JHn_ThreeDigests
/-- The three retained-byte equations are proved separately; only the453
concrete tree digest equations remain a named hypothesis. -/
theorem source [trees : JHe_SHARealization] : JHh_SHARealization := {
  toJHe_SHARealization := trees
  proof := JHn_ProofEquation.source
  publicInput := JHn_PublicEquation.source
  checksum := JHn_ChecksumEquation.source }
#print axioms source
end AspisR1.JHn_ThreeDigests
