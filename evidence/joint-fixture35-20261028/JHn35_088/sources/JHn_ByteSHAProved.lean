import JHn_ByteSHA
import JHn_ProofEquation
import JHn_PublicEquation
import JHn_ChecksumEquation
set_option autoImplicit false
namespace AspisR1.JHn_ByteSHAProved
/-- All byte-digest equations are independently proved; no tree premises. -/
theorem source : JHn_ByteSHA :=
  ⟨JHn_ProofEquation.source,JHn_PublicEquation.source,JHn_ChecksumEquation.source⟩
#print axioms source
end AspisR1.JHn_ByteSHAProved
