import NDO_JHn_ByteSHA
import NDO_JHn_ProofEquation
import NDO_JHn_PublicEquation
import NDO_JHn_ChecksumEquation
set_option autoImplicit false
namespace AspisR1.JHn_ByteSHAProved
/-- All byte-digest equations are independently proved; no tree premises. -/
theorem source : JHn_ByteSHA :=
  ⟨JHn_ProofEquation.source,JHn_PublicEquation.source,JHn_ChecksumEquation.source⟩
#print axioms source
end AspisR1.JHn_ByteSHAProved
