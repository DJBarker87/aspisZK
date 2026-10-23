import Port1_LibraryDecode
import Port1_DriverSubstitution
import Port1_CarrierObstruction
import Port1_Annotation

/-! Final focused compatible-import and trust-boundary audit. This is not a
coherent frozen release replay and establishes no deployed security target. -/
set_option autoImplicit false
namespace AspisR1.Port1_Audit
#print AspisR1.Port1_Library.TrustedStd
#print AspisR1.Port1_DriverSubstitution.BodyJoins
#print AspisR1.Port1_Annotation.backward
#check AspisR1.VTop_Annotation.two_pass
#print axioms AspisR1.Port1_LibrarySource.mark_none
#print axioms AspisR1.Port1_LibraryDecode.map_bind
#print axioms AspisR1.Port1_LibraryDecode.map_ite
#print axioms AspisR1.Port1_LibraryDecode.limbs_agreement
#print axioms AspisR1.Port1_LibraryDecode.decoder_agreement
#print axioms AspisR1.Port1_LibraryDecode.strict_fixed
#print axioms AspisR1.Port1_LibraryDecode.wrong_length
#print axioms AspisR1.Port1_Library.std_semantics
#print axioms AspisR1.Port1_Library.library_values
#print axioms AspisR1.Port1_Library.library_no_read
#print axioms AspisR1.Port1_Library.library_join
#print axioms AspisR1.Port1_Library.release_mark
#print axioms AspisR1.Port1_Driver.stages_substitute
#print axioms AspisR1.Port1_DriverSubstitution.body_operation
#print axioms AspisR1.Port1_DriverSubstitution.ports
#print axioms AspisR1.Port1_DriverSubstitution.driver_substitute
#print axioms AspisR1.Port1_CarrierObstruction.constant_rejected
#print axioms AspisR1.Port1_CarrierObstruction.proof_irrelevant
#print axioms AspisR1.Port1_CarrierObstruction.raw_join_forces_rejection
#print axioms AspisR1.Port1_Annotation.source_enrich
#print axioms AspisR1.Port1_Annotation.backward
end AspisR1.Port1_Audit
