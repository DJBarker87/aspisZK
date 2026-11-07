import NLI_SourceEquality
import NLU_FrontierSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Transcription
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Frozen r1_semantic.rs:232-308; NMC_REVIEWED_TRANSCRIPTION records the
single reviewed item. Native parent fidelity is not asserted by this theorem. -/
theorem source {H : Type} (input : NLC_Finish.Input H) :
 NLC_Goals.FinishSourceEquality input := NLI_Source.finishSourceEquality input
#print axioms source
set_option pp.proofs false in #print source
end AspisR1.NMC_Transcription
end
