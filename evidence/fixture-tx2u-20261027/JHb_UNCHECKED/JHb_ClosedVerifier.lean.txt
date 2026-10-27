import JHb_Realizes
import JGx_AdoptedStage
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHb_ClosedVerifier
open Aeneas Aeneas.Std Result DrvC_Installation
attribute [local irreducible] VTop_Stages.verifier.candidate.tx2_authenticated
/-- The complete installed verifier computation on the retained triple.
No SHA realization or reader/batch/query/flush/finish success premise remains.
This is not ASQ8 validation or outer SDK/native wrapper acceptance. -/
theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    VTop_Stages.verifier.candidate.tx2_authenticated (DrvC_Installation.stage (JGx_Configuration.value c err))
      (DrvC_Installation.digest (JGx_Configuration.value c err)) JFx_NativeBytes.publicInput
      JFx_NativeBytes.proof JFx_NativeBytes.checkpoint () none=ok (.Ok ()) :=
  JGx_AdoptedStage.source c err JHb_Realizes.source
#print axioms source
end AspisR1.JHb_ClosedVerifier
end
