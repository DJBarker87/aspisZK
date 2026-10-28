import NDO_JGx_AdoptedStage
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_SdkVerifier
open Aeneas Aeneas.Std Result DrvC_Installation
attribute [local irreducible] VTop_Stages.verifier.candidate.tx2_authenticated

theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    (DrvC_Installation.sdk (JGx_Configuration.value c err)).op11
      (DrvC_Installation.digest (JGx_Configuration.value c err))
      JFx_NativeBytes.publicInput JFx_NativeBytes.proof JFx_NativeBytes.checkpoint () none=ok (.Ok ()) :=
  JGx_AdoptedStage.source c err realizes
#print axioms source
end AspisR1.JGx_SdkVerifier
end
