import NDO_JGx_Authenticated
import NDO_JGx_Configuration
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_AdoptedStage
open Aeneas Aeneas.Std Result DrvC_Installation
attribute [local irreducible] VTop_Stages.verifier.candidate.tx2_authenticated

theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    VTop_Stages.verifier.candidate.tx2_authenticated (DrvC_Installation.stage (JGx_Configuration.value c err))
      (DrvC_Installation.digest (JGx_Configuration.value c err)) JFx_NativeBytes.publicInput
      JFx_NativeBytes.proof JFx_NativeBytes.checkpoint () none=ok (.Ok ()) := by
  rw [JGx_Configuration.stage]
  have computed := JGx_Authenticated.source c.stageBase c.finish err c.geometry c.query
    (DrvC_Installation.digest (JGx_Configuration.value c err)) () realizes
  rw [←JGx_Configuration.digest] at computed
  exact computed
#print axioms source
end AspisR1.JGx_AdoptedStage
end
