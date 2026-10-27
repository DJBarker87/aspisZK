import JGx_AdoptedStage
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_Saved
open Aeneas Aeneas.Std Result DrvC_Installation
attribute [local irreducible] VTop_Stages.verifier.candidate.tx2_authenticated

theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (saved : alloc.vec.Vec U8) (same : saved.val=JFx_NativeBytes.checkpoint.val)
    (realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    VTop_Stages.verifier.candidate.tx2_authenticated (DrvC_Installation.stage (JGx_Configuration.value c err))
      (DrvC_Installation.digest (JGx_Configuration.value c err)) JFx_NativeBytes.publicInput
      JFx_NativeBytes.proof (⟨saved.val,saved.property⟩ : Slice U8) () none=ok (.Ok ()) := by
  have cp : (⟨saved.val,saved.property⟩ : Slice U8)=JFx_NativeBytes.checkpoint := Subtype.ext same
  rw [cp]
  exact JGx_AdoptedStage.source c err realizes
#print axioms source
end AspisR1.JGx_Saved
end
