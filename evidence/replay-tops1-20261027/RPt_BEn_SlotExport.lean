import RPt_BEn_LocalAssociation
import RPt_BEk_SlotExport
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEn_SlotExport
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem current {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (H : Bytes → State) (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared) (root : Digest)
    (state : S) (before : Log)
    (returning : SdkC_BatchPair.Returning hashv H (SdkC_BatchSource.currentCode hashv proof p root) (.Ok ())) :
    BEj_SlotExport.Prefix hashv H (SdkC_BatchSource.currentCode hashv proof p root) before
      (BEn_ExtractedSlots.observe call (BEn_ExtractedSlots.currentBody hashv proof p root) state before).2.2 :=
  BEk_SlotExport.current call hashv binding H proof p root state before _
    (BEn_LocalAssociation.current call hashv proof p root state before) returning

theorem stage {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (H : Bytes → State) (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (root : Digest)
    (state : S) (before : Log)
    (returning : SdkC_BatchPair.Returning hashv H (SdkC_BatchSource.stageCode hashv proof p root) (.Ok ())) :
    BEj_SlotExport.Prefix hashv H (SdkC_BatchSource.stageCode hashv proof p root) before
      (BEn_ExtractedSlots.observe call (BEn_ExtractedSlots.stageBody hashv proof p root) state before).2.2 :=
  BEk_SlotExport.stage call hashv binding H proof p root state before _
    (BEn_LocalAssociation.stage call hashv proof p root state before) returning

#print axioms current
#print axioms stage
end AspisR1.BEn_SlotExport
end
