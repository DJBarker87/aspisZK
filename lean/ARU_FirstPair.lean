import GExp_FirstPair
import ARU_Returning
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_FirstPair
open Aeneas Aeneas.Std Result AspisR1CurrentCaller S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open GExp_FirstPair
theorem same_pair {F C : Type} (adapter : AdapterRw.Ops) (ops : Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (ClaimsUnrolledSdk.sdkOps adapter (Uni_Install.current ops reserved query geo) B std)
      native1 native2 hashv)
    (H : Bytes → State)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (ClaimsUnrolledSdk.sdkOps adapter (Uni_Install.current ops reserved query geo) B std)
      accounts1 accounts2 saved f s)
    (agrees : ARS_QueryTransport.Agrees H (SdkC_Source.run hashv
      (code adapter ops stage finish reserved query geo B std hashv f) []).2) :
    SdkC_BatchPair.Returning hashv H (code adapter ops stage finish reserved query geo B std hashv f)
      (.Ok saved) := by
  apply ARU_Returning.returning hashv H _ _ ?_ agrees
  rw [SdkC_Source.erasure]
  unfold code
  rw [GExp_FirstSource.source _ _ _ _ _
    (S2W_DigestExtraction.native_binding _ native1 native2 hashv extraction ())]
  rw [installed]
  exact AspisS6CurrentFirstInstallation.current_success _ _ f.semantic f.pub f.proof f.split () saved
    (AspisS6CurrentStage1CodecJoin.first_success _ f.semantic f.pub f.proof f.split saved cuts.first)

#print axioms same_pair
end AspisR1.ARU_FirstPair
end
