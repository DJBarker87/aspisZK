import GExp_SecondPair
import ARU_Returning
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_SecondPair
open Aeneas Aeneas.Std Result AspisR1CurrentCaller S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open GExp_SecondPair
theorem same_pair {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (sdk adapter ops stage finish reserved query geo B std) native1 native2 hashv)
    (H : Bytes → State)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (sdk adapter ops stage finish reserved query geo B std)
      accounts1 accounts2 saved f s)
    (agrees : ARS_QueryTransport.Agrees H (SdkC_Source.run hashv
      (code adapter ops stage finish reserved query geo B std hashv s) []).2) :
    SdkC_BatchPair.Returning hashv H (code adapter ops stage finish reserved query geo B std hashv s)
      (.Ok ()) := by
  apply ARU_Returning.returning hashv H _ _ ?_ agrees
  rw [SdkC_Source.erasure]
  unfold code
  rw [GExp_SecondSource.source _ _ _ _
    (S2W_DigestExtraction.native_binding _ native1 native2 hashv extraction ())]
  rw [installed]
  exact cuts.second

#print axioms same_pair
end AspisR1.ARU_SecondPair
end
