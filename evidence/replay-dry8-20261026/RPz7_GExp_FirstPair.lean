import RPz7_GExp_FirstAccepted
import RPz7_SdkD_Accepted
import RPz7_SdkC_BatchPair
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_FirstPair
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def base {C : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C) :=
  Op3I_Install.install (Uni_Install.base ops reserved query geo)

theorem installed {C : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    GExp_FirstCode.installed (base ops reserved query geo) B std =
    RowShape_InstalledSlots.verifierOps (Uni_Install.current ops reserved query geo) B std := by
  cases ops; rfl

def code {F C : Type} (adapter : AdapterRw.Ops) (ops : Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (f : FirstCut) :=
  GExp_FirstCode.code (base ops reserved query geo) B std hashv
    (GExp_InstalledPrepare.digest (ClaimsUnrolledSdk.sdkOps adapter
      (Uni_Install.current ops reserved query geo) B std))
    (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split

theorem same_pair {F C : Type} (adapter : AdapterRw.Ops) (ops : Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (ClaimsUnrolledSdk.sdkOps adapter (Uni_Install.current ops reserved query geo) B std)
      native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (ClaimsUnrolledSdk.sdkOps adapter (Uni_Install.current ops reserved query geo) B std)
      accounts1 accounts2 saved f s) :
    SdkC_BatchPair.Returning hashv H (code adapter ops stage finish reserved query geo B std hashv f)
      (.Ok saved) := by
  apply SdkC_BatchPair.returning hashv sha256 H p1 syscall
  rw [SdkC_Source.erasure]
  unfold code
  rw [GExp_FirstSource.source _ _ _ _ _
    (S2W_DigestExtraction.native_binding _ native1 native2 hashv extraction ())]
  rw [installed]
  exact AspisS6CurrentFirstInstallation.current_success _ _ f.semantic f.pub f.proof f.split () saved
    (AspisS6CurrentStage1CodecJoin.first_success _ f.semantic f.pub f.proof f.split saved cuts.first)

#print axioms installed
#print axioms same_pair
end AspisR1.GExp_FirstPair
end
