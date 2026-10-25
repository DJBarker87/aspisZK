import GExp_SecondSource
import GExp_FirstPair
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_SecondPair
open Aeneas Aeneas.Std Result
open S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def base {F C : Type} (stage : VTop_Stages.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C) :=
  Tx2I_Install.stage (Op5T_Concrete.stage (Tx2N_Execution.control stage reserved query geo)) finish

def sdk {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :=
  ClaimsUnrolledSdk.sdkOps
    (Tx2I_Install.install adapter (Op5T_Concrete.stage (Tx2N_Execution.control stage reserved query geo)) finish)
    (Uni_Install.current ops reserved query geo) B std

theorem installed {F C : Type} (stage : VTop_Stages.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C) :
    GExp_SecondCode.installed (base stage finish reserved query geo) reserved =
      base stage finish reserved query geo := by
  cases stage; rfl

def code {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (s : SecondCut) :=
  GExp_SecondCode.code (base stage finish reserved query geo) reserved hashv
    (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
      (sdk adapter ops stage finish reserved query geo B std)) s.pub s.proof s.checkpoint

theorem same_pair {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (sdk adapter ops stage finish reserved query geo B std) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (sdk adapter ops stage finish reserved query geo B std)
      accounts1 accounts2 saved f s) :
    SdkC_BatchPair.Returning hashv H (code adapter ops stage finish reserved query geo B std hashv s)
      (.Ok ()) := by
  apply SdkC_BatchPair.returning hashv sha256 H p1 syscall
  rw [SdkC_Source.erasure]
  unfold code
  rw [GExp_SecondSource.source _ _ _ _
    (S2W_DigestExtraction.native_binding _ native1 native2 hashv extraction ())]
  rw [installed]
  exact cuts.second

#print axioms installed
#print axioms same_pair
end AspisR1.GExp_SecondPair
end
