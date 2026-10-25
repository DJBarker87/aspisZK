import GExp_ExperimentTransport
import GExp_SecondPair
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_FixedPair
open Aeneas Aeneas.Std Result GExp_Experiment
open S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def firstInput (f : FirstCut) : FirstInputs :=
  ⟨AspisS6CurrentVerifierCarrier.toPublic f.semantic,f.pub,f.proof,f.split⟩
def secondInput (s : SecondCut) : SecondInputs := ⟨s.pub,s.proof,s.checkpoint⟩

def program {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (f : FirstCut) (s : SecondCut) :=
  let sdk := GExp_SecondPair.sdk adapter ops stage finish reserved query geo B std
  GExp_Experiment.program (GExp_FirstPair.base ops reserved query geo)
    (GExp_SecondPair.base stage finish reserved query geo) reserved B std hashv
    (GExp_InstalledPrepare.digest sdk) (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 sdk)
    (.done (firstInput f)) (fun _ _ => .done (secondInput s))

theorem same_pair {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (GExp_SecondPair.sdk adapter ops stage finish reserved query geo B std) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (GExp_SecondPair.sdk adapter ops stage finish reserved query geo B std)
      accounts1 accounts2 saved f s) :
    eval H (program adapter ops stage finish reserved query geo B std hashv f s) =
      (SdkC_Source.readLog (SdkC_Source.run hashv
        (GExp_FirstPair.code (Tx2I_Install.install adapter (Op5T_Concrete.stage
          (Tx2N_Execution.control stage reserved query geo)) finish)
          ops stage finish reserved query geo B std hashv f) []).2 ++
       SdkC_Source.readLog (SdkC_Source.run hashv
        (GExp_SecondPair.code adapter ops stage finish reserved query geo B std hashv s) []).2,
       firstInput f,ok (.Ok saved),some (secondInput s,ok (.Ok ()))) := by
  have first := GExp_FirstPair.same_pair
    (Tx2I_Install.install adapter (Op5T_Concrete.stage (Tx2N_Execution.control stage reserved query geo)) finish)
    ops stage finish reserved query geo B std native1 native2 hashv extraction sha256 H p1 syscall
    accounts1 accounts2 saved f s cuts
  have second := GExp_SecondPair.same_pair adapter ops stage finish reserved query geo B std
    native1 native2 hashv extraction sha256 H p1 syscall accounts1 accounts2 saved f s cuts
  exact GExp_ExperimentTransport.accepted _ _ _ _ _ _ _ _ _ _ H _ _ saved [] _ [] _ rfl first.2.1 rfl second.2.1

#print axioms same_pair
end AspisR1.GExp_FixedPair
end
