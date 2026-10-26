import RPz7_F3N_ConsDictionary
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_SameOracle
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem current {F C : Type} (a : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) :
    CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest (Tx1Q_Install.digest
      (SdkD_PairBatches.current a ops stage finish reserved query geo B std))) () H := by
  intro parts digest returned
  change (SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std).op43 () parts=ok digest at returned
  rw [extraction.digestSource,S2W_DigestExtraction.digest_eq_hashv] at returned
  exact (syscall.returningValue parts digest returned).trans (p1.realization _)

#print axioms current
end AspisR1.F3N_SameOracle
end
