import PFin_WorldFirst
import PFin_WorldEval
import PFin_WorldSecond
import PFin_SecondCode
import F3V_RunEvidence
import F3V_SecondComplete
import F3S_SecondOnRun
import GExq_SecondSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_WorldSchedule
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem log {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : Submission)
    (H : Bytes → State) (e : Evidence c B s H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (accepted : (AspisV8R19.MemoizedProgramLaw.eval H (F3T_Installed.source c hashv (input c s))).2=true)
    (first : AspisR1CurrentCaller.verifier.candidate.tx1
      (GExp_FirstCode.installed (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) c.boundaries c.std)
      (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize () none=ok (.Ok e.saved)) :
    ∃ (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
      (root : Array U8 32#usize) (view : Slice U8),
      AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops c.reserved)
        (VTop_Checkpoint.digest (D2 c H)) e.saved.deref e.proof e.pub .S2 ()=ok (.Ok (p,a)) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        e.proof {start:=7751#usize,«end»:=7783#usize}=ok view ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view=ok (.Ok root) ∧
      Op5T_Install.stageBatch Port4B_Install.leaves (D2 c H) e.proof p root 1#usize ()=ok (.Ok ()) ∧
      (AspisV8R19.MemoizedProgramLaw.eval H (F3T_Installed.source c hashv (input c s))).1=
      SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H) (SdkD_PrepareLower.lower
        (SdkD_PrepareSource.code (Uni_Install.current c.currentBase c.reserved c.query c.geometry)
          c.boundaries c.std (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.proof ()
          (Array.repeat 29#usize e.run.zero))) []).2 ++
      (SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
        (SdkC_BatchSource.currentCode (F3U_Oracle.hashv H) e.proof e.run.p e.run.root) []).2 ++
      (SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
        (GExp_FirstCode.writerCode e.run.p {e.run.out with weights:=⟨e.run.flushed.val,e.run.flushed.property⟩} e.proof e.pub) []).2 ++
      (SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
        (GExq_RetainedReader.code c.reserved e.saved.deref e.proof e.pub .S2) []).2 ++
       SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
        (SdkC_BatchSource.stageCode (F3U_Oracle.hashv H) e.proof p root) []).2))) := by
  have evaluated := congrArg Prod.fst (PFin_WorldEval.log c B s H e hashv accepted first)
  dsimp only at evaluated
  have firstLog := PFin_WorldFirst.log c B s H e hashv first
  obtain ⟨p,a,root,view,read,range,copy,batch,secondLog⟩ := PFin_WorldSecond.log c B s H e hashv
  rw [firstLog,secondLog] at evaluated
  exact ⟨p,a,root,view,read,range,copy,batch,by simpa only [List.append_assoc] using evaluated⟩

#print axioms log
end AspisR1.PFin_WorldSchedule
end
