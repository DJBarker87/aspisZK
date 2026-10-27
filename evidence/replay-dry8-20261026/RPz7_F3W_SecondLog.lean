import RPz7_F3W_SourceLog
import RPz7_F3V_SecondRun
import RPz7_F3S_SecondOnRun
import RPz7_F3U_SecondCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3W_SecondLog
open Aeneas Aeneas.Std Result MultiproofConeCanonical CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem log {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Submission) (H : Bytes → State) (e : Evidence c B s H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) :
    ∃ (p2 : AspisR1Stage2.verifier.Prepared) (a2 : AspisR1Stage2.verifier.Accumulator)
      (root : Array U8 32#usize) (view : Slice U8),
      AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops c.reserved)
        (VTop_Checkpoint.digest (D2 c H)) e.saved.deref e.proof e.pub .S2 ()=ok (.Ok (p2,a2)) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        e.proof {start:=7751#usize,«end»:=7783#usize}=ok view ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view=ok (.Ok root) ∧
      Op5T_Install.stageBatch Port4B_Install.leaves (D2 c H) e.proof p2 root 1#usize ()=ok (.Ok ()) ∧
      SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
        (GExp_SecondCode.code (stage c) c.reserved hashv (digest c) e.pub e.proof e.saved.deref) []).2=
        SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
          (GExq_RetainedReader.code c.reserved e.saved.deref e.proof e.pub .S2) []).2 ++
        SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
          (SdkC_BatchSource.stageCode (F3U_Oracle.hashv H) e.proof p2 root) []).2 := by
  obtain ⟨p2,a2,root,view,read,range,copy,batch⟩ :=
    F3V_SecondRun.accepted c (D2 c H) () e.pub e.proof e.saved.deref e.second
  refine ⟨p2,a2,root,view,read,range,copy,batch,?_⟩
  rw [F3V_SecondComplete.same H,←F3U_SecondCode.same]
  have reader : erase (SdkC_Source.dictionary (F3U_Oracle.hashv H)) ()
      (GExq_RetainedReader.code c.reserved e.saved.deref e.proof e.pub .S2)=ok (.Ok (p2,a2)) := by
    rw [GExq_RetainedReader.source c.reserved (F3U_Oracle.hashv H) (D2 c H) () (fun _=>rfl)]
    rw [Port4A_ReaderInstall.reference_eq]
    unfold Port3_CheckpointInstall.reader
    rw [read]
    rfl
  have result := F3S_SecondOnRun.log (stage c) c.reserved (F3U_Oracle.hashv H) (D2 c H)
    e.pub e.proof e.saved.deref () p2 a2 root view reader rfl rfl rfl range copy
    (by rw [F3U_SecondCode.same,GExp_SecondSource.source (stage c) c.reserved
      (F3U_Oracle.hashv H) (D2 c H) (fun _=>rfl)];exact e.second)
  rw [F3S_BatchDictionary.stage] at result
  exact result

#print axioms log
end AspisR1.F3W_SecondLog
end
