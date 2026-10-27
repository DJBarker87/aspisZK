import F3S_ReaderSkeleton
import F3S_MapLog
import GExq_RetainedReader
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_ReaderSyntax
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect
 theorem program (ops : ResumeOps) (ck proof pub : Slice U8) (v : transport.Variant)
    (size : 32≤ck.val.length) :
    Port8EFF_NativeReader.program ops ck proof pub v=CheckpointBytes5Resume.program ops ck proof pub v := by
  have tails : Port4A_NativeReader.tail ops ck v=CheckpointBytes5Resume.tail ops ck v := by
    funext i4 end1 s6 a2
    rfl
  rw [F3S_ReaderSkeleton.native,F3S_ReaderSkeleton.retained,tails]
  have order : (32#usize : Usize).val≤(Slice.len ck).val := by
    change 32≤ck.val.length
    exact size
  rw [Port4A_ReaderNormalize.checked_sub (Slice.len ck) 32#usize order]
  rfl
 theorem log (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (reserved : Bool) (ck proof pub : Slice U8) (size : 32≤ck.val.length) :
    SdkC_Source.readLog (SdkC_Source.run hashv (GExq_RetainedReader.code reserved ck proof pub .S2) []).2=
      SdkC_Source.readLog (SdkC_Source.run hashv
        (CheckpointBytes5Resume.program (CheckpointBytes4Ops.ops reserved) ck proof pub .S2) []).2 := by
  have mapped := F3S_MapLog.run_map hashv (Port8EFF_NativeReader.program
    (CheckpointBytes4Ops.ops reserved) ck proof pub .S2)
    (fun out=> match out with | core.result.Result.Ok pair=>core.result.Result.Ok pair | core.result.Result.Err e=>core.result.Result.Err (Port3_CheckpointInstall.error e)) []
  change _=_ at mapped
  rw [program _ ck proof pub .S2 size] at mapped
  exact congrArg SdkC_Source.readLog mapped
#print axioms program
#print axioms log
end AspisR1.F3S_ReaderSyntax
end
