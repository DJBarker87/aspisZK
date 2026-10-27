import RPz7_F3S_FirstOnRun
import RPz7_F3S_FirstBase
import RPz7_F3S_FirstHeader
import RPz7_F3S_FirstTailLogs
import RPz7_F3S_RunCalls
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_FirstPairLog
open Aeneas Aeneas.Std Result CheckpointBytes5Effect AspisR1CurrentCaller
 theorem log {C Hash : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (law : ∀ h parts,D.digest h parts=hashv parts)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo B std) reserved query geo D hash semantic pub proof split saved)
    (slots : Tx1Q_Execution.Slots (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo B std) reserved query geo)
    (zeroCall : aspis_core.field.wide_exact.WideExact.ZERO (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo B std)=ok run.zero)
    (start : compact.OFF_FOLDED_ROOT (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo B std)=ok 7751#usize)
    (finish : compact.OFF_ROUND1 (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo B std)=ok 7783#usize)
    (view : Slice U8)
    (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=7751#usize,«end»:=7783#usize}=ok view)
    (copy : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view=ok (.Ok run.root))
    (success : erase (SdkC_Source.dictionary hashv) ()
      (GExq_FirstCode.code (GExp_FirstPair.base ops reserved query geo) B std hashv D semantic pub proof split hash)=ok (.Ok saved)) :
    SdkC_Source.readLog (SdkC_Source.run hashv
      (GExq_FirstCode.code (GExp_FirstPair.base ops reserved query geo) B std hashv D semantic pub proof split hash) []).2=
    SdkC_Source.readLog (SdkC_Source.run hashv (SdkD_PrepareLower.lower
      (SdkD_PrepareSource.code (Uni_Install.current ops reserved query geo)
        B std D semantic proof hash (Array.repeat 29#usize run.zero))) []).2 ++
    (SdkC_Source.readLog (SdkC_Source.run hashv (GExq_BatchSource.current D hash proof run.p run.root) []).2 ++
     SdkC_Source.readLog (SdkC_Source.run hashv (GExp_FirstCode.writerCode run.p
       {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩} proof pub) []).2) := by
  have result := F3S_FirstOnRun.log (GExp_FirstPair.base ops reserved query geo) reserved query geo
    B std hashv D hash law semantic pub proof split saved
  rw [F3S_Dictionary.first] at result
  simpa only [F3S_FirstBase.preparation] using result run slots zeroCall start finish view range copy success
#print axioms log
end AspisR1.F3S_FirstPairLog
end
