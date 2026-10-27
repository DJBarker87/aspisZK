import F3S_FirstHeader
import F3S_FirstTailLogs
import F3S_RunCalls
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_FirstOnRun
open Aeneas Aeneas.Std Result CheckpointBytes5Effect AspisR1CurrentCaller
 theorem log {C Hash : Type} (base : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (law : ∀ h parts,D.digest h parts=hashv parts)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (GExp_FirstCode.installed base B std) reserved query geo D hash semantic pub proof split saved)
    (slots : Tx1Q_Execution.Slots (GExp_FirstCode.installed base B std) reserved query geo)
    (zeroCall : aspis_core.field.wide_exact.WideExact.ZERO (GExp_FirstCode.installed base B std)=ok run.zero)
    (start : compact.OFF_FOLDED_ROOT (GExp_FirstCode.installed base B std)=ok 7751#usize)
    (finish : compact.OFF_ROUND1 (GExp_FirstCode.installed base B std)=ok 7783#usize)
    (view : Slice U8)
    (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=7751#usize,«end»:=7783#usize}=ok view)
    (copy : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view=ok (.Ok run.root))
    (success : erase (SdkC_Source.dictionary hashv) ()
      (GExq_FirstCode.code base B std hashv D semantic pub proof split hash)=ok (.Ok saved)) :
    SdkC_Source.readLog (SdkC_Source.run hashv
      (GExq_FirstCode.code base B std hashv D semantic pub proof split hash) []).2=
    SdkC_Source.readLog (SdkC_Source.run hashv (SdkD_PrepareLower.lower
      (SdkD_PrepareSource.code (Op5T_Concrete.current {base with op16:=Tx1Q_Install.writer})
        B std D semantic proof hash (Array.repeat 29#usize run.zero))) []).2 ++
    (SdkC_Source.readLog (SdkC_Source.run hashv (GExq_BatchSource.current D hash proof run.p run.root) []).2 ++
     SdkC_Source.readLog (SdkC_Source.run hashv (GExp_FirstCode.writerCode run.p
       {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩} proof pub) []).2) := by
  obtain ⟨zero,p,scratch,hzero,hprep,tail,logs⟩ :=
    F3S_FirstHeader.split base B std hashv D semantic pub proof split hash saved success
  have zeroSame : zero=run.zero := Result.ok.inj (hzero.symm.trans zeroCall)
  subst zero
  rw [GExq_FirstErasure.prepare base B std hashv D law] at hprep
  have same := Result.ok.inj (hprep.symm.trans run.prepare_call)
  have pSame := core.result.Result.Ok.inj (congrArg Prod.fst same)
  have scratchSame := congrArg Prod.snd same
  dsimp only at pSame scratchSame
  subst p
  subst scratch
  obtain ⟨initial,geometry,pending,queryCall,flush,writer⟩ :=
    F3S_RunCalls.source _ reserved query geo D hash semantic pub proof split saved run slots
  have batch : erase (SdkC_Source.dictionary hashv) ()
      (GExq_BatchSource.current D hash proof run.p run.root)=ok (.Ok ()) := by
    rw [GExq_FirstErasure.batch hashv D hash (law hash)]
    exact run.batch_call
  have wrote : erase (SdkC_Source.dictionary hashv) () (GExp_FirstCode.writerCode run.p
      {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩} proof pub)=ok saved := by
    rw [GExq_FirstErasure.writer hashv D hash (law hash)]
    rw [slots.writer] at writer
    exact writer
  have tailLog := F3S_FirstTailLogs.on_calls base B std hashv D pub proof split hash run.p run.scratch
    run.initial run.out run.geometry run.pending run.after run.flushed run.root view
    initial start finish range copy batch geometry pending queryCall saved wrote flush
  exact logs.trans (congrArg (fun l=>_ ++ l) tailLog)
#print axioms log
end AspisR1.F3S_FirstOnRun
end
