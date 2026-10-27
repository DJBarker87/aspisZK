import RPz7_SdkD_BatchUnion
import RPz7_SdkD_Tx1Run
import RPz7_SdkD_SecondCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_PairBatches
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open S2W_NativeConsolidation MultiproofConeCanonical

def dictionary {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :=
  Op5T_SamePair.dictionary adapter (Uni_Install.base ops reserved query geo)
    (SdkD_Install.stage stage reserved query geo) finish B std

abbrev current {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :=
  AspisS6CurrentFirstInstallation.toDigest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
    (dictionary adapter ops stage finish reserved query geo B std))

theorem first_run {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (dictionary adapter ops stage finish reserved query geo B std) accounts1 accounts2 saved f s) :
    ∃ run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo B std)
      reserved query geo (current adapter ops stage finish reserved query geo B std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved,
      ∃ view : Slice U8,
        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
          f.proof {start:=7751#usize,«end»:=7783#usize} = ok view ∧
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view = ok (.Ok run.root) := by
  have tx := AspisS6CurrentFirstInstallation.current_success
    (RowShape_InstalledSlots.verifierOps (Uni_Install.current ops reserved query geo) B std) _
    f.semantic f.pub f.proof f.split () saved
    (AspisS6CurrentStage1CodecJoin.first_success _ f.semantic f.pub f.proof f.split saved cuts.first)
  have same : RowShape_InstalledSlots.verifierOps (Uni_Install.current ops reserved query geo) B std =
      Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo B std := by
    rw [Uni_Install.compose_tx1]
    rfl
  rw [same] at tx
  have constants := SdkD_FoldedCut.installed_constants (Uni_Install.current ops reserved query geo) B std
  rw [same] at constants
  obtain ⟨run,zero,view,range,copy⟩ := SdkD_Tx1Run.accepted _ reserved query geo _ ()
    (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved
    (Tx1Q_Execution.actual_slots (Op5T_Concrete.current ops) reserved query geo B std)
    constants.1 constants.2 tx
  exact ⟨run,view,range,copy⟩

#print axioms first_run
end AspisR1.SdkD_PairBatches
end
