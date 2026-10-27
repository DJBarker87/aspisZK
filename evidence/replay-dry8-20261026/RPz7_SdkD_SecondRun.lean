import RPz7_SdkD_PairBatches
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_SecondRun
open Aeneas Aeneas.Std Result
open S2W_NativeConsolidation

theorem same_cut {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (SdkD_PairBatches.dictionary adapter ops stage finish reserved query geo B std)
      accounts1 accounts2 saved f s) :
    let D := AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
      (SdkD_PairBatches.dictionary adapter ops stage finish reserved query geo B std)
    ∃ (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
      (root : Array U8 32#usize) (view : Slice U8),
      AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved)
        (VTop_Checkpoint.digest D) s.checkpoint s.proof s.pub .S2 () = ok (.Ok (p,a)) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        s.proof {start:=7751#usize,«end»:=7783#usize} = ok view ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view = ok (.Ok root) ∧
      Op5T_Install.stageBatch Port4B_Install.leaves D s.proof p root 1#usize () = ok (.Ok ()) := by
  dsimp only
  obtain ⟨variant,shape,common⟩ := Tx2I_Cuts.authenticated_reached
    (Tx2I_Install.stage (Op5T_Concrete.stage (SdkD_Install.stage stage reserved query geo)) finish)
    _ () s.pub s.proof s.checkpoint none cuts.second
  obtain ⟨p,a,root,view,read,range,copy,batch⟩ := SdkD_SecondCut.common _ _ () s.pub s.proof s.checkpoint
    rfl rfl rfl common
  have source := Port4A_ReaderInstall.accepted_source stage reserved _ () s.checkpoint s.proof s.pub .S2 p a read
  exact ⟨p,a,root,view,source,range,copy,batch⟩

#print axioms same_cut
end AspisR1.SdkD_SecondRun
end
