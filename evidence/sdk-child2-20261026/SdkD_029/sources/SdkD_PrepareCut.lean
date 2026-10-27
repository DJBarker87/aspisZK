import SdkD_PrepareProvenance
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_PrepareCut
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open S2W_NativeConsolidation

/-- The actual preparation, copied folded root and batch call of THIS source
cut. Prepared is not selected from a separate successful verifier execution. -/
theorem first {F : Type} (adapter : AdapterRw.Ops) (ops : Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (Op5T_SamePair.dictionary adapter ops stage finish B std)
      accounts1 accounts2 saved f s) :
    let installed := RowShape_InstalledSlots.verifierOps (Op3I_Install.install (Op5T_Concrete.current ops)) B std
    let D := AspisS6CurrentFirstInstallation.toDigest
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
        (Op5T_SamePair.dictionary adapter ops stage finish B std))
    ∃ (zero : aspis_core.field.wide_exact.WideExact) (p : verifier.Prepared)
      (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (root : Array U8 32#usize) (view : Slice U8),
      aspis_core.field.wide_exact.WideExact.ZERO installed = ok zero ∧
      verifier.candidate.prepare installed D (AspisS6CurrentVerifierCarrier.toPublic f.semantic)
        f.proof () none (Array.repeat 29#usize zero) = ok (.Ok p,g) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        f.proof {start:=7751#usize,«end»:=7783#usize} = ok view ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view = ok (.Ok root) ∧
      Op5T_Install.currentBatch Port4B_Install.leaves D f.proof p root 0#usize () = ok (.Ok ()) := by
  dsimp only
  have tx := AspisS6CurrentFirstInstallation.current_success
    (RowShape_InstalledSlots.verifierOps (Op3I_Install.install (Op5T_Concrete.current ops)) B std) _
    f.semantic f.pub f.proof f.split () saved
    (AspisS6CurrentStage1CodecJoin.first_success
      (Op5T_SamePair.dictionary adapter ops stage finish B std) f.semantic f.pub f.proof f.split saved cuts.first)
  obtain ⟨split,variant,zero,p,g,shape,scan,hzero,hprepare,tail⟩ :=
    Tx1Reachability.tx1_success _ _ _ f.pub f.proof f.split () saved tx
  have constants := SdkD_FoldedCut.installed_constants (Op3I_Install.install (Op5T_Concrete.current ops)) B std
  obtain ⟨root,view,range,copy,batch⟩ :=
    SdkD_FoldedCut.suffix _ _ f.pub f.proof f.split () p g saved constants.1 constants.2 tail
  exact ⟨zero,p,g,root,view,hzero,hprepare,range,copy,batch⟩

#print axioms first
end AspisR1.SdkD_PrepareCut
end
