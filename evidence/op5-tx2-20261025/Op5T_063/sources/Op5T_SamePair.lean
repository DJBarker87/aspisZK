import Op5T_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.Op5T_SamePair
open Aeneas Aeneas.Std Result
open S2W_NativeConsolidation

def dictionary {F : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :=
  ClaimsUnrolledSdk.sdkOps (Tx2I_Install.install adapter (Op5T_Concrete.stage stage) finish)
    (Op3I_Install.install (Op5T_Concrete.current ops)) B std

/-- Both batch successes are derived from the SAME f/s SourceCuts exported by
accepted_pair_claims_op5. Neither batch success nor an independent cut is an
input. Source Prepared/root arguments are retained, not model replacements. -/
theorem batches {F : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (dictionary adapter ops stage finish B std) accounts1 accounts2 saved f s) :
    let sdk := dictionary adapter ops stage finish B std
    let D := AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 sdk
    let currentD := AspisS6CurrentFirstInstallation.toDigest D
    ∃ (p0 : AspisR1CurrentCaller.verifier.Prepared) (root0 : Array U8 32#usize)
      (p1 : VTop_Stages.verifier.Prepared) (root1 : Array U8 32#usize),
      Op5T_Install.currentBatch Port4B_Install.leaves currentD f.proof p0 root0 0#usize () = ok (.Ok ()) ∧
      Op5T_Install.stageBatch Port4B_Install.leaves D s.proof p1 root1 1#usize () = ok (.Ok ()) := by
  dsimp only
  have tx := AspisS6CurrentFirstInstallation.current_success
    (RowShape_InstalledSlots.verifierOps (Op3I_Install.install (Op5T_Concrete.current ops)) B std) _
    f.semantic f.pub f.proof f.split () saved
    (AspisS6CurrentStage1CodecJoin.first_success
      (dictionary adapter ops stage finish B std) f.semantic f.pub f.proof f.split saved cuts.first)
  obtain ⟨_,variant,zero,p0,g,shape,scan,z,prep,suffix⟩ :=
    AspisR1CurrentCaller.Tx1Reachability.tx1_success _ _ _ f.pub f.proof f.split () saved tx
  obtain ⟨root0,batch0⟩ := Op5T_Cuts.first_batch _ _ f.pub f.proof f.split () p0 g saved suffix
  obtain ⟨variant,shape,common⟩ := Tx2I_Cuts.authenticated_reached
    (Tx2I_Install.stage (Op5T_Concrete.stage stage) finish) _ () s.pub s.proof s.checkpoint none cuts.second
  obtain ⟨p1,root1,batch1⟩ := Op5T_Cuts.second_batch _ _ () s.pub s.proof s.checkpoint common
  exact ⟨p0,root0,p1,root1,batch0,batch1⟩

#print axioms batches
end AspisR1.Op5T_SamePair
end
