import Op4P_Install
import Op3I_Cuts
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Op4P_Cuts
open AspisR1CurrentCaller S2W_NativeConsolidation

/-- Both laws follow from the same accepted TX1 call and the same SourceCuts.
Only op4 is further specialized; op3 remains Op3I's installed source body. -/
theorem same_cut_scan (adapterOps : AdapterRw.Ops) (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts
      (ClaimsUnrolledSdk.sdkOps adapterOps (Op3I_Install.install (Op4P_Install.install ops)) B std)
      accounts1 accounts2 saved f s) :
    (RowShape_InstalledSlots.verifierOps (Op3I_Install.install (Op4P_Install.install ops)) B std).op4 f.proof =
      ok (.Ok ()) ∧
    Op4P_Install.sourceBody f.proof = ok (.Ok ()) ∧
    OraclePortCompactDraft.scan (MultiproofConeCanonical.bytesOf f.proof.val) := by
  have tx := AspisS6CurrentFirstInstallation.current_success
    (RowShape_InstalledSlots.verifierOps (Op3I_Install.install (Op4P_Install.install ops)) B std) _
    f.semantic f.pub f.proof f.split () saved
    (AspisS6CurrentStage1CodecJoin.first_success
      (ClaimsUnrolledSdk.sdkOps adapterOps (Op3I_Install.install (Op4P_Install.install ops)) B std)
      f.semantic f.pub f.proof f.split saved cuts.first)
  obtain ⟨_,variant,zero,prepared,scratch,shape,scan,_⟩ :=
    Tx1Reachability.tx1_success _ _ _ f.pub f.proof f.split () saved tx
  have headerCall : Op3I_Install.sourceBody f.proof = ok (.Ok variant) := shape
  have header := (Op3I_Install.header_of_success f.proof variant headerCall).2
  have length : f.proof.val.length = 57607 := by
    simpa only [MultiproofConeCanonical.bytesOf,List.length_map] using
      ((OraclePortHeader.accepts_iff _).mp header).1
  have scanCall : Op4P_Install.sourceBody f.proof = ok (.Ok ()) := scan
  exact ⟨scan,scanCall,Op4P_Install.scan_of_success f.proof length scanCall⟩

#print axioms same_cut_scan
end AspisR1.Op4P_Cuts
end
