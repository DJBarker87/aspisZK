import NCA_CheckPort
import Op4P_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCA_AcceptedScan
open Aeneas Aeneas.Std Result AspisR1CurrentCaller S2W_NativeConsolidation

/-- Discharge the compact-check premise of NBR on the SAME accepted TX1 cut.
The native association of the op4 implementation remains a named P6 lower
bridge, rather than an extra successful check supplied by the caller. -/
theorem source (adapterOps : AdapterRw.Ops) (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts
      (ClaimsUnrolledSdk.sdkOps adapterOps (Op3I_Install.install (Op4P_Install.install ops)) B std)
      accounts1 accounts2 saved f s) :
    LPt_External.compact.check_values (NBR_ProducerBuffers.compactInput f.proof)=ok (.Ok ()) := by
  obtain ⟨_,_,header,_⟩ := Op3I_Cuts.same_cut_header adapterOps (Op4P_Install.install ops)
    B std accounts1 accounts2 saved f s cuts
  have length : f.proof.val.length=57607 := by
    simpa only [MultiproofConeCanonical.bytesOf,List.length_map] using
      ((OraclePortHeader.accepts_iff _).mp header).1
  exact NCA_CheckPort.y1 f.proof length
    (Op4P_Cuts.same_cut_scan adapterOps ops B std accounts1 accounts2 saved f s cuts).2.2

#print axioms source
end AspisR1.NCA_AcceptedScan
end
