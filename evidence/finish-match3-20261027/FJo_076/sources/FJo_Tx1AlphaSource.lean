import PAln_BothBuffers
import PAln_Borrowed
import F3M_InactiveCanonical
import CurrentPreparedInstalledMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_Tx1AlphaSource
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete
open AspisS1ValuesOwnedInstallation OriginalSerializerInstallation
/-- Actual TX1 scratch values, derived from the constructor in this execution. -/
theorem value {CoreError H : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved) :
    ∃ (p : AspisR1PublicPreparation.verifier.Prepared) (rs : Array PE 29#usize),
      currentPrepared p=run.p ∧ mapArray currentE rs=run.scratch ∧
      CanonicalAlphaPair p := by
  obtain ⟨stored,initial,expanded,storedY1,initialY1,y1,view,sem,
    read,expand,readY1,expandY1,wide,semanticEq,yEq,verify,prepare⟩ :=
    PAln_BothBuffers.on_run ops reserved query geo B std D hash pub publicBytes proof split saved run
  obtain ⟨p,rs,prepared,output,scratch⟩ := PAln_Borrowed.original_success
    (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed D sem view hash
    (Array.repeat 29#usize run.zero) run.scratch run.p prepare
  have meaning := prepared_installed_meaning
    (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed (retainedDigest D)
    (retainedSem sem) (retainedView view) hash p rs
    (mapArray retainedE (Array.repeat 29#usize run.zero))
    (F3M_InactiveCanonical.source proof expanded y1 view wide) prepared
  exact ⟨p,rs,output,scratch,meaning.2.1⟩
#print axioms value
end AspisR1.FJo_Tx1AlphaSource
end
