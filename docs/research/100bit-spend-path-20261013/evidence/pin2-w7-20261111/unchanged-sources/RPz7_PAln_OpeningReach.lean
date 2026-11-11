import RPz7_PAln_Borrowed
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.PAln_OpeningReach
open AspisR1CurrentCaller InstalledPreparation OriginalPreparedInstallation
open BorrowedClaimPrepared AspisS1ValuesOwnedInstallation OriginalSerializerInstallation
open AspisR1PreparedSourcePowersBoundariesV1
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning

/-- The opening preparation uses the same semantic value, view, returned
Prepared and scratch of this accepted TX1. Child successes are conclusions. -/
theorem on_run {CoreError H : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved) :
    ∃ (stored initial expanded y1 : Slice U8) (view : verifier.View)
      (sem : r1_semantic.Verified H) (retained : AspisR1PublicPreparation.verifier.Prepared)
      (rs : Array AspisR1PublicPreparation.aspis_core.field.WideExact 29#usize),
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=16#usize,«end»:=7031#usize}=ok stored ∧
      AspisS1NativeCompact.compact.expand_semantic nativeValues stored initial=ok (.Ok (),expanded) ∧
      sourceView proof expanded y1=ok (.Ok view) ∧ view.semantic=expanded ∧
      S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
        (ClaimsUnrolledFinish.install std B) D pub expanded hash=ok (.Ok sem) ∧
      AspisR1PublicPreparation.PreparedScratchReachability.Reachable
        (concreteBoundaries (installedBoundaries (withOriginalSerializer closedSampling)
          AspisS1M31Embedding.Total.embed)) (retainedDigest D) (retainedSem sem)
        (retainedView view) hash retained rs ∧
      currentPrepared retained=run.p ∧ mapArray currentE rs=run.scratch := by
  obtain ⟨stored,initial,expanded,y1,view,sem,read,expand,wide,same,verify,prepare⟩ :=
    PSem_SourceCuts.buffers ops reserved query geo B std D hash pub publicBytes proof split saved run
  obtain ⟨retained,rs,reached,out,scratch⟩ := PAln_Borrowed.original_reached
    (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed D sem view hash
    (Array.repeat 29#usize run.zero) run.scratch run.p prepare
  exact ⟨stored,initial,expanded,y1,view,sem,retained,rs,read,expand,wide,same,verify,reached,out,scratch⟩

#print axioms on_run
end AspisR1.PAln_OpeningReach
end
