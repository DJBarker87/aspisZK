import PSem_SourceCuts
import PAln_Borrowed
import F3M_InactiveCanonical
import CurrentPreparedInstalledMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_Cuts
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisS1ValuesOwnedInstallation OriginalSerializerInstallation

/-- Invert this successful preparation, without assuming a complete TX1. -/
theorem buffers (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (RowShape_InstalledSlots.verifierOps ops B std)
      D pub proof hash none input=ok (.Ok p,scratch)) :
    ∃ (stored initial expanded y1 : Slice U8) (view : verifier.View)
      (sem : r1_semantic.Verified H),
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=16#usize,«end»:=7031#usize}=ok stored ∧
      AspisS1NativeCompact.compact.expand_semantic nativeValues stored initial=ok (.Ok (),expanded) ∧
      sourceView proof expanded y1=ok (.Ok view) ∧ view.semantic=expanded ∧
      S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
        (ClaimsUnrolledFinish.install std B) D pub expanded hash=ok (.Ok sem) ∧
      originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
        D sem view hash input=ok (.Ok p,scratch) := by
  exact NativeBuffers.prepare_buffers (withValues ops) nativeValues
    AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install std B)
    (fun input output status updated call => length_frame input output updated status call)
    D pub proof hash p input scratch success

#print axioms buffers
end AspisR1.SAP_Cuts
end
