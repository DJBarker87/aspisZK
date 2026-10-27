import RPz7_Tx1Q_Execution
import RPz7_S1NativePrepareBuffersV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.PSem_SourceCuts
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisS1ValuesOwnedInstallation OriginalSerializerInstallation

/-- The SAME preparation returns the compact input, expanded output, parsed
semantic verifier input, source View and semantic object. No second prepare
or independent successful child is selected. -/
theorem buffers {CoreError H : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved) :
    ∃ (stored initial expanded y1 : Slice U8) (view : verifier.View)
      (sem : r1_semantic.Verified H),
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=16#usize,«end»:=7031#usize}=ok stored ∧
      AspisS1NativeCompact.compact.expand_semantic nativeValues stored initial=ok (.Ok (),expanded) ∧
      sourceView proof expanded y1=ok (.Ok view) ∧ view.semantic=expanded ∧
      S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
        (ClaimsUnrolledFinish.install std B) D pub expanded hash=ok (.Ok sem) ∧
      originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
        D sem view hash (Array.repeat 29#usize run.zero)=ok (.Ok run.p,run.scratch) := by
  apply NativeBuffers.prepare_buffers
    (withValues (Op3I_Install.install (Op4P_Install.install (Tx1Q_Execution.base ops reserved query geo))))
    nativeValues AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install std B)
    (fun input output status updated call => length_frame input output updated status call)
    D pub proof hash run.p (Array.repeat 29#usize run.zero) run.scratch
  exact run.prepare_call

theorem parsed_prefix {CoreError H : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved) :
    ∃ (stored initial expanded y1 : Slice U8) (view : verifier.View)
      (sem : r1_semantic.Verified H) (pre : AspisR1PublicPreparation.r1_wire.Prefix),
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=16#usize,«end»:=7031#usize}=ok stored ∧
      AspisS1NativeCompact.compact.expand_semantic nativeValues stored initial=ok (.Ok (),expanded) ∧
      sourceView proof expanded y1=ok (.Ok view) ∧ view.semantic=expanded ∧
      S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
        (ClaimsUnrolledFinish.install std B) D pub expanded hash=ok (.Ok sem) ∧
      originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
        D sem view hash (Array.repeat 29#usize run.zero)=ok (.Ok run.p,run.scratch) ∧
      AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded=ok (.Ok pre) := by
  obtain ⟨stored,initial,expanded,y1,view,sem,read,expand,wide,same,verify,prepare⟩ :=
    buffers ops reserved query geo B std D hash pub publicBytes proof split saved run
  obtain ⟨pre,t0,t1,challenges,payload,root,parsed,_⟩ :=
    S1SemanticInstallation.verify_roots AspisS1ExtractedRoundChildren.children
      (ClaimsUnrolledFinish.install std B) D pub expanded hash sem verify
  exact ⟨stored,initial,expanded,y1,view,sem,pre,read,expand,wide,same,verify,prepare,parsed⟩

#print axioms parsed_prefix
#print axioms buffers
end AspisR1.PSem_SourceCuts
end
