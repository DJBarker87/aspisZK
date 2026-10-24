import S1ValuesOwnedStage1RootsV1
import S1ValuesOwnedPrepareViewY1V1
import S1ValuesOwnedStage1ViewY1V1
import S1ExtractedRoundChildrenV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedInstallation
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller AspisR1CurrentCaller.BorrowedClaimPrepared AspisR1CurrentCaller.InstalledPreparation


/-- Same complete accepted stage1, now with concrete extracted decode, boundary
and value children. The SDK/account transport is still an explicit residual. -/
theorem owned_stage1_extracted_children (adapterOps : AdapterRw.Ops) (ops : Ops)
   
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount)
    (data : Slice U8) (out : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned
      (AspisS6CurrentFirstInstallation.install adapterOps (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))
      program accounts data=ok (.Ok out)) :
    ∃ (bytes proof : Slice U8) (split : Usize)
      (statement : AspisR1PublicPreparation.FirstCaller.DecoderStatement),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok statement) ∧
      split=compact.SPLIT ∧
      ∃ (zero : aspis_core.field.wide_exact.WideExact) (prepared : verifier.Prepared)
        (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
        (root0 root1 : Array U8 32#usize),
        verifier.candidate.prepare (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B) (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
          (FirstComposition.toCurrentPublic
            (AspisR1PublicPreparation.PreparationBinding.preparationPublic statement))
          proof () none (Array.repeat 29#usize zero)=ok (.Ok prepared,scratch) ∧
        prepared.roots=Array.make 2#usize [root0,root1] ∧ root0.val=proof.val.slice 16 48 ∧ root1.val=proof.val.slice 63 95 ∧
        Tx1Reachability.afterPrepare (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B) (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
          bytes proof split () none prepared scratch=ok (.Ok out) ∧
        ∃ (stored initial semantic : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified Unit),
          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
            proof {start:=7031#usize,«end»:=7495#usize}=ok stored ∧
          expandValues stored initial=ok (.Ok (),view.y1) ∧
          stored.length=464 ∧ initial.length=928 ∧ view.y1.length=928 ∧
          (∀ j, j<928 → view.y1.val[j]?=
            if j%32<16 then stored.val[(j/32)*16+j%32]? else some 0#u8) ∧
          sourceView proof semantic view.y1=ok (.Ok view) ∧
          (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B).op9
            (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
            (FirstComposition.toCurrentPublic
              (AspisR1PublicPreparation.PreparationBinding.preparationPublic statement))
            view.semantic () none=ok (.Ok sem) ∧
          (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B).op8
            (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
            sem view () (Array.repeat 29#usize zero)=ok (.Ok prepared,scratch) ∧
          ∀ l : Usize, l.val<29 → ∃ parsed : AspisR1CurrentPreparedClaim.Concrete.E,
            AspisR1CurrentPreparedClaim.ClaimParser.field view.y1 l=ok parsed ∧
            AspisR1CurrentPreparedClaim.Concrete.Canonical parsed := by
  exact owned_stage1_view_y1 adapterOps ops AspisS1ExtractedRoundChildren.children B program accounts data out accepted

#print axioms owned_stage1_extracted_children
end AspisS1ValuesOwnedInstallation
