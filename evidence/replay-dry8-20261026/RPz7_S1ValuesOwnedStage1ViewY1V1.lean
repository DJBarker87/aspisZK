import RPz7_S1ValuesOwnedStage1RootsV1
import RPz7_S1ValuesOwnedPrepareViewY1V1
set_option autoImplicit false
namespace AspisS1ValuesOwnedInstallation
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller AspisR1CurrentCaller.BorrowedClaimPrepared AspisR1CurrentCaller.InstalledPreparation

/-- Same full accepted owned stage1: decoded public statement, release None,
actual prepare/scratch, both physical roots, actual View.y1 bytes, all field reads and continuation.
Native SDK/account correspondence remains separate. -/
theorem owned_stage1_view_y1 (adapterOps : AdapterRw.Ops) (ops : Ops)
   
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount)
    (data : Slice U8) (out : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned
      (AspisS6CurrentFirstInstallation.install adapterOps (NativeBuffers.install (withValues ops) nativeValues R B))
      program accounts data=ok (.Ok out)) :
    ∃ (bytes proof : Slice U8) (split : Usize)
      (statement : AspisR1PublicPreparation.FirstCaller.DecoderStatement),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok statement) ∧
      split=compact.SPLIT ∧
      ∃ (zero : aspis_core.field.wide_exact.WideExact) (prepared : verifier.Prepared)
        (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
        (root0 root1 : Array U8 32#usize),
        verifier.candidate.prepare (NativeBuffers.install (withValues ops) nativeValues R B) (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues R B)
          (FirstComposition.toCurrentPublic
            (AspisR1PublicPreparation.PreparationBinding.preparationPublic statement))
          proof () none (Array.repeat 29#usize zero)=ok (.Ok prepared,scratch) ∧
        prepared.roots=Array.make 2#usize [root0,root1] ∧ root0.val=proof.val.slice 16 48 ∧ root1.val=proof.val.slice 63 95 ∧
        Tx1Reachability.afterPrepare (NativeBuffers.install (withValues ops) nativeValues R B) (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues R B)
          bytes proof split () none prepared scratch=ok (.Ok out) ∧
        ∃ (stored initial semantic : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified Unit),
          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
            proof {start:=7031#usize,«end»:=7495#usize}=ok stored ∧
          expandValues stored initial=ok (.Ok (),view.y1) ∧
          stored.length=464 ∧ initial.length=928 ∧ view.y1.length=928 ∧
          (∀ j, j<928 → view.y1.val[j]?=
            if j%32<16 then stored.val[(j/32)*16+j%32]? else some 0#u8) ∧
          sourceView proof semantic view.y1=ok (.Ok view) ∧
          (NativeBuffers.install (withValues ops) nativeValues R B).op9
            (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues R B)
            (FirstComposition.toCurrentPublic
              (AspisR1PublicPreparation.PreparationBinding.preparationPublic statement))
            view.semantic () none=ok (.Ok sem) ∧
          (NativeBuffers.install (withValues ops) nativeValues R B).op8
            (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues R B)
            sem view () (Array.repeat 29#usize zero)=ok (.Ok prepared,scratch) ∧
          ∀ l : Usize, l.val<29 → ∃ parsed : AspisR1CurrentPreparedClaim.Concrete.E,
            AspisR1CurrentPreparedClaim.ClaimParser.field view.y1 l=ok parsed ∧
            AspisR1CurrentPreparedClaim.Concrete.Canonical parsed := by
  obtain ⟨bytes,proof,split,statement,decoded,hk,zero,prepared,scratch,root0,root1,
    hprepare,hroots,hphysical0,hphysical1,tail⟩ :=
    owned_stage1_physical_roots adapterOps ops R B program accounts data out accepted
  obtain ⟨stored,initial,semantic,view,sem,hstored,hvalues,storedSize,initialSize,
    expandedSize,formula,hview,hsem,hnew,fields⟩ :=
    prepare_view_y1 ops R B (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues R B)
      _ proof () prepared (Array.repeat 29#usize zero) scratch hprepare
  exact ⟨bytes,proof,split,statement,decoded,hk,zero,prepared,scratch,root0,root1,
    hprepare,hroots,hphysical0,hphysical1,tail,
    stored,initial,semantic,view,sem,hstored,hvalues,storedSize,initialSize,expandedSize,formula,hview,hsem,hnew,fields⟩

#print axioms owned_stage1_view_y1
end AspisS1ValuesOwnedInstallation
