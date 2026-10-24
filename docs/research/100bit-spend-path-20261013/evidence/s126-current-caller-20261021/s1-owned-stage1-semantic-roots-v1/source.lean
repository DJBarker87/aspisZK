import S1PrepareSemanticRootsV1
import S6CurrentStage1FirstJoinV1
set_option autoImplicit false
noncomputable section
namespace AspisR1CurrentCaller.BorrowedClaimPrepared
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge
open OriginalSerializerInstallation

def semanticCallerOps (ops : Ops) (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) : Ops :=
  closedInstall (S1SemanticInstallation.install ops R B)

def semanticCallerDigest (adapterOps : AdapterRw.Ops) (ops : Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) : aspis_core.digest.Digest32 Unit :=
  AspisS6CurrentFirstInstallation.toDigest
    (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
      (AspisS6CurrentFirstInstallation.install adapterOps (semanticCallerOps ops R B)))

/-- The SAME accepted owned stage1 supplies the decoded full statement,
semantic public argument, complete semantic verifier execution, both Prepared
roots and the continuation on its returned scratch/checkpoint. No independent
first/decoder/semantic/prepare call, root law or public-selection premise.
Native SDK/callee and physical compact expansion bindings remain open. -/
theorem owned_stage1_semantic_roots (adapterOps : AdapterRw.Ops) (ops : Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount)
    (data : Slice U8) (out : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned
      (AspisS6CurrentFirstInstallation.install adapterOps (semanticCallerOps ops R B))
      program accounts data=ok (.Ok out)) :
    ∃ (bytes proof : Slice U8) (split : Usize)
      (statement : AspisR1PublicPreparation.FirstCaller.DecoderStatement),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok statement) ∧
      split=compact.SPLIT ∧
      ∃ (zero : aspis_core.field.wide_exact.WideExact) (prepared : verifier.Prepared)
        (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
        (semantic y1 : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified Unit)
        (pre : AspisR1PublicPreparation.r1_wire.Prefix)
        (payload : Slice U8) (root2 : Array U8 32#usize),
        sourceView proof semantic y1=ok (.Ok view) ∧
        S1SemanticInstallation.verify R B (semanticCallerDigest adapterOps ops R B)
          (FirstComposition.toCurrentPublic
            (AspisR1PublicPreparation.PreparationBinding.preparationPublic statement))
          view.semantic ()=ok (.Ok sem) ∧
        AspisR1PublicPreparation.PrefixAdapter.parseAccepted view.semantic=ok (.Ok pre) ∧
        AspisR1PublicPreparation.FinishModel.payload pre 2#u8=ok (.Ok payload) ∧
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 payload=ok (.Ok root2) ∧
        root2.val=payload.val ∧ prepared.roots=Array.make 2#usize [pre.c1_root,root2] ∧
        Tx1Reachability.afterPrepare (semanticCallerOps ops R B) (semanticCallerDigest adapterOps ops R B)
          bytes proof split () none prepared scratch=ok (.Ok out) := by
  obtain ⟨bytes,proof,split,decoded,encoded,hdecode,hnative,hencode,hbytes,hfirst⟩ :=
    AspisS6CurrentStage1FirstJoin.accepted_stage1 adapterOps (semanticCallerOps ops R B)
      program accounts data out accepted
  obtain ⟨statement,hd,hk,zero,prepared,scratch,semantic,y1,view,sem,hview,hsem,hnew,tail⟩ :=
    FirstComposition.first_current_prepared_new AdapterRw.solana_program_error.ProgramError.InvalidAccountData
      (semanticCallerOps ops R B) (semanticCallerDigest adapterOps ops R B)
      (fun error => adapterOps.op44 (AspisS6CurrentVerifierCarrier.fromError error)) bytes proof split out hfirst
  change sourceView proof semantic y1=ok (.Ok view) at hview
  change S1SemanticInstallation.verify R B (semanticCallerDigest adapterOps ops R B)
    (FirstComposition.toCurrentPublic (AspisR1PublicPreparation.PreparationBinding.preparationPublic statement))
    view.semantic ()=ok (.Ok sem) at hsem
  change originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
    (semanticCallerDigest adapterOps ops R B) sem view () (Array.repeat 29#usize zero)=ok (.Ok prepared,scratch) at hnew
  have fields := originalNew_static (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
    (semanticCallerDigest adapterOps ops R B) sem view () prepared scratch (Array.repeat 29#usize zero) hnew
  obtain ⟨pre,initial,after,challenges,payload,root2,parsed,publicInit,begin,finish,hpayload,hcopy,hpayloadBytes,hroots⟩ :=
    S1SemanticInstallation.verify_roots R B (semanticCallerDigest adapterOps ops R B)
      _ view.semantic () sem hsem
  exact ⟨bytes,proof,split,statement,hd,hk,zero,prepared,scratch,semantic,y1,view,sem,pre,payload,root2,
    hview,hsem,parsed,hpayload,hcopy,hpayloadBytes,fields.2.1.trans hroots,tail⟩

#print axioms owned_stage1_semantic_roots
end AspisR1CurrentCaller.BorrowedClaimPrepared
