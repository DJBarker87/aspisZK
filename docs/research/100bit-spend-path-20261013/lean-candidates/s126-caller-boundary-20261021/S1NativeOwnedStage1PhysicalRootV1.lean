import S1NativePreparePhysicalRootV1
import S6CurrentStage1FirstJoinV1
set_option autoImplicit false
namespace AspisR1CurrentCaller.BorrowedClaimPrepared.NativeBuffers
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge

def callerDigest (adapterOps : AdapterRw.Ops) (ops : Ops) (native : AspisS1NativeCompact.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) : aspis_core.digest.Digest32 Unit :=
  AspisS6CurrentFirstInstallation.toDigest
    (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
      (AspisS6CurrentFirstInstallation.install adapterOps (install ops native R B)))

/-- The SAME accepted owned stage1 binds its decoded full statement, source
preparation, first physical root and checkpoint continuation. No separate
first/decode/tx1/prepare/semantic/expansion success or root law is assumed.
The explicit Y1 length law and native SDK/account association remain open. -/
theorem owned_stage1_physical_root0 (adapterOps : AdapterRw.Ops) (ops : Ops)
    (native : AspisS1NativeCompact.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (valueLength : ∀ input output status updated,
      ops.op11 input output=ok (status,updated) → updated.length=output.length)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount)
    (data : Slice U8) (out : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned
      (AspisS6CurrentFirstInstallation.install adapterOps (install ops native R B))
      program accounts data=ok (.Ok out)) :
    ∃ (bytes proof : Slice U8) (split : Usize)
      (statement : AspisR1PublicPreparation.FirstCaller.DecoderStatement),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok statement) ∧
      split=compact.SPLIT ∧
      ∃ (zero : aspis_core.field.wide_exact.WideExact) (prepared : verifier.Prepared)
        (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
        (root0 root1 : Array U8 32#usize),
        verifier.candidate.prepare (install ops native R B) (callerDigest adapterOps ops native R B)
          (FirstComposition.toCurrentPublic
            (AspisR1PublicPreparation.PreparationBinding.preparationPublic statement))
          proof () none (Array.repeat 29#usize zero)=ok (.Ok prepared,scratch) ∧
        prepared.roots=Array.make 2#usize [root0,root1] ∧ root0.val=proof.val.slice 16 48 ∧
        Tx1Reachability.afterPrepare (install ops native R B) (callerDigest adapterOps ops native R B)
          bytes proof split () none prepared scratch=ok (.Ok out) := by
  obtain ⟨bytes,proof,split,decoded,encoded,hdecode,hnative,hencode,hbytes,hfirst⟩ :=
    AspisS6CurrentStage1FirstJoin.accepted_stage1 adapterOps (install ops native R B)
      program accounts data out accepted
  obtain ⟨statement,pub,hd,hpub,htx⟩ := AspisR1PublicPreparation.RepinS6First.first_success
    AdapterRw.solana_program_error.ProgramError.InvalidAccountData
    (FirstComposition.currentTx1 (install ops native R B) (callerDigest adapterOps ops native R B))
    (fun error => adapterOps.op44 (AspisS6CurrentVerifierCarrier.fromError error))
    bytes proof split out hfirst
  subst pub
  change verifier.candidate.tx1 (install ops native R B) (callerDigest adapterOps ops native R B)
    (FirstComposition.toCurrentPublic
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic statement))
    bytes proof split () none=ok (.Ok out) at htx
  obtain ⟨hk,variant,zero,prepared,scratch,hvariant,hcheck,hzero,hprepare,tail⟩ := Tx1Reachability.tx1_success
    (install ops native R B) (callerDigest adapterOps ops native R B)
    (FirstComposition.toCurrentPublic
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic statement))
    bytes proof split () out htx
  obtain ⟨root0,root1,hroots,hphysical⟩ := prepare_physical_root0 ops native R B valueLength
    (callerDigest adapterOps ops native R B) _ proof () prepared (Array.repeat 29#usize zero) scratch hprepare
  exact ⟨bytes,proof,split,statement,hd,hk,zero,prepared,scratch,root0,root1,
    hprepare,hroots,hphysical,tail⟩

#print axioms owned_stage1_physical_root0
end AspisR1CurrentCaller.BorrowedClaimPrepared.NativeBuffers
