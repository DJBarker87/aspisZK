import S1ClosedPreparationOracleV1
import S6CurrentStage1FirstJoinV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
noncomputable section
namespace AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1CurrentCaller AspisR1ClaimPreparedBridge
open AspisR1PublicPreparation.PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open S4SolanaDigestWrapperP3BindingV1

/-- Exactly the source Clone and hashv/to_bytes wrapper under existing P3.
Other SDK/account operations are retained. No deployed SDK equality is asserted. -/
def installP3Adapter (ops : AdapterRw.Ops) (sha : Bytes → Array U8 32#usize) : AdapterRw.Ops :=
  {ops with op42 := solanaDigestClone, op43 := (p3PublicDigest32 sha).digest}

theorem stage1_p3_digest (adapterOps : AdapterRw.Ops) (ops : Ops)
    (sha : Bytes → Array U8 32#usize) :
    AspisS6CurrentFirstInstallation.toDigest
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
        (AspisS6CurrentFirstInstallation.install (installP3Adapter adapterOps sha) (closedInstall ops)))=
      p3CallerDigest sha := rfl

/-- One accepted OWNED stage1 call supplies its own public/proof bytes, decoder
and preparation input/output, full ordered preparation log and continuation.
No separate first/prepare success or per-call hash association is a premise. -/
theorem owned_stage1_preparation_oracle (adapterOps : AdapterRw.Ops) (ops : Ops)
    (sha : Bytes → Array U8 32#usize) (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount)
    (data : Slice U8) (out : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned
      (AspisS6CurrentFirstInstallation.install (installP3Adapter adapterOps sha) (closedInstall ops))
      program accounts data=ok (.Ok out)) :
    ∃ (bytes proof : Slice U8) (k : Usize)
      (statement : AspisS6CurrentCodecInstallation.Statement) (encoded : Array U8 1880#usize),
      AspisS6CurrentCodecInstallation.decode bytes=ok (.Ok statement) ∧
      AspisS6CurrentCodecInstallation.encode statement=ok (.Ok encoded) ∧ encoded.val=bytes.val ∧
      ∃ (s : AspisR1PublicPreparation.FirstCaller.DecoderStatement),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok s) ∧
      k=compact.SPLIT ∧ ∃ (zero : aspis_core.field.wide_exact.WideExact)
        (prepared : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
        (semantic y1 : Slice U8) (v : verifier.View) (sem : r1_semantic.Verified Unit),
        (closedInstall ops).op5 proof semantic y1=ok (.Ok v) ∧
        (closedInstall ops).op9 (p3CallerDigest sha)
          (FirstComposition.toCurrentPublic (AspisR1PublicPreparation.PreparationBinding.preparationPublic s))
          v.semantic () none=ok (.Ok sem) ∧
        eval (fun bytes => decodeState (sha bytes))
          (oracleProgram (closedPreparationCode (p3CallerDigest sha) sem v () (Array.repeat 29#usize zero)))=
          (observe (run (closedPreparationCode (p3CallerDigest sha) sem v () (Array.repeat 29#usize zero))).1,
            ok (core.result.Result.Ok prepared,scratch)) ∧
        Tx1Reachability.afterPrepare (closedInstall ops) (p3CallerDigest sha) bytes proof k () none
          prepared scratch=ok (.Ok out) := by
  obtain ⟨bytes,proof,k,statement,encoded,hdecode,hnative,hencode,hbytes,hfirst⟩ :=
    AspisS6CurrentStage1FirstJoin.accepted_stage1 (installP3Adapter adapterOps sha) (closedInstall ops)
      program accounts data out accepted
  rw [stage1_p3_digest] at hfirst
  obtain ⟨s,hd,hk,zero,prepared,scratch,semantic,y1,v,sem,hview,hsem,hnew,htail⟩ :=
    FirstComposition.first_current_prepared_new _ (closedInstall ops) (p3CallerDigest sha)
      _ bytes proof k out hfirst
  refine ⟨bytes,proof,k,statement,encoded,hdecode,hencode,hbytes,s,hd,hk,
    zero,prepared,scratch,semantic,y1,v,sem,hview,hsem,?_,htail⟩
  rw [closedPreparation_oracle_exact]
  congr 1
  rw [run_value,closedPreparationCode_installed ops]
  exact hnew

#print axioms stage1_p3_digest
#print axioms owned_stage1_preparation_oracle
end AspisR1CurrentCaller.BorrowedClaimPrepared
