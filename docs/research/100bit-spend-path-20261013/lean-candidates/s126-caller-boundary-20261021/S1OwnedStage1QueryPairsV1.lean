import S1PreparedQueryPairsInstallationV1
import S1QueryRow31ProgramV1
import S1WideViewVariantV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
noncomputable section
namespace AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1CurrentCaller AspisR1ClaimPreparedBridge
open AspisR1PublicPreparation.PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open S4SolanaDigestWrapperP3BindingV1

/-- Same accepted owned caller; original full preparation now exposes the
source-equal paired query code whose materializer is the fixed math chain.
S2 variant is derived from the actual View child, not separately assumed. -/
theorem owned_stage1_query_pairs_oracle (adapterOps : AdapterRw.Ops) (ops : Ops)
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
        (closedInstall ops).op5 proof semantic y1=ok (.Ok v) ∧ v.variant=.S2 ∧
        (closedInstall ops).op9 (p3CallerDigest sha)
          (FirstComposition.toCurrentPublic (AspisR1PublicPreparation.PreparationBinding.preparationPublic s))
          v.semantic () none=ok (.Ok sem) ∧
        eval (fun bytes => decodeState (sha bytes))
          (pairedCausalPreparationProgram sem v () (Array.repeat 29#usize zero))=
          (observe (run (closedPreparationCode (p3CallerDigest sha) sem v () (Array.repeat 29#usize zero))).1,
            ok (core.result.Result.Ok prepared,scratch)) ∧
        Tx1Reachability.afterPrepare (closedInstall ops) (p3CallerDigest sha) bytes proof k () none
          prepared scratch=ok (.Ok out) := by
  obtain ⟨bytes,proof,k,statement,encoded,hdecode,hencode,hbytes,s,hd,hk,
    zero,prepared,scratch,semantic,y1,v,sem,hview,hsem,hlog,htail⟩ :=
    owned_stage1_causal_preparation_oracle adapterOps ops sha program accounts data out accepted
  have variant : v.variant=.S2 := InstalledPreparation.sourceView_variant proof semantic y1 v hview
  rw [← pairedCausalPreparationProgram_eq] at hlog
  exact ⟨bytes,proof,k,statement,encoded,hdecode,hencode,hbytes,s,hd,hk,
    zero,prepared,scratch,semantic,y1,v,sem,hview,variant,hsem,hlog,htail⟩

theorem closed_query31_program_eq_model {H M Cv : Type} {L : Nat}
    (p : FS2.Duplex.Params M Cv L) (D : aspis_core.digest.Digest32 H)
    (self : AspisR1PublicPreparation.transcript.Transcript H) (payload : Slice U8) :
    oracleProgram (AspisR1PublicPreparation.PreparedQueryEffects.queries effects closedHashQueries
      (InstalledPreparation.retainedDigest D) self 31#u8 payload)=
      AspisR1PublicPreparation.PreparedQueryMaterialize.row31Model closedHashQueries p
        (InstalledPreparation.retainedDigest D) self payload :=
  AspisR1PublicPreparation.PreparedQueryMaterialize.query31_program_eq_model _ p _ _ _

#print axioms owned_stage1_query_pairs_oracle
#print axioms closed_query31_program_eq_model
end AspisR1CurrentCaller.BorrowedClaimPrepared
