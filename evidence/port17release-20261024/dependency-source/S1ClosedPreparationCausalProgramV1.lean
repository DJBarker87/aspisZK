import S1PreparedOracleCompleteIrrelevanceV1
import S1ClaimDigestIrrelevanceV1
import S1OwnedStage1PreparationOracleV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
noncomputable section
namespace AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1CurrentCaller AspisR1ClaimPreparedBridge
open AspisR1PublicPreparation.PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open S4SolanaDigestWrapperP3BindingV1

/-- The COMPLETE program, rather than merely its accepted result, is
independent of the backend dictionary. The concrete claim law is discharged. -/
theorem closedPreparation_dictionary_irrelevant {H : Type}
    (first second : aspis_core.digest.Digest32 H) (sem : r1_semantic.Verified H)
    (view : verifier.View) (hash : H) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    oracleProgram (closedPreparationCode first sem view hash scratch)=
      oracleProgram (closedPreparationCode second sem view hash scratch) := by
  unfold closedPreparationCode
  apply oracleProgram_bind_congr
  · apply preparation_oracle_dictionary_irrelevant
    intro sem y1 inactive powers kappa
    exact claimPublic_digest_irrelevant _ _ _ _ _ _ _
  · intro value
    rfl

/-- A fixed causal program. The dummy dictionary never supplies a returned
hash: all digest nodes are interpreted by oracleProgram's ask constructor.
Dictionary independence above proves this, not an opaque source replacement. -/
def causalPreparationProgram (sem : r1_semantic.Verified SolanaDigest)
    (view : verifier.View) (hash : SolanaDigest)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    Program Bytes State (Result (core.result.Result verifier.Prepared verifier.Error ×
      Array aspis_core.field.wide_exact.WideExact 29#usize)) :=
  oracleProgram (closedPreparationCode
    (p3CallerDigest (fun _ => Array.repeat 32#usize 0#u8)) sem view hash scratch)

/-- Whole ordered oracle execution and returned Result for a fixed program,
for every functional SHA interpretation. No oracle-dependent program premise. -/
theorem causalPreparation_exact (sha : Bytes → Array U8 32#usize)
    (sem : r1_semantic.Verified SolanaDigest) (view : verifier.View) (hash : SolanaDigest)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    eval (fun bytes => decodeState (sha bytes)) (causalPreparationProgram sem view hash scratch)=
      (observe (run (closedPreparationCode (p3CallerDigest sha) sem view hash scratch)).1,
        (run (closedPreparationCode (p3CallerDigest sha) sem view hash scratch)).2) := by
  unfold causalPreparationProgram
  rw [closedPreparation_dictionary_irrelevant _ (p3CallerDigest sha)]
  exact closedPreparation_oracle_exact sha sem view hash scratch

theorem causalPreparation_installed (ops : Ops) (sha : Bytes → Array U8 32#usize)
    (sem : r1_semantic.Verified SolanaDigest) (view : verifier.View) (hash : SolanaDigest)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    (eval (fun bytes => decodeState (sha bytes)) (causalPreparationProgram sem view hash scratch)).2=
      (closedInstall ops).op8 (p3CallerDigest sha) sem view hash scratch := by
  rw [causalPreparation_exact,run_value]
  exact closedPreparationCode_installed ops _ _ _ _ _

theorem owned_stage1_causal_preparation_oracle (adapterOps : AdapterRw.Ops) (ops : Ops)
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
          (causalPreparationProgram sem v () (Array.repeat 29#usize zero))=
          (observe (run (closedPreparationCode (p3CallerDigest sha) sem v () (Array.repeat 29#usize zero))).1,
            ok (core.result.Result.Ok prepared,scratch)) ∧
        Tx1Reachability.afterPrepare (closedInstall ops) (p3CallerDigest sha) bytes proof k () none
          prepared scratch=ok (.Ok out) := by
  obtain ⟨bytes,proof,k,statement,encoded,hdecode,hencode,hbytes,s,hd,hk,
    zero,prepared,scratch,semantic,y1,v,sem,hview,hsem,hlog,htail⟩ :=
    owned_stage1_preparation_oracle adapterOps ops sha program accounts data out accepted
  have same : causalPreparationProgram sem v () (Array.repeat 29#usize zero)=
      oracleProgram (closedPreparationCode (p3CallerDigest sha) sem v () (Array.repeat 29#usize zero)) :=
    closedPreparation_dictionary_irrelevant _ (p3CallerDigest sha) _ _ _ _
  rw [← same] at hlog
  exact ⟨bytes,proof,k,statement,encoded,hdecode,hencode,hbytes,s,hd,hk,
    zero,prepared,scratch,semantic,y1,v,sem,hview,hsem,hlog,htail⟩

#print axioms owned_stage1_causal_preparation_oracle

#print axioms closedPreparation_dictionary_irrelevant
#print axioms causalPreparation_exact
#print axioms causalPreparation_installed
end AspisR1CurrentCaller.BorrowedClaimPrepared
