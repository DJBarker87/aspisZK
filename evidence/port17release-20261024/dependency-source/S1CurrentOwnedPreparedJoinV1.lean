import S1BorrowedClaimFirstCallerV1
import S6CurrentStage1FirstJoinV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
namespace AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge
open AspisR1ClaimPreparedBridge.InstalledMeaning AspisR1CurrentPreparedClaim.Concrete

def callerDigest (adapterOps : AdapterRw.Ops) (ops : Ops)
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 → Result PE) :
    aspis_core.digest.Digest32 Unit :=
  AspisS6CurrentFirstInstallation.toDigest
    (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
      (AspisS6CurrentFirstInstallation.install adapterOps (install ops sampling embed)))

/-- Current extracted owned stage1, with concrete codec and current tx1,
supplies the original Prepared.new/borrowed-reference claim trace from THIS
parent. No independent first/prepare/continuation success premise is added.
Sampling/embed/native-claim and SDK runtime refinement obligations remain. -/
theorem current_owned_stage1_claim_and_rank {M Cv : Type} {L : Nat}
    (adapterOps : AdapterRw.Ops) (ops : Ops)
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 → Result PE)
    (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : Array U8 32#usize) (length : U32)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount)
    (data : Slice U8) (out : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned
      (AspisS6CurrentFirstInstallation.install adapterOps (install ops sampling embed))
      program accounts data=ok (.Ok out)) :
    ∃ (bytes proof : Slice U8) (k : Usize),
    ∃ (s : AspisR1PublicPreparation.FirstCaller.DecoderStatement),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok s) ∧
      k=compact.SPLIT ∧ ∃ (zero : aspis_core.field.wide_exact.WideExact)
        (semantic y1 : Slice U8) (v : AspisR1SelectedWideViewV1.verifier.View)
        (sem : r1_semantic.Verified Unit) (prepared : AspisR1PublicPreparation.verifier.Prepared)
        (scratch : Array PE 29#usize),
        AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1=ok (.Ok v) ∧
        ops.op9 (callerDigest adapterOps ops sampling embed) (FirstComposition.toCurrentPublic
          (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)) v.semantic () none=ok (.Ok sem) ∧
        (Canonical (toClaimE prepared.gamma) ∧ Canonical (toClaimE prepared.kappa)) ∧
        OriginalPayloadClaimMeaning (retainedSem sem) v.y1
          (toClaimE (AspisR1SelectedWideViewV1.prepCarrier v.inactive))
          (toClaimE prepared.gamma) (toClaimE prepared.kappa) (toClaimE prepared.claim)
          (mapArray toClaimE scratch) ∧
        (∀ i : Usize, i.val<29 → ∃ value : AspisR1CurrentPreparedClaim.Concrete.E,
          Array.index_usize (mapArray toClaimE scratch) i=ok value ∧
          Canonical value ∧ decode value=decode (toClaimE prepared.gamma)^i.val) ∧
        JointRankTrace sampling embed (retainedDigest (callerDigest adapterOps ops sampling embed)) p pubInput root length
          (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView v) () prepared scratch ∧
        Tx1Reachability.afterPrepare (install ops sampling embed) (callerDigest adapterOps ops sampling embed) bytes proof k () none
          (currentPrepared prepared) (mapArray currentE scratch)=ok (.Ok out) := by
  obtain ⟨bytes,proof,k,statement,encoded,hdecode,hnative,hencode,hbytes,hfirst⟩ :=
    AspisS6CurrentStage1FirstJoin.accepted_stage1 adapterOps (install ops sampling embed)
      program accounts data out accepted
  exact ⟨bytes,proof,k,first_borrowed_reference_claim_and_rank
    AdapterRw.solana_program_error.ProgramError.InvalidAccountData ops sampling embed
    (callerDigest adapterOps ops sampling embed) p pubInput root length
    (fun error => adapterOps.op44 (AspisS6CurrentVerifierCarrier.fromError error))
    bytes proof k out hfirst⟩

#print axioms callerDigest
#print axioms current_owned_stage1_claim_and_rank
end AspisR1CurrentCaller.BorrowedClaimPrepared
