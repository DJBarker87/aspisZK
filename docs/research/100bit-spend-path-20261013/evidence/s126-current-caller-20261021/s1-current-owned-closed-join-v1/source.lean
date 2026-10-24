import S1ClosedPreparationInstallationV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
namespace AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge
open AspisR1ClaimPreparedBridge.InstalledMeaning AspisR1CurrentPreparedClaim.Concrete
open OriginalSerializerInstallation

/-- Accepted current owned source caller with concrete preparation procedures.
No sampling/embedding/serialization callback parameter or independent first,
prepare, scratch, canonicality or continuation success remains. Native source
claim and SDK/runtime/cone-backend installation are separate obligations. -/
theorem current_owned_stage1_closed_claim_and_rank {M Cv : Type} {L : Nat}
    (adapterOps : AdapterRw.Ops) (ops : Ops)
    (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : Array U8 32#usize) (length : U32)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount)
    (data : Slice U8) (out : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned
      (AspisS6CurrentFirstInstallation.install adapterOps (closedInstall ops))
      program accounts data=ok (.Ok out)) :
    ∃ (bytes proof : Slice U8) (k : Usize),
    ∃ (s : AspisR1PublicPreparation.FirstCaller.DecoderStatement),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok s) ∧
      k=compact.SPLIT ∧ ∃ (zero : aspis_core.field.wide_exact.WideExact)
        (semantic y1 : Slice U8) (v : AspisR1SelectedWideViewV1.verifier.View)
        (sem : r1_semantic.Verified Unit) (prepared : AspisR1PublicPreparation.verifier.Prepared)
        (scratch : Array PE 29#usize),
        AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1=ok (.Ok v) ∧
        ops.op9 (closedCallerDigest adapterOps ops) (FirstComposition.toCurrentPublic
          (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)) v.semantic () none=ok (.Ok sem) ∧
        (Canonical (toClaimE prepared.gamma) ∧ Canonical (toClaimE prepared.kappa)) ∧
        OriginalPayloadClaimMeaning (retainedSem sem) v.y1
          (toClaimE (AspisR1SelectedWideViewV1.prepCarrier v.inactive))
          (toClaimE prepared.gamma) (toClaimE prepared.kappa) (toClaimE prepared.claim)
          (mapArray toClaimE scratch) ∧
        (∀ i : Usize, i.val<29 → ∃ value : AspisR1CurrentPreparedClaim.Concrete.E,
          Array.index_usize (mapArray toClaimE scratch) i=ok value ∧
          Canonical value ∧ decode value=decode (toClaimE prepared.gamma)^i.val) ∧
        ExactSerializedRankTrace (retainedDigest (closedCallerDigest adapterOps ops)) p pubInput root length
          (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView v) () prepared scratch ∧
        Tx1Reachability.afterPrepare (closedInstall ops) (closedCallerDigest adapterOps ops) bytes proof k () none
          (currentPrepared prepared) (mapArray currentE scratch)=ok (.Ok out) := by
  exact current_owned_stage1_concrete_claim_and_rank adapterOps ops closedSampling
    p pubInput root length program accounts data out accepted

#print axioms current_owned_stage1_closed_claim_and_rank
end AspisR1CurrentCaller.BorrowedClaimPrepared
