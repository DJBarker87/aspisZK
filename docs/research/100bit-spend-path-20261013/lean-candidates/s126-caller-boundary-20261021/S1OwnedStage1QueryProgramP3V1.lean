import S1CurrentOwnedQueryProgramJoinV1
import S1Row31P3ProgramMeaningV1
import S1OwnedStage1PreparationOracleV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
namespace AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge
open AspisR1ClaimPreparedBridge.InstalledMeaning AspisR1CurrentPreparedClaim.Concrete
open OriginalSerializerInstallation

/-- SAME accepted owned parent under the existing P3 source wrapper slots.
All prior claim/powers/rank/scanner conclusions remain, and the fixed query
program evaluates to the actual source query result with its COMPLETE hash log.
No independent query success or per-call hash law. Native SDK/iterator, P3 runtime
acceptance and fixed whole-verifier composition remain separate obligations. -/
theorem owned_stage1_closed_query_program_p3 {M Cv : Type} {L : Nat}
    (adapterOps : AdapterRw.Ops) (ops : Ops)
    (sha : Bytes → Array U8 32#usize)
    (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : Array U8 32#usize) (length : U32)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount)
    (data : Slice U8) (out : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned
      (AspisS6CurrentFirstInstallation.install (installP3Adapter adapterOps sha) (closedInstall ops))
      program accounts data=ok (.Ok out)) :
    ∃ (bytes proof : Slice U8) (k : Usize),
    ∃ (s : AspisR1PublicPreparation.FirstCaller.DecoderStatement),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok s) ∧
      k=compact.SPLIT ∧ ∃ (zero : aspis_core.field.wide_exact.WideExact)
        (semantic y1 : Slice U8) (v : AspisR1SelectedWideViewV1.verifier.View)
        (sem : r1_semantic.Verified Unit) (prepared : AspisR1PublicPreparation.verifier.Prepared)
        (scratch : Array PE 29#usize),
        AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1=ok (.Ok v) ∧
        ops.op9 (p3CallerDigest sha) (FirstComposition.toCurrentPublic
          (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)) v.semantic () none=ok (.Ok sem) ∧
        (Canonical (toClaimE prepared.gamma) ∧ Canonical (toClaimE prepared.kappa)) ∧
        OriginalPayloadClaimMeaning (retainedSem sem) v.y1
          (toClaimE (AspisR1SelectedWideViewV1.prepCarrier v.inactive))
          (toClaimE prepared.gamma) (toClaimE prepared.kappa) (toClaimE prepared.claim)
          (mapArray toClaimE scratch) ∧
        (∀ i : Usize, i.val<29 → ∃ value : AspisR1CurrentPreparedClaim.Concrete.E,
          Array.index_usize (mapArray toClaimE scratch) i=ok value ∧
          Canonical value ∧ decode value=decode (toClaimE prepared.gamma)^i.val) ∧
        ExactSerializedRankTrace (retainedDigest (p3CallerDigest sha)) p pubInput root length
          (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView v) () prepared scratch ∧
        QueryScannerMeaning (retainedDigest (p3CallerDigest sha))
          (AspisR1SelectedWideViewV1.preparedView v) prepared ∧
        Row31QueryProgramMeaning (retainedDigest (p3CallerDigest sha))
          (AspisR1SelectedWideViewV1.preparedView v) prepared ∧
        Row31P3ProgramMeaning sha (AspisR1SelectedWideViewV1.preparedView v) prepared ∧
        Tx1Reachability.afterPrepare (closedInstall ops) (p3CallerDigest sha) bytes proof k () none
          (currentPrepared prepared) (mapArray currentE scratch)=ok (.Ok out) := by
  have digestEq : closedCallerDigest (installP3Adapter adapterOps sha) ops=p3CallerDigest sha :=
    stage1_p3_digest adapterOps ops sha
  obtain ⟨bytes,proof,k,s,hd,hk,zero,semantic,y1,v,sem,prepared,scratch,
    hview,hsem,hcanonical,hclaim,hpowers,htrace,scanner,queryProgram,htail⟩ :=
    current_owned_stage1_closed_claim_rank_and_query_program (installP3Adapter adapterOps sha) ops p
      pubInput root length program accounts data out accepted
  rw [digestEq] at hsem htrace scanner queryProgram htail
  have p3Meaning := row31P3_from_program_meaning p sha
    (AspisR1SelectedWideViewV1.preparedView v) prepared queryProgram
  exact ⟨bytes,proof,k,s,hd,hk,zero,semantic,y1,v,sem,prepared,scratch,
    hview,hsem,hcanonical,hclaim,hpowers,htrace,scanner,queryProgram,p3Meaning,htail⟩

#print axioms owned_stage1_closed_query_program_p3
end AspisR1CurrentCaller.BorrowedClaimPrepared
