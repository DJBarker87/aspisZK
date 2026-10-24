import S1OwnedStage1QueryProgramP3V1
import S1Row31SelectedProgramMeaningV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
namespace AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge
open AspisR1ClaimPreparedBridge.InstalledMeaning AspisR1CurrentPreparedClaim.Concrete
open OriginalSerializerInstallation

/-- SAME accepted owned parent supplies the actual final-message size and
framing for the selected fixed-parameter query constructor, including the
complete source hash log, ordered result/state and subsequent rho call. All
prior claim/powers/rank/scanner/public/continuation conclusions remain. No
independent frame, size, cast, message or query-success premise is added.
Actual full-prefix and native SDK/iterator/arithmetic binding remain open. -/
theorem owned_stage1_selected_query_program {M Cv : Type} {L : Nat}
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
        v.final_message.length=2048 ∧
        Row31SelectedProgramMeaning sha (AspisR1SelectedWideViewV1.preparedView v) prepared ∧
        Tx1Reachability.afterPrepare (closedInstall ops) (p3CallerDigest sha) bytes proof k () none
          (currentPrepared prepared) (mapArray currentE scratch)=ok (.Ok out) := by
  obtain ⟨bytes,proof,k,s,hd,hk,zero,semantic,y1,v,sem,prepared,scratch,
    hview,hsem,hcanonical,hclaim,hpowers,htrace,scanner,queryProgram,p3Meaning,htail⟩ :=
    owned_stage1_closed_query_program_p3 adapterOps ops sha p pubInput root length
      program accounts data out accepted
  have finalLength := AspisR1SelectedWideViewV1.wide_view_final_length proof semantic y1 v hview
  have selected := row31_selected_from_p3 sha (AspisR1SelectedWideViewV1.preparedView v) prepared finalLength p3Meaning
  exact ⟨bytes,proof,k,s,hd,hk,zero,semantic,y1,v,sem,prepared,scratch,
    hview,hsem,hcanonical,hclaim,hpowers,htrace,scanner,queryProgram,p3Meaning,finalLength,selected,htail⟩

#print axioms owned_stage1_selected_query_program
end AspisR1CurrentCaller.BorrowedClaimPrepared
